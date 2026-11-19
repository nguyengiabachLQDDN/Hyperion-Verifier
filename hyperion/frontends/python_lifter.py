"""Python AST to Unified SSA IR Lifter with Phi-node synthesis and security taint tagging."""

import ast
from typing import Dict, List, Optional, Tuple

from hyperion.ir.ssa import (
    ArrayLoadOp,
    ArrayStoreOp,
    AssertOp,
    AssignOp,
    BasicBlock,
    BinaryOp,
    CallOp,
    CondBranchOp,
    Const,
    IRFunction,
    IRModule,
    IRType,
    IRValue,
    Instruction,
    JumpOp,
    PhiOp,
    ReturnOp,
    SSAVar,
    SinkOp,
    UnaryOp,
)

TAINT_SOURCES = {
    "input",
    "raw_input",
    "recv",
    "read_packet",
    "get_user_input",
    "untrusted_input",
    "getenv",
    "argv",
    "read_line",
}

SANITIZERS = {
    "sanitize",
    "escape",
    "html_escape",
    "validate_int",
    "int",
    "clamp",
    "quote",
    "clean_input",
}

SECURITY_SINKS = {
    "eval": "code_injection",
    "exec": "code_injection",
    "system": "os_command_injection",
    "popen": "os_command_injection",
    "run_cmd": "os_command_injection",
    "execute": "sql_injection",
    "sql_query": "sql_injection",
    "sql_exec": "sql_injection",
    "open": "path_traversal",
    "buffer_write": "buffer_overflow",
}


class _SSABuilder:
    """Maintains block construction, variable SSA versioning, and Phi merges."""

    def __init__(
        self,
        fn_name: str,
        params: List[str],
        source_file: str,
        line_start: int,
        line_end: int,
        source_code: str,
    ) -> None:
        self.fn = IRFunction(
            name=fn_name,
            source_lang="python",
            source_file=source_file,
            line_start=line_start,
            line_end=line_end,
            source_code=source_code,
        )
        self._next_block_id = 0
        self._next_inst_id = 1
        self._versions: Dict[str, int] = {}
        self._current_env: Dict[str, SSAVar] = {}

        entry = self.new_block("entry")
        self.fn.entry_id = entry.id
        self.cur_block = entry

        for p in params:
            var = self.new_var(p, IRType.ANY)
            self.fn.params.append(var)
            self._current_env[p] = var

    def new_block(self, label: str) -> BasicBlock:
        bid = self._next_block_id
        self._next_block_id += 1
        blk = BasicBlock(id=bid, label=label)
        self.fn.blocks[bid] = blk
        return blk

    def new_var(self, base: str, ir_type: IRType = IRType.ANY) -> SSAVar:
        ver = self._versions.get(base, 0)
        self._versions[base] = ver + 1
        return SSAVar(name=base, version=ver, ir_type=ir_type)

    def emit(self, ins: Instruction, block: Optional[BasicBlock] = None) -> Instruction:
        target = block or self.cur_block
        ins.id = self._next_inst_id
        self._next_inst_id += 1
        target.instructions.append(ins)
        return ins

    def snapshot_env(self) -> Dict[str, SSAVar]:
        return dict(self._current_env)

    def restore_env(self, env: Dict[str, SSAVar]) -> None:
        self._current_env = dict(env)

    def get_var(self, name: str) -> IRValue:
        if name in self._current_env:
            return self._current_env[name]
        v = self.new_var(name, IRType.ANY)
        self._current_env[name] = v
        return v

    def set_var(self, name: str, val: IRValue, line: int) -> SSAVar:
        dest = self.new_var(name, val.ir_type)
        self.emit(AssignOp(dest=dest, line=line, src=val))
        self._current_env[name] = dest
        return dest

    def link(self, src_id: int, dst_id: int) -> None:
        src = self.fn.blocks[src_id]
        dst = self.fn.blocks[dst_id]
        if dst_id not in src.succs:
            src.succs.append(dst_id)
        if src_id not in dst.preds:
            dst.preds.append(src_id)

    def terminate_jump(self, target_id: int, line: int) -> None:
        if not self.cur_block.is_terminated():
            self.emit(JumpOp(line=line, target=target_id))
            self.link(self.cur_block.id, target_id)


def _binop_symbol(op: ast.operator) -> str:
    mapping = {
        ast.Add: "+",
        ast.Sub: "-",
        ast.Mult: "*",
        ast.Div: "/",
        ast.FloorDiv: "//",
        ast.Mod: "%",
        ast.BitAnd: "&",
        ast.BitOr: "|",
        ast.BitXor: "^",
        ast.LShift: "<<",
        ast.RShift: ">>",
        ast.Pow: "**",
    }
    return mapping.get(type(op), "+")


def _cmp_symbol(op: ast.cmpop) -> str:
    mapping = {
        ast.Eq: "==",
        ast.NotEq: "!=",
        ast.Lt: "<",
        ast.LtE: "<=",
        ast.Gt: ">",
        ast.GtE: ">=",
        ast.In: "in",
        ast.NotIn: "not_in",
        ast.Is: "==",
        ast.IsNot: "!=",
    }
    return mapping.get(type(op), "==")


def _const_from_node(node: ast.Constant) -> Const:
    v = node.value
    if isinstance(v, bool):
        return Const(value=v, ir_type=IRType.BOOL)
    if isinstance(v, int):
        return Const(value=v, ir_type=IRType.INT)
    if isinstance(v, float):
        return Const(value=v, ir_type=IRType.FLOAT)
    if isinstance(v, str):
        return Const(value=v, ir_type=IRType.STRING)
    return Const(value=0 if v is None else str(v), ir_type=IRType.ANY)


def _call_name(func_node: ast.AST) -> str:
    if isinstance(func_node, ast.Name):
        return func_node.id
    if isinstance(func_node, ast.Attribute):
        return func_node.attr
    return "dynamic_call"


def _lift_expr(b: _SSABuilder, node: Optional[ast.AST], line: int) -> IRValue:
    if node is None:
        return Const(value=0, ir_type=IRType.INT)
    ln = getattr(node, "lineno", line)

    if isinstance(node, ast.Constant):
        return _const_from_node(node)

    if isinstance(node, ast.Name):
        if node.id in ("True", "False"):
            return Const(value=(node.id == "True"), ir_type=IRType.BOOL)
        if node.id == "None":
            return Const(value=0, ir_type=IRType.ANY)
        return b.get_var(node.id)

    if isinstance(node, ast.UnaryOp):
        operand = _lift_expr(b, node.operand, ln)
        op_str = "-"
        res_type = operand.ir_type
        if isinstance(node.op, ast.Not):
            op_str = "not"
            res_type = IRType.BOOL
        elif isinstance(node.op, ast.Invert):
            op_str = "~"
            res_type = IRType.INT
        elif isinstance(node.op, ast.UAdd):
            return operand
        dest = b.new_var("u", res_type)
        b.emit(UnaryOp(dest=dest, line=ln, op=op_str, operand=operand))
        return dest

    if isinstance(node, ast.BinOp):
        left = _lift_expr(b, node.left, ln)
        right = _lift_expr(b, node.right, ln)
        sym = _binop_symbol(node.op)
        res_type = IRType.FLOAT if sym == "/" else (
            IRType.INT if left.ir_type == IRType.INT and right.ir_type == IRType.INT else IRType.ANY
        )
        dest = b.new_var("t", res_type)
        b.emit(BinaryOp(dest=dest, line=ln, op=sym, left=left, right=right))
        return dest

    if isinstance(node, ast.BoolOp):
        sym = "and" if isinstance(node.op, ast.And) else "or"
        acc = _lift_expr(b, node.values[0], ln)
        for nxt_node in node.values[1:]:
            rhs = _lift_expr(b, nxt_node, ln)
            dest = b.new_var("b", IRType.BOOL)
            b.emit(BinaryOp(dest=dest, line=ln, op=sym, left=acc, right=rhs))
            acc = dest
        return acc

    if isinstance(node, ast.Compare):
        left = _lift_expr(b, node.left, ln)
        acc: Optional[IRValue] = None
        for op, comp_node in zip(node.ops, node.comparators):
            right = _lift_expr(b, comp_node, ln)
            dest = b.new_var("cmp", IRType.BOOL)
            b.emit(BinaryOp(dest=dest, line=ln, op=_cmp_symbol(op), left=left, right=right))
            if acc is None:
                acc = dest
            else:
                joined = b.new_var("and", IRType.BOOL)
                b.emit(BinaryOp(dest=joined, line=ln, op="and", left=acc, right=dest))
                acc = joined
            left = right
        return acc or Const(value=True, ir_type=IRType.BOOL)

    if isinstance(node, ast.Call):
        callee = _call_name(node.func)
        args = [_lift_expr(b, a, ln) for a in node.args]
        dest = b.new_var("ret", IRType.ANY)
        if callee in SECURITY_SINKS:
            b.emit(SinkOp(dest=dest, line=ln, sink_kind=SECURITY_SINKS[callee], args=args))
        else:
            b.emit(
                CallOp(
                    dest=dest,
                    line=ln,
                    callee=callee,
                    args=args,
                    is_taint_source=(callee in TAINT_SOURCES or callee.startswith("untrusted_")),
                    is_sanitizer=(callee in SANITIZERS),
                )
            )
        return dest

    if isinstance(node, ast.Subscript):
        arr = _lift_expr(b, node.value, ln)
        idx = _lift_expr(b, node.slice, ln)
        known_len = None
        if isinstance(arr, SSAVar):
            known_len = b.fn.array_lengths.get(arr.name)
        dest = b.new_var("elem", IRType.ANY)
        b.emit(ArrayLoadOp(dest=dest, line=ln, array=arr, index=idx, known_length=known_len))
        return dest

    if isinstance(node, ast.List):
        dest = b.new_var("arr", IRType.ARRAY)
        b.fn.array_lengths[dest.name] = len(node.elts)
        b.emit(CallOp(dest=dest, line=ln, callee="alloc_array", args=[Const(value=len(node.elts), ir_type=IRType.INT)]))
        return dest

    if isinstance(node, ast.IfExp):
        cond = _lift_expr(b, node.test, ln)
        t_val = _lift_expr(b, node.body, ln)
        f_val = _lift_expr(b, node.orelse, ln)
        dest = b.new_var("tern", t_val.ir_type)
        b.emit(CallOp(dest=dest, line=ln, callee="select", args=[cond, t_val, f_val]))
        return dest

    if isinstance(node, ast.Attribute):
        base = _lift_expr(b, node.value, ln)
        dest = b.new_var("attr", IRType.ANY)
        b.emit(CallOp(dest=dest, line=ln, callee=f"getattr_{node.attr}", args=[base]))
        return dest

    return Const(value=0, ir_type=IRType.ANY)


def _merge_phis(
    b: _SSABuilder,
    join_block: BasicBlock,
    env_a: Dict[str, SSAVar],
    pred_a: int,
    env_b: Dict[str, SSAVar],
    pred_b: int,
    line: int,
) -> Dict[str, SSAVar]:
    merged: Dict[str, SSAVar] = {}
    all_keys = sorted(set(env_a.keys()) | set(env_b.keys()))
    for k in all_keys:
        va = env_a.get(k)
        vb = env_b.get(k)
        if va is not None and vb is not None and va.key() == vb.key():
            merged[k] = va
        elif va is not None and vb is not None:
            dest = b.new_var(k, va.ir_type)
            b.emit(
                PhiOp(dest=dest, line=line, incomings=[(pred_a, va), (pred_b, vb)]),
                block=join_block,
            )
            merged[k] = dest
        else:
            chosen = va if va is not None else vb
            if chosen is not None:
                merged[k] = chosen
    return merged


def _lift_stmts(b: _SSABuilder, stmts: List[ast.stmt]) -> None:
    for stmt in stmts:
        if b.cur_block.is_terminated():
            break
        ln = getattr(stmt, "lineno", 1)

        if isinstance(stmt, ast.Assign):
            val = _lift_expr(b, stmt.value, ln)
            for tgt in stmt.targets:
                if isinstance(tgt, ast.Name):
                    if isinstance(stmt.value, ast.List):
                        b.fn.array_lengths[tgt.id] = len(stmt.value.elts)
                    b.set_var(tgt.id, val, ln)
                elif isinstance(tgt, ast.Subscript):
                    arr = _lift_expr(b, tgt.value, ln)
                    idx = _lift_expr(b, tgt.slice, ln)
                    known_len = b.fn.array_lengths.get(arr.name) if isinstance(arr, SSAVar) else None
                    b.emit(ArrayStoreOp(line=ln, array=arr, index=idx, value=val, known_length=known_len))

        elif isinstance(stmt, ast.AnnAssign):
            if stmt.value is not None and isinstance(stmt.target, ast.Name):
                val = _lift_expr(b, stmt.value, ln)
                b.set_var(stmt.target.id, val, ln)

        elif isinstance(stmt, ast.AugAssign):
            if isinstance(stmt.target, ast.Name):
                cur = b.get_var(stmt.target.id)
                rhs = _lift_expr(b, stmt.value, ln)
                tmp = b.new_var("aug", cur.ir_type)
                b.emit(BinaryOp(dest=tmp, line=ln, op=_binop_symbol(stmt.op), left=cur, right=rhs))
                b.set_var(stmt.target.id, tmp, ln)

        elif isinstance(stmt, ast.Expr):
            _lift_expr(b, stmt.value, ln)

        elif isinstance(stmt, ast.Assert):
            cond = _lift_expr(b, stmt.test, ln)
            msg = "assert_failed"
            if stmt.msg and isinstance(stmt.msg, ast.Constant):
                msg = str(stmt.msg.value)
            b.emit(AssertOp(line=ln, cond=cond, message=msg))

        elif isinstance(stmt, ast.Return):
            val = _lift_expr(b, stmt.value, ln) if stmt.value is not None else None
            b.emit(ReturnOp(line=ln, value=val))

        elif isinstance(stmt, ast.If):
            cond = _lift_expr(b, stmt.test, ln)
            pre_env = b.snapshot_env()
            entry_blk = b.cur_block
            then_blk = b.new_block(f"if_then_{ln}")
            else_blk = b.new_block(f"if_else_{ln}")
            join_blk = b.new_block(f"if_join_{ln}")

            b.emit(
                CondBranchOp(line=ln, cond=cond, true_target=then_blk.id, false_target=else_blk.id),
                block=entry_blk,
            )
            b.link(entry_blk.id, then_blk.id)
            b.link(entry_blk.id, else_blk.id)

            b.cur_block = then_blk
            b.restore_env(pre_env)
            _lift_stmts(b, stmt.body)
            then_end = b.cur_block
            then_falls = not then_end.is_terminated()
            if then_falls:
                b.terminate_jump(join_blk.id, ln)
            then_env = b.snapshot_env()

            b.cur_block = else_blk
            b.restore_env(pre_env)
            _lift_stmts(b, stmt.orelse)
            else_end = b.cur_block
            else_falls = not else_end.is_terminated()
            if else_falls:
                b.terminate_jump(join_blk.id, ln)
            else_env = b.snapshot_env()

            if then_falls and else_falls:
                b.cur_block = join_blk
                merged = _merge_phis(
                    b, join_blk, then_env, then_end.id, else_env, else_end.id, ln
                )
                b.restore_env(merged)
            elif then_falls:
                b.cur_block = join_blk
                b.restore_env(then_env)
            elif else_falls:
                b.cur_block = join_blk
                b.restore_env(else_env)
            else:
                b.cur_block = join_blk
                b.emit(ReturnOp(line=ln, value=None), block=join_blk)

        elif isinstance(stmt, ast.While):
            pre_env = b.snapshot_env()
            pre_blk = b.cur_block
            hdr_blk = b.new_block(f"while_hdr_{ln}")
            body_blk = b.new_block(f"while_body_{ln}")
            exit_blk = b.new_block(f"while_exit_{ln}")

            b.terminate_jump(hdr_blk.id, ln)
            b.cur_block = hdr_blk
            b.restore_env(pre_env)

            # Reserve Phi slots for variables modified in loop
            cond = _lift_expr(b, stmt.test, ln)
            b.emit(
                CondBranchOp(line=ln, cond=cond, true_target=body_blk.id, false_target=exit_blk.id),
                block=hdr_blk,
            )
            b.link(hdr_blk.id, body_blk.id)
            b.link(hdr_blk.id, exit_blk.id)

            b.cur_block = body_blk
            _lift_stmts(b, stmt.body)
            if not b.cur_block.is_terminated():
                b.terminate_jump(hdr_blk.id, ln)
            body_env = b.snapshot_env()

            # Insert PhiOp at header for mutated loop variables
            loop_phis: List[PhiOp] = []
            for k, post_v in body_env.items():
                pre_v = pre_env.get(k)
                if pre_v is not None and post_v.key() != pre_v.key():
                    phi_v = b.new_var(k, pre_v.ir_type)
                    loop_phis.append(
                        PhiOp(
                            id=b._next_inst_id,
                            dest=phi_v,
                            line=ln,
                            incomings=[(pre_blk.id, pre_v), (b.cur_block.id, post_v)],
                        )
                    )
                    b._next_inst_id += 1
                    pre_env[k] = phi_v
            if loop_phis:
                hdr_blk.instructions = loop_phis + hdr_blk.instructions

            b.cur_block = exit_blk
            b.restore_env(pre_env)

        elif isinstance(stmt, ast.For):
            # Lower `for i in range(...)` cleanly into counter loop SSA
            iter_var = stmt.target.id if isinstance(stmt.target, ast.Name) else "_idx"
            start_val: IRValue = Const(value=0, ir_type=IRType.INT)
            stop_val: IRValue = Const(value=10, ir_type=IRType.INT)
            if (
                isinstance(stmt.iter, ast.Call)
                and _call_name(stmt.iter.func) == "range"
                and stmt.iter.args
            ):
                if len(stmt.iter.args) == 1:
                    stop_val = _lift_expr(b, stmt.iter.args[0], ln)
                else:
                    start_val = _lift_expr(b, stmt.iter.args[0], ln)
                    stop_val = _lift_expr(b, stmt.iter.args[1], ln)
            else:
                _lift_expr(b, stmt.iter, ln)

            init_v = b.set_var(iter_var, start_val, ln)
            pre_blk = b.cur_block
            pre_env = b.snapshot_env()

            hdr_blk = b.new_block(f"for_hdr_{ln}")
            body_blk = b.new_block(f"for_body_{ln}")
            exit_blk = b.new_block(f"for_exit_{ln}")

            b.terminate_jump(hdr_blk.id, ln)
            b.cur_block = hdr_blk
            phi_idx = b.new_var(iter_var, IRType.INT)
            pre_env[iter_var] = phi_idx
            b.restore_env(pre_env)

            cond_v = b.new_var("for_cond", IRType.BOOL)
            b.emit(BinaryOp(dest=cond_v, line=ln, op="<", left=phi_idx, right=stop_val))
            b.emit(
                CondBranchOp(line=ln, cond=cond_v, true_target=body_blk.id, false_target=exit_blk.id)
            )
            b.link(hdr_blk.id, body_blk.id)
            b.link(hdr_blk.id, exit_blk.id)

            b.cur_block = body_blk
            _lift_stmts(b, stmt.body)
            if not b.cur_block.is_terminated():
                next_v = b.new_var(iter_var, IRType.INT)
                b.emit(
                    BinaryOp(
                        dest=next_v, line=ln, op="+", left=b.get_var(iter_var), right=Const(value=1, ir_type=IRType.INT)
                    )
                )
                b._current_env[iter_var] = next_v
                back_id = b.cur_block.id
                b.terminate_jump(hdr_blk.id, ln)
            else:
                back_id = b.cur_block.id
                next_v = b.get_var(iter_var)

            phi = PhiOp(
                id=b._next_inst_id,
                dest=phi_idx,
                line=ln,
                incomings=[(pre_blk.id, init_v), (back_id, next_v)],
            )
            b._next_inst_id += 1
            hdr_blk.instructions.insert(0, phi)

            b.cur_block = exit_blk
            b.restore_env(pre_env)

        elif isinstance(stmt, ast.Try):
            _lift_stmts(b, stmt.body)
            for h in stmt.handlers:
                _lift_stmts(b, h.body)
            _lift_stmts(b, stmt.finalbody)


def lift_python_source(
    source_code: str, module_name: str = "module", source_file: str = "<memory>"
) -> IRModule:
    """Parse Python source string and lift all functions/methods into Unified SSA IR."""
    mod = IRModule(
        name=module_name,
        language="python",
        source_file=source_file,
        source_code=source_code,
    )
    try:
        tree = ast.parse(source_code)
    except SyntaxError as exc:
        mod.parse_errors.append(f"SyntaxError at line {exc.lineno}: {exc.msg}")
        return mod

    lines = source_code.splitlines()

    def process_fn(node: ast.FunctionDef | ast.AsyncFunctionDef, prefix: str = "") -> None:
        param_names = [a.arg for a in node.args.args if a.arg != "self"]
        l_start = getattr(node, "lineno", 1)
        l_end = getattr(node, "end_lineno", l_start)
        snippet = "\n".join(lines[max(0, l_start - 1) : l_end])
        full_name = f"{prefix}{node.name}"
        builder = _SSABuilder(
            fn_name=full_name,
            params=param_names,
            source_file=source_file,
            line_start=l_start,
            line_end=l_end,
            source_code=snippet,
        )
        _lift_stmts(builder, node.body)
        if not builder.cur_block.is_terminated():
            builder.emit(ReturnOp(line=l_end, value=None))
        mod.functions.append(builder.fn)

    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            process_fn(node)
        elif isinstance(node, ast.ClassDef):
            for sub in node.body:
                if isinstance(sub, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    process_fn(sub, prefix=f"{node.name}.")

    return mod
