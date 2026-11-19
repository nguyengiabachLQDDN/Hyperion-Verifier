"""Multi-pass SSA Optimization Engine (Constant Folding, Algebraic Simplification, CSE, DCE)."""

from dataclasses import dataclass
from typing import Any, Dict, Optional, Set, Tuple

from hyperion.ir.ssa import (
    AssignOp,
    AssertOp,
    ArrayStoreOp,
    BinaryOp,
    CallOp,
    CondBranchOp,
    Const,
    IRFunction,
    IRType,
    IRValue,
    JumpOp,
    PhiOp,
    ReturnOp,
    SSAVar,
    SinkOp,
    UnaryOp,
)


@dataclass
class OptimizationStats:
    passes_run: int = 0
    constants_folded: int = 0
    copies_propagated: int = 0
    cse_eliminated: int = 0
    dead_instructions_removed: int = 0


def _eval_binary_const(op: str, a: Any, b: Any) -> Tuple[bool, Any]:
    try:
        if op == "+":
            return True, a + b
        if op == "-":
            return True, a - b
        if op == "*":
            return True, a * b
        if op == "/" and b != 0:
            return True, a / b
        if op == "//" and b != 0:
            return True, a // b
        if op == "%" and b != 0:
            return True, a % b
        if op == "==":
            return True, bool(a == b)
        if op == "!=":
            return True, bool(a != b)
        if op == "<":
            return True, bool(a < b)
        if op == "<=":
            return True, bool(a <= b)
        if op == ">":
            return True, bool(a > b)
        if op == ">=":
            return True, bool(a >= b)
        if op == "and":
            return True, bool(a and b)
        if op == "or":
            return True, bool(a or b)
        if op == "&" and isinstance(a, int) and isinstance(b, int):
            return True, a & b
        if op == "|" and isinstance(a, int) and isinstance(b, int):
            return True, a | b
        if op == "^" and isinstance(a, int) and isinstance(b, int):
            return True, a ^ b
        if op == "<<" and isinstance(a, int) and isinstance(b, int) and 0 <= b <= 32:
            return True, a << b
        if op == ">>" and isinstance(a, int) and isinstance(b, int) and 0 <= b <= 32:
            return True, a >> b
    except Exception:
        return False, None
    return False, None


def _infer_const_type(val: Any) -> IRType:
    if isinstance(val, bool):
        return IRType.BOOL
    if isinstance(val, int):
        return IRType.INT
    if isinstance(val, float):
        return IRType.FLOAT
    if isinstance(val, str):
        return IRType.STRING
    return IRType.ANY


def optimize_function_ssa(fn: IRFunction, max_rounds: int = 3) -> OptimizationStats:
    """Apply iterative Copy Propagation, Constant Folding, CSE, and DCE on SSA IR."""
    stats = OptimizationStats()

    for _ in range(max_rounds):
        stats.passes_run += 1
        changed = False
        env: Dict[str, IRValue] = {}

        def resolve(v: IRValue) -> IRValue:
            if isinstance(v, SSAVar) and v.key() in env:
                return env[v.key()]
            return v

        # Pass 1: Copy Propagation + Constant Folding + Algebraic Identity
        for bid in sorted(fn.blocks.keys()):
            blk = fn.blocks[bid]
            cse_table: Dict[Tuple[str, str, str], SSAVar] = {}
            new_insts = []
            for ins in blk.instructions:
                if isinstance(ins, AssignOp):
                    src = resolve(ins.src)
                    ins.src = src
                    if ins.dest is not None:
                        env[ins.dest.key()] = src
                        if src != ins.src:
                            stats.copies_propagated += 1
                    new_insts.append(ins)
                elif isinstance(ins, UnaryOp):
                    opd = resolve(ins.operand)
                    ins.operand = opd
                    if isinstance(opd, Const) and ins.dest is not None:
                        val: Optional[Any] = None
                        if ins.op == "-" and isinstance(opd.value, (int, float)):
                            val = -opd.value
                        elif ins.op in ("not", "!"):
                            val = not bool(opd.value)
                        elif ins.op == "~" and isinstance(opd.value, int):
                            val = ~opd.value
                        if val is not None:
                            c = Const(value=val, ir_type=_infer_const_type(val))
                            env[ins.dest.key()] = c
                            new_insts.append(AssignOp(id=ins.id, dest=ins.dest, line=ins.line, src=c))
                            stats.constants_folded += 1
                            changed = True
                            continue
                    new_insts.append(ins)
                elif isinstance(ins, BinaryOp):
                    lval = resolve(ins.left)
                    rval = resolve(ins.right)
                    ins.left, ins.right = lval, rval
                    if isinstance(lval, Const) and isinstance(rval, Const) and ins.dest is not None:
                        ok, folded = _eval_binary_const(ins.op, lval.value, rval.value)
                        if ok:
                            c = Const(value=folded, ir_type=_infer_const_type(folded))
                            env[ins.dest.key()] = c
                            new_insts.append(AssignOp(id=ins.id, dest=ins.dest, line=ins.line, src=c))
                            stats.constants_folded += 1
                            changed = True
                            continue
                    # Algebraic simplifications
                    if ins.dest is not None and isinstance(rval, Const):
                        if ins.op in ("+", "-") and rval.value == 0:
                            env[ins.dest.key()] = lval
                            new_insts.append(AssignOp(id=ins.id, dest=ins.dest, line=ins.line, src=lval))
                            stats.copies_propagated += 1
                            changed = True
                            continue
                        if ins.op == "*" and rval.value == 1:
                            env[ins.dest.key()] = lval
                            new_insts.append(AssignOp(id=ins.id, dest=ins.dest, line=ins.line, src=lval))
                            stats.copies_propagated += 1
                            changed = True
                            continue
                        if ins.op == "*" and rval.value == 0:
                            c0 = Const(value=0, ir_type=IRType.INT)
                            env[ins.dest.key()] = c0
                            new_insts.append(AssignOp(id=ins.id, dest=ins.dest, line=ins.line, src=c0))
                            stats.constants_folded += 1
                            changed = True
                            continue
                    # Local CSE within block
                    if ins.dest is not None:
                        key = (ins.op, lval.format(), rval.format())
                        if key in cse_table:
                            prev = cse_table[key]
                            env[ins.dest.key()] = prev
                            new_insts.append(AssignOp(id=ins.id, dest=ins.dest, line=ins.line, src=prev))
                            stats.cse_eliminated += 1
                            changed = True
                            continue
                        cse_table[key] = ins.dest
                    new_insts.append(ins)
                elif isinstance(ins, PhiOp):
                    ins.incomings = [(b, resolve(v)) for b, v in ins.incomings]
                    vals = [v for _, v in ins.incomings]
                    if vals and all(v == vals[0] for v in vals) and ins.dest is not None:
                        env[ins.dest.key()] = vals[0]
                        new_insts.append(AssignOp(id=ins.id, dest=ins.dest, line=ins.line, src=vals[0]))
                        stats.copies_propagated += 1
                        changed = True
                        continue
                    new_insts.append(ins)
                elif isinstance(ins, CondBranchOp):
                    ins.cond = resolve(ins.cond)
                    new_insts.append(ins)
                elif isinstance(ins, CallOp):
                    ins.args = [resolve(a) for a in ins.args]
                    new_insts.append(ins)
                elif isinstance(ins, SinkOp):
                    ins.args = [resolve(a) for a in ins.args]
                    new_insts.append(ins)
                elif isinstance(ins, AssertOp):
                    ins.cond = resolve(ins.cond)
                    new_insts.append(ins)
                elif isinstance(ins, ReturnOp):
                    if ins.value is not None:
                        ins.value = resolve(ins.value)
                    new_insts.append(ins)
                else:
                    new_insts.append(ins)
            blk.instructions = new_insts

        # Pass 2: Dead Code Elimination (keep side-effecting, live defs, and named user assignments)
        _temp_names = {"t", "u", "b", "cmp", "and", "ret", "elem", "arr", "tern", "attr", "aug", "call", "for_cond"}
        used_vars: Set[str] = set()
        for blk in fn.blocks.values():
            for ins in blk.instructions:
                for u in ins.uses():
                    if isinstance(u, SSAVar):
                        used_vars.add(u.key())

        for blk in fn.blocks.values():
            kept = []
            for ins in blk.instructions:
                has_side_effect = isinstance(
                    ins,
                    (
                        CondBranchOp,
                        JumpOp,
                        ReturnOp,
                        CallOp,
                        SinkOp,
                        AssertOp,
                        ArrayStoreOp,
                    ),
                )
                is_named_assign = (
                    isinstance(ins, AssignOp)
                    and ins.dest is not None
                    and ins.dest.name not in _temp_names
                )
                if has_side_effect or is_named_assign or ins.dest is None or ins.dest.key() in used_vars:
                    kept.append(ins)
                else:
                    stats.dead_instructions_removed += 1
                    changed = True
            blk.instructions = kept

        if not changed:
            break

    return stats
