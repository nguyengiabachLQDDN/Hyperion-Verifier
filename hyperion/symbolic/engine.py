"""Symbolic Execution Engine with Path Forking, Constraint Solving & Counterexample Synthesis."""

from dataclasses import dataclass, field, asdict
import math
from typing import Dict, List, Optional, Set, Tuple, Any

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
    IRValue,
    JumpOp,
    PhiOp,
    ReturnOp,
    SSAVar,
    SinkOp,
    UnaryOp,
)
from hyperion.solver.dpll_smt import (
    DPLLTSolver,
    SymBinOp,
    SymConst,
    SymExpr,
    SymNot,
    SymVar,
)


@dataclass
class Counterexample:
    kind: str  # "ASSERTION_VIOLATION" | "DIV_BY_ZERO" | "BUFFER_OOB" | "TAINT_REACHABLE"
    severity: str
    function: str
    line: int
    block_id: int
    description: str
    inputs: Dict[str, int] = field(default_factory=dict)
    path_blocks: List[int] = field(default_factory=list)
    trace_steps: List[Dict[str, Any]] = field(default_factory=list)

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)


@dataclass
class DeadBranchInfo:
    block_id: int
    target_block_id: int
    line: int
    branch_kind: str  # "true" | "false" | "unreachable"
    condition: str
    reason: str

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)


@dataclass
class SymbolicResult:
    function: str
    paths_explored: int = 0
    feasible_paths: int = 0
    infeasible_pruned: int = 0
    smt_queries: int = 0
    smt_decisions: int = 0
    smt_conflicts: int = 0
    counterexamples: List[Counterexample] = field(default_factory=list)
    synthesized_test_vectors: List[Dict[str, int]] = field(default_factory=list)
    dead_branches: List[Dict[str, Any]] = field(default_factory=list)
    dead_block_ids: Set[int] = field(default_factory=set)
    dead_edges: Set[Tuple[int, int]] = field(default_factory=set)


@dataclass
class _SymState:
    block_id: int
    prev_block_id: Optional[int]
    env: Dict[str, SymExpr]
    tainted: Set[str]
    constraints: List[SymExpr]
    trace: List[int]
    depth: int = 0


def _to_sym(val: IRValue, env: Dict[str, SymExpr]) -> SymExpr:
    if isinstance(val, Const):
        if isinstance(val.value, bool):
            return SymConst(1 if val.value else 0)
        if isinstance(val.value, (int, float)):
            return SymConst(int(val.value))
        return SymConst(len(str(val.value)))
    if isinstance(val, SSAVar):
        return env.get(val.key(), SymVar(val.name))
    return SymConst(0)


def _is_tainted(val: IRValue, tainted: Set[str]) -> bool:
    return isinstance(val, SSAVar) and val.key() in tainted


def _format_sym_expr(expr: SymExpr) -> str:
    if isinstance(expr, SymConst):
        return str(expr.value)
    if isinstance(expr, SymVar):
        return expr.name
    if isinstance(expr, SymNot):
        inner = _format_sym_expr(expr.expr)
        return f"not ({inner})"
    if isinstance(expr, SymBinOp):
        left = _format_sym_expr(expr.left)
        right = _format_sym_expr(expr.right)
        return f"({left} {expr.op} {right})"
    return ""


def _format_trace_val(v: Any) -> Any:
    if v is None or isinstance(v, (bool, int, str)):
        return v
    if isinstance(v, float):
        return v if math.isfinite(v) else str(v)
    if isinstance(v, list):
        if len(v) <= 12:
            return [_format_trace_val(x) for x in v]
        return f"[array len={len(v)}]"
    return repr(v)[:64]


def _snapshot_vars(env: Dict[str, Any], fn: IRFunction, ins: Any) -> Dict[str, Any]:
    param_keys = [p.key() for p in fn.params]
    if len(env) <= 24:
        ordered: List[str] = []
        seen: Set[str] = set()
        for pk in param_keys:
            if pk in env and pk not in seen:
                ordered.append(pk)
                seen.add(pk)
        for k in env:
            if k not in seen:
                ordered.append(k)
                seen.add(k)
        return {k: _format_trace_val(env[k]) for k in ordered}

    priority: List[str] = []
    seen_p: Set[str] = set()
    for pk in param_keys:
        if pk in env and pk not in seen_p:
            priority.append(pk)
            seen_p.add(pk)
    dest = getattr(ins, "dest", None)
    if isinstance(dest, SSAVar) and dest.key() in env and dest.key() not in seen_p:
        priority.append(dest.key())
        seen_p.add(dest.key())
    for u in ins.uses():
        if isinstance(u, SSAVar) and u.key() in env and u.key() not in seen_p:
            priority.append(u.key())
            seen_p.add(u.key())

    for k in reversed(list(env.keys())):
        if len(priority) >= 24:
            break
        if k not in seen_p:
            priority.append(k)
            seen_p.add(k)
    return {k: _format_trace_val(env[k]) for k in priority[:24]}


def _filter_intervals(
    intervals: Optional[Dict[str, str]], vars_snap: Dict[str, Any], ins: Any
) -> Dict[str, str]:
    if not intervals:
        return {}
    active: Set[str] = set(vars_snap.keys())
    dest = getattr(ins, "dest", None)
    if isinstance(dest, SSAVar):
        active.add(dest.key())
    for u in ins.uses():
        if isinstance(u, SSAVar):
            active.add(u.key())
    out: Dict[str, str] = {}
    for k, v in intervals.items():
        if k in active:
            out[k] = str(v)
            if len(out) >= 24:
                break
    return out


def replay_function_trace(
    fn: IRFunction,
    inputs: Dict[str, Any],
    intervals: Optional[Dict[str, str]] = None,
    gas_limit: int = 2000,
) -> List[Dict[str, Any]]:
    """Replay concrete SSA execution step-by-step matching IRInterpreter semantics."""
    if not fn.blocks or fn.entry_id not in fn.blocks:
        return []

    gas_cap = max(1, min(int(gas_limit), 10000))
    env: Dict[str, Any] = {}
    arrays: Dict[str, List[Any]] = {}
    for p in fn.params:
        if p.name in inputs:
            val = inputs[p.name]
        elif p.key() in inputs:
            val = inputs[p.key()]
        else:
            val = 0
        env[p.key()] = list(val) if isinstance(val, list) else val

    def val_of(v: IRValue) -> Any:
        if isinstance(v, Const):
            return v.value
        if isinstance(v, SSAVar):
            return env.get(v.key(), 0)
        return 0

    cur_bid: Optional[int] = fn.entry_id
    prev_bid: Optional[int] = None
    steps = 0
    trace: List[Dict[str, Any]] = []

    def make_step(blk_id: int, blk_label: str, ins: Any, event: str) -> Dict[str, Any]:
        vars_snap = _snapshot_vars(env, fn, ins)
        iv_snap = _filter_intervals(intervals, vars_snap, ins)
        return {
            "step": len(trace),
            "block_id": blk_id,
            "block_label": blk_label,
            "line": ins.line,
            "instruction": ins.format(),
            "vars": vars_snap,
            "intervals": iv_snap,
            "event": event,
        }

    while cur_bid is not None and cur_bid in fn.blocks:
        blk = fn.blocks[cur_bid]
        next_bid: Optional[int] = None

        for ins in blk.instructions:
            steps += 1
            if steps > gas_cap:
                trace.append(make_step(cur_bid, blk.label, ins, "timeout:gas_limit_exceeded"))
                return trace

            event = "step"

            if isinstance(ins, PhiOp):
                chosen: Optional[IRValue] = None
                if prev_bid is not None:
                    for pb, pv in ins.incomings:
                        if pb == prev_bid:
                            chosen = pv
                            break
                if chosen is None and ins.incomings:
                    chosen = ins.incomings[0][1]
                if ins.dest is not None:
                    env[ins.dest.key()] = val_of(chosen) if chosen is not None else 0

            elif isinstance(ins, AssignOp):
                if ins.dest is not None:
                    env[ins.dest.key()] = val_of(ins.src)

            elif isinstance(ins, UnaryOp):
                opd = val_of(ins.operand)
                try:
                    if ins.op == "-":
                        u_res = -opd
                    elif ins.op in ("not", "!"):
                        u_res = not bool(opd)
                    elif ins.op == "~":
                        u_res = ~int(opd)
                    else:
                        u_res = opd
                except Exception:
                    trace.append(make_step(cur_bid, blk.label, ins, "trap:runtime_error"))
                    return trace
                if ins.dest is not None:
                    env[ins.dest.key()] = u_res

            elif isinstance(ins, BinaryOp):
                lv = val_of(ins.left)
                rv = val_of(ins.right)
                try:
                    op = ins.op
                    if op == "+":
                        b_res = lv + rv
                    elif op == "-":
                        b_res = lv - rv
                    elif op == "*":
                        b_res = lv * rv
                    elif op in ("/", "//"):
                        if rv == 0:
                            trace.append(make_step(cur_bid, blk.label, ins, "trap:zero_division"))
                            return trace
                        b_res = lv / rv if op == "/" else lv // rv
                    elif op == "%":
                        if rv == 0:
                            trace.append(make_step(cur_bid, blk.label, ins, "trap:zero_modulo"))
                            return trace
                        b_res = lv % rv
                    elif op == "==":
                        b_res = lv == rv
                    elif op == "!=":
                        b_res = lv != rv
                    elif op == "<":
                        b_res = lv < rv
                    elif op == "<=":
                        b_res = lv <= rv
                    elif op == ">":
                        b_res = lv > rv
                    elif op == ">=":
                        b_res = lv >= rv
                    elif op == "and":
                        b_res = bool(lv) and bool(rv)
                    elif op == "or":
                        b_res = bool(lv) or bool(rv)
                    elif op == "&":
                        b_res = int(lv) & int(rv)
                    elif op == "|":
                        b_res = int(lv) | int(rv)
                    elif op == "^":
                        b_res = int(lv) ^ int(rv)
                    elif op == "<<":
                        b_res = int(lv) << max(0, min(int(rv), 16))
                    elif op == ">>":
                        b_res = int(lv) >> max(0, min(int(rv), 16))
                    else:
                        b_res = 0
                except Exception:
                    trace.append(make_step(cur_bid, blk.label, ins, "trap:runtime_error"))
                    return trace
                if ins.dest is not None:
                    env[ins.dest.key()] = b_res

            elif isinstance(ins, CallOp):
                if ins.dest is not None:
                    if ins.callee == "alloc_array" and ins.args:
                        sz = max(0, min(int(val_of(ins.args[0])), 256))
                        arr_key = ins.dest.key()
                        arrays[arr_key] = [0] * sz
                        env[arr_key] = arrays[arr_key]
                    elif ins.callee == "len" and ins.args:
                        arg0 = val_of(ins.args[0])
                        env[ins.dest.key()] = len(arg0) if hasattr(arg0, "__len__") else 0
                    elif ins.callee == "select" and len(ins.args) == 3:
                        env[ins.dest.key()] = (
                            val_of(ins.args[1]) if val_of(ins.args[0]) else val_of(ins.args[2])
                        )
                    else:
                        acc = sum(
                            int(val_of(a))
                            for a in ins.args
                            if isinstance(val_of(a), (int, float))
                        )
                        env[ins.dest.key()] = (acc * 31 + len(ins.callee)) & 0xFFFF

            elif isinstance(ins, ArrayLoadOp):
                arr_v = val_of(ins.array)
                idx_raw = val_of(ins.index)
                idx_v = int(idx_raw) if isinstance(idx_raw, (int, float)) else 0
                if isinstance(arr_v, list):
                    if idx_v < 0 or idx_v >= len(arr_v):
                        trace.append(make_step(cur_bid, blk.label, ins, "trap:oob_read"))
                        return trace
                    val = arr_v[idx_v]
                elif ins.known_length is not None and (idx_v < 0 or idx_v >= ins.known_length):
                    trace.append(make_step(cur_bid, blk.label, ins, "trap:oob_read"))
                    return trace
                else:
                    val = idx_v
                if ins.dest is not None:
                    env[ins.dest.key()] = val

            elif isinstance(ins, ArrayStoreOp):
                arr_v = val_of(ins.array)
                idx_raw = val_of(ins.index)
                idx_v = int(idx_raw) if isinstance(idx_raw, (int, float)) else 0
                if isinstance(arr_v, list):
                    if idx_v < 0 or idx_v >= len(arr_v):
                        trace.append(make_step(cur_bid, blk.label, ins, "trap:oob_write"))
                        return trace
                    arr_v[idx_v] = val_of(ins.value)
                elif ins.known_length is not None and (idx_v < 0 or idx_v >= ins.known_length):
                    trace.append(make_step(cur_bid, blk.label, ins, "trap:oob_write"))
                    return trace

            elif isinstance(ins, AssertOp):
                if not bool(val_of(ins.cond)):
                    trace.append(make_step(cur_bid, blk.label, ins, "trap:assertion_failed"))
                    return trace

            elif isinstance(ins, SinkOp):
                if ins.dest is not None:
                    env[ins.dest.key()] = 1
                event = f"sink:{ins.sink_kind}"

            elif isinstance(ins, CondBranchOp):
                taken = bool(val_of(ins.cond))
                next_bid = ins.true_target if taken else ins.false_target
                trace.append(
                    make_step(cur_bid, blk.label, ins, "branch_true" if taken else "branch_false")
                )
                break

            elif isinstance(ins, JumpOp):
                next_bid = ins.target
                trace.append(make_step(cur_bid, blk.label, ins, "jump"))
                break

            elif isinstance(ins, ReturnOp):
                if ins.value is not None:
                    _ = val_of(ins.value)
                trace.append(make_step(cur_bid, blk.label, ins, "return"))
                return trace

            trace.append(make_step(cur_bid, blk.label, ins, event))

        prev_bid = cur_bid
        cur_bid = next_bid

    return trace


def run_symbolic_execution(
    fn: IRFunction,
    max_paths: int = 100,
    max_depth: int = 24,
    intervals: Optional[Dict[str, str]] = None,
) -> SymbolicResult:
    """Explore feasible SSA execution paths and synthesize concrete counterexamples via DPLL(T)."""
    res = SymbolicResult(function=fn.name)
    if not fn.blocks or fn.entry_id not in fn.blocks:
        return res

    solver = DPLLTSolver(default_lo=-64, default_hi=64)
    init_env: Dict[str, SymExpr] = {}
    init_tainted: Set[str] = set()
    param_names = [p.name for p in fn.params]

    for p in fn.params:
        init_env[p.key()] = SymVar(p.name)
        pname = p.name.lower()
        if any(tok in pname for tok in ("input", "user", "query", "payload", "cmd", "packet", "raw", "untrusted")):
            init_tainted.add(p.key())

    queue: List[_SymState] = [
        _SymState(
            block_id=fn.entry_id,
            prev_block_id=None,
            env=init_env,
            tainted=init_tainted,
            constraints=[],
            trace=[fn.entry_id],
            depth=0,
        )
    ]
    seen_bugs: Set[Tuple[str, int, int]] = set()
    seen_vectors: Set[Tuple[Tuple[str, int], ...]] = set()
    reached_blocks: Set[int] = {fn.entry_id}
    branch_outcomes: Dict[Tuple[int, int], bool] = {}
    branch_meta: Dict[Tuple[int, int], Tuple[int, str, str]] = {}
    unroll_capped_blocks: Set[int] = set()

    def record_vector(model: Dict[str, int]) -> None:
        vec = {p: model.get(p, 0) for p in param_names}
        key = tuple(sorted(vec.items()))
        if key not in seen_vectors and len(res.synthesized_test_vectors) < 16:
            seen_vectors.add(key)
            res.synthesized_test_vectors.append(vec)

    while queue and res.paths_explored < max_paths:
        st = queue.pop(0)
        reached_blocks.add(st.block_id)
        res.paths_explored += 1
        blk = fn.blocks[st.block_id]
        env = dict(st.env)
        tainted = set(st.tainted)
        constraints = list(st.constraints)

        for ins in blk.instructions:
            if isinstance(ins, PhiOp):
                chosen: Optional[IRValue] = None
                if st.prev_block_id is not None:
                    for pred_b, val in ins.incomings:
                        if pred_b == st.prev_block_id:
                            chosen = val
                            break
                if chosen is None and ins.incomings:
                    chosen = ins.incomings[0][1]
                if ins.dest is not None and chosen is not None:
                    env[ins.dest.key()] = _to_sym(chosen, env)
                    if _is_tainted(chosen, tainted):
                        tainted.add(ins.dest.key())

            elif isinstance(ins, AssignOp):
                if ins.dest is not None:
                    env[ins.dest.key()] = _to_sym(ins.src, env)
                    if _is_tainted(ins.src, tainted):
                        tainted.add(ins.dest.key())

            elif isinstance(ins, UnaryOp):
                if ins.dest is not None:
                    opd = _to_sym(ins.operand, env)
                    if ins.op in ("not", "!"):
                        env[ins.dest.key()] = SymNot(opd)
                    elif ins.op == "-":
                        env[ins.dest.key()] = SymBinOp("-", SymConst(0), opd)
                    else:
                        env[ins.dest.key()] = opd
                    if _is_tainted(ins.operand, tainted):
                        tainted.add(ins.dest.key())

            elif isinstance(ins, BinaryOp):
                l_sym = _to_sym(ins.left, env)
                r_sym = _to_sym(ins.right, env)
                if ins.op in ("/", "//", "%"):
                    # Query SMT solver for divisor == 0 reachability
                    res.smt_queries += 1
                    div_zero = solver.solve(constraints + [SymBinOp("==", r_sym, SymConst(0))])
                    res.smt_decisions += div_zero.stats.decisions
                    res.smt_conflicts += div_zero.stats.conflicts
                    if div_zero.status == "SAT":
                        bkey = ("DIV_BY_ZERO", blk.id, ins.line)
                        if bkey not in seen_bugs:
                            seen_bugs.add(bkey)
                            vec = {p: div_zero.model.get(p, 0) for p in param_names}
                            res.counterexamples.append(
                                Counterexample(
                                    kind="DIV_BY_ZERO",
                                    severity="HIGH",
                                    function=fn.name,
                                    line=ins.line,
                                    block_id=blk.id,
                                    description=f"Đường chạy khả thi dẫn tới lỗi chia cho 0 tại số chia {ins.right.format()}",
                                    inputs=vec,
                                    path_blocks=list(st.trace),
                                    trace_steps=replay_function_trace(fn, vec, intervals=intervals),
                                )
                            )
                            record_vector(div_zero.model)
                if ins.dest is not None:
                    env[ins.dest.key()] = SymBinOp(ins.op, l_sym, r_sym)
                    if _is_tainted(ins.left, tainted) or _is_tainted(ins.right, tainted):
                        tainted.add(ins.dest.key())

            elif isinstance(ins, CallOp):
                if ins.dest is not None:
                    env[ins.dest.key()] = SymVar(f"{ins.dest.key()}")
                    if ins.is_taint_source:
                        tainted.add(ins.dest.key())
                    elif ins.is_sanitizer:
                        tainted.discard(ins.dest.key())
                    elif any(_is_tainted(a, tainted) for a in ins.args):
                        tainted.add(ins.dest.key())

            elif isinstance(ins, AssertOp):
                cond_sym = _to_sym(ins.cond, env)
                res.smt_queries += 1
                fail_res = solver.solve(constraints + [SymNot(cond_sym)])
                res.smt_decisions += fail_res.stats.decisions
                res.smt_conflicts += fail_res.stats.conflicts
                if fail_res.status == "SAT":
                    bkey = ("ASSERTION_VIOLATION", blk.id, ins.line)
                    if bkey not in seen_bugs:
                        seen_bugs.add(bkey)
                        vec = {p: fail_res.model.get(p, 0) for p in param_names}
                        res.counterexamples.append(
                            Counterexample(
                                kind="ASSERTION_VIOLATION",
                                severity="HIGH",
                                function=fn.name,
                                line=ins.line,
                                block_id=blk.id,
                                description=f"Khẳng định (assert) '{ins.message}' bị vi phạm trên đường chạy khả thi",
                                inputs=vec,
                                path_blocks=list(st.trace),
                                trace_steps=replay_function_trace(fn, vec, intervals=intervals),
                            )
                        )
                        record_vector(fail_res.model)

            elif isinstance(ins, (ArrayLoadOp, ArrayStoreOp)):
                idx_sym = _to_sym(ins.index, env)
                oob_conds: List[SymExpr] = [SymBinOp("<", idx_sym, SymConst(0))]
                if ins.known_length is not None:
                    oob_conds.append(SymBinOp(">=", idx_sym, SymConst(ins.known_length)))
                for oob_c in oob_conds:
                    res.smt_queries += 1
                    oob_res = solver.solve(constraints + [oob_c])
                    res.smt_decisions += oob_res.stats.decisions
                    res.smt_conflicts += oob_res.stats.conflicts
                    if oob_res.status == "SAT":
                        bkey = ("BUFFER_OOB", blk.id, ins.line)
                        if bkey not in seen_bugs:
                            seen_bugs.add(bkey)
                            vec = {p: oob_res.model.get(p, 0) for p in param_names}
                            res.counterexamples.append(
                                Counterexample(
                                    kind="BUFFER_OOB",
                                    severity="CRITICAL",
                                    function=fn.name,
                                    line=ins.line,
                                    block_id=blk.id,
                                    description=f"Chỉ số truy cập mảng {ins.index.format()} vượt ngoài giới hạn (độ dài={ins.known_length if ins.known_length is not None else '?'})",
                                    inputs=vec,
                                    path_blocks=list(st.trace),
                                    trace_steps=replay_function_trace(fn, vec, intervals=intervals),
                                )
                            )
                            record_vector(oob_res.model)
                        break

            elif isinstance(ins, SinkOp):
                if any(_is_tainted(a, tainted) for a in ins.args):
                    res.smt_queries += 1
                    reach = solver.solve(constraints)
                    res.smt_decisions += reach.stats.decisions
                    res.smt_conflicts += reach.stats.conflicts
                    if reach.status == "SAT":
                        bkey = ("TAINT_REACHABLE", blk.id, ins.line)
                        if bkey not in seen_bugs:
                            seen_bugs.add(bkey)
                            vec = {p: reach.model.get(p, 0) for p in param_names}
                            res.counterexamples.append(
                                Counterexample(
                                    kind="TAINT_REACHABLE",
                                    severity="CRITICAL",
                                    function=fn.name,
                                    line=ins.line,
                                    block_id=blk.id,
                                    description=f"Đường chạy khả thi đưa dữ liệu không tin cậy tới sink bảo mật '{ins.sink_kind}'",
                                    inputs=vec,
                                    path_blocks=list(st.trace),
                                    trace_steps=replay_function_trace(fn, vec, intervals=intervals),
                                )
                            )
                            record_vector(reach.model)

            elif isinstance(ins, CondBranchOp):
                if st.depth >= max_depth:
                    unroll_capped_blocks.add(blk.id)
                    continue
                cond_sym = _to_sym(ins.cond, env)
                cond_str = _format_sym_expr(cond_sym) or ins.cond.format()
                for take_true, target_id in (
                    (True, ins.true_target),
                    (False, ins.false_target),
                ):
                    if st.trace.count(target_id) >= 3:
                        unroll_capped_blocks.add(blk.id)
                        unroll_capped_blocks.add(target_id)
                        continue  # Loop unroll cap
                    branch_meta.setdefault(
                        (blk.id, target_id),
                        (ins.line, "true" if take_true else "false", cond_str),
                    )
                    branch_c = cond_sym if take_true else SymNot(cond_sym)
                    nxt_constraints = constraints + [branch_c]
                    res.smt_queries += 1
                    sat = solver.solve(nxt_constraints)
                    res.smt_decisions += sat.stats.decisions
                    res.smt_conflicts += sat.stats.conflicts
                    if sat.status in ("SAT", "UNKNOWN"):
                        branch_outcomes[(blk.id, target_id)] = True
                        reached_blocks.add(target_id)
                        if sat.status == "SAT":
                            record_vector(sat.model)
                        queue.append(
                            _SymState(
                                block_id=target_id,
                                prev_block_id=blk.id,
                                env=env,
                                tainted=tainted,
                                constraints=nxt_constraints,
                                trace=st.trace + [target_id],
                                depth=st.depth + 1,
                            )
                        )
                    else:
                        res.infeasible_pruned += 1
                        if (blk.id, target_id) not in branch_outcomes:
                            branch_outcomes[(blk.id, target_id)] = False

            elif isinstance(ins, JumpOp):
                if st.depth < max_depth and st.trace.count(ins.target) < 3:
                    reached_blocks.add(ins.target)
                    queue.append(
                        _SymState(
                            block_id=ins.target,
                            prev_block_id=blk.id,
                            env=env,
                            tainted=tainted,
                            constraints=constraints,
                            trace=st.trace + [ins.target],
                            depth=st.depth + 1,
                        )
                    )
                else:
                    unroll_capped_blocks.add(blk.id)
                    unroll_capped_blocks.add(ins.target)

            elif isinstance(ins, ReturnOp):
                res.feasible_paths += 1
                if constraints:
                    res.smt_queries += 1
                    sat = solver.solve(constraints)
                    if sat.status == "SAT":
                        record_vector(sat.model)

    # Compute UNSAT dead branches & unreachable blocks (excluding synthetic if_join artifacts)
    incoming_blocks: Dict[int, Set[int]] = {bid: set() for bid in fn.blocks}
    for b_id, b_obj in fn.blocks.items():
        for s in b_obj.succs:
            if s in incoming_blocks:
                incoming_blocks[s].add(b_id)
        if b_obj.instructions:
            last = b_obj.instructions[-1]
            if isinstance(last, CondBranchOp):
                for t in (last.true_target, last.false_target):
                    if t in incoming_blocks:
                        incoming_blocks[t].add(b_id)
            elif isinstance(last, JumpOp) and last.target in incoming_blocks:
                incoming_blocks[last.target].add(b_id)

    def _is_synthetic_if_join(blk_obj: BasicBlock) -> bool:
        return (
            blk_obj.id != fn.entry_id
            and blk_obj.label.startswith("if_join_")
            and not incoming_blocks.get(blk_obj.id)
            and not blk_obj.succs
            and len(blk_obj.instructions) == 1
            and isinstance(blk_obj.instructions[0], ReturnOp)
            and blk_obj.instructions[0].value is None
        )

    budget_exhausted = bool(queue)

    # Step 1: Proven UNSAT conditional edges
    for (src_id, dst_id), was_feasible in sorted(branch_outcomes.items()):
        if not was_feasible and src_id not in unroll_capped_blocks:
            res.dead_edges.add((src_id, dst_id))
            line_no, bkind, cond_str = branch_meta.get(
                (src_id, dst_id), (fn.line_start, "true", "")
            )
            if bkind == "true":
                reason = (
                    f"Nhánh TRUE (dòng {line_no}) không thể đạt được (UNSAT): "
                    f"điều kiện '{cond_str}' mâu thuẫn với ràng buộc đường dẫn trước đó."
                )
            else:
                reason = (
                    f"Nhánh FALSE (dòng {line_no}) không thể đạt được (UNSAT): "
                    f"phủ định của '{cond_str}' mâu thuẫn với ràng buộc đường dẫn trước đó."
                )
            res.dead_branches.append(
                DeadBranchInfo(
                    block_id=src_id,
                    target_block_id=dst_id,
                    line=line_no,
                    branch_kind=bkind,
                    condition=cond_str,
                    reason=reason,
                ).to_dict()
            )
            if (
                dst_id in fn.blocks
                and dst_id not in reached_blocks
                and not _is_synthetic_if_join(fn.blocks[dst_id])
            ):
                res.dead_block_ids.add(dst_id)

    # Step 2: Unreached / transitive dead blocks
    if not budget_exhausted and not unroll_capped_blocks:
        for bid, blk_obj in sorted(fn.blocks.items()):
            if bid not in reached_blocks and not _is_synthetic_if_join(blk_obj):
                res.dead_block_ids.add(bid)
    else:
        changed_dead = True
        while changed_dead:
            changed_dead = False
            for bid, blk_obj in sorted(fn.blocks.items()):
                if bid in res.dead_block_ids or bid in reached_blocks:
                    continue
                if _is_synthetic_if_join(blk_obj):
                    continue
                preds = incoming_blocks.get(bid, set())
                if (not preds and bid != fn.entry_id) or (
                    preds and preds.issubset(res.dead_block_ids)
                ):
                    res.dead_block_ids.add(bid)
                    changed_dead = True

    # Step 3: Dead outgoing edges from dead blocks & "unreachable" entries
    for bid in sorted(res.dead_block_ids):
        blk_obj = fn.blocks[bid]
        succ_targets: List[int] = list(blk_obj.succs)
        if blk_obj.instructions:
            last = blk_obj.instructions[-1]
            if isinstance(last, CondBranchOp):
                succ_targets.extend([last.true_target, last.false_target])
            elif isinstance(last, JumpOp):
                succ_targets.append(last.target)
        for s in succ_targets:
            if (
                s in fn.blocks
                and s not in reached_blocks
                and not _is_synthetic_if_join(fn.blocks[s])
            ):
                res.dead_edges.add((bid, s))

    covered_targets = {d["target_block_id"] for d in res.dead_branches}
    for bid in sorted(res.dead_block_ids):
        if bid not in covered_targets:
            blk_obj = fn.blocks[bid]
            ln = (
                blk_obj.instructions[0].line
                if blk_obj.instructions and blk_obj.instructions[0].line
                else fn.line_start
            )
            res.dead_branches.append(
                DeadBranchInfo(
                    block_id=bid,
                    target_block_id=bid,
                    line=ln,
                    branch_kind="unreachable",
                    condition="",
                    reason=(
                        f"Khối lệnh B{bid} ({blk_obj.label}) không thể tiếp cận "
                        f"từ bất kỳ đường chạy khả thi nào (UNSAT)."
                    ),
                ).to_dict()
            )

    if not res.synthesized_test_vectors and param_names:
        res.synthesized_test_vectors.append({p: 1 for p in param_names})
    return res
