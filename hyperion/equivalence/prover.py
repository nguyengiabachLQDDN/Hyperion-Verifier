"""Kiểm chứng tương đương ngữ nghĩa giữa Hàm Cũ và Hàm Mới bằng Unified SSA IR, DPLL(T) và IRInterpreter."""

from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Set, Tuple

from hyperion.frontends.python_lifter import lift_python_source
from hyperion.frontends.ts_dsl_parser import parse_ts_dsl_source
from hyperion.ir.optimizer import optimize_function_ssa
from hyperion.ir.ssa import (
    ArrayLoadOp,
    ArrayStoreOp,
    AssertOp,
    AssignOp,
    BinaryOp,
    CallOp,
    CondBranchOp,
    Const,
    IRFunction,
    IRModule,
    IRValue,
    JumpOp,
    PhiOp,
    ReturnOp,
    SSAVar,
    SinkOp,
    UnaryOp,
)
from hyperion.mutation.engine import IRInterpreter, VMOutcome
from hyperion.solver.dpll_smt import (
    DPLLTSolver,
    SymBinOp,
    SymConst,
    SymExpr,
    SymNot,
    SymVar,
)

_CMP_OPS = {"==", "!=", "<", "<=", ">", ">="}
_NEG_CMP = {"==": "!=", "!=": "==", "<": ">=", ">=": "<", "<=": ">", ">": "<="}
_FLIP_CMP = {"==": "==", "!=": "!=", "<": ">", ">": "<", "<=": ">=", ">=": "<="}
_BOOL_OPS = _CMP_OPS | {"and", "or"}


@dataclass
class PathSummary:
    constraints: List[SymExpr]
    ret_expr: Optional[SymExpr] = None
    is_void_return: bool = False
    is_trap: bool = False
    trap_kind: str = ""
    trace: List[int] = field(default_factory=list)


@dataclass
class _ExtractionMeta:
    hit_bound: bool = False
    solver_unknown: bool = False
    has_opaque_ops: bool = False
    has_float_div: bool = False
    smt_queries: int = 0


@dataclass
class _SymState:
    block_id: int
    prev_block_id: Optional[int]
    inst_idx: int
    env: Dict[str, SymExpr]
    alloc_arrays: Dict[str, int]
    array_elems: Dict[str, Optional[List[SymExpr]]]
    constraints: List[SymExpr]
    trace: List[int]
    depth: int = 0


def _to_sym(val: IRValue, env: Dict[str, SymExpr], side_tag: str) -> SymExpr:
    if isinstance(val, Const):
        if isinstance(val.value, bool):
            return SymConst(1 if val.value else 0)
        if isinstance(val.value, (int, float)):
            return SymConst(int(val.value))
        return SymConst(len(str(val.value)))
    if isinstance(val, SSAVar):
        if val.key() in env:
            return env[val.key()]
        return SymVar(f"{side_tag}:{val.key()}")
    return SymConst(0)


def _is_bool_like(expr: SymExpr) -> bool:
    if isinstance(expr, SymNot):
        return True
    if isinstance(expr, SymBinOp) and expr.op in _BOOL_OPS:
        return True
    return False


def _simplify_sym_expr(expr: SymExpr) -> SymExpr:
    if isinstance(expr, (SymVar, SymConst)):
        return expr
    if isinstance(expr, SymNot):
        inner = _simplify_sym_expr(expr.expr)
        if isinstance(inner, SymConst):
            return SymConst(0 if inner.value else 1)
        if isinstance(inner, SymNot):
            return inner.expr
        if isinstance(inner, SymBinOp) and inner.op in _NEG_CMP:
            return _simplify_sym_expr(SymBinOp(_NEG_CMP[inner.op], inner.left, inner.right))
        return SymNot(inner)
    if isinstance(expr, SymBinOp):
        l = _simplify_sym_expr(expr.left)
        r = _simplify_sym_expr(expr.right)
        op = expr.op
        if isinstance(l, SymConst) and isinstance(r, SymConst):
            a, b = l.value, r.value
            if op == "+":
                return SymConst(a + b)
            if op == "-":
                return SymConst(a - b)
            if op == "*":
                return SymConst(a * b)
            if op == "//" and b != 0:
                return SymConst(a // b)
            if op == "/" and b != 0 and a % b == 0:
                return SymConst(a // b)
            if op == "%" and b != 0:
                return SymConst(a % b)
            if op == "&":
                return SymConst(a & b)
            if op == "|":
                return SymConst(a | b)
            if op == "^":
                return SymConst(a ^ b)
            if op == "<<":
                return SymConst(a << max(0, min(b, 16)))
            if op == ">>":
                return SymConst(a >> max(0, min(b, 16)))
            if op == "==":
                return SymConst(1 if a == b else 0)
            if op == "!=":
                return SymConst(1 if a != b else 0)
            if op == "<":
                return SymConst(1 if a < b else 0)
            if op == "<=":
                return SymConst(1 if a <= b else 0)
            if op == ">":
                return SymConst(1 if a > b else 0)
            if op == ">=":
                return SymConst(1 if a >= b else 0)
            if op == "and":
                return SymConst(1 if (a != 0 and b != 0) else 0)
            if op == "or":
                return SymConst(1 if (a != 0 or b != 0) else 0)

        if op == "+" and isinstance(l, SymConst) and isinstance(r, SymVar):
            l, r = r, l
        if op in ("+", "-") and isinstance(r, SymConst) and r.value == 0:
            return l
        if op == "*":
            if (isinstance(l, SymConst) and l.value == 0) or (isinstance(r, SymConst) and r.value == 0):
                return SymConst(0)
            if isinstance(r, SymConst) and r.value == 1:
                return l
            if isinstance(l, SymConst) and l.value == 1:
                return r
        if op in _CMP_OPS:
            if isinstance(l, SymConst) and isinstance(r, SymVar):
                l, r, op = r, l, _FLIP_CMP[op]
            if (
                isinstance(l, SymBinOp)
                and l.op == "-"
                and isinstance(l.left, SymConst)
                and l.left.value == 0
                and isinstance(l.right, SymVar)
                and isinstance(r, SymConst)
            ):
                return SymBinOp(_FLIP_CMP[op], l.right, SymConst(-r.value))
        return SymBinOp(op, l, r)
    return expr


def _to_dnf(expr: SymExpr, max_branches: int = 8) -> List[List[SymExpr]]:
    s = _simplify_sym_expr(expr)
    if isinstance(s, SymBinOp) and s.op == "and":
        left_b = _to_dnf(s.left, max_branches)
        right_b = _to_dnf(s.right, max_branches)
        out: List[List[SymExpr]] = []
        for lb in left_b:
            for rb in right_b:
                out.append(lb + rb)
                if len(out) >= max_branches:
                    return out
        return out
    if isinstance(s, SymBinOp) and s.op == "or":
        out = _to_dnf(s.left, max_branches) + _to_dnf(s.right, max_branches)
        return out[:max_branches]
    if isinstance(s, SymNot) and isinstance(s.expr, SymBinOp):
        if s.expr.op == "and":
            out = _to_dnf(SymNot(s.expr.left), max_branches) + _to_dnf(SymNot(s.expr.right), max_branches)
            return out[:max_branches]
        if s.expr.op == "or":
            left_b = _to_dnf(SymNot(s.expr.left), max_branches)
            right_b = _to_dnf(SymNot(s.expr.right), max_branches)
            out = []
            for lb in left_b:
                for rb in right_b:
                    out.append(lb + rb)
                    if len(out) >= max_branches:
                        return out
            return out
    return [[s]]


def _expand_disjunctions(constraints: List[SymExpr], max_branches: int = 8) -> List[List[SymExpr]]:
    branches: List[List[SymExpr]] = [[]]
    for c in constraints:
        dnf = _to_dnf(c, max_branches=max_branches)
        nxt: List[List[SymExpr]] = []
        for base in branches:
            for part in dnf:
                merged = base + part
                if any(isinstance(atom, SymConst) and atom.value == 0 for atom in merged):
                    continue
                nxt.append([atom for atom in merged if not (isinstance(atom, SymConst) and atom.value != 0)])
                if len(nxt) >= max_branches:
                    break
            if len(nxt) >= max_branches:
                break
        branches = nxt
        if not branches:
            return []
    return branches


def _solve_constraints(
    solver: DPLLTSolver,
    constraints: List[SymExpr],
    max_steps: int = 360,
) -> Tuple[str, Optional[Dict[str, int]], int]:
    """Solve DNF-expanded constraints, returning (status, model, smt_queries_used)."""
    branches = _expand_disjunctions(constraints, max_branches=8)
    if not branches:
        return "UNSAT", None, 0

    queries = 0
    saw_unknown = False
    for branch in branches:
        if not branch:
            return "SAT", {}, queries
        queries += 1
        res = solver.solve(branch, max_steps=max_steps)
        if res.status == "SAT":
            return "SAT", res.model, queries
        if res.status == "UNKNOWN":
            saw_unknown = True
    return ("UNKNOWN" if saw_unknown else "UNSAT"), None, queries


def _extract_path_summaries(
    fn: IRFunction,
    canon_params: List[str],
    side_tag: str,
    solver: DPLLTSolver,
    max_paths: int = 64,
    max_depth: int = 24,
    max_unroll: int = 3,
) -> Tuple[List[PathSummary], _ExtractionMeta]:
    meta = _ExtractionMeta()
    if not fn.blocks or fn.entry_id not in fn.blocks:
        return [], meta

    init_env: Dict[str, SymExpr] = {
        p.key(): SymVar(cp) for p, cp in zip(fn.params, canon_params)
    }
    queue: List[_SymState] = [
        _SymState(
            block_id=fn.entry_id,
            prev_block_id=None,
            inst_idx=0,
            env=init_env,
            alloc_arrays={},
            array_elems={},
            constraints=[],
            trace=[fn.entry_id],
            depth=0,
        )
    ]
    summaries: List[PathSummary] = []
    explored = 0

    while queue and explored < max_paths:
        st = queue.pop(0)
        explored += 1
        blk = fn.blocks[st.block_id]
        env = dict(st.env)
        alloc_arrays = dict(st.alloc_arrays)
        array_elems: Dict[str, Optional[List[SymExpr]]] = {
            k: (list(v) if v is not None else None) for k, v in st.array_elems.items()
        }
        constraints = list(st.constraints)
        terminated = False

        for idx in range(st.inst_idx, len(blk.instructions)):
            ins = blk.instructions[idx]

            if isinstance(ins, PhiOp):
                chosen: Optional[IRValue] = None
                if st.prev_block_id is not None:
                    for pb, pv in ins.incomings:
                        if pb == st.prev_block_id:
                            chosen = pv
                            break
                if chosen is None and ins.incomings:
                    chosen = ins.incomings[0][1]
                if ins.dest is not None:
                    if chosen is not None:
                        env[ins.dest.key()] = _to_sym(chosen, env, side_tag)
                        if isinstance(chosen, SSAVar) and chosen.key() in alloc_arrays:
                            alloc_arrays[ins.dest.key()] = alloc_arrays[chosen.key()]
                            elems = array_elems.get(chosen.key())
                            array_elems[ins.dest.key()] = list(elems) if elems is not None else None
                    else:
                        env[ins.dest.key()] = SymConst(0)

            elif isinstance(ins, AssignOp):
                if ins.dest is not None:
                    env[ins.dest.key()] = _to_sym(ins.src, env, side_tag)
                    if isinstance(ins.src, SSAVar) and ins.src.key() in alloc_arrays:
                        alloc_arrays[ins.dest.key()] = alloc_arrays[ins.src.key()]
                        elems = array_elems.get(ins.src.key())
                        array_elems[ins.dest.key()] = list(elems) if elems is not None else None

            elif isinstance(ins, UnaryOp):
                if ins.dest is not None:
                    opd = _to_sym(ins.operand, env, side_tag)
                    if ins.op in ("not", "!"):
                        env[ins.dest.key()] = SymNot(opd)
                    elif ins.op == "-":
                        env[ins.dest.key()] = _simplify_sym_expr(SymBinOp("-", SymConst(0), opd))
                    elif ins.op == "~":
                        env[ins.dest.key()] = SymBinOp("-", SymConst(-1), opd)
                    else:
                        env[ins.dest.key()] = opd

            elif isinstance(ins, BinaryOp):
                l_sym = _to_sym(ins.left, env, side_tag)
                r_sym = _to_sym(ins.right, env, side_tag)
                if ins.op in ("/", "//", "%"):
                    trap_c = constraints + [SymBinOp("==", r_sym, SymConst(0))]
                    st_trap, _, q = _solve_constraints(solver, trap_c, max_steps=160)
                    meta.smt_queries += q
                    if st_trap == "UNKNOWN":
                        meta.solver_unknown = True
                    if st_trap in ("SAT", "UNKNOWN"):
                        summaries.append(
                            PathSummary(
                                constraints=trap_c,
                                is_trap=True,
                                trap_kind="DIV_BY_ZERO",
                                trace=list(st.trace),
                            )
                        )
                    constraints = constraints + [SymBinOp("!=", r_sym, SymConst(0))]
                    if ins.op == "/":
                        ls = _simplify_sym_expr(l_sym)
                        rs = _simplify_sym_expr(r_sym)
                        if not (isinstance(ls, SymConst) and isinstance(rs, SymConst) and rs.value != 0 and ls.value % rs.value == 0):
                            meta.has_float_div = True
                elif ins.op == "**":
                    meta.has_opaque_ops = True
                if ins.dest is not None:
                    env[ins.dest.key()] = _simplify_sym_expr(SymBinOp(ins.op, l_sym, r_sym))

            elif isinstance(ins, CallOp):
                if ins.callee == "select" and len(ins.args) == 3 and ins.dest is not None:
                    cond_s = _simplify_sym_expr(_to_sym(ins.args[0], env, side_tag))
                    t_s = _to_sym(ins.args[1], env, side_tag)
                    f_s = _to_sym(ins.args[2], env, side_tag)
                    if isinstance(cond_s, SymConst):
                        env[ins.dest.key()] = t_s if cond_s.value != 0 else f_s
                    else:
                        # Fork false branch from next instruction in the same block
                        false_c = constraints + [SymNot(cond_s)]
                        st_f, _, q_f = _solve_constraints(solver, false_c, max_steps=160)
                        meta.smt_queries += q_f
                        if st_f == "UNKNOWN":
                            meta.solver_unknown = True
                        if st_f in ("SAT", "UNKNOWN"):
                            f_env = dict(env)
                            f_env[ins.dest.key()] = f_s
                            queue.append(
                                _SymState(
                                    block_id=blk.id,
                                    prev_block_id=st.prev_block_id,
                                    inst_idx=idx + 1,
                                    env=f_env,
                                    alloc_arrays=dict(alloc_arrays),
                                    array_elems={
                                        k: (list(v) if v is not None else None)
                                        for k, v in array_elems.items()
                                    },
                                    constraints=false_c,
                                    trace=list(st.trace),
                                    depth=st.depth,
                                )
                            )
                        true_c = constraints + [cond_s]
                        st_t, _, q_t = _solve_constraints(solver, true_c, max_steps=160)
                        meta.smt_queries += q_t
                        if st_t == "UNKNOWN":
                            meta.solver_unknown = True
                        if st_t == "UNSAT":
                            terminated = True
                            break
                        constraints = true_c
                        env[ins.dest.key()] = t_s

                elif ins.callee == "alloc_array" and ins.args and ins.dest is not None:
                    sz_sym = _simplify_sym_expr(_to_sym(ins.args[0], env, side_tag))
                    sz = max(0, min(sz_sym.value, 256)) if isinstance(sz_sym, SymConst) else 0
                    alloc_arrays[ins.dest.key()] = sz
                    array_elems[ins.dest.key()] = [SymConst(0)] * sz if sz <= 16 else None
                    env[ins.dest.key()] = SymConst(0)
                elif ins.callee == "len" and ins.args and ins.dest is not None:
                    arg0 = ins.args[0]
                    if isinstance(arg0, SSAVar) and arg0.key() in alloc_arrays:
                        env[ins.dest.key()] = SymConst(alloc_arrays[arg0.key()])
                    else:
                        meta.has_opaque_ops = True
                        env[ins.dest.key()] = SymConst(0)
                elif ins.dest is not None:
                    meta.has_opaque_ops = True
                    env[ins.dest.key()] = SymVar(f"{side_tag}:{ins.dest.key()}")
                else:
                    meta.has_opaque_ops = True

            elif isinstance(ins, ArrayLoadOp):
                idx_sym = _to_sym(ins.index, env, side_tag)
                arr_key = ins.array.key() if isinstance(ins.array, SSAVar) else ""
                arr_len = alloc_arrays.get(arr_key)
                if arr_len is not None:
                    for oob_c in (
                        SymBinOp("<", idx_sym, SymConst(0)),
                        SymBinOp(">=", idx_sym, SymConst(arr_len)),
                    ):
                        trap_c = constraints + [oob_c]
                        st_trap, _, q = _solve_constraints(solver, trap_c, max_steps=160)
                        meta.smt_queries += q
                        if st_trap == "UNKNOWN":
                            meta.solver_unknown = True
                        if st_trap in ("SAT", "UNKNOWN"):
                            summaries.append(
                                PathSummary(
                                    constraints=trap_c,
                                    is_trap=True,
                                    trap_kind="BUFFER_OOB",
                                    trace=list(st.trace),
                                )
                            )
                    constraints = constraints + [
                        SymBinOp(">=", idx_sym, SymConst(0)),
                        SymBinOp("<", idx_sym, SymConst(arr_len)),
                    ]
                    if ins.dest is not None:
                        elems = array_elems.get(arr_key)
                        idx_simple = _simplify_sym_expr(idx_sym)
                        if elems is not None and isinstance(idx_simple, SymConst) and 0 <= idx_simple.value < len(elems):
                            env[ins.dest.key()] = elems[idx_simple.value]
                        else:
                            meta.has_opaque_ops = True
                            env[ins.dest.key()] = SymVar(f"{side_tag}:{ins.dest.key()}")
                else:
                    meta.has_opaque_ops = True
                    if ins.dest is not None:
                        env[ins.dest.key()] = idx_sym

            elif isinstance(ins, ArrayStoreOp):
                idx_sym = _to_sym(ins.index, env, side_tag)
                arr_key = ins.array.key() if isinstance(ins.array, SSAVar) else ""
                arr_len = alloc_arrays.get(arr_key)
                if arr_len is not None:
                    for oob_c in (
                        SymBinOp("<", idx_sym, SymConst(0)),
                        SymBinOp(">=", idx_sym, SymConst(arr_len)),
                    ):
                        trap_c = constraints + [oob_c]
                        st_trap, _, q = _solve_constraints(solver, trap_c, max_steps=160)
                        meta.smt_queries += q
                        if st_trap == "UNKNOWN":
                            meta.solver_unknown = True
                        if st_trap in ("SAT", "UNKNOWN"):
                            summaries.append(
                                PathSummary(
                                    constraints=trap_c,
                                    is_trap=True,
                                    trap_kind="BUFFER_OOB",
                                    trace=list(st.trace),
                                )
                            )
                    constraints = constraints + [
                        SymBinOp(">=", idx_sym, SymConst(0)),
                        SymBinOp("<", idx_sym, SymConst(arr_len)),
                    ]
                    elems = array_elems.get(arr_key)
                    idx_simple = _simplify_sym_expr(idx_sym)
                    if elems is not None and isinstance(idx_simple, SymConst) and 0 <= idx_simple.value < len(elems):
                        elems[idx_simple.value] = _to_sym(ins.value, env, side_tag)
                    else:
                        array_elems[arr_key] = None
                else:
                    meta.has_opaque_ops = True

            elif isinstance(ins, AssertOp):
                cond_sym = _to_sym(ins.cond, env, side_tag)
                trap_c = constraints + [SymNot(cond_sym)]
                st_trap, _, q = _solve_constraints(solver, trap_c, max_steps=160)
                meta.smt_queries += q
                if st_trap == "UNKNOWN":
                    meta.solver_unknown = True
                if st_trap in ("SAT", "UNKNOWN"):
                    summaries.append(
                        PathSummary(
                            constraints=trap_c,
                            is_trap=True,
                            trap_kind="ASSERTION_VIOLATION",
                            trace=list(st.trace),
                        )
                    )
                constraints = constraints + [cond_sym]

            elif isinstance(ins, SinkOp):
                meta.has_opaque_ops = True
                if ins.dest is not None:
                    env[ins.dest.key()] = SymConst(1)

            elif isinstance(ins, CondBranchOp):
                terminated = True
                if st.depth >= max_depth:
                    meta.hit_bound = True
                    break
                cond_sym = _to_sym(ins.cond, env, side_tag)
                for take_true, target_id in ((True, ins.true_target), (False, ins.false_target)):
                    branch_c = cond_sym if take_true else SymNot(cond_sym)
                    nxt_c = constraints + [branch_c]
                    st_br, _, q = _solve_constraints(solver, nxt_c, max_steps=160)
                    meta.smt_queries += q
                    if st_br == "UNKNOWN":
                        meta.solver_unknown = True
                    if st_br == "UNSAT":
                        continue
                    if st.trace.count(target_id) >= max_unroll:
                        meta.hit_bound = True
                        continue
                    queue.append(
                        _SymState(
                            block_id=target_id,
                            prev_block_id=blk.id,
                            inst_idx=0,
                            env=env,
                            alloc_arrays=alloc_arrays,
                            array_elems=array_elems,
                            constraints=nxt_c,
                            trace=st.trace + [target_id],
                            depth=st.depth + 1,
                        )
                    )
                break

            elif isinstance(ins, JumpOp):
                terminated = True
                if st.depth >= max_depth or st.trace.count(ins.target) >= max_unroll:
                    meta.hit_bound = True
                    break
                queue.append(
                    _SymState(
                        block_id=ins.target,
                        prev_block_id=blk.id,
                        inst_idx=0,
                        env=env,
                        alloc_arrays=alloc_arrays,
                        array_elems=array_elems,
                        constraints=constraints,
                        trace=st.trace + [ins.target],
                        depth=st.depth + 1,
                    )
                )
                break

            elif isinstance(ins, ReturnOp):
                terminated = True
                ret_e = None if ins.value is None else _to_sym(ins.value, env, side_tag)
                summaries.append(
                    PathSummary(
                        constraints=constraints,
                        ret_expr=ret_e,
                        is_void_return=(ins.value is None),
                        is_trap=False,
                        trace=list(st.trace),
                    )
                )
                break

        if not terminated:
            summaries.append(
                PathSummary(
                    constraints=constraints,
                    ret_expr=None,
                    is_void_return=True,
                    is_trap=False,
                    trace=list(st.trace),
                )
            )

    if queue:
        meta.hit_bound = True
    return summaries, meta


# ---------------------------------------------------------------------------
# Equality substitution & sparse polynomial canonicalization
# ---------------------------------------------------------------------------

Poly = Dict[Tuple[str, ...], int]


def _poly_add(a: Poly, b: Poly, sign: int = 1) -> Poly:
    out = dict(a)
    for k, v in b.items():
        nv = out.get(k, 0) + sign * v
        if nv == 0:
            out.pop(k, None)
        else:
            out[k] = nv
    return out


def _poly_mul(a: Poly, b: Poly, max_terms: int = 64, max_deg: int = 4) -> Optional[Poly]:
    out: Poly = {}
    for ka, va in a.items():
        for kb, vb in b.items():
            if len(ka) + len(kb) > max_deg:
                return None
            k = tuple(sorted(ka + kb))
            nv = out.get(k, 0) + va * vb
            if nv == 0:
                out.pop(k, None)
            else:
                out[k] = nv
            if len(out) > max_terms:
                return None
    return out


def _extract_equalities(constraints: List[SymExpr]) -> Dict[str, SymExpr]:
    """Extract canonical substitutions `var -> const` or `var -> rep_var` from constraints."""
    parent: Dict[str, str] = {}
    const_val: Dict[str, int] = {}

    def find(x: str) -> str:
        while parent.get(x, x) != x:
            parent[x] = parent.get(parent[x], parent[x])
            x = parent[x]
        return x

    def union(a: str, b: str) -> None:
        ra, rb = find(a), find(b)
        if ra == rb:
            return
        # Prefer canonical parameter names `p0, p1, ...` as root
        if rb.startswith("p") and not ra.startswith("p"):
            ra, rb = rb, ra
        elif ra > rb and not (ra.startswith("p") and not rb.startswith("p")):
            ra, rb = rb, ra
        parent[rb] = ra
        if rb in const_val and ra not in const_val:
            const_val[ra] = const_val[rb]

    for branch_c in constraints:
        s = _simplify_sym_expr(branch_c)
        stack = [s]
        while stack:
            cur = stack.pop()
            if isinstance(cur, SymBinOp) and cur.op == "and":
                stack.append(cur.left)
                stack.append(cur.right)
                continue
            if isinstance(cur, SymBinOp) and cur.op == "==":
                if isinstance(cur.left, SymVar) and isinstance(cur.right, SymConst):
                    const_val[find(cur.left.name)] = cur.right.value
                elif isinstance(cur.left, SymConst) and isinstance(cur.right, SymVar):
                    const_val[find(cur.right.name)] = cur.left.value
                elif isinstance(cur.left, SymVar) and isinstance(cur.right, SymVar):
                    union(cur.left.name, cur.right.name)

    subs: Dict[str, SymExpr] = {}
    all_vars = set(parent.keys()) | set(const_val.keys())
    for v in all_vars:
        root = find(v)
        if root in const_val:
            subs[v] = SymConst(const_val[root])
        elif root != v:
            subs[v] = SymVar(root)
    return subs


def _subst_sym(expr: SymExpr, subs: Dict[str, SymExpr]) -> SymExpr:
    if isinstance(expr, SymVar):
        return subs.get(expr.name, expr)
    if isinstance(expr, SymConst):
        return expr
    if isinstance(expr, SymNot):
        return SymNot(_subst_sym(expr.expr, subs))
    if isinstance(expr, SymBinOp):
        return SymBinOp(expr.op, _subst_sym(expr.left, subs), _subst_sym(expr.right, subs))
    return expr


def _to_poly(expr: SymExpr) -> Optional[Poly]:
    if isinstance(expr, SymConst):
        return {(): int(expr.value)} if expr.value != 0 else {}
    if isinstance(expr, SymVar):
        return {(expr.name,): 1}
    if isinstance(expr, SymBinOp):
        if expr.op in ("+", "-", "*"):
            lp = _to_poly(expr.left)
            rp = _to_poly(expr.right)
            if lp is None or rp is None:
                return None
            if expr.op == "+":
                return _poly_add(lp, rp, 1)
            if expr.op == "-":
                return _poly_add(lp, rp, -1)
            return _poly_mul(lp, rp)
    return None


def _collect_int_constants(fn: IRFunction) -> List[int]:
    vals: Set[int] = set()
    for blk in fn.blocks.values():
        for ins in blk.instructions:
            for v in ins.uses():
                if isinstance(v, Const) and isinstance(v.value, int) and not isinstance(v.value, bool):
                    if abs(v.value) <= 100000:
                        vals.add(int(v.value))
            if isinstance(ins, AssignOp) and isinstance(ins.src, Const):
                if isinstance(ins.src.value, int) and not isinstance(ins.src.value, bool):
                    if abs(ins.src.value) <= 100000:
                        vals.add(int(ins.src.value))
    return sorted(vals)


def _fmt_vm_output(out: VMOutcome) -> Dict[str, Any]:
    return {
        "status": out.status,
        "return_value": out.return_value,
        "error": out.error,
    }


def _build_counterexample(
    old_ir: IRFunction,
    new_ir: IRFunction,
    vals: List[int],
    o_out: VMOutcome,
    n_out: VMOutcome,
) -> Dict[str, Any]:
    old_inputs = {p.name: v for p, v in zip(old_ir.params, vals)}
    new_inputs = {p.name: v for p, v in zip(new_ir.params, vals)}
    return {
        "inputs": old_inputs,
        "new_inputs": new_inputs,
        "old_output": _fmt_vm_output(o_out),
        "new_output": _fmt_vm_output(n_out),
        "old_status": o_out.status,
        "new_status": n_out.status,
    }


def _select_fn(mod: IRModule, fn_name: Optional[str]) -> Optional[IRFunction]:
    if not mod.functions:
        return None
    if not fn_name:
        return mod.functions[0]
    for f in mod.functions:
        if f.name == fn_name or f.name.endswith(f".{fn_name}"):
            return f
    return None


def prove_equivalence(
    old_code: str,
    new_code: str,
    language: str = "python",
    old_fn: Optional[str] = None,
    new_fn: Optional[str] = None,
) -> Dict[str, Any]:
    """Kiểm chứng tương đương ngữ nghĩa giữa Hàm Cũ và Hàm Mới trên Unified SSA IR."""
    lang = (language or "python").strip().lower()
    if lang not in ("python", "py", "typescript", "ts", "javascript", "js"):
        return {
            "equivalent": False,
            "status": "ERROR",
            "summary": f"Ngôn ngữ không được hỗ trợ: '{language}'. Chỉ hỗ trợ python hoặc typescript/javascript.",
            "old_function": old_fn or "",
            "new_function": new_fn or "",
            "params": [],
            "counterexample": None,
            "smt_queries": 0,
            "paths_checked": 0,
            "parse_errors": [f"Unsupported language: {language}"],
        }

    is_py = lang in ("python", "py")
    parse_errors: List[str] = []
    if not (old_code or "").strip():
        parse_errors.append("Mã nguồn Hàm Cũ đang trống.")
    if not (new_code or "").strip():
        parse_errors.append("Mã nguồn Hàm Mới đang trống.")
    if parse_errors:
        return {
            "equivalent": False,
            "status": "ERROR",
            "summary": " ".join(parse_errors),
            "old_function": old_fn or "",
            "new_function": new_fn or "",
            "params": [],
            "counterexample": None,
            "smt_queries": 0,
            "paths_checked": 0,
            "parse_errors": parse_errors,
        }

    old_mod = (
        lift_python_source(old_code, "old_module", "<old>.py")
        if is_py
        else parse_ts_dsl_source(old_code, "old_module", "<old>.ts")
    )
    new_mod = (
        lift_python_source(new_code, "new_module", "<new>.py")
        if is_py
        else parse_ts_dsl_source(new_code, "new_module", "<new>.ts")
    )

    parse_errors.extend(old_mod.parse_errors)
    parse_errors.extend(new_mod.parse_errors)
    if not old_mod.functions:
        parse_errors.append("Không tìm thấy định nghĩa hàm hợp lệ trong Hàm Cũ.")
    if not new_mod.functions:
        parse_errors.append("Không tìm thấy định nghĩa hàm hợp lệ trong Hàm Mới.")

    if parse_errors:
        return {
            "equivalent": False,
            "status": "ERROR",
            "summary": f"Lỗi phân tích cú pháp khi nâng lên SSA IR: {'; '.join(parse_errors)}",
            "old_function": old_fn or "",
            "new_function": new_fn or "",
            "params": [],
            "counterexample": None,
            "smt_queries": 0,
            "paths_checked": 0,
            "parse_errors": parse_errors,
        }

    old_ir = _select_fn(old_mod, old_fn)
    new_ir = _select_fn(new_mod, new_fn)
    if old_ir is None or new_ir is None:
        missing = []
        if old_ir is None:
            missing.append(f"Không tìm thấy hàm '{old_fn}' trong Hàm Cũ")
        if new_ir is None:
            missing.append(f"Không tìm thấy hàm '{new_fn}' trong Hàm Mới")
        return {
            "equivalent": False,
            "status": "ERROR",
            "summary": "; ".join(missing) + ".",
            "old_function": old_fn or (old_mod.functions[0].name if old_mod.functions else ""),
            "new_function": new_fn or (new_mod.functions[0].name if new_mod.functions else ""),
            "params": [],
            "counterexample": None,
            "smt_queries": 0,
            "paths_checked": 0,
            "parse_errors": missing,
        }

    optimize_function_ssa(old_ir)
    optimize_function_ssa(new_ir)

    public_params = [p.name for p in old_ir.params]
    if len(old_ir.params) != len(new_ir.params):
        return {
            "equivalent": False,
            "status": "ERROR",
            "summary": (
                f"Số lượng tham số không khớp giữa '{old_ir.name}' ({len(old_ir.params)} tham số) "
                f"và '{new_ir.name}' ({len(new_ir.params)} tham số)."
            ),
            "old_function": old_ir.name,
            "new_function": new_ir.name,
            "params": public_params,
            "counterexample": None,
            "smt_queries": 0,
            "paths_checked": 0,
            "parse_errors": [],
        }

    arity = len(old_ir.params)
    canon_params = [f"p{i}" for i in range(arity)]
    vm = IRInterpreter(gas_limit=4000)

    def check_concrete(vals: List[int]) -> Optional[Dict[str, Any]]:
        o_args = {p.name: v for p, v in zip(old_ir.params, vals)}
        n_args = {p.name: v for p, v in zip(new_ir.params, vals)}
        o_out = vm.execute(old_ir, o_args)
        n_out = vm.execute(new_ir, n_args)
        if o_out.status != n_out.status:
            return _build_counterexample(old_ir, new_ir, vals, o_out, n_out)
        if o_out.status == "OK" and o_out.return_value != n_out.return_value:
            return _build_counterexample(old_ir, new_ir, vals, o_out, n_out)
        return None

    # Step 1: Fast differential boundary execution via IRInterpreter
    all_consts = sorted(set(_collect_int_constants(old_ir) + _collect_int_constants(new_ir)))
    pool: List[int] = []
    seen_pool: Set[int] = set()
    for base_v in (-2, -1, 0, 1, 2, 5, 10, -10, 64, -64):
        if base_v not in seen_pool:
            seen_pool.add(base_v)
            pool.append(base_v)
    for c in all_consts[:12]:
        for delta in (-1, 0, 1):
            v = c + delta
            if v not in seen_pool:
                seen_pool.add(v)
                pool.append(v)

    tuples_to_test: List[List[int]] = []
    seen_tuples: Set[Tuple[int, ...]] = set()

    def add_tuple(t: List[int]) -> None:
        if len(tuples_to_test) >= 96:
            return
        kt = tuple(t)
        if kt not in seen_tuples:
            seen_tuples.add(kt)
            tuples_to_test.append(t)

    if arity == 0:
        add_tuple([])
    elif arity == 1:
        for v in pool:
            add_tuple([v])
    else:
        for v in pool:
            add_tuple([v] * arity)
        for anchor in (0, 1, 2, -1):
            for axis in range(arity):
                for v in pool[:10]:
                    row = [anchor] * arity
                    row[axis] = v
                    add_tuple(row)
        for v1 in pool[:6]:
            for v2 in pool[:6]:
                row = [0] * arity
                row[0] = v1
                row[1] = v2
                add_tuple(row)

    for vals in tuples_to_test:
        cx = check_concrete(vals)
        if cx is not None:
            return {
                "equivalent": False,
                "status": "NON_EQUIVALENT",
                "summary": (
                    f"Phát hiện hai hàm KHÔNG tương đương qua kiểm tra biên thực tế: "
                    f"đầu vào {cx['inputs']} cho '{old_ir.name}' -> {cx['old_output']} "
                    f"nhưng '{new_ir.name}' -> {cx['new_output']}."
                ),
                "old_function": old_ir.name,
                "new_function": new_ir.name,
                "params": public_params,
                "counterexample": cx,
                "smt_queries": 0,
                "paths_checked": 0,
                "parse_errors": [],
            }

    # Step 2: Bounded symbolic path-summary extraction with dynamic bounds
    max_abs = max((abs(c) for c in all_consts), default=0)
    bound_mag = min(16384, max(128, max_abs + 32))
    solver = DPLLTSolver(default_lo=-bound_mag, default_hi=bound_mag)

    old_sums, old_meta = _extract_path_summaries(old_ir, canon_params, "old", solver)
    new_sums, new_meta = _extract_path_summaries(new_ir, canon_params, "new", solver)

    smt_queries = old_meta.smt_queries + new_meta.smt_queries
    hit_bound = old_meta.hit_bound or new_meta.hit_bound
    solver_unknown = old_meta.solver_unknown or new_meta.solver_unknown
    has_opaque_ops = old_meta.has_opaque_ops or new_meta.has_opaque_ops
    has_float_div = old_meta.has_float_div or new_meta.has_float_div
    spurious_witness_seen = False
    paths_checked = 0

    def try_differential_query(q_constraints: List[SymExpr], max_steps: int = 640) -> Optional[Dict[str, Any]]:
        nonlocal smt_queries, solver_unknown, spurious_witness_seen
        st, model, q_cnt = _solve_constraints(solver, q_constraints, max_steps=max_steps)
        smt_queries += q_cnt
        if st == "UNKNOWN":
            solver_unknown = True
            return None
        if st == "SAT" and model is not None:
            vals = [int(model.get(cp, 0)) for cp in canon_params]
            cx = check_concrete(vals)
            if cx is not None:
                return cx
            spurious_witness_seen = True
        return None

    # Step 3: Pairwise feasible path differential checking
    for s_old in old_sums:
        for s_new in new_sums:
            paths_checked += 1
            joint = s_old.constraints + s_new.constraints

            if s_old.is_trap and s_new.is_trap:
                continue
            if s_old.is_trap != s_new.is_trap:
                cx = try_differential_query(joint)
                if cx is not None:
                    return {
                        "equivalent": False,
                        "status": "NON_EQUIVALENT",
                        "summary": (
                            f"Phát hiện sai khác trạng thái ngoại lệ (TRAP vs OK): "
                            f"đầu vào {cx['inputs']} cho '{old_ir.name}' -> {cx['old_output']} "
                            f"nhưng '{new_ir.name}' -> {cx['new_output']}."
                        ),
                        "old_function": old_ir.name,
                        "new_function": new_ir.name,
                        "params": public_params,
                        "counterexample": cx,
                        "smt_queries": smt_queries,
                        "paths_checked": paths_checked,
                        "parse_errors": [],
                    }
                continue

            if s_old.is_void_return and s_new.is_void_return:
                continue
            if s_old.is_void_return != s_new.is_void_return:
                cx = try_differential_query(joint)
                if cx is not None:
                    return {
                        "equivalent": False,
                        "status": "NON_EQUIVALENT",
                        "summary": (
                            f"Phát hiện sai khác giá trị trả về (None vs có giá trị): "
                            f"đầu vào {cx['inputs']} cho '{old_ir.name}' -> {cx['old_output']} "
                            f"nhưng '{new_ir.name}' -> {cx['new_output']}."
                        ),
                        "old_function": old_ir.name,
                        "new_function": new_ir.name,
                        "params": public_params,
                        "counterexample": cx,
                        "smt_queries": smt_queries,
                        "paths_checked": paths_checked,
                        "parse_errors": [],
                    }
                continue

            assert s_old.ret_expr is not None and s_new.ret_expr is not None
            subs = _extract_equalities(joint)
            ro = _simplify_sym_expr(_subst_sym(s_old.ret_expr, subs))
            rn = _simplify_sym_expr(_subst_sym(s_new.ret_expr, subs))
            if ro == rn:
                continue

            po = _to_poly(ro)
            pn = _to_poly(rn)
            if po is not None and pn is not None:
                diff = _poly_add(po, pn, -1)
                if not diff:
                    continue  # Identical algebraic polynomials -> 0 SMT queries needed
                if len(diff) == 1 and () in diff:
                    # Difference is a non-zero constant -> just check feasibility of joint constraints
                    cx = try_differential_query(joint)
                    if cx is not None:
                        return {
                            "equivalent": False,
                            "status": "NON_EQUIVALENT",
                            "summary": (
                                f"Phát hiện hai hàm KHÔNG tương đương: đầu vào {cx['inputs']} "
                                f"cho '{old_ir.name}' -> {cx['old_output']} "
                                f"nhưng '{new_ir.name}' -> {cx['new_output']}."
                            ),
                            "old_function": old_ir.name,
                            "new_function": new_ir.name,
                            "params": public_params,
                            "counterexample": cx,
                            "smt_queries": smt_queries,
                            "paths_checked": paths_checked,
                            "parse_errors": [],
                        }
                    continue

                # Check single-variable affine difference `a * p + b != 0`
                var_terms = [(k, v) for k, v in diff.items() if len(k) == 1]
                const_term = diff.get((), 0)
                if len(diff) == len(var_terms) + (1 if () in diff else 0) and len(var_terms) == 1:
                    (vname,), coeff = var_terms[0]
                    if coeff != 0 and const_term % coeff == 0:
                        root = -const_term // coeff
                        cx = try_differential_query(joint + [SymBinOp("!=", SymVar(vname), SymConst(root))])
                        if cx is not None:
                            return {
                                "equivalent": False,
                                "status": "NON_EQUIVALENT",
                                "summary": (
                                    f"Phát hiện hai hàm KHÔNG tương đương: đầu vào {cx['inputs']} "
                                    f"cho '{old_ir.name}' -> {cx['old_output']} "
                                    f"nhưng '{new_ir.name}' -> {cx['new_output']}."
                                ),
                                "old_function": old_ir.name,
                                "new_function": new_ir.name,
                                "params": public_params,
                                "counterexample": cx,
                                "smt_queries": smt_queries,
                                "paths_checked": paths_checked,
                                "parse_errors": [],
                            }
                        continue

            if _is_bool_like(ro) and _is_bool_like(rn):
                for diff_q in ([ro, SymNot(rn)], [SymNot(ro), rn]):
                    cx = try_differential_query(joint + diff_q)
                    if cx is not None:
                        return {
                            "equivalent": False,
                            "status": "NON_EQUIVALENT",
                            "summary": (
                                f"Phát hiện hai hàm KHÔNG tương đương ở biểu thức logic: "
                                f"đầu vào {cx['inputs']} cho '{old_ir.name}' -> {cx['old_output']} "
                                f"nhưng '{new_ir.name}' -> {cx['new_output']}."
                            ),
                            "old_function": old_ir.name,
                            "new_function": new_ir.name,
                            "params": public_params,
                            "counterexample": cx,
                            "smt_queries": smt_queries,
                            "paths_checked": paths_checked,
                            "parse_errors": [],
                        }
            else:
                cx = try_differential_query(joint + [SymBinOp("!=", ro, rn)])
                if cx is not None:
                    return {
                        "equivalent": False,
                        "status": "NON_EQUIVALENT",
                        "summary": (
                            f"Phát hiện hai hàm KHÔNG tương đương: đầu vào {cx['inputs']} "
                            f"cho '{old_ir.name}' -> {cx['old_output']} "
                            f"nhưng '{new_ir.name}' -> {cx['new_output']}."
                        ),
                        "old_function": old_ir.name,
                        "new_function": new_ir.name,
                        "params": public_params,
                        "counterexample": cx,
                        "smt_queries": smt_queries,
                        "paths_checked": paths_checked,
                        "parse_errors": [],
                    }
                for cmp_op in ("<", ">"):
                    cx = try_differential_query(joint + [SymBinOp(cmp_op, ro, rn)])
                    if cx is not None:
                        return {
                            "equivalent": False,
                            "status": "NON_EQUIVALENT",
                            "summary": (
                                f"Phát hiện hai hàm KHÔNG tương đương: đầu vào {cx['inputs']} "
                                f"cho '{old_ir.name}' -> {cx['old_output']} "
                                f"nhưng '{new_ir.name}' -> {cx['new_output']}."
                            ),
                            "old_function": old_ir.name,
                            "new_function": new_ir.name,
                            "params": public_params,
                            "counterexample": cx,
                            "smt_queries": smt_queries,
                            "paths_checked": paths_checked,
                            "parse_errors": [],
                        }

    if (
        not hit_bound
        and not has_opaque_ops
        and not has_float_div
        and not spurious_witness_seen
        and paths_checked > 0
    ):
        return {
            "equivalent": True,
            "status": "EQUIVALENT",
            "summary": (
                f"Đã chứng minh hai hàm '{old_ir.name}' và '{new_ir.name}' TƯƠNG ĐƯƠNG "
                f"trên toàn bộ {paths_checked} cặp đường chạy khả thi ({smt_queries} truy vấn SMT DPLL(T))."
            ),
            "old_function": old_ir.name,
            "new_function": new_ir.name,
            "params": public_params,
            "counterexample": None,
            "smt_queries": smt_queries,
            "paths_checked": paths_checked,
            "parse_errors": [],
        }

    reasons: List[str] = []
    if hit_bound:
        reasons.append("chạm giới hạn độ sâu hoặc vòng lặp")
    if solver_unknown:
        reasons.append("bộ giải SMT trả về UNKNOWN cho ràng buộc phức tạp")
    if has_float_div:
        reasons.append("có phép chia thực '/'")
    if has_opaque_ops:
        reasons.append("có lời gọi hàm hoặc thao tác mảng tổng quát")
    if spurious_witness_seen:
        reasons.append("mô hình SMT cần kiểm tra bổ sung")
    if paths_checked == 0:
        reasons.append("không trích xuất được cặp đường chạy hoàn chỉnh")

    return {
        "equivalent": False,
        "status": "UNKNOWN",
        "summary": (
            f"Chưa thể kết luận tương đương hoàn toàn ({', '.join(reasons)}); "
            f"chưa phát hiện sai khác trên {paths_checked} cặp đường chạy đã kiểm tra."
        ),
        "old_function": old_ir.name,
        "new_function": new_ir.name,
        "params": public_params,
        "counterexample": None,
        "smt_queries": smt_queries,
        "paths_checked": paths_checked,
        "parse_errors": [],
    }
