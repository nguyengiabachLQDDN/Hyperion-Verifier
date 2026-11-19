"""In-memory SSA IR Virtual Machine and Mutation Testing Engine (AOR, ROR, LCR, CR, BSR)."""

from dataclasses import dataclass, field, asdict
from typing import Any, Dict, List, Optional, Set, Tuple

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
    IRType,
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


class GasExhaustedError(Exception):
    pass


class RuntimeTrapError(Exception):
    pass


@dataclass
class VMOutcome:
    status: str  # "OK" | "TIMEOUT" | "TRAP"
    return_value: Any = None
    steps: int = 0
    error: str = ""


class IRInterpreter:
    """Fast sandboxed SSA IR interpreter with strict instruction gas limit."""

    def __init__(self, gas_limit: int = 4000) -> None:
        self.gas_limit = gas_limit

    def execute(self, fn: IRFunction, args: Dict[str, Any]) -> VMOutcome:
        if not fn.blocks or fn.entry_id not in fn.blocks:
            return VMOutcome(status="OK", return_value=None, steps=0)

        env: Dict[str, Any] = {}
        arrays: Dict[str, List[Any]] = {}
        for p in fn.params:
            env[p.key()] = args.get(p.name, 0)

        cur_bid: Optional[int] = fn.entry_id
        prev_bid: Optional[int] = None
        steps = 0

        def val_of(v: IRValue) -> Any:
            if isinstance(v, Const):
                return v.value
            if isinstance(v, SSAVar):
                return env.get(v.key(), 0)
            return 0

        while cur_bid is not None and cur_bid in fn.blocks:
            blk = fn.blocks[cur_bid]
            next_bid: Optional[int] = None

            for ins in blk.instructions:
                steps += 1
                if steps > self.gas_limit:
                    return VMOutcome(status="TIMEOUT", steps=steps, error="gas_limit_exceeded")

                if isinstance(ins, PhiOp):
                    chosen = None
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
                            res = -opd
                        elif ins.op in ("not", "!"):
                            res = not bool(opd)
                        elif ins.op == "~":
                            res = ~int(opd)
                        else:
                            res = opd
                    except Exception as exc:
                        return VMOutcome(status="TRAP", steps=steps, error=str(exc))
                    if ins.dest is not None:
                        env[ins.dest.key()] = res

                elif isinstance(ins, BinaryOp):
                    lv = val_of(ins.left)
                    rv = val_of(ins.right)
                    try:
                        op = ins.op
                        if op == "+":
                            res = lv + rv
                        elif op == "-":
                            res = lv - rv
                        elif op == "*":
                            res = lv * rv
                        elif op in ("/", "//"):
                            if rv == 0:
                                return VMOutcome(status="TRAP", steps=steps, error="zero_division")
                            res = lv / rv if op == "/" else lv // rv
                        elif op == "%":
                            if rv == 0:
                                return VMOutcome(status="TRAP", steps=steps, error="zero_modulo")
                            res = lv % rv
                        elif op == "==":
                            res = lv == rv
                        elif op == "!=":
                            res = lv != rv
                        elif op == "<":
                            res = lv < rv
                        elif op == "<=":
                            res = lv <= rv
                        elif op == ">":
                            res = lv > rv
                        elif op == ">=":
                            res = lv >= rv
                        elif op == "and":
                            res = bool(lv) and bool(rv)
                        elif op == "or":
                            res = bool(lv) or bool(rv)
                        elif op == "&":
                            res = int(lv) & int(rv)
                        elif op == "|":
                            res = int(lv) | int(rv)
                        elif op == "^":
                            res = int(lv) ^ int(rv)
                        elif op == "<<":
                            res = int(lv) << max(0, min(int(rv), 16))
                        elif op == ">>":
                            res = int(lv) >> max(0, min(int(rv), 16))
                        else:
                            res = 0
                    except Exception as exc:
                        return VMOutcome(status="TRAP", steps=steps, error=str(exc))
                    if ins.dest is not None:
                        env[ins.dest.key()] = res

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
                            env[ins.dest.key()] = val_of(ins.args[1]) if val_of(ins.args[0]) else val_of(ins.args[2])
                        else:
                            # Deterministic pure surrogate hash for external helpers
                            acc = sum(int(val_of(a)) for a in ins.args if isinstance(val_of(a), (int, float)))
                            env[ins.dest.key()] = (acc * 31 + len(ins.callee)) & 0xFFFF

                elif isinstance(ins, ArrayLoadOp):
                    arr_v = val_of(ins.array)
                    idx_v = int(val_of(ins.index)) if isinstance(val_of(ins.index), (int, float)) else 0
                    if isinstance(arr_v, list):
                        if idx_v < 0 or idx_v >= len(arr_v):
                            return VMOutcome(status="TRAP", steps=steps, error="oob_read")
                        val = arr_v[idx_v]
                    else:
                        val = idx_v
                    if ins.dest is not None:
                        env[ins.dest.key()] = val

                elif isinstance(ins, ArrayStoreOp):
                    arr_v = val_of(ins.array)
                    idx_v = int(val_of(ins.index)) if isinstance(val_of(ins.index), (int, float)) else 0
                    if isinstance(arr_v, list):
                        if idx_v < 0 or idx_v >= len(arr_v):
                            return VMOutcome(status="TRAP", steps=steps, error="oob_write")
                        arr_v[idx_v] = val_of(ins.value)

                elif isinstance(ins, AssertOp):
                    if not bool(val_of(ins.cond)):
                        return VMOutcome(status="TRAP", steps=steps, error="assertion_failed")

                elif isinstance(ins, SinkOp):
                    if ins.dest is not None:
                        env[ins.dest.key()] = 1

                elif isinstance(ins, CondBranchOp):
                    taken = bool(val_of(ins.cond))
                    next_bid = ins.true_target if taken else ins.false_target
                    break

                elif isinstance(ins, JumpOp):
                    next_bid = ins.target
                    break

                elif isinstance(ins, ReturnOp):
                    ret_v = val_of(ins.value) if ins.value is not None else None
                    return VMOutcome(status="OK", return_value=ret_v, steps=steps)

            prev_bid = cur_bid
            cur_bid = next_bid

        return VMOutcome(status="OK", return_value=None, steps=steps)


AOR_MAP = {"+": "-", "-": "+", "*": "//", "//": "*", "/": "*", "%": "+"}
ROR_MAP = {"<": "<=", "<=": "<", ">": ">=", ">=": ">", "==": "!=", "!=": "=="}
LCR_MAP = {"and": "or", "or": "and"}


@dataclass
class MutantRecord:
    mutant_id: int
    operator: str  # AOR, ROR, LCR, CR, BSR
    block_id: int
    line: int
    original: str
    mutated: str
    status: str  # "KILLED" | "SURVIVED" | "TIMEOUT"
    steps_executed: int = 0
    killer_inputs: Optional[Dict[str, int]] = None
    killed_by_smt: bool = False

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)


@dataclass
class MutationResult:
    function: str
    total_mutants: int = 0
    killed: int = 0
    survived: int = 0
    timeouts: int = 0
    total_vm_steps: int = 0
    mutation_score_pct: float = 0.0
    records: List[MutantRecord] = field(default_factory=list)
    initial_survived: int = 0
    newly_killed: int = 0
    kill_witnesses: List[Dict[str, Any]] = field(default_factory=list)
    witness_vectors: List[Dict[str, int]] = field(default_factory=list)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "function": self.function,
            "total_mutants": self.total_mutants,
            "killed": self.killed,
            "survived": self.survived,
            "timeouts": self.timeouts,
            "total_vm_steps": self.total_vm_steps,
            "mutation_score_pct": self.mutation_score_pct,
            "initial_survived": self.initial_survived,
            "newly_killed": self.newly_killed,
            "records": [r.to_dict() for r in self.records],
            "kill_witnesses": list(self.kill_witnesses),
            "witness_vectors": list(self.witness_vectors),
        }


def _generate_mutant_specs(fn: IRFunction, max_mutants: int) -> List[Tuple[str, int, int, str, str, IRFunction]]:
    """Create in-memory mutated IRFunction clones without touching disk."""
    specs: List[Tuple[str, int, int, str, str, IRFunction]] = []

    for bid in sorted(fn.blocks.keys()):
        blk = fn.blocks[bid]
        for idx, ins in enumerate(blk.instructions):
            if len(specs) >= max_mutants:
                return specs

            if isinstance(ins, BinaryOp):
                if ins.op in AOR_MAP:
                    clone = fn.clone()
                    target_ins = clone.blocks[bid].instructions[idx]
                    assert isinstance(target_ins, BinaryOp)
                    orig_s = ins.format()
                    target_ins.op = AOR_MAP[ins.op]
                    specs.append(("AOR", bid, ins.line, orig_s, target_ins.format(), clone))
                elif ins.op in ROR_MAP:
                    clone = fn.clone()
                    target_ins = clone.blocks[bid].instructions[idx]
                    assert isinstance(target_ins, BinaryOp)
                    orig_s = ins.format()
                    target_ins.op = ROR_MAP[ins.op]
                    specs.append(("ROR", bid, ins.line, orig_s, target_ins.format(), clone))
                elif ins.op in LCR_MAP:
                    clone = fn.clone()
                    target_ins = clone.blocks[bid].instructions[idx]
                    assert isinstance(target_ins, BinaryOp)
                    orig_s = ins.format()
                    target_ins.op = LCR_MAP[ins.op]
                    specs.append(("LCR", bid, ins.line, orig_s, target_ins.format(), clone))
                elif isinstance(ins.right, Const) and isinstance(ins.right.value, int):
                    clone = fn.clone()
                    target_ins = clone.blocks[bid].instructions[idx]
                    assert isinstance(target_ins, BinaryOp)
                    orig_s = ins.format()
                    old_c = ins.right.value
                    new_c = 1 if old_c == 0 else (old_c + 1)
                    target_ins.right = Const(value=new_c, ir_type=IRType.INT)
                    specs.append(("CR", bid, ins.line, orig_s, target_ins.format(), clone))

            elif isinstance(ins, AssignOp) and isinstance(ins.src, Const) and isinstance(ins.src.value, int) and not isinstance(ins.src.value, bool):
                clone = fn.clone()
                target_ins = clone.blocks[bid].instructions[idx]
                assert isinstance(target_ins, AssignOp)
                orig_s = ins.format()
                old_c = ins.src.value
                target_ins.src = Const(value=(1 if old_c == 0 else old_c + 1), ir_type=IRType.INT)
                specs.append(("CR", bid, ins.line, orig_s, target_ins.format(), clone))

            elif isinstance(ins, CondBranchOp):
                clone = fn.clone()
                target_ins = clone.blocks[bid].instructions[idx]
                assert isinstance(target_ins, CondBranchOp)
                orig_s = ins.format()
                target_ins.true_target, target_ins.false_target = (
                    target_ins.false_target,
                    target_ins.true_target,
                )
                specs.append(("BSR", bid, ins.line, orig_s, target_ins.format(), clone))

    return specs


_CMP_OPS = {"==", "!=", "<", "<=", ">", ">="}
_NEG_CMP = {"==": "!=", "!=": "==", "<": ">=", ">=": "<", "<=": ">", ">": "<="}
_FLIP_CMP = {"==": "==", "!=": "!=", "<": ">", ">": "<", "<=": ">=", ">=": "<="}
_BOOL_OPS = _CMP_OPS | {"and", "or"}


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

        # Canonicalize `const + var` -> `var + const` for DPLLTSolver._propagate_bounds
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
            # Normalize `(-var) cmp const` -> `var inv_cmp (-const)`
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


def _collect_consts(expr: SymExpr, out: List[int]) -> None:
    if isinstance(expr, SymConst):
        out.append(int(expr.value))
    elif isinstance(expr, SymNot):
        _collect_consts(expr.expr, out)
    elif isinstance(expr, SymBinOp):
        _collect_consts(expr.left, out)
        _collect_consts(expr.right, out)


def _solve_branch_set(constraints: List[SymExpr], max_steps: int = 360) -> Tuple[str, Optional[Dict[str, int]]]:
    """Return ('SAT', model), ('UNSAT', None), or ('UNKNOWN', None)."""
    branches = _expand_disjunctions(constraints, max_branches=8)
    if not branches:
        return "UNSAT", None

    saw_unknown = False
    for branch in branches:
        if not branch:
            return "SAT", {}
        consts: List[int] = []
        for atom in branch:
            _collect_consts(atom, consts)
        min_c = min(consts) if consts else 0
        max_c = max(consts) if consts else 0
        lo_dyn = max(-100000, min(-128, min_c - 16))
        hi_dyn = min(100000, max(128, max_c + 16))

        solver = DPLLTSolver(default_lo=lo_dyn, default_hi=hi_dyn)
        res = solver.solve(branch, max_steps=max_steps)
        if res.status == "SAT":
            return "SAT", res.model
        if res.status == "UNKNOWN":
            saw_unknown = True
            if lo_dyn < -64 or hi_dyn > 64:
                retry = DPLLTSolver(default_lo=-64, default_hi=64).solve(branch, max_steps=max_steps)
                if retry.status == "SAT":
                    return "SAT", retry.model

    return ("UNKNOWN" if saw_unknown else "UNSAT"), None


@dataclass
class _PathSummary:
    constraints: List[SymExpr]
    blocks: Set[int]
    outcome_kind: str  # "RETURN" | "TRAP" | "INCOMPLETE"
    ret_expr: Optional[SymExpr] = None
    is_void: bool = False


@dataclass
class _PathState:
    block_id: int
    prev_block_id: Optional[int]
    env: Dict[str, SymExpr]
    alloc_arrays: Dict[str, int]
    array_elems: Dict[str, Optional[List[SymExpr]]]
    constraints: List[SymExpr]
    trace: List[int]
    depth: int = 0


def _compute_reverse_reachable(fn: IRFunction, target_block_id: int) -> Set[int]:
    """Return set of block IDs that can reach target_block_id in fn's CFG."""
    if target_block_id not in fn.blocks:
        return set()
    rev_adj: Dict[int, Set[int]] = {bid: set(blk.preds) for bid, blk in fn.blocks.items()}
    for bid, blk in fn.blocks.items():
        for succ in blk.succs:
            rev_adj.setdefault(succ, set()).add(bid)
        for ins in blk.instructions:
            if isinstance(ins, CondBranchOp):
                rev_adj.setdefault(ins.true_target, set()).add(bid)
                rev_adj.setdefault(ins.false_target, set()).add(bid)
            elif isinstance(ins, JumpOp):
                rev_adj.setdefault(ins.target, set()).add(bid)

    reachable: Set[int] = {target_block_id}
    stack = [target_block_id]
    while stack:
        cur = stack.pop()
        for pred in rev_adj.get(cur, ()):
            if pred not in reachable and pred in fn.blocks:
                reachable.add(pred)
                stack.append(pred)
    return reachable


def _extract_path_summaries(
    fn: IRFunction,
    target_block_id: Optional[int] = None,
    max_paths: int = 80,
    max_depth: int = 40,
) -> List[_PathSummary]:
    if not fn.blocks or fn.entry_id not in fn.blocks:
        return []

    can_reach = (
        _compute_reverse_reachable(fn, target_block_id)
        if target_block_id is not None
        else set(fn.blocks.keys())
    )
    if target_block_id is not None and fn.entry_id not in can_reach:
        return []

    init_env: Dict[str, SymExpr] = {p.key(): SymVar(p.name) for p in fn.params}
    queue: List[_PathState] = [
        _PathState(
            block_id=fn.entry_id,
            prev_block_id=None,
            env=init_env,
            alloc_arrays={},
            array_elems={},
            constraints=[],
            trace=[fn.entry_id],
            depth=0,
        )
    ]
    summaries: List[_PathSummary] = []
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

        for ins_idx, ins in enumerate(blk.instructions):
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
                        env[ins.dest.key()] = _to_sym(chosen, env)
                        if isinstance(chosen, SSAVar) and chosen.key() in alloc_arrays:
                            alloc_arrays[ins.dest.key()] = alloc_arrays[chosen.key()]
                            elems = array_elems.get(chosen.key())
                            array_elems[ins.dest.key()] = list(elems) if elems is not None else None
                    else:
                        env[ins.dest.key()] = SymConst(0)

            elif isinstance(ins, AssignOp):
                if ins.dest is not None:
                    env[ins.dest.key()] = _to_sym(ins.src, env)
                    if isinstance(ins.src, SSAVar) and ins.src.key() in alloc_arrays:
                        alloc_arrays[ins.dest.key()] = alloc_arrays[ins.src.key()]
                        elems = array_elems.get(ins.src.key())
                        array_elems[ins.dest.key()] = list(elems) if elems is not None else None

            elif isinstance(ins, UnaryOp):
                if ins.dest is not None:
                    opd = _to_sym(ins.operand, env)
                    if ins.op in ("not", "!"):
                        env[ins.dest.key()] = SymNot(opd)
                    elif ins.op == "-":
                        env[ins.dest.key()] = _simplify_sym_expr(SymBinOp("-", SymConst(0), opd))
                    elif ins.op == "~":
                        env[ins.dest.key()] = SymBinOp("-", SymConst(-1), opd)
                    else:
                        env[ins.dest.key()] = opd

            elif isinstance(ins, BinaryOp):
                l_sym = _to_sym(ins.left, env)
                r_sym = _to_sym(ins.right, env)
                if ins.op in ("/", "//", "%"):
                    trap_c = constraints + [SymBinOp("==", r_sym, SymConst(0))]
                    st_trap, _ = _solve_branch_set(trap_c, max_steps=160)
                    if st_trap in ("SAT", "UNKNOWN"):
                        summaries.append(
                            _PathSummary(
                                constraints=trap_c,
                                blocks=set(st.trace),
                                outcome_kind="TRAP",
                            )
                        )
                    constraints = constraints + [SymBinOp("!=", r_sym, SymConst(0))]
                if ins.dest is not None:
                    env[ins.dest.key()] = _simplify_sym_expr(SymBinOp(ins.op, l_sym, r_sym))

            elif isinstance(ins, CallOp):
                if ins.callee == "select" and len(ins.args) == 3 and ins.dest is not None:
                    cond_s = _simplify_sym_expr(_to_sym(ins.args[0], env))
                    t_s = _to_sym(ins.args[1], env)
                    f_s = _to_sym(ins.args[2], env)
                    if isinstance(cond_s, SymConst):
                        env[ins.dest.key()] = t_s if cond_s.value != 0 else f_s
                    else:
                        # Fork symbolic state on select false branch while continuing true branch
                        false_c = constraints + [SymNot(cond_s)]
                        st_f, _ = _solve_branch_set(false_c, max_steps=160)
                        if st_f in ("SAT", "UNKNOWN") and len(queue) < max_paths:
                            alt_env = dict(env)
                            alt_env[ins.dest.key()] = f_s
                            # Replay remaining instructions in the same block via a synthetic continuation
                            rem_ok = True
                            alt_constraints = list(false_c)
                            for rem_ins in blk.instructions[ins_idx + 1 :]:
                                if isinstance(rem_ins, AssignOp) and rem_ins.dest is not None:
                                    alt_env[rem_ins.dest.key()] = _to_sym(rem_ins.src, alt_env)
                                elif isinstance(rem_ins, ReturnOp):
                                    summaries.append(
                                        _PathSummary(
                                            constraints=alt_constraints,
                                            blocks=set(st.trace),
                                            outcome_kind="RETURN",
                                            ret_expr=(
                                                None
                                                if rem_ins.value is None
                                                else _to_sym(rem_ins.value, alt_env)
                                            ),
                                            is_void=(rem_ins.value is None),
                                        )
                                    )
                                    rem_ok = False
                                    break
                                else:
                                    rem_ok = False
                                    break
                            if rem_ok:
                                summaries.append(
                                    _PathSummary(
                                        constraints=alt_constraints,
                                        blocks=set(st.trace),
                                        outcome_kind="INCOMPLETE",
                                    )
                                )
                        constraints = constraints + [cond_s]
                        env[ins.dest.key()] = t_s
                elif ins.callee == "alloc_array" and ins.args and ins.dest is not None:
                    sz_sym = _simplify_sym_expr(_to_sym(ins.args[0], env))
                    sz = max(0, min(sz_sym.value, 256)) if isinstance(sz_sym, SymConst) else 0
                    alloc_arrays[ins.dest.key()] = sz
                    array_elems[ins.dest.key()] = [SymConst(0)] * sz if sz <= 16 else None
                    env[ins.dest.key()] = SymConst(0)
                elif ins.callee == "len" and ins.args and ins.dest is not None:
                    arg0 = ins.args[0]
                    if isinstance(arg0, SSAVar) and arg0.key() in alloc_arrays:
                        env[ins.dest.key()] = SymConst(alloc_arrays[arg0.key()])
                    else:
                        env[ins.dest.key()] = SymConst(0)
                elif ins.dest is not None:
                    arg_syms = [_to_sym(a, env) for a in ins.args]
                    acc: SymExpr = SymConst(0)
                    for a_s in arg_syms:
                        acc = _simplify_sym_expr(SymBinOp("+", acc, a_s))
                    hashed = SymBinOp(
                        "&",
                        SymBinOp("+", SymBinOp("*", acc, SymConst(31)), SymConst(len(ins.callee))),
                        SymConst(0xFFFF),
                    )
                    env[ins.dest.key()] = _simplify_sym_expr(hashed)

            elif isinstance(ins, ArrayLoadOp):
                idx_sym = _to_sym(ins.index, env)
                arr_key = ins.array.key() if isinstance(ins.array, SSAVar) else ""
                arr_len = alloc_arrays.get(arr_key)
                if arr_len is not None:
                    for oob_c in (
                        SymBinOp("<", idx_sym, SymConst(0)),
                        SymBinOp(">=", idx_sym, SymConst(arr_len)),
                    ):
                        trap_c = constraints + [oob_c]
                        st_trap, _ = _solve_branch_set(trap_c, max_steps=160)
                        if st_trap in ("SAT", "UNKNOWN"):
                            summaries.append(
                                _PathSummary(
                                    constraints=trap_c,
                                    blocks=set(st.trace),
                                    outcome_kind="TRAP",
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
                            env[ins.dest.key()] = SymVar(ins.dest.key())
                else:
                    if ins.dest is not None:
                        env[ins.dest.key()] = idx_sym

            elif isinstance(ins, ArrayStoreOp):
                idx_sym = _to_sym(ins.index, env)
                arr_key = ins.array.key() if isinstance(ins.array, SSAVar) else ""
                arr_len = alloc_arrays.get(arr_key)
                if arr_len is not None:
                    for oob_c in (
                        SymBinOp("<", idx_sym, SymConst(0)),
                        SymBinOp(">=", idx_sym, SymConst(arr_len)),
                    ):
                        trap_c = constraints + [oob_c]
                        st_trap, _ = _solve_branch_set(trap_c, max_steps=160)
                        if st_trap in ("SAT", "UNKNOWN"):
                            summaries.append(
                                _PathSummary(
                                    constraints=trap_c,
                                    blocks=set(st.trace),
                                    outcome_kind="TRAP",
                                )
                            )
                    constraints = constraints + [
                        SymBinOp(">=", idx_sym, SymConst(0)),
                        SymBinOp("<", idx_sym, SymConst(arr_len)),
                    ]
                    elems = array_elems.get(arr_key)
                    idx_simple = _simplify_sym_expr(idx_sym)
                    if elems is not None and isinstance(idx_simple, SymConst) and 0 <= idx_simple.value < len(elems):
                        elems[idx_simple.value] = _to_sym(ins.value, env)
                    else:
                        array_elems[arr_key] = None

            elif isinstance(ins, AssertOp):
                cond_sym = _to_sym(ins.cond, env)
                trap_c = constraints + [SymNot(cond_sym)]
                st_trap, _ = _solve_branch_set(trap_c, max_steps=160)
                if st_trap in ("SAT", "UNKNOWN"):
                    summaries.append(
                        _PathSummary(
                            constraints=trap_c,
                            blocks=set(st.trace),
                            outcome_kind="TRAP",
                        )
                    )
                constraints = constraints + [cond_sym]

            elif isinstance(ins, SinkOp):
                if ins.dest is not None:
                    env[ins.dest.key()] = SymConst(1)

            elif isinstance(ins, CondBranchOp):
                terminated = True
                if st.depth >= max_depth:
                    summaries.append(
                        _PathSummary(
                            constraints=constraints,
                            blocks=set(st.trace),
                            outcome_kind="INCOMPLETE",
                        )
                    )
                    break
                cond_sym = _to_sym(ins.cond, env)
                for take_true, target_id in ((True, ins.true_target), (False, ins.false_target)):
                    if (
                        target_block_id is not None
                        and target_block_id not in st.trace
                        and target_id not in can_reach
                    ):
                        continue
                    branch_c = cond_sym if take_true else SymNot(cond_sym)
                    nxt_c = constraints + [branch_c]
                    st_br, _ = _solve_branch_set(nxt_c, max_steps=160)
                    if st_br == "UNSAT":
                        continue
                    if st.trace.count(target_id) >= 3:
                        summaries.append(
                            _PathSummary(
                                constraints=nxt_c,
                                blocks=set(st.trace),
                                outcome_kind="INCOMPLETE",
                            )
                        )
                        continue
                    queue.append(
                        _PathState(
                            block_id=target_id,
                            prev_block_id=blk.id,
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
                if (
                    target_block_id is not None
                    and target_block_id not in st.trace
                    and ins.target not in can_reach
                ):
                    break
                if st.depth >= max_depth or st.trace.count(ins.target) >= 3:
                    summaries.append(
                        _PathSummary(
                            constraints=constraints,
                            blocks=set(st.trace),
                            outcome_kind="INCOMPLETE",
                        )
                    )
                    break
                queue.append(
                    _PathState(
                        block_id=ins.target,
                        prev_block_id=blk.id,
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
                ret_e = None if ins.value is None else _to_sym(ins.value, env)
                summaries.append(
                    _PathSummary(
                        constraints=constraints,
                        blocks=set(st.trace),
                        outcome_kind="RETURN",
                        ret_expr=ret_e,
                        is_void=(ins.value is None),
                    )
                )
                break

        if not terminated:
            summaries.append(
                _PathSummary(
                    constraints=constraints,
                    blocks=set(st.trace),
                    outcome_kind="RETURN",
                    ret_expr=None,
                    is_void=True,
                )
            )

    while queue:
        st_rem = queue.pop(0)
        summaries.append(
            _PathSummary(
                constraints=st_rem.constraints,
                blocks=set(st_rem.trace),
                outcome_kind="INCOMPLETE",
            )
        )
    return summaries


def _collect_fn_int_constants(fn: IRFunction) -> List[int]:
    vals: Set[int] = set()
    for blk in fn.blocks.values():
        for ins in blk.instructions:
            for v in ins.uses():
                if isinstance(v, Const) and isinstance(v.value, int) and not isinstance(v.value, bool):
                    if abs(v.value) <= 10000:
                        vals.add(int(v.value))
            if isinstance(ins, AssignOp) and isinstance(ins.src, Const):
                if isinstance(ins.src.value, int) and not isinstance(ins.src.value, bool):
                    if abs(ins.src.value) <= 10000:
                        vals.add(int(ins.src.value))
    return sorted(vals)


def _format_vm_outcome(out: VMOutcome) -> Any:
    if out.status == "OK":
        return out.return_value
    return f"{out.status}:{out.error}"


def _verify_kill_candidate(
    vm: IRInterpreter,
    fn: IRFunction,
    mut_fn: IRFunction,
    cand: Dict[str, int],
    param_names: List[str],
) -> Optional[Tuple[Dict[str, int], VMOutcome, VMOutcome, str]]:
    norm = {p: int(cand.get(p, 0)) for p in param_names}
    orig_out = vm.execute(fn, norm)
    mut_out = vm.execute(mut_fn, norm)
    if mut_out.status == "TIMEOUT" and orig_out.status != "TIMEOUT":
        return norm, orig_out, mut_out, "TIMEOUT"
    if mut_out.status != orig_out.status or mut_out.return_value != orig_out.return_value:
        return norm, orig_out, mut_out, "KILLED"
    return None


def _solve_differential_witness(
    fn: IRFunction,
    mut_fn: IRFunction,
    mut_bid: int,
    orig_paths: List[_PathSummary],
    vm: IRInterpreter,
    param_names: List[str],
    existing_witnesses: List[Dict[str, int]],
    base_suite: List[Dict[str, Any]],
) -> Optional[Tuple[Dict[str, int], VMOutcome, VMOutcome, str]]:
    # 1. Fast reuse of previously synthesized witnesses for this function
    for w in existing_witnesses:
        hit = _verify_kill_candidate(vm, fn, mut_fn, w, param_names)
        if hit is not None:
            return hit

    # 2. Extract bounded symbolic path summaries reaching mut_bid
    mut_paths = _extract_path_summaries(mut_fn, target_block_id=mut_bid, max_paths=24, max_depth=20)
    orig_targeted = [p for p in orig_paths if mut_bid in p.blocks][:10]
    if not orig_targeted:
        orig_targeted = orig_paths[:10]

    smt_budget = [0]

    def try_constraints(c_list: List[SymExpr]) -> Optional[Tuple[Dict[str, int], VMOutcome, VMOutcome, str]]:
        if smt_budget[0] >= 24:
            return None
        smt_budget[0] += 1
        status, model = _solve_branch_set(c_list, max_steps=280)
        if status == "SAT" and model is not None:
            return _verify_kill_candidate(vm, fn, mut_fn, model, param_names)
        return None

    for p_orig in orig_targeted:
        for p_mut in mut_paths[:10]:
            if smt_budget[0] >= 24:
                break
            if mut_bid not in p_mut.blocks:
                continue
            joint = p_orig.constraints + p_mut.constraints

            if p_orig.outcome_kind == "RETURN" and p_mut.outcome_kind == "RETURN":
                if p_orig.is_void and p_mut.is_void:
                    continue
                if p_orig.is_void != p_mut.is_void:
                    hit = try_constraints(joint)
                    if hit is not None:
                        return hit
                    continue
                assert p_orig.ret_expr is not None and p_mut.ret_expr is not None
                ro = _simplify_sym_expr(p_orig.ret_expr)
                rm = _simplify_sym_expr(p_mut.ret_expr)
                if ro == rm:
                    continue
                if _is_bool_like(ro) and _is_bool_like(rm):
                    for diff_q in ([ro, SymNot(rm)], [SymNot(ro), rm]):
                        hit = try_constraints(joint + diff_q)
                        if hit is not None:
                            return hit
                else:
                    hit = try_constraints(joint + [SymBinOp("!=", ro, rm)])
                    if hit is not None:
                        return hit
                    # Fallback split `<` / `>` because DPLL(T) propagates two-var inequalities better than `!=`
                    for cmp_op in ("<", ">"):
                        hit = try_constraints(joint + [SymBinOp(cmp_op, ro, rm)])
                        if hit is not None:
                            return hit

            elif (p_orig.outcome_kind == "RETURN" and p_mut.outcome_kind == "TRAP") or (
                p_orig.outcome_kind == "TRAP" and p_mut.outcome_kind == "RETURN"
            ):
                hit = try_constraints(joint)
                if hit is not None:
                    return hit

            elif p_orig.outcome_kind == "INCOMPLETE" or p_mut.outcome_kind == "INCOMPLETE":
                hit = try_constraints(joint)
                if hit is not None:
                    return hit

    # Check single-side incomplete/trap paths reaching mut_bid if pair cross-product was empty
    for p_mut in mut_paths:
        if mut_bid in p_mut.blocks and p_mut.constraints:
            hit = try_constraints(p_mut.constraints)
            if hit is not None:
                return hit

    # 3. Boundary and branch-targeted concrete probes (always cross-verified by IRInterpreter)
    if param_names:
        consts = sorted(set(_collect_fn_int_constants(fn) + _collect_fn_int_constants(mut_fn)))
        scalars: List[int] = []
        seen_sc: Set[int] = set()
        for sc in [-2, -1, 0, 1, 2]:
            if sc not in seen_sc:
                seen_sc.add(sc)
                scalars.append(sc)
        for c in consts[:32]:
            for delta in (-1, 0, 1):
                val = c + delta
                if val not in seen_sc:
                    seen_sc.add(val)
                    scalars.append(val)

        probes: List[Dict[str, int]] = []
        seen_probes: Set[Tuple[int, ...]] = set()

        def add_probe(d: Dict[str, int]) -> None:
            if len(probes) >= 96:
                return
            t = tuple(int(d.get(p, 0)) for p in param_names)
            if t not in seen_probes:
                seen_probes.add(t)
                probes.append({p: v for p, v in zip(param_names, t)})

        for sc in scalars:
            add_probe({p: sc for p in param_names})
        if len(param_names) > 1:
            anchors: List[Dict[str, int]] = [{p: 0 for p in param_names}, {p: 1 for p in param_names}]
            for bv in base_suite[:4]:
                anchors.append({p: int(bv.get(p, 0)) for p in param_names})
            for anch in anchors:
                for p in param_names:
                    for sc in scalars:
                        cand = dict(anch)
                        cand[p] = sc
                        add_probe(cand)

        for cand in probes:
            hit = _verify_kill_candidate(vm, fn, mut_fn, cand, param_names)
            if hit is not None:
                return hit

    return None


def _kill_surviving_mutants(
    fn: IRFunction,
    res: MutationResult,
    surviving_entries: List[Tuple[int, str, int, int, str, str, IRFunction, Optional[MutantRecord]]],
    vm: IRInterpreter,
    param_names: List[str],
    base_suite: List[Dict[str, Any]],
) -> None:
    import time
    deadline = time.monotonic() + 2.5
    orig_paths = _extract_path_summaries(fn, target_block_id=None, max_paths=32, max_depth=22)
    seen_witness_keys: Set[Tuple[int, ...]] = set()

    for mid, op_kind, bid, line, orig_s, mut_s, mut_fn, rec in surviving_entries:
        if time.monotonic() > deadline:
            break
        hit = _solve_differential_witness(
            fn=fn,
            mut_fn=mut_fn,
            mut_bid=bid,
            orig_paths=orig_paths,
            vm=vm,
            param_names=param_names,
            existing_witnesses=res.witness_vectors,
            base_suite=base_suite,
        )
        if hit is None:
            continue

        cand, orig_out, mut_out, new_status = hit
        res.total_vm_steps += orig_out.steps + mut_out.steps
        if new_status == "TIMEOUT":
            res.timeouts += 1
        res.killed += 1
        res.survived = max(0, res.survived - 1)
        res.newly_killed += 1

        if rec is not None:
            rec.status = new_status
            rec.killer_inputs = dict(cand)
            rec.killed_by_smt = True
            rec.steps_executed += mut_out.steps

        res.kill_witnesses.append(
            {
                "mutant_id": mid,
                "operator": op_kind,
                "line": line,
                "original": orig_s,
                "mutated": mut_s,
                "witness_inputs": dict(cand),
                "orig_output": _format_vm_outcome(orig_out),
                "mut_output": _format_vm_outcome(mut_out),
            }
        )

        w_key = tuple(int(cand.get(p, 0)) for p in param_names)
        if w_key not in seen_witness_keys:
            seen_witness_keys.add(w_key)
            res.witness_vectors.append(dict(cand))


def run_mutation_testing(
    fn: IRFunction,
    test_vectors: List[Dict[str, int]],
    max_mutants: int = 60,
    gas_limit: int = 4000,
    kill_surviving: bool = False,
) -> MutationResult:
    """Evaluate all generated in-memory IR mutants against symbolic + boundary test vectors."""
    res = MutationResult(function=fn.name)
    vm = IRInterpreter(gas_limit=gas_limit)

    # Deduplicate caller-supplied vectors first (preserving witness vectors on re-runs),
    # then pad with deterministic boundary vectors up to 12.
    param_names = [p.name for p in fn.params]
    dedup_suite: List[Dict[str, Any]] = []
    seen_s: Set[Tuple[Tuple[str, Any], ...]] = set()

    def _vec_key(vec: Dict[str, Any]) -> Tuple[Tuple[str, Any], ...]:
        return tuple(
            sorted((k, int(v) if isinstance(v, (int, bool)) else str(v)) for k, v in vec.items())
        )

    for vec in test_vectors:
        key = _vec_key(vec)
        if key not in seen_s:
            seen_s.add(key)
            dedup_suite.append(dict(vec))
        if len(dedup_suite) >= 48:
            break

    if param_names and not dedup_suite:
        for val in (0, 1, -1, 5, 17):
            vec = {p: val for p in param_names}
            key = _vec_key(vec)
            if key not in seen_s:
                seen_s.add(key)
                dedup_suite.append(vec)
            if len(dedup_suite) >= 12:
                break

    if not dedup_suite:
        dedup_suite.append({})

    # Baseline oracle outputs on unmutated function
    oracle: List[Tuple[str, Any]] = []
    for vec in dedup_suite:
        out = vm.execute(fn, vec)
        res.total_vm_steps += out.steps
        oracle.append((out.status, out.return_value))

    specs = _generate_mutant_specs(fn, max_mutants=max_mutants)
    res.total_mutants = len(specs)
    surviving_entries: List[Tuple[int, str, int, int, str, str, IRFunction, Optional[MutantRecord]]] = []

    for mid, (op_kind, bid, line, orig_s, mut_s, mut_fn) in enumerate(specs, start=1):
        status = "SURVIVED"
        mut_steps = 0
        for vec, (base_status, base_ret) in zip(dedup_suite, oracle):
            m_out = vm.execute(mut_fn, vec)
            mut_steps += m_out.steps
            res.total_vm_steps += m_out.steps
            if m_out.status == "TIMEOUT" and base_status != "TIMEOUT":
                status = "TIMEOUT"
                break
            if m_out.status != base_status or m_out.return_value != base_ret:
                status = "KILLED"
                break

        if status == "KILLED":
            res.killed += 1
        elif status == "TIMEOUT":
            res.timeouts += 1
            res.killed += 1  # Infinite-loop mutants count as detected
        else:
            res.survived += 1

        rec: Optional[MutantRecord] = None
        if len(res.records) < 40:
            rec = MutantRecord(
                mutant_id=mid,
                operator=op_kind,
                block_id=bid,
                line=line,
                original=orig_s,
                mutated=mut_s,
                status=status,
                steps_executed=mut_steps,
            )
            res.records.append(rec)

        if status == "SURVIVED":
            surviving_entries.append((mid, op_kind, bid, line, orig_s, mut_s, mut_fn, rec))

    res.initial_survived = res.survived
    if kill_surviving and surviving_entries:
        _kill_surviving_mutants(fn, res, surviving_entries, vm, param_names, dedup_suite)

    if res.total_mutants > 0:
        res.mutation_score_pct = round((res.killed / res.total_mutants) * 100.0, 1)
    return res


def kill_surviving_mutants(
    fn: IRFunction,
    test_vectors: List[Dict[str, int]],
    max_mutants: int = 60,
    gas_limit: int = 4000,
) -> MutationResult:
    """Run mutation testing and synthesize SMT differential witnesses to kill SURVIVED mutants."""
    return run_mutation_testing(
        fn,
        test_vectors,
        max_mutants=max_mutants,
        gas_limit=gas_limit,
        kill_surviving=True,
    )
