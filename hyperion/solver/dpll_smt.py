"""From-scratch CDCL SAT + Linear Integer Interval Theory DPLL(T) Constraint Solver."""

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Set, Tuple


@dataclass(frozen=True)
class SymExpr:
    """Symbolic expression AST used in path constraints."""
    pass


@dataclass(frozen=True)
class SymVar(SymExpr):
    name: str


@dataclass(frozen=True)
class SymConst(SymExpr):
    value: int


@dataclass(frozen=True)
class SymBinOp(SymExpr):
    op: str
    left: SymExpr
    right: SymExpr


@dataclass(frozen=True)
class SymNot(SymExpr):
    expr: SymExpr


@dataclass
class SolverStats:
    decisions: int = 0
    propagations: int = 0
    conflicts: int = 0
    learned_clauses: int = 0
    theory_checks: int = 0


@dataclass
class SolverResult:
    status: str  # "SAT" | "UNSAT" | "UNKNOWN"
    model: Dict[str, int] = field(default_factory=dict)
    stats: SolverStats = field(default_factory=SolverStats)


def eval_sym_expr(expr: SymExpr, env: Dict[str, int]) -> Optional[int]:
    """Concrete evaluation of a symbolic integer/boolean expression under an integer model."""
    if isinstance(expr, SymConst):
        return int(expr.value)
    if isinstance(expr, SymVar):
        return env.get(expr.name, 0)
    if isinstance(expr, SymNot):
        v = eval_sym_expr(expr.expr, env)
        return None if v is None else (0 if v else 1)
    if isinstance(expr, SymBinOp):
        lv = eval_sym_expr(expr.left, env)
        rv = eval_sym_expr(expr.right, env)
        if lv is None or rv is None:
            return None
        op = expr.op
        if op == "+":
            return lv + rv
        if op == "-":
            return lv - rv
        if op == "*":
            return lv * rv
        if op == "//" or op == "/":
            return lv // rv if rv != 0 else None
        if op == "%":
            return lv % rv if rv != 0 else None
        if op == "&":
            return lv & rv
        if op == "|":
            return lv | rv
        if op == "^":
            return lv ^ rv
        if op == "<<":
            return lv << max(0, min(rv, 16))
        if op == ">>":
            return lv >> max(0, min(rv, 16))
        if op == "==":
            return 1 if lv == rv else 0
        if op == "!=":
            return 1 if lv != rv else 0
        if op == "<":
            return 1 if lv < rv else 0
        if op == "<=":
            return 1 if lv <= rv else 0
        if op == ">":
            return 1 if lv > rv else 0
        if op == ">=":
            return 1 if lv >= rv else 0
        if op == "and":
            return 1 if (lv != 0 and rv != 0) else 0
        if op == "or":
            return 1 if (lv != 0 or rv != 0) else 0
    return None


def collect_vars(expr: SymExpr, out: Optional[Set[str]] = None) -> Set[str]:
    if out is None:
        out = set()
    if isinstance(expr, SymVar):
        out.add(expr.name)
    elif isinstance(expr, SymNot):
        collect_vars(expr.expr, out)
    elif isinstance(expr, SymBinOp):
        collect_vars(expr.left, out)
        collect_vars(expr.right, out)
    return out


class CDCLSATSolver:
    """Pure-Python Conflict-Driven Clause Learning (CDCL) SAT core for Boolean theory skeleton."""

    def __init__(self, num_vars: int, clauses: List[List[int]]) -> None:
        self.num_vars = num_vars
        self.clauses: List[List[int]] = [list(c) for c in clauses]
        self.learned: List[List[int]] = []
        self.stats = SolverStats()

    def solve(self, max_conflicts: int = 512) -> Optional[Dict[int, bool]]:
        assign: Dict[int, bool] = {}
        level_of: Dict[int, int] = {}
        reason_of: Dict[int, Optional[List[int]]] = {}
        trail: List[int] = []
        dec_level = 0

        def lit_val(lit: int) -> Optional[bool]:
            v = abs(lit)
            if v not in assign:
                return None
            return assign[v] if lit > 0 else not assign[v]

        def propagate() -> Optional[List[int]]:
            changed = True
            while changed:
                changed = False
                for cl in self.clauses + self.learned:
                    unassigned: List[int] = []
                    sat = False
                    for lit in cl:
                        val = lit_val(lit)
                        if val is True:
                            sat = True
                            break
                        if val is None:
                            unassigned.append(lit)
                    if sat:
                        continue
                    if not unassigned:
                        return cl  # Conflict
                    if len(unassigned) == 1:
                        unit = unassigned[0]
                        v = abs(unit)
                        assign[v] = unit > 0
                        level_of[v] = dec_level
                        reason_of[v] = cl
                        trail.append(v)
                        self.stats.propagations += 1
                        changed = True
            return None

        def backtrack(target_level: int) -> None:
            while trail and level_of[trail[-1]] > target_level:
                v = trail.pop()
                assign.pop(v, None)
                level_of.pop(v, None)
                reason_of.pop(v, None)

        while True:
            conflict = propagate()
            if conflict is not None:
                self.stats.conflicts += 1
                if dec_level == 0 or self.stats.conflicts > max_conflicts:
                    return None
                # Learn a simple conflict-negation clause at decision literals
                dec_lits = [
                    (-v if assign[v] else v)
                    for v in trail
                    if reason_of.get(v) is None and level_of[v] > 0
                ]
                if not dec_lits:
                    return None
                self.learned.append(dec_lits)
                self.stats.learned_clauses += 1
                dec_level -= 1
                backtrack(dec_level)
                continue

            # Pick unassigned variable
            next_v = None
            for v in range(1, self.num_vars + 1):
                if v not in assign:
                    next_v = v
                    break
            if next_v is None:
                return dict(assign)

            dec_level += 1
            self.stats.decisions += 1
            assign[next_v] = True
            level_of[next_v] = dec_level
            reason_of[next_v] = None
            trail.append(next_v)


class DPLLTSolver:
    """DPLL(T) Solver combining Interval Bounds Propagation, Linear Theory, and Branch-and-Bound."""

    def __init__(self, default_lo: int = -128, default_hi: int = 128) -> None:
        self.default_lo = default_lo
        self.default_hi = default_hi

    def _decompose_conjuncts(self, expr: SymExpr, out: List[SymExpr]) -> None:
        if isinstance(expr, SymNot) and isinstance(expr.expr, SymNot):
            self._decompose_conjuncts(expr.expr.expr, out)
        elif isinstance(expr, SymBinOp) and expr.op == "and":
            self._decompose_conjuncts(expr.left, out)
            self._decompose_conjuncts(expr.right, out)
        elif isinstance(expr, SymNot) and isinstance(expr.expr, SymBinOp) and expr.expr.op == "or":
            self._decompose_conjuncts(SymNot(expr.expr.left), out)
            self._decompose_conjuncts(SymNot(expr.expr.right), out)
        elif isinstance(expr, SymNot) and isinstance(expr.expr, SymBinOp) and expr.expr.op == "and":
            out.append(SymBinOp("or", SymNot(expr.expr.left), SymNot(expr.expr.right)))
        else:
            out.append(expr)

    def _flatten_or(self, expr: SymExpr) -> List[SymExpr]:
        if isinstance(expr, SymNot) and isinstance(expr.expr, SymNot):
            return self._flatten_or(expr.expr.expr)
        if isinstance(expr, SymBinOp) and expr.op == "or":
            return self._flatten_or(expr.left) + self._flatten_or(expr.right)
        if isinstance(expr, SymNot) and isinstance(expr.expr, SymBinOp) and expr.expr.op == "and":
            return self._flatten_or(SymNot(expr.expr.left)) + self._flatten_or(SymNot(expr.expr.right))
        return [expr]

    def _negate_comparison(self, op: str) -> str:
        inv = {"==": "!=", "!=": "==", "<": ">=", ">=": "<", "<=": ">", ">": "<="}
        return inv.get(op, op)

    def _normalize_atom(self, expr: SymExpr) -> SymExpr:
        while isinstance(expr, SymNot) and isinstance(expr.expr, SymNot):
            expr = expr.expr.expr
        if isinstance(expr, SymNot) and isinstance(expr.expr, SymBinOp):
            if expr.expr.op in ("==", "!=", "<", "<=", ">", ">="):
                return SymBinOp(
                    op=self._negate_comparison(expr.expr.op),
                    left=expr.expr.left,
                    right=expr.expr.right,
                )
        return expr

    def _propagate_bounds(
        self, atoms: List[SymExpr], bounds: Dict[str, List[int]], neq_bans: Dict[str, Set[int]]
    ) -> bool:
        """Tighten [lo, hi] bounds for single-variable and difference constraints."""
        changed = True
        iters = 0
        while changed and iters < 16:
            changed = False
            iters += 1
            for raw in atoms:
                atom = self._normalize_atom(raw)
                if not collect_vars(atom):
                    if not eval_sym_expr(atom, {}):
                        return False
                    continue
                if isinstance(atom, SymVar):
                    neq_bans[atom.name].add(0)
                    lo, hi = bounds[atom.name]
                    if lo == 0 and hi == 0:
                        return False
                    continue
                if isinstance(atom, SymNot) and isinstance(atom.expr, SymVar):
                    vname = atom.expr.name
                    lo, hi = bounds[vname]
                    lo, hi = max(lo, 0), min(hi, 0)
                    if lo > hi or 0 in neq_bans[vname]:
                        return False
                    if [lo, hi] != bounds[vname]:
                        bounds[vname] = [lo, hi]
                        changed = True
                    continue
                if not isinstance(atom, SymBinOp):
                    continue
                l, r, op = atom.left, atom.right, atom.op
                # Normalize `const op var` -> `var inv_op const`
                if isinstance(l, SymConst) and isinstance(r, SymVar):
                    flip = {"==": "==", "!=": "!=", "<": ">", "<=": ">=", ">": "<", ">=": "<="}
                    if op in flip:
                        l, r, op = r, l, flip[op]

                if isinstance(l, SymVar) and isinstance(r, SymConst):
                    lo, hi = bounds[l.name]
                    c = r.value
                    if op == "==":
                        lo, hi = max(lo, c), min(hi, c)
                    elif op == "<":
                        hi = min(hi, c - 1)
                    elif op == "<=":
                        hi = min(hi, c)
                    elif op == ">":
                        lo = max(lo, c + 1)
                    elif op == ">=":
                        lo = max(lo, c)
                    elif op == "!=":
                        neq_bans[l.name].add(c)
                    if lo > hi or (lo == hi and lo in neq_bans[l.name]):
                        return False
                    if [lo, hi] != bounds[l.name]:
                        bounds[l.name] = [lo, hi]
                        changed = True
                    continue

                # Linear offset: (var + k) op c, (k + var) op c, or (var - k) op c
                offset_var: Optional[Tuple[str, int]] = None
                if isinstance(l, SymBinOp) and isinstance(r, SymConst):
                    if l.op in ("+", "-") and isinstance(l.left, SymVar) and isinstance(l.right, SymConst):
                        offset_var = (l.left.name, l.right.value if l.op == "+" else -l.right.value)
                    elif l.op == "+" and isinstance(l.left, SymConst) and isinstance(l.right, SymVar):
                        offset_var = (l.right.name, l.left.value)
                if offset_var is not None:
                    vname, k = offset_var
                    target = r.value - k
                    lo, hi = bounds[vname]
                    if op == "==":
                        lo, hi = max(lo, target), min(hi, target)
                    elif op == "<":
                        hi = min(hi, target - 1)
                    elif op == "<=":
                        hi = min(hi, target)
                    elif op == ">":
                        lo = max(lo, target + 1)
                    elif op == ">=":
                        lo = max(lo, target)
                    elif op == "!=":
                        neq_bans[vname].add(target)
                    if lo > hi or (lo == hi and lo in neq_bans[vname]):
                        return False
                    if [lo, hi] != bounds[vname]:
                        bounds[vname] = [lo, hi]
                        changed = True

                # Two-variable relation: x < y, x == y, etc.
                elif isinstance(l, SymVar) and isinstance(r, SymVar):
                    lo_x, hi_x = bounds[l.name]
                    lo_y, hi_y = bounds[r.name]
                    if op == "==":
                        nlo, nhi = max(lo_x, lo_y), min(hi_x, hi_y)
                        if nlo > nhi:
                            return False
                        if [nlo, nhi] != [lo_x, hi_x] or [nlo, nhi] != [lo_y, hi_y]:
                            bounds[l.name] = [nlo, nhi]
                            bounds[r.name] = [nlo, nhi]
                            changed = True
                    elif op == "<":
                        if lo_x >= hi_y:
                            return False
                        nhi_x = min(hi_x, hi_y - 1)
                        nlo_y = max(lo_y, lo_x + 1)
                        if nlo_y > hi_y or lo_x > nhi_x:
                            return False
                        if nhi_x != hi_x or nlo_y != lo_y:
                            bounds[l.name][1] = nhi_x
                            bounds[r.name][0] = nlo_y
                            changed = True
                    elif op == "<=":
                        if lo_x > hi_y:
                            return False
                        nhi_x = min(hi_x, hi_y)
                        nlo_y = max(lo_y, lo_x)
                        if nhi_x != hi_x or nlo_y != lo_y:
                            bounds[l.name][1] = nhi_x
                            bounds[r.name][0] = nlo_y
                            changed = True
                    elif op == ">":
                        if hi_x <= lo_y:
                            return False
                        nlo_x = max(lo_x, lo_y + 1)
                        nhi_y = min(hi_y, hi_x - 1)
                        if nlo_x > hi_x or lo_y > nhi_y:
                            return False
                        if nlo_x != lo_x or nhi_y != hi_y:
                            bounds[l.name][0] = nlo_x
                            bounds[r.name][1] = nhi_y
                            changed = True
                    elif op == ">=":
                        if hi_x < lo_y:
                            return False
                        nlo_x = max(lo_x, lo_y)
                        nhi_y = min(hi_y, hi_x)
                        if nlo_x != lo_x or nhi_y != hi_y:
                            bounds[l.name][0] = nlo_x
                            bounds[r.name][1] = nhi_y
                            changed = True
        return True

    def solve(self, constraints: List[SymExpr], max_steps: int = 320) -> SolverResult:
        """Solve conjunction of SymExpr constraints over integer/boolean variables."""
        stats = SolverStats()
        if not constraints:
            return SolverResult(status="SAT", model={}, stats=stats)

        atoms: List[SymExpr] = []
        for c in constraints:
            self._decompose_conjuncts(c, atoms)

        # Quick constant check + disjunctive CDCL skeleton check
        var_names: Set[str] = set()
        or_clauses: List[SymExpr] = []
        conj_atoms: List[SymExpr] = []

        for a in atoms:
            collect_vars(a, var_names)
            if isinstance(a, SymBinOp) and a.op == "or":
                or_clauses.append(a)
            else:
                conj_atoms.append(a)

        sorted_vars = sorted(var_names)
        if not sorted_vars:
            ok = all(bool(eval_sym_expr(a, {})) for a in atoms)
            return SolverResult(status="SAT" if ok else "UNSAT", model={}, stats=stats)

        # Run CDCL SAT check on abstract boolean encoding of disjunctions if present
        if or_clauses:
            lit_map: Dict[str, int] = {}
            cnf: List[List[int]] = []

            def lit_id(sub: SymExpr) -> int:
                s = repr(sub)
                if s not in lit_map:
                    lit_map[s] = len(lit_map) + 1
                return lit_map[s]

            for oc in or_clauses:
                if isinstance(oc, SymBinOp) and oc.op == "or":
                    cnf.append([lit_id(oc.left), lit_id(oc.right)])
            cdcl = CDCLSATSolver(len(lit_map), cnf)
            sat_res = cdcl.solve(max_conflicts=64)
            stats.decisions += cdcl.stats.decisions
            stats.propagations += cdcl.stats.propagations
            stats.conflicts += cdcl.stats.conflicts
            if sat_res is None:
                return SolverResult(status="UNSAT", stats=stats)

        init_bounds: Dict[str, List[int]] = {v: [self.default_lo, self.default_hi] for v in sorted_vars}
        neq_bans: Dict[str, Set[int]] = {v: set() for v in sorted_vars}

        stats.theory_checks += 1
        if not self._propagate_bounds(conj_atoms, init_bounds, neq_bans):
            stats.conflicts += 1
            return SolverResult(status="UNSAT", stats=stats)

        if or_clauses:
            active_ors = list(or_clauses)
            for _ in range(len(or_clauses) + 1):
                next_ors: List[SymExpr] = []
                progressed = False
                for oc in active_ors:
                    disjuncts = self._flatten_or(oc)
                    feasible_disjuncts: List[SymExpr] = []
                    for d in disjuncts:
                        d_atoms: List[SymExpr] = []
                        self._decompose_conjuncts(d, d_atoms)
                        d_conj = [x for x in d_atoms if not (isinstance(x, SymBinOp) and x.op == "or")]
                        b_copy = {k: list(v) for k, v in init_bounds.items()}
                        n_copy = {k: set(v) for k, v in neq_bans.items()}
                        stats.theory_checks += 1
                        if self._propagate_bounds(d_conj, b_copy, n_copy):
                            feasible_disjuncts.append(d)
                    if not feasible_disjuncts:
                        stats.conflicts += 1
                        return SolverResult(status="UNSAT", stats=stats)
                    if len(feasible_disjuncts) == 1:
                        unit_atoms: List[SymExpr] = []
                        self._decompose_conjuncts(feasible_disjuncts[0], unit_atoms)
                        unit_conj = [x for x in unit_atoms if not (isinstance(x, SymBinOp) and x.op == "or")]
                        unit_ors = [x for x in unit_atoms if isinstance(x, SymBinOp) and x.op == "or"]
                        if unit_conj:
                            stats.propagations += len(unit_conj)
                            stats.theory_checks += 1
                            if not self._propagate_bounds(unit_conj, init_bounds, neq_bans):
                                stats.conflicts += 1
                                return SolverResult(status="UNSAT", stats=stats)
                        next_ors.extend(unit_ors)
                        progressed = True
                    else:
                        next_ors.append(oc)
                active_ors = next_ors
                if not progressed or not active_ors:
                    break

        # Try fast witness points first (low, 0, high, mid)
        def check_model(cand: Dict[str, int]) -> bool:
            for a in atoms:
                val = eval_sym_expr(a, cand)
                if not val:
                    return False
            return True

        # Backtracking DPLL(T) domain splitting search
        steps = [0]

        def search(bounds: Dict[str, List[int]]) -> Optional[Dict[str, int]]:
            steps[0] += 1
            if steps[0] > max_steps:
                return None
            stats.theory_checks += 1

            # Pick candidate values from current intervals
            witness: Dict[str, int] = {}
            for v in sorted_vars:
                lo, hi = bounds[v]
                bans = neq_bans[v]
                picked = lo
                for probe in (0, 1, -1, lo, hi, (lo + hi) // 2):
                    if lo <= probe <= hi and probe not in bans:
                        picked = probe
                        break
                else:
                    for probe in range(lo, min(hi + 1, lo + 16)):
                        if probe not in bans:
                            picked = probe
                            break
                witness[v] = picked

            if check_model(witness):
                return witness

            # Find widest splittable variable
            split_var = None
            best_width = 0
            for v in sorted_vars:
                lo, hi = bounds[v]
                w = hi - lo
                if w > best_width:
                    best_width = w
                    split_var = v

            if split_var is None:
                stats.conflicts += 1
                return None

            lo, hi = bounds[split_var]
            if best_width <= 6:
                # Enumerate small discrete domain directly
                for val in range(lo, hi + 1):
                    if val in neq_bans[split_var]:
                        continue
                    sub_b = {k: list(b) for k, b in bounds.items()}
                    sub_b[split_var] = [val, val]
                    stats.decisions += 1
                    res_m = search(sub_b)
                    if res_m is not None:
                        return res_m
                return None

            mid = (lo + hi) // 2
            stats.decisions += 1
            for sub_lo, sub_hi in ((lo, mid), (mid + 1, hi)):
                sub_b = {k: list(b) for k, b in bounds.items()}
                sub_b[split_var] = [sub_lo, sub_hi]
                res_m = search(sub_b)
                if res_m is not None:
                    return res_m
            stats.conflicts += 1
            return None

        model = search(init_bounds)
        if model is not None:
            return SolverResult(status="SAT", model=model, stats=stats)
        status = "UNKNOWN" if steps[0] >= max_steps else "UNSAT"
        return SolverResult(status=status, model={}, stats=stats)
