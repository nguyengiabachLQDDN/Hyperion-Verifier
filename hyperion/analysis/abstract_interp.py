"""Worklist Fixed-Point Abstract Interpreter with Interval + Taint Lattices and Widening."""

from dataclasses import dataclass, field, asdict
import math
from typing import Dict, List, Optional, Set, Tuple, Any

from hyperion.ir.cfg import CFGAnalysisResult
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
    IRValue,
    PhiOp,
    ReturnOp,
    SSAVar,
    SinkOp,
    UnaryOp,
)


INF = 10 ** 12


@dataclass(frozen=True)
class Interval:
    """Closed integer/real interval lattice [lo, hi] with bottom representation."""

    lo: float
    hi: float
    is_bottom: bool = False

    @classmethod
    def bottom(cls) -> "Interval":
        return cls(0, -1, is_bottom=True)

    @classmethod
    def top(cls) -> "Interval":
        return cls(-INF, INF, is_bottom=False)

    @classmethod
    def const(cls, v: float) -> "Interval":
        return cls(v, v, is_bottom=False)

    def join(self, other: "Interval") -> "Interval":
        if self.is_bottom:
            return other
        if other.is_bottom:
            return self
        return Interval(min(self.lo, other.lo), max(self.hi, other.hi))

    def meet(self, other: "Interval") -> "Interval":
        if self.is_bottom or other.is_bottom:
            return Interval.bottom()
        lo = max(self.lo, other.lo)
        hi = min(self.hi, other.hi)
        if lo > hi:
            return Interval.bottom()
        return Interval(lo, hi)

    def widen(self, other: "Interval") -> "Interval":
        if self.is_bottom:
            return other
        if other.is_bottom:
            return self
        lo = -INF if other.lo < self.lo else self.lo
        hi = INF if other.hi > self.hi else self.hi
        return Interval(lo, hi)

    def contains_zero(self) -> bool:
        if self.is_bottom:
            return False
        return self.lo <= 0 <= self.hi

    def format(self) -> str:
        if self.is_bottom:
            return "⊥"
        lo_s = "-∞" if self.lo <= -INF else str(int(self.lo) if self.lo == int(self.lo) else round(self.lo, 2))
        hi_s = "+∞" if self.hi >= INF else str(int(self.hi) if self.hi == int(self.hi) else round(self.hi, 2))
        return f"[{lo_s}, {hi_s}]"


def _eval_interval_binop(op: str, a: Interval, b: Interval) -> Interval:
    if a.is_bottom or b.is_bottom:
        return Interval.bottom()
    if op == "+":
        return Interval(max(-INF, a.lo + b.lo), min(INF, a.hi + b.hi))
    if op == "-":
        return Interval(max(-INF, a.lo - b.hi), min(INF, a.hi - b.lo))
    if op == "*":
        products = [a.lo * b.lo, a.lo * b.hi, a.hi * b.lo, a.hi * b.hi]
        return Interval(max(-INF, min(products)), min(INF, max(products)))
    if op in ("/", "//"):
        if b.contains_zero():
            return Interval.top()
        quos = [a.lo / b.lo, a.lo / b.hi, a.hi / b.lo, a.hi / b.hi]
        if op == "//":
            quos = [math.floor(q) for q in quos]
        return Interval(max(-INF, min(quos)), min(INF, max(quos)))
    if op == "%":
        if b.hi <= 0 or b.contains_zero():
            return Interval.top()
        return Interval(0, max(0, b.hi - 1))
    if op in ("==", "!=", "<", "<=", ">", ">=", "and", "or"):
        return Interval(0, 1)
    if op == "&":
        if b.lo >= 0 and b.hi < INF:
            return Interval(0, b.hi)
        return Interval.top()
    return Interval.top()


@dataclass(frozen=True)
class TaintValue:
    tainted: bool = False
    sources: Tuple[str, ...] = ()

    @classmethod
    def clean(cls) -> "TaintValue":
        return cls(False, ())

    @classmethod
    def from_source(cls, src: str) -> "TaintValue":
        return cls(True, (src,))

    def join(self, other: "TaintValue") -> "TaintValue":
        if not self.tainted and not other.tainted:
            return TaintValue.clean()
        merged = tuple(sorted(set(self.sources) | set(other.sources)))
        return TaintValue(True, merged)


@dataclass
class AbstractFinding:
    kind: str
    severity: str
    function: str
    line: int
    block_id: int
    message: str

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)


@dataclass
class AbstractAnalysisResult:
    function: str
    iterations: int = 0
    intervals: Dict[str, str] = field(default_factory=dict)
    tainted_vars: List[str] = field(default_factory=list)
    findings: List[AbstractFinding] = field(default_factory=list)


def run_abstract_interpretation(
    fn: IRFunction, cfg: CFGAnalysisResult, max_iterations: int = 250
) -> AbstractAnalysisResult:
    """Run chaotic worklist abstract interpretation with widening over Unified SSA IR."""
    res = AbstractAnalysisResult(function=fn.name)
    if not fn.blocks or fn.entry_id not in fn.blocks:
        return res

    intervals: Dict[str, Interval] = {}
    taints: Dict[str, TaintValue] = {}

    for p in fn.params:
        intervals[p.key()] = Interval.top()
        # Heuristic: parameters named payload/query/cmd/user_input start tainted
        pname = p.name.lower()
        if any(tok in pname for tok in ("input", "user", "query", "payload", "cmd", "packet", "raw", "untrusted")):
            taints[p.key()] = TaintValue.from_source(f"param:{p.name}")
        else:
            taints[p.key()] = TaintValue.clean()

    def get_iv(v: IRValue) -> Interval:
        if isinstance(v, Const):
            if isinstance(v.value, bool):
                return Interval.const(1 if v.value else 0)
            if isinstance(v.value, (int, float)):
                return Interval.const(float(v.value))
            return Interval.top()
        if isinstance(v, SSAVar):
            return intervals.get(v.key(), Interval.top())
        return Interval.top()

    def get_taint(v: IRValue) -> TaintValue:
        if isinstance(v, SSAVar):
            return taints.get(v.key(), TaintValue.clean())
        return TaintValue.clean()

    worklist: List[int] = list(cfg.rpo_order or sorted(fn.blocks.keys()))
    in_worklist: Set[int] = set(worklist)
    block_visits: Dict[int, int] = {}
    loop_headers = set(cfg.natural_loops.keys())

    while worklist and res.iterations < max_iterations:
        res.iterations += 1
        bid = worklist.pop(0)
        in_worklist.discard(bid)
        blk = fn.blocks[bid]
        visits = block_visits.get(bid, 0) + 1
        block_visits[bid] = visits
        changed = False

        for ins in blk.instructions:
            if ins.dest is None:
                continue
            key = ins.dest.key()
            old_iv = intervals.get(key, Interval.bottom())
            old_t = taints.get(key, TaintValue.clean())
            new_iv = old_iv
            new_t = old_t

            if isinstance(ins, AssignOp):
                new_iv = get_iv(ins.src)
                new_t = get_taint(ins.src)
            elif isinstance(ins, UnaryOp):
                op_iv = get_iv(ins.operand)
                if ins.op == "-":
                    new_iv = Interval(-op_iv.hi, -op_iv.lo) if not op_iv.is_bottom else Interval.bottom()
                elif ins.op in ("not", "!"):
                    new_iv = Interval(0, 1)
                else:
                    new_iv = Interval.top()
                new_t = get_taint(ins.operand)
            elif isinstance(ins, BinaryOp):
                new_iv = _eval_interval_binop(ins.op, get_iv(ins.left), get_iv(ins.right))
                new_t = get_taint(ins.left).join(get_taint(ins.right))
            elif isinstance(ins, PhiOp):
                acc_iv = Interval.bottom()
                acc_t = TaintValue.clean()
                for _, val in ins.incomings:
                    acc_iv = acc_iv.join(get_iv(val))
                    acc_t = acc_t.join(get_taint(val))
                new_iv = acc_iv
                new_t = acc_t
            elif isinstance(ins, CallOp):
                new_iv = Interval.top()
                if ins.is_taint_source:
                    new_t = TaintValue.from_source(f"call:{ins.callee}")
                elif ins.is_sanitizer:
                    new_t = TaintValue.clean()
                else:
                    acc_t = TaintValue.clean()
                    for a in ins.args:
                        acc_t = acc_t.join(get_taint(a))
                    new_t = acc_t
            elif isinstance(ins, (ArrayLoadOp, SinkOp)):
                new_iv = Interval.top()
                acc_t = TaintValue.clean()
                for u in ins.uses():
                    acc_t = acc_t.join(get_taint(u))
                new_t = acc_t

            # Apply widening at loop headers after 2 visits to guarantee termination
            if bid in loop_headers and visits > 2:
                joined_iv = old_iv.widen(new_iv)
            else:
                joined_iv = old_iv.join(new_iv)
            joined_t = old_t.join(new_t)

            if joined_iv != old_iv or joined_t != old_t:
                intervals[key] = joined_iv
                taints[key] = joined_t
                changed = True

        if changed:
            for succ in blk.succs:
                if succ not in in_worklist:
                    worklist.append(succ)
                    in_worklist.add(succ)

    # Emit static findings after fixed-point convergence
    seen_keys: Set[Tuple[str, int, int]] = set()
    for bid in cfg.rpo_order or sorted(fn.blocks.keys()):
        blk = fn.blocks[bid]
        for ins in blk.instructions:
            if isinstance(ins, BinaryOp) and ins.op in ("/", "//", "%"):
                div_iv = get_iv(ins.right)
                if div_iv.contains_zero():
                    fkey = ("DIV_BY_ZERO_RISK", bid, ins.line)
                    if fkey not in seen_keys:
                        seen_keys.add(fkey)
                        res.findings.append(
                            AbstractFinding(
                                kind="DIV_BY_ZERO_RISK",
                                severity="HIGH",
                                function=fn.name,
                                line=ins.line,
                                block_id=bid,
                                message=f"Số chia {ins.right.format()} có khoảng giá trị {div_iv.format()} chứa 0 (nguy cơ chia cho 0)",
                            )
                        )
            elif isinstance(ins, (ArrayLoadOp, ArrayStoreOp)):
                idx_iv = get_iv(ins.index)
                if idx_iv.lo < 0 or (ins.known_length is not None and idx_iv.hi >= ins.known_length):
                    fkey = ("BUFFER_INDEX_OOB", bid, ins.line)
                    if fkey not in seen_keys:
                        seen_keys.add(fkey)
                        res.findings.append(
                            AbstractFinding(
                                kind="BUFFER_INDEX_OOB",
                                severity="HIGH",
                                function=fn.name,
                                line=ins.line,
                                block_id=bid,
                                message=f"Chỉ số mảng {ins.index.format()} với khoảng giá trị {idx_iv.format()} có thể vượt giới hạn (độ dài={ins.known_length if ins.known_length is not None else '?'})",
                            )
                        )
            elif isinstance(ins, SinkOp):
                for arg in ins.args:
                    tv = get_taint(arg)
                    if tv.tainted:
                        fkey = ("TAINT_SINK_FLOW", bid, ins.line)
                        if fkey not in seen_keys:
                            seen_keys.add(fkey)
                            res.findings.append(
                                AbstractFinding(
                                    kind="TAINT_SINK_FLOW",
                                    severity="CRITICAL",
                                    function=fn.name,
                                    line=ins.line,
                                    block_id=bid,
                                    message=f"Dữ liệu chưa kiểm duyệt (taint) từ {','.join(tv.sources)} đi tới sink '{ins.sink_kind}'",
                                )
                            )
            elif isinstance(ins, CondBranchOp):
                civ = get_iv(ins.cond)
                if not civ.is_bottom and civ.lo == civ.hi:
                    branch_taken = "TRUE" if civ.lo != 0 else "FALSE"
                    fkey = ("CONSTANT_BRANCH", bid, ins.line)
                    if fkey not in seen_keys:
                        seen_keys.add(fkey)
                        res.findings.append(
                            AbstractFinding(
                                kind="CONSTANT_BRANCH",
                                severity="INFO",
                                function=fn.name,
                                line=ins.line,
                                block_id=bid,
                                message=f"Điều kiện rẽ nhánh luôn cho kết quả tĩnh là {branch_taken}",
                            )
                        )

    res.intervals = {k: iv.format() for k, iv in sorted(intervals.items())[:40]}
    res.tainted_vars = sorted(k for k, tv in taints.items() if tv.tainted)
    return res
