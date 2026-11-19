"""Control Flow Graph, Cooper-Harvey-Kennedy Dominators, Natural Loops, and Data-Flow Graph."""

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Set, Tuple, Any

from hyperion.ir.ssa import (
    IRFunction,
    SSAVar,
    CondBranchOp,
    JumpOp,
    ReturnOp,
    SinkOp,
    AssertOp,
)


@dataclass
class CFGAnalysisResult:
    rpo_order: List[int] = field(default_factory=list)
    idom: Dict[int, int] = field(default_factory=dict)
    dom_tree: Dict[int, List[int]] = field(default_factory=dict)
    dom_frontiers: Dict[int, List[int]] = field(default_factory=dict)
    back_edges: List[Tuple[int, int]] = field(default_factory=list)
    natural_loops: Dict[int, Set[int]] = field(default_factory=dict)
    cyclomatic_complexity: int = 1
    def_blocks: Dict[str, int] = field(default_factory=dict)
    use_edges: List[Tuple[int, int, str]] = field(default_factory=list)

    def to_graph_json(
        self,
        fn: IRFunction,
        dead_blocks: Optional[Set[int]] = None,
        dead_edges: Optional[Set[Tuple[int, int]]] = None,
        dead_reasons: Optional[Dict[int, str]] = None,
    ) -> Dict[str, Any]:
        """Serialize CFG, Dominator tree, and Data-Flow edges for Canvas rendering."""
        nodes = []
        edges = []
        loop_nodes: Set[int] = set()
        for body in self.natural_loops.values():
            loop_nodes.update(body)

        dead_blk_set: Set[int] = dead_blocks or set()
        dead_edge_set: Set[Tuple[int, int]] = dead_edges or set()
        reason_map: Dict[int, str] = dead_reasons or {}

        for bid in sorted(fn.blocks.keys()):
            blk = fn.blocks[bid]
            has_sink = any(isinstance(ins, SinkOp) for ins in blk.instructions)
            has_assert = any(isinstance(ins, AssertOp) for ins in blk.instructions)
            is_exit = any(isinstance(ins, ReturnOp) for ins in blk.instructions) or not blk.succs
            inst_preview = [ins.format() for ins in blk.instructions[:6]]
            if len(blk.instructions) > 6:
                inst_preview.append(f"... (+{len(blk.instructions) - 6} lệnh nữa)")
            is_dead = bid in dead_blk_set
            has_dead_in = any(t == bid for _, t in dead_edge_set)
            dead_reason = (
                ""
                if not is_dead
                else reason_map.get(
                    bid,
                    "Nhánh rẽ không khả thi (UNSAT)"
                    if has_dead_in
                    else "Khối lệnh không thể tiếp cận (UNSAT)",
                )
            )
            nodes.append(
                {
                    "id": bid,
                    "label": f"B{bid}: {blk.label}",
                    "inst_count": len(blk.instructions),
                    "instructions": inst_preview,
                    "is_entry": bid == fn.entry_id,
                    "is_exit": is_exit,
                    "is_loop_header": bid in self.natural_loops,
                    "in_loop": bid in loop_nodes,
                    "has_sink": has_sink,
                    "has_assert": has_assert,
                    "idom": self.idom.get(bid, bid),
                    "is_dead": is_dead,
                    "dead_reason": dead_reason,
                }
            )
            for s in blk.succs:
                edge_type = "flow"
                if blk.instructions and isinstance(blk.instructions[-1], CondBranchOp):
                    br = blk.instructions[-1]
                    if s == br.true_target:
                        edge_type = "true"
                    elif s == br.false_target:
                        edge_type = "false"
                is_back = (bid, s) in self.back_edges
                is_dead_edge = (
                    ((bid, s) in dead_edge_set)
                    if dead_edges is not None
                    else (bid in dead_blk_set or s in dead_blk_set)
                )
                edges.append(
                    {
                        "source": bid,
                        "target": s,
                        "kind": "back_edge" if is_back else edge_type,
                        "is_dead": is_dead_edge,
                    }
                )

        dom_edges = [
            {"source": parent, "target": child}
            for parent, children in self.dom_tree.items()
            for child in children
            if parent != child
        ]
        dfg_edges = [
            {"source": src_b, "target": dst_b, "var": var_name}
            for src_b, dst_b, var_name in self.use_edges[:80]
        ]
        return {
            "function": fn.name,
            "language": fn.source_lang,
            "cyclomatic_complexity": self.cyclomatic_complexity,
            "loop_count": len(self.natural_loops),
            "nodes": nodes,
            "edges": edges,
            "dom_edges": dom_edges,
            "dfg_edges": dfg_edges,
        }


def compute_cfg_analysis(fn: IRFunction) -> CFGAnalysisResult:
    """Run full CFG reachability, Cooper-Harvey-Kennedy dominators, loops, and Def-Use chains."""
    res = CFGAnalysisResult()
    if not fn.blocks or fn.entry_id not in fn.blocks:
        return res

    # Normalize preds/succs from terminating instructions when missing
    for blk in fn.blocks.values():
        blk.preds.clear()
        if not blk.succs and blk.instructions:
            last = blk.instructions[-1]
            if isinstance(last, CondBranchOp):
                blk.succs = [last.true_target, last.false_target]
            elif isinstance(last, JumpOp):
                blk.succs = [last.target]

    for bid, blk in fn.blocks.items():
        dedup = []
        for s in blk.succs:
            if s in fn.blocks and s not in dedup:
                dedup.append(s)
        blk.succs = dedup
        for s in blk.succs:
            if bid not in fn.blocks[s].preds:
                fn.blocks[s].preds.append(bid)

    # 1. Reverse Post-Order (RPO) from entry
    visited: Set[int] = set()
    postorder: List[int] = []

    def dfs(u: int) -> None:
        visited.add(u)
        for v in fn.blocks[u].succs:
            if v not in visited:
                dfs(v)
        postorder.append(u)

    dfs(fn.entry_id)
    rpo = list(reversed(postorder))
    res.rpo_order = rpo
    rpo_idx = {b: i for i, b in enumerate(rpo)}

    # 2. Cooper-Harvey-Kennedy iterative dominator algorithm
    idom: Dict[int, int] = {fn.entry_id: fn.entry_id}

    def intersect(b1: int, b2: int) -> int:
        f1, f2 = b1, b2
        while f1 != f2:
            while rpo_idx[f1] > rpo_idx[f2]:
                f1 = idom[f1]
            while rpo_idx[f2] > rpo_idx[f1]:
                f2 = idom[f2]
        return f1

    changed = True
    while changed:
        changed = False
        for b in rpo:
            if b == fn.entry_id:
                continue
            processed_preds = [p for p in fn.blocks[b].preds if p in idom]
            if not processed_preds:
                continue
            new_idom = processed_preds[0]
            for p in processed_preds[1:]:
                new_idom = intersect(p, new_idom)
            if idom.get(b) != new_idom:
                idom[b] = new_idom
                changed = True

    res.idom = idom
    for b in rpo:
        res.dom_tree[b] = []
    for b, p in idom.items():
        if b != p:
            res.dom_tree.setdefault(p, []).append(b)

    # 3. Dominance Frontiers
    df: Dict[int, Set[int]] = {b: set() for b in rpo}
    for b in rpo:
        preds = [p for p in fn.blocks[b].preds if p in rpo_idx]
        if len(preds) >= 2:
            for p in preds:
                runner = p
                while runner != idom.get(b, fn.entry_id):
                    df[runner].add(b)
                    next_runner = idom.get(runner, fn.entry_id)
                    if next_runner == runner:
                        break
                    runner = next_runner
    res.dom_frontiers = {b: sorted(s) for b, s in df.items()}
    for b, frontier in res.dom_frontiers.items():
        fn.blocks[b].dom_frontier = frontier

    # 4. Natural loops via dominance check (u -> v is back-edge iff v dominates u)
    def dominates(a: int, b: int) -> bool:
        cur = b
        while cur != a:
            nxt = idom.get(cur)
            if nxt is None or nxt == cur:
                return False
            cur = nxt
        return True

    for u in rpo:
        for v in fn.blocks[u].succs:
            if v in rpo_idx and dominates(v, u):
                res.back_edges.append((u, v))
                loop_body: Set[int] = {v, u}
                stack = [u] if u != v else []
                while stack:
                    m = stack.pop()
                    for p in fn.blocks[m].preds:
                        if p in rpo_idx and p not in loop_body:
                            loop_body.add(p)
                            stack.append(p)
                res.natural_loops.setdefault(v, set()).update(loop_body)

    # 5. Cyclomatic complexity M = E - N + 2
    num_nodes = len(rpo)
    num_edges = sum(len([s for s in fn.blocks[b].succs if s in rpo_idx]) for b in rpo)
    res.cyclomatic_complexity = max(1, num_edges - num_nodes + 2)

    # 6. Def-Use DFG chain mapping across basic blocks
    for p in fn.params:
        res.def_blocks[p.key()] = fn.entry_id
    for b in rpo:
        for ins in fn.blocks[b].instructions:
            for d in ins.defs():
                res.def_blocks[d.key()] = b
    seen_dfg: Set[Tuple[int, int, str]] = set()
    for b in rpo:
        for ins in fn.blocks[b].instructions:
            for u in ins.uses():
                if isinstance(u, SSAVar):
                    src_b = res.def_blocks.get(u.key(), fn.entry_id)
                    edge = (src_b, b, u.key())
                    if src_b != b and edge not in seen_dfg:
                        seen_dfg.add(edge)
                        res.use_edges.append(edge)

    return res
