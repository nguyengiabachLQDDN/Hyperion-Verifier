"""Multiprocessing Worker Pool Orchestrator, Safety Watchdog & Cross-Machine Scorer."""

import multiprocessing
import os
import threading
import time
from typing import Any, Dict, List, Optional, Tuple

from hyperion.analysis.abstract_interp import run_abstract_interpretation
from hyperion.config import RunConfig
from hyperion.corpus.generator import (
    SourceUnit,
    generate_procedural_corpus,
    load_custom_directory_corpus,
    load_self_host_corpus,
)
from hyperion.frontends.python_lifter import lift_python_source
from hyperion.frontends.ts_dsl_parser import parse_ts_dsl_source
from hyperion.hardware.telemetry import (
    HardwareMonitor,
    SafetyGovernor,
    get_machine_profile,
    set_worker_low_priority,
)
from hyperion.ir.cfg import compute_cfg_analysis
from hyperion.ir.optimizer import optimize_function_ssa
from hyperion.ir.ssa import IRModule
from hyperion.mutation.engine import run_mutation_testing
from hyperion.storage.db import LeaderboardDB
from hyperion.symbolic.engine import run_symbolic_execution
from hyperion.testgen.generator import generate_all_frameworks


_WORKER_ARENA: List[Any] = []
_WORKER_ARENA_BYTES: int = 0


def _worker_init(below_normal: bool) -> None:
    """Initialize each multiprocessing worker with BELOW_NORMAL priority."""
    global _WORKER_ARENA, _WORKER_ARENA_BYTES
    _WORKER_ARENA = []
    _WORKER_ARENA_BYTES = 0
    if below_normal:
        set_worker_low_priority()


def _retain_in_worker_arena(
    module: IRModule,
    cfg_snapshots: List[Any],
    per_worker_budget_mb: float,
    min_free_ram_pct: float,
) -> int:
    """Retain live IR/CFG artifacts + contiguous IR bitcode slab in RAM up to safe budget."""
    global _WORKER_ARENA, _WORKER_ARENA_BYTES
    if per_worker_budget_mb <= 0:
        return 0

    budget_bytes = int(per_worker_budget_mb * 1024 * 1024)
    if _WORKER_ARENA_BYTES >= budget_bytes:
        # Touch existing arena slabs to stress memory bandwidth without growing past cap
        if _WORKER_ARENA:
            _, slab = _WORKER_ARENA[_WORKER_ARENA_BYTES % len(_WORKER_ARENA)]
            _ = sum(slab[::4096])
        return _WORKER_ARENA_BYTES

    # Check host physical free RAM floor before allocating a new slab
    mon = HardwareMonitor()
    _, _, free_pct, _ = mon._sample_memory()
    if free_pct <= (min_free_ram_pct + 2.0):
        return _WORKER_ARENA_BYTES

    # Allocate a 4 MB IR/Clause cache slab populated from module SSA bytecode patterns
    slab_bytes = min(4 * 1024 * 1024, max(256 * 1024, budget_bytes - _WORKER_ARENA_BYTES))
    slab = bytearray(slab_bytes)
    seed_byte = (len(module.functions) * 37 + len(module.source_code)) & 0xFF
    for off in range(0, slab_bytes, 4096):
        slab[off] = (seed_byte + (off >> 12)) & 0xFF

    _WORKER_ARENA.append(((module, cfg_snapshots), slab))
    _WORKER_ARENA_BYTES += slab_bytes
    return _WORKER_ARENA_BYTES


def _analyze_unit_task(payload: Tuple[SourceUnit, Dict[str, Any]]) -> Dict[str, Any]:
    """Top-level pickleable worker task running the complete compiler + verification pipeline in RAM."""
    unit, cfg_dict = payload
    t0 = time.perf_counter()

    # 1. Polyglot Frontend Lift to Unified SSA IR
    if unit.language == "python":
        module: IRModule = lift_python_source(
            unit.source_code, module_name=unit.name, source_file=unit.source_file
        )
    else:
        module = parse_ts_dsl_source(
            unit.source_code, module_name=unit.name, source_file=unit.source_file
        )

    enable_opt = bool(cfg_dict.get("enable_optimizer", True))
    enable_ai = bool(cfg_dict.get("enable_abstract_interp", True))
    enable_sym = bool(cfg_dict.get("enable_symbolic", True))
    enable_mut = bool(cfg_dict.get("enable_mutation", True))
    max_paths = int(cfg_dict.get("max_symbolic_paths_per_fn", 96))
    max_mutants = int(cfg_dict.get("max_mutants_per_fn", 60))
    gas_limit = int(cfg_dict.get("instruction_gas_limit", 4000))
    per_worker_arena_mb = float(cfg_dict.get("per_worker_arena_mb", 0.0))
    min_free_ram_pct = float(cfg_dict.get("min_free_system_ram_pct", 25.0))

    fn_reports: List[Dict[str, Any]] = []
    cfg_snapshots: List[Any] = []
    totals = {
        "functions": len(module.functions),
        "loc": unit.loc,
        "blocks": 0,
        "ssa_instructions": 0,
        "opt_folded": 0,
        "opt_dce": 0,
        "ai_iterations": 0,
        "ai_findings": 0,
        "paths_explored": 0,
        "feasible_paths": 0,
        "smt_queries": 0,
        "smt_decisions": 0,
        "smt_conflicts": 0,
        "counterexamples": 0,
        "mutants_evaluated": 0,
        "mutants_killed": 0,
        "mutants_survived": 0,
        "vm_steps": 0,
    }

    for fn in module.functions:
        # 2. SSA Optimization passes
        opt_stats = optimize_function_ssa(fn) if enable_opt else None
        # 3. CFG, Cooper-Harvey-Kennedy Dominators, Natural Loops, Def-Use DFG
        cfg = compute_cfg_analysis(fn)
        if per_worker_arena_mb > 0:
            cfg_snapshots.append(cfg)

        block_cnt = len(fn.blocks)
        inst_cnt = fn.instruction_count()
        totals["blocks"] += block_cnt
        totals["ssa_instructions"] += inst_cnt
        if opt_stats:
            totals["opt_folded"] += opt_stats.constants_folded
            totals["opt_dce"] += opt_stats.dead_instructions_removed

        # 4. Abstract Interpretation (Interval + Taint)
        ai_res = run_abstract_interpretation(fn, cfg) if enable_ai else None
        if ai_res:
            totals["ai_iterations"] += ai_res.iterations
            totals["ai_findings"] += len(ai_res.findings)

        # 5. Symbolic Execution + From-Scratch DPLL(T) SMT Solving
        sym_res = run_symbolic_execution(fn, max_paths=max_paths) if enable_sym else None
        vectors = sym_res.synthesized_test_vectors if sym_res else []
        if sym_res:
            totals["paths_explored"] += sym_res.paths_explored
            totals["feasible_paths"] += sym_res.feasible_paths
            totals["smt_queries"] += sym_res.smt_queries
            totals["smt_decisions"] += sym_res.smt_decisions
            totals["smt_conflicts"] += sym_res.smt_conflicts
            totals["counterexamples"] += len(sym_res.counterexamples)

        # 6. 100% In-Memory Mutation Testing
        mut_res = (
            run_mutation_testing(fn, vectors, max_mutants=max_mutants, gas_limit=gas_limit)
            if enable_mut
            else None
        )
        if mut_res:
            totals["mutants_evaluated"] += mut_res.total_mutants
            totals["mutants_killed"] += mut_res.killed
            totals["mutants_survived"] += mut_res.survived
            totals["vm_steps"] += mut_res.total_vm_steps

        extra_vecs = mut_res.witness_vectors if mut_res else None
        gen_tests = generate_all_frameworks(fn, symbolic_res=sym_res, extra_vectors=extra_vecs)
        dead_blocks = sym_res.dead_block_ids if sym_res else None
        dead_edges = sym_res.dead_edges if sym_res else None

        # Compact per-function report for UI inspection
        fn_reports.append(
            {
                "name": fn.name,
                "language": fn.source_lang,
                "source_file": fn.source_file,
                "line_start": fn.line_start,
                "line_end": fn.line_end,
                "source_code": fn.source_code,
                "ssa_dump": fn.dump_ssa(),
                "blocks": block_cnt,
                "instructions": inst_cnt,
                "cyclomatic_complexity": cfg.cyclomatic_complexity,
                "loop_count": len(cfg.natural_loops),
                "cfg_graph": cfg.to_graph_json(fn, dead_blocks=dead_blocks, dead_edges=dead_edges),
                "intervals": ai_res.intervals if ai_res else {},
                "tainted_vars": ai_res.tainted_vars if ai_res else [],
                "ai_findings": [f.to_dict() for f in ai_res.findings] if ai_res else [],
                "dead_branches": sym_res.dead_branches if sym_res else [],
                "paths_explored": sym_res.paths_explored if sym_res else 0,
                "smt_queries": sym_res.smt_queries if sym_res else 0,
                "counterexamples": [c.to_dict() for c in sym_res.counterexamples] if sym_res else [],
                "generated_tests": gen_tests,
                "kill_witnesses": mut_res.kill_witnesses if mut_res else [],
                "mutation": {
                    "total": mut_res.total_mutants if mut_res else 0,
                    "killed": mut_res.killed if mut_res else 0,
                    "survived": mut_res.survived if mut_res else 0,
                    "initial_survived": mut_res.initial_survived if mut_res else 0,
                    "newly_killed": mut_res.newly_killed if mut_res else 0,
                    "score_pct": mut_res.mutation_score_pct if mut_res else 0.0,
                    "vm_steps": mut_res.total_vm_steps if mut_res else 0,
                    "records": [r.to_dict() for r in mut_res.records] if mut_res else [],
                },
            }
        )

    arena_bytes = _retain_in_worker_arena(
        module, cfg_snapshots, per_worker_arena_mb, min_free_ram_pct
    )

    elapsed = max(1e-6, time.perf_counter() - t0)
    return {
        "unit_name": unit.name,
        "language": unit.language,
        "source_file": unit.source_file,
        "pid": os.getpid(),
        "arena_mb": round(arena_bytes / (1024 * 1024), 1),
        "elapsed_sec": round(elapsed, 4),
        "parse_errors": module.parse_errors,
        "totals": totals,
        "functions": fn_reports,
    }


def _compute_scores(totals: Dict[str, int], duration_sec: float, workers_used: int) -> Dict[str, float]:
    """Derive normalized Cross-Machine Benchmark scores from throughput and analysis depth."""
    dt = max(0.05, duration_sec)
    ssa_rate = (totals["ssa_instructions"] + totals["blocks"] * 3 + totals["ai_iterations"] * 2) / dt
    smt_rate = (totals["smt_queries"] * 12 + totals["smt_decisions"] * 3 + totals["paths_explored"] * 8) / dt
    mut_rate = (totals["mutants_evaluated"] * 25 + totals["vm_steps"] * 0.25) / dt
    loc_rate = totals["loc"] / dt

    ssa_cfg_score = round(ssa_rate * 0.85, 1)
    smt_symbolic_score = round(smt_rate * 0.45, 1)
    mutation_score = round(mut_rate * 0.35, 1)
    parallel_throughput = round((loc_rate * 1.4 + (totals["functions"] / dt) * 18.0), 1)
    composite = round(
        ssa_cfg_score * 0.25
        + smt_symbolic_score * 0.35
        + mutation_score * 0.30
        + parallel_throughput * 0.10,
        1,
    )
    return {
        "composite_score": composite,
        "ssa_cfg_score": ssa_cfg_score,
        "smt_symbolic_score": smt_symbolic_score,
        "mutation_score": mutation_score,
        "parallel_throughput": parallel_throughput,
        "loc_per_sec": round(totals["loc"] / dt, 1),
        "ssa_per_sec": round(totals["ssa_instructions"] / dt, 1),
        "smt_per_sec": round(totals["smt_queries"] / dt, 1),
        "mutants_per_sec": round(totals["mutants_evaluated"] / dt, 1),
        "workers_used": float(workers_used),
    }


class HyperionOrchestrator:
    """Thread-safe coordinator managing multiprocessing pools, telemetry streaming, and emergency stops."""

    def __init__(self, db: Optional[LeaderboardDB] = None) -> None:
        self.db = db or LeaderboardDB()
        self.monitor = HardwareMonitor()
        self.machine = get_machine_profile()
        self._lock = threading.RLock()
        self._stop_event = threading.Event()
        self._active_pool: Optional[multiprocessing.pool.Pool] = None
        self._runner_thread: Optional[threading.Thread] = None

        self.state: str = "IDLE"  # "IDLE" | "RUNNING" | "COMPLETED" | "STOPPED" | "SAFETY_TRIPPED"
        self.stop_reason: str = ""
        self.active_config: Optional[Dict[str, Any]] = None
        self.progress: Dict[str, Any] = {"completed_units": 0, "total_units": 0, "pct": 0.0}
        self.totals: Dict[str, int] = self._empty_totals()
        self.scores: Dict[str, float] = {}
        self.worker_stats: Dict[int, Dict[str, Any]] = {}
        self.functions_catalog: List[Dict[str, Any]] = []
        self.findings_feed: List[Dict[str, Any]] = []
        self.telemetry_history: List[Dict[str, Any]] = []
        self.started_at: float = 0.0
        self.duration_sec: float = 0.0
        self._last_run_id: Optional[int] = None

    @staticmethod
    def _empty_totals() -> Dict[str, int]:
        return {
            "units": 0,
            "functions": 0,
            "loc": 0,
            "blocks": 0,
            "ssa_instructions": 0,
            "opt_folded": 0,
            "opt_dce": 0,
            "ai_iterations": 0,
            "ai_findings": 0,
            "paths_explored": 0,
            "feasible_paths": 0,
            "smt_queries": 0,
            "smt_decisions": 0,
            "smt_conflicts": 0,
            "counterexamples": 0,
            "mutants_evaluated": 0,
            "mutants_killed": 0,
            "mutants_survived": 0,
            "vm_steps": 0,
        }

    def _build_corpus(self, cfg: RunConfig, round_idx: int = 0) -> List[SourceUnit]:
        if cfg.corpus_source == "self_host":
            units = load_self_host_corpus()
            # If user selected heavy/extreme on self_host, clone batches for stress throughput
            if cfg.mode == "stress" and cfg.scale_factor > 1 and units:
                extra = []
                for idx in range(min(cfg.scale_factor, 6)):
                    for u in units[:10]:
                        extra.append(
                            SourceUnit(
                                name=f"{u.name}_pass{idx}",
                                language=u.language,
                                source_file=u.source_file,
                                source_code=u.source_code,
                                loc=u.loc,
                            )
                        )
                return units + extra
            return units
        if cfg.corpus_source == "custom_path":
            return load_custom_directory_corpus(cfg.custom_path)
        # Procedural torture corpus (deterministic seed in benchmark mode)
        seed = cfg.seed if cfg.mode == "benchmark" else (cfg.seed + round_idx * 9973)
        return generate_procedural_corpus(scale_factor=cfg.scale_factor, seed=seed)

    def start_run(self, cfg: RunConfig, blocking: bool = False) -> Tuple[bool, str]:
        cfg.apply_intensity_defaults()
        with self._lock:
            if self.state == "RUNNING":
                return False, "Một tác vụ phân tích đang chạy, vui lòng đợi hoặc bấm Dừng khẩn cấp."
            self._stop_event.clear()
            self.state = "RUNNING"
            self.stop_reason = ""
            self.active_config = cfg.to_dict()
            self.totals = self._empty_totals()
            self.scores = {}
            self.worker_stats = {}
            self.functions_catalog = []
            self.findings_feed = []
            self.telemetry_history = []
            self.progress = {"completed_units": 0, "total_units": 0, "pct": 0.0}
            self.started_at = time.monotonic()
            self.duration_sec = 0.0
            self._last_run_id = None

        if blocking:
            self._execute_run(cfg)
            return True, self.state

        t = threading.Thread(target=self._execute_run, args=(cfg,), daemon=True)
        self._runner_thread = t
        t.start()
        return True, "STARTED"

    def emergency_stop(self, reason: str = "Đã kích hoạt Dừng khẩn cấp theo yêu cầu của người vận hành.") -> Dict[str, Any]:
        """Immediately halt running worker pool (<50ms) and transition to safe stopped state."""
        self._stop_event.set()
        with self._lock:
            pool = self._active_pool
            if self.state == "RUNNING":
                self.stop_reason = reason
                self.state = "STOPPED"
        if pool is not None:
            try:
                pool.terminate()
            except Exception:
                pass
        return {"stopped": True, "reason": reason}

    def _execute_run(self, cfg: RunConfig) -> None:
        governor = SafetyGovernor(cfg.safety, monitor=self.monitor)
        governor.reset_timer()
        workers = min(cfg.safety.max_workers, max(1, (os.cpu_count() or 2) * 2))

        if cfg.safety.below_normal_priority:
            set_worker_low_priority()

        units = self._build_corpus(cfg, round_idx=0)
        if not units:
            with self._lock:
                self.state = "STOPPED"
                self.stop_reason = "Không tìm thấy tệp mã nguồn hợp lệ nào trong nguồn dữ liệu đã chọn."
                self.duration_sec = round(time.monotonic() - self.started_at, 3)
            return

        task_cfg = {
            "enable_optimizer": cfg.enable_optimizer,
            "enable_abstract_interp": cfg.enable_abstract_interp,
            "enable_symbolic": cfg.enable_symbolic,
            "enable_mutation": cfg.enable_mutation,
            "max_symbolic_paths_per_fn": cfg.safety.max_symbolic_paths_per_fn,
            "max_mutants_per_fn": cfg.safety.max_mutants_per_fn,
            "instruction_gas_limit": cfg.safety.instruction_gas_limit,
            "per_worker_arena_mb": (cfg.safety.ram_arena_mb / max(1, workers)) if cfg.safety.ram_arena_mb > 0 else 0.0,
            "min_free_system_ram_pct": cfg.safety.min_free_system_ram_pct,
        }

        with self._lock:
            self.progress["total_units"] = len(units)

        pool: Optional[multiprocessing.pool.Pool] = None
        round_idx = 0
        final_status = "COMPLETED"
        final_reason = ""

        try:
            pool = multiprocessing.Pool(
                processes=workers,
                initializer=_worker_init,
                initargs=(cfg.safety.below_normal_priority,),
            )
            with self._lock:
                self._active_pool = pool

            while not self._stop_event.is_set():
                if round_idx > 0:
                    units = self._build_corpus(cfg, round_idx=round_idx)
                    with self._lock:
                        self.progress["total_units"] += len(units)

                pending = [
                    pool.apply_async(_analyze_unit_task, ((u, task_cfg),))
                    for u in units
                ]

                while pending:
                    if self._stop_event.is_set():
                        final_status = "STOPPED"
                        final_reason = self.stop_reason or "Đã dừng theo yêu cầu của người vận hành."
                        break

                    # Safety Circuit-Breaker Check across Parent + ALL active Child Worker PIDs
                    child_pids = tuple(
                        p.pid for p in getattr(pool, "_pool", []) if p.pid and p.is_alive()
                    )
                    healthy, reason, snap = governor.check_health(child_pids=child_pids)
                    elapsed_now = max(0.05, time.monotonic() - self.started_at)
                    with self._lock:
                        cur_scores = _compute_scores(self.totals, elapsed_now, workers)
                        self.scores = cur_scores
                        self.duration_sec = round(elapsed_now, 2)
                        self.telemetry_history.append(
                            {
                                "t": round(elapsed_now, 2),
                                "cpu_pct": snap.cpu_load_pct,
                                "ram_mb": snap.process_ram_mb,
                                "free_ram_pct": snap.free_ram_pct,
                                "smt_per_sec": cur_scores["smt_per_sec"],
                                "mutants_per_sec": cur_scores["mutants_per_sec"],
                                "ssa_per_sec": cur_scores["ssa_per_sec"],
                            }
                        )
                        if len(self.telemetry_history) > 120:
                            self.telemetry_history = self.telemetry_history[-120:]

                    if not healthy:
                        final_status = "SAFETY_TRIPPED"
                        final_reason = reason
                        self._stop_event.set()
                        try:
                            pool.terminate()
                        except Exception:
                            pass
                        break

                    still_running = []
                    made_progress = False
                    for async_res in pending:
                        if async_res.ready():
                            made_progress = True
                            try:
                                result = async_res.get(timeout=0.05)
                                self._ingest_unit_result(result)
                            except Exception as exc:
                                with self._lock:
                                    self.findings_feed.insert(
                                        0,
                                        {
                                            "kind": "WORKER_ERROR",
                                            "severity": "INFO",
                                            "function": "worker",
                                            "line": 0,
                                            "message": str(exc),
                                        },
                                    )
                        else:
                            still_running.append(async_res)
                    pending = still_running
                    if pending and not made_progress:
                        time.sleep(0.08)

                if self._stop_event.is_set():
                    break
                # Benchmark and analyze execute one full pass; stress loops until timeout/stop/safety trip
                if cfg.mode != "stress":
                    break
                round_idx += 1

        finally:
            if pool is not None:
                try:
                    if self._stop_event.is_set():
                        pool.terminate()
                    else:
                        pool.close()
                    pool.join()
                except Exception:
                    pass
            with self._lock:
                self._active_pool = None
                self.duration_sec = round(max(0.01, time.monotonic() - self.started_at), 3)
                self.scores = _compute_scores(self.totals, self.duration_sec, workers)
                if self.state == "RUNNING" or final_status != "COMPLETED":
                    self.state = final_status
                if final_reason and not self.stop_reason:
                    self.stop_reason = final_reason

                summary = {
                    "mode": cfg.mode,
                    "corpus_source": cfg.corpus_source,
                    "intensity": cfg.intensity,
                    "workers_used": workers,
                    "duration_sec": self.duration_sec,
                    "scores": dict(self.scores),
                    "totals": dict(self.totals),
                    "status": self.state,
                    "stop_reason": self.stop_reason,
                }
            if cfg.mode in ("benchmark", "stress") and self.totals["functions"] > 0:
                run_id = self.db.save_run(summary, self.machine)
                with self._lock:
                    self._last_run_id = run_id

    def _ingest_unit_result(self, result: Dict[str, Any]) -> None:
        with self._lock:
            self.progress["completed_units"] += 1
            tot_u = max(1, self.progress["total_units"])
            self.progress["pct"] = round(
                min(100.0, (self.progress["completed_units"] / tot_u) * 100.0), 1
            )
            self.totals["units"] += 1
            unit_totals = result.get("totals", {})
            for k, v in unit_totals.items():
                if k in self.totals:
                    self.totals[k] += int(v)

            pid = int(result.get("pid", 0))
            ws = self.worker_stats.setdefault(
                pid,
                {"pid": pid, "units": 0, "functions": 0, "smt_queries": 0, "mutants": 0, "busy_sec": 0.0},
            )
            ws["units"] += 1
            ws["functions"] += int(unit_totals.get("functions", 0))
            ws["smt_queries"] += int(unit_totals.get("smt_queries", 0))
            ws["mutants"] += int(unit_totals.get("mutants_evaluated", 0))
            ws["busy_sec"] = round(ws["busy_sec"] + float(result.get("elapsed_sec", 0.0)), 3)

            for fn_rep in result.get("functions", []):
                fn_id = len(self.functions_catalog)
                fn_rep["id"] = fn_id
                if len(self.functions_catalog) < 150:
                    self.functions_catalog.append(fn_rep)

                for f in fn_rep.get("ai_findings", []):
                    if len(self.findings_feed) < 120:
                        self.findings_feed.append(f)
                for cx in fn_rep.get("counterexamples", []):
                    entry = {
                        "kind": cx["kind"],
                        "severity": cx["severity"],
                        "function": cx["function"],
                        "line": cx["line"],
                        "message": f"{cx['description']} | Đầu vào nhân chứng: {cx['inputs']}",
                        "inputs": cx["inputs"],
                    }
                    self.findings_feed.insert(0, entry)
                    if len(self.findings_feed) > 120:
                        self.findings_feed = self.findings_feed[:120]

    def get_status_snapshot(self) -> Dict[str, Any]:
        with self._lock:
            pool = self._active_pool
            child_pids = (
                tuple(p.pid for p in getattr(pool, "_pool", []) if p.pid and p.is_alive())
                if pool is not None
                else ()
            )
        snap = self.monitor.snapshot(child_pids=child_pids)
        with self._lock:
            # Lightweight catalog metadata (exclude bulky SSA dumps from periodic poll)
            catalog_summary = [
                {
                    "id": f["id"],
                    "name": f["name"],
                    "language": f["language"],
                    "source_file": f["source_file"],
                    "blocks": f["blocks"],
                    "instructions": f["instructions"],
                    "cyclomatic_complexity": f["cyclomatic_complexity"],
                    "loop_count": f["loop_count"],
                    "smt_queries": f["smt_queries"],
                    "counterexamples": len(f["counterexamples"]),
                    "ai_findings": len(f["ai_findings"]),
                    "mutation_score_pct": f["mutation"]["score_pct"],
                    "mutants_total": f["mutation"]["total"],
                }
                for f in self.functions_catalog
            ]
            return {
                "state": self.state,
                "stop_reason": self.stop_reason,
                "duration_sec": self.duration_sec,
                "last_run_id": self._last_run_id,
                "machine": self.machine,
                "hardware": snap.to_dict(),
                "config": self.active_config or RunConfig().to_dict(),
                "progress": dict(self.progress),
                "totals": dict(self.totals),
                "scores": dict(self.scores),
                "workers": list(self.worker_stats.values()),
                "telemetry_history": list(self.telemetry_history[-60:]),
                "findings": list(self.findings_feed[:40]),
                "functions": catalog_summary,
                "catalog_summary": catalog_summary,
            }

    def get_function_detail(self, fn_id: int) -> Optional[Dict[str, Any]]:
        with self._lock:
            if 0 <= fn_id < len(self.functions_catalog):
                return self.functions_catalog[fn_id]
            return None
