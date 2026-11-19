"""Bộ kiểm thử tự động toàn diện cho tất cả phân hệ và cơ chế bảo vệ phần cứng của HYPERION."""

import ast
import ctypes
from ctypes import wintypes
import json
import os
import sys
import tempfile
import threading
import time
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from hyperion.analysis.abstract_interp import run_abstract_interpretation
from hyperion.config import RunConfig, SafetyConfig
from hyperion.corpus.generator import generate_procedural_corpus, load_self_host_corpus
from hyperion.equivalence.prover import prove_equivalence
from hyperion.frontends.python_lifter import lift_python_source
from hyperion.frontends.ts_dsl_parser import parse_ts_dsl_source
from hyperion.hardware.telemetry import (
    HardwareMonitor,
    SafetyGovernor,
    get_win32_bindings,
    set_worker_low_priority,
)
from hyperion.ir.cfg import compute_cfg_analysis
from hyperion.ir.optimizer import optimize_function_ssa
from hyperion.mutation.engine import kill_surviving_mutants, run_mutation_testing
from hyperion.orchestrator.coordinator import HyperionOrchestrator
from hyperion.server.app import create_server
from hyperion.solver.dpll_smt import DPLLTSolver, SymBinOp, SymConst, SymVar
from hyperion.storage.db import LeaderboardDB
from hyperion.symbolic.engine import replay_function_trace, run_symbolic_execution
from hyperion.testgen.generator import generate_unit_tests


def test_hardware_and_safety_governor() -> None:
    print("[1/7] Kiểm tra Telemetry phần cứng, chữ ký HANDLE 64-bit & SafetyGovernor...")
    assert set_worker_low_priority() is True
    bindings = get_win32_bindings()
    if os.name == "nt":
        k32 = bindings["kernel32"]
        psapi = bindings["psapi"]
        assert k32.GetCurrentProcess.restype in (wintypes.HANDLE, ctypes.c_void_p)
        assert list(k32.SetPriorityClass.argtypes) == [wintypes.HANDLE, wintypes.DWORD]
        assert psapi.GetProcessMemoryInfo.argtypes[0] in (wintypes.HANDLE, ctypes.c_void_p)

    mon = HardwareMonitor()
    snap = mon.snapshot()
    assert snap.total_ram_mb > 512
    assert 0.0 <= snap.free_ram_pct <= 100.0

    gov_ok = SafetyGovernor(
        SafetyConfig(max_process_ram_mb=8192, min_free_system_ram_pct=5.0, max_duration_sec=60),
        mon,
    )
    ok, reason, _ = gov_ok.check_health()
    assert ok and reason == "OK", f"Expected safe check, got {(ok, reason)}"

    gov_trip = SafetyGovernor(SafetyConfig(min_free_system_ram_pct=99.9), mon)
    ok2, reason2, _ = gov_trip.check_health()
    assert not ok2 and ("ram" in reason2.lower() or "ngưỡng" in reason2.lower()), (
        f"Expected Vietnamese RAM floor trip, got {ok2}, {reason2}"
    )
    print("   PASS: Đã xác minh telemetry 64-bit HANDLE và cầu chì RAM tiếng Việt.")


def test_polyglot_frontends_cfg_and_optimizer() -> None:
    print("[2/7] Kiểm tra Frontend đa ngôn ngữ (Python + TS/DSL), Unified SSA IR, CFG & Optimizer...")
    py_src = """
def sample_py(x, user_input):
    arr = [1, 2, 3]
    c = 2 + 3
    if x > 5:
        y = x + c
    else:
        y = x - 1
    if x == 10:
        z = arr[x]
    tok = read_packet(user_input)
    if x < 0:
        sql_query(tok)
    return y
"""
    py_mod = lift_python_source(py_src, "test_py", "<mem>.py")
    assert len(py_mod.functions) == 1
    fn_py = py_mod.functions[0]
    opt_py = optimize_function_ssa(fn_py)
    assert opt_py.constants_folded >= 1
    cfg_py = compute_cfg_analysis(fn_py)
    assert len(cfg_py.rpo_order) >= 4
    assert cfg_py.cyclomatic_complexity >= 3

    ts_src = """
export function sampleTs(a: number, b: number, untrustedPayload: number): number {
    let buf = [10, 20, 30];
    let acc = 4 + 6;
    for (let i = 0; i < 3; i++) {
        acc = acc + i;
    }
    if (a == 7 && b >= 3) {
        let bad = buf[b];
        acc = acc + bad;
    }
    if (a < 0) {
        sqlExec(untrustedPayload, acc);
    }
    assert(acc > -50, "acc_ok");
    return acc;
}
"""
    ts_mod = parse_ts_dsl_source(ts_src, "test_ts", "<mem>.ts")
    assert len(ts_mod.functions) == 1
    fn_ts = ts_mod.functions[0]
    optimize_function_ssa(fn_ts)
    cfg_ts = compute_cfg_analysis(fn_ts)
    assert len(cfg_ts.natural_loops) >= 1
    assert cfg_ts.to_graph_json(fn_ts)["nodes"]
    print("   PASS: Python và TS/DSL đã nâng về Unified SSA IR + Dominators + Vòng lặp.")


def test_smt_symbolic_dead_branches_and_trace() -> None:
    print("[3/7] Kiểm tra DPLL(T) SMT, Nhánh Code Chết UNSAT & Trace Replay...")
    solver = DPLLTSolver(default_lo=-100, default_hi=100)
    x, y = SymVar("x"), SymVar("y")
    sat_res = solver.solve([
        SymBinOp(">", x, SymConst(10)),
        SymBinOp("<", x, y),
        SymBinOp("<=", y, SymConst(15)),
    ])
    assert sat_res.status == "SAT"
    assert sat_res.model["x"] > 10 and sat_res.model["x"] < sat_res.model["y"] <= 15

    unsat_res = solver.solve([
        SymBinOp(">", x, SymConst(20)),
        SymBinOp("<", x, SymConst(10)),
    ])
    assert unsat_res.status == "UNSAT"

    src = """
def vuln_div_and_oob(k, user_input):
    buf = [1, 2, 3, 4]
    if k > 25:
        if k < 5:
            return -999
    if k == 9:
        v = buf[k]
    denom = k - 5
    res = 100 // denom
    if k < 0:
        eval(user_input)
    assert k != 4, "k_cannot_be_4"
    return res
"""
    mod = lift_python_source(src)
    fn = mod.functions[0]
    cfg = compute_cfg_analysis(fn)
    ai = run_abstract_interpretation(fn, cfg)
    assert any(f.kind in ("DIV_BY_ZERO_RISK", "BUFFER_INDEX_OOB", "TAINT_SINK_FLOW") for f in ai.findings)

    sym = run_symbolic_execution(fn, max_paths=80)
    kinds = {c.kind for c in sym.counterexamples}
    assert {"DIV_BY_ZERO", "BUFFER_OOB", "ASSERTION_VIOLATION", "TAINT_REACHABLE"}.issubset(kinds)
    assert len(sym.dead_branches) >= 1, "Expected UNSAT dead branch"
    assert len(sym.dead_block_ids) >= 1

    steps = replay_function_trace(fn, {"k": 5, "user_input": 0}, intervals=ai.intervals)
    assert len(steps) >= 2
    assert [s["step"] for s in steps] == list(range(len(steps)))
    assert steps[0]["block_id"] == 0
    print(f"   PASS: Tổng hợp {len(sym.counterexamples)} phản ví dụ, {len(sym.dead_branches)} nhánh chết UNSAT, {len(steps)} bước tua vết.")


def test_testgen_equivalence_and_mutant_killer() -> None:
    print("[4/7] Kiểm tra Sinh Unit Test (pytest/vitest/jest), Kiểm chứng Tương đương & Diệt Mutant...")
    src_gate = "def gate(x):\n    if x > 10:\n        return 100\n    return 0\n"
    fn_gate = lift_python_source(src_gate).functions[0]
    optimize_function_ssa(fn_gate)

    km = kill_surviving_mutants(fn_gate, [{"x": 0}, {"x": 11}], max_mutants=40)
    assert km.initial_survived >= 1
    assert km.newly_killed >= 1
    assert any(w["witness_inputs"].get("x") == 10 for w in km.kill_witnesses)

    tests_bundle = generate_unit_tests(fn_gate, extra_vectors=km.witness_vectors)
    ast.parse(tests_bundle["pytest"])
    assert "describe(" in tests_bundle["vitest"] and "vitest" in tests_bundle["vitest"]
    assert "describe(" in tests_bundle["jest"]

    eq_ok = prove_equivalence(
        "def old_fn(x):\n    if x > 0:\n        return x * 2\n    return 0\n",
        "def new_fn(x):\n    if x <= 0:\n        return 0\n    return x + x\n",
        language="python",
    )
    assert eq_ok["equivalent"] is True and eq_ok["status"] == "EQUIVALENT"

    eq_bad = prove_equivalence(
        "def old_fn(x):\n    if x >= 10:\n        return 1\n    return 0\n",
        "def new_fn(x):\n    if x > 10:\n        return 1\n    return 0\n",
        language="python",
    )
    assert eq_bad["equivalent"] is False and eq_bad["status"] == "NON_EQUIVALENT"
    assert eq_bad["counterexample"]["inputs"]["x"] == 10
    print("   PASS: Sinh Unit Test, Kiểm chứng Tương đương & Diệt Mutant bằng SMT hoạt động chính xác.")


def test_in_memory_mutation_engine() -> None:
    print("[5/7] Kiểm tra Động cơ Đột biến trên RAM & IRInterpreter...")
    src = """
def arith_kernel(a, b):
    if a > b:
        return (a - b) * 3 + 1
    return (b - a) + 2
"""
    fn = lift_python_source(src).functions[0]
    sym = run_symbolic_execution(fn, max_paths=40)
    mut = run_mutation_testing(fn, sym.synthesized_test_vectors, max_mutants=30, gas_limit=2000)
    assert mut.total_mutants >= 5
    assert mut.killed >= 3
    assert mut.total_vm_steps > 0
    print(f"   PASS: Đã đánh giá {mut.total_mutants} đột biến trên RAM (diệt {mut.killed}, điểm {mut.mutation_score_pct}%).")


def test_corpus_and_multiprocessing_orchestrator() -> None:
    print("[6/7] Kiểm tra 3 Nguồn Corpus, Điều phối Đa nhân & Bảng xếp hạng SQLite...")
    assert len(load_self_host_corpus(max_files=10)) >= 3
    assert len(generate_procedural_corpus(scale_factor=2, seed=42)) >= 6

    with tempfile.TemporaryDirectory() as tmp:
        db = LeaderboardDB(Path(tmp) / "test_bench.sqlite3")
        orch = HyperionOrchestrator(db=db)
        cfg = RunConfig(
            mode="benchmark",
            corpus_source="procedural",
            intensity="balanced",
            scale_factor=2,
            safety=SafetyConfig(max_workers=2, max_duration_sec=45, min_free_system_ram_pct=5.0),
        )
        ok, state = orch.start_run(cfg, blocking=True)
        assert ok and state == "COMPLETED", f"Unexpected state: {state} ({orch.stop_reason})"
        snap = orch.get_status_snapshot()
        assert snap["totals"]["functions"] >= 10
        assert snap["totals"]["smt_queries"] > 0
        assert snap["totals"]["mutants_evaluated"] > 0
        assert snap["scores"]["composite_score"] > 0
        assert len(db.list_runs()) == 1
    print("   PASS: Đa nhân multiprocessing và SQLite portable hoạt động ổn định.")


def test_http_server_and_all_new_apis() -> None:
    print("[7/7] Kiểm tra Máy chủ HTTP REST API & Toàn bộ Endpoint Mới...")
    srv, port = create_server(host="127.0.0.1", preferred_port=18765)
    t = threading.Thread(target=srv.serve_forever, daemon=True)
    t.start()
    try:
        base = f"http://127.0.0.1:{port}"
        with urllib.request.urlopen(f"{base}/api/telemetry", timeout=5) as resp:
            assert resp.status == 200
            tel = json.loads(resp.read().decode("utf-8"))
            assert "hardware" in tel and "machine" in tel

        def post_json(path: str, payload: dict) -> dict:
            req = urllib.request.Request(
                f"{base}{path}",
                data=json.dumps(payload).encode("utf-8"),
                headers={"Content-Type": "application/json"},
                method="POST",
            )
            with urllib.request.urlopen(req, timeout=10) as r:
                assert r.status == 200
                return json.loads(r.read().decode("utf-8"))

        an = post_json("/api/analyze-snippet", {
            "language": "typescript",
            "code": "export function check(x: number): number { let a = [1,2]; if (x > 20 && x < 5) { return -1; } if (x == 5) { return a[x]; } return x + 1; }",
            "kill_mutants": True,
        })
        fn_an = an["functions"][0]
        assert len(fn_an["dead_branches"]) >= 1
        assert len(fn_an["counterexamples"]) >= 1
        assert "pytest" in fn_an["generated_tests"]

        gt = post_json("/api/generate-tests", {
            "language": "python",
            "framework": "pytest",
            "code": "def f(x):\n    return x * 2 if x > 0 else 0\n",
        })
        assert "pytest" in gt["functions"][0]

        eq = post_json("/api/equivalence", {
            "language": "python",
            "old_code": "def f(x): return x + x\n",
            "new_code": "def g(x): return x * 2\n",
        })
        assert eq["equivalent"] is True

        km = post_json("/api/kill-mutants", {
            "language": "python",
            "code": "def gate(x):\n    if x > 10:\n        return 100\n    return 0\n",
            "existing_vectors": [{"x": 0}, {"x": 11}],
        })
        assert km["newly_killed"] >= 1

        tr = post_json("/api/trace-replay", {
            "language": "python",
            "code": "def div0(x):\n    return 10 // x\n",
            "inputs": {"x": 0},
        })
        assert tr["outcome"]["status"] == "TRAP"
        assert len(tr["trace_steps"]) >= 1
    finally:
        srv.shutdown()
        srv.server_close()
    print("   PASS: Tất cả 5 endpoint phân tích thực chiến phản hồi chính xác.")


def main() -> int:
    t0 = time.perf_counter()
    test_hardware_and_safety_governor()
    test_polyglot_frontends_cfg_and_optimizer()
    test_smt_symbolic_dead_branches_and_trace()
    test_testgen_equivalence_and_mutant_killer()
    test_in_memory_mutation_engine()
    test_corpus_and_multiprocessing_orchestrator()
    test_http_server_and_all_new_apis()
    dt = time.perf_counter() - t0
    print(f"\nHOÀN TẤT: TOÀN BỘ 7 BỘ KIỂM THỬ HYPERION ĐẠT CHUẨN trong {dt:.2f} giây.")
    return 0


if __name__ == "__main__":
    import multiprocessing
    multiprocessing.freeze_support()
    raise SystemExit(main())
