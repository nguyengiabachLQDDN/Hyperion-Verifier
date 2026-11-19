"""Điểm khởi chạy chính của HYPERION: Web Studio, Benchmark đa nhân & Công cụ kiểm chứng CLI."""

import argparse
import json
import multiprocessing
from pathlib import Path
import sys
import threading
from typing import Any, Dict, List, Optional
import webbrowser

from hyperion.analysis.abstract_interp import run_abstract_interpretation
from hyperion.config import RunConfig, SafetyConfig
from hyperion.equivalence.prover import prove_equivalence
from hyperion.frontends.python_lifter import lift_python_source
from hyperion.frontends.ts_dsl_parser import parse_ts_dsl_source
from hyperion.hardware.telemetry import set_worker_low_priority
from hyperion.ir.cfg import compute_cfg_analysis
from hyperion.ir.optimizer import optimize_function_ssa
from hyperion.ir.ssa import IRModule
from hyperion.mutation.engine import IRInterpreter, kill_surviving_mutants
from hyperion.orchestrator.coordinator import HyperionOrchestrator
from hyperion.server.app import _append_killer_witness_tests, create_server
from hyperion.symbolic.engine import replay_function_trace, run_symbolic_execution
from hyperion.testgen.generator import generate_all_frameworks


def _configure_utf8_io() -> None:
    for stream in (sys.stdout, sys.stderr):
        try:
            if hasattr(stream, "reconfigure"):
                stream.reconfigure(encoding="utf-8", errors="replace")
        except Exception:
            pass


def _detect_lang(file_path: Path, explicit_lang: str) -> str:
    if explicit_lang:
        return explicit_lang
    ext = file_path.suffix.lower()
    if ext in (".ts", ".tsx", ".js", ".jsx"):
        return "typescript"
    return "python"


def _read_source_or_exit(raw_path: str) -> tuple[Path, str]:
    p = Path(raw_path)
    if not p.exists() or not p.is_file():
        print(f"[HYPERION LỖI] Không tìm thấy tệp mã nguồn: {raw_path}", file=sys.stderr)
        raise SystemExit(1)
    try:
        return p, p.read_text(encoding="utf-8")
    except Exception as exc:
        print(f"[HYPERION LỖI] Không thể đọc tệp mã nguồn '{raw_path}': {exc}", file=sys.stderr)
        raise SystemExit(1)


def _lift_file(path: Path, code: str, lang: str) -> IRModule:
    if lang == "typescript":
        return parse_ts_dsl_source(code, module_name=path.stem, source_file=str(path))
    return lift_python_source(code, module_name=path.stem, source_file=str(path))


def run_gen_tests_cli(args: argparse.Namespace) -> int:
    path, code = _read_source_or_exit(args.gen_tests)
    lang = _detect_lang(path, args.lang)
    mod = _lift_file(path, code, lang)

    suites: List[Dict[str, Any]] = []
    for fn in mod.functions:
        optimize_function_ssa(fn)
        sym = run_symbolic_execution(fn, max_paths=64)
        km = kill_surviving_mutants(fn, sym.synthesized_test_vectors, max_mutants=60, gas_limit=4000)
        base = generate_all_frameworks(fn, symbolic_res=sym, extra_vectors=km.witness_vectors)
        suite = _append_killer_witness_tests(base, fn, km.kill_witnesses)
        suites.append(suite)

    if args.json_out:
        print(json.dumps({"parse_errors": mod.parse_errors, "functions": suites}, indent=2, ensure_ascii=False))
        return 0

    print(f"[HYPERION] Đã sinh bộ unit test ({args.framework}) cho {len(suites)} hàm trong '{path.name}':")
    for s in suites:
        print(f"\n--- Hàm: {s['function']} ({len(s['cases'])} trường hợp kiểm thử) ---")
        print(s.get(args.framework, s["pytest"]))
    return 0


def run_prove_equiv_cli(args: argparse.Namespace) -> int:
    p_old, code_old = _read_source_or_exit(args.prove_equiv[0])
    p_new, code_new = _read_source_or_exit(args.prove_equiv[1])
    lang = _detect_lang(p_old, args.lang)
    res = prove_equivalence(code_old, code_new, language=lang)

    if args.json_out:
        print(json.dumps(res, indent=2, ensure_ascii=False))
        return 0

    print("=== KẾT QUẢ KIỂM CHỨNG TƯƠNG ĐƯƠNG NGỮ NGHĨA (HYPERION) ===")
    print(f"Hàm cũ / Hàm mới : {res['old_function']} <-> {res['new_function']}")
    print(f"Trạng thái       : {res['status']} (Tương đương: {'CÓ' if res['equivalent'] else 'KHÔNG'})")
    print(f"Tóm tắt          : {res['summary']}")
    print(f"Đường chạy / SMT : {res['paths_checked']} cặp đường chạy | {res['smt_queries']} truy vấn DPLL(T)")
    if res.get("counterexample"):
        print(f"Phản ví dụ       : {json.dumps(res['counterexample'], ensure_ascii=False)}")
    return 0


def run_kill_mutants_cli(args: argparse.Namespace) -> int:
    path, code = _read_source_or_exit(args.kill_mutants)
    lang = _detect_lang(path, args.lang)
    mod = _lift_file(path, code, lang)
    if not mod.functions:
        print(f"[HYPERION LỖI] Không tìm thấy hàm hợp lệ trong '{path}'.", file=sys.stderr)
        return 1

    fn = mod.functions[0]
    optimize_function_ssa(fn)
    sym = run_symbolic_execution(fn, max_paths=64)
    mut = kill_surviving_mutants(fn, sym.synthesized_test_vectors, max_mutants=60, gas_limit=4000)
    base_tests = generate_all_frameworks(fn, symbolic_res=sym, extra_vectors=sym.synthesized_test_vectors)
    appended = _append_killer_witness_tests(base_tests, fn, mut.kill_witnesses)

    payload = {
        "function": fn.name,
        "language": fn.source_lang,
        "initial_survived": mut.initial_survived,
        "newly_killed": mut.newly_killed,
        "remaining_survived": mut.survived,
        "new_score_pct": mut.mutation_score_pct,
        "kill_witnesses": mut.kill_witnesses,
        "mutation": {
            "total": mut.total_mutants,
            "killed": mut.killed,
            "survived": mut.survived,
            "initial_survived": mut.initial_survived,
            "newly_killed": mut.newly_killed,
            "score_pct": mut.mutation_score_pct,
            "vm_steps": mut.total_vm_steps,
            "records": [r.to_dict() for r in mut.records],
        },
        "appended_tests": appended,
    }
    if args.json_out:
        print(json.dumps(payload, indent=2, ensure_ascii=False))
        return 0

    print("=== KẾT QUẢ DIỆT MUTANT SỐNG SÓT BẰNG SMT DPLL(T) ===")
    print(f"Hàm phân tích     : {fn.name}")
    print(f"Tổng đột biến     : {mut.total_mutants} | Sống sót ban đầu: {mut.initial_survived}")
    print(f"Đã tiêu diệt thêm : {mut.newly_killed} | Còn sống: {mut.survived} | Điểm mới: {mut.mutation_score_pct}%")
    for w in mut.kill_witnesses:
        print(f"  - Đột biến #{w['mutant_id']} ({w['operator']} dòng {w['line']}): đầu vào {w['witness_inputs']}")
    return 0


def run_dead_branches_cli(args: argparse.Namespace) -> int:
    path, code = _read_source_or_exit(args.dead_branches)
    lang = _detect_lang(path, args.lang)
    mod = _lift_file(path, code, lang)

    fn_results: List[Dict[str, Any]] = []
    for fn in mod.functions:
        optimize_function_ssa(fn)
        sym = run_symbolic_execution(fn, max_paths=80)
        fn_results.append(
            {
                "function": fn.name,
                "language": fn.source_lang,
                "dead_branches": sym.dead_branches,
            }
        )

    if args.json_out:
        print(json.dumps({"parse_errors": mod.parse_errors, "functions": fn_results}, indent=2, ensure_ascii=False))
        return 0

    print(f"=== KẾT QUẢ PHÁT HIỆN NHÁNH CODE CHẾT (UNSAT) CHO '{path.name}' ===")
    for item in fn_results:
        dbs = item["dead_branches"]
        print(f"Hàm {item['function']}: phát hiện {len(dbs)} nhánh chết (UNSAT).")
        for db in dbs:
            print(f"  - Khối B{db['block_id']} -> B{db['target_block_id']} (dòng {db['line']}): {db['reason']}")
    return 0


def run_trace_replay_cli(args: argparse.Namespace) -> int:
    path, code = _read_source_or_exit(args.trace_replay)
    try:
        inputs = json.loads(args.inputs)
    except Exception:
        print("[HYPERION LỖI] Chuỗi JSON đầu vào (--inputs) không hợp lệ.", file=sys.stderr)
        return 1
    if not isinstance(inputs, dict):
        print("[HYPERION LỖI] Tham số --inputs phải là một đối tượng JSON (ví dụ: '{\"x\": 0}').", file=sys.stderr)
        return 1

    lang = _detect_lang(path, args.lang)
    mod = _lift_file(path, code, lang)
    if not mod.functions:
        print(f"[HYPERION LỖI] Không tìm thấy hàm hợp lệ trong '{path}'.", file=sys.stderr)
        return 1

    fn = mod.functions[0]
    optimize_function_ssa(fn)
    cfg = compute_cfg_analysis(fn)
    ai = run_abstract_interpretation(fn, cfg)
    vm_out = IRInterpreter(gas_limit=2000).execute(fn, inputs)
    steps = replay_function_trace(fn, inputs, intervals=ai.intervals, gas_limit=2000)

    payload = {
        "function": fn.name,
        "language": fn.source_lang,
        "inputs": inputs,
        "outcome": {
            "status": vm_out.status,
            "return_value": vm_out.return_value,
            "steps": vm_out.steps,
            "error": vm_out.error,
        },
        "trace_steps": steps,
    }
    if args.json_out:
        print(json.dumps(payload, indent=2, ensure_ascii=False))
        return 0

    print(f"=== TUA TỪNG BƯỚC ĐƯỜNG CHẠY THỰC THI CHO HÀM '{fn.name}' ===")
    print(f"Đầu vào  : {json.dumps(inputs, ensure_ascii=False)}")
    print(f"Kết quả  : {vm_out.status} | Giá trị trả về: {vm_out.return_value} | Lỗi: {vm_out.error or 'không'}")
    for st in steps:
        print(f"  Bước {st['step']} [B{st['block_id']} {st['block_label']} | D{st['line']}]: {st['instruction']} | Biến={st['vars']} ({st['event']})")
    return 0


def run_cli_mode(args: argparse.Namespace) -> int:
    safety = SafetyConfig(
        max_workers=args.workers,
        max_process_ram_mb=args.max_ram_mb,
        min_free_system_ram_pct=args.min_free_ram_pct,
        max_duration_sec=args.timeout,
        ram_arena_mb=args.ram_arena_mb,
    )
    mode = "stress" if args.stress_cli else "benchmark"
    cfg = RunConfig(
        mode=mode,
        corpus_source=args.corpus,
        custom_path=args.path or "",
        intensity="benchmark" if mode == "benchmark" else args.intensity,
        scale_factor=args.scale,
        safety=safety,
    )
    cfg.clamp_and_validate()

    orch = HyperionOrchestrator()
    print(f"[HYPERION] Phần cứng máy chủ: {orch.machine['cpu_model']} ({orch.machine['logical_cores']} luồng CPU, {orch.machine['total_ram_gb']} GB RAM)")
    print(f"[HYPERION] Khởi chạy chế độ {mode.upper()} | nguồn dữ liệu={cfg.corpus_source} | tỷ lệ={cfg.scale_factor} | số luồng xử lý={cfg.safety.max_workers}")
    print(f"[HYPERION] Bảo vệ phần cứng: trần RAM={cfg.safety.max_process_ram_mb} MB | ngưỡng RAM trống={cfg.safety.min_free_system_ram_pct}% | ưu tiên thấp={cfg.safety.below_normal_priority}")

    orch.start_run(cfg, blocking=True)
    snap = orch.get_status_snapshot()
    print("\n=== TỔNG KẾT PHIÊN CHẠY HYPERION ===")
    print(f"Trạng thái        : {snap['state']}" + (f" ({snap['stop_reason']})" if snap["stop_reason"] else ""))
    print(f"Thời gian chạy    : {snap['duration_sec']} giây")
    print(f"Số hàm / Dòng code: {snap['totals']['functions']} hàm / {snap['totals']['loc']} LOC")
    print(f"Lệnh SSA IR       : {snap['totals']['ssa_instructions']} (gấp hằng={snap['totals']['opt_folded']}, xóa mã chết={snap['totals']['opt_dce']})")
    print(f"DPLL(T) & Ký hiệu : {snap['totals']['paths_explored']} đường chạy | {snap['totals']['smt_queries']} truy vấn SMT | {snap['totals']['counterexamples']} phản ví dụ")
    print(f"Đột biến trên RAM : {snap['totals']['mutants_evaluated']} bản đột biến (đã diệt={snap['totals']['mutants_killed']}, {snap['totals']['vm_steps']} bước VM)")
    scores = snap["scores"]
    print(
        f"Điểm hiệu năng    : TỔNG={scores.get('composite_score', 0)} | "
        f"SSA/CFG={scores.get('ssa_cfg_score', 0)} | "
        f"SMT={scores.get('smt_symbolic_score', 0)} | "
        f"ĐỘT BIẾN={scores.get('mutation_score', 0)} | "
        f"THÔNG LƯỢNG={scores.get('parallel_throughput', 0)}"
    )
    if args.json_out:
        print(json.dumps({"scores": scores, "totals": snap["totals"], "status": snap["state"]}, indent=2, ensure_ascii=False))
    return 0


def run_server_mode(args: argparse.Namespace) -> int:
    set_worker_low_priority()
    srv, port = create_server(host=args.host, preferred_port=args.port)
    url = f"http://{args.host}:{port}/"
    print(f"[HYPERION] Giao diện Web Studio tiếng Việt đang chạy tại {url}")
    print("[HYPERION] Chế độ 100% Portable trên Win10_SSD, không ghi tệp tạm ra đĩa. Nhấn Ctrl+C để thoát.")

    if not args.no_browser:
        threading.Timer(0.6, lambda: webbrowser.open(url)).start()

    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        print("\n[HYPERION] Đang tắt máy chủ an toàn...")
        srv.orchestrator.emergency_stop("Tắt máy chủ theo lệnh người vận hành")
        srv.shutdown()
    return 0


def build_arg_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        description="HYPERION — Hệ thống phân tích tĩnh, thực thi ký hiệu DPLL(T), sinh unit test và kiểm thử đột biến chạy hoàn toàn trên RAM"
    )
    p.add_argument("--host", default="127.0.0.1", help="Địa chỉ lắng nghe HTTP (mặc định: 127.0.0.1)")
    p.add_argument("--port", type=int, default=8765, help="Cổng HTTP ưu tiên (mặc định: 8765)")
    p.add_argument("--no-browser", action="store_true", help="Không tự động mở trình duyệt khi khởi động máy chủ")
    p.add_argument("--benchmark-cli", action="store_true", help="Chạy chấm điểm chuẩn đa nhân qua CLI và lưu kết quả")
    p.add_argument("--stress-cli", action="store_true", help="Chạy kiểm tra tải liên tục qua CLI")
    p.add_argument("--corpus", default="procedural", choices=["procedural", "self_host", "custom_path"], help="Nguồn mã mục tiêu")
    p.add_argument("--path", default="", help="Đường dẫn thư mục cho nguồn custom_path")
    p.add_argument("--intensity", default="heavy", choices=["balanced", "heavy", "extreme", "benchmark"], help="Mức cường độ tải")
    p.add_argument("--scale", type=int, default=4, help="Hệ số quy mô bộ sinh mã nguồn (1-50)")
    p.add_argument("--workers", type=int, default=SafetyConfig().max_workers, help="Số tiến trình xử lý tối đa")
    p.add_argument("--max-ram-mb", type=int, default=1536, help="Trần RAM tối đa cho tiến trình (MB)")
    p.add_argument("--ram-arena-mb", type=int, default=0, help="Dung lượng vùng nhớ RAM giữ lại để ép tải (MB)")
    p.add_argument("--min-free-ram-pct", type=float, default=SafetyConfig().min_free_system_ram_pct, help="Ngưỡng RAM trống hệ thống tối thiểu (%%)")
    p.add_argument("--timeout", type=int, default=120, help="Thời gian chạy tối đa mỗi phiên (giây)")
    p.add_argument("--json-out", action="store_true", help="Xuất kết quả dạng JSON chuẩn trên CLI")

    # Nhóm lệnh phân tích & kiểm chứng thực chiến
    p.add_argument("--gen-tests", default="", metavar="FILE", help="Sinh bộ unit test pytest/vitest/jest cho tệp mã nguồn")
    p.add_argument("--framework", default="pytest", choices=["pytest", "vitest", "jest"], help="Framework xuất test")
    p.add_argument("--prove-equiv", nargs=2, metavar=("OLD_FILE", "NEW_FILE"), help="Kiểm chứng tương đương ngữ nghĩa giữa Hàm Cũ và Hàm Mới")
    p.add_argument("--kill-mutants", default="", metavar="FILE", help="Dùng SMT DPLL(T) tiêu diệt các đột biến SURVIVED")
    p.add_argument("--dead-branches", default="", metavar="FILE", help="Phát hiện các nhánh code chết (UNSAT) trong tệp mã nguồn")
    p.add_argument("--trace-replay", default="", metavar="FILE", help="Tua từng bước đường chạy thực thi trên SSA IR")
    p.add_argument("--inputs", default="{}", help="Chuỗi JSON tham số đầu vào cho --trace-replay")
    p.add_argument("--lang", default="", choices=["", "python", "typescript"], help="Ngôn ngữ mã nguồn (tự nhận diện nếu bỏ trống)")
    return p


if __name__ == "__main__":
    multiprocessing.freeze_support()
    _configure_utf8_io()
    parser = build_arg_parser()
    parsed_args = parser.parse_args()
    if parsed_args.gen_tests:
        raise SystemExit(run_gen_tests_cli(parsed_args))
    if parsed_args.prove_equiv:
        raise SystemExit(run_prove_equiv_cli(parsed_args))
    if parsed_args.kill_mutants:
        raise SystemExit(run_kill_mutants_cli(parsed_args))
    if parsed_args.dead_branches:
        raise SystemExit(run_dead_branches_cli(parsed_args))
    if parsed_args.trace_replay:
        raise SystemExit(run_trace_replay_cli(parsed_args))
    if parsed_args.benchmark_cli or parsed_args.stress_cli:
        raise SystemExit(run_cli_mode(parsed_args))
    raise SystemExit(run_server_mode(parsed_args))
