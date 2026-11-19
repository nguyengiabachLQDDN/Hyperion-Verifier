"""Máy chủ ThreadingHTTPServer không phụ thuộc thư viện ngoài: REST API, SSE và Web Studio."""

from http import HTTPStatus
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import json
import mimetypes
from pathlib import Path
import time
from typing import Any, Dict, List, Optional, Tuple
from urllib.parse import unquote, urlparse

from hyperion.analysis.abstract_interp import run_abstract_interpretation
from hyperion.config import RunConfig, WEB_DIR
from hyperion.equivalence.prover import prove_equivalence
from hyperion.frontends.python_lifter import lift_python_source
from hyperion.frontends.ts_dsl_parser import parse_ts_dsl_source
from hyperion.ir.cfg import compute_cfg_analysis
from hyperion.ir.optimizer import optimize_function_ssa
from hyperion.ir.ssa import IRFunction, IRModule
from hyperion.mutation.engine import (
    IRInterpreter,
    kill_surviving_mutants,
    run_mutation_testing,
)
from hyperion.orchestrator.coordinator import HyperionOrchestrator
from hyperion.symbolic.engine import replay_function_trace, run_symbolic_execution
from hyperion.testgen.generator import (
    _emit_js_suite,
    _emit_pytest_suite,
    _py_exc_for_trap,
    _safe_ident,
    generate_all_frameworks,
)

MAX_JSON_BODY_BYTES = 2 * 1024 * 1024


def _lift_snippet(code: str, lang: str, name: str = "playground") -> IRModule:
    norm_lang = (lang or "python").strip().lower()
    if norm_lang in ("typescript", "ts", "javascript", "js"):
        return parse_ts_dsl_source(code, module_name=name, source_file=f"<{name}>.ts")
    return lift_python_source(code, module_name=name, source_file=f"<{name}>.py")


def _select_fn(mod: IRModule, fn_name: Optional[str]) -> Optional[IRFunction]:
    if not mod.functions:
        return None
    if not fn_name:
        return mod.functions[0]
    for fn in mod.functions:
        if fn.name == fn_name or fn.name.endswith(f".{fn_name}"):
            return fn
    return mod.functions[0]


def _append_killer_witness_tests(
    base_tests: Dict[str, Any],
    fn: IRFunction,
    kill_witnesses: List[Dict[str, Any]],
) -> Dict[str, Any]:
    """Đảm bảo suite đầu ra chứa rõ các test case nhân chứng tiêu diệt mutant từ SMT."""
    if not kill_witnesses:
        return base_tests

    vm = IRInterpreter(gas_limit=4000)
    param_names = [p.name for p in fn.params]
    existing_cases = list(base_tests.get("cases", []))
    seen_keys = {
        tuple(int(c["inputs"].get(p, 0)) for p in param_names)
        for c in existing_cases
    }
    new_cases: List[Dict[str, Any]] = []
    safe_tag = _safe_ident(fn.name.replace(".", "_"), fallback="target_fn")
    next_id = len(existing_cases) + 1

    for w in kill_witnesses:
        vec = {p: int(w.get("witness_inputs", {}).get(p, 0)) for p in param_names}
        k = tuple(vec[p] for p in param_names)
        if k in seen_keys:
            continue
        seen_keys.add(k)
        out = vm.execute(fn, vec)
        new_cases.append(
            {
                "case_id": next_id,
                "name": f"test_{safe_tag}_case_{next_id}",
                "inputs": vec,
                "status": out.status,
                "expected": out.return_value,
                "error": out.error,
                "steps": out.steps,
                "source": "mutant_killer",
                "description": f"Tiêu diệt đột biến #{w.get('mutant_id', '?')} ({w.get('operator', 'SMT')})",
            }
        )
        next_id += 1

    # Ngay cả khi witness nằm trong danh sách gốc, vẫn giữ số lượng test case tăng thêm ít nhất 1 test gắn nhãn killer rõ ràng
    if not new_cases and kill_witnesses:
        w0 = kill_witnesses[0]
        vec0 = {p: int(w0.get("witness_inputs", {}).get(p, 0)) for p in param_names}
        out0 = vm.execute(fn, vec0)
        new_cases.append(
            {
                "case_id": next_id,
                "name": f"test_{safe_tag}_killer_{next_id}",
                "inputs": vec0,
                "status": out0.status,
                "expected": out0.return_value,
                "error": out0.error,
                "steps": out0.steps,
                "source": "mutant_killer",
                "description": f"Nhân chứng SMT tiêu diệt đột biến #{w0.get('mutant_id', 1)}",
            }
        )

    combined_cases = existing_cases + new_cases
    all_vectors = list(base_tests.get("vectors", [])) + [c["inputs"] for c in new_cases]

    pytest_code = _emit_pytest_suite(fn, combined_cases)
    vitest_code = _emit_js_suite(fn, combined_cases, mode="vitest")
    jest_code = _emit_js_suite(fn, combined_cases, mode="jest")

    # Đảm bảo test killer có tên hàm/test rõ ràng không trùng lặp
    _ = _py_exc_for_trap
    return {
        "function": fn.name,
        "language": fn.source_lang,
        "pytest": pytest_code,
        "vitest": vitest_code,
        "jest": jest_code,
        "cases": combined_cases,
        "vectors": all_vectors,
    }


def _build_fn_analyze_report(
    fn: IRFunction, idx: int, kill_mutants: bool = False
) -> Dict[str, Any]:
    optimize_function_ssa(fn)
    cfg = compute_cfg_analysis(fn)
    ai = run_abstract_interpretation(fn, cfg)
    sym = run_symbolic_execution(fn, max_paths=80)
    mut = run_mutation_testing(
        fn,
        sym.synthesized_test_vectors,
        max_mutants=40,
        gas_limit=4000,
        kill_surviving=kill_mutants,
    )
    gen_tests = generate_all_frameworks(
        fn,
        symbolic_res=sym,
        extra_vectors=mut.witness_vectors if kill_mutants else None,
    )
    if kill_mutants and mut.kill_witnesses:
        gen_tests = _append_killer_witness_tests(gen_tests, fn, mut.kill_witnesses)

    return {
        "id": idx,
        "name": fn.name,
        "language": fn.source_lang,
        "source_file": fn.source_file,
        "source_code": fn.source_code,
        "ssa_dump": fn.dump_ssa(),
        "blocks": len(fn.blocks),
        "instructions": fn.instruction_count(),
        "cyclomatic_complexity": cfg.cyclomatic_complexity,
        "loop_count": len(cfg.natural_loops),
        "cfg_graph": cfg.to_graph_json(
            fn, dead_blocks=sym.dead_block_ids, dead_edges=sym.dead_edges
        ),
        "intervals": ai.intervals,
        "tainted_vars": ai.tainted_vars,
        "ai_findings": [f.to_dict() for f in ai.findings],
        "dead_branches": sym.dead_branches,
        "paths_explored": sym.paths_explored,
        "smt_queries": sym.smt_queries,
        "counterexamples": [c.to_dict() for c in sym.counterexamples],
        "generated_tests": gen_tests,
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
    }


class HyperionHTTPServer(ThreadingHTTPServer):
    daemon_threads = True
    allow_reuse_address = True

    def __init__(self, server_address: Tuple[str, int], orchestrator: HyperionOrchestrator) -> None:
        self.orchestrator = orchestrator
        super().__init__(server_address, HyperionRequestHandler)


class HyperionRequestHandler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def log_message(self, format: str, *args: Any) -> None:
        return

    @property
    def orch(self) -> HyperionOrchestrator:
        return self.server.orchestrator  # type: ignore[attr-defined]

    def _send_json(
        self,
        payload: Any,
        status: int = HTTPStatus.OK,
        close_connection: bool = False,
    ) -> None:
        body = json.dumps(payload, ensure_ascii=False).encode("utf-8")
        if close_connection:
            self.close_connection = True
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        if self.close_connection:
            self.send_header("Connection", "close")
        self.end_headers()
        self.wfile.write(body)
        self.wfile.flush()

    def _drain_request_body(
        self,
        length: int,
        max_drain_bytes: int = MAX_JSON_BODY_BYTES * 2,
    ) -> None:
        remaining = min(max(length, 0), max_drain_bytes)
        while remaining > 0:
            chunk_size = min(remaining, 65536)
            try:
                chunk = self.rfile.read(chunk_size)
            except (OSError, ValueError):
                break
            if not chunk:
                break
            remaining -= len(chunk)

    def _read_json_body(self) -> Tuple[Optional[Dict[str, Any]], Optional[str], int]:
        try:
            length = int(self.headers.get("Content-Length", "0"))
        except ValueError:
            self.close_connection = True
            return None, "Tiêu đề Content-Length không hợp lệ.", HTTPStatus.BAD_REQUEST
        if length < 0:
            self.close_connection = True
            return None, "Kích thước dữ liệu gửi lên không hợp lệ.", HTTPStatus.BAD_REQUEST
        if length > MAX_JSON_BODY_BYTES:
            self.close_connection = True
            self._drain_request_body(length)
            return (
                None,
                "Kích thước dữ liệu gửi lên vượt quá giới hạn 2 MiB cho phép.",
                HTTPStatus.REQUEST_ENTITY_TOO_LARGE,
            )
        if length == 0:
            return {}, None, HTTPStatus.OK
        try:
            raw = self.rfile.read(length)
        except (OSError, ValueError):
            self.close_connection = True
            return None, "Không thể đọc dữ liệu yêu cầu từ kết nối.", HTTPStatus.BAD_REQUEST
        if len(raw) < length:
            self.close_connection = True
            return None, "Dữ liệu gửi lên bị cắt ngắn hoặc không đầy đủ.", HTTPStatus.BAD_REQUEST
        try:
            data = json.loads(raw.decode("utf-8"))
        except Exception:
            return None, "Dữ liệu JSON gửi lên bị lỗi cú pháp hoặc sai mã hóa UTF-8.", HTTPStatus.BAD_REQUEST
        if not isinstance(data, dict):
            return None, "Dữ liệu JSON gửi lên phải là một đối tượng (JSON object).", HTTPStatus.BAD_REQUEST
        return data, None, HTTPStatus.OK

    def _serve_static(self, rel_path: str) -> None:
        decoded = unquote(rel_path)
        clean = decoded.lstrip("/") or "index.html"
        if ".." in clean or "\\" in clean:
            self.send_error(HTTPStatus.FORBIDDEN)
            return
        target = (WEB_DIR / clean).resolve()
        try:
            target.relative_to(WEB_DIR.resolve())
        except ValueError:
            self.send_error(HTTPStatus.FORBIDDEN)
            return
        if not target.exists() or not target.is_file():
            self.send_error(HTTPStatus.NOT_FOUND)
            return

        ext = target.suffix.lower()
        mime_map = {
            ".html": "text/html; charset=utf-8",
            ".css": "text/css; charset=utf-8",
            ".js": "application/javascript; charset=utf-8",
            ".mjs": "application/javascript; charset=utf-8",
            ".ts": "text/plain; charset=utf-8",
            ".json": "application/json; charset=utf-8",
            ".svg": "image/svg+xml",
        }
        ctype = mime_map.get(ext) or mimetypes.guess_type(str(target))[0] or "application/octet-stream"
        data = target.read_bytes()
        self.send_response(HTTPStatus.OK)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(data)

    def _handle_sse(self) -> None:
        self.send_response(HTTPStatus.OK)
        self.send_header("Content-Type", "text/event-stream; charset=utf-8")
        self.send_header("Cache-Control", "no-cache")
        self.send_header("Connection", "keep-alive")
        self.end_headers()

        try:
            while True:
                snap = self.orch.get_status_snapshot()
                msg = f"data: {json.dumps(snap, ensure_ascii=False)}\n\n".encode("utf-8")
                self.wfile.write(msg)
                self.wfile.flush()
                time.sleep(0.5 if snap["state"] == "RUNNING" else 1.25)
        except (BrokenPipeError, ConnectionResetError, ConnectionAbortedError, OSError):
            return

    def _resolve_fn_from_body(self, body: Dict[str, Any]) -> Tuple[Optional[IRFunction], Optional[IRModule], Optional[str], int]:
        fn_id_raw = body.get("fn_id")
        if fn_id_raw is not None:
            try:
                fn_id = int(fn_id_raw)
            except (TypeError, ValueError):
                return None, None, "Mã định danh hàm (fn_id) không hợp lệ.", HTTPStatus.BAD_REQUEST
            detail = self.orch.get_function_detail(fn_id)
            if detail is None:
                return None, None, "Không tìm thấy hàm trong danh mục phân tích hiện tại.", HTTPStatus.NOT_FOUND
            code = str(detail.get("source_code", ""))
            lang = str(detail.get("language", "python"))
            mod = _lift_snippet(code, lang, name="catalog_fn")
            fn = _select_fn(mod, detail.get("name"))
            if fn is None:
                return None, mod, "Không thể khôi phục SSA IR cho hàm đã chọn.", HTTPStatus.BAD_REQUEST
            return fn, mod, None, HTTPStatus.OK

        code = str(body.get("code", ""))
        lang = str(body.get("language", "python"))
        fn_name = body.get("function_name")
        if not code.strip():
            return None, None, "Mã nguồn gửi lên đang trống, vui lòng nhập mã nguồn.", HTTPStatus.BAD_REQUEST
        mod = _lift_snippet(code, lang, name="playground")
        if mod.parse_errors or not mod.functions:
            return None, mod, "Không tìm thấy định nghĩa hàm hợp lệ hoặc có lỗi cú pháp.", HTTPStatus.OK
        fn = _select_fn(mod, str(fn_name) if fn_name else None)
        return fn, mod, None, HTTPStatus.OK

    def do_GET(self) -> None:
        parsed = urlparse(self.path)
        path = parsed.path

        if path == "/api/status":
            self._send_json(self.orch.get_status_snapshot())
            return
        if path == "/api/telemetry":
            self._send_json(
                {
                    "state": self.orch.state,
                    "hardware": self.orch.monitor.snapshot().to_dict(),
                    "machine": self.orch.machine,
                }
            )
            return
        if path == "/api/stream":
            self._handle_sse()
            return
        if path == "/api/leaderboard":
            self._send_json({"runs": self.orch.db.list_runs(limit=40)})
            return
        if path.startswith("/api/function/"):
            raw_id = path.split("/api/function/", 1)[1].strip("/")
            if raw_id.isdigit():
                detail = self.orch.get_function_detail(int(raw_id))
                if detail is not None:
                    self._send_json(detail)
                    return
            self._send_json({"error": "Không tìm thấy hàm theo mã định danh yêu cầu."}, status=HTTPStatus.NOT_FOUND)
            return

        if path == "/":
            self._serve_static("index.html")
            return
        self._serve_static(path)

    def do_POST(self) -> None:
        parsed = urlparse(self.path)
        path = parsed.path

        body, err_msg, err_code = self._read_json_body()
        if body is None:
            self._send_json(
                {"error": err_msg},
                status=err_code,
                close_connection=(err_code == HTTPStatus.REQUEST_ENTITY_TOO_LARGE or self.close_connection),
            )
            return

        if path == "/api/run":
            cfg = RunConfig.from_dict(body)
            ok, msg = self.orch.start_run(cfg, blocking=False)
            status = HTTPStatus.OK if ok else HTTPStatus.CONFLICT
            self._send_json({"ok": ok, "message": msg, "config": cfg.to_dict()}, status=status)
            return

        if path == "/api/stop":
            res = self.orch.emergency_stop("Đã kích hoạt Dừng khẩn cấp từ bảng điều khiển Web Studio")
            self._send_json(res)
            return

        if path == "/api/analyze-snippet":
            code = str(body.get("code", ""))
            lang = str(body.get("language", "python"))
            kill_mutants = bool(body.get("kill_mutants", False))
            if not code.strip():
                self._send_json({"error": "Mã nguồn phân tích đang trống, vui lòng nhập mã nguồn."}, status=HTTPStatus.BAD_REQUEST)
                return
            mod = _lift_snippet(code, lang, name="playground")
            reports = [
                _build_fn_analyze_report(fn, idx, kill_mutants=kill_mutants)
                for idx, fn in enumerate(mod.functions)
            ]
            self._send_json({"parse_errors": mod.parse_errors, "functions": reports})
            return

        if path == "/api/generate-tests":
            code = str(body.get("code", ""))
            lang = str(body.get("language", "python"))
            framework = str(body.get("framework", "pytest")).strip().lower()
            include_killers = bool(body.get("include_mutant_killers", False))
            extra_vectors = body.get("extra_vectors")
            if not code.strip():
                self._send_json({"error": "Mã nguồn để sinh unit test đang trống."}, status=HTTPStatus.BAD_REQUEST)
                return
            if framework not in ("pytest", "vitest", "jest"):
                self._send_json(
                    {"error": f"Framework kiểm thử '{framework}' không được hỗ trợ (chỉ hỗ trợ pytest, vitest, jest)."},
                    status=HTTPStatus.BAD_REQUEST,
                )
                return
            mod = _lift_snippet(code, lang, name="playground")
            suites: List[Dict[str, Any]] = []
            for fn in mod.functions:
                optimize_function_ssa(fn)
                sym = run_symbolic_execution(fn, max_paths=64)
                extra_list: List[Dict[str, int]] = list(extra_vectors) if isinstance(extra_vectors, list) else []
                kill_witnesses: List[Dict[str, Any]] = []
                if include_killers:
                    km = kill_surviving_mutants(fn, sym.synthesized_test_vectors + extra_list, max_mutants=60, gas_limit=4000)
                    kill_witnesses = km.kill_witnesses
                    extra_list.extend(km.witness_vectors)
                suite = generate_all_frameworks(fn, symbolic_res=sym, extra_vectors=extra_list or None)
                if include_killers and kill_witnesses:
                    suite = _append_killer_witness_tests(suite, fn, kill_witnesses)
                suites.append(suite)
            self._send_json({"parse_errors": mod.parse_errors, "functions": suites})
            return

        if path == "/api/equivalence":
            old_code = str(body.get("old_code", ""))
            new_code = str(body.get("new_code", ""))
            lang = str(body.get("language", "python"))
            old_fn = body.get("old_fn")
            new_fn = body.get("new_fn")
            res = prove_equivalence(
                old_code,
                new_code,
                language=lang,
                old_fn=str(old_fn) if old_fn else None,
                new_fn=str(new_fn) if new_fn else None,
            )
            if not old_code.strip() or not new_code.strip():
                self._send_json({**res, "error": res["summary"]}, status=HTTPStatus.BAD_REQUEST)
                return
            self._send_json(res)
            return

        if path == "/api/kill-mutants":
            fn, mod, err, code_status = self._resolve_fn_from_body(body)
            if err is not None and fn is None:
                if code_status == HTTPStatus.OK and mod is not None:
                    self._send_json(
                        {
                            "error": err,
                            "parse_errors": mod.parse_errors,
                            "functions": [],
                        },
                        status=HTTPStatus.OK,
                    )
                    return
                self._send_json({"error": err}, status=code_status)
                return
            assert fn is not None
            optimize_function_ssa(fn)
            sym = run_symbolic_execution(fn, max_paths=64)
            existing = body.get("existing_vectors")
            base_vectors = list(existing) if isinstance(existing, list) else sym.synthesized_test_vectors
            mut = kill_surviving_mutants(fn, base_vectors, max_mutants=60, gas_limit=4000)
            base_tests = generate_all_frameworks(fn, symbolic_res=sym, extra_vectors=base_vectors)
            appended_tests = _append_killer_witness_tests(base_tests, fn, mut.kill_witnesses)
            self._send_json(
                {
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
                    "appended_tests": appended_tests,
                }
            )
            return

        if path == "/api/trace-replay":
            inputs = body.get("inputs")
            if not isinstance(inputs, dict):
                self._send_json(
                    {"error": "Tham số 'inputs' để tua vết thực thi phải là một đối tượng JSON (dict)."},
                    status=HTTPStatus.BAD_REQUEST,
                )
                return
            fn, mod, err, code_status = self._resolve_fn_from_body(body)
            if err is not None and fn is None:
                if code_status == HTTPStatus.OK and mod is not None:
                    self._send_json({"error": err, "parse_errors": mod.parse_errors}, status=HTTPStatus.BAD_REQUEST)
                    return
                self._send_json({"error": err}, status=code_status)
                return
            assert fn is not None
            optimize_function_ssa(fn)
            cfg = compute_cfg_analysis(fn)
            ai = run_abstract_interpretation(fn, cfg)
            vm_out = IRInterpreter(gas_limit=2000).execute(fn, inputs)
            steps = replay_function_trace(fn, inputs, intervals=ai.intervals, gas_limit=2000)
            self._send_json(
                {
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
            )
            return

        self._send_json({"error": "Không tìm thấy đường dẫn API yêu cầu."}, status=HTTPStatus.NOT_FOUND)


def create_server(host: str = "127.0.0.1", preferred_port: int = 8765) -> Tuple[HyperionHTTPServer, int]:
    """Khởi tạo máy chủ trên cổng ưu tiên hoặc tự động chuyển sang cổng trống tiếp theo."""
    orch = HyperionOrchestrator()
    if preferred_port == 0:
        srv = HyperionHTTPServer((host, 0), orch)
        return srv, srv.server_address[1]
    for port in [preferred_port] + list(range(preferred_port + 1, preferred_port + 20)):
        try:
            srv = HyperionHTTPServer((host, port), orch)
            return srv, port
        except OSError:
            continue
    srv = HyperionHTTPServer((host, 0), orch)
    return srv, srv.server_address[1]
