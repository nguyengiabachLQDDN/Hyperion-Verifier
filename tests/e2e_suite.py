"""Requirement-driven, opaque-box End-to-End (E2E) test suite for HYPERION.

Tiers:
  Tier 1 (>=40): Isolated happy-path coverage across features F1..F8 (>=5 each).
  Tier 2 (>=40): Boundary, corner, and error-handling cases across F1..F8 (>=5 each).
  Tier 3 (>=8):  Pairwise & multi-feature combination tests.
  Tier 4 (>=5):  Realistic end-to-end application scenarios (S1..S5).

Zero external dependencies (Python 3.10+ stdlib only).
"""

from __future__ import annotations

import argparse
import ast
import ctypes
from ctypes import wintypes
from dataclasses import dataclass
from html.parser import HTMLParser
import inspect
import json
import multiprocessing
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import traceback
import types
from typing import Any, Callable, Dict, Iterable, List, Optional, Set, Tuple
import urllib.error
import urllib.request


ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from hyperion.config import DATA_DIR, ROOT_DIR, WEB_DIR, SafetyConfig
from hyperion.hardware.telemetry import (
    HardwareMonitor,
    SafetyGovernor,
    set_worker_low_priority,
)
from hyperion.orchestrator.coordinator import HyperionOrchestrator
from hyperion.server.app import HyperionHTTPServer
from hyperion.storage.db import LeaderboardDB


VALID_FEATURES = ("F1", "F2", "F3", "F4", "F5", "F6", "F7", "F8")
VALID_TIERS = (1, 2, 3, 4)

VIETNAMESE_DIACRITIC_RE = re.compile(
    r"[àáảãạăằắẳẵặâầấẩẫậèéẻẽẹêềếểễệìíỉĩịòóỏõọôồốổỗộơờớởỡợùúủũụưừứửữựỳýỷỹỵđ]",
    re.IGNORECASE,
)

ALLOWED_TECH_TOKENS = {
    "pytest", "vitest", "jest", "unsat", "sat", "unknown", "dpll(t)", "dpll",
    "cfg", "ssa", "smt", "ir", "vm", "aor", "ror", "lcr", "cr", "bsr",
    "survived", "killed", "timeout", "win10_ssd", "sqlite", "pid", "ram",
    "cpu", "mb", "gb", "loc", "phi", "cli", "api", "http", "json", "sse",
    "url", "html", "dom", "hyperion", "python", "typescript", "js", "ts",
    "dsl", "web", "studio", "worker", "portable", "windows", "node",
    "pragma", "journal_mode", "memory", "below_normal_priority_class",
    "handle", "ctypes", "wintypes", "utf-8", "dfg", "idom", "rpo", "ast",
    "e2e", "msvc", "cpu/ram", "ok", "trap",
}

INTERNAL_ENUM_TOKENS = {
    "IDLE", "RUNNING", "COMPLETED", "STOPPED", "SAFETY_TRIPPED",
    "EQUIVALENT", "NON_EQUIVALENT", "ERROR",
    "DIV_BY_ZERO_RISK", "BUFFER_INDEX_OOB", "TAINT_SINK_FLOW",
    "CONSTANT_BRANCH", "UNSAT_DEAD_BRANCH",
    "DIV_BY_ZERO", "BUFFER_OOB", "ASSERTION_VIOLATION", "TAINT_REACHABLE",
    "CRITICAL", "HIGH", "MEDIUM", "LOW", "INFO", "OK", "TRAP",
    "benchmark", "stress", "analyze", "procedural", "self_host", "custom_path",
}

LEGACY_ENGLISH_HTML_BLACKLIST = [
    "Verification & Stress Workbench",
    "Probing host hardware",
    "CPU load",
    "Free system RAM",
    "Process RAM",
    "Browser workers",
    "Launch engine",
    "Emergency stop",
    "Execution mode",
    "Target corpus",
    "Intensity preset",
    "Scale factor",
    "Hardware protection",
    "In-RAM only",
    "Telemetry & workers",
    "Control-flow graph",
    "SSA & SMT inspector",
    "Mutations & leaderboard",
    "No symbol selected",
    "Live polyglot playground",
    "Source code",
    "In-memory IR mutation matrix",
    "Portable benchmark leaderboard",
]

LEGACY_ENGLISH_JS_BLACKLIST = [
    "Parse Errors:",
    "Tainted SSA Vars:",
    "No interval data.",
    "No counterexample violations",
    "CIRCUIT BREAKER / STOP:",
    "Workers idle",
    "No findings yet.",
    "No matching functions.",
    "Logical Cores",
    "Click or drag any basic block",
]

LEGACY_ENGLISH_README_BLACKLIST = [
    "Hardware Safety Guardrails",
    "Quick Start",
    "Zero SSD Thrashing",
    "OS Responsiveness Guard",
    "Portable Static Analysis",
]

LEGACY_ENGLISH_RUNTIME_BLACKLIST = [
    "System free RAM floor breached",
    "Process RAM ceiling exceeded",
    "Duration limit reached",
    "Empty source snippet",
    "Function not found",
    "Unknown endpoint",
    "=== HYPERION RUN SUMMARY ===",
    "A workload is already running",
]


# ---------------------------------------------------------------------------
# Verified E2E Snippets (Spec-Miner Compliant: loop-free in [-50, 50])
# ---------------------------------------------------------------------------

SNIPPET_A_PY = """\
def audit_packet(k, user_input):
    buf = [1, 2, 3, 4]
    acc = 0
    if k == 9:
        v = buf[k]
        acc = acc + v
    if k > 25:
        if k < 10:
            return -999
    denom = k - 5
    res = 100 // denom
    if k < 0:
        eval(user_input)
    assert k != 4, "k_cannot_be_4"
    return acc + res
"""

SNIPPET_B_TS = """\
export function auditPacketTs(k: number, untrustedPayload: number): number {
    let buf: number[] = [1, 2, 3, 4];
    let acc: number = 0;
    if (k == 9) {
        let v = buf[k];
        acc = acc + v;
    }
    if (k > 30) {
        if (k < 10) {
            return -999;
        }
    }
    let denom = k - 5;
    let res = 100 / denom;
    if (k < 0) {
        sqlExec(untrustedPayload, res);
    }
    assert(k != 4, "k_cannot_be_4");
    return acc + res;
}
"""

SNIPPET_C_PY = """\
def early_return_abs(x):
    if x >= 0:
        return x
    else:
        return -x
"""

SNIPPET_C_TS = """\
export function earlyReturnAbsTs(x: number): number {
    if (x >= 0) {
        return x;
    } else {
        return -x;
    }
}
"""

GATE_THRESHOLD_PY = """\
def gate_threshold(x):
    if x > 10:
        return 100
    return 0
"""

GATE_THRESHOLD_TS = """\
export function gateThresholdTs(x: number): number {
    if (x > 10) {
        return 100;
    }
    return 0;
}
"""

CLASSIFY_SCORE_PY = """\
def classify_score(score, bonus, flags):
    base = (flags & 3) + 1
    if score >= 20 and bonus > 5:
        return (score + bonus) * 2
    elif score >= 10 or bonus > 2:
        return score * base + 5
    else:
        return score - 1
"""

CALC_ACCESS_FEE_OLD_PY = """\
def calc_access_fee(role, amount, coupon):
    if role <= 0:
        return -1
    fee = amount * 2
    if role == 2:
        fee = fee - coupon
    else:
        if coupon > 10:
            fee = fee - 10
        else:
            fee = fee - coupon
    if fee < 0:
        return 0
    return fee
"""

CALC_ACCESS_FEE_NEW_PY = """\
def calc_access_fee_new(role, amount, coupon):
    if role <= 0:
        return -1
    discount = coupon
    if role != 2 and coupon > 10:
        discount = 10
    fee = amount * 2 - discount
    if fee < 0:
        return 0
    return fee
"""

CALC_ACCESS_FEE_BUGGY_PY = """\
def calc_access_fee_buggy(role, amount, coupon):
    if role <= 0:
        return -1
    discount = coupon
    if role != 2 and coupon >= 10:
        discount = 10
    fee = amount * 2 - discount
    return fee
"""

CALC_ACCESS_FEE_TS = """\
export function calcAccessFee(role: number, amount: number, coupon: number): number {
    if (role <= 0) { return -1; }
    let discount = coupon;
    if (role != 2 && coupon > 10) { discount = 10; }
    let fee = amount * 2 - discount;
    if (fee < 0) { return 0; }
    return fee;
}
"""

FILTER_PACKET_GATEWAY_PY = """\
def filter_packet_gateway(proto, hdr_len, flags, payload):
    rules = [10, 20, 30, 40]
    pkt = read_packet(payload)
    score = hdr_len + 8
    if proto == 6 and proto != 6:
        return -99
    if hdr_len > 30 and hdr_len < 10:
        return -88
    if flags == 4 and hdr_len >= 4:
        r = rules[hdr_len]
        score = score + r
    if proto < 0:
        sql_query(pkt, score)
    denom = proto - 2
    if hdr_len > 5:
        score = score // denom
    assert score >= 0, "packet_score_valid"
    return score
"""

VALIDATE_RISK_THRESHOLD_PY = """\
def validate_risk_threshold(level, delta, cap):
    base = level * 2 + 4
    if level > 5:
        adj = base - delta
    else:
        adj = base + delta
    if adj > cap:
        return cap
    return adj
"""


# ---------------------------------------------------------------------------
# Runner Infrastructure, Isolation & Meta-Verification Helpers
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class E2ECase:
    test_id: str
    tier: int
    features: Tuple[str, ...]
    entrypoint: str
    title: str
    fn: Callable[["E2ERunnerContext"], None]


@dataclass
class CLIResult:
    returncode: int
    stdout: str
    stderr: str
    raw_stdout: bytes
    raw_stderr: bytes


TEST_REGISTRY: List[E2ECase] = []


def register_case(
    test_id: str,
    tier: int,
    features: Iterable[str],
    entrypoint: str,
    title: str,
) -> Callable[[Callable[["E2ERunnerContext"], None]], Callable[["E2ERunnerContext"], None]]:
    feat_tuple = tuple(features)

    def _decorator(fn: Callable[["E2ERunnerContext"], None]) -> Callable[["E2ERunnerContext"], None]:
        TEST_REGISTRY.append(
            E2ECase(
                test_id=test_id,
                tier=tier,
                features=feat_tuple,
                entrypoint=entrypoint,
                title=title,
                fn=fn,
            )
        )
        return fn

    return _decorator


class IsolatedHyperionServer:
    """Starts an isolated HyperionHTTPServer on ephemeral port 0 with temp SQLite DB."""

    def __init__(self) -> None:
        self._tmp: Optional[tempfile.TemporaryDirectory[str]] = None
        self._srv: Optional[HyperionHTTPServer] = None
        self._thread: Optional[threading.Thread] = None
        self.orch: Optional[HyperionOrchestrator] = None
        self.base_url: str = ""

    def __enter__(self) -> Tuple[str, HyperionOrchestrator, HyperionHTTPServer]:
        self._tmp = tempfile.TemporaryDirectory(prefix="hyperion_e2e_srv_")
        db = LeaderboardDB(Path(self._tmp.name) / "e2e_benchmarks.sqlite3")
        self.orch = HyperionOrchestrator(db=db)
        self._srv = HyperionHTTPServer(("127.0.0.1", 0), self.orch)
        port = self._srv.server_address[1]
        self._thread = threading.Thread(target=self._srv.serve_forever, daemon=True)
        self._thread.start()
        self.base_url = f"http://127.0.0.1:{port}"
        return self.base_url, self.orch, self._srv

    def __exit__(self, *exc: Any) -> None:
        if self.orch is not None and self.orch.state == "RUNNING":
            try:
                self.orch.emergency_stop("E2E teardown")
            except Exception:
                pass
        if self._srv is not None:
            try:
                self._srv.shutdown()
            except Exception:
                pass
            try:
                self._srv.server_close()
            except Exception:
                pass
        if self._thread is not None:
            self._thread.join(timeout=3.0)
        if self._tmp is not None:
            try:
                self._tmp.cleanup()
            except Exception:
                pass


class E2ERunnerContext:
    """Shared context passed to each E2E test case."""

    def __init__(self, verbose: bool = False) -> None:
        self.verbose = verbose

    def isolated_server(self) -> IsolatedHyperionServer:
        return IsolatedHyperionServer()

    def http_request(
        self,
        base_url: str,
        method: str,
        path: str,
        json_body: Optional[Any] = None,
        raw_bytes: Optional[bytes] = None,
        headers: Optional[Dict[str, str]] = None,
        timeout: float = 20.0,
    ) -> Tuple[int, Dict[str, str], bytes]:
        hdrs: Dict[str, str] = dict(headers or {})
        data: Optional[bytes] = raw_bytes
        if json_body is not None:
            data = json.dumps(json_body).encode("utf-8")
            hdrs.setdefault("Content-Type", "application/json")
        req = urllib.request.Request(
            f"{base_url}{path}",
            data=data,
            headers=hdrs,
            method=method.upper(),
        )
        try:
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                resp_hdrs = {k.lower(): v for k, v in resp.headers.items()}
                return resp.status, resp_hdrs, resp.read()
        except urllib.error.HTTPError as err:
            resp_hdrs = {k.lower(): v for k, v in err.headers.items()} if err.headers else {}
            body = err.read() if err.fp else b""
            return err.code, resp_hdrs, body

    def http_json(
        self,
        base_url: str,
        method: str,
        path: str,
        json_body: Optional[Any] = None,
        raw_bytes: Optional[bytes] = None,
        headers: Optional[Dict[str, str]] = None,
        timeout: float = 20.0,
    ) -> Tuple[int, Any, bytes]:
        status, _, raw = self.http_request(
            base_url, method, path, json_body=json_body, raw_bytes=raw_bytes, headers=headers, timeout=timeout
        )
        parsed = None
        if raw:
            try:
                parsed = json.loads(raw.decode("utf-8"))
            except Exception:
                parsed = None
        return status, parsed, raw

    def run_cli(self, args: List[str], timeout: float = 60.0) -> CLIResult:
        env = os.environ.copy()
        env["PYTHONDONTWRITEBYTECODE"] = "1"
        env["PYTHONIOENCODING"] = "utf-8"
        proc = subprocess.run(
            [sys.executable, str(ROOT / "main.py"), *args],
            cwd=str(ROOT),
            env=env,
            capture_output=True,
            timeout=timeout,
        )
        raw_out = proc.stdout or b""
        raw_err = proc.stderr or b""
        stdout = raw_out.decode("utf-8", errors="replace")
        stderr = raw_err.decode("utf-8", errors="replace")
        return CLIResult(
            returncode=proc.returncode,
            stdout=stdout,
            stderr=stderr,
            raw_stdout=raw_out,
            raw_stderr=raw_err,
        )


def extract_json_from_cli_stdout(stdout: str) -> Any:
    """Extract JSON payload from CLI stdout (supports pure JSON or summary+JSON)."""
    stripped = stdout.strip()
    if not stripped:
        raise AssertionError("CLI stdout is empty; expected JSON output")
    try:
        return json.loads(stripped)
    except json.JSONDecodeError:
        pass
    decoder = json.JSONDecoder()
    for idx, ch in enumerate(stdout):
        if ch in "{[":
            try:
                obj, end = decoder.raw_decode(stdout[idx:])
                if stdout[idx + end :].strip() == "" or isinstance(obj, (dict, list)):
                    return obj
            except json.JSONDecodeError:
                continue
    raise AssertionError(f"Could not parse JSON from CLI stdout:\n{stdout[:600]}")


def wait_for_run_state(
    ctx: E2ERunnerContext,
    base_url: str,
    target_states: Iterable[str],
    timeout: float = 25.0,
) -> Dict[str, Any]:
    targets = set(target_states)
    deadline = time.monotonic() + timeout
    last_snap: Dict[str, Any] = {}
    while time.monotonic() < deadline:
        status, snap, _ = ctx.http_json(base_url, "GET", "/api/status")
        assert status == 200 and isinstance(snap, dict), f"Bad /api/status: {status} {snap}"
        last_snap = snap
        if snap.get("state") in targets:
            return snap
        time.sleep(0.05)
    raise AssertionError(f"Timed out waiting for states {targets}; last state={last_snap.get('state')}")


def _assert_has_vietnamese(text: str, context_label: str = "text") -> None:
    assert isinstance(text, str) and text.strip(), f"Expected non-empty string for {context_label}"
    assert VIETNAMESE_DIACRITIC_RE.search(text), (
        f"Expected Vietnamese text with diacritics for {context_label}, got: {text!r}"
    )


def _assert_no_blacklist(text: str, blacklist: Iterable[str], label: str) -> None:
    for bad in blacklist:
        assert bad not in text, f"Untranslated English string {bad!r} found in {label}"


class _PytestRaisesCtx:
    """Minimal stdlib-only context manager emulating pytest.raises."""

    def __init__(self, expected_exc: Any) -> None:
        self.expected_exc = expected_exc
        self.value: Optional[BaseException] = None

    def __enter__(self) -> "_PytestRaisesCtx":
        return self

    def __exit__(self, exc_type: Any, exc_val: Any, exc_tb: Any) -> bool:
        if exc_type is None:
            raise AssertionError(f"Expected {self.expected_exc} to be raised, but nothing was raised")
        if issubclass(exc_type, self.expected_exc):
            self.value = exc_val
            return True
        return False


def _pytest_raises(expected_exc: Any, *args: Any, **kwargs: Any) -> Any:
    if args:
        fn = args[0]
        call_args = args[1:]
        with _PytestRaisesCtx(expected_exc) as ctx:
            fn(*call_args, **kwargs)
        return ctx
    return _PytestRaisesCtx(expected_exc)


def _strip_placeholder_imports(tree: ast.Module, target_names: Set[str]) -> ast.Module:
    new_body: List[ast.stmt] = []
    for stmt in tree.body:
        if isinstance(stmt, ast.Import):
            kept = [a for a in stmt.names if a.name != "pytest"]
            if kept:
                stmt.names = kept
                new_body.append(stmt)
            continue
        if isinstance(stmt, ast.ImportFrom):
            mod = stmt.module or ""
            if mod == "pytest":
                continue
            if all(a.name in target_names for a in stmt.names) and mod not in sys.stdlib_module_names:
                continue
        new_body.append(stmt)
    tree.body = new_body
    ast.fix_missing_locations(tree)
    return tree


def verify_and_exec_pytest(
    pytest_code: str,
    target_fns: Dict[str, Callable[..., Any]],
    expect_fail: bool = False,
    min_tests: int = 1,
) -> int:
    """Parse generated pytest code with ast.parse and execute test_* functions in isolation."""
    assert isinstance(pytest_code, str) and pytest_code.strip(), "Empty pytest code"
    tree = ast.parse(pytest_code)
    test_names = [
        node.name
        for node in tree.body
        if isinstance(node, ast.FunctionDef) and node.name.startswith("test_")
    ]
    assert len(test_names) >= min_tests, (
        f"Expected >= {min_tests} test_* functions, got {len(test_names)}: {test_names}"
    )

    filtered_tree = _strip_placeholder_imports(ast.parse(pytest_code), set(target_fns.keys()))
    code_obj = compile(filtered_tree, "<generated_pytest>", "exec")

    pytest_mod = types.ModuleType("pytest")
    pytest_mod.raises = _pytest_raises  # type: ignore[attr-defined]
    pytest_mod.approx = lambda val, rel=1e-6, abs=1e-12: val  # type: ignore[attr-defined]

    ns: Dict[str, Any] = {
        "__builtins__": __builtins__,
        "pytest": pytest_mod,
        "raises": _pytest_raises,
    }
    ns.update(target_fns)

    prev_pytest = sys.modules.get("pytest")
    sys.modules["pytest"] = pytest_mod
    try:
        exec(code_obj, ns)
        # Re-inject target functions so caller-supplied variants override any inline copy
        ns.update(target_fns)
        failures = 0
        for name in test_names:
            fn = ns[name]
            try:
                fn()
            except Exception:
                if not expect_fail:
                    raise
                failures += 1
        if expect_fail:
            assert failures >= 1, (
                f"Expected at least 1 generated test to fail against buggy/mutated target, but all {len(test_names)} passed"
            )
    finally:
        if prev_pytest is None:
            sys.modules.pop("pytest", None)
        else:
            sys.modules["pytest"] = prev_pytest

    return len(test_names)


def verify_js_test_suite(
    js_code: str,
    framework: str,
    expected_fn_name: Optional[str] = None,
) -> None:
    """Validate vitest/jest structural assertions and run node --check when Node is present."""
    assert isinstance(js_code, str) and js_code.strip(), f"Empty {framework} code"
    assert "describe(" in js_code, f"Expected describe( in {framework} suite"
    assert "it(" in js_code or "test(" in js_code, f"Expected it( or test( in {framework} suite"
    assert "expect(" in js_code, f"Expected expect( in {framework} suite"
    if expected_fn_name:
        assert expected_fn_name in js_code, f"Expected {expected_fn_name} in {framework} suite"
    if framework == "vitest":
        assert "vitest" in js_code, "Expected vitest reference/import in vitest suite"
    elif framework == "jest":
        assert "from 'vitest'" not in js_code and 'from "vitest"' not in js_code, (
            "Jest suite must not import vitest"
        )

    node_bin = shutil.which("node")
    if node_bin:
        cleaned_lines = []
        for line in js_code.splitlines():
            if re.match(r"^\s*import\s+.*from\s+['\"][^'\"]+['\"]\s*;?\s*$", line):
                continue
            cleaned_lines.append(line)
        cleaned = "\n".join(cleaned_lines)
        proc = subprocess.run(
            [node_bin, "--check", "--input-type=module", "-"],
            input=cleaned,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=15,
        )
        assert proc.returncode == 0, (
            f"node --check failed on generated {framework} code:\n{proc.stderr}\nCode:\n{cleaned}"
        )


class _VisibleHTMLScanner(HTMLParser):
    """Extracts visible text and UI attributes from HTML, skipping script/style/comments."""

    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.lang: Optional[str] = None
        self.skip_depth = 0
        self.text_chunks: List[str] = []
        self.ui_attrs: List[str] = []
        self.ids: Set[str] = set()
        self.external_urls: List[str] = []
        self.option_values: List[str] = []

    def handle_starttag(self, tag: str, attrs: List[Tuple[str, Optional[str]]]) -> None:
        t = tag.lower()
        attr_map = {k.lower(): (v or "") for k, v in attrs}
        if t == "html":
            self.lang = attr_map.get("lang")
        if "id" in attr_map and attr_map["id"]:
            self.ids.add(attr_map["id"])
        if t == "option" and "value" in attr_map:
            self.option_values.append(attr_map["value"])
        if t in ("script", "link"):
            url = attr_map.get("src") or attr_map.get("href") or ""
            if url.startswith(("http://", "https://", "//")):
                self.external_urls.append(url)
        for key in ("placeholder", "title", "aria-label"):
            val = attr_map.get(key, "").strip()
            if val:
                self.ui_attrs.append(val)
        if t in ("script", "style"):
            self.skip_depth += 1

    def handle_endtag(self, tag: str) -> None:
        if tag.lower() in ("script", "style") and self.skip_depth > 0:
            self.skip_depth -= 1

    def handle_data(self, data: str) -> None:
        if self.skip_depth == 0:
            s = re.sub(r"\s+", " ", data).strip()
            if s:
                self.text_chunks.append(s)


def _strip_tech_tokens(text: str) -> str:
    tokens = re.findall(r"[A-Za-zÀ-ỹ0-9_()-]+", text)
    kept = []
    for tok in tokens:
        low = tok.lower()
        if low in ALLOWED_TECH_TOKENS or tok in INTERNAL_ENUM_TOKENS:
            continue
        if re.fullmatch(r"b\d+", low) or re.fullmatch(r"\d+", low):
            continue
        kept.append(tok)
    return " ".join(kept)


def validate_vietnamese_html(html_text: str) -> _VisibleHTMLScanner:
    parser = _VisibleHTMLScanner()
    parser.feed(html_text)
    parser.close()

    assert parser.lang == "vi", f"Expected <html lang='vi'>, got {parser.lang!r}"
    assert not parser.external_urls, f"External CDN URLs forbidden: {parser.external_urls}"

    all_visible = parser.text_chunks + parser.ui_attrs
    joined = "\n".join(all_visible)
    _assert_no_blacklist(joined, LEGACY_ENGLISH_HTML_BLACKLIST, "web/index.html")

    english_prose_re = re.compile(
        r"\b(the|and|for|with|from|into|click|drag|select|refresh|reset|loading|running|workers|no\s+\w+|priority)\b",
        re.IGNORECASE,
    )
    for snippet in all_visible:
        cleaned = _strip_tech_tokens(snippet)
        words = [w for w in cleaned.split() if any(ch.isalpha() for ch in w)]
        if len(words) >= 3 and not VIETNAMESE_DIACRITIC_RE.search(cleaned):
            assert not english_prose_re.search(cleaned), (
                f"Untranslated English visible HTML snippet: {snippet!r}"
            )
    return parser


def _strip_sample_blocks_from_js(js_text: str) -> str:
    cleaned = re.sub(r"(?:const|let|var)\s+SAMPLE_(?:PY|TS)\s*=\s*`[\s\S]*?`;", "", js_text)
    return cleaned


def validate_vietnamese_js(js_text: str, label: str = "web/dist/app.js") -> None:
    stripped = _strip_sample_blocks_from_js(js_text)
    _assert_no_blacklist(stripped, LEGACY_ENGLISH_JS_BLACKLIST, label)
    assert VIETNAMESE_DIACRITIC_RE.search(stripped), f"Expected Vietnamese strings in {label}"
    low = stripped.lower()
    assert ("bước" in low or "tua" in low), f"Expected Vietnamese trace replay UI text in {label}"
    assert ("tương đương" in low or "sai khác" in low), f"Expected Vietnamese equivalence UI text in {label}"
    assert ("nhánh" in low or "chết" in low), f"Expected Vietnamese dead-branch UI text in {label}"


def validate_vietnamese_readme(readme_text: str) -> None:
    _assert_no_blacklist(readme_text, LEGACY_ENGLISH_README_BLACKLIST, "README.md")
    no_fenced = re.sub(r"```[\s\S]*?```", " ", readme_text)
    no_inline = re.sub(r"`[^`]+`", " ", no_fenced)
    no_urls = re.sub(r"https?://\S+", " ", no_inline)
    prose_lines = [
        ln.strip()
        for ln in no_urls.splitlines()
        if ln.strip() and not ln.strip().startswith(("---", "|"))
    ]
    assert prose_lines, "README.md prose is empty"
    _assert_has_vietnamese("\n".join(prose_lines), "README.md prose")
    for token in ("pytest", "vitest", "UNSAT", "DPLL(T)"):
        assert token in readme_text, f"Expected preserved technical token {token!r} in README.md"


def validate_vietnamese_runtime_text(text: str, label: str) -> None:
    _assert_no_blacklist(text, LEGACY_ENGLISH_RUNTIME_BLACKLIST, label)
    _assert_has_vietnamese(text, label)


# ===========================================================================
# TIER 1 — Isolated Happy-Path Tests (F1..F8, >=5 per feature = 42 tests)
# ===========================================================================

# --- F1: 64-bit HANDLE Fix & Hardware Guardrails (5 tests) ---

@register_case("T1-F1-01", 1, ("F1",), "API", "get_win32_bindings caches singletons with 64-bit HANDLE/DWORD/BOOL signatures")
def t1_f1_01(ctx: E2ERunnerContext) -> None:
    from hyperion.hardware import telemetry

    assert hasattr(telemetry, "get_win32_bindings"), "Missing telemetry.get_win32_bindings()"
    b1 = telemetry.get_win32_bindings()
    b2 = telemetry.get_win32_bindings()
    assert isinstance(b1, dict) and "kernel32" in b1 and "psapi" in b1
    if os.name == "nt":
        k32, psapi = b1["kernel32"], b1["psapi"]
        assert k32 is b2["kernel32"] and psapi is b2["psapi"], "WinDLL bindings must be cached singletons"
        assert k32.GetCurrentProcess.restype in (wintypes.HANDLE, ctypes.c_void_p)
        assert ctypes.sizeof(k32.GetCurrentProcess.restype) == ctypes.sizeof(ctypes.c_void_p)
        assert list(k32.SetPriorityClass.argtypes) == [wintypes.HANDLE, wintypes.DWORD]
        assert k32.SetPriorityClass.restype == wintypes.BOOL
        assert list(k32.OpenProcess.argtypes) == [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
        assert k32.OpenProcess.restype in (wintypes.HANDLE, ctypes.c_void_p)
        assert list(k32.CloseHandle.argtypes) == [wintypes.HANDLE]
        assert k32.CloseHandle.restype == wintypes.BOOL
        assert psapi.GetProcessMemoryInfo.argtypes[0] in (wintypes.HANDLE, ctypes.c_void_p)
        assert psapi.GetProcessMemoryInfo.argtypes[2] == wintypes.DWORD
        assert psapi.GetProcessMemoryInfo.restype == wintypes.BOOL
        assert k32.GlobalMemoryStatusEx.restype == wintypes.BOOL
        assert k32.GetSystemTimes.restype == wintypes.BOOL


@register_case("T1-F1-02", 1, ("F1",), "API", "set_worker_low_priority and HardwareMonitor.snapshot return valid hardware metrics")
def t1_f1_02(ctx: E2ERunnerContext) -> None:
    assert set_worker_low_priority() is True
    mon = HardwareMonitor()
    snap = mon.snapshot()
    assert snap.total_ram_mb > 512
    assert snap.avail_ram_mb > 0
    assert 0.0 <= snap.free_ram_pct <= 100.0
    assert snap.process_ram_mb > 0
    assert snap.logical_cores >= 1


@register_case("T1-F1-03", 1, ("F1",), "API", "SafetyConfig default min_free_system_ram_pct==10.0 and healthy SafetyGovernor passes")
def t1_f1_03(ctx: E2ERunnerContext) -> None:
    default_cfg = SafetyConfig()
    assert default_cfg.min_free_system_ram_pct == 10.0, (
        f"Expected SafetyConfig().min_free_system_ram_pct == 10.0, got {default_cfg.min_free_system_ram_pct}"
    )
    gov = SafetyGovernor(
        SafetyConfig(max_process_ram_mb=8192, min_free_system_ram_pct=5.0, max_duration_sec=60),
        HardwareMonitor(),
    )
    ok, reason, snap = gov.check_health()
    assert ok is True and reason == "OK", f"Expected healthy check, got {(ok, reason)}"
    assert snap.total_ram_mb > 0


@register_case("T1-F1-04", 1, ("F1",), "HTTP", "Emergency Stop halts active workload in <50ms and transitions to STOPPED")
def t1_f1_04(ctx: E2ERunnerContext) -> None:
    with ctx.isolated_server() as (base_url, orch, _):
        status, data, _ = ctx.http_json(
            base_url,
            "POST",
            "/api/run",
            json_body={
                "mode": "stress",
                "corpus_source": "procedural",
                "intensity": "heavy",
                "scale_factor": 4,
                "safety": {"max_workers": 2, "min_free_system_ram_pct": 5.0, "max_duration_sec": 30},
            },
        )
        assert status == 200 and data["ok"] is True
        deadline = time.monotonic() + 5.0
        while time.monotonic() < deadline and orch.state != "RUNNING":
            time.sleep(0.01)

        t0 = time.perf_counter()
        stop_res = orch.emergency_stop("E2E emergency stop")
        dt = time.perf_counter() - t0
        assert stop_res["stopped"] is True
        assert dt < 0.050, f"Emergency stop exceeded 50ms SLA: {dt:.4f}s"

        st_code, st_json, _ = ctx.http_json(base_url, "GET", "/api/status")
        assert st_code == 200
        assert st_json["state"] in ("STOPPED", "COMPLETED")


@register_case("T1-F1-05", 1, ("F1",), "HTTP", "GET /api/telemetry returns hardware and machine telemetry in IDLE state")
def t1_f1_05(ctx: E2ERunnerContext) -> None:
    with ctx.isolated_server() as (base_url, _, _):
        status, data, _ = ctx.http_json(base_url, "GET", "/api/telemetry")
        assert status == 200 and isinstance(data, dict)
        assert data["state"] == "IDLE"
        for key in ("cpu_load_pct", "total_ram_mb", "free_ram_pct", "process_ram_mb", "tracemalloc_mb"):
            assert key in data["hardware"], f"Missing hardware.{key}"
        for key in ("cpu_model", "logical_cores", "total_ram_gb", "arch"):
            assert key in data["machine"], f"Missing machine.{key}"


# --- F2: Zero External Deps & Portability (5 tests) ---

@register_case("T1-F2-01", 1, ("F2",), "STATIC", "All Python files import only stdlib or internal hyperion modules")
def t1_f2_01(ctx: E2ERunnerContext) -> None:
    py_files = [ROOT / "main.py"]
    py_files.extend(sorted((ROOT / "hyperion").rglob("*.py")))
    py_files.extend(sorted((ROOT / "tests").glob("*.py")))
    for path in py_files:
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    top = alias.name.split(".")[0]
                    assert top == "hyperion" or top in sys.stdlib_module_names, (
                        f"Non-stdlib import {alias.name!r} in {path}"
                    )
            elif isinstance(node, ast.ImportFrom) and node.level == 0 and node.module:
                top = node.module.split(".")[0]
                assert top == "hyperion" or top in sys.stdlib_module_names, (
                    f"Non-stdlib from-import {node.module!r} in {path}"
                )


@register_case("T1-F2-02", 1, ("F2",), "STATIC", "Web Studio has zero external CDN links, no node_modules, and non-empty dist bundles")
def t1_f2_02(ctx: E2ERunnerContext) -> None:
    html_text = (WEB_DIR / "index.html").read_text(encoding="utf-8")
    scanner = _VisibleHTMLScanner()
    scanner.feed(html_text)
    scanner.close()
    assert not scanner.external_urls, f"External CDN URLs found: {scanner.external_urls}"
    assert not (ROOT / "package.json").exists(), "package.json must not exist in zero-bundler repo"
    assert not (ROOT / "node_modules").exists(), "node_modules must not exist"
    assert (WEB_DIR / "dist" / "app.js").stat().st_size > 1000
    assert (WEB_DIR / "dist" / "compute_worker.js").stat().st_size > 200


@register_case("T1-F2-03", 1, ("F2",), "STATIC", "Web JS bundles pass node --check and TS sources pass stripTypeScriptTypes")
def t1_f2_03(ctx: E2ERunnerContext) -> None:
    node_bin = shutil.which("node")
    assert node_bin, "Node.js binary not found on PATH for JS/TS syntax check"
    for js_rel in ("dist/app.js", "dist/compute_worker.js"):
        proc = subprocess.run(
            [node_bin, "--check", str(WEB_DIR / js_rel)],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=15,
        )
        assert proc.returncode == 0, f"node --check failed on {js_rel}: {proc.stderr}"

    for ts_rel in ("src/app.ts", "src/compute_worker.ts"):
        ts_path = str(WEB_DIR / ts_rel).replace("\\", "\\\\")
        script = (
            "const fs=require('fs'), m=require('module');"
            f"const code=m.stripTypeScriptTypes(fs.readFileSync('{ts_path}','utf8'),{{mode:'strip'}});"
            "process.stdout.write(code);"
        )
        strip_proc = subprocess.run(
            [node_bin, "-e", script],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=15,
        )
        assert strip_proc.returncode == 0, f"stripTypeScriptTypes failed on {ts_rel}: {strip_proc.stderr}"
        chk_proc = subprocess.run(
            [node_bin, "--check", "--input-type=module", "-"],
            input=strip_proc.stdout,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=15,
        )
        assert chk_proc.returncode == 0, f"Stripped TS failed node --check for {ts_rel}: {chk_proc.stderr}"


@register_case("T1-F2-04", 1, ("F2",), "HTTP", "HTTP server serves static Web Studio assets with Cache-Control: no-store")
def t1_f2_04(ctx: E2ERunnerContext) -> None:
    with ctx.isolated_server() as (base_url, _, _):
        expected = [
            ("/", "text/html"),
            ("/styles.css", "text/css"),
            ("/dist/app.js", "javascript"),
            ("/dist/compute_worker.js", "javascript"),
        ]
        for path, ctype_sub in expected:
            status, hdrs, body = ctx.http_request(base_url, "GET", path)
            assert status == 200, f"GET {path} returned {status}"
            assert hdrs.get("cache-control") == "no-store", f"Missing no-store on {path}"
            assert ctype_sub in hdrs.get("content-type", ""), f"Unexpected Content-Type on {path}: {hdrs}"
            assert len(body) > 100, f"Empty body for {path}"


@register_case("T1-F2-05", 1, ("F2",), "CLI", "Isolated server and CLI analysis leave data/benchmarks.sqlite3 and __pycache__ clean")
def t1_f2_05(ctx: E2ERunnerContext) -> None:
    db_file = DATA_DIR / "benchmarks.sqlite3"
    before_stat = (db_file.exists(), db_file.stat().st_size if db_file.exists() else 0, db_file.stat().st_mtime if db_file.exists() else 0.0)
    with ctx.isolated_server() as (base_url, _, _):
        s1, _, _ = ctx.http_json(base_url, "POST", "/api/analyze-snippet", json_body={"code": GATE_THRESHOLD_PY, "language": "python"})
        s2, _, _ = ctx.http_json(base_url, "POST", "/api/generate-tests", json_body={"code": GATE_THRESHOLD_PY, "language": "python", "framework": "pytest"})
        assert s1 == 200 and s2 == 200

    with tempfile.TemporaryDirectory(prefix="hyperion_e2e_iso_") as tmp:
        tmp_py = Path(tmp) / "sample.py"
        tmp_py.write_text(GATE_THRESHOLD_PY, encoding="utf-8")
        res = ctx.run_cli(["--gen-tests", str(tmp_py), "--lang", "python", "--framework", "pytest", "--json-out"])
        assert res.returncode == 0, f"CLI --gen-tests failed: {res.stderr}\n{res.stdout}"

    after_stat = (db_file.exists(), db_file.stat().st_size if db_file.exists() else 0, db_file.stat().st_mtime if db_file.exists() else 0.0)
    assert before_stat == after_stat, f"data/benchmarks.sqlite3 was modified! before={before_stat}, after={after_stat}"


# --- F3: Dead-Branch Detector (5 tests) ---

@register_case("T1-F3-01", 1, ("F3",), "HTTP", "Detect UNSAT dead branch in Python snippet and mark cfg_graph is_dead")
def t1_f3_01(ctx: E2ERunnerContext) -> None:
    code = "def f(x):\n    if x > 10:\n        if x < 5:\n            return 1\n    return 0\n"
    with ctx.isolated_server() as (base_url, _, _):
        status, data, _ = ctx.http_json(base_url, "POST", "/api/analyze-snippet", json_body={"code": code, "language": "python"})
        assert status == 200
        fn = data["functions"][0]
        assert len(fn["dead_branches"]) >= 1, "Expected UNSAT dead branch for x > 10 and x < 5"
        db0 = fn["dead_branches"][0]
        assert "line" in db0 and "reason" in db0
        _assert_has_vietnamese(db0["reason"], "dead_branches[0].reason")
        assert any(n.get("is_dead") is True for n in fn["cfg_graph"]["nodes"]), "Expected dead node in cfg_graph"
        assert any(e.get("is_dead") is True for e in fn["cfg_graph"]["edges"]), "Expected dead edge in cfg_graph"


@register_case("T1-F3-02", 1, ("F3",), "HTTP", "Detect UNSAT dead branch in TypeScript snippet")
def t1_f3_02(ctx: E2ERunnerContext) -> None:
    code = (
        "export function checkDead(a: number): number {\n"
        "    if (a == 3 && a == 9) { return -1; }\n"
        "    return a + 1;\n"
        "}\n"
    )
    with ctx.isolated_server() as (base_url, _, _):
        status, data, _ = ctx.http_json(base_url, "POST", "/api/analyze-snippet", json_body={"code": code, "language": "typescript"})
        assert status == 200
        fn = data["functions"][0]
        assert len(fn["dead_branches"]) >= 1
        assert any(n.get("is_dead") is True for n in fn["cfg_graph"]["nodes"])
        assert any(n.get("is_dead") is False for n in fn["cfg_graph"]["nodes"])


@register_case("T1-F3-03", 1, ("F3",), "HTTP", "Detect transitive UNSAT contradiction y = x + 1; x > 5 and y < 0")
def t1_f3_03(ctx: E2ERunnerContext) -> None:
    code = (
        "def g(x):\n"
        "    y = x + 1\n"
        "    if x > 5:\n"
        "        if y < 0:\n"
        "            return 99\n"
        "    return y\n"
    )
    with ctx.isolated_server() as (base_url, _, _):
        status, data, _ = ctx.http_json(base_url, "POST", "/api/analyze-snippet", json_body={"code": code, "language": "python"})
        assert status == 200
        fn = data["functions"][0]
        assert len(fn["dead_branches"]) >= 1, "Expected transitive UNSAT dead branch"


@register_case("T1-F3-04", 1, ("F3",), "CLI", "CLI --dead-branches detects UNSAT branch and emits Vietnamese output + JSON")
def t1_f3_04(ctx: E2ERunnerContext) -> None:
    code = "def f(x):\n    if x > 20:\n        if x < 10:\n            return 1\n    return 0\n"
    with tempfile.TemporaryDirectory(prefix="hyperion_e2e_db_") as tmp:
        py_file = Path(tmp) / "dead.py"
        py_file.write_text(code, encoding="utf-8")
        res_txt = ctx.run_cli(["--dead-branches", str(py_file), "--lang", "python"])
        assert res_txt.returncode == 0, f"CLI --dead-branches failed: {res_txt.stderr}\n{res_txt.stdout}"
        _assert_has_vietnamese(res_txt.stdout, "CLI --dead-branches stdout")
        assert "UNSAT" in res_txt.stdout or "Nhánh" in res_txt.stdout

        res_json = ctx.run_cli(["--dead-branches", str(py_file), "--lang", "python", "--json-out"])
        assert res_json.returncode == 0
        payload = extract_json_from_cli_stdout(res_json.stdout)
        fns = payload.get("functions", [payload] if "dead_branches" in payload else [])
        assert len(fns) >= 1 and len(fns[0]["dead_branches"]) >= 1


@register_case("T1-F3-05", 1, ("F3",), "HTTP", "Live-only early_return_abs produces zero dead_branches and zero is_dead flags")
def t1_f3_05(ctx: E2ERunnerContext) -> None:
    with ctx.isolated_server() as (base_url, _, _):
        status, data, _ = ctx.http_json(
            base_url, "POST", "/api/analyze-snippet", json_body={"code": SNIPPET_C_PY, "language": "python"}
        )
        assert status == 200
        fn = data["functions"][0]
        assert fn["dead_branches"] == [], f"Unexpected dead branches: {fn['dead_branches']}"
        assert all(n.get("is_dead") is False and n.get("dead_reason", "") == "" for n in fn["cfg_graph"]["nodes"])
        assert all(e.get("is_dead") is False for e in fn["cfg_graph"]["edges"])


# --- F4: Bug Trace Replay Data & Controls (5 tests) ---

@register_case("T1-F4-01", 1, ("F4",), "HTTP", "Counterexample for DIV_BY_ZERO includes step-by-step trace_steps with vars and intervals")
def t1_f4_01(ctx: E2ERunnerContext) -> None:
    code = "def div_bug(x):\n    y = x - 3\n    z = 100 // y\n    return z\n"
    with ctx.isolated_server() as (base_url, _, _):
        status, data, _ = ctx.http_json(base_url, "POST", "/api/analyze-snippet", json_body={"code": code, "language": "python"})
        assert status == 200
        cxs = data["functions"][0]["counterexamples"]
        div_cx = next((c for c in cxs if c["kind"] == "DIV_BY_ZERO"), None)
        assert div_cx is not None, f"Expected DIV_BY_ZERO counterexample, got {cxs}"
        assert div_cx["inputs"]["x"] == 3
        assert len(div_cx["path_blocks"]) >= 1
        steps = div_cx["trace_steps"]
        assert isinstance(steps, list) and len(steps) >= 2
        for st in steps:
            for key in ("step", "block_id", "block_label", "line", "instruction", "vars", "intervals", "event"):
                assert key in st, f"Missing {key} in trace step"
        assert any(any(k.startswith("y") and v == 0 for k, v in st["vars"].items()) for st in steps)


@register_case("T1-F4-02", 1, ("F4",), "HTTP", "TypeScript BUFFER_OOB counterexample emits monotonic trace_steps")
def t1_f4_02(ctx: E2ERunnerContext) -> None:
    code = (
        "export function oobTs(i: number): number {\n"
        "    let a = [10, 20, 30];\n"
        "    let acc = 0;\n"
        "    if (i == 5) { let v = a[i]; acc = acc + v; }\n"
        "    return acc;\n"
        "}\n"
    )
    with ctx.isolated_server() as (base_url, _, _):
        status, data, _ = ctx.http_json(base_url, "POST", "/api/analyze-snippet", json_body={"code": code, "language": "typescript"})
        assert status == 200
        cxs = data["functions"][0]["counterexamples"]
        oob_cx = next((c for c in cxs if c["kind"] == "BUFFER_OOB"), None)
        assert oob_cx is not None, f"Expected BUFFER_OOB, got {cxs}"
        assert oob_cx["inputs"]["i"] == 5
        steps = oob_cx["trace_steps"]
        assert len(steps) >= 2
        assert [s["step"] for s in steps] == list(range(len(steps)))


@register_case("T1-F4-03", 1, ("F4",), "HTTP", "POST /api/trace-replay replays concrete path and returns exact outcome")
def t1_f4_03(ctx: E2ERunnerContext) -> None:
    code = (
        "def f(a, b):\n"
        "    c = a + b\n"
        "    if c > 10:\n"
        "        return c * 2\n"
        "    return c\n"
    )
    with ctx.isolated_server() as (base_url, _, _):
        status, data, _ = ctx.http_json(
            base_url,
            "POST",
            "/api/trace-replay",
            json_body={"code": code, "language": "python", "inputs": {"a": 7, "b": 5}},
        )
        assert status == 200
        assert data["function"] == "f"
        assert data["inputs"] == {"a": 7, "b": 5}
        assert data["outcome"]["return_value"] == 24
        assert len(data["trace_steps"]) >= 3
        assert any(any(k.startswith("c") and v == 12 for k, v in st["vars"].items()) for st in data["trace_steps"])


@register_case("T1-F4-04", 1, ("F4",), "CLI", "CLI --trace-replay replays trap path from B0 with vars and intervals")
def t1_f4_04(ctx: E2ERunnerContext) -> None:
    code = "def f(x):\n    return 50 // x\n"
    with tempfile.TemporaryDirectory(prefix="hyperion_e2e_tr_") as tmp:
        py_file = Path(tmp) / "div0.py"
        py_file.write_text(code, encoding="utf-8")
        res = ctx.run_cli(["--trace-replay", str(py_file), "--lang", "python", "--inputs", '{"x": 0}', "--json-out"])
        assert res.returncode == 0, f"CLI --trace-replay failed: {res.stderr}\n{res.stdout}"
        payload = extract_json_from_cli_stdout(res.stdout)
        steps = payload["trace_steps"]
        assert len(steps) >= 1
        assert steps[0]["block_id"] == 0
        assert any(v == 0 for st in steps for v in st["vars"].values())
        assert isinstance(steps[0]["intervals"], dict)


@register_case("T1-F4-05", 1, ("F4",), "STATIC", "Web Studio HTML and app.js contain semantic dead-branch and trace-replay controls")
def t1_f4_05(ctx: E2ERunnerContext) -> None:
    html_text = (WEB_DIR / "index.html").read_text(encoding="utf-8")
    app_js = (WEB_DIR / "dist" / "app.js").read_text(encoding="utf-8")
    assert 'id="cfgCanvas"' in html_text
    assert 'id="cfgBlockOverlay"' in html_text
    html_low = html_text.lower()
    assert ("unsat" in html_low or "nhánh" in html_low), "Missing dead-branch toggle/label in web/index.html"
    assert ("tua" in html_low or "bước" in html_low or "trace" in html_low), "Missing trace replay UI controls in web/index.html"
    assert "trace_steps" in app_js, "web/dist/app.js must handle trace_steps"
    assert "is_dead" in app_js, "web/dist/app.js must handle is_dead"
    assert "/api/trace-replay" in app_js or "trace_steps" in app_js


# --- F5: Unit Test Generator (6 tests) ---

@register_case("T1-F5-01", 1, ("F5",), "HTTP", "Generate pytest suite for Python classify(x) and meta-execute against real Python")
def t1_f5_01(ctx: E2ERunnerContext) -> None:
    code = (
        "def classify(x):\n"
        "    if x > 10:\n"
        "        return x * 2\n"
        "    elif x < 0:\n"
        "        return -x\n"
        "    return x + 1\n"
    )
    ns: Dict[str, Any] = {}
    exec(code, ns)
    classify_fn = ns["classify"]

    with ctx.isolated_server() as (base_url, _, _):
        status, data, _ = ctx.http_json(
            base_url, "POST", "/api/generate-tests", json_body={"code": code, "language": "python", "framework": "pytest"}
        )
        assert status == 200
        fn_res = data["functions"][0]
        pytest_code = fn_res["pytest"]
        count = verify_and_exec_pytest(pytest_code, {"classify": classify_fn}, expect_fail=False, min_tests=3)
        assert count >= 3


@register_case("T1-F5-02", 1, ("F5",), "HTTP", "Generate vitest suite for TypeScript clampScore and pass node --check")
def t1_f5_02(ctx: E2ERunnerContext) -> None:
    code = (
        "export function clampScore(s: number): number {\n"
        "    if (s < 0) { return 0; }\n"
        "    if (s > 100) { return 100; }\n"
        "    return s;\n"
        "}\n"
    )
    with ctx.isolated_server() as (base_url, _, _):
        status, data, _ = ctx.http_json(
            base_url, "POST", "/api/generate-tests", json_body={"code": code, "language": "typescript", "framework": "vitest"}
        )
        assert status == 200
        vitest_code = data["functions"][0]["vitest"]
        verify_js_test_suite(vitest_code, "vitest", expected_fn_name="clampScore")


@register_case("T1-F5-03", 1, ("F5",), "HTTP", "Generate jest suite for TypeScript clampScore and pass node --check")
def t1_f5_03(ctx: E2ERunnerContext) -> None:
    code = (
        "export function clampScore(s: number): number {\n"
        "    if (s < 0) { return 0; }\n"
        "    if (s > 100) { return 100; }\n"
        "    return s;\n"
        "}\n"
    )
    with ctx.isolated_server() as (base_url, _, _):
        status, data, _ = ctx.http_json(
            base_url, "POST", "/api/generate-tests", json_body={"code": code, "language": "typescript", "framework": "jest"}
        )
        assert status == 200
        jest_code = data["functions"][0]["jest"]
        verify_js_test_suite(jest_code, "jest", expected_fn_name="clampScore")


@register_case("T1-F5-04", 1, ("F5",), "HTTP", "Generate pytest suite with pytest.raises for division-by-zero trap and meta-execute")
def t1_f5_04(ctx: E2ERunnerContext) -> None:
    code = (
        "def safe_div(a, b):\n"
        "    if b == 0:\n"
        "        return 10 // b\n"
        "    return a + b\n"
    )
    ns: Dict[str, Any] = {}
    exec(code, ns)
    safe_div_fn = ns["safe_div"]

    with ctx.isolated_server() as (base_url, _, _):
        status, data, _ = ctx.http_json(
            base_url, "POST", "/api/generate-tests", json_body={"code": code, "language": "python", "framework": "pytest"}
        )
        assert status == 200
        pytest_code = data["functions"][0]["pytest"]
        assert "raises" in pytest_code, f"Expected pytest.raises in trap test suite:\n{pytest_code}"
        verify_and_exec_pytest(pytest_code, {"safe_div": safe_div_fn}, expect_fail=False, min_tests=2)


@register_case("T1-F5-05", 1, ("F5",), "CLI", "CLI --gen-tests emits valid parseable pytest suite")
def t1_f5_05(ctx: E2ERunnerContext) -> None:
    code = "def add_pos(a, b):\n    if a > 0:\n        return a + b\n    return b\n"
    with tempfile.TemporaryDirectory(prefix="hyperion_e2e_gt_") as tmp:
        py_file = Path(tmp) / "add_pos.py"
        py_file.write_text(code, encoding="utf-8")
        res = ctx.run_cli(["--gen-tests", str(py_file), "--framework", "pytest", "--lang", "python", "--json-out"])
        assert res.returncode == 0, f"CLI --gen-tests failed: {res.stderr}\n{res.stdout}"
        payload = extract_json_from_cli_stdout(res.stdout)
        pytest_code = payload["functions"][0]["pytest"]
        ast.parse(pytest_code)
        assert "def test_" in pytest_code


@register_case("T1-F5-06", 1, ("F5",), "HTTP", "POST /api/analyze-snippet includes inline generated_tests for all frameworks")
def t1_f5_06(ctx: E2ERunnerContext) -> None:
    code = "def max2(a, b):\n    if a > b:\n        return a\n    return b\n"
    with ctx.isolated_server() as (base_url, _, _):
        status, data, _ = ctx.http_json(base_url, "POST", "/api/analyze-snippet", json_body={"code": code, "language": "python"})
        assert status == 200
        gt = data["functions"][0]["generated_tests"]
        for key in ("pytest", "vitest", "jest", "cases"):
            assert key in gt and gt[key], f"Missing or empty generated_tests.{key}"


# --- F6: Semantic Equivalence Prover (6 tests) ---

@register_case("T1-F6-01", 1, ("F6",), "HTTP", "Equivalence Prover confirms semantically equivalent Python refactor")
def t1_f6_01(ctx: E2ERunnerContext) -> None:
    old_code = "def f_old(x):\n    if x > 0:\n        return x + x\n    return 0\n"
    new_code = "def f_new(x):\n    if x <= 0:\n        return 0\n    return 2 * x\n"
    with ctx.isolated_server() as (base_url, _, _):
        status, data, _ = ctx.http_json(
            base_url, "POST", "/api/equivalence", json_body={"old_code": old_code, "new_code": new_code, "language": "python"}
        )
        assert status == 200
        assert data["equivalent"] is True
        assert data["status"] == "EQUIVALENT"
        assert data["counterexample"] is None
        assert data["paths_checked"] >= 2
        _assert_has_vietnamese(data["summary"], "equivalence.summary")


@register_case("T1-F6-02", 1, ("F6",), "HTTP", "Equivalence Prover finds exact boundary counterexample x==10 for off-by-one bug")
def t1_f6_02(ctx: E2ERunnerContext) -> None:
    old_code = "def g_old(x):\n    if x >= 10:\n        return 1\n    return 0\n"
    new_code = "def g_new(x):\n    if x > 10:\n        return 1\n    return 0\n"
    with ctx.isolated_server() as (base_url, _, _):
        status, data, _ = ctx.http_json(
            base_url, "POST", "/api/equivalence", json_body={"old_code": old_code, "new_code": new_code, "language": "python"}
        )
        assert status == 200
        assert data["equivalent"] is False
        assert data["status"] == "NON_EQUIVALENT"
        cx = data["counterexample"]
        assert cx is not None and cx["inputs"]["x"] == 10
        assert cx["old_output"]["return_value"] == 1
        assert cx["new_output"]["return_value"] == 0


@register_case("T1-F6-03", 1, ("F6",), "HTTP", "Equivalence Prover confirms equivalent TypeScript algebraic refactor")
def t1_f6_03(ctx: E2ERunnerContext) -> None:
    old_code = "export function calc(a: number, b: number): number { return (a + b) - b; }\n"
    new_code = "export function calc2(a: number, b: number): number { return a; }\n"
    with ctx.isolated_server() as (base_url, _, _):
        status, data, _ = ctx.http_json(
            base_url, "POST", "/api/equivalence", json_body={"old_code": old_code, "new_code": new_code, "language": "typescript"}
        )
        assert status == 200
        assert data["equivalent"] is True
        assert data["status"] == "EQUIVALENT"
        assert data["params"] == ["a", "b"]


@register_case("T1-F6-04", 1, ("F6",), "HTTP", "Equivalence Prover catches trap divergence (guarded vs unguarded division by zero)")
def t1_f6_04(ctx: E2ERunnerContext) -> None:
    old_code = "def h_old(x):\n    if x == 0:\n        return 0\n    return 100 // x\n"
    new_code = "def h_new(x):\n    return 100 // x\n"
    with ctx.isolated_server() as (base_url, _, _):
        status, data, _ = ctx.http_json(
            base_url, "POST", "/api/equivalence", json_body={"old_code": old_code, "new_code": new_code, "language": "python"}
        )
        assert status == 200
        assert data["equivalent"] is False
        assert data["status"] == "NON_EQUIVALENT"
        cx = data["counterexample"]
        assert cx["inputs"]["x"] == 0
        assert cx["old_output"]["status"] == "OK"
        assert cx["new_output"]["status"] == "TRAP"


@register_case("T1-F6-05", 1, ("F6",), "CLI", "CLI --prove-equiv detects non-equivalent Python pair and outputs Vietnamese + JSON")
def t1_f6_05(ctx: E2ERunnerContext) -> None:
    old_code = "def g_old(x):\n    if x >= 10:\n        return 1\n    return 0\n"
    new_code = "def g_new(x):\n    if x > 10:\n        return 1\n    return 0\n"
    with tempfile.TemporaryDirectory(prefix="hyperion_e2e_eq_") as tmp:
        f_old = Path(tmp) / "old.py"
        f_new = Path(tmp) / "new.py"
        f_old.write_text(old_code, encoding="utf-8")
        f_new.write_text(new_code, encoding="utf-8")
        res = ctx.run_cli(["--prove-equiv", str(f_old), str(f_new), "--lang", "python", "--json-out"])
        assert res.returncode == 0, f"CLI --prove-equiv failed: {res.stderr}\n{res.stdout}"
        payload = extract_json_from_cli_stdout(res.stdout)
        assert payload["equivalent"] is False
        assert payload["status"] == "NON_EQUIVALENT"
        assert payload["counterexample"]["inputs"]["x"] == 10


@register_case("T1-F6-06", 1, ("F6",), "HTTP", "Equivalence Prover selects explicit old_fn and new_fn in multi-function modules")
def t1_f6_06(ctx: E2ERunnerContext) -> None:
    old_code = (
        "def helper(z):\n    return z + 1\n\n"
        "def target_v1(x):\n    return x * 2\n"
    )
    new_code = (
        "def helper(z):\n    return z + 999\n\n"
        "def target_v2(x):\n    return x + x\n"
    )
    with ctx.isolated_server() as (base_url, _, _):
        status, data, _ = ctx.http_json(
            base_url,
            "POST",
            "/api/equivalence",
            json_body={
                "old_code": old_code,
                "new_code": new_code,
                "language": "python",
                "old_fn": "target_v1",
                "new_fn": "target_v2",
            },
        )
        assert status == 200
        assert data["old_function"] == "target_v1"
        assert data["new_function"] == "target_v2"
        assert data["equivalent"] is True


# --- F7: SMT-Driven Surviving Mutant Killer (5 tests) ---

@register_case("T1-F7-01", 1, ("F7",), "HTTP", "POST /api/kill-mutants kills surviving ROR mutant in gate_threshold at x==10")
def t1_f7_01(ctx: E2ERunnerContext) -> None:
    ns: Dict[str, Any] = {}
    exec(GATE_THRESHOLD_PY, ns)
    gate_fn = ns["gate_threshold"]

    with ctx.isolated_server() as (base_url, _, _):
        status, data, _ = ctx.http_json(
            base_url,
            "POST",
            "/api/kill-mutants",
            json_body={
                "code": GATE_THRESHOLD_PY,
                "language": "python",
                "existing_vectors": [{"x": 0}, {"x": 11}],
            },
        )
        assert status == 200
        assert data["initial_survived"] >= 1
        assert data["newly_killed"] >= 1
        witnesses = data["kill_witnesses"]
        assert len(witnesses) >= 1
        assert any(w["witness_inputs"].get("x") == 10 for w in witnesses)
        for w in witnesses:
            assert w["orig_output"] != w["mut_output"]
        verify_and_exec_pytest(data["appended_tests"]["pytest"], {"gate_threshold": gate_fn}, expect_fail=False)


@register_case("T1-F7-02", 1, ("F7",), "HTTP", "POST /api/kill-mutants kills surviving mutant in TypeScript and emits vitest/jest tests")
def t1_f7_02(ctx: E2ERunnerContext) -> None:
    with ctx.isolated_server() as (base_url, _, _):
        status, data, _ = ctx.http_json(
            base_url,
            "POST",
            "/api/kill-mutants",
            json_body={
                "code": GATE_THRESHOLD_TS,
                "language": "typescript",
                "existing_vectors": [{"x": 0}, {"x": 11}],
            },
        )
        assert status == 200
        assert data["newly_killed"] >= 1
        assert any(w["witness_inputs"].get("x") == 10 for w in data["kill_witnesses"])
        for w in data["kill_witnesses"]:
            assert w["orig_output"] != w["mut_output"]
        verify_js_test_suite(data["appended_tests"]["vitest"], "vitest", expected_fn_name="gateThresholdTs")
        verify_js_test_suite(data["appended_tests"]["jest"], "jest", expected_fn_name="gateThresholdTs")


@register_case("T1-F7-03", 1, ("F7",), "HTTP", "POST /api/analyze-snippet with kill_mutants=true populates kill_witnesses and killed_by_smt")
def t1_f7_03(ctx: E2ERunnerContext) -> None:
    with ctx.isolated_server() as (base_url, _, _):
        status, data, _ = ctx.http_json(
            base_url,
            "POST",
            "/api/analyze-snippet",
            json_body={"code": GATE_THRESHOLD_PY, "language": "python", "kill_mutants": True},
        )
        assert status == 200
        fn = data["functions"][0]
        assert len(fn["kill_witnesses"]) >= 1
        assert any(r.get("killed_by_smt") is True and r.get("killer_inputs") for r in fn["mutation"]["records"])
        assert "10" in fn["generated_tests"]["pytest"]


@register_case("T1-F7-04", 1, ("F7",), "HTTP", "POST /api/kill-mutants works via fn_id from catalog after benchmark run")
def t1_f7_04(ctx: E2ERunnerContext) -> None:
    with ctx.isolated_server() as (base_url, _, _):
        st, run_res, _ = ctx.http_json(
            base_url,
            "POST",
            "/api/run",
            json_body={
                "mode": "benchmark",
                "corpus_source": "procedural",
                "intensity": "balanced",
                "scale_factor": 1,
                "safety": {"max_workers": 2, "min_free_system_ram_pct": 5.0, "max_duration_sec": 30},
            },
        )
        assert st == 200 and run_res["ok"] is True
        snap = wait_for_run_state(ctx, base_url, ("COMPLETED", "STOPPED", "SAFETY_TRIPPED"), timeout=30.0)
        assert snap["state"] == "COMPLETED", f"Run did not complete: {snap.get('stop_reason')}"
        catalog = snap.get("catalog_summary", [])
        assert len(catalog) >= 1
        target = next((item for item in catalog if item.get("mutants_total", 0) > 0), catalog[0])
        fn_id = target["id"]

        ks, kdata, _ = ctx.http_json(base_url, "POST", "/api/kill-mutants", json_body={"fn_id": fn_id})
        assert ks == 200
        for key in ("function", "mutation", "kill_witnesses", "appended_tests"):
            assert key in kdata, f"Missing {key} in /api/kill-mutants catalog response"


@register_case("T1-F7-05", 1, ("F7",), "CLI", "CLI --kill-mutants synthesizes concrete SMT witnesses for gate_threshold")
def t1_f7_05(ctx: E2ERunnerContext) -> None:
    with tempfile.TemporaryDirectory(prefix="hyperion_e2e_km_") as tmp:
        py_file = Path(tmp) / "gate.py"
        py_file.write_text(GATE_THRESHOLD_PY, encoding="utf-8")
        res = ctx.run_cli(["--kill-mutants", str(py_file), "--lang", "python", "--json-out"])
        assert res.returncode == 0, f"CLI --kill-mutants failed: {res.stderr}\n{res.stdout}"
        payload = extract_json_from_cli_stdout(res.stdout)
        assert len(payload["kill_witnesses"]) >= 1
        assert any(w["witness_inputs"].get("x") == 10 and w["orig_output"] != w["mut_output"] for w in payload["kill_witnesses"])
        ast.parse(payload["appended_tests"]["pytest"])


# --- F8: Complete Vietnamese Localization (5 tests) ---

@register_case("T1-F8-01", 1, ("F8",), "STATIC", "Web Studio HTML, TS, and JS are 100% localized in Vietnamese")
def t1_f8_01(ctx: E2ERunnerContext) -> None:
    html_text = (WEB_DIR / "index.html").read_text(encoding="utf-8")
    app_ts = (WEB_DIR / "src" / "app.ts").read_text(encoding="utf-8")
    app_js = (WEB_DIR / "dist" / "app.js").read_text(encoding="utf-8")
    validate_vietnamese_html(html_text)
    validate_vietnamese_js(app_ts, "web/src/app.ts")
    validate_vietnamese_js(app_js, "web/dist/app.js")


@register_case("T1-F8-02", 1, ("F8",), "STATIC", "README.md is localized in Vietnamese while preserving technical tokens")
def t1_f8_02(ctx: E2ERunnerContext) -> None:
    readme_text = (ROOT_DIR / "README.md").read_text(encoding="utf-8")
    validate_vietnamese_readme(readme_text)


@register_case("T1-F8-03", 1, ("F8",), "HTTP", "Analyzer findings, counterexamples, and dead_branches emit Vietnamese descriptions while preserving enum codes")
def t1_f8_03(ctx: E2ERunnerContext) -> None:
    with ctx.isolated_server() as (base_url, _, _):
        status, data, _ = ctx.http_json(
            base_url, "POST", "/api/analyze-snippet", json_body={"code": SNIPPET_A_PY, "language": "python"}
        )
        assert status == 200
        fn = data["functions"][0]
        assert len(fn["ai_findings"]) >= 1
        for finding in fn["ai_findings"]:
            assert finding["kind"] in INTERNAL_ENUM_TOKENS
            assert finding["severity"] in INTERNAL_ENUM_TOKENS
            validate_vietnamese_runtime_text(finding["message"], "ai_findings.message")
        assert len(fn["counterexamples"]) >= 4
        for cx in fn["counterexamples"]:
            assert cx["kind"] in INTERNAL_ENUM_TOKENS
            assert cx["severity"] in INTERNAL_ENUM_TOKENS
            validate_vietnamese_runtime_text(cx["description"], "counterexamples.description")
        assert len(fn["dead_branches"]) >= 1
        for db in fn["dead_branches"]:
            validate_vietnamese_runtime_text(db["reason"], "dead_branches.reason")


@register_case("T1-F8-04", 1, ("F8",), "CLI", "CLI --help and analysis commands output Vietnamese prose and preserve technical terms")
def t1_f8_04(ctx: E2ERunnerContext) -> None:
    help_res = ctx.run_cli(["--help"])
    assert help_res.returncode == 0
    validate_vietnamese_runtime_text(help_res.stdout, "main.py --help")

    with tempfile.TemporaryDirectory(prefix="hyperion_e2e_vi_") as tmp:
        py_file = Path(tmp) / "dead.py"
        py_file.write_text("def f(x):\n    if x > 20:\n        if x < 10:\n            return 1\n    return 0\n", encoding="utf-8")
        res = ctx.run_cli(["--dead-branches", str(py_file), "--lang", "python"])
        assert res.returncode == 0
        validate_vietnamese_runtime_text(res.stdout, "CLI --dead-branches stdout")


@register_case("T1-F8-05", 1, ("F8",), "API", "SafetyGovernor trip reasons are localized in Vietnamese while healthy check returns OK")
def t1_f8_05(ctx: E2ERunnerContext) -> None:
    mon = HardwareMonitor()
    ok_gov = SafetyGovernor(SafetyConfig(max_process_ram_mb=8192, min_free_system_ram_pct=5.0, max_duration_sec=60), mon)
    ok, reason, _ = ok_gov.check_health()
    assert ok and reason == "OK"

    floor_gov = SafetyGovernor(SafetyConfig(min_free_system_ram_pct=99.9), mon)
    ok_f, reason_f, _ = floor_gov.check_health()
    assert not ok_f
    validate_vietnamese_runtime_text(reason_f, "SafetyGovernor RAM floor reason")

    ceil_gov = SafetyGovernor(SafetyConfig(max_process_ram_mb=256, min_free_system_ram_pct=5.0), mon)
    ok_c, reason_c, _ = ceil_gov.check_health(extra_worker_ram_mb=99999.0)
    assert not ok_c
    validate_vietnamese_runtime_text(reason_c, "SafetyGovernor RAM ceiling reason")

    time_gov = SafetyGovernor(SafetyConfig(max_duration_sec=5, min_free_system_ram_pct=5.0), mon)
    time_gov.start_time -= 999.0
    ok_t, reason_t, _ = time_gov.check_health()
    assert not ok_t
    validate_vietnamese_runtime_text(reason_t, "SafetyGovernor duration reason")


# ===========================================================================
# TIER 2 — Boundary, Corner & Error Cases (F1..F8, >=5 per feature = 42 tests)
# ===========================================================================

# --- F1: Hardware Boundaries & Guardrails (6 tests) ---

@register_case("T2-F1-01", 2, ("F1",), "API", "64-bit HANDLE signatures avoid 32-bit sign truncation and OpenProcess/CloseHandle work on PID")
def t2_f1_01(ctx: E2ERunnerContext) -> None:
    from hyperion.hardware import telemetry

    if os.name != "nt":
        assert set_worker_low_priority() is True
        return
    bindings = telemetry.get_win32_bindings()
    k32 = bindings["kernel32"]
    psapi = bindings["psapi"]
    assert k32.GetCurrentProcess.restype is not ctypes.c_long
    assert k32.GetCurrentProcess.restype is not ctypes.c_int32
    assert ctypes.sizeof(k32.GetCurrentProcess.restype) == 8

    PROCESS_QUERY_LIMITED_INFORMATION = 0x1000
    h = k32.OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, False, os.getpid())
    assert h, "OpenProcess failed on current PID"
    try:
        pmc = telemetry.PROCESS_MEMORY_COUNTERS_EX()
        pmc.cb = ctypes.sizeof(telemetry.PROCESS_MEMORY_COUNTERS_EX)
        ok = psapi.GetProcessMemoryInfo(h, ctypes.byref(pmc), pmc.cb)
        assert bool(ok) is True and pmc.WorkingSetSize > 0
    finally:
        assert bool(k32.CloseHandle(h)) is True

    bad_h = k32.OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, False, 0x7FFFFFF0)
    assert not bad_h


@register_case("T2-F1-02", 2, ("F1",), "API", "SafetyGovernor trips immediately when min_free_system_ram_pct=99.9")
def t2_f1_02(ctx: E2ERunnerContext) -> None:
    gov = SafetyGovernor(SafetyConfig(min_free_system_ram_pct=99.9), HardwareMonitor())
    ok, reason, snap = gov.check_health()
    assert ok is False and gov.tripped is True
    assert snap.free_ram_pct < 99.9
    validate_vietnamese_runtime_text(reason, "RAM floor trip")
    assert "RAM" in reason or "%" in reason


@register_case("T2-F1-03", 2, ("F1",), "API", "SafetyGovernor trips distinctly on RAM ceiling and max duration")
def t2_f1_03(ctx: E2ERunnerContext) -> None:
    mon = HardwareMonitor()
    g_ram = SafetyGovernor(SafetyConfig(max_process_ram_mb=256, min_free_system_ram_pct=5.0, max_duration_sec=60), mon)
    ok_r, reason_r, _ = g_ram.check_health(extra_worker_ram_mb=99999.0)
    assert ok_r is False and g_ram.tripped is True

    g_dur = SafetyGovernor(SafetyConfig(max_process_ram_mb=8192, min_free_system_ram_pct=5.0, max_duration_sec=5), mon)
    g_dur.start_time -= 100.0
    ok_d, reason_d, _ = g_dur.check_health()
    assert ok_d is False and g_dur.tripped is True
    assert reason_r != reason_d
    validate_vietnamese_runtime_text(reason_r, "RAM ceiling trip")
    validate_vietnamese_runtime_text(reason_d, "Duration trip")


@register_case("T2-F1-04", 2, ("F1",), "API", "SafetyConfig.clamp() enforces min and max operational bounds")
def t2_f1_04(ctx: E2ERunnerContext) -> None:
    low = SafetyConfig(
        max_workers=-5,
        max_process_ram_mb=1,
        min_free_system_ram_pct=0.0,
        max_duration_sec=1,
        max_symbolic_paths_per_fn=1,
        max_mutants_per_fn=1,
        instruction_gas_limit=1,
        ram_arena_mb=999999,
    ).clamp()
    assert low.max_workers == 1
    assert low.max_process_ram_mb == 256
    assert 5.0 <= low.min_free_system_ram_pct <= 95.0
    assert low.max_duration_sec == 5
    assert low.max_symbolic_paths_per_fn == 8
    assert low.max_mutants_per_fn == 4
    assert low.instruction_gas_limit == 200
    assert low.ram_arena_mb <= int(256 * 0.85)

    high = SafetyConfig(
        max_workers=9999,
        max_process_ram_mb=999999,
        min_free_system_ram_pct=150.0,
        max_duration_sec=999999,
        instruction_gas_limit=999999,
    ).clamp()
    assert high.max_process_ram_mb == 16384
    assert high.min_free_system_ram_pct <= 95.0
    assert high.max_duration_sec == 3600
    assert high.instruction_gas_limit == 50000


@register_case("T2-F1-05", 2, ("F1",), "HTTP", "POST /api/stop is idempotent when IDLE and preserves server health")
def t2_f1_05(ctx: E2ERunnerContext) -> None:
    with ctx.isolated_server() as (base_url, _, _):
        for _ in range(2):
            t0 = time.perf_counter()
            st, data, _ = ctx.http_json(base_url, "POST", "/api/stop")
            dt = time.perf_counter() - t0
            assert st == 200 and data["stopped"] is True
            assert dt < 0.250
        st_tel, _, _ = ctx.http_json(base_url, "GET", "/api/telemetry")
        assert st_tel == 200


@register_case("T2-F1-06", 2, ("F1",), "HTTP", "Concurrent POST /api/run returns 409 Conflict with Vietnamese message")
def t2_f1_06(ctx: E2ERunnerContext) -> None:
    with ctx.isolated_server() as (base_url, orch, _):
        payload = {
            "mode": "stress",
            "corpus_source": "procedural",
            "intensity": "heavy",
            "scale_factor": 5,
            "safety": {"max_workers": 2, "min_free_system_ram_pct": 5.0, "max_duration_sec": 30},
        }
        st1, d1, _ = ctx.http_json(base_url, "POST", "/api/run", json_body=payload)
        assert st1 == 200 and d1["ok"] is True
        st2, d2, _ = ctx.http_json(base_url, "POST", "/api/run", json_body=payload)
        assert st2 == 409 and d2["ok"] is False
        validate_vietnamese_runtime_text(d2["message"], "409 conflict message")
        orch.emergency_stop("Cleanup after 409 test")


# --- F2: HTTP Robustness & Missing File Errors (5 tests) ---

@register_case("T2-F2-01", 2, ("F2",), "HTTP", "Malformed JSON body returns 400 client error without crashing server")
def t2_f2_01(ctx: E2ERunnerContext) -> None:
    with ctx.isolated_server() as (base_url, _, _):
        for route in ("/api/analyze-snippet", "/api/equivalence"):
            st, data, _ = ctx.http_json(
                base_url,
                "POST",
                route,
                raw_bytes=b"{not valid json!!!",
                headers={"Content-Type": "application/json"},
            )
            assert st == 400 and isinstance(data, dict) and "error" in data, f"Expected 400 error on {route}, got {st} {data}"
        st_tel, _, _ = ctx.http_json(base_url, "GET", "/api/telemetry")
        assert st_tel == 200


@register_case("T2-F2-02", 2, ("F2",), "HTTP", "Non-dict JSON body returns 400 client error without 500 traceback")
def t2_f2_02(ctx: E2ERunnerContext) -> None:
    with ctx.isolated_server() as (base_url, _, _):
        for raw in (b"[1, 2, 3]", b'"hello"'):
            st, data, _ = ctx.http_json(
                base_url,
                "POST",
                "/api/analyze-snippet",
                raw_bytes=raw,
                headers={"Content-Type": "application/json"},
            )
            assert st == 400 and isinstance(data, dict) and "error" in data


@register_case("T2-F2-03", 2, ("F2",), "HTTP", "Oversized >2 MiB POST body is cleanly rejected (400 or 413)")
def t2_f2_03(ctx: E2ERunnerContext) -> None:
    with ctx.isolated_server() as (base_url, _, _):
        big = b'{"code": "' + (b"x" * (2 * 1024 * 1024 + 1024)) + b'"}'
        st, data, _ = ctx.http_json(
            base_url,
            "POST",
            "/api/analyze-snippet",
            raw_bytes=big,
            headers={"Content-Type": "application/json"},
        )
        assert st in (400, 413), f"Expected 400/413 for oversized body, got {st}"
        assert isinstance(data, dict) and "error" in data
        st_ok, _, _ = ctx.http_json(base_url, "GET", "/api/status")
        assert st_ok == 200


@register_case("T2-F2-04", 2, ("F2",), "HTTP", "Path traversal and missing static assets return 403/404 and never leak repo files")
def t2_f2_04(ctx: E2ERunnerContext) -> None:
    with ctx.isolated_server() as (base_url, _, _):
        for path in ("/../main.py", "/..%2fmain.py"):
            st, _, body = ctx.http_request(base_url, "GET", path)
            assert st in (403, 404), f"Traversal {path} returned {st}"
            assert b"build_arg_parser" not in body
        st_miss, _, _ = ctx.http_request(base_url, "GET", "/nonexistent_asset_xyz.js")
        assert st_miss == 404


@register_case("T2-F2-05", 2, ("F2",), "CLI", "Missing input files across all new CLI flags exit non-zero cleanly in Vietnamese")
def t2_f2_05(ctx: E2ERunnerContext) -> None:
    missing = str(ROOT / "nonexistent_e2e_file_xyz_999.py")
    invocations = [
        ["--gen-tests", missing, "--lang", "python"],
        ["--prove-equiv", missing, missing, "--lang", "python"],
        ["--kill-mutants", missing, "--lang", "python"],
        ["--dead-branches", missing, "--lang", "python"],
        ["--trace-replay", missing, "--lang", "python", "--inputs", '{"x": 1}'],
    ]
    for args in invocations:
        res = ctx.run_cli(args)
        assert res.returncode != 0, f"Expected non-zero exit for missing file on {args}"
        combined = res.stdout + res.stderr
        assert "Traceback (most recent call last)" not in combined, f"Raw traceback leaked on {args}: {combined}"
        _assert_has_vietnamese(combined, f"CLI missing-file error ({args[0]})")


# --- F3: Dead-Branch Detector Boundaries (5 tests) ---

@register_case("T2-F3-01", 2, ("F3",), "HTTP", "Early-return if/else negative control reports zero dead_branches in Python and TS")
def t2_f3_01(ctx: E2ERunnerContext) -> None:
    with ctx.isolated_server() as (base_url, _, _):
        for lang, code in (("python", SNIPPET_C_PY), ("typescript", SNIPPET_C_TS)):
            st, data, _ = ctx.http_json(
                base_url, "POST", "/api/analyze-snippet", json_body={"code": code, "language": lang}
            )
            assert st == 200
            fn = data["functions"][0]
            assert fn["dead_branches"] == [], f"Synthetic if_join leaked into {lang} dead_branches: {fn['dead_branches']}"
            assert all(n.get("is_dead") is False for n in fn["cfg_graph"]["nodes"])


@register_case("T2-F3-02", 2, ("F3",), "HTTP", "Empty or whitespace-only snippets return 400 error for Python and TS")
def t2_f3_02(ctx: E2ERunnerContext) -> None:
    with ctx.isolated_server() as (base_url, _, _):
        for lang, code in (("python", "   \n\t  "), ("typescript", "")):
            st, data, _ = ctx.http_json(
                base_url, "POST", "/api/analyze-snippet", json_body={"code": code, "language": lang}
            )
            assert st == 400 and "error" in data


@register_case("T2-F3-03", 2, ("F3",), "HTTP", "Syntax errors populate parse_errors in Python and return functions==[] in TS without 500")
def t2_f3_03(ctx: E2ERunnerContext) -> None:
    with ctx.isolated_server() as (base_url, _, _):
        st_py, d_py, _ = ctx.http_json(
            base_url, "POST", "/api/analyze-snippet", json_body={"code": "def broken(x:\n    return x\n", "language": "python"}
        )
        assert st_py in (200, 400)
        assert len(d_py.get("parse_errors", [])) >= 1
        assert d_py.get("functions", []) == []

        st_ts, d_ts, _ = ctx.http_json(
            base_url,
            "POST",
            "/api/analyze-snippet",
            json_body={"code": "function { ??? invalid !!!", "language": "typescript"},
        )
        assert st_ts in (200, 400)
        assert d_ts.get("functions", []) == []


@register_case("T2-F3-04", 2, ("F3",), "HTTP", "Contradictory compound AND and constant false branch are both detected without duplication")
def t2_f3_04(ctx: E2ERunnerContext) -> None:
    code = (
        "def c(x):\n"
        "    if x == 1 and x == 2:\n"
        "        return 10\n"
        "    if 0:\n"
        "        return 20\n"
        "    return 30\n"
    )
    with ctx.isolated_server() as (base_url, _, _):
        st, data, _ = ctx.http_json(base_url, "POST", "/api/analyze-snippet", json_body={"code": code, "language": "python"})
        assert st == 200
        dbs = data["functions"][0]["dead_branches"]
        assert len(dbs) >= 2, f"Expected both dead branches flagged, got {dbs}"
        keys = [(d.get("block_id"), d.get("target_block_id"), d.get("branch_kind")) for d in dbs]
        assert len(keys) == len(set(keys)), f"Duplicate dead_branches entries: {dbs}"


@register_case("T2-F3-05", 2, ("F3",), "HTTP", "Snippet with comments and constants only returns empty functions and zero parse_errors")
def t2_f3_05(ctx: E2ERunnerContext) -> None:
    code = "# only a comment\nCONST_X = 42\n"
    with ctx.isolated_server() as (base_url, _, _):
        st, data, _ = ctx.http_json(base_url, "POST", "/api/analyze-snippet", json_body={"code": code, "language": "python"})
        assert st == 200
        assert data["parse_errors"] == []
        assert data["functions"] == []


# --- F4: Trace Replay Boundaries (5 tests) ---

@register_case("T2-F4-01", 2, ("F4",), "HTTP", "Missing or invalid fn_id returns 404 across /api/trace-replay and /api/function/<id>")
def t2_f4_01(ctx: E2ERunnerContext) -> None:
    with ctx.isolated_server() as (base_url, _, _):
        s1, d1, _ = ctx.http_json(base_url, "POST", "/api/trace-replay", json_body={"fn_id": 999999, "inputs": {"x": 1}})
        s2, d2, _ = ctx.http_json(base_url, "GET", "/api/function/999999")
        s3, d3, _ = ctx.http_json(base_url, "GET", "/api/function/not_a_number")
        for st, data in ((s1, d1), (s2, d2), (s3, d3)):
            assert st == 404 and "error" in data


@register_case("T2-F4-02", 2, ("F4",), "HTTP", "Invalid inputs type returns 400 and partial inputs do not 500 crash")
def t2_f4_02(ctx: E2ERunnerContext) -> None:
    code = "def f(x, y):\n    return x + y\n"
    with ctx.isolated_server() as (base_url, _, _):
        s1, d1, _ = ctx.http_json(
            base_url, "POST", "/api/trace-replay", json_body={"code": code, "language": "python", "inputs": "bad"}
        )
        assert s1 == 400 and "error" in d1
        s2, d2, _ = ctx.http_json(
            base_url, "POST", "/api/trace-replay", json_body={"code": code, "language": "python", "inputs": {"x": 5}}
        )
        assert s2 in (200, 400) and isinstance(d2, dict)


@register_case("T2-F4-03", 2, ("F4",), "HTTP", "Gas-limited loop terminates cleanly as TIMEOUT with bounded trace_steps")
def t2_f4_03(ctx: E2ERunnerContext) -> None:
    # Reserve while loop strictly for gas-limit TIMEOUT test
    code = (
        "def spin(n):\n"
        "    i = 0\n"
        "    while i < 100000:\n"
        "        i = i + 1\n"
        "    return i\n"
    )
    with ctx.isolated_server() as (base_url, _, _):
        t0 = time.monotonic()
        st, data, _ = ctx.http_json(
            base_url, "POST", "/api/trace-replay", json_body={"code": code, "language": "python", "inputs": {"n": 1}}
        )
        dt = time.monotonic() - t0
        assert st == 200 and dt < 5.0
        assert data["outcome"]["status"] == "TIMEOUT"
        assert len(data["trace_steps"]) > 0


@register_case("T2-F4-04", 2, ("F4",), "CLI", "Malformed --inputs JSON on --trace-replay exits non-zero with Vietnamese error")
def t2_f4_04(ctx: E2ERunnerContext) -> None:
    with tempfile.TemporaryDirectory(prefix="hyperion_e2e_badin_") as tmp:
        py_file = Path(tmp) / "f.py"
        py_file.write_text("def f(x):\n    return x + 1\n", encoding="utf-8")
        res = ctx.run_cli(["--trace-replay", str(py_file), "--lang", "python", "--inputs", "{invalid_json"])
        assert res.returncode != 0
        combined = res.stdout + res.stderr
        assert "Traceback (most recent call last)" not in combined
        _assert_has_vietnamese(combined, "CLI invalid --inputs JSON error")


@register_case("T2-F4-05", 2, ("F4",), "HTTP", "Bug-free function produces 0 counterexamples and trace-replay computes exact output")
def t2_f4_05(ctx: E2ERunnerContext) -> None:
    code = "def safe_add(a, b):\n    return a + b\n"
    with ctx.isolated_server() as (base_url, _, _):
        s1, d1, _ = ctx.http_json(base_url, "POST", "/api/analyze-snippet", json_body={"code": code, "language": "python"})
        assert s1 == 200 and d1["functions"][0]["counterexamples"] == []
        s2, d2, _ = ctx.http_json(
            base_url, "POST", "/api/trace-replay", json_body={"code": code, "language": "python", "inputs": {"a": 2, "b": 3}}
        )
        assert s2 == 200
        assert d2["outcome"]["return_value"] == 5
        assert len(d2["trace_steps"]) >= 1 and d2["trace_steps"][0]["block_id"] == 0


# --- F5: Unit Test Generator Boundaries (5 tests) ---

@register_case("T2-F5-01", 2, ("F5",), "HTTP", "POST /api/generate-tests handles empty snippet (400) and Python syntax error cleanly")
def t2_f5_01(ctx: E2ERunnerContext) -> None:
    with ctx.isolated_server() as (base_url, _, _):
        s1, d1, _ = ctx.http_json(
            base_url, "POST", "/api/generate-tests", json_body={"code": "", "language": "python", "framework": "pytest"}
        )
        assert s1 == 400 and "error" in d1
        s2, d2, _ = ctx.http_json(
            base_url, "POST", "/api/generate-tests", json_body={"code": "def x(:", "language": "python", "framework": "pytest"}
        )
        assert s2 in (200, 400)
        assert len(d2.get("parse_errors", [])) >= 1
        assert d2.get("functions", []) == []


@register_case("T2-F5-02", 2, ("F5",), "HTTP", "Zero-parameter function generates valid pytest suite and passes meta-execution")
def t2_f5_02(ctx: E2ERunnerContext) -> None:
    code = "def const_fn():\n    return 42\n"
    ns: Dict[str, Any] = {}
    exec(code, ns)
    with ctx.isolated_server() as (base_url, _, _):
        st, data, _ = ctx.http_json(
            base_url, "POST", "/api/generate-tests", json_body={"code": code, "language": "python", "framework": "pytest"}
        )
        assert st == 200
        pytest_code = data["functions"][0]["pytest"]
        assert "const_fn()" in pytest_code and "42" in pytest_code
        verify_and_exec_pytest(pytest_code, {"const_fn": ns["const_fn"]}, expect_fail=False)


@register_case("T2-F5-03", 2, ("F5",), "HTTP", "Unsupported framework value fails cleanly (400) or defaults safely without 500")
def t2_f5_03(ctx: E2ERunnerContext) -> None:
    with ctx.isolated_server() as (base_url, _, _):
        st, data, _ = ctx.http_json(
            base_url,
            "POST",
            "/api/generate-tests",
            json_body={"code": "def f(x): return x\n", "language": "python", "framework": "mocha_unknown"},
        )
        assert st in (200, 400) and isinstance(data, dict)
        if st == 400:
            assert "error" in data


@register_case("T2-F5-04", 2, ("F5",), "HTTP", "Function with UNSAT dead branch never generates tests asserting impossible return value")
def t2_f5_04(ctx: E2ERunnerContext) -> None:
    code = (
        "def f(x):\n"
        "    if x > 10:\n"
        "        if x < 0:\n"
        "            return 999\n"
        "    return x + 1\n"
    )
    ns: Dict[str, Any] = {}
    exec(code, ns)
    with ctx.isolated_server() as (base_url, _, _):
        st, data, _ = ctx.http_json(
            base_url, "POST", "/api/generate-tests", json_body={"code": code, "language": "python", "framework": "pytest"}
        )
        assert st == 200
        pytest_code = data["functions"][0]["pytest"]
        assert "999" not in pytest_code, f"Dead branch output 999 leaked into generated tests:\n{pytest_code}"
        verify_and_exec_pytest(pytest_code, {"f": ns["f"]}, expect_fail=False)


@register_case("T2-F5-05", 2, ("F5",), "HTTP", "Looping function in /api/generate-tests completes rapidly under gas limit without hang/500")
def t2_f5_05(ctx: E2ERunnerContext) -> None:
    # Reserve while loop strictly for gas-limit graceful completion test
    code = (
        "def sum_n(n):\n"
        "    s = 0\n"
        "    i = 0\n"
        "    while i < n:\n"
        "        s = s + i\n"
        "        i = i + 1\n"
        "    return s\n"
    )
    with ctx.isolated_server() as (base_url, _, _):
        t0 = time.monotonic()
        st, data, _ = ctx.http_json(
            base_url, "POST", "/api/generate-tests", json_body={"code": code, "language": "python", "framework": "pytest"}
        )
        dt = time.monotonic() - t0
        assert st == 200 and dt < 5.0
        assert len(data["functions"]) == 1
        ast.parse(data["functions"][0]["pytest"])


# --- F6: Semantic Equivalence Prover Boundaries (6 tests) ---

@register_case("T2-F6-01", 2, ("F6",), "HTTP", "Parameter arity mismatch reports NON_EQUIVALENT/ERROR in Vietnamese")
def t2_f6_01(ctx: E2ERunnerContext) -> None:
    with ctx.isolated_server() as (base_url, _, _):
        st, data, _ = ctx.http_json(
            base_url,
            "POST",
            "/api/equivalence",
            json_body={"old_code": "def f(x): return x + 1\n", "new_code": "def f(x, y): return x + y\n", "language": "python"},
        )
        assert st in (200, 400)
        if st == 200:
            assert data["equivalent"] is False
            assert data["status"] in ("NON_EQUIVALENT", "ERROR")
            _assert_has_vietnamese(data["summary"], "arity mismatch summary")


@register_case("T2-F6-02", 2, ("F6",), "HTTP", "Empty old_code or new_code fails gracefully with error/ERROR status")
def t2_f6_02(ctx: E2ERunnerContext) -> None:
    with ctx.isolated_server() as (base_url, _, _):
        for payload in (
            {"old_code": "", "new_code": "def f(x): return x\n", "language": "python"},
            {"old_code": "def f(x): return x\n", "new_code": "   \n", "language": "python"},
        ):
            st, data, _ = ctx.http_json(base_url, "POST", "/api/equivalence", json_body=payload)
            assert st in (200, 400)
            if st == 200:
                assert data["equivalent"] is False and data["status"] == "ERROR"
            else:
                assert "error" in data


@register_case("T2-F6-03", 2, ("F6",), "HTTP", "Syntax error in new_code returns ERROR with non-empty parse_errors in Python and safe error in TS")
def t2_f6_03(ctx: E2ERunnerContext) -> None:
    with ctx.isolated_server() as (base_url, _, _):
        st_py, d_py, _ = ctx.http_json(
            base_url,
            "POST",
            "/api/equivalence",
            json_body={"old_code": "def f(x): return x\n", "new_code": "def f(x return\n", "language": "python"},
        )
        assert st_py in (200, 400)
        assert d_py.get("equivalent") is False
        assert d_py.get("status") == "ERROR"
        assert len(d_py.get("parse_errors", [])) >= 1

        st_ts, d_ts, _ = ctx.http_json(
            base_url,
            "POST",
            "/api/equivalence",
            json_body={
                "old_code": "export function f(x: number): number { return x; }",
                "new_code": "function { ???",
                "language": "typescript",
            },
        )
        assert st_ts in (200, 400)
        assert d_ts.get("equivalent") is False
        assert d_ts.get("status") == "ERROR"


@register_case("T2-F6-04", 2, ("F6",), "HTTP", "Zero-parameter functions prove EQUIVALENT when equal and NON_EQUIVALENT when distinct")
def t2_f6_04(ctx: E2ERunnerContext) -> None:
    with ctx.isolated_server() as (base_url, _, _):
        s1, d1, _ = ctx.http_json(
            base_url,
            "POST",
            "/api/equivalence",
            json_body={"old_code": "def a(): return 7\n", "new_code": "def b(): return 7\n", "language": "python"},
        )
        assert s1 == 200 and d1["equivalent"] is True and d1["status"] == "EQUIVALENT"

        s2, d2, _ = ctx.http_json(
            base_url,
            "POST",
            "/api/equivalence",
            json_body={"old_code": "def a(): return 7\n", "new_code": "def b(): return 8\n", "language": "python"},
        )
        assert s2 == 200 and d2["equivalent"] is False and d2["status"] == "NON_EQUIVALENT"
        assert d2["counterexample"]["old_output"]["return_value"] == 7
        assert d2["counterexample"]["new_output"]["return_value"] == 8


@register_case("T2-F6-05", 2, ("F6",), "HTTP", "Positional parameter alignment proves equivalence despite renamed parameters")
def t2_f6_05(ctx: E2ERunnerContext) -> None:
    with ctx.isolated_server() as (base_url, _, _):
        st, data, _ = ctx.http_json(
            base_url,
            "POST",
            "/api/equivalence",
            json_body={"old_code": "def f1(x, y): return x - y\n", "new_code": "def f2(a, b): return a - b\n", "language": "python"},
        )
        assert st == 200
        assert data["equivalent"] is True
        assert data["status"] == "EQUIVALENT"


@register_case("T2-F6-06", 2, ("F6",), "HTTP", "Equivalence Prover handles x*2 == x+x (EQUIVALENT) and x*x != x*2 (NON_EQUIVALENT)")
def t2_f6_06(ctx: E2ERunnerContext) -> None:
    with ctx.isolated_server() as (base_url, _, _):
        s1, d1, _ = ctx.http_json(
            base_url,
            "POST",
            "/api/equivalence",
            json_body={"old_code": "def p1(x): return x * 2\n", "new_code": "def p2(x): return x + x\n", "language": "python"},
        )
        assert s1 == 200 and d1["equivalent"] is True and d1["status"] == "EQUIVALENT"

        s2, d2, _ = ctx.http_json(
            base_url,
            "POST",
            "/api/equivalence",
            json_body={"old_code": "def q1(x): return x * x\n", "new_code": "def q2(x): return x * 2\n", "language": "python"},
        )
        assert s2 == 200 and d2["equivalent"] is False and d2["status"] == "NON_EQUIVALENT"
        cx = d2["counterexample"]
        assert cx["old_output"] != cx["new_output"]


# --- F7: Mutant Killer Boundaries (5 tests) ---

@register_case("T2-F7-01", 2, ("F7",), "HTTP", "Zero-mutant identity function returns 0/0 cleanly without ZeroDivisionError")
def t2_f7_01(ctx: E2ERunnerContext) -> None:
    with ctx.isolated_server() as (base_url, _, _):
        st, data, _ = ctx.http_json(
            base_url, "POST", "/api/kill-mutants", json_body={"code": "def id_fn(x):\n    return x\n", "language": "python"}
        )
        assert st == 200
        assert data["mutation"]["total"] == 0
        assert data["initial_survived"] == 0
        assert data["newly_killed"] == 0
        assert data["remaining_survived"] == 0
        assert data["kill_witnesses"] == []


@register_case("T2-F7-02", 2, ("F7",), "HTTP", "Equivalent mutant edge case never emits false witness where orig_output == mut_output")
def t2_f7_02(ctx: E2ERunnerContext) -> None:
    code = "def equiv_mut(x):\n    y = x * 1\n    return y + 0\n"
    with ctx.isolated_server() as (base_url, _, _):
        st, data, _ = ctx.http_json(
            base_url, "POST", "/api/kill-mutants", json_body={"code": code, "language": "python"}
        )
        assert st == 200
        for w in data["kill_witnesses"]:
            assert w["orig_output"] != w["mut_output"], f"False kill witness emitted: {w}"
        assert data["remaining_survived"] >= 0


@register_case("T2-F7-03", 2, ("F7",), "HTTP", "POST /api/kill-mutants with non-existent fn_id returns 404")
def t2_f7_03(ctx: E2ERunnerContext) -> None:
    with ctx.isolated_server() as (base_url, _, _):
        st, data, _ = ctx.http_json(base_url, "POST", "/api/kill-mutants", json_body={"fn_id": 999999})
        assert st == 404 and "error" in data


@register_case("T2-F7-04", 2, ("F7",), "HTTP", "POST /api/kill-mutants rejects empty snippet (400) and handles syntax errors safely")
def t2_f7_04(ctx: E2ERunnerContext) -> None:
    with ctx.isolated_server() as (base_url, _, _):
        s1, d1, _ = ctx.http_json(base_url, "POST", "/api/kill-mutants", json_body={"code": "", "language": "python"})
        assert s1 == 400 and "error" in d1

        s2, d2, _ = ctx.http_json(base_url, "POST", "/api/kill-mutants", json_body={"code": "def bad(:", "language": "python"})
        assert s2 in (200, 400) and isinstance(d2, dict)
        assert ("error" in d2 or len(d2.get("parse_errors", [])) >= 1 or d2.get("functions", []) == [])

        s3, d3, _ = ctx.http_json(
            base_url, "POST", "/api/kill-mutants", json_body={"code": "function { ???", "language": "typescript"}
        )
        assert s3 in (200, 400) and isinstance(d3, dict)
        assert ("error" in d3 or d3.get("functions", []) == [])


@register_case("T2-F7-05", 2, ("F7",), "HTTP", "100%-killed suite leaves 0 initial_survived, 0 newly_killed, and 100.0 score")
def t2_f7_05(ctx: E2ERunnerContext) -> None:
    code = "def add1(x):\n    return x + 1\n"
    with ctx.isolated_server() as (base_url, _, _):
        st, data, _ = ctx.http_json(
            base_url,
            "POST",
            "/api/kill-mutants",
            json_body={"code": code, "language": "python", "existing_vectors": [{"x": 0}, {"x": 5}]},
        )
        assert st == 200
        assert data["initial_survived"] == 0
        assert data["newly_killed"] == 0
        assert data["new_score_pct"] == 100.0
        assert data["kill_witnesses"] == []


# --- F8: Localization Boundaries (5 tests) ---

@register_case("T2-F8-01", 2, ("F8",), "CLI", "Piped CLI stdout decodes strictly as UTF-8 with zero mojibake")
def t2_f8_01(ctx: E2ERunnerContext) -> None:
    with tempfile.TemporaryDirectory(prefix="hyperion_e2e_utf8_") as tmp:
        f_old = Path(tmp) / "a.py"
        f_new = Path(tmp) / "b.py"
        f_old.write_text("def f(x):\n    if x >= 10:\n        return 1\n    return 0\n", encoding="utf-8")
        f_new.write_text("def f(x):\n    if x > 10:\n        return 1\n    return 0\n", encoding="utf-8")
        res = ctx.run_cli(["--prove-equiv", str(f_old), str(f_new), "--lang", "python"])
        assert res.returncode == 0
        decoded = res.raw_stdout.decode("utf-8", errors="strict")
        assert "???" not in decoded
        _assert_has_vietnamese(decoded, "CLI piped UTF-8 output")


@register_case("T2-F8-02", 2, ("F8",), "HTTP", "HTTP 400/404 JSON error responses emit localized Vietnamese messages")
def t2_f8_02(ctx: E2ERunnerContext) -> None:
    with ctx.isolated_server() as (base_url, _, _):
        cases = [
            ("GET", "/api/function/999999", None, 404),
            ("POST", "/api/analyze-snippet", {"code": "", "language": "python"}, 400),
            ("POST", "/api/unknown-route", {}, 404),
        ]
        for method, path, body, expected_code in cases:
            st, data, _ = ctx.http_json(base_url, method, path, json_body=body)
            assert st == expected_code, f"Expected {expected_code} for {method} {path}, got {st}"
            assert isinstance(data, dict) and "error" in data
            validate_vietnamese_runtime_text(data["error"], f"HTTP {expected_code} {path} error")


@register_case("T2-F8-03", 2, ("F8",), "STATIC", "web/src/app.ts and web/dist/app.js share consistent DOM IDs and Vietnamese UI strings")
def t2_f8_03(ctx: E2ERunnerContext) -> None:
    app_ts = (WEB_DIR / "src" / "app.ts").read_text(encoding="utf-8")
    app_js = (WEB_DIR / "dist" / "app.js").read_text(encoding="utf-8")
    validate_vietnamese_js(app_ts, "web/src/app.ts")
    validate_vietnamese_js(app_js, "web/dist/app.js")
    for preserved_id in ("cfgCanvas", "srcEditor", "ssaViewer", "mutationTable", "leaderboardTable"):
        assert preserved_id in app_ts and preserved_id in app_js, f"Missing {preserved_id} in TS/JS sync"
    for cls_tok in ("SURVIVED", "KILLED", "TIMEOUT", "CRITICAL", "HIGH"):
        assert cls_tok in app_js, f"Preserved status/severity token {cls_tok} missing in app.js"


@register_case("T2-F8-04", 2, ("F8",), "HTTP", "UTF-8 Vietnamese comments and identifiers analyze and generate tests cleanly")
def t2_f8_04(ctx: E2ERunnerContext) -> None:
    code = (
        "def tinh_tong(so_a, so_b):\n"
        "    # kiểm tra chia cho 0\n"
        "    if so_b == 0:\n"
        "        return 10 // so_b\n"
        "    return so_a + so_b\n"
    )
    with ctx.isolated_server() as (base_url, _, _):
        st, data, _ = ctx.http_json(base_url, "POST", "/api/analyze-snippet", json_body={"code": code, "language": "python"})
        assert st == 200
        fn = data["functions"][0]
        assert fn["name"] == "tinh_tong"
        assert "kiểm tra chia cho 0" in fn["source_code"]
        ast.parse(fn["generated_tests"]["pytest"])


@register_case("T2-F8-05", 2, ("F8",), "HTTP", "Internal finding/counterexample enum codes stay intact while descriptions are Vietnamese")
def t2_f8_05(ctx: E2ERunnerContext) -> None:
    with ctx.isolated_server() as (base_url, _, _):
        st, data, _ = ctx.http_json(base_url, "POST", "/api/analyze-snippet", json_body={"code": SNIPPET_A_PY, "language": "python"})
        assert st == 200
        fn = data["functions"][0]
        cx_kinds = {c["kind"] for c in fn["counterexamples"]}
        assert {"DIV_BY_ZERO", "BUFFER_OOB", "ASSERTION_VIOLATION", "TAINT_REACHABLE"}.issubset(cx_kinds)
        for c in fn["counterexamples"]:
            assert c["kind"] in INTERNAL_ENUM_TOKENS
            assert c["severity"] in ("CRITICAL", "HIGH", "MEDIUM", "LOW", "INFO")
            validate_vietnamese_runtime_text(c["description"], f"cx[{c['kind']}].description")


# ===========================================================================
# TIER 3 — Pairwise & Multi-Feature Combination Tests (10 tests: T3_01..T3_10)
# ===========================================================================

@register_case("T3_01", 3, ("F3", "F4", "F8"), "HTTP", "Dead-branch UNSAT + trace replay never enters dead block (Python)")
def t3_01(ctx: E2ERunnerContext) -> None:
    code = (
        "def route_packet(port, len_hdr):\n"
        "    rules = [1, 2, 3, 4]\n"
        "    acc = 0\n"
        "    if port > 20 and port < 5:\n"
        "        return -999\n"
        "    if len_hdr == 8:\n"
        "        v = rules[len_hdr]\n"
        "        acc = acc + v\n"
        "    return acc + (100 // (port - 3))\n"
    )
    with ctx.isolated_server() as (base_url, _, _):
        st, data, _ = ctx.http_json(base_url, "POST", "/api/analyze-snippet", json_body={"code": code, "language": "python"})
        assert st == 200
        fn = data["functions"][0]
        assert len(fn["dead_branches"]) >= 1
        dead_node_ids = {n["id"] for n in fn["cfg_graph"]["nodes"] if n.get("is_dead")}
        assert dead_node_ids, "Expected at least one is_dead node"
        for n in fn["cfg_graph"]["nodes"]:
            if n["id"] in dead_node_ids:
                validate_vietnamese_runtime_text(n["dead_reason"], "cfg_graph.node.dead_reason")

        cx = next((c for c in fn["counterexamples"] if c["kind"] in ("BUFFER_OOB", "DIV_BY_ZERO")), None)
        assert cx is not None and len(cx["trace_steps"]) >= 1
        assert cx["trace_steps"][0]["block_id"] == 0

        rs, rdata, _ = ctx.http_json(
            base_url, "POST", "/api/trace-replay", json_body={"code": code, "language": "python", "inputs": cx["inputs"]}
        )
        assert rs == 200
        visited = {s["block_id"] for s in rdata["trace_steps"]}
        assert not (visited & dead_node_ids), f"Trace replay entered dead block: {visited & dead_node_ids}"


@register_case("T3_02", 3, ("F3", "F4"), "HTTP", "TS UNSAT dead branch vs live early return + ASSERTION_VIOLATION trace_steps")
def t3_02(ctx: E2ERunnerContext) -> None:
    code = (
        "export function checkFlags(flags: number, x: number): number {\n"
        "    if (flags > 15 && flags < 2) { return -1; }\n"
        "    assert(x != 7, 'x_not_7');\n"
        "    if (x > 0) { return 1; } else { return 2; }\n"
        "}\n"
    )
    with ctx.isolated_server() as (base_url, _, _):
        st, data, _ = ctx.http_json(base_url, "POST", "/api/analyze-snippet", json_body={"code": code, "language": "typescript"})
        assert st == 200
        fn = data["functions"][0]
        assert len(fn["dead_branches"]) == 1, f"Expected exactly 1 UNSAT dead branch (no synthetic join), got {fn['dead_branches']}"
        acx = next((c for c in fn["counterexamples"] if c["kind"] == "ASSERTION_VIOLATION"), None)
        assert acx is not None and len(acx["trace_steps"]) >= 1


@register_case("T3_03", 3, ("F5", "F7", "F2"), "HTTP", "Generate tests -> kill surviving mutant -> meta-verify appended pytest kills hand-mutated variant")
def t3_03(ctx: E2ERunnerContext) -> None:
    ns_orig: Dict[str, Any] = {}
    exec(GATE_THRESHOLD_PY, ns_orig)
    orig_fn = ns_orig["gate_threshold"]

    mutated_py = "def gate_threshold(x):\n    if x >= 10:\n        return 100\n    return 0\n"
    ns_mut: Dict[str, Any] = {}
    exec(mutated_py, ns_mut)
    mut_fn = ns_mut["gate_threshold"]

    seed_vectors = [{"x": 0}, {"x": 11}]
    with ctx.isolated_server() as (base_url, _, _):
        s1, d1, _ = ctx.http_json(
            base_url,
            "POST",
            "/api/generate-tests",
            json_body={"code": GATE_THRESHOLD_PY, "language": "python", "framework": "pytest", "extra_vectors": seed_vectors},
        )
        assert s1 == 200
        init_pytest = d1["functions"][0]["pytest"]
        init_cnt = len([n for n in ast.parse(init_pytest).body if isinstance(n, ast.FunctionDef) and n.name.startswith("test_")])

        s2, d2, _ = ctx.http_json(
            base_url,
            "POST",
            "/api/kill-mutants",
            json_body={"code": GATE_THRESHOLD_PY, "language": "python", "existing_vectors": seed_vectors},
        )
        assert s2 == 200
        assert d2["initial_survived"] >= 1
        assert d2["newly_killed"] >= 1
        init_total = d2["mutation"]["total"]
        init_score = round((init_total - d2["initial_survived"]) / init_total * 100.0, 2) if init_total else 100.0
        assert d2["new_score_pct"] > init_score
        for w in d2["kill_witnesses"]:
            assert w["orig_output"] != w["mut_output"]

        appended_pytest = d2["appended_tests"]["pytest"]
        new_cnt = verify_and_exec_pytest(appended_pytest, {"gate_threshold": orig_fn}, expect_fail=False)
        assert new_cnt > init_cnt, f"Expected appended pytest count ({new_cnt}) > initial ({init_cnt})"
        verify_and_exec_pytest(appended_pytest, {"gate_threshold": mut_fn}, expect_fail=True)


@register_case("T3_04", 3, ("F5", "F7"), "HTTP", "TypeScript surviving mutant killer appends valid vitest and jest witness tests")
def t3_04(ctx: E2ERunnerContext) -> None:
    code = (
        "export function checkQuota(tier: number, used: number): number {\n"
        "    if (tier > 5) {\n"
        "        return 100 - used;\n"
        "    }\n"
        "    return 20 - used;\n"
        "}\n"
    )
    with ctx.isolated_server() as (base_url, _, _):
        st, data, _ = ctx.http_json(
            base_url,
            "POST",
            "/api/kill-mutants",
            json_body={"code": code, "language": "typescript", "existing_vectors": [{"tier": 1, "used": 2}, {"tier": 10, "used": 2}]},
        )
        assert st == 200
        assert data["newly_killed"] >= 1
        assert len(data["kill_witnesses"]) >= 1
        verify_js_test_suite(data["appended_tests"]["vitest"], "vitest", expected_fn_name="checkQuota")
        verify_js_test_suite(data["appended_tests"]["jest"], "jest", expected_fn_name="checkQuota")


@register_case("T3_05", 3, ("F5", "F6", "F8"), "HTTP", "Equivalence diverging counterexample fed into generate-tests catches buggy refactor")
def t3_05(ctx: E2ERunnerContext) -> None:
    old_code = "def discount_v1(price, level):\n    if level > 3:\n        return price - 10\n    return price - 2\n"
    new_buggy = "def discount_v2(price, level):\n    if level >= 3:\n        return price - 10\n    return price - 2\n"
    ns_old: Dict[str, Any] = {}
    ns_new: Dict[str, Any] = {}
    exec(old_code, ns_old)
    exec(new_buggy, ns_new)

    with ctx.isolated_server() as (base_url, _, _):
        s1, eq, _ = ctx.http_json(
            base_url, "POST", "/api/equivalence", json_body={"old_code": old_code, "new_code": new_buggy, "language": "python"}
        )
        assert s1 == 200
        assert eq["equivalent"] is False and eq["status"] == "NON_EQUIVALENT"
        validate_vietnamese_runtime_text(eq["summary"], "T3_05 equivalence summary")
        cx_inputs = eq["counterexample"]["inputs"]

        s2, gt, _ = ctx.http_json(
            base_url,
            "POST",
            "/api/generate-tests",
            json_body={"code": old_code, "language": "python", "framework": "pytest", "extra_vectors": [cx_inputs]},
        )
        assert s2 == 200
        pytest_code = gt["functions"][0]["pytest"]
        verify_and_exec_pytest(pytest_code, {"discount_v1": ns_old["discount_v1"]}, expect_fail=False)
        verify_and_exec_pytest(pytest_code, {"discount_v1": ns_new["discount_v2"]}, expect_fail=True)


@register_case("T3_06", 3, ("F3", "F5", "F8"), "HTTP", "Dead-branch UNSAT excluded from generated pytest while reachable branches pass")
def t3_06(ctx: E2ERunnerContext) -> None:
    code = (
        "def dispatch_mode(mode):\n"
        "    if mode > 50:\n"
        "        if mode < 10:\n"
        "            return -777\n"
        "    if mode >= 0:\n"
        "        return mode + 1\n"
        "    return -mode\n"
    )
    ns: Dict[str, Any] = {}
    exec(code, ns)
    with ctx.isolated_server() as (base_url, _, _):
        st, data, _ = ctx.http_json(base_url, "POST", "/api/analyze-snippet", json_body={"code": code, "language": "python"})
        assert st == 200
        fn = data["functions"][0]
        assert len(fn["dead_branches"]) >= 1
        validate_vietnamese_runtime_text(fn["dead_branches"][0]["reason"], "T3_06 dead_branches.reason")
        pytest_code = fn["generated_tests"]["pytest"]
        assert "-777" not in pytest_code
        verify_and_exec_pytest(pytest_code, {"dispatch_mode": ns["dispatch_mode"]}, expect_fail=False)


@register_case("T3_07", 3, ("F1", "F2", "F8"), "CLI", "CLI --benchmark-cli --scale 2 --json-out satisfies 64-bit HANDLE, stdlib-only, and Vietnamese output")
def t3_07(ctx: E2ERunnerContext) -> None:
    t1_f1_01(ctx)
    t1_f2_01(ctx)
    res = ctx.run_cli(["--benchmark-cli", "--scale", "2", "--min-free-ram-pct", "5.0", "--json-out"], timeout=90.0)
    assert res.returncode == 0, f"Benchmark CLI failed: {res.stderr}\n{res.stdout}"
    validate_vietnamese_runtime_text(res.stdout, "benchmark CLI stdout")
    payload = extract_json_from_cli_stdout(res.stdout)
    assert payload["totals"]["functions"] >= 10
    assert payload["scores"]["composite_score"] > 0


@register_case("T3_08", 3, ("F3", "F4", "F6", "F8"), "CLI", "New CLI subcommands (--dead-branches, --trace-replay, --prove-equiv, --gen-tests, --kill-mutants) match HTTP semantics")
def t3_08(ctx: E2ERunnerContext) -> None:
    with tempfile.TemporaryDirectory(prefix="hyperion_e2e_cli_all_") as tmp:
        p_pkt = Path(tmp) / "pkt.py"
        p_old = Path(tmp) / "old.py"
        p_new = Path(tmp) / "new.py"
        p_gate = Path(tmp) / "gate.py"
        p_pkt.write_text(SNIPPET_A_PY, encoding="utf-8")
        p_old.write_text(CALC_ACCESS_FEE_OLD_PY, encoding="utf-8")
        p_new.write_text(CALC_ACCESS_FEE_NEW_PY, encoding="utf-8")
        p_gate.write_text(GATE_THRESHOLD_PY, encoding="utf-8")

        r1 = ctx.run_cli(["--dead-branches", str(p_pkt), "--lang", "python", "--json-out"])
        r2 = ctx.run_cli(["--trace-replay", str(p_pkt), "--lang", "python", "--inputs", '{"k": 5, "user_input": 0}', "--json-out"])
        r3 = ctx.run_cli(["--prove-equiv", str(p_old), str(p_new), "--lang", "python", "--json-out"])
        r4 = ctx.run_cli(["--gen-tests", str(p_gate), "--lang", "python", "--framework", "pytest", "--json-out"])
        r5 = ctx.run_cli(["--kill-mutants", str(p_gate), "--lang", "python", "--json-out"])
        for label, r in (("dead-branches", r1), ("trace-replay", r2), ("prove-equiv", r3), ("gen-tests", r4), ("kill-mutants", r5)):
            assert r.returncode == 0, f"CLI {label} failed: {r.stderr}\n{r.stdout}"

        j1 = extract_json_from_cli_stdout(r1.stdout)
        fns1 = j1.get("functions", [j1] if "dead_branches" in j1 else [])
        assert len(fns1) >= 1 and len(fns1[0]["dead_branches"]) >= 1
        assert extract_json_from_cli_stdout(r2.stdout)["trace_steps"][0]["block_id"] == 0
        assert extract_json_from_cli_stdout(r3.stdout)["equivalent"] is True
        j4 = extract_json_from_cli_stdout(r4.stdout)
        fns4 = j4.get("functions", [j4] if "pytest" in j4 else [])
        ast.parse(fns4[0]["pytest"])
        assert len(extract_json_from_cli_stdout(r5.stdout)["kill_witnesses"]) >= 1


@register_case("T3_09", 3, ("F1", "F2", "F8"), "HTTP", "Emergency stop recovers cleanly and allows immediate snippet analysis")
def t3_09(ctx: E2ERunnerContext) -> None:
    with ctx.isolated_server() as (base_url, orch, _):
        s1, d1, _ = ctx.http_json(
            base_url,
            "POST",
            "/api/run",
            json_body={
                "mode": "stress",
                "corpus_source": "procedural",
                "intensity": "heavy",
                "scale_factor": 4,
                "safety": {"max_workers": 2, "min_free_system_ram_pct": 5.0, "max_duration_sec": 30},
            },
        )
        assert s1 == 200 and d1["ok"] is True
        t0 = time.perf_counter()
        stop = orch.emergency_stop("Dừng khẩn cấp kiểm thử phục hồi")
        assert stop["stopped"] is True and (time.perf_counter() - t0) < 0.050

        st_code, st_data, _ = ctx.http_json(base_url, "GET", "/api/status")
        assert st_code == 200 and st_data["state"] in ("STOPPED", "COMPLETED")
        if st_data["stop_reason"]:
            validate_vietnamese_runtime_text(st_data["stop_reason"], "stop_reason")

        s2, a2, _ = ctx.http_json(
            base_url, "POST", "/api/analyze-snippet", json_body={"code": GATE_THRESHOLD_PY, "language": "python"}
        )
        assert s2 == 200 and len(a2["functions"]) == 1


@register_case("T3_10", 3, ("F5", "F6", "F2"), "HTTP", "Generated pytest from equivalent Hàm Cũ passes 100% on both Hàm Cũ and Hàm Mới")
def t3_10(ctx: E2ERunnerContext) -> None:
    ns_old: Dict[str, Any] = {}
    ns_new: Dict[str, Any] = {}
    exec(CALC_ACCESS_FEE_OLD_PY, ns_old)
    exec(CALC_ACCESS_FEE_NEW_PY, ns_new)

    with ctx.isolated_server() as (base_url, _, _):
        s1, eq, _ = ctx.http_json(
            base_url,
            "POST",
            "/api/equivalence",
            json_body={"old_code": CALC_ACCESS_FEE_OLD_PY, "new_code": CALC_ACCESS_FEE_NEW_PY, "language": "python"},
        )
        assert s1 == 200 and eq["equivalent"] is True and eq["status"] == "EQUIVALENT"

        s2, gt, _ = ctx.http_json(
            base_url,
            "POST",
            "/api/generate-tests",
            json_body={"code": CALC_ACCESS_FEE_OLD_PY, "language": "python", "framework": "pytest"},
        )
        assert s2 == 200
        pytest_code = gt["functions"][0]["pytest"]
        verify_and_exec_pytest(pytest_code, {"calc_access_fee": ns_old["calc_access_fee"]}, expect_fail=False)
        verify_and_exec_pytest(pytest_code, {"calc_access_fee": ns_new["calc_access_fee_new"]}, expect_fail=False)


# ===========================================================================
# TIER 4 — Realistic End-to-End Application Scenarios (5 scenarios: T4_S1..T4_S5)
# ===========================================================================

@register_case("T4_S1", 4, ("F2", "F5", "F6", "F8"), "HTTP", "Scenario 1: Refactor calc_access_fee (Hàm Cũ vs Hàm Mới & buggy) + pytest/vitest/jest meta-execution")
def t4_s1(ctx: E2ERunnerContext) -> None:
    ns: Dict[str, Any] = {}
    exec(CALC_ACCESS_FEE_OLD_PY, ns)
    exec(CALC_ACCESS_FEE_NEW_PY, ns)
    exec(CALC_ACCESS_FEE_BUGGY_PY, ns)
    fn_old = ns["calc_access_fee"]
    fn_new = ns["calc_access_fee_new"]
    fn_bug = ns["calc_access_fee_buggy"]

    with ctx.isolated_server() as (base_url, _, _):
        # 1. Prove old == new
        s1, eq_ok, _ = ctx.http_json(
            base_url,
            "POST",
            "/api/equivalence",
            json_body={"old_code": CALC_ACCESS_FEE_OLD_PY, "new_code": CALC_ACCESS_FEE_NEW_PY, "language": "python"},
        )
        assert s1 == 200 and eq_ok["equivalent"] is True and eq_ok["status"] == "EQUIVALENT"
        validate_vietnamese_runtime_text(eq_ok["summary"], "S1 equivalence OK summary")

        # 2. Catch divergence old != buggy
        s2, eq_bad, _ = ctx.http_json(
            base_url,
            "POST",
            "/api/equivalence",
            json_body={"old_code": CALC_ACCESS_FEE_OLD_PY, "new_code": CALC_ACCESS_FEE_BUGGY_PY, "language": "python"},
        )
        assert s2 == 200 and eq_bad["equivalent"] is False and eq_bad["status"] == "NON_EQUIVALENT"
        cx_inputs = eq_bad["counterexample"]["inputs"]
        assert fn_old(**cx_inputs) != fn_bug(**cx_inputs), f"Counterexample {cx_inputs} did not diverge in Python!"

        # 3. Generate pytest with counterexample and meta-execute against all 3 variants
        s3, gt_py, _ = ctx.http_json(
            base_url,
            "POST",
            "/api/generate-tests",
            json_body={
                "code": CALC_ACCESS_FEE_OLD_PY,
                "language": "python",
                "framework": "pytest",
                "extra_vectors": [cx_inputs],
            },
        )
        assert s3 == 200
        pytest_code = gt_py["functions"][0]["pytest"]
        verify_and_exec_pytest(pytest_code, {"calc_access_fee": fn_old}, expect_fail=False, min_tests=3)
        verify_and_exec_pytest(pytest_code, {"calc_access_fee": fn_new}, expect_fail=False, min_tests=3)
        verify_and_exec_pytest(pytest_code, {"calc_access_fee": fn_bug}, expect_fail=True, min_tests=3)

        # 4. Generate TS vitest & jest
        s4, gt_ts, _ = ctx.http_json(
            base_url,
            "POST",
            "/api/generate-tests",
            json_body={"code": CALC_ACCESS_FEE_TS, "language": "typescript", "framework": "vitest"},
        )
        assert s4 == 200
        verify_js_test_suite(gt_ts["functions"][0]["vitest"], "vitest", expected_fn_name="calcAccessFee")
        verify_js_test_suite(gt_ts["functions"][0]["jest"], "jest", expected_fn_name="calcAccessFee")


@register_case("T4_S2", 4, ("F3", "F4", "F8"), "HTTP+CLI", "Scenario 2: filter_packet_gateway UNSAT dead branches + multi-bug trace replay via HTTP & CLI")
def t4_s2(ctx: E2ERunnerContext) -> None:
    with ctx.isolated_server() as (base_url, _, _):
        st, data, _ = ctx.http_json(
            base_url, "POST", "/api/analyze-snippet", json_body={"code": FILTER_PACKET_GATEWAY_PY, "language": "python"}
        )
        assert st == 200
        fn = data["functions"][0]
        assert len(fn["dead_branches"]) >= 1
        for db in fn["dead_branches"]:
            validate_vietnamese_runtime_text(db["reason"], "S2 dead_branches.reason")
        dead_nodes = {n["id"] for n in fn["cfg_graph"]["nodes"] if n.get("is_dead")}
        assert dead_nodes and any(e.get("is_dead") for e in fn["cfg_graph"]["edges"])

        cx_kinds = {c["kind"] for c in fn["counterexamples"]}
        assert {"DIV_BY_ZERO", "BUFFER_OOB", "TAINT_REACHABLE"}.issubset(cx_kinds), f"Missing expected bugs: {cx_kinds}"
        target_cx = next(c for c in fn["counterexamples"] if c["kind"] == "DIV_BY_ZERO")
        assert len(target_cx["trace_steps"]) >= 2

        rs, rdata, _ = ctx.http_json(
            base_url,
            "POST",
            "/api/trace-replay",
            json_body={"code": FILTER_PACKET_GATEWAY_PY, "language": "python", "inputs": target_cx["inputs"]},
        )
        assert rs == 200
        rsteps = rdata["trace_steps"]
        assert rsteps[0]["block_id"] == 0
        assert not ({s["block_id"] for s in rsteps} & dead_nodes)

    with tempfile.TemporaryDirectory(prefix="hyperion_e2e_s2_") as tmp:
        py_file = Path(tmp) / "gateway.py"
        py_file.write_text(FILTER_PACKET_GATEWAY_PY, encoding="utf-8")
        c_db = ctx.run_cli(["--dead-branches", str(py_file), "--lang", "python"])
        c_tr = ctx.run_cli(["--trace-replay", str(py_file), "--lang", "python", "--inputs", json.dumps(target_cx["inputs"])])
        assert c_db.returncode == 0 and c_tr.returncode == 0
        validate_vietnamese_runtime_text(c_db.stdout, "S2 CLI --dead-branches")
        validate_vietnamese_runtime_text(c_tr.stdout, "S2 CLI --trace-replay")
        assert "B0" in c_tr.stdout


@register_case("T4_S3", 4, ("F5", "F7", "F8"), "HTTP", "Scenario 3: validate_risk_threshold surviving mutants killed via SMT and appended tests verified in Python")
def t4_s3(ctx: E2ERunnerContext) -> None:
    ns_orig: Dict[str, Any] = {}
    exec(VALIDATE_RISK_THRESHOLD_PY, ns_orig)
    orig_fn = ns_orig["validate_risk_threshold"]

    mut_py = VALIDATE_RISK_THRESHOLD_PY.replace("if level > 5:", "if level >= 5:")
    ns_mut: Dict[str, Any] = {}
    exec(mut_py, ns_mut)
    mut_fn = ns_mut["validate_risk_threshold"]

    seed = [{"level": 10, "delta": 2, "cap": 30}, {"level": 1, "delta": 2, "cap": 30}]
    with ctx.isolated_server() as (base_url, _, _):
        s1, g1, _ = ctx.http_json(
            base_url,
            "POST",
            "/api/generate-tests",
            json_body={"code": VALIDATE_RISK_THRESHOLD_PY, "language": "python", "framework": "pytest", "extra_vectors": seed},
        )
        assert s1 == 200
        init_pytest = g1["functions"][0]["pytest"]
        init_cnt = len([n for n in ast.parse(init_pytest).body if isinstance(n, ast.FunctionDef) and n.name.startswith("test_")])

        s2, km, _ = ctx.http_json(
            base_url,
            "POST",
            "/api/kill-mutants",
            json_body={"code": VALIDATE_RISK_THRESHOLD_PY, "language": "python", "existing_vectors": seed},
        )
        assert s2 == 200
        assert km["initial_survived"] >= 1
        assert km["newly_killed"] >= 1
        total_m = km["mutation"]["total"]
        init_score = round((total_m - km["initial_survived"]) / total_m * 100.0, 2) if total_m else 100.0
        assert km["new_score_pct"] > init_score
        for w in km["kill_witnesses"]:
            assert w["orig_output"] != w["mut_output"]

        appended_pytest = km["appended_tests"]["pytest"]
        new_cnt = verify_and_exec_pytest(appended_pytest, {"validate_risk_threshold": orig_fn}, expect_fail=False)
        assert new_cnt > init_cnt
        verify_and_exec_pytest(appended_pytest, {"validate_risk_threshold": mut_fn}, expect_fail=True)


@register_case("T4_S4", 4, ("F1", "F2", "F8"), "CLI", "Scenario 4: python main.py --benchmark-cli --scale 2 with 64-bit HANDLE, RAM guardrails & Vietnamese output")
def t4_s4(ctx: E2ERunnerContext) -> None:
    t1_f1_01(ctx)
    assert SafetyConfig().min_free_system_ram_pct == 10.0
    t1_f2_01(ctx)

    res = ctx.run_cli(["--benchmark-cli", "--scale", "2", "--json-out"], timeout=90.0)
    assert res.returncode == 0, f"--benchmark-cli --scale 2 failed: {res.stderr}\n{res.stdout}"
    validate_vietnamese_runtime_text(res.stdout, "Scenario 4 --benchmark-cli --scale 2 stdout")
    payload = extract_json_from_cli_stdout(res.stdout)
    assert payload["status"] == "COMPLETED"
    assert payload["totals"]["functions"] >= 10
    assert payload["totals"]["smt_queries"] > 0
    assert payload["totals"]["mutants_evaluated"] > 0
    assert payload["scores"]["composite_score"] > 0


@register_case("T4_S5", 4, ("F2", "F3", "F4", "F5", "F6", "F7", "F8"), "STATIC+HTTP", "Scenario 5: Full Web Studio UI sync, Vietnamese localization, API wiring & headless Edge DOM check")
def t4_s5(ctx: E2ERunnerContext) -> None:
    html_text = (WEB_DIR / "index.html").read_text(encoding="utf-8")
    app_ts = (WEB_DIR / "src" / "app.ts").read_text(encoding="utf-8")
    app_js = (WEB_DIR / "dist" / "app.js").read_text(encoding="utf-8")
    readme_text = (ROOT_DIR / "README.md").read_text(encoding="utf-8")

    # 1. HTML structure & preserved DOM IDs + semantic new feature controls
    scanner = validate_vietnamese_html(html_text)
    for core_id in (
        "machineBanner", "gCpu", "gFreeRam", "gProcRam", "gWebWorkers",
        "stateBadge", "btnStart", "btnEmergencyStop", "cfgCanvas",
        "cfgBlockOverlay", "srcEditor", "ssaViewer", "aiIntervalsBox",
        "cxDetailBox", "mutationTable", "leaderboardTable",
    ):
        assert core_id in scanner.ids, f"Preserved DOM ID #{core_id} missing from web/index.html"

    opt_vals = {v.lower() for v in scanner.option_values}
    html_low = html_text.lower()
    assert {"pytest", "vitest", "jest"}.issubset(opt_vals | set(re.findall(r"\b(?:pytest|vitest|jest)\b", html_low))), (
        "Missing pytest/vitest/jest selector options in web/index.html"
    )
    assert html_low.count("<textarea") >= 2, "Expected dual editors (<textarea>) for Equivalence Prover in web/index.html"
    assert ("tương đương" in html_low), "Missing Equivalence Prover Vietnamese label in web/index.html"
    assert ("mutant" in html_low or "đột biến" in html_low), "Missing Mutant Killer control in web/index.html"
    assert ("nhánh" in html_low or "unsat" in html_low), "Missing Dead-Branch toggle in web/index.html"
    assert ("tua" in html_low or "bước" in html_low), "Missing Trace Replay controls in web/index.html"

    # 2. TS <-> JS sync & syntax check + API wiring
    t1_f2_03(ctx)
    for route in ("/api/analyze-snippet", "/api/equivalence", "/api/kill-mutants", "/api/trace-replay"):
        assert route in app_js and route in app_ts, f"Missing API route {route} in app.ts/app.js"
    assert ("/api/generate-tests" in app_js or "generated_tests" in app_js), "Missing test generator wiring in app.js"
    assert "is_dead" in app_js and "trace_steps" in app_js

    # 3. Vietnamese localization checks
    validate_vietnamese_js(app_ts, "web/src/app.ts")
    validate_vietnamese_js(app_js, "web/dist/app.js")
    validate_vietnamese_readme(readme_text)

    # 4. Live HTTP static assets + optional headless Edge DOM runtime check
    with ctx.isolated_server() as (base_url, _, _):
        for asset in ("/", "/styles.css", "/dist/app.js", "/dist/compute_worker.js"):
            st, _, _ = ctx.http_request(base_url, "GET", asset)
            assert st == 200

        edge_candidates = [
            Path(r"C:\Program Files (x86)\Microsoft\Edge\Application\msedge.exe"),
            Path(r"C:\Program Files\Microsoft\Edge\Application\msedge.exe"),
        ]
        edge_bin = next((p for p in edge_candidates if p.exists()), None)
        if edge_bin is not None:
            with tempfile.TemporaryDirectory(prefix="hyperion_e2e_edge_") as edge_tmp:
                proc = subprocess.run(
                    [
                        str(edge_bin),
                        "--headless",
                        "--disable-gpu",
                        "--no-sandbox",
                        f"--user-data-dir={edge_tmp}",
                        "--virtual-time-budget=3000",
                        "--dump-dom",
                        f"{base_url}/",
                    ],
                    capture_output=True,
                    text=True,
                    encoding="utf-8",
                    errors="replace",
                    timeout=30,
                )
                if proc.returncode == 0 and proc.stdout.strip():
                    dom = proc.stdout
                    assert 'lang="vi"' in dom or "lang='vi'" in dom
                    _assert_has_vietnamese(dom, "Headless Edge rendered DOM")
                    assert "cfgCanvas" in dom and "srcEditor" in dom


# ===========================================================================
# Registry Validation, Reporting & CLI Main
# ===========================================================================

def validate_registry(cases: Optional[List[E2ECase]] = None) -> Dict[str, Any]:
    reg = TEST_REGISTRY if cases is None else cases
    seen_ids: Set[str] = set()
    tier_counts: Dict[int, int] = {t: 0 for t in VALID_TIERS}
    t1_per_feat: Dict[str, int] = {f: 0 for f in VALID_FEATURES}
    t2_per_feat: Dict[str, int] = {f: 0 for f in VALID_FEATURES}

    for case in reg:
        assert case.test_id not in seen_ids, f"Duplicate test_id: {case.test_id}"
        seen_ids.add(case.test_id)
        assert case.tier in VALID_TIERS, f"Invalid tier {case.tier} on {case.test_id}"
        assert case.features, f"Empty features on {case.test_id}"
        for f in case.features:
            assert f in VALID_FEATURES, f"Invalid feature {f!r} on {case.test_id}"
        sig = inspect.signature(case.fn)
        assert len(sig.parameters) == 1, f"{case.test_id} callable must accept 1 context parameter"

        tier_counts[case.tier] += 1
        if case.tier == 1:
            for f in case.features:
                t1_per_feat[f] += 1
        elif case.tier == 2:
            for f in case.features:
                t2_per_feat[f] += 1

    assert tier_counts[1] >= 40, f"Tier 1 count {tier_counts[1]} < 40"
    assert tier_counts[2] >= 40, f"Tier 2 count {tier_counts[2]} < 40"
    assert tier_counts[3] >= 8, f"Tier 3 count {tier_counts[3]} < 8"
    assert tier_counts[4] >= 5, f"Tier 4 count {tier_counts[4]} < 5"
    for f in VALID_FEATURES:
        assert t1_per_feat[f] >= 5, f"Tier 1 feature {f} count {t1_per_feat[f]} < 5"
        assert t2_per_feat[f] >= 5, f"Tier 2 feature {f} count {t2_per_feat[f]} < 5"

    return {
        "total": len(reg),
        "tiers": tier_counts,
        "tier1_per_feature": t1_per_feat,
        "tier2_per_feature": t2_per_feat,
    }


def _check_dry_run_preconditions() -> None:
    suite_path = Path(__file__).resolve()
    tree = ast.parse(suite_path.read_text(encoding="utf-8"), filename=str(suite_path))
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                top = alias.name.split(".")[0]
                assert top == "hyperion" or top in sys.stdlib_module_names, (
                    f"Non-stdlib import {alias.name!r} in {suite_path}"
                )
        elif isinstance(node, ast.ImportFrom) and node.level == 0 and node.module:
            top = node.module.split(".")[0]
            assert top == "hyperion" or top in sys.stdlib_module_names, (
                f"Non-stdlib from-import {node.module!r} in {suite_path}"
            )
    assert (ROOT / "main.py").is_file(), "Missing main.py"
    assert (WEB_DIR / "index.html").is_file(), "Missing web/index.html"
    with tempfile.TemporaryDirectory(prefix="hyperion_e2e_dry_") as tmp:
        assert Path(tmp).is_dir()


def _select_cases(tier_arg: str) -> List[E2ECase]:
    if tier_arg == "all":
        return list(TEST_REGISTRY)
    t = int(tier_arg)
    return [c for c in TEST_REGISTRY if c.tier == t]


def _write_json_out(path_arg: str, payload: Dict[str, Any]) -> None:
    rendered = json.dumps(payload, indent=2, ensure_ascii=False)
    if path_arg == "-":
        print(rendered)
    else:
        out_path = Path(path_arg)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(rendered, encoding="utf-8")


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="HYPERION Requirement-Driven Opaque-Box E2E Suite")
    parser.add_argument("--tier", default="all", choices=["1", "2", "3", "4", "all"], help="Tier(s) to list or run")
    parser.add_argument("-v", "--verbose", action="store_true", help="Verbose per-test diagnostics")
    parser.add_argument("--list", action="store_true", help="List registered E2E cases for selected tier")
    parser.add_argument("--dry-run", action="store_true", help="Validate test registry and runner preconditions without executing tests")
    parser.add_argument("--json-out", default="", help="Write JSON report to path (or '-' for stdout)")
    args = parser.parse_args(argv)

    summary_meta = validate_registry()
    selected = _select_cases(args.tier)

    if args.list:
        print(f"{'TEST_ID':<10} | {'TIER':<4} | {'FEATURES':<12} | {'ENTRY':<11} | TITLE")
        print("-" * 92)
        for c in selected:
            print(f"{c.test_id:<10} | T{c.tier:<3} | {','.join(c.features):<12} | {c.entrypoint:<11} | {c.title}")
        print(f"\nSelected: {len(selected)} tests (Total registered: {summary_meta['total']})")
        return 0

    if args.dry_run:
        _check_dry_run_preconditions()
        dry_payload = {
            "mode": "dry-run",
            "valid": True,
            "selected_count": len(selected),
            "registry": summary_meta,
        }
        if args.verbose:
            print(f"[DRY-RUN] Registry validated: {summary_meta['total']} total tests")
            print(f"  Tiers: {summary_meta['tiers']}")
            print(f"  Tier 1 per feature: {summary_meta['tier1_per_feature']}")
            print(f"  Tier 2 per feature: {summary_meta['tier2_per_feature']}")
            print(f"  Preconditions OK (stdlib-only AST, main.py, web/index.html, tempdir).")
        else:
            print(f"DRY-RUN OK: {len(selected)} selected / {summary_meta['total']} registered tests.")
        if args.json_out:
            _write_json_out(args.json_out, dry_payload)
        return 0

    ctx = E2ERunnerContext(verbose=args.verbose)
    t_start = time.perf_counter()
    results: List[Dict[str, Any]] = []
    passed = 0
    failed = 0

    for c in selected:
        tc0 = time.perf_counter()
        err_msg = ""
        tb_str = ""
        ok = False
        try:
            c.fn(ctx)
            ok = True
            passed += 1
        except Exception as exc:
            failed += 1
            err_msg = f"{type(exc).__name__}: {exc}"
            tb_str = traceback.format_exc()
        dt_ms = round((time.perf_counter() - tc0) * 1000.0, 2)
        results.append(
            {
                "test_id": c.test_id,
                "tier": c.tier,
                "features": list(c.features),
                "entrypoint": c.entrypoint,
                "title": c.title,
                "status": "PASS" if ok else "FAIL",
                "duration_ms": dt_ms,
                "error": err_msg,
            }
        )
        if args.verbose or not ok:
            tag = "PASS" if ok else "FAIL"
            print(f"[{tag}] {c.test_id} (T{c.tier} {','.join(c.features)} {c.entrypoint}) - {dt_ms}ms - {c.title}")
            if not ok:
                print(f"  Error: {err_msg}")
                if args.verbose:
                    for line in tb_str.rstrip().splitlines():
                        print(f"    {line}")

    total_sec = round(time.perf_counter() - t_start, 3)
    tier_summary: Dict[str, Dict[str, int]] = {}
    for r in results:
        tk = f"T{r['tier']}"
        bucket = tier_summary.setdefault(tk, {"total": 0, "passed": 0, "failed": 0})
        bucket["total"] += 1
        if r["status"] == "PASS":
            bucket["passed"] += 1
        else:
            bucket["failed"] += 1

    final_payload = {
        "total": len(results),
        "passed": passed,
        "failed": failed,
        "duration_sec": total_sec,
        "tiers": tier_summary,
        "results": results,
    }
    print(f"\nE2E Summary: {passed}/{len(results)} passed, {failed} failed in {total_sec}s.")
    if args.json_out:
        _write_json_out(args.json_out, final_payload)
    return 0 if failed == 0 else 1


if __name__ == "__main__":
    multiprocessing.freeze_support()
    raise SystemExit(main())
