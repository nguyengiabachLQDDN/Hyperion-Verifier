"""Bộ sinh Unit Test tự động cho pytest, vitest và jest dựa trên IRInterpreter oracle."""

import json
import keyword
import math
from pathlib import Path
import re
from typing import Any, Dict, List, Optional, Set, Tuple

from hyperion.ir.ssa import (
    ArrayLoadOp,
    ArrayStoreOp,
    AssignOp,
    BinaryOp,
    Const,
    IRFunction,
    SSAVar,
)
from hyperion.mutation.engine import IRInterpreter, VMOutcome
from hyperion.symbolic.engine import SymbolicResult, run_symbolic_execution

_JS_RESERVED = {
    "break", "case", "catch", "class", "const", "continue", "debugger", "default",
    "delete", "do", "else", "enum", "export", "extends", "false", "finally", "for",
    "function", "if", "import", "in", "instanceof", "new", "null", "return", "super",
    "switch", "this", "throw", "true", "try", "typeof", "var", "void", "while", "with",
    "yield", "let", "await", "implements", "interface", "package", "private",
    "protected", "public", "static", "undefined",
}


def _safe_ident(raw: str, fallback: str = "fn") -> str:
    cleaned = re.sub(r"[^A-Za-z0-9_]", "_", raw or "")
    cleaned = re.sub(r"_+", "_", cleaned).strip("_")
    if not cleaned:
        cleaned = fallback
    if cleaned[0].isdigit() or keyword.iskeyword(cleaned) or cleaned in _JS_RESERVED:
        cleaned = f"fn_{cleaned}"
    return cleaned


def _module_stem(source_file: str) -> str:
    if not source_file or source_file.startswith("<"):
        return "target_module"
    stem = Path(source_file).stem
    return _safe_ident(stem, fallback="target_module")


def _extract_const_and_affine_maps(
    fn: IRFunction,
) -> Tuple[Dict[str, int], Dict[str, Tuple[str, int]]]:
    """Read-only pass recovering integer constants and affine parameter offsets (param + offset)."""
    const_map: Dict[str, int] = {}
    affine_map: Dict[str, Tuple[str, int]] = {p.key(): (p.name, 0) for p in fn.params}

    def as_int(v: Any) -> Optional[int]:
        if isinstance(v, Const) and isinstance(v.value, int) and not isinstance(v.value, bool):
            return int(v.value)
        if isinstance(v, SSAVar) and v.key() in const_map:
            return const_map[v.key()]
        return None

    for bid in sorted(fn.blocks.keys()):
        blk = fn.blocks[bid]
        for ins in blk.instructions:
            if isinstance(ins, AssignOp) and ins.dest is not None:
                c = as_int(ins.src)
                if c is not None:
                    const_map[ins.dest.key()] = c
                elif isinstance(ins.src, SSAVar) and ins.src.key() in affine_map:
                    affine_map[ins.dest.key()] = affine_map[ins.src.key()]
            elif isinstance(ins, BinaryOp) and ins.dest is not None:
                lc = as_int(ins.left)
                rc = as_int(ins.right)
                if lc is not None and rc is not None:
                    if ins.op == "+":
                        const_map[ins.dest.key()] = lc + rc
                    elif ins.op == "-":
                        const_map[ins.dest.key()] = lc - rc
                    elif ins.op == "*":
                        const_map[ins.dest.key()] = lc * rc
                    elif ins.op == "//" and rc != 0:
                        const_map[ins.dest.key()] = lc // rc
                    continue
                if ins.op == "+" and isinstance(ins.left, SSAVar) and ins.left.key() in affine_map and rc is not None:
                    pname, off = affine_map[ins.left.key()]
                    affine_map[ins.dest.key()] = (pname, off + rc)
                elif ins.op == "+" and isinstance(ins.right, SSAVar) and ins.right.key() in affine_map and lc is not None:
                    pname, off = affine_map[ins.right.key()]
                    affine_map[ins.dest.key()] = (pname, off + lc)
                elif ins.op == "-" and isinstance(ins.left, SSAVar) and ins.left.key() in affine_map and rc is not None:
                    pname, off = affine_map[ins.left.key()]
                    affine_map[ins.dest.key()] = (pname, off - rc)
    return const_map, affine_map


def _normalize_vector(vec: Dict[str, Any], param_names: List[str]) -> Dict[str, int]:
    norm: Dict[str, int] = {}
    for p in param_names:
        raw = vec.get(p, 0)
        if isinstance(raw, bool):
            norm[p] = 1 if raw else 0
        elif isinstance(raw, (int, float)):
            norm[p] = int(raw)
        else:
            norm[p] = 0
    return norm


def _collect_candidate_cases(
    fn: IRFunction,
    symbolic_res: SymbolicResult,
    extra_vectors: Optional[List[Dict[str, int]]] = None,
    max_cases: int = 36,
) -> List[Tuple[Dict[str, int], str, str]]:
    """Collect prioritized, deduplicated test vectors with provenance tags."""
    param_names = [p.name for p in fn.params]
    candidates: List[Tuple[Dict[str, int], str, str]] = []

    # Priority 1: Counterexamples from symbolic execution
    for cx in symbolic_res.counterexamples:
        candidates.append(
            (
                dict(cx.inputs),
                "counterexample",
                f"Tái hiện lỗi {cx.kind} (dòng {cx.line}): {cx.description}",
            )
        )

    # Priority 2: Mutant killer witnesses / caller extra vectors
    for vec in extra_vectors or []:
        candidates.append(
            (
                dict(vec),
                "mutant_killer",
                "Vector nhân chứng tiêu diệt đột biến (SMT witness)",
            )
        )

    # Priority 3: Symbolic path vectors
    for vec in symbolic_res.synthesized_test_vectors:
        candidates.append(
            (
                dict(vec),
                "symbolic",
                "Vector sinh từ khám phá nhánh tượng trưng DPLL(T)",
            )
        )

    # Priority 4: IR boundary & array-index values
    if param_names:
        const_map, affine_map = _extract_const_and_affine_maps(fn)
        zero_vec = {p: 0 for p in param_names}
        anchor_vec = (
            _normalize_vector(symbolic_res.synthesized_test_vectors[0], param_names)
            if symbolic_res.synthesized_test_vectors
            else dict(zero_vec)
        )

        def resolve_const(v: Any) -> Optional[int]:
            if isinstance(v, Const) and isinstance(v.value, int) and not isinstance(v.value, bool):
                return int(v.value)
            if isinstance(v, SSAVar) and v.key() in const_map:
                return const_map[v.key()]
            return None

        def emit_target(pname: str, target_val: int, hint: str) -> None:
            for base in (zero_vec, anchor_vec):
                v = dict(base)
                v[pname] = target_val
                candidates.append((v, "boundary", hint))

        # Baseline scalars: -1, 0, 1
        for sc in (-1, 0, 1):
            candidates.append(({p: sc for p in param_names}, "boundary", f"Giá trị biên cơ bản ({sc})"))
            if len(param_names) > 1:
                for p in param_names:
                    v = dict(zero_vec)
                    v[p] = sc
                    candidates.append((v, "boundary", f"Giá trị biên tham số {p}={sc}"))

        # Branch comparison & division/modulo constants
        for bid in sorted(fn.blocks.keys()):
            blk = fn.blocks[bid]
            for ins in blk.instructions:
                if isinstance(ins, BinaryOp):
                    if ins.op in ("/", "//", "%"):
                        if isinstance(ins.right, SSAVar) and ins.right.key() in affine_map:
                            pname, off = affine_map[ins.right.key()]
                            for t in (-1, 0, 1):
                                emit_target(pname, t - off, f"Biên mẫu số chia dòng {ins.line}")
                    if ins.op in ("==", "!=", "<", "<=", ">", ">="):
                        rc = resolve_const(ins.right)
                        lc = resolve_const(ins.left)
                        if rc is not None and abs(rc) <= 100000:
                            if isinstance(ins.left, SSAVar) and ins.left.key() in affine_map:
                                pname, off = affine_map[ins.left.key()]
                                for t in (rc - 1, rc, rc + 1):
                                    emit_target(pname, t - off, f"Biên điều kiện nhánh ({rc}) dòng {ins.line}")
                            else:
                                for t in (rc - 1, rc, rc + 1):
                                    candidates.append(({p: t for p in param_names}, "boundary", f"Biên hằng số nhánh ({t})"))
                        if lc is not None and abs(lc) <= 100000:
                            if isinstance(ins.right, SSAVar) and ins.right.key() in affine_map:
                                pname, off = affine_map[ins.right.key()]
                                for t in (lc - 1, lc, lc + 1):
                                    emit_target(pname, t - off, f"Biên điều kiện nhánh ({lc}) dòng {ins.line}")
                            else:
                                for t in (lc - 1, lc, lc + 1):
                                    candidates.append(({p: t for p in param_names}, "boundary", f"Biên hằng số nhánh ({t})"))

                elif isinstance(ins, (ArrayLoadOp, ArrayStoreOp)):
                    arr_len = ins.known_length
                    if arr_len is None and isinstance(ins.array, SSAVar):
                        arr_len = fn.array_lengths.get(ins.array.name)
                    if isinstance(arr_len, int) and arr_len >= 0:
                        idx_targets = (-1, 0, max(0, arr_len - 1), arr_len)
                        if isinstance(ins.index, SSAVar) and ins.index.key() in affine_map:
                            pname, off = affine_map[ins.index.key()]
                            for t in idx_targets:
                                emit_target(pname, t - off, f"Biên chỉ số mảng [0..{arr_len - 1}] dòng {ins.line}")
                        else:
                            for t in idx_targets:
                                candidates.append(({p: t for p in param_names}, "boundary", f"Biên chỉ số mảng ({t})"))
    else:
        candidates.append(({}, "boundary", "Kiểm thử hàm không tham số"))

    # Deduplicate in priority order
    deduped: List[Tuple[Dict[str, int], str, str]] = []
    seen: Set[Tuple[int, ...]] = set()
    for raw_vec, source, hint in candidates:
        norm = _normalize_vector(raw_vec, param_names)
        key = tuple(norm[p] for p in param_names)
        if key in seen:
            continue
        seen.add(key)
        if len(deduped) >= max_cases and source not in ("counterexample", "mutant_killer"):
            continue
        deduped.append((norm, source, hint))

    if not deduped:
        deduped.append(({p: 0 for p in param_names}, "boundary", "Vector mặc định"))
    return deduped


def _format_args_summary(inputs: Dict[str, int]) -> str:
    if not inputs:
        return "(không tham số)"
    return ", ".join(f"{k}={v}" for k, v in inputs.items())


def _build_vn_description(source: str, hint: str, out: VMOutcome, inputs: Dict[str, int]) -> str:
    args_s = _format_args_summary(inputs)
    if out.status == "TRAP":
        return f"Kiểm tra bẫy ngoại lệ ({out.error}) với {args_s}"
    if out.status == "TIMEOUT":
        return f"Kiểm tra giới hạn gas VM (TIMEOUT) với {args_s}"
    if source == "counterexample":
        return f"{hint} | đầu vào {args_s}"
    if source == "mutant_killer":
        return f"Tiêu diệt đột biến (SMT witness) với {args_s}"
    if source == "boundary":
        return f"{hint} với {args_s}"
    return f"Kiểm thử đường thực thi tượng trưng với {args_s}"


def _py_exc_for_trap(error: str) -> str:
    if error in ("zero_division", "zero_modulo"):
        return "ZeroDivisionError"
    if error in ("oob_read", "oob_write"):
        return "IndexError"
    if error == "assertion_failed":
        return "AssertionError"
    return "Exception"


def _emit_pytest_suite(
    fn: IRFunction,
    cases: List[Dict[str, Any]],
) -> str:
    mod_name = _module_stem(fn.source_file)
    param_names = [p.name for p in fn.params]

    if "." in fn.name:
        cls_raw, meth_raw = fn.name.split(".", 1)
        cls_ident = _safe_ident(cls_raw, fallback="TargetClass")
        meth_ident = _safe_ident(meth_raw, fallback="method")
        import_line = f"from {mod_name} import {cls_ident}"
        call_prefix = f"{cls_ident}().{meth_ident}"
        safe_fn_tag = _safe_ident(f"{cls_ident}_{meth_ident}")
    else:
        fn_ident = _safe_ident(fn.name, fallback="target_fn")
        import_line = f"from {mod_name} import {fn_ident}"
        call_prefix = fn_ident
        safe_fn_tag = fn_ident

    needs_math = any(
        c["status"] == "OK"
        and isinstance(c["expected"], float)
        and (math.isnan(c["expected"]) or math.isinf(c["expected"]))
        for c in cases
    )

    lines: List[str] = [
        f"# Bộ unit test pytest được Hyperion sinh tự động cho `{fn.name}`",
        "# Oracle xác nhận trực tiếp từ máy ảo SSA IRInterpreter.",
    ]
    if needs_math:
        lines.append("import math")
    lines.append("import pytest")
    lines.append(import_line)
    lines.append("")

    for case in cases:
        cid = case["case_id"]
        inputs = case["inputs"]
        status = case["status"]
        expected = case["expected"]
        desc = str(case["description"]).replace("\n", " ")
        args_list = ", ".join(repr(inputs.get(p, 0)) for p in param_names)
        call_expr = f"{call_prefix}({args_list})"
        test_fn_name = f"test_{safe_fn_tag}_case_{cid}"

        if status == "TIMEOUT":
            lines.append('@pytest.mark.skip(reason="Vượt giới hạn gas VM (vòng lặp dài hoặc vô hạn)")')
            lines.append(f"def {test_fn_name}() -> None:")
            lines.append(f"    # {desc}")
            lines.append(f"    {call_expr}")
            lines.append("")
            continue

        lines.append(f"def {test_fn_name}() -> None:")
        lines.append(f"    # {desc}")
        if status == "TRAP":
            exc_cls = _py_exc_for_trap(str(case.get("error", "")))
            lines.append(f"    with pytest.raises({exc_cls}):")
            lines.append(f"        {call_expr}")
        else:
            if expected is None:
                lines.append(f"    assert {call_expr} is None")
            elif isinstance(expected, bool):
                lines.append(f"    assert {call_expr} == {'True' if expected else 'False'}")
            elif isinstance(expected, int):
                lines.append(f"    assert {call_expr} == {expected}")
            elif isinstance(expected, float):
                if math.isnan(expected):
                    lines.append(f"    assert math.isnan({call_expr})")
                elif math.isinf(expected):
                    lines.append(f"    assert math.isinf({call_expr})")
                else:
                    lines.append(f"    assert {call_expr} == pytest.approx({repr(expected)})")
            else:
                lines.append(f"    assert {call_expr} == {repr(expected)}")
        lines.append("")

    return "\n".join(lines).rstrip() + "\n"


def _emit_js_suite(
    fn: IRFunction,
    cases: List[Dict[str, Any]],
    mode: str,  # "vitest" | "jest"
) -> str:
    mod_name = _module_stem(fn.source_file)
    param_names = [p.name for p in fn.params]

    if "." in fn.name:
        cls_raw, meth_raw = fn.name.split(".", 1)
        cls_ident = _safe_ident(cls_raw, fallback="TargetClass")
        meth_ident = _safe_ident(meth_raw, fallback="method")
        import_symbol = cls_ident
        call_prefix = f"new {cls_ident}().{meth_ident}"
    else:
        fn_ident = _safe_ident(fn.name, fallback="target_fn")
        import_symbol = fn_ident
        call_prefix = fn_ident

    lines: List[str] = [
        f"// Bộ unit test {mode} được Hyperion sinh tự động cho `{fn.name}`",
        "// Oracle xác nhận trực tiếp từ máy ảo SSA IRInterpreter.",
    ]
    if mode == "vitest":
        lines.append('import { describe, it, expect } from "vitest";')
        lines.append(f'import {{ {import_symbol} }} from "./{mod_name}";')
        runner = "it"
    else:
        lines.append('// Với cấu hình ESM có thể dùng: import { describe, test, expect } from "@jest/globals";')
        lines.append(f'const {{ {import_symbol} }} = require("./{mod_name}");')
        runner = "test"

    lines.append("")
    suite_title = json.dumps(f"Kiểm thử tự động cho {fn.name}", ensure_ascii=False)
    lines.append(f"describe({suite_title}, () => {{")

    for case in cases:
        cid = case["case_id"]
        inputs = case["inputs"]
        status = case["status"]
        expected = case["expected"]
        desc = str(case["description"]).replace("\n", " ")
        args_list = ", ".join(str(int(inputs.get(p, 0))) for p in param_names)
        call_expr = f"{call_prefix}({args_list})"
        test_title = json.dumps(f"Trường hợp #{cid}: {desc}", ensure_ascii=False)

        if status == "TIMEOUT":
            lines.append(f"  {runner}.skip({test_title}, () => {{")
            lines.append(f"    {call_expr};")
            lines.append("  });")
            continue

        lines.append(f"  {runner}({test_title}, () => {{")
        if status == "TRAP":
            lines.append(f"    expect(() => {call_expr}).toThrow();")
        else:
            if expected is None:
                lines.append(f"    expect({call_expr}).toBe(undefined);")
            elif isinstance(expected, bool):
                lines.append(f"    expect({call_expr}).toBe({'true' if expected else 'false'});")
            elif isinstance(expected, int):
                lines.append(f"    expect({call_expr}).toBe({expected});")
            elif isinstance(expected, float):
                if math.isnan(expected):
                    lines.append(f"    expect(Number.isNaN({call_expr})).toBe(true);")
                elif math.isinf(expected):
                    inf_lit = "Infinity" if expected > 0 else "-Infinity"
                    lines.append(f"    expect({call_expr}).toBe({inf_lit});")
                else:
                    lines.append(f"    expect({call_expr}).toBeCloseTo({repr(expected)});")
            elif isinstance(expected, list):
                lines.append(f"    expect({call_expr}).toEqual({json.dumps(expected, ensure_ascii=False)});")
            else:
                lines.append(f"    expect({call_expr}).toBe({json.dumps(expected, ensure_ascii=False)});")
        lines.append("  });")

    lines.append("});")
    lines.append("")
    return "\n".join(lines)


def generate_all_frameworks(
    fn: IRFunction,
    symbolic_res: Optional[SymbolicResult] = None,
    extra_vectors: Optional[List[Dict[str, int]]] = None,
) -> Dict[str, Any]:
    """Sinh đầy đủ bộ test pytest, vitest và jest cho một IRFunction."""
    sym = symbolic_res if symbolic_res is not None else run_symbolic_execution(fn, max_paths=48)
    selected = _collect_candidate_cases(fn, sym, extra_vectors=extra_vectors)
    vm = IRInterpreter(gas_limit=4000)

    safe_tag = _safe_ident(fn.name.replace(".", "_"), fallback="target_fn")
    cases: List[Dict[str, Any]] = []
    vectors: List[Dict[str, int]] = []

    for idx, (vec, source, hint) in enumerate(selected, start=1):
        out = vm.execute(fn, vec)
        vectors.append(dict(vec))
        cases.append(
            {
                "case_id": idx,
                "name": f"test_{safe_tag}_case_{idx}",
                "inputs": dict(vec),
                "status": out.status,
                "expected": out.return_value,
                "error": out.error,
                "steps": out.steps,
                "source": source,
                "description": _build_vn_description(source, hint, out, vec),
            }
        )

    pytest_code = _emit_pytest_suite(fn, cases)
    vitest_code = _emit_js_suite(fn, cases, mode="vitest")
    jest_code = _emit_js_suite(fn, cases, mode="jest")

    return {
        "function": fn.name,
        "language": fn.source_lang,
        "pytest": pytest_code,
        "vitest": vitest_code,
        "jest": jest_code,
        "cases": cases,
        "vectors": vectors,
    }


def generate_unit_tests(
    fn: IRFunction,
    symbolic_res: Optional[SymbolicResult] = None,
    extra_vectors: Optional[List[Dict[str, int]]] = None,
    framework: str = "pytest",
) -> Dict[str, Any]:
    """Sinh unit test suite (trả về cả pytest, vitest, jest kèm danh sách cases và vectors)."""
    _ = framework  # Đảm bảo tương thích tham số framework theo contract
    return generate_all_frameworks(fn, symbolic_res=symbolic_res, extra_vectors=extra_vectors)
