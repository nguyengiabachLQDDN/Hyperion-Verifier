"""Target Corpus Manager supporting Self-Hosting, Procedural Torture Synthesis, and Local Folder Scans."""

from dataclasses import dataclass
from pathlib import Path
import random
from typing import List

from hyperion.config import ROOT_DIR


@dataclass
class SourceUnit:
    name: str
    language: str  # "python" | "typescript"
    source_file: str
    source_code: str
    loc: int


def _count_loc(code: str) -> int:
    return sum(1 for ln in code.splitlines() if ln.strip())


def load_self_host_corpus(max_files: int = 40) -> List[SourceUnit]:
    """Read Hyperion's own Python and TypeScript source files from Win10_SSD for self-analysis."""
    units: List[SourceUnit] = []
    scan_dirs = [ROOT_DIR / "hyperion", ROOT_DIR / "web" / "src", ROOT_DIR / "tests"]
    for base in scan_dirs:
        if not base.exists():
            continue
        for p in sorted(base.rglob("*")):
            if len(units) >= max_files:
                break
            if not p.is_file():
                continue
            if p.suffix == ".py":
                lang = "python"
            elif p.suffix in (".ts", ".js"):
                lang = "typescript"
            else:
                continue
            try:
                text = p.read_text(encoding="utf-8", errors="ignore")
                rel = str(p.relative_to(ROOT_DIR))
                units.append(
                    SourceUnit(
                        name=p.stem,
                        language=lang,
                        source_file=rel,
                        source_code=text,
                        loc=_count_loc(text),
                    )
                )
            except Exception:
                continue
    return units


def load_custom_directory_corpus(
    folder_path: str, max_files: int = 80, max_bytes_per_file: int = 256 * 1024
) -> List[SourceUnit]:
    """Read-only scan of any local directory for Python/TypeScript/JS source analysis."""
    units: List[SourceUnit] = []
    root = Path(folder_path)
    if not folder_path or not root.exists() or not root.is_dir():
        return units

    ignored = {"node_modules", ".git", "__pycache__", ".venv", "venv", "dist", "build"}
    for p in sorted(root.rglob("*")):
        if len(units) >= max_files:
            break
        if any(part in ignored for part in p.parts):
            continue
        if not p.is_file():
            continue
        if p.suffix == ".py":
            lang = "python"
        elif p.suffix in (".ts", ".tsx", ".js", ".jsx"):
            lang = "typescript"
        else:
            continue
        try:
            if p.stat().st_size > max_bytes_per_file:
                continue
            text = p.read_text(encoding="utf-8", errors="ignore")
            units.append(
                SourceUnit(
                    name=p.stem,
                    language=lang,
                    source_file=str(p),
                    source_code=text,
                    loc=_count_loc(text),
                )
            )
        except Exception:
            continue
    return units


def _gen_python_crypto_kernel(rng: random.Random, idx: int) -> str:
    c1 = rng.randint(17, 97)
    c2 = rng.randint(101, 251)
    mask = rng.choice([255, 1023, 4095])
    threshold = rng.randint(12, 48)
    trap_val = rng.randint(5, 25)
    return f"""
def sponge_feistel_round_{idx}(state_a, state_b, key_sched, rounds):
    acc = (state_a ^ {c1}) + (state_b & {mask})
    parity = 0
    limit = rounds if rounds < 16 else 16
    for i in range(limit):
        mix = ((acc << 3) ^ (state_b + i * {c2})) & {mask}
        if mix > {threshold}:
            acc = (acc + mix + key_sched) & {mask}
            parity = parity ^ 1
        else:
            acc = (acc - mix + {c1}) & {mask}
            parity = parity + 2
        state_b = (state_b + acc + i) & {mask}
    denom = state_a - {trap_val}
    if key_sched > 10 and rounds > 2:
        norm = acc // denom
        acc = acc + norm
    assert acc >= 0, "sponge_invariant"
    return acc + parity
""".lstrip()


def _gen_python_auth_taint(rng: random.Random, idx: int) -> str:
    role_cap = rng.randint(2, 5)
    secret_magic = rng.randint(20, 60)
    return f"""
def rbac_query_gateway_{idx}(user_input, role_level, tenant_id, bypass_token):
    token = read_packet(user_input)
    score = role_level * 10 + tenant_id
    if role_level >= {role_cap} and bypass_token == {secret_magic}:
        clean = sanitize(token)
        if tenant_id > 0:
            score = score + 100
        return score
    if role_level < {role_cap} and tenant_id == 7:
        # Conditional taint path directly into SQL sink
        sql_query(token, tenant_id)
    if bypass_token < 0:
        cmd_arg = user_input
        system(cmd_arg)
    assert score >= 0, "score_non_negative"
    return score
""".lstrip()


def _gen_python_btree_splitter(rng: random.Random, idx: int) -> str:
    cap = rng.randint(8, 16)
    pivot_shift = rng.randint(2, 6)
    return f"""
def btree_page_split_{idx}(key_count, target_slot, fanout):
    page = [0, 1, 2, 3, 4, 5, 6, 7]
    mid = key_count // 2
    if fanout <= 0:
        fanout = 4
    cursor = 0
    while cursor < 6 and key_count > {pivot_shift}:
        if target_slot == cursor:
            val = page[target_slot]
            mid = mid + val
        cursor = cursor + 1
    if key_count > {cap} and target_slot >= 8:
        # Triggers symbolic OOB array store detection
        page[target_slot] = mid
    assert mid >= 0, "btree_mid_valid"
    return mid + (key_count % fanout)
""".lstrip()


def _gen_ts_packet_parser(rng: random.Random, idx: int) -> str:
    magic = rng.randint(10, 40)
    hdr_sz = rng.randint(4, 12)
    return f"""
export function parsePacketFrame_{idx}(packetLen: number, flags: number, offset: number, untrustedPayload: number): number {{
    let ring = [1, 2, 3, 4, 5, 6];
    let checksum = (packetLen ^ {magic}) + (flags & 31);
    let i = 0;
    while (i < 5 && packetLen > {hdr_sz}) {{
        if ((flags & 1) == 1) {{
            checksum = checksum + i * 3;
        }} else {{
            checksum = checksum - i;
        }}
        i = i + 1;
    }}
    if (flags == 9 && offset >= 6) {{
        let bad = ring[offset];
        checksum = checksum + bad;
    }}
    if (packetLen == {magic} && flags < 0) {{
        sqlExec(untrustedPayload, checksum);
    }}
    assert(checksum > -500, "checksum_bound");
    return checksum;
}}
""".lstrip()


def _gen_ts_orderbook_engine(rng: random.Random, idx: int) -> str:
    spread = rng.randint(2, 12)
    fee_bps = rng.randint(5, 25)
    return f"""
export function matchOrderBook_{idx}(bidPrice: number, askPrice: number, qty: number, feeMode: number): number {{
    let notional = 0;
    let filled = 0;
    if (bidPrice >= askPrice + {spread} && qty > 0) {{
        let step = 0;
        for (let k = 0; k < 4; k++) {{
            if (qty > k * 5) {{
                filled = filled + 1;
                step = step + bidPrice - askPrice;
            }}
        }}
        notional = step * qty;
    }} else {{
        notional = (askPrice - bidPrice) * 2;
    }}
    let denom = feeMode - 3;
    if (bidPrice > 20 && askPrice < 10) {{
        let fee = notional / denom;
        notional = notional - fee - {fee_bps};
    }}
    assert(filled >= 0, "filled_positive");
    return notional + filled;
}}
""".lstrip()


def generate_procedural_corpus(scale_factor: int = 4, seed: int = 133742) -> List[SourceUnit]:
    """Synthesize a deterministic polyglot workload in RAM scaled by `scale_factor`."""
    rng = random.Random(seed)
    units: List[SourceUnit] = []
    # Each scale unit produces 2 Python modules + 1 TypeScript module (with 3-4 complex functions each)
    num_py_modules = max(2, scale_factor * 2)
    num_ts_modules = max(1, scale_factor)

    for m_idx in range(num_py_modules):
        chunks = [
            _gen_python_crypto_kernel(rng, m_idx * 3 + 1),
            _gen_python_auth_taint(rng, m_idx * 3 + 2),
            _gen_python_btree_splitter(rng, m_idx * 3 + 3),
        ]
        code = "\n".join(chunks)
        units.append(
            SourceUnit(
                name=f"synth_py_kernel_{m_idx:03d}",
                language="python",
                source_file=f"<procedural>/synth_py_kernel_{m_idx:03d}.py",
                source_code=code,
                loc=_count_loc(code),
            )
        )

    for t_idx in range(num_ts_modules):
        chunks = [
            _gen_ts_packet_parser(rng, t_idx * 2 + 1),
            _gen_ts_orderbook_engine(rng, t_idx * 2 + 2),
        ]
        code = "\n".join(chunks)
        units.append(
            SourceUnit(
                name=f"synth_ts_engine_{t_idx:03d}",
                language="typescript",
                source_file=f"<procedural>/synth_ts_engine_{t_idx:03d}.ts",
                source_code=code,
                loc=_count_loc(code),
            )
        )

    return units
