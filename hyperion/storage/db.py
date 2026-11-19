"""Portable SQLite Leaderboard & Run History with in-memory journaling to protect SSD health."""

import json
import sqlite3
import time
from pathlib import Path
from typing import Any, Dict, List

from hyperion.config import DATA_DIR


class LeaderboardDB:
    """Stores cross-machine benchmark scores inside Win10_SSD without SSD journal churn."""

    def __init__(self, db_path: Path | None = None) -> None:
        self.db_path = db_path or (DATA_DIR / "benchmarks.sqlite3")
        self.db_path.parent.mkdir(parents=True, exist_ok=True)
        self._init_schema()

    def _connect(self) -> sqlite3.Connection:
        conn = sqlite3.connect(str(self.db_path), timeout=5.0)
        # Keep rollback journal in RAM to minimize flash writes on Win10_SSD
        conn.execute("PRAGMA journal_mode=MEMORY;")
        conn.execute("PRAGMA synchronous=NORMAL;")
        return conn

    def _init_schema(self) -> None:
        with self._connect() as conn:
            conn.execute(
                """
                CREATE TABLE IF NOT EXISTS benchmark_runs (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    created_at REAL NOT NULL,
                    hostname TEXT NOT NULL,
                    cpu_model TEXT NOT NULL,
                    logical_cores INTEGER NOT NULL,
                    total_ram_gb REAL NOT NULL,
                    mode TEXT NOT NULL,
                    corpus_source TEXT NOT NULL,
                    intensity TEXT NOT NULL,
                    workers_used INTEGER NOT NULL,
                    duration_sec REAL NOT NULL,
                    composite_score REAL NOT NULL,
                    ssa_cfg_score REAL NOT NULL,
                    smt_symbolic_score REAL NOT NULL,
                    mutation_score REAL NOT NULL,
                    parallel_throughput REAL NOT NULL,
                    functions_analyzed INTEGER NOT NULL,
                    loc_analyzed INTEGER NOT NULL,
                    smt_queries INTEGER NOT NULL,
                    mutants_evaluated INTEGER NOT NULL,
                    status TEXT NOT NULL,
                    details_json TEXT NOT NULL
                )
                """
            )
            conn.commit()

    def save_run(self, summary: Dict[str, Any], machine: Dict[str, Any]) -> int:
        scores = summary.get("scores", {})
        totals = summary.get("totals", {})
        with self._connect() as conn:
            cur = conn.execute(
                """
                INSERT INTO benchmark_runs (
                    created_at, hostname, cpu_model, logical_cores, total_ram_gb,
                    mode, corpus_source, intensity, workers_used, duration_sec,
                    composite_score, ssa_cfg_score, smt_symbolic_score,
                    mutation_score, parallel_throughput,
                    functions_analyzed, loc_analyzed, smt_queries, mutants_evaluated,
                    status, details_json
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                """,
                (
                    time.time(),
                    str(machine.get("hostname", "unknown")),
                    str(machine.get("cpu_model", "Unknown CPU")),
                    int(machine.get("logical_cores", 1)),
                    float(machine.get("total_ram_gb", 0.0)),
                    str(summary.get("mode", "benchmark")),
                    str(summary.get("corpus_source", "procedural")),
                    str(summary.get("intensity", "heavy")),
                    int(summary.get("workers_used", 1)),
                    float(summary.get("duration_sec", 0.0)),
                    float(scores.get("composite_score", 0.0)),
                    float(scores.get("ssa_cfg_score", 0.0)),
                    float(scores.get("smt_symbolic_score", 0.0)),
                    float(scores.get("mutation_score", 0.0)),
                    float(scores.get("parallel_throughput", 0.0)),
                    int(totals.get("functions", 0)),
                    int(totals.get("loc", 0)),
                    int(totals.get("smt_queries", 0)),
                    int(totals.get("mutants_evaluated", 0)),
                    str(summary.get("status", "COMPLETED")),
                    json.dumps(
                        {
                            "stop_reason": summary.get("stop_reason", ""),
                            "os": machine.get("os", ""),
                            "arch": machine.get("arch", ""),
                        }
                    ),
                ),
            )
            # Cap history at 200 entries to keep database compact
            conn.execute(
                """
                DELETE FROM benchmark_runs
                WHERE id NOT IN (
                    SELECT id FROM benchmark_runs ORDER BY id DESC LIMIT 200
                )
                """
            )
            conn.commit()
            return int(cur.lastrowid or 0)

    def list_runs(self, limit: int = 30) -> List[Dict[str, Any]]:
        with self._connect() as conn:
            conn.row_factory = sqlite3.Row
            rows = conn.execute(
                """
                SELECT id, created_at, hostname, cpu_model, logical_cores, total_ram_gb,
                       mode, corpus_source, intensity, workers_used, duration_sec,
                       composite_score, ssa_cfg_score, smt_symbolic_score,
                       mutation_score, parallel_throughput,
                       functions_analyzed, loc_analyzed, smt_queries, mutants_evaluated,
                       status, details_json
                FROM benchmark_runs
                ORDER BY composite_score DESC, id DESC
                LIMIT ?
                """,
                (limit,),
            ).fetchall()
        results: List[Dict[str, Any]] = []
        for r in rows:
            d = dict(r)
            try:
                d["details"] = json.loads(d.pop("details_json", "{}"))
            except Exception:
                d["details"] = {}
            results.append(d)
        return results
