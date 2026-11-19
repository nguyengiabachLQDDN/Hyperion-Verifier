"""Configuration profiles, safety guardrails, and runtime settings for HYPERION."""

from dataclasses import dataclass, field, asdict
import os
from pathlib import Path
from typing import Dict, Any


ROOT_DIR = Path(__file__).resolve().parent.parent
DATA_DIR = ROOT_DIR / "data"
WEB_DIR = ROOT_DIR / "web"


def default_worker_count() -> int:
    """Reserve one logical core by default so the host OS remains responsive."""
    cores = os.cpu_count() or 2
    return max(1, cores - 1)


@dataclass
class SafetyConfig:
    """User-configurable hardware safety and circuit-breaker limits."""

    max_workers: int = field(default_factory=default_worker_count)
    max_process_ram_mb: int = 1536
    min_free_system_ram_pct: float = 10.0
    max_duration_sec: int = 120
    max_symbolic_paths_per_fn: int = 120
    max_mutants_per_fn: int = 80
    instruction_gas_limit: int = 4000
    ram_arena_mb: int = 0
    below_normal_priority: bool = True

    def clamp(self) -> "SafetyConfig":
        """Normalize user inputs to valid operational bounds."""
        cores = os.cpu_count() or 2
        self.max_workers = max(1, min(self.max_workers, max(1, cores * 2)))
        self.max_process_ram_mb = max(256, min(self.max_process_ram_mb, 16384))
        self.min_free_system_ram_pct = max(5.0, min(float(self.min_free_system_ram_pct), 95.0))
        self.max_duration_sec = max(5, min(self.max_duration_sec, 3600))
        self.max_symbolic_paths_per_fn = max(8, min(self.max_symbolic_paths_per_fn, 1024))
        self.max_mutants_per_fn = max(4, min(self.max_mutants_per_fn, 512))
        self.instruction_gas_limit = max(200, min(self.instruction_gas_limit, 50000))
        self.ram_arena_mb = max(0, min(self.ram_arena_mb, int(self.max_process_ram_mb * 0.85)))
        return self

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def from_dict(cls, raw: Dict[str, Any]) -> "SafetyConfig":
        cfg = cls()
        for k, v in raw.items():
            if hasattr(cfg, k) and v is not None:
                cur_type = type(getattr(cfg, k))
                if cur_type is bool:
                    setattr(cfg, k, bool(v))
                elif cur_type is int:
                    setattr(cfg, k, int(v))
                elif cur_type is float:
                    setattr(cfg, k, float(v))
        return cfg.clamp()


@dataclass
class RunConfig:
    """Execution parameters for a benchmark or torture stress run."""

    mode: str = "benchmark"  # "benchmark" | "stress" | "analyze"
    corpus_source: str = "procedural"  # "self_host" | "procedural" | "custom_path"
    custom_path: str = ""
    intensity: str = "heavy"  # "balanced" | "heavy" | "extreme" | "benchmark"
    scale_factor: int = 4
    seed: int = 133742
    enable_optimizer: bool = True
    enable_abstract_interp: bool = True
    enable_symbolic: bool = True
    enable_mutation: bool = True
    safety: SafetyConfig = field(default_factory=SafetyConfig)

    def apply_intensity_defaults(self) -> "RunConfig":
        """Map named intensity presets without overriding explicit safety bounds."""
        presets = {
            "balanced": (2, 48, 32, 2500),
            "heavy": (5, 96, 64, 4000),
            "extreme": (10, 220, 128, 7500),
            "benchmark": (4, 100, 60, 4000),
        }
        if self.intensity in presets:
            scale, paths, mutants, gas = presets[self.intensity]
            if self.mode == "benchmark":
                self.scale_factor = scale
            elif self.scale_factor <= 0:
                self.scale_factor = scale
            self.safety.max_symbolic_paths_per_fn = max(self.safety.max_symbolic_paths_per_fn, paths) if self.intensity == "extreme" else paths
            self.safety.max_mutants_per_fn = max(self.safety.max_mutants_per_fn, mutants) if self.intensity == "extreme" else mutants
            self.safety.instruction_gas_limit = gas
        self.scale_factor = max(1, min(self.scale_factor, 50))
        self.safety.clamp()
        return self

    def to_dict(self) -> Dict[str, Any]:
        d = asdict(self)
        return d

    @classmethod
    def from_dict(cls, raw: Dict[str, Any]) -> "RunConfig":
        safety_raw = raw.get("safety") or {}
        cfg = cls(
            mode=str(raw.get("mode", "benchmark")),
            corpus_source=str(raw.get("corpus_source", "procedural")),
            custom_path=str(raw.get("custom_path", "")),
            intensity=str(raw.get("intensity", "heavy")),
            scale_factor=int(raw.get("scale_factor", 4)),
            seed=int(raw.get("seed", 133742)),
            enable_optimizer=bool(raw.get("enable_optimizer", True)),
            enable_abstract_interp=bool(raw.get("enable_abstract_interp", True)),
            enable_symbolic=bool(raw.get("enable_symbolic", True)),
            enable_mutation=bool(raw.get("enable_mutation", True)),
            safety=SafetyConfig.from_dict(safety_raw),
        )
        return cfg.clamp_and_validate()

    def clamp_and_validate(self) -> "RunConfig":
        if self.mode not in ("benchmark", "stress", "analyze"):
            self.mode = "benchmark"
        if self.corpus_source not in ("self_host", "procedural", "custom_path"):
            self.corpus_source = "procedural"
        if self.intensity not in ("balanced", "heavy", "extreme", "benchmark"):
            self.intensity = "heavy"
        self.scale_factor = max(1, min(self.scale_factor, 50))
        self.safety.clamp()
        return self
