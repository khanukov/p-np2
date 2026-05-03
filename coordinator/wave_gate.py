"""Wave-gate enforcement — Research Governance v0.1, MVP-0.5 (Phase E).

Reads `spec/wave_gate_thresholds.toml` at startup; exposes the
current Wave's `max_concurrent` worker cap and the per-Wave lease
defaults.  Refuses `GET /v1/task` assignments when the current
in-flight worker count is at the cap.

Phase E ships the GATE; automatic promotion (Wave N -> N+1) is a
post-MVP refinement: today the wave is set at startup via env
`AUTORESEARCH_INITIAL_WAVE` (default 0).  An operator promotes by
restarting with a higher initial wave once promotion_requirements
are demonstrably met.

API:
  WaveGate(thresholds_path).max_concurrent(wave_no)
                            .lease_seconds(wave_no)
                            .promotion_requirements(wave_no)
                            .can_assign(in_flight, wave_no) -> bool
                            .current_wave -> int
"""

from __future__ import annotations

import os
from dataclasses import dataclass
from pathlib import Path
from typing import Any

try:
    import tomllib  # type: ignore[import]
except ModuleNotFoundError:  # Python < 3.11
    tomllib = None  # type: ignore[assignment]


ROOT = Path(__file__).resolve().parent.parent
DEFAULT_THRESHOLDS_PATH = ROOT / "spec" / "wave_gate_thresholds.toml"


@dataclass(frozen=True)
class WaveConfig:
    name: str
    max_concurrent: int
    default_lease_seconds: int
    max_attempts_per_worker: int
    promotion_requirements: dict[str, Any]


class WaveGate:
    def __init__(self, thresholds_path: Path | None = None) -> None:
        self.thresholds_path = (
            thresholds_path if thresholds_path is not None
            else DEFAULT_THRESHOLDS_PATH)
        self._waves: dict[int, WaveConfig] = {}
        self._initial_wave = 0
        self._load()
        self._current_wave = int(
            os.environ.get("AUTORESEARCH_INITIAL_WAVE",
                           str(self._initial_wave)))

    def _load(self) -> None:
        if tomllib is None:
            # Fall back to a hard-coded Wave-0 config when running on
            # a Python < 3.11 system (CI runs 3.11+; this branch is
            # for local dev safety).
            self._waves = {
                0: WaveConfig(
                    name="Pilot Wave 0 (fallback)",
                    max_concurrent=10,
                    default_lease_seconds=1800,
                    max_attempts_per_worker=50,
                    promotion_requirements={},
                ),
            }
            self._initial_wave = 0
            return
        with self.thresholds_path.open("rb") as f:
            data = tomllib.load(f)
        default = data.get("default", {})
        self._initial_wave = int(default.get("initial_wave", 0))
        waves = data.get("waves", {})
        for wave_key, wave_data in waves.items():
            try:
                wave_no = int(wave_key)
            except (TypeError, ValueError):
                continue
            self._waves[wave_no] = WaveConfig(
                name=str(wave_data.get("name", f"Wave {wave_no}")),
                max_concurrent=int(wave_data.get("max_concurrent", 0)),
                default_lease_seconds=int(
                    wave_data.get("default_lease_seconds", 1800)),
                max_attempts_per_worker=int(
                    wave_data.get("max_attempts_per_worker", 0)),
                promotion_requirements=dict(
                    wave_data.get("promotion_requirements", {})),
            )

    @property
    def current_wave(self) -> int:
        return self._current_wave

    def set_current_wave(self, wave_no: int) -> None:
        if wave_no not in self._waves:
            raise ValueError(f"unknown wave: {wave_no}")
        self._current_wave = wave_no

    def config(self, wave_no: int | None = None) -> WaveConfig:
        wave = wave_no if wave_no is not None else self._current_wave
        if wave not in self._waves:
            raise KeyError(f"no wave config for wave {wave}")
        return self._waves[wave]

    def max_concurrent(self, wave_no: int | None = None) -> int:
        return self.config(wave_no).max_concurrent

    def lease_seconds(self, wave_no: int | None = None) -> int:
        return self.config(wave_no).default_lease_seconds

    def can_assign(
        self,
        in_flight: int,
        wave_no: int | None = None,
    ) -> tuple[bool, str | None]:
        cap = self.max_concurrent(wave_no)
        if in_flight >= cap:
            return (False,
                    f"Wave {wave_no or self._current_wave} cap reached: "
                    f"{in_flight}/{cap} in-flight assignments")
        return (True, None)
