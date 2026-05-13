"""Coordinator canonical-ledger write path —
Research Governance v0.1, MVP-0.2.

The Coordinator does NOT introduce a new ledger format.  When it
accepts a result submission, it:

  1. Validates the AttemptLedgerEntry payload via
     `scripts/validate_jsonl.py::validate_attempt`.
  2. Pipes the payload through `scripts/attempts_append.py` (which
     applies the MVP-0.1.8 Phase A flock and assigns the
     ATT-NNNNNN id atomically).
  3. If the submission carries a NoGoLogEntry (critic_status=fail),
     pipes it through `scripts/nogolog_append.py`.
  4. If a SurvivorHistoryEntry is included, pipes it through
     `scripts/survivor_append.py`.

The coordinator therefore reuses the Phase A locking primitives
verbatim; it does NOT bypass them.  Future Phase F (sharded
coordinator) will replace this subprocess pipe with a shared-
backend write, but the lock-discipline contract is preserved.
"""

from __future__ import annotations

import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
APPEND_ATTEMPTS = ROOT / "scripts" / "attempts_append.py"
APPEND_NOGOLOG = ROOT / "scripts" / "nogolog_append.py"
APPEND_SURVIVOR = ROOT / "scripts" / "survivor_append.py"


class LedgerWriteError(RuntimeError):
    """Raised when a canonical-ledger append fails (validation,
    flock conflict, etc.).  The HTTP layer translates this into
    a 4xx/5xx response."""

    def __init__(self, kind: str, stderr: str) -> None:
        super().__init__(f"{kind}: {stderr.strip()}")
        self.kind = kind
        self.stderr = stderr


def append_attempt(payload: dict) -> str:
    """Append an AttemptLedgerEntry; return the assigned ATT-NNNNNN id."""
    return _append_via(APPEND_ATTEMPTS, payload, kind="attempts")


def append_nogolog(payload: dict) -> str:
    """Append a NoGoLogEntry; return the assigned NOGO-NNNNNN id."""
    return _append_via(APPEND_NOGOLOG, payload, kind="nogolog")


def append_survivor(payload: dict) -> str:
    """Append a SurvivorHistoryEntry; survivor_append.py prints a
    human-readable line, not an id; we return that line."""
    return _append_via(APPEND_SURVIVOR, payload, kind="survivor")


def _append_via(script: Path, payload: dict, kind: str) -> str:
    if not script.exists():
        raise LedgerWriteError(kind, f"writer script missing: {script}")
    proc = subprocess.run(
        ["python3", str(script)],
        input=json.dumps(payload).encode("utf-8"),
        capture_output=True,
        timeout=60,
    )
    if proc.returncode != 0:
        raise LedgerWriteError(kind, proc.stderr.decode("utf-8", "replace"))
    return proc.stdout.decode("utf-8", "replace").strip()
