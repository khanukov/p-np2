"""Cost-budget reaper — Research Governance v0.1, Autoresearch MVP-0.5.6.

v0.4.2 Track C2.  A daemon thread that periodically scans for
overdue assignments and synthesises FAIL_TIMEOUT AttemptLedgerEntries.
The compare-and-set lease_id discipline (per
`spec/coordinator_protocol.md`) ensures a worker submitting at the
same wall-clock instant the reaper transitions the row never
produces a duplicate ledger entry.

Threading model
---------------

* One `CostBudgetReaper` per coordinator process.
* `start()` spawns a daemon `threading.Thread` that calls `tick()`
  every `reaper.tick_seconds` (default 60 s).
* Per tick, every assignment with `status='assigned'`,
  `deadline < now`, and a non-empty `lease_id` is offered to
  `_auto_fail_one`.  That helper does:

    1. `claim_for_timeout(assignment_id, lease_id)` (atomic UPDATE)
       — if 0 rows, the worker beat us: skip.
    2. Synthesise an AttemptLedgerEntry payload with
       `verifier_status="FAIL_TIMEOUT"`,
       `verifier_failure_class="timeout"`, and the same
       `lease_id` as the assignment.  Append via
       `coordinator.ledger.append_attempt`.
    3. `finalize_timed_out(assignment_id, attempt_id)` to move the
       row to `submitted` with the synthesised `attempt_id`.

* Metric: `autoresearch_attempts_auto_failed_total{reason="timeout"}`.

Configuration is read from `spec/cost_budget_thresholds.toml` at
startup; the reaper does NOT re-read on the fly (operator restarts
the coordinator after changing thresholds).
"""

from __future__ import annotations

import threading
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable, Optional

from .ledger import LedgerWriteError, append_attempt
from .store import CoordinatorStore

try:
    import tomllib  # type: ignore[import]
except ModuleNotFoundError:  # pragma: no cover
    tomllib = None  # type: ignore[assignment]


DEFAULTS = {
    "role.gen.default_minutes": 30,
    "role.gen.hard_cap_minutes": 90,
    "role.crit.default_minutes": 15,
    "role.crit.hard_cap_minutes": 45,
    "role.rev.default_minutes": 60,
    "role.rev.hard_cap_minutes": 240,
    "reaper.tick_seconds": 60,
}


class CostBudgetThresholds:
    """Parse `spec/cost_budget_thresholds.toml` into a flat dict.

    Falls back to `DEFAULTS` for any missing key so a partial TOML
    cannot crash the reaper at startup.
    """

    def __init__(self, path: Path | None) -> None:
        self._values: dict[str, int] = dict(DEFAULTS)
        if path is None or tomllib is None or not path.exists():
            return
        try:
            with path.open("rb") as f:
                data = tomllib.load(f)
        except Exception:  # pragma: no cover — degrade silently
            return
        for role in ("gen", "crit", "rev"):
            sect = (data.get("role", {}) or {}).get(role, {}) or {}
            if "default_minutes" in sect:
                self._values[f"role.{role}.default_minutes"] = int(
                    sect["default_minutes"])
            if "hard_cap_minutes" in sect:
                self._values[f"role.{role}.hard_cap_minutes"] = int(
                    sect["hard_cap_minutes"])
        reaper = data.get("reaper", {}) or {}
        if "tick_seconds" in reaper:
            self._values["reaper.tick_seconds"] = int(reaper["tick_seconds"])

    def get(self, key: str) -> int:
        return self._values.get(key, DEFAULTS[key])


def _now_iso() -> str:
    return datetime.now(tz=timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


class CostBudgetReaper:
    """Daemon thread that auto-FAIL_TIMEOUTs overdue assignments."""

    def __init__(
        self,
        store: CoordinatorStore,
        thresholds: CostBudgetThresholds,
        *,
        spec_version: str = "0.1.0",
        attack_suite_version: str = "0.1.0",
        coordinator_git_commit: str = "",
        on_autofail: Optional[Callable[[dict], None]] = None,
        append_attempt_fn: Callable[[dict], str] = append_attempt,
    ) -> None:
        self.store = store
        self.thresholds = thresholds
        self.spec_version = spec_version
        self.attack_suite_version = attack_suite_version
        self.coordinator_git_commit = coordinator_git_commit
        self.on_autofail = on_autofail
        # Injectable for tests so we don't actually subprocess to the
        # canonical writer when running under a stub.
        self._append_attempt = append_attempt_fn
        self._stop = threading.Event()
        self._thread: threading.Thread | None = None

    # ------------------------------------------------------------------
    # Lifecycle.
    # ------------------------------------------------------------------

    def start(self) -> None:
        if self._thread is not None and self._thread.is_alive():
            return
        self._stop.clear()
        self._thread = threading.Thread(
            target=self._loop, name="cost-budget-reaper", daemon=True)
        self._thread.start()

    def stop(self, timeout: float = 5.0) -> None:
        self._stop.set()
        t = self._thread
        if t is not None:
            t.join(timeout=timeout)
        self._thread = None

    def _loop(self) -> None:
        period = max(1, self.thresholds.get("reaper.tick_seconds"))
        # First tick happens immediately; subsequent ticks honour
        # `period`.  Operators expect a freshly started coordinator
        # to clean up overdue rows from a previous incarnation
        # without waiting `period` seconds.
        while not self._stop.is_set():
            try:
                self.tick()
            except Exception:
                # Reaper failures must NEVER propagate to the
                # coordinator's request handlers.  Swallow and
                # retry on the next tick.
                pass
            if self._stop.wait(timeout=period):
                return

    # ------------------------------------------------------------------
    # The actual auto-fail logic.
    # ------------------------------------------------------------------

    def tick(self) -> int:
        """Run one sweep.  Returns the number of assignments
        auto-failed in this tick (mostly for tests; the production
        loop discards the count)."""
        now_iso = _now_iso()
        overdue = self.store.find_overdue_for_autofail(now_iso)
        n = 0
        for row in overdue:
            if self._auto_fail_one(row):
                n += 1
        return n

    def _auto_fail_one(self, row: dict) -> bool:
        """Auto-fail one overdue assignment.  Returns True if this
        reaper instance owned the transition."""
        if not self.store.claim_for_timeout(
                row["assignment_id"], row["lease_id"]):
            # Worker beat us, or another reaper claimed it: skip.
            return False

        # We own the row.  Synthesise the AttemptLedgerEntry.  Any
        # failure below leaves the row in `timed_out`; the next
        # tick is idempotent because `find_overdue_for_autofail`
        # filters on `status='assigned'`, so we won't double-claim.
        # Operator alarm comes via the metric, not via re-attempt.
        payload = {
            "candidate_id": row["candidate_id"],
            "method_family": "ac0_locality_support",
            "seed_pack_id": row["seed_pack_id"],
            "verifier_status": "FAIL_TIMEOUT",
            "verifier_failure_class": "timeout",
            "critic_status": "not_run",
            "applicable_spec_version": self.spec_version,
            "attack_suite_version": self.attack_suite_version,
            "created_at": _now_iso(),
            "lease_id": row["lease_id"],
            "notes": (
                "auto-FAIL_TIMEOUT after lease expiry "
                "(coordinator cost_budget reaper)"),
        }
        if self.coordinator_git_commit:
            payload["git_commit"] = self.coordinator_git_commit

        try:
            attempt_id = self._append_attempt(payload)
        except LedgerWriteError:
            # Leave the row in 'timed_out'; next tick won't re-claim.
            # Operator inspects via /v1/metrics + jsonl validator.
            return False

        # Move to terminal `submitted` state.  Should always succeed
        # since we own the row.
        if not self.store.finalize_timed_out(
                row["assignment_id"], attempt_id):
            return False

        if self.on_autofail is not None:
            try:
                self.on_autofail({
                    "assignment_id": row["assignment_id"],
                    "attempt_id": attempt_id,
                    "role": row["role"],
                })
            except Exception:
                pass
        return True
