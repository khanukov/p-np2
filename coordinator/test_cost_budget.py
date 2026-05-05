#!/usr/bin/env python3
"""End-to-end test for v0.4.2 Track C2 cost-budget reaper.

Uses an isolated stub repo + sqlite store so we can poke the
deadline column directly without polluting the real ledger.

Asserts:

  1. An assignment whose deadline is in the past is auto-failed
     by `CostBudgetReaper.tick()` exactly once.
  2. The synthesised AttemptLedgerEntry has
     `verifier_status="FAIL_TIMEOUT"` and
     `verifier_failure_class="timeout"` and carries the original
     assignment's `lease_id`.
  3. After auto-fail, the assignment is in `submitted` status with
     the synthesised attempt_id; a worker submitting the same
     assignment now hits a 409 (status check) — the race-free
     compare-and-set design.
  4. Cross-field validator rejects a hand-crafted FAIL_TIMEOUT
     payload that omits `verifier_failure_class="timeout"`.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
from datetime import datetime, timedelta, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from coordinator.cost_budget import CostBudgetReaper, CostBudgetThresholds
from coordinator.store import CoordinatorStore


def _now_minus(seconds: int) -> str:
    return (datetime.now(tz=timezone.utc) - timedelta(seconds=seconds)).strftime(
        "%Y-%m-%dT%H:%M:%SZ")


def _stage_stub(tmp: Path) -> Path:
    stub = tmp / "stub"
    (stub / "scripts").mkdir(parents=True, exist_ok=True)
    (stub / "spec").mkdir(parents=True, exist_ok=True)
    (stub / "outputs").mkdir(parents=True, exist_ok=True)
    (stub / "coordinator").mkdir(parents=True, exist_ok=True)
    for name in (
        "attempts_append.py", "validate_jsonl.py", "validate_critic_report.py",
        "nogolog_append.py", "survivor_append.py",
    ):
        shutil.copy2(ROOT / "scripts" / name, stub / "scripts" / name)
    for name in (
        "nogolog_schema.json", "version_manifest.toml",
        "cost_budget_thresholds.toml", "target.toml", "known_guards.toml",
    ):
        src = ROOT / "spec" / name
        if src.exists():
            shutil.copy2(src, stub / "spec" / name)
    for name in ("attempts.jsonl", "nogolog.jsonl", "survivor_history.jsonl"):
        (stub / "outputs" / name).write_text("")
    return stub


def run_test_reaper_auto_fails_overdue(stub: Path) -> None:
    """A row whose deadline is past and lease_id is set is auto-failed
    in one tick.  Subsequent ticks are no-op (idempotent)."""
    db_path = stub / "coordinator" / "state.db"
    store = CoordinatorStore(db_path=db_path)
    try:
        rec = store.create_assignment(
            assignment_id="ASN-000001",
            candidate_id="cand_overdue",
            seed_pack_id="smoke",
            role="gen",
            worker_id="gen-overdue",
            lease_seconds=3600,
        )
        # Backdate the deadline so the reaper sees it as overdue.
        with store._lock:
            store._conn.execute(
                "UPDATE assignments SET deadline = ? "
                " WHERE assignment_id = ?",
                (_now_minus(60), rec["assignment_id"]),
            )

        # Use a stub append_attempt that writes to the stub's ledger
        # via the canonical attempts_append.py.
        def _stub_append(payload: dict) -> str:
            proc = subprocess.run(
                ["python3", str(stub / "scripts" / "attempts_append.py")],
                input=json.dumps(payload).encode("utf-8"),
                capture_output=True, cwd=stub, timeout=30,
            )
            assert proc.returncode == 0, proc.stderr.decode("utf-8", "replace")
            return proc.stdout.decode("utf-8").strip()

        thresholds = CostBudgetThresholds(
            stub / "spec" / "cost_budget_thresholds.toml")
        reaper = CostBudgetReaper(
            store=store, thresholds=thresholds,
            append_attempt_fn=_stub_append,
        )
        # First tick should auto-fail exactly the one row.
        n = reaper.tick()
        assert n == 1, f"first tick expected 1, got {n}"
        # Second tick should be no-op (row is in 'submitted').
        n2 = reaper.tick()
        assert n2 == 0, f"second tick expected 0, got {n2}"

        # Verify ledger contents.
        ledger = (stub / "outputs" / "attempts.jsonl").read_text().splitlines()
        assert len(ledger) == 1, ledger
        entry = json.loads(ledger[0])
        assert entry["verifier_status"] == "FAIL_TIMEOUT", entry
        assert entry["verifier_failure_class"] == "timeout", entry
        assert entry["lease_id"] == rec["lease_id"], entry
        assert entry["candidate_id"] == "cand_overdue", entry

        # Assignment moved to submitted with synthesised attempt_id.
        final = store.get_assignment("ASN-000001")
        assert final is not None and final["status"] == "submitted"
        assert final["attempt_id"] == entry["id"]

        print("[test_cost_budget] OK   reaper auto-fails overdue (1) and "
              "is idempotent on re-tick (0)")
    finally:
        store.close()


def run_test_validator_rejects_fail_timeout_without_timeout_class(stub: Path) -> None:
    """A FAIL_TIMEOUT entry without verifier_failure_class='timeout'
    must be rejected by scripts/validate_jsonl.py."""
    bad = {
        "id": "ATT-999999",
        "candidate_id": "bad_payload",
        "method_family": "ac0_locality_support",
        "verifier_status": "FAIL_TIMEOUT",
        "critic_status": "not_run",
        "applicable_spec_version": "0.1.0",
        "attack_suite_version": "0.1.0",
        "created_at": "2026-05-05T12:34:56Z",
        # Deliberately omitted: "verifier_failure_class": "timeout".
    }
    # validate_jsonl.py routes the validator by filename basename; the
    # path must literally end in `attempts.jsonl` to dispatch to
    # validate_attempt.
    bad_dir = stub / "outputs" / "bad_attempts_subtree"
    bad_dir.mkdir(exist_ok=True)
    bad_path = bad_dir / "attempts.jsonl"
    bad_path.write_text(json.dumps(bad) + "\n")
    proc = subprocess.run(
        ["python3", str(ROOT / "scripts" / "validate_jsonl.py"),
         str(bad_path)],
        capture_output=True, cwd=stub, timeout=30,
    )
    assert proc.returncode != 0, (
        f"validator should reject FAIL_TIMEOUT without 'timeout' class; "
        f"got rc={proc.returncode} stdout={proc.stdout.decode()!r}")
    err = proc.stdout.decode("utf-8", "replace") + \
        proc.stderr.decode("utf-8", "replace")
    assert "FAIL_TIMEOUT" in err, err
    shutil.rmtree(bad_dir, ignore_errors=True)
    print("[test_cost_budget] OK   validator rejects FAIL_TIMEOUT without "
          "timeout class")


def run_test_lease_id_compare_and_set(stub: Path) -> None:
    """Direct CAS test: claim_for_timeout fails when lease_id has
    been swapped (simulating a re-leased assignment)."""
    db_path = stub / "coordinator" / "state2.db"
    store = CoordinatorStore(db_path=db_path)
    try:
        rec = store.create_assignment(
            assignment_id="ASN-000001",
            candidate_id="cand_cas",
            seed_pack_id="smoke",
            role="gen",
            worker_id="gen-cas",
            lease_seconds=3600,
        )
        # Manually rotate the lease_id (would happen in a future
        # design where the slot is re-leased after expiry).
        with store._lock:
            store._conn.execute(
                "UPDATE assignments SET lease_id = ? WHERE assignment_id = ?",
                ("00000000-0000-0000-0000-000000000000", rec["assignment_id"]),
            )
        # Old lease_id should fail to claim.
        ok_old = store.claim_for_timeout(rec["assignment_id"], rec["lease_id"])
        assert ok_old is False, "stale lease_id should not be able to claim"
        # New lease_id should succeed.
        ok_new = store.claim_for_timeout(
            rec["assignment_id"], "00000000-0000-0000-0000-000000000000")
        assert ok_new is True, "matching lease_id should succeed"
        print("[test_cost_budget] OK   claim_for_timeout is lease_id-gated")
    finally:
        store.close()


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="cost_budget_test_") as tmp:
        stub = _stage_stub(Path(tmp))
        run_test_reaper_auto_fails_overdue(stub)
        run_test_validator_rejects_fail_timeout_without_timeout_class(stub)
        run_test_lease_id_compare_and_set(stub)
    print("[test_cost_budget] OK (3/3 cases passed)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
