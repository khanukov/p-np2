#!/usr/bin/env python3
"""Promotion-evaluator tests — Research Governance v0.1, MVP-0.5.6.

v0.4.2 Track C4.  Three cases:

  1. Empty ledger: evaluator refuses to promote to Wave 1.
  2. Synthetic ledger satisfying min_clean_cycles + critic_pass +
     critic_fail: evaluator allows promotion to Wave 1, EXCEPT for
     `role_gate_enforced=true` which is operator-attestable and
     therefore listed as unmet.
  3. FORCE override emits all three loud signals (stderr WARNING,
     audit-log append, metric counter consumed by server.py).

The audit-file written by case (3) is cleaned up at the end of
the test so scripts/check.sh Step 12.k stays green.
"""

from __future__ import annotations

import io
import json
import os
import shutil
import subprocess
import sys
import tempfile
from contextlib import redirect_stderr
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from coordinator import promotion_evaluator as pe


def run_test_empty_ledger_refuses_wave_1(tmp: Path) -> None:
    attempts = tmp / "attempts.jsonl"
    attempts.write_text("")
    nogo = tmp / "nogolog.jsonl"
    nogo.write_text("")
    can, unmet = pe.evaluate(
        target_wave=1,
        thresholds_path=ROOT / "spec" / "wave_gate_thresholds.toml",
        attempts_path=attempts,
        nogolog_path=nogo,
    )
    assert can is False, f"empty ledger must NOT unlock Wave 1; got can={can}"
    keys = [u.split(":", 1)[0] for u in unmet]
    assert "min_clean_cycles" in keys, unmet
    assert "role_gate_enforced" in keys, unmet
    print("[test_promotion_evaluator] OK   empty ledger -> Wave 1 refused "
          "with explicit unmet reasons")


def run_test_synthetic_ledger_satisfies_numeric_reqs(tmp: Path) -> None:
    """A synthetic ledger with 30 clean cycles + 1 pass + 1 fail
    satisfies the numeric requirements for Wave 1.  The
    `role_gate_enforced` flag stays operator-attestable, so the
    evaluator still says NOT promotable — but the unmet list is
    just that one flag.
    """
    attempts = tmp / "attempts.jsonl"
    rows = []
    # 30 clean cycles (PASS_SHAPE_ONLY + critic_status in pass/fail).
    for i in range(30):
        c = "pass" if i % 2 == 0 else "fail"
        row = {
            "id": f"ATT-{i+1:06d}",
            "candidate_id": f"cand_{i:03d}",
            "method_family": "ac0_locality_support",
            "verifier_status": "PASS_SHAPE_ONLY",
            "critic_status": c,
            "applicable_spec_version": "0.1.0",
            "attack_suite_version": "0.1.0",
            "created_at": "2026-05-05T12:00:00Z",
        }
        if c == "fail":
            row["critic_break_class"] = "hardwiring"
        rows.append(row)
    attempts.write_text("\n".join(json.dumps(r) for r in rows) + "\n")
    nogo = tmp / "nogolog.jsonl"
    nogo.write_text("")  # no Rule-16 slip
    can, unmet = pe.evaluate(
        target_wave=1,
        thresholds_path=ROOT / "spec" / "wave_gate_thresholds.toml",
        attempts_path=attempts,
        nogolog_path=nogo,
    )
    assert can is False, (
        f"synthetic ledger should still be blocked by role_gate_enforced; "
        f"got can={can}, unmet={unmet}")
    # Only role_gate_enforced should be unmet for Wave 1.
    assert len(unmet) == 1, unmet
    assert "role_gate_enforced" in unmet[0], unmet
    print("[test_promotion_evaluator] OK   synthetic ledger satisfies "
          "numeric reqs; only role_gate_enforced remains operator-attestable")


def run_test_force_override_emits_all_loud_signals(tmp: Path) -> None:
    """FORCE override emits stderr WARN + audit log append.  The
    metric counter is incremented by server.py on consume; we
    don't exercise that here directly (it's covered by the
    server-level integration when the e2e harness is updated).
    """
    audit_path = tmp / "wave_promotion_audit.jsonl"
    # Emit the warning into a captured stderr buffer.
    buf = io.StringIO()
    with redirect_stderr(buf):
        pe.emit_force_warning(
            target_wave=2,
            unmet=["min_clean_cycles: ledger reports 0, requirement is >= 300"],
        )
    err = buf.getvalue()
    assert "WARNING" in err, err
    assert "AUTORESEARCH_PROMOTION_FORCE" in err, err
    assert "wave 2" in err, err
    # Append-only audit record.
    pe.append_forced_promotion_audit_record(
        target_wave=2,
        coordinator_git_commit="0123456789abcdef0123456789abcdef01234567",
        unmet_reasons=[
            "min_clean_cycles: ledger reports 0, requirement is >= 300"],
        operator_note="test-marker",
        audit_path=audit_path,
    )
    assert audit_path.exists()
    line = audit_path.read_text(encoding="utf-8").strip()
    rec = json.loads(line)
    assert rec["target_wave"] == 2, rec
    assert rec["operator_note"] == "test-marker", rec
    assert rec["unmet_reasons"], rec
    print("[test_promotion_evaluator] OK   FORCE override emits stderr WARN "
          "+ audit-log entry")


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="promotion_evaluator_test_") as tmp:
        tmp_path = Path(tmp)
        run_test_empty_ledger_refuses_wave_1(tmp_path)
        run_test_synthetic_ledger_satisfies_numeric_reqs(tmp_path)
        run_test_force_override_emits_all_loud_signals(tmp_path)
    print("[test_promotion_evaluator] OK (3/3 cases passed)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
