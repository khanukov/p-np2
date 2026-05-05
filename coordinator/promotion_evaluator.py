"""Wave promotion evaluator — Research Governance v0.1, Autoresearch MVP-0.5.6.

v0.4.2 Track C4.  Reads `outputs/attempts.jsonl` and
`outputs/nogolog.jsonl`, compares against
`spec/wave_gate_thresholds.toml::[waves.N.promotion_requirements]`,
and reports whether wave N+1 (or wave N) is unlocked yet.

The evaluator is consulted by `coordinator/wave_gate.py::_resolve_initial_wave`:
when an operator sets `AUTORESEARCH_INITIAL_WAVE=2`, the evaluator
must say `can_promote(2) == True` OR the operator must set the
LOUD `AUTORESEARCH_PROMOTION_FORCE=true` override.

`AUTORESEARCH_PROMOTION_FORCE` is preserved as an emergency
override but every use:

  1. emits `autoresearch_wave_promotion_forced_total{wave=N}` metric
     (incremented by the wave_gate when the override is consumed);
  2. writes a stderr WARNING line with explicit
     "FORCE override used; promotion_requirements NOT verified by
     coordinator" wording on every coordinator start;
  3. appends a forced-promotion record to
     `outputs/wave_promotion_audit.jsonl` (an append-only file with
     its own Phase-A flock sibling).

`scripts/check.sh` Step 12.k asserts the audit file is empty (or
contains only test-marked entries) during CI.
"""

from __future__ import annotations

import fcntl
import json
import os
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

try:
    import tomllib  # type: ignore[import]
except ModuleNotFoundError:  # pragma: no cover
    tomllib = None  # type: ignore[assignment]


ROOT = Path(__file__).resolve().parent.parent
DEFAULT_THRESHOLDS_PATH = ROOT / "spec" / "wave_gate_thresholds.toml"
DEFAULT_ATTEMPTS_PATH = ROOT / "outputs" / "attempts.jsonl"
DEFAULT_NOGOLOG_PATH = ROOT / "outputs" / "nogolog.jsonl"
DEFAULT_PROMOTION_AUDIT_PATH = ROOT / "outputs" / "wave_promotion_audit.jsonl"


def _read_thresholds(path: Path) -> dict:
    if tomllib is None or not path.exists():
        return {}
    try:
        with path.open("rb") as f:
            return tomllib.load(f)
    except Exception:
        return {}


def _read_jsonl(path: Path) -> list[dict]:
    if not path.exists():
        return []
    out: list[dict] = []
    try:
        with path.open(encoding="utf-8") as f:
            for raw in f:
                line = raw.strip()
                if not line:
                    continue
                try:
                    entry = json.loads(line)
                except Exception:
                    continue
                if isinstance(entry, dict):
                    out.append(entry)
    except OSError:
        return []
    return out


def _summarise_attempts(entries: list[dict]) -> dict[str, Any]:
    """Aggregate the ledger metrics needed by promotion_requirements."""
    clean_cycles = 0
    critic_pass = 0
    critic_fail = 0
    seed_packs: set[str] = set()
    false_pass = 0
    total_with_critic_verdict = 0
    for e in entries:
        v = e.get("verifier_status")
        c = e.get("critic_status")
        if v in ("PASS", "PASS_SHAPE_ONLY") and c in ("pass", "fail"):
            clean_cycles += 1
        if c == "pass":
            critic_pass += 1
            total_with_critic_verdict += 1
            # A "false pass" in this evaluator is an attempt where
            # the verifier passed but the critic later flagged a
            # break (i.e. the candidate would have advanced under
            # verifier-only).  We approximate this with the
            # presence of a critic_break_class on a pass entry,
            # which only happens in pathological legacy data; in
            # the canonical flow `pass` and `break_class` are
            # mutually exclusive.
            if e.get("critic_break_class"):
                false_pass += 1
        elif c == "fail":
            critic_fail += 1
            total_with_critic_verdict += 1
        sp = e.get("seed_pack_id")
        if isinstance(sp, str) and sp:
            seed_packs.add(sp)
    fpr = (false_pass / total_with_critic_verdict
           if total_with_critic_verdict else 0.0)
    return {
        "min_clean_cycles": clean_cycles,
        "min_critic_pass_observed": critic_pass,
        "min_critic_fail_observed": critic_fail,
        "min_distinct_seed_packs": len(seed_packs),
        "max_false_pass_rate": fpr,
    }


def _summarise_nogolog(entries: list[dict]) -> dict[str, Any]:
    """Detect Rule-16 / typeclass-payload slips in the NoGoLog."""
    rule16_slip = any(
        e.get("failure_class") in ("typeclass_payload",
                                   "implicit_assumption_channel")
        for e in entries
    )
    return {
        "no_rule16_slip": not rule16_slip,
    }


def evaluate(
    target_wave: int,
    *,
    thresholds_path: Path = DEFAULT_THRESHOLDS_PATH,
    attempts_path: Path = DEFAULT_ATTEMPTS_PATH,
    nogolog_path: Path = DEFAULT_NOGOLOG_PATH,
) -> tuple[bool, list[str]]:
    """Return `(can_promote, unmet_reasons)`.

    `can_promote` is True iff every requirement in
    `[waves.<target_wave>.promotion_requirements]` is satisfied by
    the current ledger / nogolog.  `unmet_reasons` enumerates each
    failed requirement in human-readable form.

    Requirements not implemented by this evaluator (e.g.
    `worker_scratch_isolation_active = true` for Wave 3) are
    treated as deferred-to-operator and are NOT auto-satisfied;
    they appear in `unmet_reasons` so the operator must
    `AUTORESEARCH_PROMOTION_FORCE` to override.
    """
    data = _read_thresholds(thresholds_path)
    waves = data.get("waves", {}) or {}
    wave_block = waves.get(str(target_wave)) or waves.get(target_wave) or {}
    reqs = (wave_block.get("promotion_requirements") or {})
    if not reqs:
        return (True, [])

    attempts = _read_jsonl(attempts_path)
    nogo = _read_jsonl(nogolog_path)
    attempt_summary = _summarise_attempts(attempts)
    nogo_summary = _summarise_nogolog(nogo)
    unmet: list[str] = []

    for key, expected in reqs.items():
        if key in ("min_clean_cycles", "min_critic_pass_observed",
                   "min_critic_fail_observed", "min_distinct_seed_packs"):
            actual = int(attempt_summary.get(key, 0))
            if actual < int(expected):
                unmet.append(
                    f"{key}: ledger reports {actual}, "
                    f"requirement is >= {expected}")
        elif key == "max_false_pass_rate":
            actual_fpr = float(attempt_summary.get("max_false_pass_rate", 0.0))
            if actual_fpr > float(expected):
                unmet.append(
                    f"max_false_pass_rate: ledger reports "
                    f"{actual_fpr:.6f}, requirement is "
                    f"<= {float(expected):.6f}")
        elif key == "no_rule16_slip":
            actual_no_slip = bool(nogo_summary.get("no_rule16_slip", True))
            if bool(expected) and not actual_no_slip:
                unmet.append(
                    "no_rule16_slip: nogolog records a "
                    "typeclass_payload / implicit_assumption_channel "
                    "entry, drops back to previous wave")
        elif key in ("role_gate_enforced",
                     "worker_scratch_isolation_active",
                     "distributed_build_cache_active",
                     "mtbf_coordinator_hours",
                     "sharded_coordinator_active",
                     "result_stream_processor_active",
                     "nightly_survivor_promotion"):
            # Operator-attestable flags the coordinator cannot verify
            # automatically.  Treat as unmet so the operator must
            # explicitly FORCE.
            unmet.append(
                f"{key}: requirement is operator-attestable "
                f"(expected {expected!r}); coordinator has no "
                f"automatic check")
        else:
            unmet.append(
                f"{key}: unknown requirement key in "
                f"promotion_requirements (expected {expected!r}); "
                f"add a handler in promotion_evaluator.py")

    return (len(unmet) == 0, unmet)


def append_forced_promotion_audit_record(
    target_wave: int,
    coordinator_git_commit: str,
    unmet_reasons: list[str],
    operator_note: str = "",
    audit_path: Path = DEFAULT_PROMOTION_AUDIT_PATH,
) -> None:
    """Append a record to the wave_promotion_audit.jsonl ledger
    every time AUTORESEARCH_PROMOTION_FORCE is consumed.  Phase-A
    flock-protected via the `.lock` sibling.

    The record schema is documented in
    `spec/wave_promotion_audit_schema.json`.
    """
    entry = {
        "forced_at": datetime.now(tz=timezone.utc).strftime(
            "%Y-%m-%dT%H:%M:%SZ"),
        "target_wave": int(target_wave),
        "coordinator_git_commit": coordinator_git_commit or "",
        "unmet_reasons": list(unmet_reasons),
        "operator_note": operator_note or "",
    }
    audit_path.parent.mkdir(parents=True, exist_ok=True)
    lock_path = audit_path.with_suffix(audit_path.suffix + ".lock")
    with lock_path.open("a") as lockf:
        try:
            fcntl.flock(lockf.fileno(), fcntl.LOCK_EX)
            with audit_path.open("a", encoding="utf-8") as f:
                f.write(json.dumps(entry, sort_keys=True) + "\n")
        finally:
            fcntl.flock(lockf.fileno(), fcntl.LOCK_UN)


def emit_force_warning(target_wave: int, unmet: list[str]) -> None:
    """Write a stderr WARNING that the operator clearly sees on
    every coordinator start when FORCE is consumed."""
    sys.stderr.write(
        "[wave_gate] WARNING: AUTORESEARCH_PROMOTION_FORCE consumed "
        f"to start at wave {target_wave}.  promotion_requirements "
        "NOT verified by coordinator.  Unmet:\n")
    for r in unmet:
        sys.stderr.write(f"[wave_gate] WARNING:   - {r}\n")
    sys.stderr.write(
        "[wave_gate] WARNING: This event is recorded in "
        "outputs/wave_promotion_audit.jsonl.  CI step 12.k will "
        "fail until the audit file is reset to empty.\n")
    sys.stderr.flush()
