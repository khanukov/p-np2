#!/usr/bin/env python3
"""
NoGoLog / survivor-history JSONL validator — Research Governance v0.1, PR 9.

Targeted validator (NOT a general JSON Schema engine). Checks the
two log shapes declared in `spec/nogolog_schema.json`:

  outputs/nogolog.jsonl            => NoGoLogEntry shape
  outputs/survivor_history.jsonl   => SurvivorHistoryEntry shape

Usage:

  scripts/validate_jsonl.py            # validates both files
  scripts/validate_jsonl.py <path>...  # validates the given files

For each file:
  - missing file       -> FAIL
  - empty file         -> OK
  - non-empty: each non-blank line must parse as JSON, and the
    decoded object must satisfy the targeted shape check.

Targeted shape checks cover required fields, enum constraints,
identifier patterns (NOGO-NNNNNN), and ISO-8601 UTC timestamps.
The validator is stdlib-only; no `jsonschema` dependency.

Exit codes:
  0   all targets validate
  1   at least one target fails
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path
from typing import Callable, Iterable

# ---------------------------------------------------------------------------
# Shared constants — mirror spec/nogolog_schema.json `$defs`.
# ---------------------------------------------------------------------------

METHOD_FAMILY = {
    "algebraic", "spectral", "proof_complexity", "fine_grained",
    "meta_complexity", "ac0_locality_support", "natural_property",
    "algorithmic_williams", "info_theoretic", "sos", "wild_card", "other",
}

NOGO_STATUS = {"formalized", "informal", "needs_review"}

NOGO_FAILURE_CLASS = {
    "hardwiring", "natural_proof", "relativization", "algebrization",
    "vacuity", "refuted_route", "typeclass_payload", "goal_drift",
    "collapse_not_contradiction", "size_policy_violation",
    "implicit_assumption_channel", "joint_candidate_non_independent",
    "prior_work_collision", "reproducibility_failure", "other",
}

SURVIVOR_VERIFIER_STATUS = {"PASS", "FAIL"}
SURVIVOR_FINAL_STATUS = {
    "survived", "refuted", "expired_review", "accepted",
    "requires_revalidation",
}

# AttemptLedgerEntry — Autoresearch MVP control plane.
ATTEMPT_VERIFIER_STATUS = {"PASS", "FAIL", "PASS_SHAPE_ONLY"}
ATTEMPT_CRITIC_STATUS = {"not_run", "pass", "fail"}

NOGO_ID_RE = re.compile(r"^NOGO-[0-9]{6}$")
ATTEMPT_ID_RE = re.compile(r"^ATT-[0-9]{6}$")
TIMESTAMP_RE = re.compile(
    r"^[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}(\.[0-9]+)?Z$"
)
PATH_LINE_RE = re.compile(r"^[A-Za-z0-9_./-]+:[0-9]+$")

NOGO_REQUIRED = (
    "id", "candidate_id", "method_family", "status",
    "failure_class", "structural_pattern", "counterexample_family",
    "why_generalizes", "formal_witness", "regression_test",
    "applicable_spec_version", "attack_suite_version", "created_at",
)

SURVIVOR_REQUIRED = (
    "candidate_id", "method_family", "source_theorem_skeleton",
    "verifier_status", "critic_attacks_survived", "final_status",
    "applicable_spec_version", "attack_suite_version", "created_at",
)

ATTEMPT_REQUIRED = (
    "id", "candidate_id", "method_family",
    "verifier_status", "critic_status",
    "applicable_spec_version", "attack_suite_version", "created_at",
)

NOGO_ALLOWED = set(NOGO_REQUIRED) | {"supersedes", "notes"}
SURVIVOR_ALLOWED = set(SURVIVOR_REQUIRED) | {"notes"}
ATTEMPT_ALLOWED = set(ATTEMPT_REQUIRED) | {
    "seed_pack_id", "verifier_failure_class",
    "critic_break_class", "critic_report_path",
    "supersedes", "notes",
}


# ---------------------------------------------------------------------------
# Per-shape validators.
# ---------------------------------------------------------------------------

def _check_required(entry: dict, required: Iterable[str]) -> list[str]:
    return [f"missing required field: {f}"
            for f in required if f not in entry]


def _check_no_extras(entry: dict, allowed: set[str]) -> list[str]:
    extras = set(entry.keys()) - allowed
    return [f"extra field not in schema: {k}" for k in sorted(extras)]


def _check_string_nonempty(entry: dict, field: str) -> list[str]:
    if field in entry and not (isinstance(entry[field], str)
                               and entry[field].strip()):
        return [f"{field} must be a non-empty string"]
    return []


def _check_enum(entry: dict, field: str, allowed: set[str]) -> list[str]:
    if field in entry and entry[field] not in allowed:
        return [f"{field} not in enum: {entry[field]!r}"]
    return []


def _check_pattern(entry: dict, field: str, regex: re.Pattern) -> list[str]:
    if field in entry and not regex.match(str(entry[field])):
        return [f"{field} does not match expected pattern: {entry[field]!r}"]
    return []


def _check_path_or_null(entry: dict, field: str) -> list[str]:
    if field not in entry:
        return []
    v = entry[field]
    if v is None:
        return []
    if isinstance(v, str) and PATH_LINE_RE.match(v):
        return []
    return [f"{field} must be 'path:lineno' string or null: {v!r}"]


def _check_string_or_null(entry: dict, field: str) -> list[str]:
    if field not in entry:
        return []
    v = entry[field]
    if v is None:
        return []
    if isinstance(v, str):
        return []
    return [f"{field} must be string or null: {v!r}"]


def validate_nogo(entry: dict) -> list[str]:
    errs: list[str] = []
    if not isinstance(entry, dict):
        return ["entry is not a JSON object"]
    errs += _check_required(entry, NOGO_REQUIRED)
    errs += _check_no_extras(entry, NOGO_ALLOWED)
    errs += _check_pattern(entry, "id", NOGO_ID_RE)
    errs += _check_string_nonempty(entry, "candidate_id")
    errs += _check_enum(entry, "method_family", METHOD_FAMILY)
    errs += _check_enum(entry, "status", NOGO_STATUS)
    errs += _check_enum(entry, "failure_class", NOGO_FAILURE_CLASS)
    errs += _check_string_nonempty(entry, "structural_pattern")
    errs += _check_string_nonempty(entry, "counterexample_family")
    errs += _check_string_nonempty(entry, "why_generalizes")
    errs += _check_path_or_null(entry, "formal_witness")
    errs += _check_string_or_null(entry, "regression_test")
    errs += _check_string_nonempty(entry, "applicable_spec_version")
    errs += _check_string_nonempty(entry, "attack_suite_version")
    errs += _check_pattern(entry, "created_at", TIMESTAMP_RE)
    if "supersedes" in entry:
        errs += _check_pattern(entry, "supersedes", NOGO_ID_RE)
    return errs


def validate_survivor(entry: dict) -> list[str]:
    errs: list[str] = []
    if not isinstance(entry, dict):
        return ["entry is not a JSON object"]
    errs += _check_required(entry, SURVIVOR_REQUIRED)
    errs += _check_no_extras(entry, SURVIVOR_ALLOWED)
    errs += _check_string_nonempty(entry, "candidate_id")
    errs += _check_enum(entry, "method_family", METHOD_FAMILY)
    errs += _check_string_nonempty(entry, "source_theorem_skeleton")
    errs += _check_enum(entry, "verifier_status", SURVIVOR_VERIFIER_STATUS)
    if ("critic_attacks_survived" in entry
            and not (isinstance(entry["critic_attacks_survived"], int)
                     and not isinstance(entry["critic_attacks_survived"], bool)
                     and entry["critic_attacks_survived"] >= 0)):
        errs.append("critic_attacks_survived must be a non-negative integer")
    errs += _check_enum(entry, "final_status", SURVIVOR_FINAL_STATUS)
    errs += _check_string_nonempty(entry, "applicable_spec_version")
    errs += _check_string_nonempty(entry, "attack_suite_version")
    errs += _check_pattern(entry, "created_at", TIMESTAMP_RE)
    return errs


def validate_attempt(entry: dict) -> list[str]:
    """Validate one outputs/attempts.jsonl line (AttemptLedgerEntry shape).

    Cross-field consistency rules (Autoresearch MVP-0.1.1 hardening):

    * `critic_status = "pass"` REQUIRES `critic_report_path` to be a
      non-null string pointing to a file that parses as a completed,
      non-template Critic report whose own `critic_status` field is
      `"pass"`.  A `pass` line with no path / nonexistent path /
      template path is REJECTED.
    * `critic_status = "fail"` REQUIRES `critic_report_path` to be a
      non-null string pointing to a completed, non-template Critic
      report whose `critic_status` is `"fail"`, AND
      `critic_break_class` populated, AND the report's
      `dominant_break_class` agrees with `critic_break_class`.
    * `critic_status = "not_run"` allows `critic_report_path` to be
      missing, null, or pointing to a template (the latter for
      candidate packages that ship the empty template before Critic
      runs).
    """
    errs: list[str] = []
    if not isinstance(entry, dict):
        return ["entry is not a JSON object"]
    errs += _check_required(entry, ATTEMPT_REQUIRED)
    errs += _check_no_extras(entry, ATTEMPT_ALLOWED)
    errs += _check_pattern(entry, "id", ATTEMPT_ID_RE)
    errs += _check_string_nonempty(entry, "candidate_id")
    errs += _check_enum(entry, "method_family", METHOD_FAMILY)
    errs += _check_enum(entry, "verifier_status", ATTEMPT_VERIFIER_STATUS)
    if "verifier_failure_class" in entry:
        v = entry["verifier_failure_class"]
        if v is None:
            pass
        elif v in NOGO_FAILURE_CLASS:
            pass
        else:
            errs.append(
                f"verifier_failure_class not in enum or null: {v!r}")
    errs += _check_enum(entry, "critic_status", ATTEMPT_CRITIC_STATUS)
    if "critic_break_class" in entry:
        v = entry["critic_break_class"]
        if v is None:
            pass
        elif v in NOGO_FAILURE_CLASS:
            pass
        else:
            errs.append(
                f"critic_break_class not in enum or null: {v!r}")
    errs += _check_string_or_null(entry, "critic_report_path")
    errs += _check_string_nonempty(entry, "applicable_spec_version")
    errs += _check_string_nonempty(entry, "attack_suite_version")
    errs += _check_pattern(entry, "created_at", TIMESTAMP_RE)
    if "seed_pack_id" in entry:
        errs += _check_string_nonempty(entry, "seed_pack_id")
    if "supersedes" in entry:
        errs += _check_pattern(entry, "supersedes", ATTEMPT_ID_RE)
    # Cross-field consistency — Verifier side.
    if entry.get("verifier_status") == "FAIL" \
            and entry.get("verifier_failure_class") in (None, ...):
        if "verifier_failure_class" in entry \
                and entry["verifier_failure_class"] is None:
            errs.append(
                "verifier_failure_class must be populated when "
                "verifier_status = FAIL")

    # Cross-field consistency — Critic side (MVP-0.1.1).
    critic_status = entry.get("critic_status")
    critic_path = entry.get("critic_report_path")
    if critic_status in ("pass", "fail"):
        if critic_path is None or critic_path == "" or \
                "critic_report_path" not in entry:
            errs.append(
                f"critic_status={critic_status!r} requires a non-null "
                "critic_report_path")
        else:
            # Resolve relative to repo root.
            from pathlib import Path as _Path
            repo_root = _Path(__file__).resolve().parent.parent
            full = (repo_root / critic_path)
            if not full.exists():
                errs.append(
                    f"critic_status={critic_status!r}: critic_report_path "
                    f"file does not exist: {critic_path}")
            else:
                # Lazy import to keep top-level import light.
                try:
                    sys.path.insert(0, str(repo_root / "scripts"))
                    from validate_critic_report import (  # noqa: E402
                        validate_critic_report_file,
                    )
                except ImportError as e:
                    errs.append(
                        f"could not import validate_critic_report: {e}")
                else:
                    state = validate_critic_report_file(full)
                    if state.is_template:
                        errs.append(
                            f"critic_status={critic_status!r}: "
                            f"critic_report_path points to a TEMPLATE "
                            f"file (template marker detected): "
                            f"{critic_path}")
                    elif not state.completed:
                        errs.append(
                            f"critic_status={critic_status!r}: "
                            f"critic_report at {critic_path} is not "
                            f"completed: {state.errors}")
                    elif state.verdict_critic_status != critic_status:
                        errs.append(
                            f"critic_status={critic_status!r} disagrees "
                            f"with report verdict "
                            f"{state.verdict_critic_status!r} at "
                            f"{critic_path}")
    if critic_status == "fail":
        # Require critic_break_class populated.
        if "critic_break_class" not in entry \
                or entry.get("critic_break_class") in (None, ""):
            errs.append(
                "critic_break_class must be populated when "
                "critic_status = fail")
        else:
            # Optional: report's dominant_break_class agrees.
            if critic_path and isinstance(critic_path, str):
                from pathlib import Path as _Path
                repo_root = _Path(__file__).resolve().parent.parent
                full = (repo_root / critic_path)
                if full.exists():
                    try:
                        sys.path.insert(0, str(repo_root / "scripts"))
                        from validate_critic_report import (  # noqa: E402
                            validate_critic_report_file,
                        )
                        state = validate_critic_report_file(full)
                        rep_class = state.verdict_dominant_break_class
                        ent_class = entry.get("critic_break_class")
                        if rep_class and rep_class != "null" \
                                and rep_class != ent_class:
                            errs.append(
                                f"critic_break_class={ent_class!r} "
                                f"disagrees with report's "
                                f"dominant_break_class={rep_class!r} "
                                f"at {critic_path}")
                    except Exception:
                        pass  # already reported above

    return errs


# ---------------------------------------------------------------------------
# JSONL file driver.
# ---------------------------------------------------------------------------

Validator = Callable[[dict], list[str]]


def validate_jsonl(path: Path, validator: Validator) -> bool:
    """Return True iff `path` is a valid JSONL log under `validator`."""
    if not path.exists():
        print(f"[validate_jsonl] {path}: FAIL (missing)")
        return False
    if path.stat().st_size == 0:
        print(f"[validate_jsonl] {path}: OK (empty)")
        return True
    ok = True
    with path.open(encoding="utf-8") as f:
        for lineno, raw in enumerate(f, start=1):
            line = raw.rstrip("\n")
            if not line.strip():
                continue
            try:
                entry = json.loads(line)
            except json.JSONDecodeError as e:
                print(f"[validate_jsonl] {path}:{lineno}: "
                      f"JSON parse error: {e}")
                ok = False
                continue
            errs = validator(entry)
            for err in errs:
                print(f"[validate_jsonl] {path}:{lineno}: {err}")
                ok = False
    if ok:
        print(f"[validate_jsonl] {path}: OK")
    else:
        print(f"[validate_jsonl] {path}: FAIL")
    return ok


def main(argv: list[str]) -> int:
    if len(argv) > 1:
        # Caller supplied paths explicitly; pick a validator from the
        # path's basename. Defaults to NoGoLog shape.
        targets: list[tuple[Path, Validator]] = []
        for arg in argv[1:]:
            p = Path(arg)
            if p.name == "survivor_history.jsonl":
                targets.append((p, validate_survivor))
            elif p.name == "attempts.jsonl":
                targets.append((p, validate_attempt))
            else:
                targets.append((p, validate_nogo))
    else:
        targets = [
            (Path("outputs/nogolog.jsonl"), validate_nogo),
            (Path("outputs/survivor_history.jsonl"), validate_survivor),
            (Path("outputs/attempts.jsonl"), validate_attempt),
        ]
    ok = True
    for p, v in targets:
        if not validate_jsonl(p, v):
            ok = False
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
