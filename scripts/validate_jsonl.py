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

NOGO_ID_RE = re.compile(r"^NOGO-[0-9]{6}$")
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

NOGO_ALLOWED = set(NOGO_REQUIRED) | {"supersedes", "notes"}
SURVIVOR_ALLOWED = set(SURVIVOR_REQUIRED) | {"notes"}


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
        # Caller supplied paths explicitly; default to NoGoLog shape
        # except when the path's basename is `survivor_history.jsonl`.
        targets: list[tuple[Path, Validator]] = []
        for arg in argv[1:]:
            p = Path(arg)
            if p.name == "survivor_history.jsonl":
                targets.append((p, validate_survivor))
            else:
                targets.append((p, validate_nogo))
    else:
        targets = [
            (Path("outputs/nogolog.jsonl"), validate_nogo),
            (Path("outputs/survivor_history.jsonl"), validate_survivor),
        ]
    ok = True
    for p, v in targets:
        if not validate_jsonl(p, v):
            ok = False
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
