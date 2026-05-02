#!/usr/bin/env python3
"""
Append an AttemptLedger entry to outputs/attempts.jsonl.

Each entry records one Verifier+Critic cycle on a single candidate.
The ledger is the central artifact for the Autoresearch MVP control
plane (Research Governance v0.1, Autoresearch MVP-3): every
parallel-search attempt produces exactly one append-only line here.

Reads a JSON object on stdin, validates it against the
AttemptLedgerEntry shape from `spec/nogolog_schema.json` (via
`scripts/validate_jsonl.py::validate_attempt`), assigns a monotonic
`id` (`ATT-NNNNNN`) if absent, fills `created_at` with the current
UTC time if absent, and appends the canonicalised entry to
`outputs/attempts.jsonl`.

Exits 0 on success (prints the assigned id to stdout); exits 1 if
the entry fails validation, in which case the ledger is unchanged.

Usage:

  echo '{ ... }' | scripts/attempts_append.py

Append-only invariant (Research Constitution Rule 9): existing
entries are never edited.  Corrections are added as new entries
with the optional `supersedes` field pointing to the original.
"""

from __future__ import annotations

import json
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

from validate_jsonl import validate_attempt  # noqa: E402

LOG_PATH = ROOT / "outputs" / "attempts.jsonl"


def next_id() -> str:
    """Compute the next available ATT-NNNNNN id."""
    n = 0
    if LOG_PATH.exists() and LOG_PATH.stat().st_size > 0:
        for raw in LOG_PATH.read_text(encoding="utf-8").splitlines():
            line = raw.strip()
            if not line:
                continue
            try:
                e = json.loads(line)
            except json.JSONDecodeError:
                continue
            v = e.get("id", "")
            if isinstance(v, str) and v.startswith("ATT-"):
                try:
                    n = max(n, int(v[4:]))
                except ValueError:
                    pass
    return f"ATT-{n + 1:06d}"


def main() -> int:
    try:
        data = json.load(sys.stdin)
    except json.JSONDecodeError as e:
        print(f"[attempts_append] FAIL: stdin is not valid JSON: {e}",
              file=sys.stderr)
        return 1
    if not isinstance(data, dict):
        print("[attempts_append] FAIL: stdin must be a JSON object",
              file=sys.stderr)
        return 1

    if "id" not in data:
        data["id"] = next_id()
    if "created_at" not in data:
        data["created_at"] = (
            datetime.now(tz=timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"))

    errs = validate_attempt(data)
    if errs:
        print("[attempts_append] FAIL: entry does not validate:",
              file=sys.stderr)
        for err in errs:
            print(f"  - {err}", file=sys.stderr)
        return 1

    LOG_PATH.parent.mkdir(parents=True, exist_ok=True)
    with LOG_PATH.open("a", encoding="utf-8") as f:
        f.write(json.dumps(data, ensure_ascii=False, sort_keys=True) + "\n")
    print(data["id"])
    return 0


if __name__ == "__main__":
    sys.exit(main())
