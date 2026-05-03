#!/usr/bin/env python3
"""
Append a NoGoLog entry to outputs/nogolog.jsonl.

Reads a JSON object on stdin, validates it against the NoGoLog
shape from `spec/nogolog_schema.json` (via
`scripts/validate_jsonl.py::validate_nogo`), assigns a monotonic
`id` (`NOGO-NNNNNN`) if absent, fills `created_at` with the current
UTC time if absent, and appends the canonicalised entry to
`outputs/nogolog.jsonl`.

Exits 0 on success (prints the assigned id to stdout); exits 1 if
the entry fails validation, in which case the log is unchanged.

Usage:

  echo '{ ... }' | scripts/nogolog_append.py

Per `RESEARCH_CONSTITUTION.md` Rule 9, NoGoLog is append-only:
existing entries are never edited.  Corrections are added as new
entries with the optional `supersedes` field pointing to the
original.

Concurrency model (MVP-0.1.8 / Phase A):

  Multiple workers MAY invoke this script concurrently.  The
  read-then-write next-id allocation is wrapped in an exclusive
  fcntl.flock(LOCK_EX) on a sibling lockfile
  `outputs/nogolog.jsonl.lock` so two simultaneous calls do NOT
  produce duplicate NOGO-NNNNNN ids.  See spec/concurrency_model.md
  for the full locking contract.
"""

from __future__ import annotations

import fcntl
import json
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

from validate_jsonl import validate_nogo  # noqa: E402

LOG_PATH = ROOT / "outputs" / "nogolog.jsonl"
LOCK_PATH = ROOT / "outputs" / "nogolog.jsonl.lock"


def _scan_max_id() -> int:
    """Return the largest NOGO-NNNNNN suffix already in the ledger.

    Caller MUST hold the exclusive lock on LOCK_PATH; otherwise a
    racing writer can append between this scan and the eventual
    write, breaking monotonicity.
    """
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
            if isinstance(v, str) and v.startswith("NOGO-"):
                try:
                    n = max(n, int(v[5:]))
                except ValueError:
                    pass
    return n


def main() -> int:
    try:
        data = json.load(sys.stdin)
    except json.JSONDecodeError as e:
        print(f"[nogolog_append] FAIL: stdin is not valid JSON: {e}",
              file=sys.stderr)
        return 1
    if not isinstance(data, dict):
        print("[nogolog_append] FAIL: stdin must be a JSON object",
              file=sys.stderr)
        return 1

    LOG_PATH.parent.mkdir(parents=True, exist_ok=True)
    LOCK_PATH.touch(exist_ok=True)
    with LOCK_PATH.open("a+", encoding="utf-8") as lockf:
        fcntl.flock(lockf.fileno(), fcntl.LOCK_EX)
        try:
            if "id" not in data:
                data["id"] = f"NOGO-{_scan_max_id() + 1:06d}"
            if "created_at" not in data:
                data["created_at"] = (
                    datetime.now(tz=timezone.utc)
                    .strftime("%Y-%m-%dT%H:%M:%SZ"))

            errs = validate_nogo(data)
            if errs:
                print("[nogolog_append] FAIL: entry does not validate:",
                      file=sys.stderr)
                for err in errs:
                    print(f"  - {err}", file=sys.stderr)
                return 1

            with LOG_PATH.open("a", encoding="utf-8") as f:
                f.write(json.dumps(data, ensure_ascii=False,
                                   sort_keys=True) + "\n")
        finally:
            fcntl.flock(lockf.fileno(), fcntl.LOCK_UN)

    print(data["id"])
    return 0


if __name__ == "__main__":
    sys.exit(main())
