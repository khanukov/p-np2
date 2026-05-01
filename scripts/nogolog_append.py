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
"""

from __future__ import annotations

import json
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

from validate_jsonl import validate_nogo  # noqa: E402

LOG_PATH = ROOT / "outputs" / "nogolog.jsonl"


def next_id() -> str:
    """Compute the next available NOGO-NNNNNN id."""
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
    return f"NOGO-{n + 1:06d}"


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

    if "id" not in data:
        data["id"] = next_id()
    if "created_at" not in data:
        data["created_at"] = (
            datetime.now(tz=timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"))

    errs = validate_nogo(data)
    if errs:
        print("[nogolog_append] FAIL: entry does not validate:",
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
