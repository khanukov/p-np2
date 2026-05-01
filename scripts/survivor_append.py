#!/usr/bin/env python3
"""
Append a survivor-history entry to outputs/survivor_history.jsonl.

Reads a JSON object on stdin, validates it against the
SurvivorHistoryEntry shape from `spec/nogolog_schema.json` (via
`scripts/validate_jsonl.py::validate_survivor`), fills `created_at`
with the current UTC time if absent, and appends the entry to
`outputs/survivor_history.jsonl`.

Exits 0 on success; exits 1 if the entry fails validation, in which
case the log is unchanged.

Usage:

  echo '{ ... }' | scripts/survivor_append.py

Survivor history records candidates that pass the verifier but later
fail the Critic, plus accepted candidates and revalidations (Rule
14).  The log is append-only.
"""

from __future__ import annotations

import json
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

from validate_jsonl import validate_survivor  # noqa: E402

LOG_PATH = ROOT / "outputs" / "survivor_history.jsonl"


def main() -> int:
    try:
        data = json.load(sys.stdin)
    except json.JSONDecodeError as e:
        print(f"[survivor_append] FAIL: stdin is not valid JSON: {e}",
              file=sys.stderr)
        return 1
    if not isinstance(data, dict):
        print("[survivor_append] FAIL: stdin must be a JSON object",
              file=sys.stderr)
        return 1

    if "created_at" not in data:
        data["created_at"] = (
            datetime.now(tz=timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"))

    errs = validate_survivor(data)
    if errs:
        print("[survivor_append] FAIL: entry does not validate:",
              file=sys.stderr)
        for err in errs:
            print(f"  - {err}", file=sys.stderr)
        return 1

    LOG_PATH.parent.mkdir(parents=True, exist_ok=True)
    with LOG_PATH.open("a", encoding="utf-8") as f:
        f.write(json.dumps(data, ensure_ascii=False, sort_keys=True) + "\n")
    print(f"[survivor_append] OK: appended candidate_id={data['candidate_id']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
