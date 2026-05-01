#!/usr/bin/env python3
"""
Parse a candidate's `manifest.toml` and emit JSON on stdout.

Usage:

  scripts/parse_manifest.py <candidate-dir>

Uses Python 3.11+ stdlib `tomllib`. No external dependencies.

Exit codes:

  0   manifest parsed, JSON emitted
  1   manifest missing or unparseable
  2   wrong arguments
"""

from __future__ import annotations

import json
import sys
import tomllib
from pathlib import Path


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: scripts/parse_manifest.py <candidate-dir>",
              file=sys.stderr)
        return 2
    path = Path(sys.argv[1]) / "manifest.toml"
    if not path.is_file():
        print(json.dumps({"error": f"{path} not found"}))
        return 1
    try:
        with path.open("rb") as f:
            data = tomllib.load(f)
    except tomllib.TOMLDecodeError as e:
        print(json.dumps({"error": f"{path}: {e}"}))
        return 1
    json.dump(data, sys.stdout, indent=2, default=str)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
