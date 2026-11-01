"""Ordinary portable unit tests with explicit private DATA, never a Lean runner."""
import sys
if sys.flags.optimize:
    raise SystemExit("optimized unit runner rejected; workbench tests require ordinary Python")
import argparse
import os
from pathlib import Path
import tempfile
import unittest

PACKAGE = Path(__file__).resolve().parents[1]


def run(data):
    os.environ["CI_DATA_ROOT"] = str(data)
    suite = unittest.defaultTestLoader.discover(str(PACKAGE / "tests"))
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if result.wasSuccessful() else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data-root", type=Path, help="fresh private DATA directory; otherwise a temporary directory is used")
    args = parser.parse_args()
    if args.data_root is not None:
        path = args.data_root
        if path.exists() or path.is_symlink():
            raise ValueError("fresh private DATA directory required; existing paths are never reused")
        path.mkdir(parents=True, exist_ok=False)
        return run(path.resolve())
    with tempfile.TemporaryDirectory(prefix="conditional-ci-data-") as folder:
        return run(Path(folder))


if __name__ == "__main__":
    sys.exit(main())
