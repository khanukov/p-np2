"""Wrapper around ``./scripts/check.sh``.

Used as the basic-adequacy gate: when a Stage 5 Lean L0 probe is
attempted (out of scope for the machine itself but useful for
operator follow-ups), the wrapper invokes the existing repository
check and returns a structured result.
"""

from __future__ import annotations

import subprocess
from dataclasses import dataclass
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
CHECK_SH = REPO_ROOT / "scripts" / "check.sh"


@dataclass
class CheckResult:
    returncode: int
    stdout: str
    stderr: str
    ok: bool


def run_check() -> CheckResult:
    """Run ``./scripts/check.sh`` and capture the outcome.

    The caller is responsible for ensuring the lean toolchain is
    available in PATH.
    """
    if not CHECK_SH.exists():
        return CheckResult(
            returncode=127,
            stdout="",
            stderr=f"check.sh not found at {CHECK_SH}",
            ok=False,
        )
    proc = subprocess.run(
        ["bash", str(CHECK_SH)],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
    )
    return CheckResult(
        returncode=proc.returncode,
        stdout=proc.stdout,
        stderr=proc.stderr,
        ok=(proc.returncode == 0),
    )


if __name__ == "__main__":
    r = run_check()
    print(f"check.sh exit code: {r.returncode}")
    print("ok" if r.ok else "FAILED")
