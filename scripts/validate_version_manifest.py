#!/usr/bin/env python3
"""
Version manifest cross-check —
Research Governance v0.1, Autoresearch MVP-0.1.4.

Confirms that `spec/version_manifest.toml::[snapshot]` is consistent
with the actual `[meta].spec_version` fields of the spec files it
references.  Drift fails the check.

For files whose snapshot row carries an explicit `target` path but
no expected `[meta].spec_version` (e.g. attack_suite, autoresearch_mvp,
critic_protocol — non-TOML or no [meta] block), the validator
verifies only that the `target` path EXISTS.  The version itself is
declarative.

Stdlib-only (uses tomllib, available since Python 3.11).

Exit codes:
  0   manifest matches all referenced files
  1   at least one mismatch / missing file
"""

from __future__ import annotations

import sys
from pathlib import Path

try:
    import tomllib  # type: ignore[import]
except ModuleNotFoundError:  # pragma: no cover
    print("[validate_version_manifest] FAIL: requires Python 3.11+",
          file=sys.stderr)
    sys.exit(2)

ROOT = Path(__file__).resolve().parent.parent

MANIFEST_PATH = ROOT / "spec" / "version_manifest.toml"


def _load_toml(path: Path) -> dict:
    with path.open("rb") as f:
        return tomllib.load(f)


def _meta_spec_version(path: Path) -> str | None:
    """Read `[meta].spec_version` from a TOML file, or None."""
    try:
        data = _load_toml(path)
    except FileNotFoundError:
        return None
    except tomllib.TOMLDecodeError:
        return None
    meta = data.get("meta")
    if not isinstance(meta, dict):
        return None
    v = meta.get("spec_version")
    if isinstance(v, str):
        return v
    return None


def main(argv: list[str]) -> int:
    if not MANIFEST_PATH.exists():
        print(f"[validate_version_manifest] FAIL: missing {MANIFEST_PATH}",
              file=sys.stderr)
        return 1

    try:
        manifest = _load_toml(MANIFEST_PATH)
    except tomllib.TOMLDecodeError as e:
        print(f"[validate_version_manifest] FAIL: TOML parse error: {e}",
              file=sys.stderr)
        return 1

    snapshot = manifest.get("snapshot")
    if not isinstance(snapshot, dict):
        print("[validate_version_manifest] FAIL: missing [snapshot]",
              file=sys.stderr)
        return 1

    fail = 0

    # Direct [meta].spec_version cross-checks for paired rows.
    direct_pairs = [
        ("target_spec_version", "target_spec_path"),
        ("known_guards_version", "known_guards_path"),
        ("provider_audit_registry_version",
         "provider_audit_registry_path"),
    ]
    for v_key, p_key in direct_pairs:
        if v_key not in snapshot or p_key not in snapshot:
            print(f"[validate_version_manifest] FAIL: snapshot missing"
                  f" {v_key!r} or {p_key!r}", file=sys.stderr)
            fail = 1
            continue
        expected = snapshot[v_key]
        rel = snapshot[p_key]
        full = ROOT / rel
        actual = _meta_spec_version(full)
        if actual is None:
            print(f"[validate_version_manifest] FAIL: cannot read"
                  f" [meta].spec_version from {rel}", file=sys.stderr)
            fail = 1
            continue
        if actual != expected:
            print(f"[validate_version_manifest] FAIL: {v_key} mismatch:"
                  f" manifest={expected!r} actual={actual!r} ({rel})",
                  file=sys.stderr)
            fail = 1
        else:
            print(f"[validate_version_manifest] OK   {v_key} = {expected}"
                  f" (matches {rel})")

    # Existence-only checks for snapshot.* sub-tables that carry a
    # `target` path but no [meta].spec_version on the other side.
    for sub_name, sub_val in snapshot.items():
        if not isinstance(sub_val, dict):
            continue
        target = sub_val.get("target")
        if not isinstance(target, str):
            continue
        full = ROOT / target
        if not full.exists():
            print(f"[validate_version_manifest] FAIL: snapshot.{sub_name}"
                  f".target does not exist: {target}", file=sys.stderr)
            fail = 1
        else:
            ver = sub_val.get("version", "?")
            print(f"[validate_version_manifest] OK   snapshot.{sub_name}"
                  f" version={ver} target={target} (exists)")

    if fail:
        return 1
    print("[validate_version_manifest] OK")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
