#!/usr/bin/env bash
# Target-lock guard — Research Governance v0.1, PR 11.
#
# Belt-and-suspenders complement to `pnp3/Tests/TargetLockProbe.lean`:
# the Lean-side compile-time assertions catch structural drifts of
# `ResearchGapWitness` at build time; this shell guard catches drifts
# that elaborate but should still fail (e.g. a phantom axiom anywhere
# in the source tree, or removal of the probe file from the build
# glob), and serves as a regression-watch in CI logs.
#
# Three checks:
#
#   (A) ResearchGapWitness shape (regex on the trust-root file):
#       structure ResearchGapWitness ... where
#         dagSeparation : ...
#       — the `dagSeparation` field must appear immediately after
#       the `structure` line.
#
#   (B) Phantom axiom (defensive duplicate of PR 1's
#       `check_doc_honesty.sh` Part A):
#       no top-level `axiom P_ne_NP_unconditional` anywhere in
#       pnp3/pnp4.
#
#   (C) Probe glob registration: `Tests.TargetLockProbe` must be
#       listed in `lakefile.lean`'s `lean_lib PnP3` glob, otherwise
#       the Lean-side compile-time assertions are silently skipped.

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

if ! command -v rg >/dev/null 2>&1; then
  echo "[target-lock] Missing required dependency: rg (ripgrep)." >&2
  exit 127
fi

fail=0

# ---------------------------------------------------------------------------
# (A) ResearchGapWitness structural check.
# ---------------------------------------------------------------------------

echo "[target-lock] (A) ResearchGapWitness shape"

gap_file="pnp3/Magnification/UnconditionalResearchGap.lean"
if [[ ! -f "${gap_file}" ]]; then
  echo "[target-lock] FAIL: ${gap_file} not found"
  fail=1
elif ! rg -n -U \
        'structure[[:space:]]+ResearchGapWitness[^\n]*\n[[:space:]]*dagSeparation[[:space:]]*:[[:space:]]*ResearchGapTarget' \
        "${gap_file}" >/dev/null 2>&1; then
  echo "[target-lock] FAIL: ResearchGapWitness shape is not"
  echo "[target-lock]       structure ResearchGapWitness ... where"
  echo "[target-lock]         dagSeparation : ResearchGapTarget"
  echo "[target-lock]       in ${gap_file}."
  rg -n -U 'structure[[:space:]]+ResearchGapWitness[^\n]*\n[^\n]*' "${gap_file}" \
    | head -8 | sed 's/^/[target-lock]   /'
  fail=1
fi

# Also assert that `ResearchGapTarget` is the alias for
# `NP_not_subset_PpolyDAG` (the canonical bridge target). Multi-line
# `def`-form is accepted as well as single-line `abbrev`.
if ! rg -n -U \
        '(?:def|abbrev)[[:space:]]+ResearchGapTarget[[:space:]]*(?::[[:space:]]*Prop)?[[:space:]]*(?::=|=)[[:space:]\n]+ComplexityInterfaces\.NP_not_subset_PpolyDAG' \
        "${gap_file}" >/dev/null 2>&1; then
  echo "[target-lock] FAIL: ResearchGapTarget alias is not"
  echo "[target-lock]       (def|abbrev) ResearchGapTarget := ComplexityInterfaces.NP_not_subset_PpolyDAG"
  echo "[target-lock]       in ${gap_file}."
  fail=1
fi

# ---------------------------------------------------------------------------
# (B) Phantom axiom defensive check.
# ---------------------------------------------------------------------------

echo "[target-lock] (B) phantom axiom defensive scan"

axiom_hits="$(rg -n '^[[:space:]]*axiom[[:space:]]+P_ne_NP_unconditional\b' \
                -g'*.lean' pnp3 pnp4 2>/dev/null || true)"
if [[ -n "${axiom_hits}" ]]; then
  echo "[target-lock] FAIL: phantom 'axiom P_ne_NP_unconditional' detected:"
  echo "${axiom_hits}"
  echo "[target-lock]   This is also caught by check_doc_honesty.sh Part A;"
  echo "[target-lock]   target-lock duplicates the check defensively."
  fail=1
fi

# ---------------------------------------------------------------------------
# (C) TargetLockProbe must be in the PnP3 build glob.
# ---------------------------------------------------------------------------

echo "[target-lock] (C) TargetLockProbe is registered in lakefile.lean"

if ! rg -n '^[[:space:]]*Glob\.one[[:space:]]+`Tests\.TargetLockProbe' \
        lakefile.lean >/dev/null 2>&1; then
  echo "[target-lock] FAIL: \`Tests.TargetLockProbe\` is not in"
  echo "[target-lock]       lakefile.lean's lean_lib PnP3 glob."
  echo "[target-lock]       Without it, the Lean-side compile-time"
  echo "[target-lock]       assertions are silently skipped by lake build."
  fail=1
fi

# ---------------------------------------------------------------------------
# Result.
# ---------------------------------------------------------------------------

if [[ "${fail}" -ne 0 ]]; then
  echo
  echo "[target-lock] FAIL"
  echo "[target-lock]   See RESEARCH_CONSTITUTION.md Rule 0 (frozen target)"
  echo "[target-lock]       and spec/target.toml::[target] / [final]."
  exit 1
fi

echo "[target-lock] OK"
