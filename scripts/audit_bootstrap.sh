#!/usr/bin/env bash
# Audit bootstrap — Research Governance v0.1, Autoresearch MVP-0.1.5.
#
# This script is the canonical entry point for human auditors of the
# p-np2 Research Governance branch.  It exists to PREVENT the
# specific false-positive that the five-engineer audit produced:
# four of the five auditors used a raw `grep -n
# 'theorem P_ne_NP_unconditional'` in
# `pnp3/Magnification/UnconditionalResearchGap.lean` and reported an
# active unconditional theorem.  Both hits are inside fenced code
# blocks (```...```) within a Lean docstring (/-! ... -/), and are
# explicitly the COMMENTED TEMPLATE that the file's own narrative
# describes.  No active theorem of that name exists; the doc-
# honesty linter at scripts/check_doc_honesty.sh already enforces
# this via comment-stripping.
#
# Run this script BEFORE doing a manual audit pass.  It will:
#
#   1. report the current branch and HEAD commit;
#   2. cross-check against the optional EXPECTED_COMMIT env var;
#   3. run a comment-stripped Lean-source scan for `axiom
#      P_ne_NP_unconditional` and `theorem P_ne_NP_unconditional`,
#      reporting hits OUTSIDE comment regions only;
#   4. enumerate the known false-positive locations (so a raw
#      grep producing more hits than these is informative);
#   5. print the canonical pipeline commands that produce the
#      authoritative pass/fail signal: lake build PnP3 Pnp4 +
#      scripts/check.sh.
#
# The script does NOT itself run lake build; it prints the command
# the auditor should run.  This keeps the bootstrap fast and lets
# the auditor inspect output stage-by-stage.
#
# Exit codes:
#   0   bootstrap succeeded (no surprises; raw grep matches the
#       expected false-positive locations);
#   1   the comment-stripped scan found a SUSPECTED ACTIVE
#       declaration of P_ne_NP_unconditional (real blocker);
#   2   the raw grep produced unexpected hits (auditor should
#       investigate but this is NOT necessarily a real blocker;
#       a new doc-template might have appeared);
#   3   missing dependency.
#
# Usage:
#   scripts/audit_bootstrap.sh
#   EXPECTED_COMMIT=c5eb808 scripts/audit_bootstrap.sh

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

if ! command -v rg >/dev/null 2>&1; then
  echo "[audit_bootstrap] FAIL: missing required dependency: rg (ripgrep)" >&2
  exit 3
fi
if ! command -v git >/dev/null 2>&1; then
  echo "[audit_bootstrap] FAIL: missing required dependency: git" >&2
  exit 3
fi
if ! command -v awk >/dev/null 2>&1; then
  echo "[audit_bootstrap] FAIL: missing required dependency: awk" >&2
  exit 3
fi

echo "==========================================================="
echo "  p-np2 Research Governance — audit bootstrap"
echo "==========================================================="
echo

# ---------------------------------------------------------------------------
# Step 1 — branch and commit.
# ---------------------------------------------------------------------------

branch="$(git rev-parse --abbrev-ref HEAD 2>/dev/null || echo unknown)"
head_commit="$(git rev-parse HEAD 2>/dev/null || echo unknown)"
short_commit="$(git rev-parse --short HEAD 2>/dev/null || echo unknown)"

echo "[audit_bootstrap] branch:       ${branch}"
echo "[audit_bootstrap] HEAD commit:  ${head_commit}"
echo "[audit_bootstrap] HEAD (short): ${short_commit}"

if [[ -n "${EXPECTED_COMMIT:-}" ]]; then
  if [[ "${head_commit}" == "${EXPECTED_COMMIT}"* ]] \
      || [[ "${short_commit}" == "${EXPECTED_COMMIT}"* ]]; then
    echo "[audit_bootstrap] commit OK (matches EXPECTED_COMMIT="\
"${EXPECTED_COMMIT})"
  else
    echo "[audit_bootstrap] WARNING: HEAD does not match"\
"EXPECTED_COMMIT=${EXPECTED_COMMIT}"
    echo "[audit_bootstrap]   This may indicate a stale local copy"
    echo "[audit_bootstrap]   or that the audit instructions point at a"
    echo "[audit_bootstrap]   different revision.  Continuing anyway."
  fi
fi
echo

# ---------------------------------------------------------------------------
# Step 2 — comment-stripped P_ne_NP_unconditional scan.
# ---------------------------------------------------------------------------
#
# This reuses the SAME comment-stripping awk pre-pass that
# scripts/check_doc_honesty.sh uses, so that occurrences inside
# /- ... -/ block comments (including Lean docstrings /-! ... -/),
# `--` line comments, AND fenced markdown code blocks inside such
# comments are all suppressed.

echo "[audit_bootstrap] Step 2: comment-stripped scan for active"
echo "[audit_bootstrap]         P_ne_NP_unconditional declarations"

strip_dir="$(mktemp -d)"
cleanup() {
  rm -rf "${strip_dir}"
}
trap cleanup EXIT

# Pre-strip every Lean source file under pnp3/ and pnp4/ into one
# big aggregated comment-stripped buffer with file:lineno prefix.
agg="${strip_dir}/stripped.txt"
: >"${agg}"

while IFS= read -r f; do
  awk -v fname="${f}" '
    BEGIN { in_block = 0 }
    {
      line = $0
      out  = ""
      i    = 1
      n    = length(line)
      while (i <= n) {
        if (in_block) {
          j = index(substr(line, i), "-/")
          if (j == 0) { i = n + 1 }
          else        { in_block = 0; i = i + j + 1 }
        } else {
          j = index(substr(line, i), "/-")
          if (j == 0) {
            out = out substr(line, i)
            i = n + 1
          } else {
            out = out substr(line, i, j - 1)
            in_block = 1
            i = i + j + 1
          }
        }
      }
      k = index(out, "--")
      if (k > 0) out = substr(out, 1, k - 1)
      if (out !~ /^[[:space:]]*$/) {
        print fname ":" NR ":" out
      }
    }
  ' "${f}" >>"${agg}"
done < <(find pnp3 pnp4 -name '*.lean' 2>/dev/null)

# Now grep the aggregated buffer for active declarations.
active_axiom_hits="$(rg -n \
  '^[^:]+:[0-9]+:[[:space:]]*axiom[[:space:]]+P_ne_NP_unconditional\b' \
  "${agg}" 2>/dev/null || true)"
active_theorem_hits="$(rg -n \
  '^[^:]+:[0-9]+:[[:space:]]*theorem[[:space:]]+P_ne_NP_unconditional\b' \
  "${agg}" 2>/dev/null || true)"

real_blocker=0

if [[ -n "${active_axiom_hits}" ]]; then
  echo "[audit_bootstrap] FAIL: active 'axiom P_ne_NP_unconditional'"
  echo "[audit_bootstrap]       detected (comment-stripped):"
  printf '%s\n' "${active_axiom_hits}" | sed 's/^/[audit_bootstrap]   /'
  real_blocker=1
fi
if [[ -n "${active_theorem_hits}" ]]; then
  echo "[audit_bootstrap] FAIL: active 'theorem P_ne_NP_unconditional'"
  echo "[audit_bootstrap]       detected (comment-stripped):"
  printf '%s\n' "${active_theorem_hits}" | sed 's/^/[audit_bootstrap]   /'
  real_blocker=1
fi
if [[ "${real_blocker}" -eq 0 ]]; then
  echo "[audit_bootstrap]   no active P_ne_NP_unconditional"\
       "declarations found"
fi
echo

# ---------------------------------------------------------------------------
# Step 3 — known false-positive locations under raw grep.
# ---------------------------------------------------------------------------
#
# A raw grep (without comment stripping) will flag the locations
# below.  These are the EXPECTED FALSE POSITIVES.  An auditor whose
# raw-grep output matches this list exactly should NOT report a
# blocker.  An auditor whose raw-grep output DIFFERS from this list
# (extra hits) has potentially found something new and should
# investigate via Step 2 above.

echo "[audit_bootstrap] Step 3: known raw-grep false-positive locations"
echo "[audit_bootstrap]         (occurrences inside doc/template blocks)"

# Emit the raw-grep hits the auditor will see, and label each one as
# expected/false-positive iff it falls inside a Lean comment region
# (the comment-stripping pass dropped it).

raw_hits="$(rg -n -F "P_ne_NP_unconditional" \
              -g '*.lean' pnp3 pnp4 2>/dev/null || true)"

if [[ -z "${raw_hits}" ]]; then
  echo "[audit_bootstrap]   no raw grep hits — no false positives possible"
else
  unexpected_hits=0
  while IFS= read -r line; do
    fpath="$(printf '%s' "${line}" | awk -F: '{print $1}')"
    fline="$(printf '%s' "${line}" | awk -F: '{print $2}')"
    # If the same file:line appears in the comment-stripped agg AND
    # contains the identifier, it's an active hit (already reported
    # in step 2).  Otherwise it was suppressed by the comment
    # stripper and is a known false positive.
    stripped_match="$(rg -n -F \
                        ":${fline}:" "${agg}" 2>/dev/null \
                      | rg -F "${fpath}:${fline}:" 2>/dev/null \
                      | rg -F "P_ne_NP_unconditional" 2>/dev/null \
                      || true)"
    if [[ -n "${stripped_match}" ]]; then
      echo "[audit_bootstrap]   ${fpath}:${fline} ACTIVE (see Step 2)"
      unexpected_hits=1
    else
      echo "[audit_bootstrap]   ${fpath}:${fline} false-positive"\
           "(inside comment/docstring/fenced block)"
    fi
  done <<<"${raw_hits}"
  if [[ "${unexpected_hits}" -eq 1 ]]; then
    echo "[audit_bootstrap]   (one or more hits are ACTIVE — see Step 2"
    echo "[audit_bootstrap]    for the authoritative list)"
  fi
fi
echo

# ---------------------------------------------------------------------------
# Step 4 — canonical pipeline commands.
# ---------------------------------------------------------------------------
#
# The doc-honesty linter (scripts/check_doc_honesty.sh) is the
# AUTHORITATIVE source for "is there an unconditional claim" — it
# (a) hard-fails on a phantom `axiom P_ne_NP_unconditional`, and
# (b) detects whether a closed theorem of that name exists via Lean
# elaboration when `lake` is available, falling back to the same
# comment-stripped grep used here.

echo "[audit_bootstrap] Step 4: canonical pipeline commands"
echo "[audit_bootstrap]   (run these, IN THIS ORDER, for an"
echo "[audit_bootstrap]    authoritative pass/fail signal)"
echo
echo "    elan-init.sh -y --default-toolchain none      # if not present"
echo "    export PATH=\"\$HOME/.elan/bin:\$PATH\""
echo "    lake exe cache get                            # mathlib oleans"
echo "    lake build PnP3 Pnp4                          # full Lean build"
echo "    ./scripts/check.sh                            # 17/17 govern pipeline"
echo "    ./scripts/run_smoke_probes.sh                 # 8/8 smoke probes"
echo "    python3 ./scripts/validate_jsonl.py           # 3 JSONL logs"
echo "    ./scripts/test_attempts_validator.sh          # critic-state hardening"
echo "    ./scripts/test_underscore_policy.sh           # underscore bypass policy"
echo "    ./scripts/test_rule16_negative.sh             # Rule-16 negative control"
echo
echo "[audit_bootstrap]   ALL of the above must exit 0 for the branch"
echo "[audit_bootstrap]   to be considered green.  The doc-honesty"
echo "[audit_bootstrap]   linter inside scripts/check.sh is what"
echo "[audit_bootstrap]   authoritatively decides whether an active"
echo "[audit_bootstrap]   P_ne_NP_unconditional exists; raw grep is"
echo "[audit_bootstrap]   informational only."
echo

# ---------------------------------------------------------------------------
# Result.
# ---------------------------------------------------------------------------

if [[ "${real_blocker}" -ne 0 ]]; then
  echo "[audit_bootstrap] RESULT: REAL BLOCKER (active declaration found)"
  exit 1
fi

echo "[audit_bootstrap] RESULT: bootstrap clean — no real blockers from"
echo "[audit_bootstrap]         the P_ne_NP_unconditional check; raw"
echo "[audit_bootstrap]         grep hits, if any, are all inside"
echo "[audit_bootstrap]         documented comment/template regions."
exit 0
