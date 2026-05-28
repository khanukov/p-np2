#!/usr/bin/env bash
# Doc-honesty linter — Research Governance v0.1, PR 1.
#
# Scope (RESEARCH_CONSTITUTION.md Rule 1, spec/target.toml::[doc_honesty]):
#
#   Public Markdown / LaTeX documents must not claim an unconditional
#   proof of P != NP unless a closed, zero-argument theorem
#
#       P_ne_NP_unconditional : ComplexityInterfaces.P_ne_NP
#
#   exists as a `theorem` (NOT an `axiom`) in the active Lean tree, with
#   only whitelisted axioms in its dependency closure (the latter is
#   enforced by the existing UNCONDITIONAL gate in scripts/check.sh and
#   is out of scope for this linter).
#
# Two-part check:
#
#   (A) Lean-side phantom-axiom check.  An `axiom P_ne_NP_unconditional`
#       declaration anywhere in pnp3/ or pnp4/ is an immediate FAIL,
#       regardless of what the docs say.  Rule 1 forbids the axiom form.
#
#   (B) Public-doc claim scan.  If the active Lean tree does not contain
#       a closed `theorem P_ne_NP_unconditional`, public Markdown / LaTeX
#       files must not contain hard claim phrases.  Governance/spec
#       files are excluded because they reference these phrases as
#       policy text, not as claims.
#
# Design note on the bare identifier:
#
#   The identifier `P_ne_NP_unconditional` itself is NOT in the public-
#   doc forbidden-phrase list.  Existing public docs (TODO.md,
#   pnp3/Docs/Unconditionality_FAQ_ru.md, ...) legitimately describe the
#   identifier as the absent target, e.g. "expose `P_ne_NP_unconditional`
#   from that same file".  Mentioning a name is not the same as claiming
#   completion.  The phantom-axiom check (A) and the existing
#   UNCONDITIONAL gate (scripts/check.sh step 7) together enforce that
#   the identifier, when it does exist, is a real zero-argument theorem
#   with the right type and only whitelisted axioms in its closure.
#
#   If a future PR wants to additionally police the identifier in public
#   docs, that is a separate spec change to spec/target.toml and a
#   separate linter PR.

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

if ! command -v rg >/dev/null 2>&1; then
  echo "[doc-honesty] Missing required dependency: rg (ripgrep)." >&2
  exit 127
fi

fail=0

# ---------------------------------------------------------------------------
# (A) Phantom-axiom check.
# ---------------------------------------------------------------------------
#
# Rule 1: a placeholder of the form `axiom P_ne_NP_unconditional : ...` is
# forbidden.  This is enforced regardless of doc content.  We scan the
# active source trees pnp3/ and pnp4/.

echo "[doc-honesty] (A) phantom-axiom scan"

axiom_hits="$(rg -n '^[[:space:]]*axiom[[:space:]]+P_ne_NP_unconditional\b' \
                -g'*.lean' pnp3 pnp4 2>/dev/null || true)"

if [[ -n "${axiom_hits}" ]]; then
  echo "[doc-honesty] FAIL: phantom 'axiom P_ne_NP_unconditional' detected:"
  echo "${axiom_hits}"
  echo "[doc-honesty]   See RESEARCH_CONSTITUTION.md Rule 1: the final term"
  echo "[doc-honesty]   must be a closed theorem, not an axiom."
  fail=1
fi

# ---------------------------------------------------------------------------
# (B) Detect whether a closed `theorem P_ne_NP_unconditional` exists.
# ---------------------------------------------------------------------------
#
# Strategy: prefer the Lean elaborator (robust against block comments and
# docstrings) when `lake` is available; fall back to a comment-stripping
# grep heuristic otherwise.

valid_term_present=0

run_lean_probe() {
  if ! command -v lake >/dev/null 2>&1; then
    return 1
  fi
  local probe="/tmp/pnp3_doc_honesty_probe.lean"
  local log="/tmp/pnp3_doc_honesty_probe.log"
  cat >"${probe}" <<'PROBE'
import Magnification.UnconditionalResearchGap
open Pnp3.Magnification in
#check (P_ne_NP_unconditional : Pnp3.ComplexityInterfaces.P_ne_NP)
PROBE
  if lake env lean "${probe}" >"${log}" 2>&1; then
    return 0
  fi
  return 1
}

# Comment-aware Lean fallback.
#
# Strips `/- ... -/` block comments (including docstrings `/-! ... -/`)
# and `-- ...` line comments before grepping for top-level
# `theorem P_ne_NP_unconditional : ...`.  Also requires the absence of
# `(` before the first `:` to approximate a zero-argument statement.
fallback_lean_grep() {
  local stripped
  stripped="$(mktemp)"
  trap 'rm -f "${stripped}"' RETURN
  local f
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
    ' "${f}"
  done < <(find pnp3 pnp4 -name '*.lean' 2>/dev/null) >"${stripped}"

  local cand
  cand="$(rg -n '^[^:]+:[0-9]+:[[:space:]]*theorem[[:space:]]+P_ne_NP_unconditional[[:space:]]*:' \
            "${stripped}" 2>/dev/null | head -1 || true)"
  if [[ -z "${cand}" ]]; then
    return 1
  fi
  # Extract the part after the third colon (file:line:content).
  local content
  content="$(echo "${cand}" | awk -F: '{ for (i=4; i<=NF; i++) { printf "%s", $i; if (i<NF) printf ":" } }')"
  # If there is a `(` before the type colon, treat as having arguments.
  local pre_colon="${content%%:*}"
  if [[ "${pre_colon}" == *"("* ]]; then
    return 1
  fi
  return 0
}

echo "[doc-honesty] (B) closed-theorem detection"

if run_lean_probe; then
  valid_term_present=1
elif fallback_lean_grep; then
  valid_term_present=1
fi

if [[ "${valid_term_present}" == "1" ]]; then
  echo "[doc-honesty]   closed P_ne_NP_unconditional theorem appears to exist;"
  echo "[doc-honesty]   doc-claim scan is relaxed."
else
  echo "[doc-honesty]   no closed P_ne_NP_unconditional theorem in active tree;"
  echo "[doc-honesty]   public docs must not claim unconditional P != NP."
fi

# ---------------------------------------------------------------------------
# (C) Public-doc claim scan.
# ---------------------------------------------------------------------------
#
# Run only when valid_term_present == 0.  Hard claim phrases listed
# in spec/target.toml::[doc_honesty].forbidden_unless_final_term_exists.

claim_phrases=(
  "unconditional P != NP"
  "unconditional P ≠ NP"
  "we prove unconditional"
  "complete proof of P vs NP"
  "P≠NP solved"
  "P!=NP solved"
  "P != NP solved"
)

# Files excluded from the public-doc scan: governance/spec files plus
# this script itself.  Edit spec/target.toml::[doc_honesty] and bump
# [meta].spec_version when changing this list.
excluded_globs=(
  -g '!RESEARCH_CONSTITUTION.md'
  -g '!Phase0_Audit_Surface.md'
  -g '!FixedParams_Probe.md'
  -g '!spec/**'
  -g '!bench/**'
  -g '!outputs/**'
  -g '!archive/**'
  -g '!scripts/check_doc_honesty.sh'
)

scan_globs=(
  -g '*.md'
  -g '*.tex'
  -g '*.latex'
)

if [[ "${valid_term_present}" == "0" ]]; then
  echo "[doc-honesty] (C) public-doc claim scan"
  # Notes:
  # - ripgrep 14 applies -g rules in order.  Positive `*.md` etc. must
  #   come BEFORE negative `!...` exclusions, otherwise the negatives
  #   are interpreted as constraining the include set rather than
  #   refining it.
  # - Always pass an explicit search root (`.`) so ripgrep does not
  #   block reading stdin when invoked from a non-interactive shell.
  for phrase in "${claim_phrases[@]}"; do
    hits="$(rg -n -F --no-heading --color=never \
              "${scan_globs[@]}" "${excluded_globs[@]}" \
              -- "${phrase}" . 2>/dev/null || true)"
    if [[ -n "${hits}" ]]; then
      echo "[doc-honesty] FAIL: forbidden claim phrase: ${phrase}"
      echo "${hits}"
      fail=1
    fi
  done
fi

# ---------------------------------------------------------------------------
# (D) Stale public-endpoint wording scan.
# ---------------------------------------------------------------------------
#
# Independent of Rule 1 / valid_term_present.  These patterns describe the
# pre-ResearchGapWitness picture where `P_ne_NP_final` still consumed
# `MagnificationAssumptions`.  The current public default is
# `P_ne_NP_final (gap : ResearchGapWitness)`; legacy hMag / hMS /
# support-bounds endpoints are audit / compatibility wrappers only, and the
# support-bounds route is formally refuted (`MagnificationAssumptions ->
# False`, etc.).
#
# Source list: spec/target.toml::[stale_public_endpoint_wording].
#
# Allowed locations: archive/**, outputs/**, seed_packs/**, spec/**,
# bench/**, scripts/**, governance/audit docs that are exempt by name,
# and individual files that contain the opt-out marker
# `<!-- doc-status: legacy -->` near the top.

echo "[doc-honesty] (D) stale public-endpoint wording scan"

stale_endpoint_patterns=(
  'P_ne_NP_final\b\s*\(hMag'
  'current public default theorem[^\n]*MagnificationAssumptions'
  'fastest path[^\n]*remove hMag'
  'only formula-side internalization remains'
)

stale_excluded_globs=(
  -g '!RESEARCH_CONSTITUTION.md'
  -g '!Phase0_Audit_Surface.md'
  -g '!FixedParams_Probe.md'
  -g '!spec/**'
  -g '!bench/**'
  -g '!outputs/**'
  -g '!archive/**'
  -g '!seed_packs/**'
  -g '!scripts/**'
)

legacy_marker='<!-- doc-status: legacy -->'

for pattern in "${stale_endpoint_patterns[@]}"; do
  raw_hits="$(rg -n --no-heading --color=never \
                "${scan_globs[@]}" "${stale_excluded_globs[@]}" \
                -e "${pattern}" . 2>/dev/null || true)"
  if [[ -z "${raw_hits}" ]]; then
    continue
  fi

  # Filter out files that carry the legacy opt-out marker.  ripgrep
  # output lines look like `path:line:content`; the path is everything
  # before the first colon.
  filtered_hits=""
  while IFS= read -r line; do
    [[ -z "${line}" ]] && continue
    file_path="${line%%:*}"
    if [[ -f "${file_path}" ]] && rg -q -F -- "${legacy_marker}" "${file_path}" 2>/dev/null; then
      # File is explicitly tagged as legacy; skip.
      continue
    fi
    if [[ -z "${filtered_hits}" ]]; then
      filtered_hits="${line}"
    else
      filtered_hits="${filtered_hits}"$'\n'"${line}"
    fi
  done <<<"${raw_hits}"

  if [[ -n "${filtered_hits}" ]]; then
    echo "[doc-honesty] FAIL: stale public-endpoint pattern: ${pattern}"
    echo "${filtered_hits}"
    echo "[doc-honesty]   Active public docs must reflect the current public"
    echo "[doc-honesty]   default: P_ne_NP_final (gap : ResearchGapWitness)."
    echo "[doc-honesty]   Move stale phrases to archive/, outputs/, or annotate"
    echo "[doc-honesty]   the file with '${legacy_marker}' near the top to opt out."
    fail=1
  fi
done

# ---------------------------------------------------------------------------
# Result.
# ---------------------------------------------------------------------------

if [[ "${fail}" -ne 0 ]]; then
  echo
  echo "[doc-honesty] FAIL"
  echo "[doc-honesty]   See RESEARCH_CONSTITUTION.md Rule 1 and"
  echo "[doc-honesty]       spec/target.toml::[doc_honesty]."
  exit 1
fi

echo "[doc-honesty] OK"
