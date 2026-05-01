#!/usr/bin/env bash
# Refuted-predicate allowed-use guard — Research Governance v0.1, PR 4a.
#
# Scope (RESEARCH_CONSTITUTION.md Rule 6, Phase0_Audit_Surface.md §1.2,
# spec/target.toml::[refuted_predicates]):
#
#   The six refuted predicates listed in spec/target.toml have formal
#   `→ False` proofs in
#   `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`.  PR 4a
#   adds a centralised registry at `pnp3/RefutedPredicates/Registry.lean`
#   and this guard, which prevents new production-side use sites of
#   the bare predicate names from spreading further.
#
# Two-mode design (per Engineering Execution Plan v0.2.1, amendment ⑤):
#
#   (A) HARD-FAIL zone — any **code-level** occurrence of a refuted-
#       predicate name in these locations is a CI failure:
#         - pnp3/Complexity/                         (trust root)
#         - pnp3/Magnification/UnconditionalResearchGap.lean
#                                                    (canonical bridge)
#         - pnp3/Candidates/                         (Rule 3)
#         - pnp4/                                    (separate library)
#       Comment-only mentions are ignored: a refuted predicate name
#       that appears only inside `--` line comments or inside
#       `/- ... -/` / `/-! ... -/` block comments is not a code-level
#       use and does not trip the guard.
#
#   (B) SOFT-REPORT zone — historical surface where bare predicate
#       names already appear extensively in code. Code-level
#       occurrences are PRINTED to the build log as a regression-watch
#       list but DO NOT fail CI:
#         - pnp3/Magnification/        (excluding AuditRoutes/, the
#                                       `UnconditionalResearchGap.lean`
#                                       trust-root file, and the
#                                       FinalResultAuditRoutes.lean
#                                       audit subtree)
#         - pnp3/LowerBounds/
#         - pnp3/ThirdPartyFacts/
#       This is a temporary fallback per amendment ⑤. The follow-up
#       step (PR 4b after PR 14) physically relocates the predicates
#       and lets soft-report be replaced by region-bracket markers.
#
#   (C) ALLOWED zones — names may freely appear; no scan output:
#         - pnp3/RefutedPredicates/
#         - pnp3/Magnification/AuditRoutes/                (planned)
#         - pnp3/Magnification/FinalResultAuditRoutes.lean (audit file)
#         - pnp3/Tests/
#         - pnp3/Barrier/
#         - pnp3/Docs/
#         - archive/
#         - spec/, outputs/, RESEARCH_CONSTITUTION.md, Phase0_Audit_Surface.md
#
# Whole-file blanket-exemption is explicitly avoided. The HARD-FAIL
# list above only covers files where new use is actively wrong; the
# SOFT-REPORT list logs uses for visibility, so future regressions
# (new code-level use-sites in those files) are visible in build logs
# even though they don't break CI today.

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

if ! command -v rg >/dev/null 2>&1; then
  echo "[refuted-predicate] Missing required dependency: rg (ripgrep)." >&2
  exit 127
fi

# strip_lean_comments <file>
#
# Reads a Lean source file and writes to stdout one line per source
# line, with `--` line comments and `/- ... -/` block comments removed
# (block comments may span multiple lines; nested blocks are not
# tracked — Lean nests them via `/-` `-/`, but for our heuristic we
# treat them flat).  Output preserves line numbers (one input line →
# one output line, possibly empty).
strip_lean_comments() {
  local f="$1"
  awk '
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
      print out
    }
  ' "${f}"
}

# scan_file_for_predicate <file> <predicate>
#
# Returns "<file>:<lineno>:<content>" lines for each code-level
# occurrence of <predicate> as a whole word in the comment-stripped
# view of <file>.  Empty output if no code-level occurrence.
scan_file_for_predicate() {
  local f="$1"
  local pred="$2"
  if [[ ! -f "${f}" ]]; then
    return 0
  fi
  local stripped
  stripped="$(mktemp)"
  strip_lean_comments "${f}" >"${stripped}"
  rg -n -w -- "${pred}" "${stripped}" 2>/dev/null \
    | sed -e "s|^|${f}:|"
  rm -f "${stripped}"
}

# scan_dir_for_predicate <dir> <predicate>
#
# Same as above, but iterates over every *.lean file under <dir>.
scan_dir_for_predicate() {
  local dir="$1"
  local pred="$2"
  if [[ ! -d "${dir}" ]]; then
    return 0
  fi
  while IFS= read -r f; do
    scan_file_for_predicate "${f}" "${pred}"
  done < <(find "${dir}" -name '*.lean' 2>/dev/null)
}

predicates=(
  "FormulaSupportRestrictionBoundsPartial"
  "FormulaSupportBoundsFromMultiSwitchingContract"
  "MagnificationAssumptions"
  "FormulaSupportBoundsPartial_fromPipeline"
  "MagnificationAssumptions_fromPipeline"
)
# Note: word-boundary `-w` ensures `MagnificationAssumptions\b` does
# not match `MagnificationAssumptions_fromPipeline`.
#
# `fixedParams ∧ uniformProvenance` is a conjunction shape, not a
# named identifier; it's audited via the
# `RefutedPredicate_FixedParamsUniformProvenancePair` alias and its
# Probe 8a counterexample, but no name to grep here.

# ---------------------------------------------------------------------------
# (A) HARD-FAIL zone (code-level only).
# ---------------------------------------------------------------------------

echo "[refuted-predicate] (A) hard-fail scan (code-level only; comments ignored)"

hard_extra_files=(
  pnp3/Magnification/UnconditionalResearchGap.lean
)

fail=0

for pred in "${predicates[@]}"; do
  hard_hits=""
  hard_hits+="$(scan_dir_for_predicate pnp3/Complexity "${pred}")"
  hard_hits+=$'\n'
  hard_hits+="$(scan_dir_for_predicate pnp3/Candidates "${pred}")"
  hard_hits+=$'\n'
  hard_hits+="$(scan_dir_for_predicate pnp4 "${pred}")"
  hard_hits+=$'\n'
  for f in "${hard_extra_files[@]}"; do
    hard_hits+="$(scan_file_for_predicate "${f}" "${pred}")"
    hard_hits+=$'\n'
  done
  # Strip leading/trailing blank lines.
  hard_hits="$(printf '%s' "${hard_hits}" | awk 'NF { print }')"
  if [[ -n "${hard_hits}" ]]; then
    echo "[refuted-predicate] FAIL: bare '${pred}' in hard-fail zone (code-level):"
    echo "${hard_hits}"
    echo "[refuted-predicate]   Use Pnp3.RefutedPredicates.RefutedPredicate_${pred} instead,"
    echo "[refuted-predicate]   or move the use site into an audit/test/docs zone."
    fail=1
  fi
done

# ---------------------------------------------------------------------------
# (B) SOFT-REPORT zone (code-level visibility only).
# ---------------------------------------------------------------------------

echo "[refuted-predicate] (B) soft-report scan (visibility only; not CI-blocking)"

declare -A soft_counts
for pred in "${predicates[@]}"; do
  count=0
  while IFS= read -r f; do
    n=$(scan_file_for_predicate "${f}" "${pred}" | wc -l | tr -d ' ')
    count=$(( count + n ))
  done < <(
    find pnp3/Magnification pnp3/LowerBounds pnp3/ThirdPartyFacts \
      -name '*.lean' 2>/dev/null \
      | grep -v '^pnp3/Magnification/AuditRoutes/' \
      | grep -v '^pnp3/Magnification/FinalResultAuditRoutes\.lean$' \
      | grep -v '^pnp3/Magnification/UnconditionalResearchGap\.lean$'
  )
  soft_counts["${pred}"]="${count}"
done

echo "[refuted-predicate]   historical code-level occurrences:"
for pred in "${predicates[@]}"; do
  printf '[refuted-predicate]     %-50s %s\n' "${pred}" "${soft_counts[${pred}]}"
done
echo "[refuted-predicate]   (these are tracked under PR 4b for physical relocation)"

# ---------------------------------------------------------------------------
# Result.
# ---------------------------------------------------------------------------

if [[ "${fail}" -ne 0 ]]; then
  echo
  echo "[refuted-predicate] FAIL"
  echo "[refuted-predicate]   See RESEARCH_CONSTITUTION.md Rule 6,"
  echo "[refuted-predicate]       Phase0_Audit_Surface.md §1.2, and"
  echo "[refuted-predicate]       spec/target.toml::[refuted_predicates]."
  echo "[refuted-predicate]   Canonical alias home: pnp3/RefutedPredicates/Registry.lean."
  exit 1
fi

echo "[refuted-predicate] OK"
