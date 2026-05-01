#!/usr/bin/env bash
# Candidate-local Rule 16 scan — Research Governance v0.1, PR 15.1.
#
# Walks `pnp3/Candidates/<base>/<id>/**.lean` (excluding the
# `_*` directories such as `_template/`) and rejects declarations
# that violate Rule 16 of `RESEARCH_CONSTITUTION.md`
# (`spec/implicit_assumption_channels.md` §1).
#
# Hard-rejected forms (any occurrence in candidate-local code is a
# CI failure):
#
#   class ... where           - typeclass-payload channel
#   instance ... :=           - same
#   instance ... where        - same
#   default_instance          - auto-payload selection
#   attribute [instance] ...  - indirect instance registration
#   opaque ...                - hides definition behind a seal
#   Fact ...                  - typeclass-style payload smuggling
#                               (any `Fact <P>` argument)
#
# Soft-flagged forms (printed but currently NOT failing CI; will be
# tightened in a follow-up PR):
#
#   noncomputable def ...     where the name matches
#                             Provider|Default|Payload|Witness|
#                             Source|Gap
#
# The Lean comment-stripper from
# `scripts/check_refuted_predicate_usage.sh` is reused here so that
# the scan ignores docstring/comment occurrences.
#
# Allowlisted typeclasses (from
# `spec/implicit_assumption_channels.md` §3) MAY appear as instance
# bodies, but the candidate must declare them explicitly in
# `manifest.toml::[whitelisted_typeclasses].allowed`. The MVP guard
# does NOT cross-check against the manifest; it hard-rejects ALL
# `class`/`instance`/`opaque` in candidate-local code regardless.
# A real candidate that legitimately needs `Decidable` etc. should
# place those instances in a sibling file outside `proof.lean`,
# OR (future PR) the guard will read the manifest's allowed list
# and filter accordingly.

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

if ! command -v rg >/dev/null 2>&1; then
  echo "[rule16] Missing required dependency: rg (ripgrep)." >&2
  exit 127
fi

candidates_root="pnp3/Candidates"

if [[ ! -d "${candidates_root}" ]]; then
  echo "[rule16] OK (no ${candidates_root} directory yet)"
  exit 0
fi

# Collect candidate directories: any directory under
# `pnp3/Candidates/` whose path does NOT contain a component
# starting with `_` (so `_template/`, `_scratch/`, etc. are
# excluded).  Both depth-1 (`pnp3/Candidates/<id>/`) and depth-2
# (`pnp3/Candidates/<method-family>/<id>/`) layouts are accepted.
mapfile -t candidate_dirs < <(
  find "${candidates_root}" -mindepth 1 -maxdepth 3 -type d \
    | awk -F/ '{
        skip = 0
        # Skip if any path component starts with "_".
        for (i = 1; i <= NF; i++) {
          if ($i ~ /^_/) { skip = 1; break }
        }
        if (!skip) print
      }'
)

if [[ ${#candidate_dirs[@]} -eq 0 ]]; then
  echo "[rule16] OK (no real candidates yet; only ${candidates_root}/_template excluded)"
  exit 0
fi

# Stripper (reuse): block-comment + line-comment.
strip_lean() {
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
  ' "$1"
}

fail=0

# Hard-rejected patterns (per spec/implicit_assumption_channels.md §1).
hard_patterns=(
  '^[[:space:]]*class[[:space:]]+[A-Za-z]'
  '^[[:space:]]*instance[[:space:]]'
  '^[[:space:]]*default_instance\b'
  '^[[:space:]]*attribute[[:space:]]+\[instance\]'
  '^[[:space:]]*opaque[[:space:]]+'
)

# Soft-flagged: noncomputable def names that hide payload semantics.
soft_pattern='^[[:space:]]*noncomputable[[:space:]]+def[[:space:]]+[A-Za-z0-9_]*(Provider|Default|Payload|Witness|Source|Gap)'

# Fact <P> argument anywhere (in code, after stripping comments).
fact_pattern='\(\s*[A-Za-z0-9_]+\s*:\s*Fact[[:space:]]+'

soft_hits=0

for dir in "${candidate_dirs[@]}"; do
  echo "[rule16] scanning candidate: ${dir}"
  while IFS= read -r f; do
    stripped="$(mktemp)"
    strip_lean "${f}" >"${stripped}"
    for pat in "${hard_patterns[@]}"; do
      hits="$(grep -nE "${pat}" "${stripped}" || true)"
      if [[ -n "${hits}" ]]; then
        echo "[rule16] FAIL (hard): forbidden declaration in ${f}:"
        echo "${hits}" | sed -e "s|^|[rule16]   ${f}:|" -e 's|:[0-9]*:|: line |'
        echo "[rule16]   pattern: ${pat}"
        fail=1
      fi
    done
    fact_hits="$(grep -nE "${fact_pattern}" "${stripped}" || true)"
    if [[ -n "${fact_hits}" ]]; then
      echo "[rule16] FAIL (hard): Fact <P> argument in ${f}:"
      echo "${fact_hits}" | sed -e "s|^|[rule16]   ${f}:|" -e 's|:[0-9]*:|: line |'
      fail=1
    fi
    soft_match="$(grep -nE "${soft_pattern}" "${stripped}" || true)"
    if [[ -n "${soft_match}" ]]; then
      echo "[rule16] SOFT-FLAG: suspicious noncomputable def name in ${f}:"
      echo "${soft_match}" | sed -e "s|^|[rule16]   ${f}:|" -e 's|:[0-9]*:|: line |'
      soft_hits=$((soft_hits + 1))
    fi
    rm -f "${stripped}"
  done < <(find "${dir}" -name '*.lean' 2>/dev/null)
done

if [[ "${soft_hits}" -gt 0 ]]; then
  echo "[rule16] (${soft_hits} soft flag(s) above are tracked but do NOT fail CI in PR 15.1)"
fi

if [[ "${fail}" -ne 0 ]]; then
  echo
  echo "[rule16] FAIL"
  echo "[rule16]   See RESEARCH_CONSTITUTION.md Rule 16,"
  echo "[rule16]       spec/implicit_assumption_channels.md §1, and"
  echo "[rule16]       spec/target.toml::[hidden_payload_channels]."
  exit 1
fi

echo "[rule16] OK"
