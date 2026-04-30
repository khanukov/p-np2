#!/usr/bin/env bash
# Refuted-route quarantine guard — Research Governance v0.1, PR 3.
#
# Scope (RESEARCH_CONSTITUTION.md Rule 6, Phase0_Audit_Surface.md §1.2):
#
#   A final-looking theorem (i.e. a `theorem` whose name begins with
#   `NP_not_subset_` or `P_ne_NP_`) whose direct premise is one of the
#   formally refuted predicates listed in
#   `spec/target.toml::[refuted_predicates]` is audit-only.  Any such
#   declaration in production code must carry an explicit
#   `RefutedRoute_*`, `Vacuous_*`, or `AuditOnly_*` prefix.
#
# This guard is intentionally narrow in PR 3:
#
#   - It only flags identifiers that look like *finals*: names starting
#     with `NP_not_subset_` or `P_ne_NP_`.  Helper/intermediate lemmas
#     that happen to consume a refuted premise (e.g.
#     `dag_stableRestrictionGoal_of_supportBounds`) are out of PR 3
#     scope and are deferred to a later cleanup.
#
#   - It does not scan files inside the audit/test/docs allowlist
#     (`pnp3/Magnification/AuditRoutes/`,
#     `pnp3/Magnification/FinalResultAuditRoutes.lean`,
#     `pnp3/Tests/`, `pnp3/Barrier/`, `pnp3/Docs/`, `archive/`).
#     Inside those zones, refuted-route names are acceptable provided
#     they keep their `RefutedRoute_*` / `Vacuous_*` / `AuditOnly_*`
#     prefix; that is enforced by the prefix check below, not by file
#     location.
#
# Patterns considered "final-looking refuted-route" suffixes:
#
#   _final_with_supportBounds
#   _final_of_supportBounds
#   _final_with_multiswitching
#   _final_of_multiswitchingData
#   _final_with_magnification
#   _final_of_magnification
#   _final_under_fixedParams_and_uniformProvenance
#   _of_supportBounds_TM        (LowerBounds bare TM form)
#   _of_supportBounds           (LowerBounds bare form, e.g.
#                                `NP_not_subset_PpolyDAG_of_supportBounds`)
#
# A theorem name that starts with `NP_not_subset_` or `P_ne_NP_` and
# ends with one of these suffixes must also start with one of:
#
#   RefutedRoute_   Vacuous_   AuditOnly_

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

if ! command -v rg >/dev/null 2>&1; then
  echo "[refuted-route] Missing required dependency: rg (ripgrep)." >&2
  exit 127
fi

fail=0

# ---------------------------------------------------------------------------
# Suffix patterns (final-looking only).
# ---------------------------------------------------------------------------
suffix_patterns=(
  '_final_with_supportBounds'
  '_final_of_supportBounds'
  '_final_with_multiswitching'
  '_final_of_multiswitchingData'
  '_final_with_magnification'
  '_final_of_magnification'
  '_final_under_fixedParams_and_uniformProvenance'
  '_of_supportBounds_TM'
)

allowed_prefixes='RefutedRoute_|Vacuous_|AuditOnly_'

# Required head: only theorems whose names start with these final-shape
# prefixes are considered.  This excludes helper lemmas like
# `dag_stableRestrictionGoal_of_supportBounds` from PR 3 scope.
# (No trailing `_` — the suffix patterns below already supply it.)
final_heads='(NP_not_subset|P_ne_NP)'

# ---------------------------------------------------------------------------
# Search scope.  Allowed contexts are excluded.
# ---------------------------------------------------------------------------
search_paths=(
  pnp3/Magnification
  pnp3/LowerBounds
  pnp4
)
excludes=(
  -g '!pnp3/Magnification/AuditRoutes/**'
  -g '!pnp3/Magnification/FinalResultAuditRoutes.lean'
  -g '!pnp3/Tests/**'
  -g '!pnp3/Barrier/**'
  -g '!pnp3/Docs/**'
  -g '!archive/**'
)

echo "[refuted-route] scanning for unmarked direct-refuted final endpoints"

# Suffix-based check (excludes plain `_of_supportBounds` since that is
# handled separately below to avoid double-matching `_final_of_...` cases).
for suffix in "${suffix_patterns[@]}"; do
  pattern="^[[:space:]]*theorem[[:space:]]+${final_heads}[A-Za-z0-9_]*${suffix}\\b"
  hits="$(rg -n --no-heading --color=never \
            -g '*.lean' "${excludes[@]}" \
            -- "${pattern}" "${search_paths[@]}" 2>/dev/null || true)"
  if [[ -z "${hits}" ]]; then
    continue
  fi
  while IFS= read -r line; do
    content="${line#*:*:}"
    ident="$(echo "${content}" \
              | sed -nE 's/^[[:space:]]*theorem[[:space:]]+([A-Za-z0-9_]+).*/\1/p')"
    if [[ -z "${ident}" ]]; then
      continue
    fi
    if [[ "${ident}" =~ ^(${allowed_prefixes}) ]]; then
      continue
    fi
    echo "[refuted-route] FAIL: unmarked direct-refuted final endpoint: ${ident}"
    echo "  ${line}"
    echo "  Suffix: ${suffix}"
    echo "  Required prefix: RefutedRoute_, Vacuous_, or AuditOnly_."
    fail=1
  done <<< "${hits}"
done

# Bare-form `_of_supportBounds` (no `_final_` infix), restricted to
# final-looking heads.  The match excludes `_of_supportBounds_TM` (a
# distinct suffix above) and `_final_of_supportBounds` (handled above).
bare_pattern="^[[:space:]]*theorem[[:space:]]+${final_heads}[A-Za-z0-9_]*_of_supportBounds\\b"
bare_hits="$(rg -n --no-heading --color=never \
              -g '*.lean' "${excludes[@]}" \
              -- "${bare_pattern}" "${search_paths[@]}" 2>/dev/null || true)"
if [[ -n "${bare_hits}" ]]; then
  while IFS= read -r line; do
    content="${line#*:*:}"
    ident="$(echo "${content}" \
              | sed -nE 's/^[[:space:]]*theorem[[:space:]]+([A-Za-z0-9_]+).*/\1/p')"
    if [[ -z "${ident}" ]]; then
      continue
    fi
    # Skip cases already covered by the `_final_*` suffix patterns.
    if [[ "${ident}" == *_final_of_supportBounds || \
          "${ident}" == *_final_of_supportBounds_TM ]]; then
      continue
    fi
    if [[ "${ident}" == *_of_supportBounds_TM ]]; then
      continue
    fi
    if [[ "${ident}" =~ ^(${allowed_prefixes}) ]]; then
      continue
    fi
    echo "[refuted-route] FAIL: unmarked direct-refuted final endpoint: ${ident}"
    echo "  ${line}"
    echo "  Suffix: _of_supportBounds (bare)"
    echo "  Required prefix: RefutedRoute_, Vacuous_, or AuditOnly_."
    fail=1
  done <<< "${bare_hits}"
fi

# ---------------------------------------------------------------------------
# Result.
# ---------------------------------------------------------------------------

if [[ "${fail}" -ne 0 ]]; then
  echo
  echo "[refuted-route] FAIL"
  echo "[refuted-route]   See RESEARCH_CONSTITUTION.md Rule 6,"
  echo "[refuted-route]       Phase0_Audit_Surface.md §1.2, and"
  echo "[refuted-route]       spec/target.toml::[refuted_predicates]."
  exit 1
fi

echo "[refuted-route] OK"
