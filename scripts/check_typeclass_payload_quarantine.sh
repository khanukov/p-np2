#!/usr/bin/env bash
# Typeclass-payload quarantine guard — Research Governance v0.1, PR 2.
#
# Scope (RESEARCH_CONSTITUTION.md Rule 16, Phase0_Audit_Surface.md §1.3):
#
#   The provider channel `VacuousFinalPayloadProvider` (formerly
#   `FinalPayloadProvider`) and the `hasDefaultFormulaSupportRestrictionBoundsPartial`
#   default-flag stack reconstruct the refuted formula-side support-bounds
#   surface at the final endpoint boundary.  They must not appear as
#   typeclass parameters in production / mainline code.
#
# The guard performs two layered checks:
#
#   (A) Strong typeclass-parameter check.
#       Bracketed forms `[FinalPayloadProvider]`,
#       `[VacuousFinalPayloadProvider]`, and
#       `[Fact hasDefaultFormulaSupportRestrictionBoundsPartial]` are
#       forbidden outside the audit/test/docs allowlist.  These are the
#       call-site shapes that hide refuted payload through typeclass
#       synthesis.
#
#   (B) Bare-name-theorem check.
#       A `theorem P_ne_NP` declaration (exact word match, with
#       ":" or "[" or "(" or whitespace following) is forbidden in
#       `pnp3/Magnification/` and `pnp3/LowerBounds/`.  The only
#       canonical definition of `P_ne_NP` lives in
#       `pnp3/Complexity/Interfaces.lean` and uses `def`, not
#       `theorem`, so this guard does not affect the trust root.
#
# Allowlist (lines below).  Adding to this list is a Foundational PR.

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

if ! command -v rg >/dev/null 2>&1; then
  echo "[quarantine] Missing required dependency: rg (ripgrep)." >&2
  exit 127
fi

fail=0

# ---------------------------------------------------------------------------
# (A) Typeclass-parameter check.
# ---------------------------------------------------------------------------
#
# Any of these typeclass parameter shapes is forbidden outside the
# audit/test/docs/governance allowlist.

typeclass_patterns=(
  # Bare and fully-qualified `[FinalPayloadProvider]` and its renamed
  # successor.  `[A-Za-z0-9_.]*` captures any namespace prefix.
  '\[[A-Za-z0-9_.]*FinalPayloadProvider\]'
  '\[[A-Za-z0-9_.]*VacuousFinalPayloadProvider\]'
  # `[Fact <maybe-qualified> hasDefaultFormulaSupportRestrictionBoundsPartial]`,
  # tolerant of arbitrary inner whitespace and namespace prefix.
  '\[[[:space:]]*Fact[[:space:]]+[A-Za-z0-9_.]*hasDefaultFormulaSupportRestrictionBoundsPartial[[:space:]]*\]'
  # PR 6: `FormulaSemanticMultiSwitchingProvider` is a refuted-channel
  # entry per spec/provider_audit_registry.toml. New typeclass-
  # parameter uses outside the audit/test/docs surface are forbidden.
  '\[[A-Za-z0-9_.]*FormulaSemanticMultiSwitchingProvider\]'
)

# Exclusions for the typeclass parameter check.  Order matters: positives
# first, then negatives (ripgrep 14).  We restrict the search to *.lean.
typeclass_excludes=(
  -g '!pnp3/Magnification/AuditRoutes/**'
  -g '!pnp3/Magnification/FinalResultAuditRoutes.lean'
  -g '!pnp3/Tests/**'
  -g '!pnp3/Docs/**'
  -g '!archive/**'
  -g '!bench/**'
)

echo "[quarantine] (A) typeclass-parameter check"

for pattern in "${typeclass_patterns[@]}"; do
  hits="$(rg -n --no-heading --color=never \
            -g '*.lean' "${typeclass_excludes[@]}" \
            -- "${pattern}" . 2>/dev/null || true)"
  if [[ -n "${hits}" ]]; then
    echo "[quarantine] FAIL: forbidden typeclass-parameter form: ${pattern}"
    echo "${hits}"
    fail=1
  fi
done

# ---------------------------------------------------------------------------
# (B) Bare-name theorem check.
# ---------------------------------------------------------------------------
#
# The bare name `theorem P_ne_NP` must not appear in any active
# magnification / lower-bound file.  Only the suffixed forms
# `P_ne_NP_final`, `P_ne_NP_final_dag_only`, `P_ne_NP_of_researchGap`,
# `Vacuous_P_ne_NP_*`, `RefutedRoute_P_ne_NP_*`, `Conditional_P_ne_NP_*`
# are admissible.

echo "[quarantine] (B) bare-name theorem check (theorem P_ne_NP <delim>)"

# Match `theorem P_ne_NP` followed by exactly one of: end of line, space,
# `:`, `[`, or `(`, but NOT `_` (which would form a suffixed name).
bare_pattern='^[[:space:]]*theorem[[:space:]]+P_ne_NP([[:space:]]|:|\[|\(|$)'

# Bare-theorem search is restricted to magnification / lower-bound trees
# and excludes the audit subtree where Vacuous_* and RefutedRoute_*
# already live (they don't match the bare pattern anyway, but excluding
# them keeps any future audit additions safe).
bare_excludes=(
  -g '!pnp3/Magnification/AuditRoutes/**'
  -g '!pnp3/Magnification/FinalResultAuditRoutes.lean'
  -g '!archive/**'
  -g '!bench/**'
)

bare_hits="$(rg -n --no-heading --color=never \
              -g '*.lean' "${bare_excludes[@]}" \
              -- "${bare_pattern}" pnp3/Magnification pnp3/LowerBounds 2>/dev/null || true)"

if [[ -n "${bare_hits}" ]]; then
  echo "[quarantine] FAIL: bare 'theorem P_ne_NP' detected outside audit zone:"
  echo "${bare_hits}"
  echo "[quarantine]   The canonical name lives in pnp3/Complexity/Interfaces.lean"
  echo "[quarantine]   as a 'def'.  In active magnification / lower-bound code use a"
  echo "[quarantine]   suffixed form: P_ne_NP_final, P_ne_NP_final_dag_only,"
  echo "[quarantine]   P_ne_NP_of_researchGap, Vacuous_P_ne_NP_*,"
  echo "[quarantine]   RefutedRoute_P_ne_NP_*, or Conditional_P_ne_NP_*."
  fail=1
fi

# ---------------------------------------------------------------------------
# Result.
# ---------------------------------------------------------------------------

if [[ "${fail}" -ne 0 ]]; then
  echo
  echo "[quarantine] FAIL"
  echo "[quarantine]   See RESEARCH_CONSTITUTION.md Rule 16,"
  echo "[quarantine]       Phase0_Audit_Surface.md §1.3, and"
  echo "[quarantine]       spec/target.toml::[hidden_payload_channels]."
  exit 1
fi

echo "[quarantine] OK"
