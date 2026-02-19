#!/usr/bin/env bash
# Full project compilation, smoke test, and axiom inventory check.
set -euo pipefail

have_rg=0
if command -v rg >/dev/null 2>&1; then
  have_rg=1
fi

search_regex() {
  local pattern="$1"
  shift
  if [[ "${have_rg}" -eq 1 ]]; then
    rg "$pattern" "$@"
  else
    grep -R -n -E --include='*.lean' "$pattern" "$@"
  fi
}

search_fixed_quiet() {
  local needle="$1"
  local file="$2"
  if [[ "${have_rg}" -eq 1 ]]; then
    rg -Fq "$needle" "$file"
  else
    grep -Fq "$needle" "$file"
  fi
}

lake build
lake env lean --run scripts/smoke.lean

echo "Checking that pnp3 contains no sorry/admit placeholders..."
if search_regex "^[[:space:]]*(sorry|admit)\\>|:=[[:space:]]*by[[:space:]]*(sorry|admit)\\>" pnp3; then
  echo "Found forbidden placeholders (sorry/admit) in pnp3/*.lean."
  exit 1
fi
echo "No sorry/admit placeholders in pnp3."

echo "Checking active axiom inventory..."
# Two external Hirahara (2022) results are intentionally imported as axioms:
# `ThirdPartyFacts.PartialMCSP_profile_is_NP_Hard_rpoly`
# `ThirdPartyFacts.PartialMCSP_is_NP_Hard`
# Plus one explicit localized-witness scaffold for the partial general→local bridge:
# `ThirdPartyFacts.localizedFamilyWitness_partial`
expected_axioms=3
actual_axioms=$(search_regex "^[[:space:]]*axiom " pnp3 | wc -l | tr -d ' ')
if [[ "${actual_axioms}" -ne "${expected_axioms}" ]]; then
  echo "Expected ${expected_axioms} axioms, found ${actual_axioms}."
  echo "Listing active axioms:"
  search_regex "^[[:space:]]*axiom " pnp3
  exit 1
fi
echo "Axiom inventory OK (${actual_axioms} axioms)."

echo "Checking final-theorem axiom dependencies (AxiomsAudit)..."
audit_output="$(lake env lean pnp3/Tests/AxiomsAudit.lean 2>&1)"
normalized_output="$(printf '%s\n' "${audit_output}" | tr '\n' ' ' | tr -s ' ')"
expected_count=12
total_lines_count="$(printf '%s\n' "${normalized_output}" | grep -o "depends on axioms: \[" | wc -l | tr -d ' ')"
allowed_base_count="$(printf '%s\n' "${normalized_output}" | grep -o "depends on axioms: \[propext, Classical.choice, Quot.sound\]" | wc -l | tr -d ' ')"
allowed_localized_count="$(printf '%s\n' "${normalized_output}" | grep -o "depends on axioms: \[propext, Classical.choice, Quot.sound, Pnp3.ThirdPartyFacts.localizedFamilyWitness_partial\]" | wc -l | tr -d ' ')"
allowed_total_count=$((allowed_base_count + allowed_localized_count))
if [[ "${total_lines_count}" -ne "${expected_count}" || "${allowed_total_count}" -ne "${expected_count}" || "${allowed_localized_count}" -ne 2 ]]; then
  echo "Unexpected axiom dependencies in pnp3/Tests/AxiomsAudit.lean."
  echo "Expected exactly ${expected_count} lines total:"
  echo "  - ten with [propext, Classical.choice, Quot.sound]"
  echo "  - two with [propext, Classical.choice, Quot.sound, Pnp3.ThirdPartyFacts.localizedFamilyWitness_partial]"
  echo
  printf '%s\n' "${audit_output}"
  exit 1
fi
echo "AxiomsAudit OK (${expected_count} target theorems; localized witness scaffold appears exactly twice in final-layer theorems)."

echo "Checking core-cone axiom dependencies (CoreConeAxiomsAudit)..."
core_audit_output="$(lake env lean pnp3/Tests/CoreConeAxiomsAudit.lean 2>&1)"
core_normalized_output="$(printf '%s\n' "${core_audit_output}" | tr '\n' ' ' | tr -s ' ')"
core_expected_count=8
core_total_lines_count="$(printf '%s\n' "${core_normalized_output}" | grep -o "depends on axioms: \[" | wc -l | tr -d ' ')"
core_allowed_base_count="$(printf '%s\n' "${core_normalized_output}" | grep -o "depends on axioms: \[propext, Classical.choice, Quot.sound\]" | wc -l | tr -d ' ')"
if [[ "${core_total_lines_count}" -ne "${core_expected_count}" || "${core_allowed_base_count}" -ne "${core_expected_count}" ]]; then
  echo "Unexpected axiom dependencies in pnp3/Tests/CoreConeAxiomsAudit.lean."
  echo "Expected exactly ${core_expected_count} lines with: [propext, Classical.choice, Quot.sound]"
  echo
  printf '%s\n' "${core_audit_output}"
  exit 1
fi
echo "CoreConeAxiomsAudit OK (${core_expected_count} theorems; no project-specific axioms)."

echo "Checking publication gap list consistency..."
gap_doc="PUBLICATION_GAPS_AND_GUARANTEES.md"
if [[ ! -f "${gap_doc}" ]]; then
  echo "Missing ${gap_doc}."
  exit 1
fi

expected_gap_axioms=(
  "ThirdPartyFacts.PartialMCSP_profile_is_NP_Hard_rpoly"
  "ThirdPartyFacts.PartialMCSP_is_NP_Hard"
  "ThirdPartyFacts.localizedFamilyWitness_partial"
)
for ax in "${expected_gap_axioms[@]}"; do
  if ! search_fixed_quiet "${ax}" "${gap_doc}"; then
    echo "Publication gap doc is missing axiom name: ${ax}"
    exit 1
  fi
done

actual_axiom_names="$(search_regex "^[[:space:]]*axiom " pnp3 | sed -E 's/.*axiom[[:space:]]+([A-Za-z0-9_]+).*/\1/' | sort -u)"
for name in ${actual_axiom_names}; do
  if ! search_fixed_quiet "${name}" "${gap_doc}"; then
    echo "Publication gap doc does not mention active axiom: ${name}"
    exit 1
  fi
done
echo "Publication gap list is consistent with active axioms."
