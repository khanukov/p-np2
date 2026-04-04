#!/usr/bin/env bash
# Full project compilation, smoke test, and proof-surface audit.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

if ! command -v rg >/dev/null 2>&1; then
  echo "Missing required dependency: rg (ripgrep). Install ripgrep and rerun." >&2
  exit 127
fi

build_log="/tmp/pnp3_full_build.log"
echo "[check] Step 1/6: full Lean build"
if ! lake build 2>&1 | tee "${build_log}"; then
  echo "Full build failed; see ${build_log} for details."
  exit 1
fi

echo "[check] Step 2/6: smoke execution"
lake env lean --run scripts/smoke.lean

echo "[check] Step 3/6: source hygiene scan (axiom/sorry/native_decide/interface policy)"
expected_axioms=0
actual_axioms=$( (rg "^[[:space:]]*axiom " -g"*.lean" pnp3 || true) | wc -l | tr -d ' ' )
if [[ "${actual_axioms}" -ne "${expected_axioms}" ]]; then
  echo "Expected ${expected_axioms} axioms, found ${actual_axioms}."
  echo "Listing active axioms:"
  rg "^[[:space:]]*axiom " -g"*.lean" pnp3
  exit 1
fi

auto_holes=$( (rg -n "\bsorry\b|\badmit\b" -g"*.lean" pnp3 || true) | wc -l | tr -d ' ' )
if [[ "${auto_holes}" -ne 0 ]]; then
  echo "Found ${auto_holes} unfinished proof placeholders (sorry/admit):"
  rg -n "\bsorry\b|\badmit\b" -g"*.lean" pnp3 || true
  exit 1
fi

native_decide_hits=$( (rg -n "\bnative_decide\b" -g"*.lean" pnp3 || true) | wc -l | tr -d ' ' )
if [[ "${native_decide_hits}" -ne 0 ]]; then
  echo "Found ${native_decide_hits} native_decide usage(s) in pnp3 (for audit strictness we fail):"
  rg -n "\bnative_decide\b" -g"*.lean" pnp3 || true
  exit 1
fi

# Interface naming guardrails:
# - forbid legacy ambiguous names for lightweight non-uniform separation;
# - forbid placeholder-style `NP := True` regressions;
# - keep the active codebase free from lightweight-legacy interfaces.
legacy_name_hits=$( (rg -n "\bNP_not_subset_Ppoly\b|\bNP_strict_not_subset_Ppoly\b|\bP_subset_Ppoly\b|\bP_ne_NP_of_NP_strict_not_subset_Ppoly\b|\bComplexityInterfaces\.Ppoly\b" -g"*.lean" pnp3 || true) | wc -l | tr -d ' ' )
if [[ "${legacy_name_hits}" -ne 0 ]]; then
  echo "Detected legacy ambiguous lightweight-P/poly names (use *PpolyLite variants instead):"
  rg -n "\bNP_not_subset_Ppoly\b|\bNP_strict_not_subset_Ppoly\b|\bP_subset_Ppoly\b|\bP_ne_NP_of_NP_strict_not_subset_Ppoly\b|\bComplexityInterfaces\.Ppoly\b" -g"*.lean" pnp3 || true
  exit 1
fi

if [[ -f pnp3/Complexity/Interfaces_LegacyLite.lean ]]; then
  echo "Detected forbidden legacy interface module: pnp3/Complexity/Interfaces_LegacyLite.lean"
  exit 1
fi

if rg -n "^[[:space:]]*import[[:space:]]+Complexity\\.Interfaces_LegacyLite\\b" -g"*.lean" \
    pnp3 >/tmp/pnp3_legacy_import_hits.log; then
  echo "Detected forbidden import of legacy interface module:"
  cat /tmp/pnp3_legacy_import_hits.log
  exit 1
fi

if [[ -f pnp3/Complexity/Interfaces_InternalSource.lean ]]; then
  echo "Detected forbidden legacy interface module: pnp3/Complexity/Interfaces_InternalSource.lean"
  exit 1
fi

# MCSP-variant guardrails:
# active code must stay on Partial-MCSP names; total-table GapMCSP is legacy.
if rg -n "^[[:space:]]*import[[:space:]]+Models\\.Model_GapMCSP\\b" -g"*.lean" \
    pnp3 >/tmp/pnp3_gapmcsp_import_hits.log; then
  echo "Detected forbidden import of legacy total-table model Models.Model_GapMCSP in active pnp3:"
  cat /tmp/pnp3_gapmcsp_import_hits.log
  exit 1
fi

# Allow the token `GapMCSPParams` only in the explicit third-party interop
# adapter where we map external naming into Partial-MCSP semantics.
if rg -n "\\bGapMCSPParams\\b" -g"*.lean" pnp3 \
    -g"!pnp3/ThirdPartyFacts/PartialLocalityLift.lean" >/tmp/pnp3_gapmcsp_name_hits.log; then
  echo "Detected unexpected GapMCSPParams usage outside the dedicated Partial interop adapter:"
  cat /tmp/pnp3_gapmcsp_name_hits.log
  exit 1
fi

if rg -n "^[[:space:]]*import[[:space:]]+Complexity\\.Interfaces_InternalSource\\b" -g"*.lean" \
    pnp3 >/tmp/pnp3_internal_source_import_hits.log; then
  echo "Detected forbidden import of legacy internal-source interface module:"
  cat /tmp/pnp3_internal_source_import_hits.log
  exit 1
fi

# Retired module guardrails:
# keep removed legacy/compat wrappers from being reintroduced.
retired_modules=(
  "AC0.AC0Formula"
  "AC0.AC0FormulaFamily"
  "AC0.AC0FormulaRestrict"
  "AC0.AC0FormulaWitness"
  "AC0.MultiSwitching.AC0FormulaAtom"
  "AC0.MultiSwitching.FullSwitching"
  "AC0.MultiSwitching.IHInterface"
  "Complexity.PpolyReal_from_Simulation"
  "Complexity.Reductions"
  "LowerBounds.LB_GeneralFromLocal_Partial"
  "LowerBounds.LB_LocalCircuits_Partial"
  "LowerBounds.SolverLocality"
)

for mod in "${retired_modules[@]}"; do
  retired_path="pnp3/${mod//./\/}.lean"
  if [[ -f "${retired_path}" ]]; then
    echo "Detected forbidden retired module reintroduced on disk: ${retired_path}"
    exit 1
  fi
done

for mod in "${retired_modules[@]}"; do
  mod_re="${mod//./\\.}"
  retired_import_log="/tmp/pnp3_retired_import_${mod//./_}.log"
  if rg -n "^[[:space:]]*import[[:space:]]+${mod_re}\\b" -g"*.lean" \
      pnp3 >"${retired_import_log}"; then
    echo "Detected forbidden import of retired module ${mod}:"
    cat "${retired_import_log}"
    exit 1
  fi
done

if rg -n "PpolyLite|P_subset_PpolyLite|NP_not_subset_PpolyLite|Ppoly_to_PpolyFormulaDepth|FormulaSeparationToNonuniformBridge|RealSeparationToNonuniformBridge|LightweightToRealBridge|PpolyStructured" \
    pnp3/Complexity/Interfaces.lean >/tmp/pnp3_strict_iface_legacy_leak_hits.log; then
  echo "Detected legacy lightweight API leaked into strict interface (Complexity/Interfaces.lean):"
  cat /tmp/pnp3_strict_iface_legacy_leak_hits.log
  exit 1
fi

if rg -n "\\bPpolyLite\\b" -g"*.lean" pnp3 >/tmp/pnp3_legacy_ppolylite_hits.log; then
  echo "Detected forbidden lightweight alias PpolyLite in active pnp3 sources:"
  cat /tmp/pnp3_legacy_ppolylite_hits.log
  exit 1
fi

if rg -n "^[[:space:]]*abbrev[[:space:]]+Ppoly[[:space:]]*:" pnp3/Complexity/Interfaces.lean >/tmp/pnp3_legacy_ppoly_alias_hits.log; then
  echo "Detected forbidden alias 'abbrev Ppoly' in Complexity/Interfaces.lean:"
  cat /tmp/pnp3_legacy_ppoly_alias_hits.log
  exit 1
fi

if rg -n -U "^[[:space:]]*(def|abbrev)[[:space:]]+NP([[:space:]_(]|$)[^\n]*\n?[[:space:]]*:=\s*True\b" pnp3/Complexity/Interfaces.lean >/tmp/pnp3_np_true_hits.log; then
  echo "Detected forbidden placeholder definition of NP as True:"
  cat /tmp/pnp3_np_true_hits.log
  exit 1
fi

# Magnification assumptions policy guardrails:
# - in the default RC/milestone mode, assumption bundles must be present and
#   package-style signatures remain required for the canonical public finals;
# - in `UNCONDITIONAL=1` mode, those package-signature requirements are
#   intentionally suspended because the public finals are expected to become
#   assumption-free (the dedicated unconditional gate below checks that state);
# - old default-provider signatures for active finals are forbidden in all modes.
final_result_surface_files=(
  "pnp3/Magnification/FinalResult.lean"
  "pnp3/Magnification/FinalResultCore.lean"
  "pnp3/Magnification/FinalResultMainline.lean"
  "pnp3/Magnification/FinalResultWeakRoutes.lean"
  "pnp3/Magnification/FinalResultLegacyTM.lean"
)

if [[ "${UNCONDITIONAL:-0}" != "1" ]]; then
  if ! rg -n "^[[:space:]]*structure[[:space:]]+SwitchingAssumptions\\b" \
      "${final_result_surface_files[@]}" >/tmp/pnp3_switching_assumptions_hits.log; then
    echo "Missing required assumptions package: SwitchingAssumptions"
    exit 1
  fi

  if ! rg -n "^[[:space:]]*structure[[:space:]]+AntiCheckerAssumptions\\b" \
      "${final_result_surface_files[@]}" >/tmp/pnp3_antichecker_assumptions_hits.log; then
    echo "Missing required assumptions package: AntiCheckerAssumptions"
    exit 1
  fi

  if ! rg -n "^[[:space:]]*structure[[:space:]]+MagnificationAssumptions\\b" \
      "${final_result_surface_files[@]}" >/tmp/pnp3_magnification_assumptions_hits.log; then
    echo "Missing required assumptions package: MagnificationAssumptions"
    exit 1
  fi

  if ! rg -n -U "theorem[[:space:]]+NP_not_subset_PpolyFormula_final\\n[[:space:]]*\\(hMag[[:space:]]*:[[:space:]]*MagnificationAssumptions\\)" \
      "${final_result_surface_files[@]}" >/tmp/pnp3_formula_final_pkg_sig_hits.log; then
    echo "Detected non-package signature for NP_not_subset_PpolyFormula_final (expected hMag : MagnificationAssumptions)."
    exit 1
  fi

  if ! rg -n -U "theorem[[:space:]]+NP_not_subset_PpolyReal_final\\n[[:space:]]*\\(hMag[[:space:]]*:[[:space:]]*MagnificationAssumptions\\)" \
      "${final_result_surface_files[@]}" >/tmp/pnp3_real_final_pkg_sig_hits.log; then
    echo "Detected non-package signature for NP_not_subset_PpolyReal_final (expected hMag : MagnificationAssumptions)."
    exit 1
  fi

  if ! rg -n -U "theorem[[:space:]]+P_ne_NP_final\\n[[:space:]]*\\(hMag[[:space:]]*:[[:space:]]*MagnificationAssumptions\\)" \
      "${final_result_surface_files[@]}" >/tmp/pnp3_pnenp_final_pkg_sig_hits.log; then
    echo "Detected non-package signature for P_ne_NP_final (expected hMag : MagnificationAssumptions)."
    exit 1
  fi
fi

if rg -n -U "theorem[[:space:]]+NP_not_subset_PpolyFormula_final\\n[[:space:]]*\\(hDefaultProvider[[:space:]]*:[[:space:]]*hasDefaultStructuredLocalityProviderPartial\\)" \
    "${final_result_surface_files[@]}" >/tmp/pnp3_formula_final_default_sig_hits.log; then
  echo "Detected forbidden default-provider signature for NP_not_subset_PpolyFormula_final:"
  cat /tmp/pnp3_formula_final_default_sig_hits.log
  exit 1
fi

if rg -n -U "theorem[[:space:]]+NP_not_subset_PpolyReal_final\\n[[:space:]]*\\(hDefaultProvider[[:space:]]*:[[:space:]]*hasDefaultStructuredLocalityProviderPartial\\)" \
    "${final_result_surface_files[@]}" >/tmp/pnp3_real_final_default_sig_hits.log; then
  echo "Detected forbidden default-provider signature for NP_not_subset_PpolyReal_final:"
  cat /tmp/pnp3_real_final_default_sig_hits.log
  exit 1
fi

if [[ "${UNCONDITIONAL:-0}" != "1" ]]; then
  if rg -n -U "theorem[[:space:]]+P_ne_NP_final\\n[[:space:]]*\\(hNPDag[[:space:]]*:[[:space:]]*ComplexityInterfaces\\.NP_not_subset_PpolyDAG\\)" \
      "${final_result_surface_files[@]}" >/tmp/pnp3_pnenp_final_legacy_sig_hits.log; then
    echo "Detected forbidden legacy signature for P_ne_NP_final (missing MagnificationAssumptions):"
    cat /tmp/pnp3_pnenp_final_legacy_sig_hits.log
    exit 1
  fi
fi

echo "Axiom inventory OK (${actual_axioms} axioms)."
echo "Proof hole scan OK (no sorry/admit)."
echo "native_decide scan OK (no occurrences)."
echo "Interface naming policy OK (legacy aliases/modules blocked; strict interface enforced)."
if [[ "${UNCONDITIONAL:-0}" == "1" ]]; then
  echo "Magnification assumptions policy OK (unconditional mode: package-signature requirements suspended)."
else
  echo "Magnification assumptions policy OK (package-based finals enforced)."
fi

echo "[check] Step 4/6: explicit theorem-axiom surface dump"
axiom_surface_log="/tmp/pnp3_axiom_surface.log"
if ! rg -n -U "pnp3/Tests/AxiomsAudit\\.lean:[^\\n]*depends on axioms:\\s*\\[[^\\]]*\\]" \
    "${build_log}" >"${axiom_surface_log}"; then
  # Fallback for environments where replayed info lines are suppressed.
  lake env lean pnp3/Tests/AxiomsAudit.lean > "${axiom_surface_log}" 2>&1
fi

# Hard-fail if trusted compiler reduction axioms show up in audited theorem cone.
if rg -n "Lean\.ofReduceBool|Lean\.trustCompiler" "${axiom_surface_log}" >/tmp/pnp3_trust_hits.log; then
  echo "Detected trusted-compiler reduction axioms in audited theorem surface:"
  cat /tmp/pnp3_trust_hits.log
  exit 1
fi

# Always print a compact assumption summary to make external dependencies explicit.
# These assumptions are expected in the current development stage.
classical_count=$( (rg -n "Classical\.choice" "${axiom_surface_log}" || true) | wc -l | tr -d ' ' )
propext_count=$( (rg -n "\bpropext\b" "${axiom_surface_log}" || true) | wc -l | tr -d ' ' )
quot_count=$( (rg -n "Quot\.sound" "${axiom_surface_log}" || true) | wc -l | tr -d ' ' )
echo "Axiom surface summary (from Tests/AxiomsAudit):"
echo "  propext occurrences: ${propext_count}"
echo "  Classical.choice occurrences: ${classical_count}"
echo "  Quot.sound occurrences: ${quot_count}"

echo "[check] Step 5/6: run barrier audit module"
if ! rg -n "pnp3/Tests/BarrierAudit\\.lean" "${build_log}" >/tmp/pnp3_barrier_audit.log; then
  # Keep this explicit so regressions in barrier-facing final statements are visible.
  lake env lean pnp3/Tests/BarrierAudit.lean >/tmp/pnp3_barrier_audit.log 2>&1
fi

echo "[check] Step 6/6: unconditional witness gate (optional)"
if [[ "${UNCONDITIONAL:-0}" == "1" ]]; then
  echo "Checking unconditional witness surface..."
  # Legacy witness surface markers (historical blockers).
  if rg -n "ppoly_circuit_locality|FamilyIsLocalCircuit|hF_all" \
      pnp3/Magnification pnp3/LowerBounds/AntiChecker_Partial.lean >/tmp/pnp3_unconditional_gaps_legacy.txt; then
    echo "Unconditional gate failed: remaining external witness/axiom surface detected:"
    cat /tmp/pnp3_unconditional_gaps_legacy.txt
    exit 1
  fi

  # Final-cone blockers that must be internalized for unconditional status.
  #
  # IMPORTANT: this gate tracks explicit *external bridge assumptions* only.
  # Internal helper theorems may legitimately mention classes like
  # `P_subset_PpolyDAG`; such occurrences must not cause unconditional failure.
  if rg -n "hFormulaToPpoly|hRealToPpoly|FormulaSeparationToNonuniformBridge|RealSeparationToNonuniformBridge|hPsubsetReal|hFormulaInclusion|hPsubsetDag" \
      "${final_result_surface_files[@]}" pnp3/Barrier/Bypass.lean >/tmp/pnp3_unconditional_gaps_bridge.txt; then
    echo "Unconditional gate failed: final route still depends on an external non-uniform inclusion/bridge assumption:"
    cat /tmp/pnp3_unconditional_gaps_bridge.txt
    exit 1
  fi

  # Guardrail: no lightweight-Ppoly aliases in final theorem cone once migrated.
  if rg -n "PpolyLite" \
      "${final_result_surface_files[@]}" pnp3/Barrier/Bypass.lean >/tmp/pnp3_unconditional_gaps_lite.txt; then
    echo "Unconditional gate failed: lightweight Ppoly alias leaked into final cone:"
    cat /tmp/pnp3_unconditional_gaps_lite.txt
    exit 1
  fi

  # Canonical public finals must themselves become assumption-free before the
  # tree can be described as unconditionally closed. We intentionally scope
  # this to the public endpoints, not the specialized compatibility wrappers
  # (`*_of_*`, `*_TM`, barrier/audit helpers), which may remain conditional as
  # long as they are documented as non-default routes.
  if rg -n -U "theorem[[:space:]]+NP_not_subset_PpolyFormula_final\\n[[:space:]]*\\(hMag[[:space:]]*:[[:space:]]*MagnificationAssumptions\\)" \
      "${final_result_surface_files[@]}" >/tmp/pnp3_unconditional_formula_pkg_hits.log; then
    echo "Unconditional gate failed: canonical formula final still depends on MagnificationAssumptions:"
    cat /tmp/pnp3_unconditional_formula_pkg_hits.log
    exit 1
  fi

  if rg -n -U "theorem[[:space:]]+NP_not_subset_PpolyReal_final\\n[[:space:]]*\\(hMag[[:space:]]*:[[:space:]]*MagnificationAssumptions\\)" \
      "${final_result_surface_files[@]}" >/tmp/pnp3_unconditional_real_pkg_hits.log; then
    echo "Unconditional gate failed: canonical PpolyReal final still depends on MagnificationAssumptions:"
    cat /tmp/pnp3_unconditional_real_pkg_hits.log
    exit 1
  fi

  if rg -n -U "theorem[[:space:]]+P_ne_NP_final\\n[[:space:]]*\\(hMag[[:space:]]*:[[:space:]]*MagnificationAssumptions\\)" \
      "${final_result_surface_files[@]}" >/tmp/pnp3_unconditional_pnenp_pkg_hits.log; then
    echo "Unconditional gate failed: canonical P_ne_NP final still depends on MagnificationAssumptions:"
    cat /tmp/pnp3_unconditional_pnenp_pkg_hits.log
    exit 1
  fi

  if rg -n -U "theorem[[:space:]]+P_ne_NP_final\\n(?:[[:space:]]*\\([^\\n]*\\)\\n)*[[:space:]]*\\(hNPDag[[:space:]]*:[[:space:]]*(?:ComplexityInterfaces\\.)?NP_not_subset_PpolyDAG\\)" \
      "${final_result_surface_files[@]}" >/tmp/pnp3_unconditional_pnenp_dag_hits.log; then
    echo "Unconditional gate failed: canonical P_ne_NP final still depends on NP_not_subset_PpolyDAG:"
    cat /tmp/pnp3_unconditional_pnenp_dag_hits.log
    exit 1
  fi
  echo "Unconditional witness surface OK."
fi

echo "[check] All checks passed."
