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
echo "[check] Step 1/16: full Lean build"
# Both libs (`PnP3` and `Pnp4`) must be built here: Step 7/9 inspects
# pnp4's axiom-surface dump, which only appears in the build log when
# Pnp4 is actually compiled.  Plain `lake build` only builds the
# `@[default_target]` (PnP3), so we name both libraries explicitly.
if ! lake build PnP3 Pnp4 2>&1 | tee "${build_log}"; then
  echo "Full build failed; see ${build_log} for details."
  exit 1
fi

echo "[check] Step 2/16: smoke execution"
lake env lean --run scripts/smoke.lean

echo "[check] Step 3/16: source hygiene scan (axiom/sorry/native_decide/interface policy)"
expected_axioms=0
actual_axioms_pnp3=$( (rg "^[[:space:]]*axiom " -g"*.lean" pnp3 || true) | wc -l | tr -d ' ' )
if [[ "${actual_axioms_pnp3}" -ne "${expected_axioms}" ]]; then
  echo "Expected ${expected_axioms} axioms in pnp3, found ${actual_axioms_pnp3}."
  echo "Listing active axioms in pnp3:"
  rg "^[[:space:]]*axiom " -g"*.lean" pnp3
  exit 1
fi

actual_axioms_pnp4=$( (rg "^[[:space:]]*axiom " -g"*.lean" pnp4 || true) | wc -l | tr -d ' ' )
if [[ "${actual_axioms_pnp4}" -ne "${expected_axioms}" ]]; then
  echo "Expected ${expected_axioms} axioms in pnp4, found ${actual_axioms_pnp4}."
  echo "Listing active axioms in pnp4:"
  rg "^[[:space:]]*axiom " -g"*.lean" pnp4
  exit 1
fi

auto_holes=$( (rg -n "\bsorry\b|\badmit\b" -g"*.lean" pnp3 || true) | wc -l | tr -d ' ' )
if [[ "${auto_holes}" -ne 0 ]]; then
  echo "Found ${auto_holes} unfinished proof placeholders (sorry/admit) in pnp3:"
  rg -n "\bsorry\b|\badmit\b" -g"*.lean" pnp3 || true
  exit 1
fi

auto_holes_pnp4=$( (rg -n "\bsorry\b|\badmit\b" -g"*.lean" pnp4 || true) | wc -l | tr -d ' ' )
if [[ "${auto_holes_pnp4}" -ne 0 ]]; then
  echo "Found ${auto_holes_pnp4} unfinished proof placeholders (sorry/admit) in pnp4:"
  rg -n "\bsorry\b|\badmit\b" -g"*.lean" pnp4 || true
  exit 1
fi

native_decide_hits=$( (rg -n "\bnative_decide\b" -g"*.lean" pnp3 || true) | wc -l | tr -d ' ' )
if [[ "${native_decide_hits}" -ne 0 ]]; then
  echo "Found ${native_decide_hits} native_decide usage(s) in pnp3 (for audit strictness we fail):"
  rg -n "\bnative_decide\b" -g"*.lean" pnp3 || true
  exit 1
fi

native_decide_hits_pnp4=$( (rg -n "\bnative_decide\b" -g"*.lean" pnp4 || true) | wc -l | tr -d ' ' )
if [[ "${native_decide_hits_pnp4}" -ne 0 ]]; then
  echo "Found ${native_decide_hits_pnp4} native_decide usage(s) in pnp4 (for audit strictness we fail):"
  rg -n "\bnative_decide\b" -g"*.lean" pnp4 || true
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
  "pnp3/Magnification/FinalResultAuditRoutes.lean"
  "pnp3/Magnification/FinalResultCore.lean"
  "pnp3/Magnification/FinalResultMainline.lean"
  "pnp3/Magnification/FinalResultWeakRoutes.lean"
  "pnp3/Magnification/FinalResultLegacyTM.lean"
  "pnp3/Magnification/UnconditionalResearchGap.lean"
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

  # Research Governance v0.1, PR 3b: bare `NP_not_subset_PpolyFormula_final`
  # and `NP_not_subset_PpolyReal_final` (with `MagnificationAssumptions`
  # premise) are direct-refuted finals and have been renamed to
  # `RefutedRoute_*`.  We require the renamed forms to exist for audit
  # continuity.  Reintroduction of the unprefixed names is blocked by
  # `scripts/check_refuted_route_quarantine.sh` (Step 6/11).
  if ! rg -n -U "theorem[[:space:]]+RefutedRoute_NP_not_subset_PpolyFormula_final\\n[[:space:]]*\\(hMag[[:space:]]*:[[:space:]]*MagnificationAssumptions\\)" \
      "${final_result_surface_files[@]}" >/tmp/pnp3_formula_final_pkg_sig_hits.log; then
    echo "Detected non-package signature for RefutedRoute_NP_not_subset_PpolyFormula_final (expected hMag : MagnificationAssumptions)."
    exit 1
  fi

  if ! rg -n -U "theorem[[:space:]]+RefutedRoute_NP_not_subset_PpolyReal_final\\n[[:space:]]*\\(hMag[[:space:]]*:[[:space:]]*MagnificationAssumptions\\)" \
      "${final_result_surface_files[@]}" >/tmp/pnp3_real_final_pkg_sig_hits.log; then
    echo "Detected non-package signature for RefutedRoute_NP_not_subset_PpolyReal_final (expected hMag : MagnificationAssumptions)."
    exit 1
  fi

  # Current milestone policy:
  # the public DAG/P != NP finals are the honest research-gap boundary.  Legacy
  # hMS/asymptotic-pullback routes must stay under explicit audit/compatibility
  # names such as `*_of_multiswitchingData` and `*_of_asymptoticPullback`.
  if ! rg -n -U \
      "theorem[[:space:]]+NP_not_subset_PpolyDAG_final\\n[[:space:]]*\\(gap[[:space:]]*:[[:space:]]*ResearchGapWitness\\)" \
      "${final_result_surface_files[@]}" >/tmp/pnp3_npdag_final_gap_sig_hits.log; then
    echo "Detected invalid signature for NP_not_subset_PpolyDAG_final (expected gap : ResearchGapWitness)."
    exit 1
  fi

  if ! rg -n -U \
      "theorem[[:space:]]+P_ne_NP_final\\n[[:space:]]*\\(gap[[:space:]]*:[[:space:]]*ResearchGapWitness\\)" \
      "${final_result_surface_files[@]}" >/tmp/pnp3_pnenp_final_gap_sig_hits.log; then
    echo "Detected invalid signature for P_ne_NP_final (expected gap : ResearchGapWitness)."
    exit 1
  fi
fi

# Research Governance v0.1, PR 3b: forbid resurrecting the bare
# `NP_not_subset_PpolyFormula_final` / `NP_not_subset_PpolyReal_final`
# names in any form (including the legacy `hDefaultProvider` shape).
# The renamed `RefutedRoute_*` forms keep their `hMag` package signature
# above; `check_refuted_route_quarantine.sh` (Step 6/11) blocks the
# reverse rename.
if rg -n -U "theorem[[:space:]]+NP_not_subset_PpolyFormula_final\\b" \
    "${final_result_surface_files[@]}" >/tmp/pnp3_formula_final_unmarked_hits.log; then
  echo "Detected forbidden unprefixed bare _final endpoint for NP_not_subset_PpolyFormula_final."
  echo "Use RefutedRoute_NP_not_subset_PpolyFormula_final (or _fromPipeline) per PR 3b:"
  cat /tmp/pnp3_formula_final_unmarked_hits.log
  exit 1
fi

if rg -n -U "theorem[[:space:]]+NP_not_subset_PpolyReal_final\\b" \
    "${final_result_surface_files[@]}" >/tmp/pnp3_real_final_unmarked_hits.log; then
  echo "Detected forbidden unprefixed bare _final endpoint for NP_not_subset_PpolyReal_final."
  echo "Use RefutedRoute_NP_not_subset_PpolyReal_final (or _fromPipeline) per PR 3b:"
  cat /tmp/pnp3_real_final_unmarked_hits.log
  exit 1
fi

if [[ "${UNCONDITIONAL:-0}" != "1" ]]; then
  if rg -n -U \
      "theorem[[:space:]]+NP_not_subset_PpolyDAG_final\\n[[:space:]]*\\(hMS[[:space:]]*:[[:space:]]*AC0LocalityBridge\\.FormulaSupportBoundsFromMultiSwitchingContract\\)" \
      "${final_result_surface_files[@]}" >/tmp/pnp3_npdag_final_hms_sig_hits.log; then
    echo "Detected forbidden legacy signature for NP_not_subset_PpolyDAG_final (use *_of_multiswitchingData / *_of_asymptoticPullback):"
    cat /tmp/pnp3_npdag_final_hms_sig_hits.log
    exit 1
  fi

  if rg -n -U \
      "theorem[[:space:]]+P_ne_NP_final\\n[[:space:]]*\\(hMS[[:space:]]*:[[:space:]]*AC0LocalityBridge\\.FormulaSupportBoundsFromMultiSwitchingContract\\)" \
      "${final_result_surface_files[@]}" >/tmp/pnp3_pnenp_final_hms_sig_hits.log; then
    echo "Detected forbidden legacy signature for P_ne_NP_final (use *_of_multiswitchingData / *_of_asymptoticPullback):"
    cat /tmp/pnp3_pnenp_final_hms_sig_hits.log
    exit 1
  fi

  if rg -n -U "theorem[[:space:]]+P_ne_NP_final\\n[[:space:]]*\\(hNPDag[[:space:]]*:[[:space:]]*ComplexityInterfaces\\.NP_not_subset_PpolyDAG\\)" \
      "${final_result_surface_files[@]}" >/tmp/pnp3_pnenp_final_legacy_sig_hits.log; then
    echo "Detected forbidden legacy signature for P_ne_NP_final (missing MagnificationAssumptions):"
    cat /tmp/pnp3_pnenp_final_legacy_sig_hits.log
    exit 1
  fi

  if rg -n -U "theorem[[:space:]]+(NP_not_subset_PpolyDAG_final|P_ne_NP_final)_of_asymptotic[^\\n]*\\n[[:space:]]*\\(hMag[[:space:]]*:[[:space:]]*MagnificationAssumptions\\)" \
      pnp3/Magnification/FinalResultMainline.lean >/tmp/pnp3_mainline_hmag_dag_route_hits.log; then
    echo "Detected package-shaped DAG route in FinalResultMainline; move legacy hMag wrappers to FinalResultAuditRoutes:"
    cat /tmp/pnp3_mainline_hmag_dag_route_hits.log
    exit 1
  fi
fi

echo "Axiom inventory OK (pnp3=${actual_axioms_pnp3}, pnp4=${actual_axioms_pnp4})."
echo "Proof hole scan OK (no sorry/admit in pnp3 or pnp4)."
echo "native_decide scan OK (no occurrences in pnp3 or pnp4)."
echo "Interface naming policy OK (legacy aliases/modules blocked; strict interface enforced)."
if [[ "${UNCONDITIONAL:-0}" == "1" ]]; then
  echo "Magnification assumptions policy OK (unconditional mode: package-signature requirements suspended)."
else
  echo "Magnification assumptions policy OK (package-based formula/real finals + ResearchGapWitness public P != NP final enforced)."
fi

# Documentation route-policy guardrails:
# keep canonical docs aligned on the current falsifiability audit and prevent
# silent reintroduction of deprecated DAG-route wording.
route_docs=(
  "STATUS.md"
  "TODO.md"
  "CHECKLIST_UNCONDITIONAL_P_NE_NP.md"
  "pnp3/Docs/Unconditional_NP_not_subset_PpolyDAG_Plan.md"
  "pnp3/Docs/Simulation_FineGrained_Status.md"
  "pnp3/Docs/Research_Method_Boundary.md"
  "pnp3/Docs/CLOSURE_ROUTE_POLICY.md"
)

for f in "${route_docs[@]}"; do
  if [[ ! -f "${f}" ]]; then
    echo "Missing required route-policy document: ${f}"
    exit 1
  fi
done

# Hard requirement: canonical docs must explicitly mention fixed-slice no-go
# status, the refuted support-bounds/multi-switching route, and the current
# fixed-params candidate boundary.
if ! rg -n "fixed-slice.*no-go|no-go.*fixed-slice" "${route_docs[@]}" >/tmp/pnp3_route_nogo_hits.log; then
  echo "Route-policy violation: canonical docs do not explicitly state fixed-slice no-go status."
  exit 1
fi

if ! rg -n "FormulaSupportRestrictionBoundsPartial.*False|FormulaSupportBoundsFromMultiSwitchingContract.*False|support-bounds.*ex-falso|support-bounds.*false|refuted support-bounds" "${route_docs[@]}" >/tmp/pnp3_route_refuted_support_hits.log; then
  echo "Route-policy violation: canonical docs do not explicitly state the refuted support-bounds route."
  exit 1
fi

if ! rg -n "fixedParams|FormulaSupportBoundsPartial_fromPipeline_fixedParams" "${route_docs[@]}" >/tmp/pnp3_route_fixedparams_hits.log; then
  echo "Route-policy violation: canonical docs do not explicitly state the fixedParams candidate boundary."
  exit 1
fi

if ! rg -n "fixedParams.*uniformProvenance.*inconsistent|fixedParams.*uniform provenance.*inconsistent|fixedParams \\+ uniformProvenance" "${route_docs[@]}" >/tmp/pnp3_route_fixedparams_leak_hits.log; then
  echo "Route-policy violation: canonical docs do not state the fixedParams + uniformProvenance leak."
  exit 1
fi

if ! rg -n "coarse.*P_subset_PpolyDAG|P_subset_PpolyDAG.*coarse|not.*fine-grained.*compiler|fine-grained.*simulation adequacy|absence of a.*fine-grained compiler" "${route_docs[@]}" >/tmp/pnp3_route_simulation_boundary_hits.log; then
  echo "Route-policy violation: canonical docs do not state the coarse simulation / fine-grained compiler boundary."
  exit 1
fi

if ! rg -n "ResearchGapWitness.*method-agnostic|method-agnostic.*ResearchGapWitness|AcceptedFamilyCertificateAt.*optional|optional.*AcceptedFamilyCertificateAt" "${route_docs[@]}" >/tmp/pnp3_route_method_boundary_hits.log; then
  echo "Route-policy violation: canonical docs do not state the method-agnostic ResearchGapWitness / optional accepted-family boundary."
  exit 1
fi

if ! rg -n "Green CI.*not.*mathematical progress|green CI.*not.*mathematical progress|check\\.sh.*not.*mathematical progress|proof hygiene.*not.*mathematical progress" "${route_docs[@]}" >/tmp/pnp3_route_devops_boundary_hits.log; then
  echo "Route-policy violation: canonical docs do not state the CI/check.sh proof-hygiene boundary."
  exit 1
fi

if rg -n -U "Current public provider-shaped endpoint|The active explicit DAG endpoint still has this shape|P_ne_NP_final\\n[[:space:]]*\\(hMS[[:space:]]*:" \
    "${route_docs[@]}" >/tmp/pnp3_route_stale_public_endpoint_hits.log; then
  echo "Detected stale public-endpoint wording in canonical docs:"
  cat /tmp/pnp3_route_stale_public_endpoint_hits.log
  exit 1
fi

# Forbidden legacy wording: these phrases historically pointed to deprecated
# DAG-side closure prioritization and should not reappear in canonical docs.
if rg -n 'Fastest path to remove `hNPDag`|Pick a fixed slice|prove one fixed-slice DAG source theorem|asymptotic/eventual source theorem|Only one route is still active for true unconditionality|Only API cleanup remains' \
    "${route_docs[@]}" >/tmp/pnp3_route_legacy_phrase_hits.log; then
  echo "Detected deprecated fixed-slice closure wording in canonical docs:"
  cat /tmp/pnp3_route_legacy_phrase_hits.log
  exit 1
fi

echo "Route policy docs OK (fixed-slice no-go + refuted support-bounds + fixedParams + simulation + method/DevOps boundaries enforced)."

# Agent policy guardrails:
# Keep the repository-level coding-agent instructions aligned with the current
# P-vs-NP mainline decision: restricted pnp4 lower bounds are side-track work
# unless they bridge to `VerifiedNPDAGLowerBoundSource` / `PpolyDAG`.
agent_policy_docs=(
  "AGENTS.md"
  "pnp4/README.md"
)

for f in "${agent_policy_docs[@]}"; do
  if [[ ! -f "${f}" ]]; then
    echo "Missing required agent-policy document: ${f}"
    exit 1
  fi
done

if ! rg -n "SearchMCSPWeakLowerBound" "${agent_policy_docs[@]}" >/tmp/pnp4_agent_policy_search_mcsp_hits.log; then
  echo "Agent-policy violation: pnp4 mainline does not mention SearchMCSPWeakLowerBound."
  exit 1
fi

if ! rg -n "VerifiedNPDAGLowerBoundSource" "${agent_policy_docs[@]}" >/tmp/pnp4_agent_policy_verified_source_hits.log; then
  echo "Agent-policy violation: pnp4 mainline does not mention VerifiedNPDAGLowerBoundSource."
  exit 1
fi

if ! rg -n "AC0\\[p\\].*side track|side track.*AC0\\[p\\]|restricted.*side track|side track.*restricted" \
    "${agent_policy_docs[@]}" >/tmp/pnp4_agent_policy_side_track_hits.log; then
  echo "Agent-policy violation: restricted pnp4 lower bounds are not documented as side track."
  exit 1
fi

if ! rg -n "PpolyDAG" "${agent_policy_docs[@]}" >/tmp/pnp4_agent_policy_ppolydag_hits.log; then
  echo "Agent-policy violation: pnp4 mainline does not mention the PpolyDAG endpoint."
  exit 1
fi

echo "Agent policy docs OK (pnp4 P-vs-NP mainline + restricted side-track boundary enforced)."

echo "[check] Step 4/16: doc-honesty linter (Research Governance v0.1, Rule 1)"
"${ROOT_DIR}/scripts/check_doc_honesty.sh"

echo "[check] Step 5/16: typeclass-payload quarantine (Research Governance v0.1, Rule 16)"
"${ROOT_DIR}/scripts/check_typeclass_payload_quarantine.sh"

echo "[check] Step 6/16: refuted-route quarantine (Research Governance v0.1, Rule 6)"
"${ROOT_DIR}/scripts/check_refuted_route_quarantine.sh"

echo "[check] Step 7/16: refuted-predicate allowed-use guard (Research Governance v0.1, PR 4a)"
"${ROOT_DIR}/scripts/check_refuted_predicate_usage.sh"

echo "[check] Step 8/16: target-lock guard (Research Governance v0.1, PR 11)"
"${ROOT_DIR}/scripts/check_target_lock.sh"

echo "[check] Step 9/16: barrier-certificate queue scan (Research Governance v0.1, PR 12)"
"${ROOT_DIR}/scripts/check_barrier_certificate.sh" --queue

echo "[check] Step 10/16: smoke probes (Research Governance v0.1, PR 5)"
"${ROOT_DIR}/scripts/run_smoke_probes.sh"

echo "[check] Step 11/16: NoGoLog + survivor history validation (Research Governance v0.1, PR 9)"
python3 "${ROOT_DIR}/scripts/validate_jsonl.py"

echo "[check] Step 12/16: verify_candidate.sh smoke (Research Governance v0.1, PR 15)"
"${ROOT_DIR}/scripts/verify_candidate.sh" \
  --candidate pnp3/Candidates/_template \
  --json /tmp/verify_template_result.json
# The smoke run must produce PASS_SHAPE_ONLY on the noop template.
result_status="$(python3 -c 'import json; print(json.load(open("/tmp/verify_template_result.json"))["status"])')"
if [[ "${result_status}" != "PASS_SHAPE_ONLY" ]]; then
  echo "[check] FAIL: verify_candidate.sh on _template returned status=${result_status} (expected PASS_SHAPE_ONLY)"
  exit 1
fi

echo "[check] Step 13/16: pnp3 explicit theorem-axiom surface dump"
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

echo "[check] Step 14/16: pnp4 explicit theorem-axiom surface dump"
pnp4_axiom_surface_log="/tmp/pnp4_axiom_surface.log"
if ! rg -n -U "pnp4/Pnp4/Tests/AxiomsAudit\\.lean:[^\\n]*depends on axioms:\\s*\\[[^\\]]*\\]" \
    "${build_log}" >"${pnp4_axiom_surface_log}"; then
  lake env lean pnp4/Pnp4/Tests/AxiomsAudit.lean > "${pnp4_axiom_surface_log}" 2>&1
fi

if rg -n "Lean\.ofReduceBool|Lean\.trustCompiler" "${pnp4_axiom_surface_log}" >/tmp/pnp4_trust_hits.log; then
  echo "Detected trusted-compiler reduction axioms in pnp4 audited theorem surface:"
  cat /tmp/pnp4_trust_hits.log
  exit 1
fi

pnp4_classical_count=$( (rg -n "Classical\.choice" "${pnp4_axiom_surface_log}" || true) | wc -l | tr -d ' ' )
pnp4_propext_count=$( (rg -n "\bpropext\b" "${pnp4_axiom_surface_log}" || true) | wc -l | tr -d ' ' )
pnp4_quot_count=$( (rg -n "Quot\.sound" "${pnp4_axiom_surface_log}" || true) | wc -l | tr -d ' ' )
echo "Axiom surface summary (from pnp4/Pnp4/Tests/AxiomsAudit):"
echo "  propext occurrences: ${pnp4_propext_count}"
echo "  Classical.choice occurrences: ${pnp4_classical_count}"
echo "  Quot.sound occurrences: ${pnp4_quot_count}"

echo "[check] Step 15/16: run barrier audit module"
if ! rg -n "pnp3/Tests/BarrierAudit\\.lean" "${build_log}" >/tmp/pnp3_barrier_audit.log; then
  # Keep this explicit so regressions in barrier-facing final statements are visible.
  lake env lean pnp3/Tests/BarrierAudit.lean >/tmp/pnp3_barrier_audit.log 2>&1
fi

echo "[check] Step 16/16: unconditional witness gate (optional)"
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

  # Conditional formula/real wrappers may remain available as compatibility
  # endpoints.  The unconditional P != NP gate is the existence of a real
  # compiled zero-argument theorem, not the removal of every conditional helper.

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

  unconditional_probe="/tmp/pnp3_unconditional_probe.lean"
  {
    echo "import Magnification.FinalResult"
    echo "#check Pnp3.Magnification.P_ne_NP_unconditional"
  } >"${unconditional_probe}"
  if ! lake env lean "${unconditional_probe}" >/tmp/pnp3_unconditional_zero_arg_hits.log 2>&1; then
    echo "Unconditional gate failed: missing zero-argument P_ne_NP_unconditional theorem."
    cat /tmp/pnp3_unconditional_zero_arg_hits.log
    exit 1
  fi
  echo "Unconditional witness surface OK."
fi

echo "[check] All checks passed."
