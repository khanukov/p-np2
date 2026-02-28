#!/usr/bin/env bash
# Full project compilation, smoke test, and proof-surface audit.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

echo "[check] Step 1/6: full Lean build"
lake build

echo "[check] Step 2/6: smoke execution"
lake env lean --run scripts/smoke.lean

echo "[check] Step 3/6: source hygiene scan (axiom/sorry/native_decide)"
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

echo "Axiom inventory OK (${actual_axioms} axioms)."
echo "Proof hole scan OK (no sorry/admit)."
echo "native_decide scan OK (no occurrences)."

echo "[check] Step 4/6: explicit theorem-axiom surface dump"
axiom_surface_log="/tmp/pnp3_axiom_surface.log"
# This file contains many `#print axioms` commands; compiling it emits theorem dependency traces.
lake env lean pnp3/Tests/AxiomsAudit.lean > "${axiom_surface_log}" 2>&1

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
# Keep this explicit so regressions in barrier-facing final statements are visible.
lake env lean pnp3/Tests/BarrierAudit.lean >/tmp/pnp3_barrier_audit.log 2>&1

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
  if rg -n "hFormulaToPpoly|hRealToPpoly|FormulaSeparationToNonuniformBridge|RealSeparationToNonuniformBridge|hPsubsetReal|P_subset_PpolyReal|hFormulaInclusion|P_subset_PpolyFormula|hPsubsetDag|P_subset_PpolyDAG" \
      pnp3/Magnification/FinalResult.lean pnp3/Barrier/Bypass.lean >/tmp/pnp3_unconditional_gaps_bridge.txt; then
    echo "Unconditional gate failed: final route still depends on an external non-uniform inclusion/bridge assumption:"
    cat /tmp/pnp3_unconditional_gaps_bridge.txt
    exit 1
  fi

  # Guardrail: no lightweight-Ppoly aliases in final theorem cone once migrated.
  if rg -n "PpolyLite" \
      pnp3/Magnification/FinalResult.lean pnp3/Barrier/Bypass.lean >/tmp/pnp3_unconditional_gaps_lite.txt; then
    echo "Unconditional gate failed: lightweight Ppoly alias leaked into final cone:"
    cat /tmp/pnp3_unconditional_gaps_lite.txt
    exit 1
  fi
  echo "Unconditional witness surface OK."
fi

echo "[check] All checks passed."
