#!/usr/bin/env bash
# Full project compilation, smoke test, and axiom inventory check.
set -euo pipefail

lake build
lake env lean --run scripts/smoke.lean

echo "Checking active axiom inventory..."
# Default and CI both enforce a closed proof surface.
expected_axioms=0
actual_axioms=$( (rg "^[[:space:]]*axiom " -g"*.lean" pnp3 || true) | wc -l | tr -d ' ' )
if [[ "${actual_axioms}" -ne "${expected_axioms}" ]]; then
  echo "Expected ${expected_axioms} axioms, found ${actual_axioms}."
  echo "Listing active axioms:"
  rg "^[[:space:]]*axiom " -g"*.lean" pnp3
  exit 1
fi
echo "Axiom inventory OK (${actual_axioms} axioms)."

if [[ "${UNCONDITIONAL:-0}" == "1" ]]; then
  echo "Checking unconditional witness surface..."
  if rg -n "ppoly_circuit_locality|FamilyIsLocalCircuit|hF_all" \
      pnp3/Magnification pnp3/LowerBounds/AntiChecker_Partial.lean >/tmp/pnp3_unconditional_gaps.txt; then
    echo "Unconditional gate failed: remaining external witness/axiom surface detected:"
    cat /tmp/pnp3_unconditional_gaps.txt
    exit 1
  fi
  echo "Unconditional witness surface OK."
fi
