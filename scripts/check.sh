#!/usr/bin/env bash
# Full project compilation, smoke test, and axiom inventory check.
set -euo pipefail

lake build
lake env lean --run scripts/smoke.lean

echo "Checking active axiom inventory..."
expected_axioms=0
actual_axioms=$(rg "^[[:space:]]*axiom " -g"*.lean" pnp3 | wc -l | tr -d ' ')
if [[ "${actual_axioms}" -ne "${expected_axioms}" ]]; then
  echo "Expected ${expected_axioms} axioms, found ${actual_axioms}."
  echo "Listing active axioms:"
  rg "^[[:space:]]*axiom " -g"*.lean" pnp3
  exit 1
fi
echo "Axiom inventory OK (${actual_axioms} axioms)."
