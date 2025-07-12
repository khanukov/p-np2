#!/usr/bin/env bash
# Full project compilation and smoke test.
set -euo pipefail

lake build
lake build Pnp
lake env lean --run scripts/smoke.lean
lake env lean --run scripts/pnp_smoke.lean
