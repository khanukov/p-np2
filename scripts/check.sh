#!/usr/bin/env bash
# Full project compilation and smoke test.
set -euo pipefail

lake build
lake env lean --run scripts/smoke.lean
lake test
