#!/usr/bin/env bash
set -euo pipefail

# Automatically fetch the precompiled mathlib cache if it is missing.
if [ ! -f .lake/packages/mathlib/lake-manifest.json ]; then
  echo "[lake_build] mathlib cache missing – downloading via 'lake exe cache get'."
  lake exe cache get
fi

# Forward all arguments to `lake build`.
lake build "$@"
