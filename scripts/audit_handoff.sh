#!/usr/bin/env bash
set -euo pipefail

ts="$(date -u +%Y%m%dT%H%M%SZ)"
out_dir="artifacts/audit/${ts}"
mkdir -p "${out_dir}"

{
  echo "timestamp_utc=${ts}"
  echo "pwd=$(pwd)"
  echo "uname=$(uname -a)"
  echo "lean_version=$(lake env lean --version | tr '\n' ' ' | sed 's/[[:space:]]\\+/ /g')"
  echo "lake_version=$(lake --version | tr '\n' ' ' | sed 's/[[:space:]]\\+/ /g')"
} > "${out_dir}/env.txt"

{
  echo "## git rev-parse HEAD"
  git rev-parse HEAD
  echo
  echo "## git status --short"
  git status --short
} > "${out_dir}/git.txt"

lake build 2>&1 | tee "${out_dir}/build.log"
bash scripts/check.sh 2>&1 | tee "${out_dir}/check.log"

{
  echo "## pnp3/Tests/AxiomsAudit.lean"
  lake env lean pnp3/Tests/AxiomsAudit.lean 2>&1
  echo
  echo "## pnp3/Tests/CoreConeAxiomsAudit.lean"
  lake env lean pnp3/Tests/CoreConeAxiomsAudit.lean 2>&1
  echo
  echo "## pnp3/Tests/AntiCheckerConeAxiomsAudit.lean"
  lake env lean pnp3/Tests/AntiCheckerConeAxiomsAudit.lean 2>&1
} > "${out_dir}/axioms.log"

echo "Audit handoff artifacts written to: ${out_dir}"
