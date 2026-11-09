# Optional idea-to-Lean pilot — Infrastructure

Freeze a closed proposition before candidate generation. Candidate → Lean →
repair records PROVED, REFUTED (entire negation), or retryable UNKNOWN with a
technical reason. Audit colors/exit0/search failure certify nothing. Partial
results do not satisfy the unchanged closed-R/assembly checker. R, lower bounds
and P≠NP remain unproved; no novelty claim. Other routes remain available.

## Current mathematical context

Literal primary context cannot be truncated. References:

* `ConditionalSeparation.OpenProblem.R`: ../../conditional_separation/ConditionalSeparation/OpenProblem.lean.
* `Research.LengthwiseSearch.LengthwiseR`, `R_iff_lengthwise`: ../lengthwise_search/Attempt/RNormalForm.lean. R ↔ LengthwiseR.
* `Research.SolverToDag.LowerBound.TreeMCSPDAGLowerBound`, `lowerBound_implies_R`: ../solver_to_dag/Attempt/LowerBound.lean. LowerBound → R ONLY.

One k precedes all d; N=2^n; per-output size N^d+d; promise correctness;
TREE witnesses versus DAG solvers. Premises/model adequacy remain open.
Legacy routes are optional. Separate addon Attempt roots are not merged:
the pilot cohort uses only installed core DAG/OpenProblem imports.

## Frozen goal and trusted boundary

Save the `freeze` hash outside candidate control. GOAL.json binds exact
type/imports/model/role, core/loader/lock/toolchain/compiler and controls.
Elaboration/object pins precede generation and are rechecked. Candidates supply
tactic bodies only; the target is a separate compiled module.
`kernel.verify_outcome(path,result_sha,goal_sha)` checks external hashes and
rejects missing/changed/relabelled evidence without recompiling.

The loader buffer is authenticated before execution; installed core/objects
must be independently trusted, immutable and nonconcurrent. Custom argv
commands retain caller permissions. This is not a hostile-code sandbox or cold
verification. POSIX ownership assumes a main-thread sole reaper; no universal
crash/grandchild guarantee is provided.

Every native request names the admitted core, exact import/primary source files,
frozen GOAL/TARGET and validation pins. Read those files directly with bounded
reads; never scan /root, reports/history, credentials, transcripts or other
agents. Candidates must not build or edit: the outer loop supplies Lean feedback.
This read contract is advice, not an OS path allowlist. Full serialized stdin
is capped at 9000 UTF-8 bytes. Only optional feedback may be shortened; immutable
type/binders/imports/model/role and integrated primary context stay complete.
Required-content overflow returns technical UNKNOWN before any provider call.

## Reproducible local use

From the repository root, put Lean 4.22.0-rc2 first on PATH; set CORE to an
admitted built package and SCRATCH to a fresh owned directory.

```bash
export LEAN_NUM_THREADS=2 MALLOC_ARENA_MAX=2 PYTHONDONTWRITEBYTECODE=1
unset LEAN_PATH LEAN_SRC_PATH ELAN_TOOLCHAIN PYTHONOPTIMIZE
mkdir "$SCRATCH"
export SCRATCH
python3 -B - <<'PY'
import json, os
from pathlib import Path
cohort=json.loads(Path('research/idea_lean_pilot/cohort.json').read_bytes())
Path(os.environ['SCRATCH'],'spec.json').write_text(json.dumps(cohort[0]))
PY
python3 -B -m idea_search_machine.probe freeze --core "$CORE" \
  --spec "$SCRATCH/spec.json" --output "$SCRATCH/frozen"
# Save the printed SHA as GOAL_SHA (trusted operator input).
```

Copy provider.example.json to SCRATCH/provider.json: Sol/xhigh, 300s,
`exec --json --output-schema`, read-only. DATA/kernel tests make no model calls.
Custom `kind: command` uses `argv` and integer `seconds`; absolute request/response
paths are appended. Response: `{"proof":"tactic body without by"}`.

All compiler batches require global SH → lane-a EX, CPUs 0,1, two threads and
at least 5 GiB disk/MemAvailable. The product acquires no locks internally:

```bash
(
  flock --shared 9
  flock --exclusive 8
  python3 -B - <<'PY'
import os, shutil
from pathlib import Path
mem=int(next(s.split()[1] for s in Path('/proc/meminfo').read_text().splitlines() if s.startswith('MemAvailable:')))*1024
if min(shutil.disk_usage(os.environ['SCRATCH']).free,mem)<5*1024**3:
    raise SystemExit('5GiB resource floor not met')
PY
  taskset --cpu-list 0,1 python3 -B -m idea_search_machine.probe probe \
    --goal "$SCRATCH/frozen/GOAL.json" --goal-sha256 "$GOAL_SHA" \
    --provider "$SCRATCH/provider.json" --calls 2 --output "$SCRATCH/probe-01"
) 9>/run/lock/pnp2-build-global.lock 8>/run/lock/pnp2-build-lane-a.lock
```

An optional `--negate` alternates prove/refute within the SAME total call
budget, not two mandatory agents. `--idea-id ID --registry DIR` attaches a
scoped result even to a historical RED/CLOSED record. Use a NEW output directory. Never bless a prover-edited GOAL_SHA.

## Fixtures, CI and measurement

Six fixture/audit roots retain the propext/Classical.choice/Quot.sound allowlist.

`python3 -B -m idea_search_machine.pilot_ci --output NEW` runs the literal
40-ID DATA roster, rejecting skips/missing IDs/errors. Under the same locks,
`python3 -B -m research.idea_lean_pilot.integration --core "$CORE"
--output NEW` runs 13 kernel/DATA cases. The proposed pinned-core workflow
retains owned goals/results/terminals/axioms, not transcripts/SDK/caches/
credentials. Current hosted/source/release acceptance belongs to actual
exact-head PR checks and independent records, not this file.

Freeze the SAME cohort first. `compare` accepts
`{"path":".../GOAL.json","sha256":"..."}` objects. In the same lock/resource scope:
`python3 -B -m idea_search_machine.probe compare --cohort COHORT.json
--provider PROVIDER.json --calls 2 --output NEW`.
Both arms are prove-only, direct before integrated, with the same goals/model/
budget/checker; `probe --negate` is separate, not a comparison refutation claim.

Observed 2026-11-09: [MEASUREMENTS.json](MEASUREMENTS.json) copies the exact parent
packet, preserving source/evidence identities and qualifications.
Twelve verified readonly Sol/xhigh contexts used exact-file reads; fresh
current-control kernel cases passed 13/13, zero skips. Both arms PROVED the true
helper; false strengthening/open R stayed UNKNOWN. Separate whole-negation
REFUTED the false strengthening after a real Lean rejection.
Direct/integrated totals: 224.602/253.583s, five candidate calls each;
six/eight compiler calls, one/two repeat goal compiles. Candidate budget120s,
not example300s. Tiny synthetic cohort, fixed order: no acceleration,
significance, lower bound or R/P!=NP claim. Cost unknown; phase/usage and
unmetered coordinator/review/CI costs stay qualified in the packet.
Two native tool outputs exceeded8500bytes; no universal transport compliance.
Native01 timeout/broad-search/cancel/UNKNOWN history remains preserved there.
