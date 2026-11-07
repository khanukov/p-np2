# Lengthwise research interface for R

Progress classification: **Infrastructure**. This contribution proves an exact
normal form of the existing research obligation. It does not prove R, weaken R,
or establish a new lower bound or a standard-model P-versus-NP separation.

Base: `khanukov/p-np2` commit
`ffba57655ac76e31f9e26304b2437139e47d4b08`.
Toolchain: the installed core's exact Lean `4.22.0-rc2` and locked dependencies.
The frozen `conditional_separation/` package is not edited.

## Mathematical result

`SolverAt problem C n s` is a solver at one length with size at most `s`
**for each output circuit**. `LowerBoundAt` says that every such tuple fails
on some promised input. The complete output vector must fail the original
relation; it need not differ from an arbitrarily selected canonical witness.

For arbitrary circuit carriers and search problems:

```
Nonempty (BoundedSearchSolver problem C bound)
  ↔ forall n, Nonempty (SolverAt problem C n (bound n))

not Nonempty (BoundedSearchSolver problem C bound)
  ↔ exists n, LowerBoundAt problem C n (bound n)
```

The reverse family construction uses `Classical.choice`. This is appropriate
for the existing NONUNIFORM model; it claims no uniform solver generator.

With the unchanged problem, codec, promise, DAG class and budget of OpenProblem:

```
R ↔ exists ONE k, forall d, exists n, forall bounded output tuples C,
       exists promised x, not relation x (C(x))
```

The bad input may depend on C. All lengths, including zero and one, remain.
No positivity or inhabitedness assumptions are added to the generic theorem.
For the concrete model we additionally prove that a bounded tuple always
exists, witness width is at least four, and both constant truth tables satisfy
the promise. The tuple uses size-one projections, not size-two constant DAGs.

This is a **lengthwise logical interface**, not an executable DAG enumerator.
Generic circuit carriers may be infinite and relations need not be decidable.

## Files

- `Attempt/Lengthwise.lean`: generic definitions, both equivalences and size monotonicity.
- `Attempt/RNormalForm.lean`: exact R specialization and concrete nonvacuity facts.
- `Attempt/Examples.lean`: constant-versus-projection lower bound, no shared bad input,
  positive solver, zero output width, and the no-bounded-tuple edge case.
- `Attempt/Surface.lean`: independently expanded R contract, full-proposition
  mirrors for all 19 authored theorems, and 24 explicit definition/type pins.
- `Attempt/Audit.lean`: exact imported-declaration set and fail-closed transitive
  axiom checks for 131 direct roots, including checking declarations and 45
  explicitly classified compiler-generated entries.
- `Attempt.lean`: ordinary import entry point.
- `prepare.py`, `check.py`: fresh workbench source preparation and validation.
- `TASK_RU.md`: engineering task, acceptance criteria and next research task.
- `VALIDATION.md`: the actual verification results and limitations.

## Reproduce

Use an independently verified, **already built** installed core with its pinned
Lean and locked dependency objects available locally. This is admitted object
reuse, not a fresh/cold foundation build. Do not run `lake build` in an attempt;
a fresh attempt does not inherit an installation's transitive dependency checkout.
The checker executes only the installed-core workspace and creates its own
objects under the fresh caller-selected attempt.

On the integration host, acquire the global shared
`/run/lock/pnp2-build-global.lock`, then exclusive lane-a
`/run/lock/pnp2-build-lane-a.lock`, once around each command below; set CPU
affinity 0,1 and require at least 5 GiB MemAvailable before preparation and
compilation. Do not nest an already locked wrapper. The recorded local run uses
Python fcntl orchestration with that order and rechecks the floor after locking.
Resource admission is a caller responsibility, not an extra mathematical premise.

From the repository root, with absolute paths and a NEW attempt destination:

```sh
export CORE=/your/verified/installed/conditional_separation
export SCRATCH=/your/private/research-scratch
export ATTEMPT="$SCRATCH/new-lengthwise-attempt"
# Start PATH with the installed pinned Lean 4.22.0-rc2 bin directory.
unset LEAN_PATH LEAN_SRC_PATH ELAN_TOOLCHAIN PYTHONOPTIMIZE LD_PRELOAD
export LEAN_NUM_THREADS=2 MALLOC_ARENA_MAX=2 PYTHONDONTWRITEBYTECODE=1
# Execute both commands inside the resource scope described above.
python3 -B research/lengthwise_search/prepare.py --core "$CORE" --output "$ATTEMPT"
python3 -B research/lengthwise_search/check.py "$ATTEMPT"
```

The caller may choose any private scratch root; no sender's absolute-path
manifest, object, cache or attempt Lake configuration is a portable source input.
If Lake needs writes to a read-only installed core, retain the real setup error
and prepare a separately admitted private installation; do not grant shared
cache writes or count setup failure as the intended R rejection.

The checker uses the verified installed core's workspace, Lean's import parser,
fresh private object outputs and explicit own-import overrides. It does not run
the attempt's Lake configuration. It compiles every research module, requires
the complete 131-root audit, and then exercises the existing production exact-R
guard. The guard MUST reject the still-conditional theorem
`exact_R_of_lengthwise`, specifically because it does not have closed type R.
Expected success status:

```
PARTIAL_RESEARCH_INTERFACE_CHECKED_NOT_R
```

Compiler stdout/stderr, source snapshots, setups and process terminals remain
under the fresh attempt's `.lake/conditional-check/runs/` directory. A successful
partial check supplies no proof of R. If research sources change, prepare a
new attempt; the source manifest intentionally rejects in-place source drift.
These scripts execute trusted research code; they are not a hostile-code sandbox.

## Why it helps

For one fixed k and each degree d, an author can now choose a suitable length n
and attack all bounded tuples at that length, then use the checked equivalence
to construct exactly the R premise consumed by the existing
`ConditionalSeparation.close`. No global dependent solver
record needs to be refuted by hand in each proof attempt. The mathematical
strength of the required lower bound is unchanged.

## Scope retained

This optional interface is equivalent to the unproved R used by the existing
direct route. R is sufficient for that route, not asserted necessary for every
possible P-versus-NP proof. The direct R API and other research routes remain
available and unchanged. Solver-to-DAG exact recognition and an actual
polynomial-size construction are a separate task, not implemented here and
not a prerequisite for this interface PR. No uniform generator, enumerator,
weaker hypothesis, new lower bound or novelty claim is supplied.

Local Linux compilation passed for six modules and all 131 direct roots; the
conditional exact-R conversion was rejected at the expected closed-type guard.
See VALIDATION.md for receipts, object-reuse warnings, failed attempts and the
separate supplied handoff history. Independent reviews, root CI, other-platform
reproduction and publication remain pending.
