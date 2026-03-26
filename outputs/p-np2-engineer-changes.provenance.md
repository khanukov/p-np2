# Provenance — p-np2-engineer-changes

Date: 2026-03-26

## Scope

Investigation of current uncommitted changes in `~/p-np2`, focused on:

- `pnp3/Counting/ShannonCounting.lean`
- `pnp3/LowerBounds/MCSPGapLocality.lean`
- `pnp3/LowerBounds/AsymptoticDAGBarrier.lean`
- `pnp3/LowerBounds/DAGStableRestrictionProducer.lean`
- `pnp3/Magnification/FinalResult.lean`
- `STATUS.md`
- `TODO.md`
- `pnp3/Docs/AsymptoticDAGBarrier_Status.md`

## Commands run

```bash
cd ~/p-np2 && pwd && git status --short && git branch --show-current && git log --oneline -n 8
cd ~/p-np2 && git diff --stat
cd ~/p-np2 && git diff -- pnp3/Counting/ShannonCounting.lean pnp3/LowerBounds/MCSPGapLocality.lean pnp3/LowerBounds/AsymptoticDAGBarrier.lean pnp3/Magnification/FinalResult.lean pnp3/Magnification/AsymptoticDAGCollapse.lean pnp3/Docs/AsymptoticDAGBarrier_Status.md STATUS.md TODO.md
cd ~/p-np2 && rg -n "DAGStableRestrictionInvariantPackage|DAGStableRestrictionSlackPackageAt|Layer B|PromiseValueLocality|ValueCoordinateSet|AgreeOnValues|ValidEncoding" pnp3 -S
cd ~/p-np2 && lake build pnp3/Counting/ShannonCounting.lean pnp3/LowerBounds/MCSPGapLocality.lean pnp3/LowerBounds/AsymptoticDAGBarrier.lean
cd ~/p-np2 && lake build pnp3/Magnification/FinalResult.lean
cd ~/p-np2 && lake env lean pnp3/Magnification/AsymptoticDAGCollapse.lean
```

## Verified observations

1. The edited modules above build successfully.
2. `pnp3/Models/PartialTruthTable.lean` still emits linter warnings.
3. `ShannonCounting.lean` now contains a direct-slack theorem `exists_hard_function_with_constraints_of_countingSlack`.
4. `MCSPGapLocality.lean` no longer requires `hSlackToHalf` in the build-critical direct-slack wrappers.
5. `MCSPGapLocality.lean` now defines `ValueCoordinateSet`, `AgreeOnValues`, `ValidEncoding`, and promise/value locality consumer theorems.
6. `AsymptoticDAGBarrier.lean` now defines `SmallDAGImpliesPromiseValueLocalityAt` and `no_dag_solver_of_promise_value_locality_at`.
7. Existing strong DAG-side packages in `DAGStableRestrictionProducer.lean` remain phrased over encoded coordinates / restrictions on `partialInputLen p`.
8. `FinalResult.lean`, `STATUS.md`, `TODO.md`, and `AsymptoticDAGBarrier_Status.md` now document the weaker promise/value endpoint as the intended main blocker and the stable-restriction route as a stronger optional path.
9. `pnp3/Magnification/AsymptoticDAGCollapse.lean` is untracked and typechecks locally, but is not part of the tracked build graph.

## Inferences (not directly proved by commands)

1. The current blocker is architectural/theorem-design, not compilation breakage.
2. A direct bridge from the existing encoded-coordinate source packages to the new promise/value interface is not yet present in the repo.
3. Introducing a new source-side package directly at the value/promise layer is likely cleaner than forcing the old encoded-coordinate API to be canonical.

## Main artifact

- `file:///root/p-np2/outputs/p-np2-engineer-changes.md`
