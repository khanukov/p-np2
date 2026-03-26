# Asymptotic DAG Barrier Status (2026-03-26)

This note documents the **current** theorem-level DAG barrier API after the
latest refactor.

## Canonical module

- `pnp3/LowerBounds/AsymptoticDAGBarrier.lean`

## Current interfaces

### 1. Family object

- `GapSliceFamily`
  - `paramsOf : Nat -> Rat -> GapPartialMCSPParams`
  - `Tof : Nat -> Rat -> Nat`
  - `Mof : Nat -> Nat -> Nat`
  - coherence fields `hIndex`, `hT`, `hM`

This replaces the old style where transport equalities were free theorem
arguments.

### 2. Layer A (counting anti-locality)

- `GapAntiLocalityAt`
- `GapAntiLocalityStatement`

Slack is expressed as:

- `M_n(T(n,beta)) < 2^(tableLen - |S|)`

### 3. Layer B (small-DAG locality)

- `SmallDAGImpliesCoordinateLocalityAt`
- `SmallDAGImpliesCoordinateLocalityStatement`

Layer B now includes an explicit size premise:

- `SizeBound n beta epsilon (DagCircuit.size C)`

This is required so Layer B talks about **small** solvers, not all correct DAGs.

### 4. Composition and endpoint

- `no_dag_solver_of_two_layer_at`
- `no_dag_solver_of_two_layer`
- `MagnificationStyleNoSmallDAG`
- `magnificationStyleNoSmallDAG_of_eventually_two_layer`

## DAG-side bridge status

Current bridge file:

- `pnp3/LowerBounds/DAGStableRestrictionProducer.lean`

Implemented routes:

1. language-level slack bridge (legacy compatibility)
   - `sliceLanguageLocality_of_dagSlackProviderOnSlices`
2. witness-indexed small-solver bridge (preferred)
   - `SmallDAGWitnessOnSlice`
   - `DAGStableRestrictionSlackPackageAt`
   - `smallDAGLocalityStatement_of_dagSlackPackageAtProvider`

## Counting-side bridge status

Current counting wrappers:

- `exists_hard_function_with_constraints_of_countingSlack`
- `exists_yes_no_agreeing_on_alive_of_countingSlack`

These wrappers still require an explicit temporary adapter hypothesis
(`hSlackToHalf`) to connect pure slack bounds to the currently implemented
Shannon backend. Removing this adapter is a remaining mathematical task.

## Honest remaining blocker

The main open mathematical step is still the same:

- prove small-DAG locality from DAG semantics on slices `(n,beta)` with the
  slack inequality, without relying on legacy half-table adapters.
