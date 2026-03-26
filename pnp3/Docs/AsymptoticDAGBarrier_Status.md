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
- `SmallDAGImpliesPromiseValueLocalityAt`
- `SmallDAGImpliesPromiseValueLocalityStatement`
- `no_dag_solver_of_promise_value_locality_at`
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
   - `generalSolverOfSmallDAGWitnessOnSlice`
   - `SmallDAGWitnessSemanticConeCertificateAt`
   - `SmallDAGWitnessRestrictionExtractionAt`
   - `SmallDAGWitnessRestrictionNumericDataAt`
   - `SmallDAGWitnessRestrictionCertificateDataAt`
   - `smallDAGWitnessRestrictionExtractionAt_of_semanticConeCertificate`
   - `smallDAGWitnessRestrictionExtractionProviderOnSlices_of_semanticConeProvider`
   - `smallDAGWitnessShrinkageCertificateAt_of_restrictionData`
   - `smallDAGWitnessShrinkageCertificateProviderOnSlices_of_restrictionDataProvider`
   - `SmallDAGWitnessShrinkageCertificateAt`
   - `DAGStableRestrictionSlackPackageAt`
   - `dagStableRestrictionSlackPackageAt_of_shrinkageCertificate`
   - `dagStableRestrictionSlackPackageAtProviderOnSlices_of_shrinkageCertificateProvider`
   - `smallDAGLocalityStatement_of_dagSlackPackageAtProvider`
   - `smallDAGLocalityStatement_of_shrinkageCertificateProvider`
   - `smallDAGLocalityStatement_of_restrictionDataProvider`
   - `smallDAGLocalityStatement_of_semanticConeAndNumericProvider`
   - `smallDAGLocalityStatement_of_restrictionExtractionAndNumericProvider`
3. witness-indexed promise/value bridge (new canonical weak-route surface)
   - `PromiseValueLocalityPackageAt`
   - `promiseValueLocalityPackageAtProviderOnSlices`
   - `smallDAGPromiseValueLocalityStatement_of_packageProvider`
4. witness-indexed one-sided YES-subcube route (preferred theorem-minimal target)
   - `YesSubcubeCertificateAt`
   - `no_small_dag_solver_of_yesSubcubeCertificateAt`
   - `yesSubcubeCertificateAtProviderOnSlices`
   - `noSmallDAG_of_yesSubcubeCertificateAtProviderOnSlices`

Current scan result: the repository already contains formula-side restriction
extraction analogues and certificate-driven downstream bridges, but no existing
DAG-side theorem producing either `YesSubcubeCertificateAt` or
`SmallDAGWitnessSemanticConeCertificateAt` from a `SmallDAGWitnessOnSlice`.

## Counting-side bridge status

Current counting wrappers:

- `exists_hard_function_with_constraints_of_countingSlack`
- `exists_yes_no_agreeing_on_alive_of_countingSlack`

These wrappers now consume pure slack directly. The Shannon backend has been
strengthened with
`Counting.exists_hard_function_with_constraints_of_countingSlack`, so the
temporary adapter hypothesis `hSlackToHalf` is no longer part of the
build-critical lower-bound path.

## Honest remaining blocker

The main open mathematical step is now slightly more specific:

- prove that actual DAG semantics on slices `(n,beta)` produce
  `YesSubcubeCertificateAt` (or an equivalent one-sided YES-centered package)
  with the corrected slack inequality;
- on the stronger fallback route, first prove a witness-indexed semantic-cone
  theorem for `generalSolverOfSmallDAGWitnessOnSlice`, i.e. produce
  `SmallDAGWitnessSemanticConeCertificateAt`, then reduce it to semantic
  restriction extraction, then separately prove the numeric side conditions
  upgrading that extraction to restriction data; once those pieces exist, the
  shrinkage certificate and old encoded-coordinate locality package are already
  automatic;
- older encoded-coordinate invariants/restrictions remain available as fallback
  routes or later bridge sources, but they are no longer the preferred
  canonical surface.
