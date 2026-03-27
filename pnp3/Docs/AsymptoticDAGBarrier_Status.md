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
- `SmallDAGImpliesAcceptedFamilyAt`
- `SmallDAGImpliesAcceptedFamilyStatement`
- `no_dag_solver_of_acceptedFamily_at`
- `no_dag_solver_of_acceptedFamily`
- `MagnificationStyleNoSmallDAG`
- `magnificationStyleNoSmallDAG_of_eventually_two_layer`
- `magnificationStyleNoSmallDAG_of_eventually_acceptedFamily`

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
3. witness-indexed promise/value bridge (producer-side weak-route surface)
   - `PromiseValueLocalityPackageAt`
   - `promiseValueLocalityPackageAtProviderOnSlices`
   - `smallDAGPromiseValueLocalityStatement_of_packageProvider`
4. witness-indexed one-sided YES-subcube route (structured producer target)
   - barrier-level mainline schema:
     `SmallDAGImpliesPromiseYesSubcubeAt`
   - family-level barrier statement:
     `SmallDAGImpliesPromiseYesSubcubeStatement`
   - direct barrier closures:
     `no_dag_solver_of_promise_yes_subcube_at`
     `no_dag_solver_of_promise_yes_subcube`
     `magnificationStyleNoSmallDAG_of_eventually_promiseYesSubcube`
   - nearer-term promise-aware source target:
     `PromiseYesSubcubeCertificateAt`
   - currently chosen candidate proof mechanism for that route:
     `PromiseYesDecisionCertificateAt`
   - formal sanity check showing that this mechanism is too weak as a
     standalone blocker:
     `promiseYesDecisionCertificateAt_fullValueCoordinates`
   - reduction from the decision-certificate mechanism to the current semantic
     target:
     `promiseYesAcceptanceInvariantAt_of_decisionCertificate`
   - direct quantitative packaging of the operational form:
     `promiseYesSubcubeCertificateAt_of_decisionCertificate`
   - semantic core of that source target:
     `PromiseYesAcceptanceInvariantAt`
   - numeric upgrade from the semantic core:
     `promiseYesSubcubeCertificateAt_of_acceptanceInvariant`
   - reduction from pairwise promise/value locality:
     `promiseYesSubcubeCertificateAt_of_promiseValueLocalityPackageAt`
   - semantic reduction from pairwise promise/value locality:
     `promiseYesAcceptanceInvariantAt_of_promiseValueLocalityPackageAt`
   - decision-certificate reduction from pairwise promise/value locality:
     `promiseYesDecisionCertificateAt_of_promiseValueLocalityPackageAt`
   - strong-to-weak bridge under a value-supported alive set:
     `promiseValueLocalityPackageAt_of_dagStableRestrictionSlackPackageAt_valueSupported`
     and
     `promiseYesSubcubeCertificateAt_of_dagStableRestrictionSlackPackageAt_valueSupported`
   - stronger fallback absorption by the generic accepted-family endpoint:
     `acceptedFamilyCertificateAt_of_dagStableRestrictionSlackPackageAt`
     and
     `no_small_dag_solver_of_dagStableRestrictionSlackPackageAt_via_acceptedFamily`
   - compiled provider/barrier closures for that stronger fallback absorption:
     `acceptedFamilyCertificateAtProviderOnSlices_of_dagStableRestrictionSlackPackageAtProvider`,
     `smallDAGAcceptedFamilyStatement_of_dagStableRestrictionSlackPackageAtProvider`,
     `smallDAGAcceptedFamilyStatement_of_shrinkageCertificateProvider`,
     `smallDAGAcceptedFamilyStatement_of_restrictionDataProvider`,
     `noSmallDAG_of_dagStableRestrictionSlackPackageAtProviderOnSlices_via_acceptedFamily`
   - direct source-side narrowing for the strong sprint:
     `dagStableRestrictionSlackPackageAt_of_restrictionExtractionAndHalfBound`,
     `dagStableRestrictionSlackPackageAt_of_restrictionExtractionAndNumeric`,
     `dagStableRestrictionSlackPackageAtProviderOnSlices_of_restrictionExtractionAndNumericProvider`,
     `smallDAGAcceptedFamilyStatement_of_restrictionExtractionAndNumericProvider`
   - first closed restricted-model theorem on the strong route:
     `smallDAGWitnessRestrictionExtractionAt_of_support`,
     `dagStableRestrictionSlackPackageAt_of_supportHalfBound`,
     `no_small_dag_solver_of_supportHalfBound_via_acceptedFamily`
   - first quantitative restricted-model foothold on the chosen weak route:
     `promiseValueLocalityPackageAt_of_supportHalfBound_valueSupported`,
     `promiseYesSubcubeCertificateAt_of_supportHalfBound_valueSupported`,
     `no_small_dag_solver_of_supportHalfBound_valueSupported`
   - conclusion from the sanity check:
     the real open problem is quantitative extraction of a small/slack-bearing
     YES-centered certificate, not mere existence of a one-sided decision
     certificate
   - direct one-sided closure:
     `no_small_dag_solver_of_promiseYesSubcubeCertificateAt`
   - provider surface:
     `promiseYesSubcubeCertificateAtProviderOnSlices`
   - provider reduction from pairwise package route:
     `promiseYesSubcubeCertificateAtProviderOnSlices_of_promiseValueLocalityPackageProvider`
   - compiled route from that provider to the barrier-level mainline schema:
     `smallDAGPromiseYesSubcubeStatement_of_packageProvider`
   - package-route closure through the YES-centered path:
     `noSmallDAG_of_promiseValueLocalityPackageProviderOnSlices`
   - provider closure:
     `noSmallDAG_of_promiseYesSubcubeCertificateAtProviderOnSlices`
   - compiled route from certificate providers to the barrier-level schema:
     `smallDAGPromiseYesSubcubeStatement_of_certificateProvider`
     `smallDAGPromiseYesSubcubeStatement_of_yesSubcubeCertificateProvider`
   - `YesSubcubeCertificateAt`
   - `no_small_dag_solver_of_yesSubcubeCertificateAt`
   - `yesSubcubeCertificateAtProviderOnSlices`
   - `noSmallDAG_of_yesSubcubeCertificateAtProviderOnSlices`
5. generic final weak-route consumer (implemented)
   - `AcceptedFamilyCertificate`
   - `no_function_solves_mcsp_of_acceptedFamilyCertificate`
   - slice-level DAG-facing endpoint:
     `AcceptedFamilyCertificateAt`
   - `no_small_dag_solver_of_acceptedFamilyCertificateAt`
   - `acceptedFamilyCertificateAtProviderOnSlices`
   - `noSmallDAG_of_acceptedFamilyCertificateAtProviderOnSlices`
   - canonical barrier bridge:
     `smallDAGAcceptedFamilyStatement_of_certificateProvider`
   - structured producer adapter:
     `acceptedFamilyCertificateAt_of_yesSubcubeCertificateAt`
   - structured provider reduction:
     `acceptedFamilyCertificateAtProviderOnSlices_of_yesSubcubeCertificateProvider`
   - YES-subcube barrier bridge:
     `smallDAGAcceptedFamilyStatement_of_yesSubcubeCertificateProvider`
   - second structured producer route:
     `PRGImageAcceptanceAt`
   - structured PRG-image adapter:
     `acceptedFamilyCertificateAt_of_prgImageAcceptanceAt`
   - structured PRG-image provider reduction:
     `acceptedFamilyCertificateAtProviderOnSlices_of_prgImageAcceptanceProvider`
   - PRG-image barrier bridge:
     `smallDAGAcceptedFamilyStatement_of_prgImageAcceptanceProvider`
   - PRG-image closure:
     `noSmallDAG_of_prgImageAcceptanceAtProviderOnSlices`

Current scan result: the repository already contains formula-side restriction
extraction analogues and certificate-driven downstream bridges, but no existing
DAG-side theorem producing `AcceptedFamilyCertificateAt`,
`YesSubcubeCertificateAt`, or `SmallDAGWitnessSemanticConeCertificateAt` from a
`SmallDAGWitnessOnSlice`.

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

- prove that actual DAG semantics on slices `(n,beta)` produce either the
  generic accepted-family weak certificate `AcceptedFamilyCertificateAt`
  directly or a structured producer such as `YesSubcubeCertificateAt` /
  `PRGImageAcceptanceAt` that reduces to it;
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

## Active research order

Current policy after the accepted-family refactor:

- treat the infrastructure phase as essentially complete for the weak route;
- keep `AcceptedFamilyCertificateAt` as the terminal consumer, not as the
  direct proof target;
- treat `PromiseYesSubcubeCertificateAt` as the nearest theorem target for the
  weak mainline, because it matches the current one-sided counting consumer
  exactly and is already fed by the existing pairwise
  `PromiseValueLocalityPackageAt` surface;
- keep `YesSubcubeCertificateAt` and `PRGImageAcceptanceAt` as stronger
  structured producer targets feeding the generic accepted-family consumer;
- treat `SmallDAGWitnessSemanticConeCertificateAt` as a secondary diagnostic /
  restricted-model theorem target rather than the default unconditional engine;
- postpone thin final DAG-wrapper work until there is a clearer source theorem
  feeding the weak route.

Sanity policy:

- do not re-upgrade exact subcube geometry to the only honest blocker unless
  the mathematics forces it;
- do not add more endpoint-generalization layers without a concrete source-side
  proof mechanism;
- do use restricted models to test which producer route is mathematically
  realistic before betting the whole project on one theorem shape.
