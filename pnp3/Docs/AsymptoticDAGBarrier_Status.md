# Asymptotic DAG Barrier Status (2026-03-28)

This note documents the **current** theorem-level DAG barrier API after the
latest refactor.

## Plan execution matrix (what is still not implemented)

Below is the short status map against the current weak-mainline plan.

- ✅ **Done (infrastructure / endpoint surface):**
  - weak terminal consumer fixed at `AcceptedFamilyCertificateAt`;
  - mainline source target surface fixed at `PromiseYesSubcube*`;
  - backup producer `PRGImageAcceptanceAt` wired to accepted-family closure;
  - strong fallback restriction stack is compiled through weak consumer;
  - thin final wrappers exposed in `Magnification/FinalResult.lean` for
    accepted-family, promise-YES, PRG-image backup, fallback extraction+numeric,
    and eventual magnification-style no-small-DAG closure.

- 🟡 **Partially done (parallel theorem tracks):**
  - restricted-model ladder has first footholds (`supportHalfBound*`,
    `valueSupported` variants), but not yet a broad ladder with multiple model
    classes and source-theorem extraction results.

- ❌ **Not done (the real blocker):**
  - semantic N1 is now closed at the acceptance-invariant level via
    `promiseYesAcceptanceInvariantAt_of_strictDAGSemantics` /
    `promiseYesAcceptanceInvariantAtProviderOnSlices_of_strictDAGSemantics`,
    but this uses the full value-coordinate set and does **not** supply the
    quantitative same-set slack required for `PromiseYesSubcubeCertificateAt`;
  - still no internal theorem proving either full
    `SmallDAGWitnessOnSlice -> PromiseYesSubcubeCertificateAt`
    or
    `SmallDAGWitnessOnSlice -> PRGImageAcceptanceAt`
    on the full target model;
  - therefore no internal unconditional proof of
    `ComplexityInterfaces.NP_not_subset_PpolyDAG`;
  - final `P_ne_NP_final*` wrappers still require an external DAG-separation
    hypothesis `hNPDag`.

- ❌ **Not done (publication/completion criteria):**
  - asymptotic final layer still not fed by an internalized `NP_not_subset_PpolyDAG`;
  - docs/release claims cannot yet state unconditional `P ≠ NP`.

## Concrete next work plan (execution-ready)

This section is the immediate patch plan for the next theorem sprints.
Each item has:
- concrete deliverable,
- target files,
- minimal acceptance check.

### Active branch map (A/B/C)

- **Branch A (strengthen Q1):**
  - build a different semantic invariant with **non-full** coordinate set
    (`S ≠ Finset.univ`), targeting either
    `PromiseYesAcceptanceInvariantAtNontrivialS` or an equivalent stronger
    `PromiseYesDecisionCertificateAt` variant with nontrivial `S`.
- **Branch B (PRG backup):**
  - if nontrivial-`S` extraction from strict Q1 is blocked, shift effort to
    `SmallDAGWitnessOnSlice -> PRGImageAcceptanceAt`, i.e. a distinct
    quantitative mechanism not tied to same-set slack on full `S`.
- **Branch C (restricted-model probe):**
  - mine support-bounded / value-supported / low-reuse submodels to identify the
    structural invariant that actually yields non-full `S`, then lift.

### A. Main blocker theorem split: semantic forcing vs quantitative slack

**Goal:** progress on
`SmallDAGWitnessOnSlice -> PromiseYesSubcubeCertificateAt`.

1. **Semantic half (one-sided forcing):**
   - deliverable: a theorem that constructs a YES center `yYes` and a value-set
     `S` with one-sided acceptance forcing on valid promise inputs;
   - target files:
     - `pnp3/LowerBounds/DAGStableRestrictionProducer.lean`
     - (if needed) `pnp3/LowerBounds/AsymptoticDAGBarrier.lean`;
   - acceptance check:
     - theorem lands in the shape of `PromiseYesAcceptanceInvariantAt` or a
       direct constructor path to `PromiseYesSubcubeCertificateAt` (without yet
       requiring final slack strength).

2. **Quantitative half (same-set slack):**
   - deliverable: bound/slack theorem for the **same** `S` produced above;
   - target files:
     - `pnp3/LowerBounds/DAGStableRestrictionProducer.lean`
     - `pnp3/LowerBounds/AcceptedFamilyBarrier.lean` (only if additional
       counting adapter is required);
   - acceptance check:
     - theorem composes directly with semantic half and yields
       `PromiseYesSubcubeCertificateAt` without introducing new endpoint layers.

Current implementation note:
- decomposition API is now explicit in code via
  `PromiseYesSourceDecompositionAt`,
  `promiseYesSubcubeCertificateAt_of_sourceDecomposition`,
  provider-level split interfaces
  `promiseYesAcceptanceInvariantAtProviderOnSlices` /
  `promiseYesSlackOnInvariantProviderOnSlices`,
  and compiled closure
  `noSmallDAG_of_promiseYesSemanticAndSlackProvidersOnSlices`;
- pairwise package providers now also reduce explicitly into that split API via
  `promiseYesAcceptanceInvariantAtProviderOnSlices_of_promiseValueLocalityPackageProvider`
  and
  `promiseYesSlackOnInvariantProviderOnSlices_of_promiseValueLocalityPackageProvider`,
  with closure theorem
  `noSmallDAG_of_promiseValueLocalityPackageProviderOnSlices_viaSemanticAndSlack`;
- what remains open is proving those providers from strict DAG semantics.
- semantic implementation update:
  - strict-DAG witness semantics now already yields the Q1 object directly via
    `promiseYesAcceptanceInvariantAt_of_strictDAGSemantics`;
  - family-level lift is exported as
    `promiseYesAcceptanceInvariantAtProviderOnSlices_of_strictDAGSemantics`;
  - quantitative diagnostic is now formalized via
    `no_sameSetSlack_of_strictDAGSemantics`: for this exact Q1 construction the
    chosen `S` is full-value (`Finset.univ`), so same-set slack is impossible;
  - branch-C probe now has a concrete bridge:
    `promiseValueLocalityPackageAt` gives `S ≠ Finset.univ` via
    `nontrivialS_of_promiseValueLocalityPackageAt`, and therefore yields
    `PromiseYesAcceptanceInvariantAtNontrivialS` through
    `promiseYesAcceptanceInvariantAtNontrivialS_of_promiseValueLocalityPackageAt`
    (and provider-level lift);
  - remaining blocker for the mainline is Q2: small enough same-set slack on
    the semantic coordinates chosen by Q1.

### B. Backup producer track: PRG-image route

**Goal:** progress on
`SmallDAGWitnessOnSlice -> PRGImageAcceptanceAt`.

1. **Structured image extraction theorem:**
   - deliverable: witness-indexed theorem that extracts an accepted structured
     image family from small-DAG semantics;
   - target file:
     - `pnp3/LowerBounds/DAGStableRestrictionProducer.lean`;
   - acceptance check:
     - theorem feeds existing bridge
       `acceptedFamilyCertificateAt_of_prgImageAcceptanceAt` and then
       `no_small_dag_solver_of_acceptedFamilyCertificateAt` without new API.

### C. Restriction fallback as diagnostic (not main endpoint)

**Goal:** use fallback to mine invariants for the weak route.

1. **Value-supported extraction pass:**
   - deliverable: theorem(s) showing when restriction data implies
     value-supported conditions needed by promise-value / promise-YES route;
   - target file:
     - `pnp3/LowerBounds/DAGStableRestrictionProducer.lean`;
   - acceptance check:
     - compiles via existing reductions
       `promiseValueLocalityPackageAt_of_*` and then
       `promiseYesSubcubeCertificateAt_of_*`.

### D. FinalResult boundary discipline

**Goal:** keep `FinalResult` as surface-only file.

1. **Boundary rule for new additions:**
   - only add wrappers to:
     - `¬ SmallDAGSolver ...` and/or
     - `MagnificationStyleNoSmallDAG ...`,
     - and eventually `NP_not_subset_PpolyDAG` / `P_ne_NP` once the real bridge
       exists;
   - do **not** add source-level internal reductions here.
   - target file:
     - `pnp3/Magnification/FinalResult.lean`;
   - acceptance check:
     - source-side technical reductions remain in lower-bounds producer/barrier
       modules.

### E. Bridge to internalized DAG separation (critical integration milestone)

**Goal:** remove external `hNPDag` eventually.

1. **Asymptotic bridge theorem skeleton:**
   - deliverable: theorem statement (and first supporting lemmas) that maps a
     global `ComplexityInterfaces.PpolyDAG` witness to the asymptotic
     `SmallDAGSolver`/`SizeBound` surface consumed by current magnification-style
     no-small-DAG theorems;
   - target files:
     - `pnp3/Magnification/FinalResult.lean` (surface theorem statement),
     - `pnp3/LowerBounds/AsymptoticDAGBarrier.lean` (quantifier plumbing),
     - optional bridge helper near `pnp3/LowerBounds/DAGStableRestrictionProducer.lean`;
   - acceptance check:
     - one explicit theorem-level dependency edge appears:
       `PpolyDAG witness -> asymptotic SmallDAGSolver family`.

Progress update (implemented):

- Added witness-level bridge in `pnp3/LowerBounds/AsymptoticDAGBarrier.lean`:
  - `ppolyDAGSizeBoundOnSlices`
  - `smallDAGSolver_of_inPpolyDAGFamilyOnSlices`
- Added membership-level adapter/bridge:
  - `inPpolyDAGFamilyOnSlices_of_PpolyDAG`
  - `smallDAGSolver_of_PpolyDAGOnSlices`
- Added eventual-surface bridge layer:
  - `EventuallyInPpolyDAGWitnessFamily`
  - `EventuallyPpolyDAGWitnessFamily`
  - `EventuallySmallDAGSolverSurface`
  - `eventuallySmallDAGSolverSurface_of_eventuallyInPpolyDAGWitnessFamily`
  - `eventuallySmallDAGSolverSurface_of_eventuallyPpolyDAGWitnessFamily`
- Added single-global witness packaging bridge:
  - `AsymptoticDAGLanguageBridge`
  - `ppolyDAGOnSlices_of_globalWitness`
  - `eventuallySmallDAGSolverSurface_of_globalPpolyDAGWitness`
- Added bridge-local contradiction schema:
  - `not_globalPpolyDAG_of_noSmallForCanonicalWitnessFamilies`
- Added concrete weak-route instantiations:
  - `not_globalPpolyDAG_of_acceptedFamilyWeakRoute`
  - `not_globalPpolyDAG_of_promiseYesWeakRoute`
  - `NP_not_subset_PpolyDAG_of_acceptedFamilyWeakRoute`
  - `NP_not_subset_PpolyDAG_of_promiseYesWeakRoute`
- Added final-surface bridge-template instantiations reusing the same canonical
  contradiction schema (no new plumbing):
  - PRG-image route:
    - `not_globalPpolyDAG_surface_of_prgImageAcceptanceWeakRoute`
    - `NP_not_subset_PpolyDAG_surface_of_prgImageAcceptanceWeakRoute`
  - stronger fallback route (restriction extraction + numeric side data):
    - `not_globalPpolyDAG_surface_of_restrictionExtractionNumericWeakRoute`
    - `NP_not_subset_PpolyDAG_surface_of_restrictionExtractionNumericWeakRoute`
- Scope note:
  - this closes the **quantifier plumbing** edge from per-slice `PpolyDAG`
    assumptions to per-slice/eventual `SmallDAGSolver` existence, including a
    single-global witness packaging layer;
  - this now also includes an explicit global witness contradiction schema
    under uniform no-small-solver assumptions for canonical witness families;
  - this now reaches explicit class-level separation statements
    `NP_not_subset_PpolyDAG_of_<weak-route-theorem>`;
  - the remaining task is to internalize the new bridge-template routes into
    final `P_ne_NP` wrappers and progressively remove external `hNPDag`
    assumptions.
  - full theorem-level DAG separation internalization is still open.

## Immediate patch queue (next 3 patches)

1. **Patch N2 (mainline quantitative completion):** prove same-set slack for
   the semantic output and compose to internal
   `PromiseYesSubcubeCertificateAt`.
2. **Patch N2b (semantic strengthening):** refine Q1 from the full-value-set
   witness to a nontrivial/smaller semantic set that is plausibly compatible
   with counting slack extraction.
3. **Patch N3 (final internalization):** thread internal class-level DAG
   separation into default final wrappers and progressively remove external
   `hNPDag` parameters.

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
- thin final DAG-wrapper work is already in place; prioritize source-theorem
  mathematics over additional wrapper layering unless a new bridge is required
  by a concrete proof.

Sanity policy:

- do not re-upgrade exact subcube geometry to the only honest blocker unless
  the mathematics forces it;
- do not add more endpoint-generalization layers without a concrete source-side
  proof mechanism;
- do use restricted models to test which producer route is mathematically
  realistic before betting the whole project on one theorem shape.
