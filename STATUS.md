# Project Status (current)

Updated: 2026-03-26

Authoritative checklist: `CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Release positioning for current tree: `RELEASE_RC.md`.
Detailed execution plan for the remaining DAG blocker:
`pnp3/Docs/Unconditional_NP_not_subset_PpolyDAG_Plan.md`.

## Current verified state

- Active `axiom` declarations in `pnp3/`: 0
- Active `sorry/admit` in `pnp3/`: 0
- `./scripts/check.sh` passes (rechecked on 2026-03-24)
- Current audit/regression tests pass (rechecked on 2026-03-24):
  `AxiomsAudit`, `BarrierAudit`, `BarrierBypassAudit`,
  `BridgeLocalityRegression`

## Current honest target

The near-term engineering target is not an unconditional headline claim.
It is to reduce the repository to one minimal honest open theorem-level blocker,
with counting glue, endpoint shape, and final-surface routing already cleaned
up around it.

Current endpoint ledger:

- Primary planned nonuniform endpoint:
  a generic accepted-family weak endpoint, with working final consumer name
  `AcceptedFamilyCertificateAt`.
- Structured producer routes into that endpoint already present or planned:
  `YesSubcubeCertificateAt`, future `PRGImageAcceptanceAt`, and other injective
  accepted-family packages.
- Stronger optional nonuniform endpoints already exposed in code:
  stable-restriction / certificate-provider / invariant-provider routes,
  plus the new semantic-cone / restriction-extraction / numeric fallback stack.
- Parallel endpoint to specify separately:
  distinguisher/uniform route.

Current research-order policy:

- Infrastructure phase is now mostly complete for the weak route:
  the repository already contains the generic accepted-family consumer,
  structured producer adapters, and the asymptotic barrier-level accepted-
  family schema.
- The active source-theorem targets for the weak mainline are now
  the promise-aware YES-centered route
  `PromiseYesSubcubeCertificateAt` as the nearest theorem target,
  plus the stronger all-valid / accepted-family producer routes
  `YesSubcubeCertificateAt` and `PRGImageAcceptanceAt`.
- The semantic-cone / restriction-extraction / shrinkage stack remains a
  stronger fallback and restricted-model diagnostic route, not the default
  unconditional engine.
- Thin final DAG wrappers remain downstream work; they should not be treated as
  the next main task until a viable weak-route source theorem is clearer.

Variant boundary policy for these endpoints:

- do not silently conflate MCSP / Partial-MCSP / Gap-MCSP / oracle variants;
- do not silently upgrade fixed-slice statements into asymptotic finals;
- do not silently upgrade formula or uniform consequences into DAG or
  `P ≠ NP` consequences.

## Route-B DAG update (2026-03-25)

- New dedicated source file:
  `pnp3/LowerBounds/DAGStableRestrictionProducer.lean`.
- New DAG-native source contracts are now explicit and compiled:
  `DAGStableRestrictionCertificate`,
  `DAGStableRestrictionInvariantPackage`,
  `dagStableRestrictionCertificateProvider`,
  `dagStableRestrictionInvariantProvider`.
- New thin final wrappers are now exposed in
  `pnp3/Magnification/FinalResult.lean`:
  `NP_not_subset_PpolyDAG_final_of_certificateProvider_TM`,
  `P_ne_NP_final_of_certificateProvider_TM`,
  `NP_not_subset_PpolyDAG_final_of_invariantProvider_TM`,
  `P_ne_NP_final_of_invariantProvider_TM`.
- `Tests/BridgeLocalityRegression` and `Tests/AxiomsAudit` now pin this
  invariant-provider route in both compile-time regression and `#print axioms`
  audit surfaces.
- These Route-B contracts remain compiled stronger sufficient conditions and
  audit surfaces, but they are no longer treated as the canonical last blocker.
- Current roadmap intent is to replace them as the primary open endpoint with a
  weaker one-sided promise/value certificate; invariant-provider stays as a
  stronger fallback route.

## Asymptotic DAG-barrier update (2026-03-26)

- Added theorem-level module
  `pnp3/LowerBounds/AsymptoticDAGBarrier.lean`.
- Added `GapSliceFamily` so slice coherence data is carried by one object
  (`paramsOf`, `Tof`, `Mof`, `hIndex`, `hT`, `hM`) instead of free theorem
  arguments.
- Layer B is now correctly small-solver scoped:
  `SmallDAGImpliesCoordinateLocalityAt` includes explicit size premise
  `SizeBound n β ε (DagCircuit.size C)`.
- Added family/eventual glue theorem
  `magnificationStyleNoSmallDAG_of_eventually_two_layer`.
- Added witness-indexed DAG-source bridge in
  `pnp3/LowerBounds/DAGStableRestrictionProducer.lean`:
  `SmallDAGWitnessOnSlice`, `DAGStableRestrictionSlackPackageAt`,
  `smallDAGLocalityStatement_of_dagSlackPackageAtProvider`.
- Added counting-slack wrappers in `pnp3/LowerBounds/MCSPGapLocality.lean`:
  `exists_hard_function_with_constraints_of_countingSlack`,
  `exists_yes_no_agreeing_on_alive_of_countingSlack`.
- The Shannon backend is now also strengthened to direct slack:
  `Counting.exists_hard_function_with_constraints_of_countingSlack`.
- Build-critical lower-bound wrappers no longer require the temporary bridge
  assumption `hSlackToHalf`.
- Added initial value-only / promise-only locality interfaces:
  `ValueCoordinateSet`, `AgreeOnValues`, `ValidEncoding`,
  `exists_yes_no_agreeing_on_values_of_countingSlack`,
  `no_value_local_function_solves_mcsp_of_countingSlack`.
- Added an asymptotic/barrier-facing small-solver interface for the same route:
  `SmallDAGImpliesPromiseValueLocalityAt`,
  `SmallDAGImpliesPromiseValueLocalityStatement`,
  `no_dag_solver_of_promise_value_locality_at`.
- Added a native source-side producer package for this route in
  `pnp3/LowerBounds/DAGStableRestrictionProducer.lean`:
  `PromiseValueLocalityPackageAt`,
  `promiseValueLocalityPackageAtProviderOnSlices`,
  `smallDAGPromiseValueLocalityStatement_of_packageProvider`.
- Added the first one-sided structured weak-route certificate surface:
  `exists_no_completion_agreeing_on_values_of_countingSlack`,
  `no_one_sided_value_local_function_solves_mcsp_of_countingSlack`,
  `YesSubcubeCertificateAt`,
  `no_small_dag_solver_of_yesSubcubeCertificateAt`,
  `yesSubcubeCertificateAtProviderOnSlices`,
  `noSmallDAG_of_yesSubcubeCertificateAtProviderOnSlices`.
- Design correction after the latest architecture/literature audit:
  `YesSubcubeCertificateAt` should now be treated as a strong structured
  producer target rather than the most general final consumer; the canonical
  weak-route consumer should be a generic accepted-family endpoint such as
  `AcceptedFamilyCertificateAt`.
- The generic accepted-family weak consumer is now formalized in code:
  `pnp3/LowerBounds/AcceptedFamilyBarrier.lean` exposes
  `AcceptedFamilyCertificate` and
  `no_function_solves_mcsp_of_acceptedFamilyCertificate`.
- The slice-level DAG-facing endpoint is now also compiled:
  `AcceptedFamilyCertificateAt`,
  `acceptedFamilyCertificateAtProviderOnSlices`,
  `no_small_dag_solver_of_acceptedFamilyCertificateAt`,
  `noSmallDAG_of_acceptedFamilyCertificateAtProviderOnSlices`.
- The asymptotic barrier module now exposes the same weak endpoint as a native
  Layer-B schema:
  `SmallDAGImpliesAcceptedFamilyAt`,
  `SmallDAGImpliesAcceptedFamilyStatement`,
  `no_dag_solver_of_acceptedFamily_at`,
  `no_dag_solver_of_acceptedFamily`,
  `magnificationStyleNoSmallDAG_of_eventually_acceptedFamily`.
- `YesSubcubeCertificateAt` is now connected as a structured producer for that
  generic consumer via
  `acceptedFamilyCertificateAt_of_yesSubcubeCertificateAt` and
  `acceptedFamilyCertificateAtProviderOnSlices_of_yesSubcubeCertificateProvider`.
- The nearer-term one-sided source target is now also explicit in code:
  `PromiseYesSubcubeCertificateAt`,
  `no_small_dag_solver_of_promiseYesSubcubeCertificateAt`,
  `promiseYesSubcubeCertificateAtProviderOnSlices`,
  `noSmallDAG_of_promiseYesSubcubeCertificateAtProviderOnSlices`,
  and the reductions
  `promiseYesSubcubeCertificateAt_of_yesSubcubeCertificateAt`,
  `promiseYesSubcubeCertificateAt_of_promiseValueLocalityPackageAt`,
  `promiseYesSubcubeCertificateAtProviderOnSlices_of_promiseValueLocalityPackageProvider`,
  `noSmallDAG_of_promiseValueLocalityPackageProviderOnSlices`.
- The asymptotic/barrier layer now also exposes that nearer-term chosen
  mainline target directly:
  `SmallDAGImpliesPromiseYesSubcubeAt`,
  `SmallDAGImpliesPromiseYesSubcubeStatement`,
  `no_dag_solver_of_promise_yes_subcube_at`,
  `no_dag_solver_of_promise_yes_subcube`,
  `magnificationStyleNoSmallDAG_of_eventually_promiseYesSubcube`,
  together with the compiled witness-indexed bridges
  `smallDAGPromiseYesSubcubeStatement_of_certificateProvider`,
  `smallDAGPromiseYesSubcubeStatement_of_packageProvider`,
  `smallDAGPromiseYesSubcubeStatement_of_yesSubcubeCertificateProvider`.
- The semantic heart of that route is now isolated explicitly as
  `PromiseYesAcceptanceInvariantAt`; the weak-route contradiction target now
  factors as:
  semantic YES-centered invariant
  -> numeric slack upgrade
  -> `PromiseYesSubcubeCertificateAt`.
- The currently chosen candidate proof mechanism for that semantic route is now
  explicit in code as `PromiseYesDecisionCertificateAt`: on valid promise
  inputs, agreement with one YES center on `S` already forces the solver
  decision.  This reduces mechanically to
  `PromiseYesAcceptanceInvariantAt`.
- Critical correction after formal sanity check:
  `PromiseYesDecisionCertificateAt` by itself is too weak to be the main
  blocker.  The theorem
  `promiseYesDecisionCertificateAt_fullValueCoordinates` shows that every
  correct small DAG witness already has such a certificate with the full value
  coordinate set.
- Therefore the honest remaining weak-route blocker is quantitative, not merely
  semantic existence: extract a YES-centered certificate with sufficiently
  small `S` (or direct counting slack), i.e. essentially
  `PromiseYesSubcubeCertificateAt` or an equivalent quantitative variant.
- That operational equivalence is now reflected directly in code via
  `promiseYesSubcubeCertificateAt_of_decisionCertificate`:
  the real quantitative theorem target can be read either as
  `PromiseYesSubcubeCertificateAt`
  or as
  `PromiseYesDecisionCertificateAt + hSlack`.
- The stronger encoded-coordinate fallback now also has a precise partial
  bridge into that weak mainline:
  `promiseValueLocalityPackageAt_of_dagStableRestrictionSlackPackageAt_valueSupported`
  and
  `promiseYesSubcubeCertificateAt_of_dagStableRestrictionSlackPackageAt_valueSupported`
  show that any slack restriction package whose surviving `alive` set is
  supported only on semantic value coordinates already yields the chosen
  one-sided YES-centered route.
- More importantly for the terminal weak consumer, the stronger
  encoded-coordinate slack package no longer needs any extra value-support
  hypothesis at all:
  `acceptedFamilyCertificateAt_of_dagStableRestrictionSlackPackageAt`
  and
  `no_small_dag_solver_of_dagStableRestrictionSlackPackageAt_via_acceptedFamily`
  show that the generic accepted-family endpoint is already weak enough to
  absorb the strong fallback route directly by working only with total
  truth-table encodings.
- This strong-fallback absorption is now also compiled at provider/barrier
  level via
  `acceptedFamilyCertificateAtProviderOnSlices_of_dagStableRestrictionSlackPackageAtProvider`,
  `smallDAGAcceptedFamilyStatement_of_dagStableRestrictionSlackPackageAtProvider`,
  `smallDAGAcceptedFamilyStatement_of_shrinkageCertificateProvider`,
  `smallDAGAcceptedFamilyStatement_of_restrictionDataProvider`,
  and the direct closures
  `noSmallDAG_of_dagStableRestrictionSlackPackageAtProviderOnSlices_via_acceptedFamily`,
  `noSmallDAG_of_shrinkageCertificateProviderOnSlices_via_acceptedFamily`,
  `noSmallDAG_of_restrictionDataProviderOnSlices_via_acceptedFamily`.
- The strong sprint target is now also slightly narrower on the source side:
  `dagStableRestrictionSlackPackageAt_of_restrictionExtractionAndHalfBound`
  and
  `dagStableRestrictionSlackPackageAt_of_restrictionExtractionAndNumeric`
  show that one does not need the full shrinkage-certificate route to reach the
  encoded-coordinate slack package; semantic restriction extraction plus a
  quarter/half alive bound already suffice.
- The strong sprint also now has a first genuinely closed restricted-model
  theorem: `smallDAGWitnessRestrictionExtractionAt_of_support` extracts a
  stabilizing restriction directly from `DagCircuit.support`, and
  `dagStableRestrictionSlackPackageAt_of_supportHalfBound` together with
  `no_small_dag_solver_of_supportHalfBound_via_acceptedFamily` closes the
  route for any slice-DAG whose output support is at most half the truth-table
  length.
- The weak mainline now also has a first quantitative restricted-model foothold:
  `promiseValueLocalityPackageAt_of_supportHalfBound_valueSupported`,
  `promiseYesSubcubeCertificateAt_of_supportHalfBound_valueSupported`,
  and `no_small_dag_solver_of_supportHalfBound_valueSupported`
  show that if the output support is both small and already confined to value
  coordinates, then the chosen YES-centered route closes directly.
- A second non-subcube structured producer route is now also compiled:
  `PRGImageAcceptanceAt`,
  `acceptedFamilyCertificateAt_of_prgImageAcceptanceAt`,
  `acceptedFamilyCertificateAtProviderOnSlices_of_prgImageAcceptanceProvider`,
  `noSmallDAG_of_prgImageAcceptanceAtProviderOnSlices`.
- The witness-indexed producer layer now compiles directly into the asymptotic
  accepted-family barrier interface via
  `smallDAGAcceptedFamilyStatement_of_certificateProvider`,
  `smallDAGAcceptedFamilyStatement_of_yesSubcubeCertificateProvider`, and
  `smallDAGAcceptedFamilyStatement_of_prgImageAcceptanceProvider`.
- Added a compiled strong fallback reduction from slice DAG witnesses viewed as
  generic solvers:
  `generalSolverOfSmallDAGWitnessOnSlice`,
  `SmallDAGWitnessSemanticConeCertificateAt`,
  `SmallDAGWitnessRestrictionExtractionAt`,
  `SmallDAGWitnessRestrictionNumericDataAt`,
  `SmallDAGWitnessRestrictionCertificateDataAt`,
  `smallDAGWitnessRestrictionExtractionAt_of_semanticConeCertificate`,
  `smallDAGWitnessRestrictionExtractionProviderOnSlices_of_semanticConeProvider`,
  `smallDAGWitnessShrinkageCertificateAt_of_restrictionData`,
  `smallDAGWitnessShrinkageCertificateProviderOnSlices_of_restrictionDataProvider`,
  `SmallDAGWitnessShrinkageCertificateAt`,
  `dagStableRestrictionSlackPackageAt_of_shrinkageCertificate`,
  `dagStableRestrictionSlackPackageAtProviderOnSlices_of_shrinkageCertificateProvider`,
  `smallDAGLocalityStatement_of_shrinkageCertificateProvider`,
  `smallDAGLocalityStatement_of_restrictionDataProvider`,
  `smallDAGLocalityStatement_of_semanticConeAndNumericProvider`,
  `smallDAGLocalityStatement_of_restrictionExtractionAndNumericProvider`.
- Current remaining gap for the weak route is now the actual source theorem:
  derive a generic accepted-family weak certificate (working name:
  `AcceptedFamilyCertificateAt`) from DAG semantics on slices, or derive a
  structured producer such as `YesSubcubeCertificateAt` /
  `PRGImageAcceptanceAt` and reduce it to that generic consumer. Older
  encoded-coordinate packages remain fallback surfaces rather than the
  canonical source API.
- On the strong fallback side, the remaining source target is now split more
  honestly as well:
  first produce `SmallDAGWitnessSemanticConeCertificateAt` for the DAG-derived
  general solver on slices, then reduce it to semantic restriction extraction,
  then separately prove the numeric side conditions upgrading that extraction
  to `SmallDAGWitnessRestrictionCertificateDataAt`.
- A repo scan confirms that the existing tree already has formula-side
  analogues and downstream restriction/certificate bridges, but no existing
  DAG-side theorem producing a generic accepted-family weak certificate,
  `YesSubcubeCertificateAt`, or `SmallDAGWitnessSemanticConeCertificateAt`
  from a `SmallDAGWitnessOnSlice`.

## Current frontier (2026-03-16)

- The current singleton `β`-route is no longer an open plumbing problem.
  It has been reduced to a decision layer:
  `CurrentSingletonRouteWitnessProp` plus the nat-crossmul comparison wrapper.
- This route is currently nongeneric: without a family-specific comparison
  theorem controlling `sYES`, the repository neither proves nor refutes a
  chosen selector witness from the current singleton theorem layer.
- Atlas/Rf compatibility is now promoted from scratch to named API:
  `pnp3/Magnification/AC0AtlasBridge.lean` exposes bridges from
  `SemanticSwitchingCertificatePartial` to
  `BoundedAtlasScenario` and `ScenarioBudget`.
- Two false downstream routes are now formally ruled out:
  `ScenarioBudget -> strict large-family gap` and
  `ApproxClass -> small mismatch`.
- The recommended active contradiction route is now the family-level package
  `SemanticSwitchingApproxFamilyPackagePartial` / provider
  `SemanticSwitchingApproxFamilyProviderPartial` in
  `pnp3/Magnification/AC0ApproxFamilyBridge.lean`.
- This route targets the existing counting contradiction
  `Counting.incompatibility` directly, instead of trying to re-enter the old
  `AntiChecker_Partial` large-family-gap endpoint.
- A symmetry-transport layer is now formalized for `UnionClass` and
  `ApproxClass`: coordinate permutations preserve approximation quality, but
  they transport the dictionary to `R.map (permuteSubcube π.symm)` rather than
  keeping a single fixed `R`.
- The older provenance-aware singleton package
  `SemanticSwitchingSmallMismatchPackagePartial` remains as a stronger-source
  side branch: it would recover linked polylog-small testsets, but it is no
  longer the primary contradiction route.
- The remaining source-side mathematical question is now:
  can semantic switching produce one large finite family `Y` lying in a common
  `ApproxClass`, with `Y.card` above the counting capacity bound?
- More sharply: the current symmetry/orbit idea is blocked not by
  `ApproxClass` closure itself, but by the need for one common fixed
  dictionary/union budget for all members of `Y`.
- The exact scratch frontier is now explicit:
  for a source-produced scenario dictionary `R = scenario.atlas.dict`, the
  next red goal is to exhibit a nontrivial permutation `π` with
  `R.map (permuteSubcube π.symm) = R`.
- Provenance-specific unfolding sharpens this further:
  `scenarioFromAC0_with_polylog` and `commonPDT_from_AC0_with_polylog` do not
  construct a new canonical tree. They simply repackage
  `hpoly.shrinkage.commonPDT`, so the current orbit/stabilizer branch has no
  generic canonical `PDT` shape to exploit.
- The next minimal stronger-source frontier is now explicit at the source
  layer:
  `AC0LocalityBridge.SemanticSwitchingNontrivialFamilyPackagePartial` /
  provider ask only for one semantic switching certificate whose family payload
  already satisfies `2 ≤ F.length`.
- Independently of the tree-symmetry issue, the explicit current internal
  source route is singleton before counting starts:
  `AC0LocalityBridge.formulaSemanticMultiSwitchingProvider_internal_singleton_family`
  shows that the earliest exported semantic package already has family payload
  `[f]`.
- This is now also fixed directly on the certificate layer:
  `AC0LocalityBridge.formulaSemanticMultiSwitchingProvider_internal_cert_length_eq_one`
  and
  `AC0LocalityBridge.formulaSemanticMultiSwitchingProvider_internal_not_nontrivial_family`
  show that the explicit internal certificate already has `F.length = 1`, so
  the minimal nontrivial-family source frontier is not realized by the current
  active internal source line.
- Independently of the tree-symmetry issue, the explicit current internal
  source route remains singleton all the way through the later contradiction
  entry layer:
  `LowerBounds.current_source_route_no_two_point_family` shows that the route
  used by `current_source_route_gives_singleton_approxClass` cannot directly
  supply even a two-point family.
- The current source-family branch should now be treated as locally exhausted:
  the active internal semantic route is singleton at package, certificate, and
  downstream `ApproxClass` entry layers.
- A new singleton/provenance endpoint layer is now present in
  `pnp3/LowerBounds/SingletonProvenanceEndpoint.lean`:
  `SemanticSwitchingSingletonProvenancePackagePartial` packages one
  source-produced bounded atlas scenario, one linked function `f`, and the
  explicit identity `pack.cert.F = [f]`.
- This package is realized directly by the current internal provider via
  `LowerBounds.singletonProvenancePackage_of_internal_provider`.
- The singleton package now also extracts the exact bounded witness already
  carried by the source-produced scenario:
  `LowerBounds.singletonProvenance_boundedWitness`.
- The package also re-derives the already-known approximation fact:
  `LowerBounds.linked_function_in_approxClass_of_singletonProvenancePackage`.
- The bridge
  `LowerBounds.smallMismatchPackage_of_singletonProvenancePackage_of_mismatch_card_le`
  now makes the frontier exact: the singleton/provenance layer already
  supplies every field needed for the stronger small-mismatch package except
  the one missing mismatch-cardinality bound.
- A new density-oriented singleton endpoint layer is now present in
  `pnp3/LowerBounds/SingletonDensityEndpoint.lean`.
  It packages the same singleton provenance object together with the exact
  source-produced bounded witness `S`, the inherited error bound
  `errU f S ≤ ε`, and the numerical estimate `ε ≤ 1 / (n + 2)`.
- This layer also exposes the natural testset
  `T = mismatchSet (coveredB S) f`, proves that `f` lies in
  `ApproxOnTestset ... T`, and bounds the density of `T` by `1 / (n + 2)`.
- A decisive abstract probe on the old testset-capacity endpoint now closes
  negatively: `testsetCapacity < 1` is impossible already for every
  `BoundedAtlasScenario`, because `testsetCapacity` is a natural number
  bounded below by `1`.
- Consequently, the old testset-capacity contradiction route is formally dead
  even on the singleton density branch:
  `LowerBounds.naturalMismatchTestset_not_testsetCapacity_lt_one_of_singletonDensityPackage`
  rules it out without using any formula-specific internals.
- This is the first genuinely DAG-robust no-go extracted from the current
  singleton density layer. The next meaningful endpoint must consume singleton
  provenance plus density/error data directly; it cannot be another wrapper
  around the old `testsetCapacity < 1` endpoint.
- A new formula-free consumer layer now exists in
  `pnp3/LowerBounds/SingletonDensityContradiction.lean`.
  It factors the current singleton-density package through the abstract
  scenario-level payload `AbstractSingletonDensityPayload`, carrying only:
  `sc`, `f ∈ sc.family`, bounded witness `S`, `errU ≤ ε`, and
  `ε ≤ 1 / (n + 2)`.
- This abstraction already rederives all natural mismatch consequences without
  referencing formula-specific source constructors and therefore marks the
  first genuinely positive DAG-relevant staging layer on the singleton route.
- The raw abstract payload is now also known to be consistent on a trivial
  empty-dictionary / constant-zero scenario, so a contradiction theorem from
  `AbstractSingletonDensityPayload` alone is the wrong target.
- The minimally strengthened abstract object is now
  `LowerBounds.AbstractLinkedSingletonDensityPayload`, but this wrapper is now
  also known to be vacuous: any raw payload can choose `target := f` and obtain
  it for free.
- The first non-vacuous abstract strengthening is now
  `LowerBounds.AbstractTargetedSingletonDensityPayload`, but this generic
  target class is still too weak: it remains consistent for trivial externally
  chosen targets such as the constant-zero function.
- The semantically fixed gap-slice target is now isolated as
  `LowerBounds.AbstractGapTargetedSingletonDensityPayload`, where the target is
  no longer chosen freely but pinned to `gapPartialMCSP_Language p` on the
  relevant slice.
- This fixed semantic payload is now realized from both active source lines:
  the current formula-side singleton-density route and a strict `PpolyDAG`
  witness for the same slice.
- The consumer-side gap-target route is no longer a single undifferentiated
  "missing contradiction theorem": it now has an explicit
  stable-restriction/locality stack
  (`AbstractGapStableRestrictionPayload`,
  `AbstractGapLocalityPayload`,
  `stableRestrictionGoal_of_abstractGapTargetedPayload`,
  `localityGoal_of_abstractGapTargetedPayload`)
  plus contradiction theorems reducing this stack to
  `MCSPGapLocality.no_local_function_solves_mcsp`.
- The first real producer into that new stack is already present on the formula
  side: the support-bounds / restriction-data / certificate route now factors
  through
  `stableRestrictionGoal_of_abstractGapTargetedPayload_of_supportBounds`.
- Therefore the honest remaining source-side blocker is now specifically the
  DAG/leaves side: no strict DAG theorem yet produces a stable restriction (or
  an equivalent locality payload) for the canonical gap-target payload.
- The cheapest consumer subroute is now formalized as an empty-witness route.
  It reduces to a purely formula-free Shannon-style numeric condition:
  `circuitCountBound * (3/4)^tableLen ≤ sc.atlas.epsilon`.
- That empty-witness subroute is now known to be too weak for contradiction:
  even when the Shannon inequality makes `Rf = []` admissible, the old
  contradiction still collapses to the impossible requirement
  `testsetCapacity < 1`.
- The next abstract strengthening now lives one level higher, as a non-empty
  witness payload
  `LowerBounds.AbstractGapWitnessedPayload`. It adds one explicit non-empty
  bounded witness `Rf` inside the same fixed gap-target scenario and already
  yields the strongest purely witness-level consequence available without new
  target semantics: some input is covered by `Rf`.
- The first semantic strengthening on top of this is now
  `LowerBounds.AbstractGapCubeSoundWitnessPayload`: every point lying in a
  witness cube is forced to be a YES-point of the fixed gap target.
- This closes the previous consumer-side red goal
  `f x = true` on covered points and upgrades the route to an existential
  YES-input statement for the fixed gap slice.
- There is now a thin contradiction theorem showing that YES-soundness would be
  enough if each witness cube also contained at least one NO-point of the same
  fixed gap target.
- So the active semantic barrier is no longer pointwise YES-soundness itself,
  but a negative/local invariant of the form "every non-empty witness cube
  contains a NO-point."
- The DAG-facing route is therefore split into two clearly documented open
  fronts:
  1) restriction route: produce a small stable restriction from DAG/leaves data;
  2) witness/selector route: strengthen the existing cube/selector semantics to
     a contradiction-strength invariant.
- See `pnp3/Docs/GapTarget_StableRestriction_Route.md` for the current
  route-level handoff and exact remaining targets.
- A new implementation-facing plan now fixes the recommended mainline: build a
  DAG-native stable-restriction producer rather than trying to strengthen the
  current singleton selectors in place. See
  `pnp3/Docs/Unconditional_NP_not_subset_PpolyDAG_Plan.md`.

## Active final theorem surface

File: `pnp3/Magnification/FinalResult.lean`

- `NP_not_subset_PpolyFormula_final*`
- `NP_not_subset_PpolyReal_final*`
- `P_ne_NP_final*`
- asymptotic NP bridge helpers:
  `AsymptoticNPPullback`

Formula-route progress note (2026-03-15):

- Active formula final wiring now consumes asymptotic NP witness directly:
  `NP_not_subset_PpolyFormula_final_with_provider` is routed through
  `strictAsymptotic` + `asymptotic_formula_collapse`.
- Active `PpolyReal` final wiring is now routed through the same asymptotic
  formula-separation path, then converted by the current-interface equivalence
  `PpolyFormula -> PpolyReal`.
- `AsymptoticFormulaTrackHypothesis` now carries explicit `sliceEq`, and
  `asymptotic_formula_collapse` consumes it from the hypothesis package.
- `MagnificationAssumptions.switching` now carries
  `FormulaSupportBoundsFromMultiSwitchingContract` (strengthened A9 boundary),
  and active formula/real finals derive support-bounds and provider internally
  via `formula_support_bounds_from_multiswitching` and
  `structuredLocalityProviderPartial_of_supportBounds`.
- Exact singleton `epsilon`, raw YES-density bounds, and the current singleton
  empty-witness decision layer are now formalized in-repo.
- Source semantic certificates now compose directly with atlas/downstream
  scenario objects through `Magnification.AC0AtlasBridge`.
- The direct family-level `ApproxClass` route is now explicit in
  `Magnification.AC0ApproxFamilyBridge`, with a contradiction theorem that
  reuses the existing counting endpoint.
- The singleton small-mismatch frontier remains formalized as a stronger-source
  side branch, with a thin bridge to linked polylog-small testsets; the new
  singleton/provenance and singleton-density endpoints isolate exactly why the
  current source line does not yet reach that branch or the old testset
  endpoint.

## Interpretation

- The repository currently formalizes a constructive, axiom-clean,
  AC0/formula pipeline plus conditional DAG final wrappers.
- Recent work has mainly eliminated false routes and localized the remaining
  mathematical barriers; it has not yet discharged the DAG-side blocker below.
- Final `P ≠ NP` wrappers are conditional.
- The project does not currently contain an unconditional in-repo theorem
  `P ≠ NP`.

## Remaining blockers to unconditional status

Active DAG final wrapper `P_ne_NP_final` still requires one external input:

1. `NP_not_subset_PpolyDAG` (`hNPDag`)

What remains open around that input is now split more explicitly:

1. Primary planned blocker:
   formalize and prove a weaker one-sided promise/value DAG endpoint that is
   sufficient for `NP_not_subset_PpolyDAG`.
2. Stronger optional fallback already present:
   stable-restriction / certificate-provider / invariant-provider routes.
3. Final-surface cleanup still pending:
   finish routing the DAG endpoint through an asymptotic surface rather than
   one fixed slice.

Current inclusion-side status:

- No-arg linear output-wire witness is closed:
  `compiledAcceptOutputWireAgreementLinear_internal`.
- No-arg inclusion endpoint is closed:
  `proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG`.
- `RuntimeConfigEqStepCompiled` remains open only for legacy bridge routes
  (`runtimeConfig` path with `step = id`), not for the active no-arg linear
  closure.

## Contract hardening updates

- A9 interface hardening is closed:
  `FormulaSupportBoundsFromMultiSwitchingContract` now includes an explicit
  semantic linkage field from AC0-family payload to the extracted strict formula.
- The vacuous empty-family constructor for this contract was removed from
  `Magnification/LocalityProvider_Partial.lean`.
- The active locality bridge now exposes a combined theorem
  `formula_support_bounds_and_semantic_link_from_multiswitching`, so the
  semantic linkage is preserved at the API level (alongside numeric bounds).
- Added split constructor
  `multiswitching_contract_of_semantic_provider_and_support_bounds`:
  full A9 contract is now assembled from
  `FormulaSemanticMultiSwitchingProvider` + `FormulaSupportRestrictionBoundsPartial`.
- Added internal constructive provider
  `AC0LocalityBridge.formulaSemanticMultiSwitchingProvider_internal` and
  internalized constructor
  `multiswitching_contract_internalized_of_support_bounds`, so semantic
  AC0/multi-switching linkage is now in-repo constructive (no external semantic
  provider input needed for contract assembly).

## Canonical CCDT bridge updates

- A8 closure is now integrated in `ThirdPartyFacts/Facts_Switching.lean`.
- Added constructive leaf-partition machinery for canonical CNF DT/CCDT:
  `LeafPartitionWithin`,
  `canonicalDT_CNF_aux_leaf_of_compatible`,
  `canonicalDT_CNF_aux_leaf_unique_of_compatible`,
  `canonicalCCDT_CNF_aux_leafPartition_free`.
- Removed external `LeafPartition` hypothesis from
  `shrinkage_negDnfFamily_to_dnf_canonicalCCDT`; canonical partition is now
  derived internally from `canonicalCCDT_CNF_aux`.

## Documentation policy

Any file claiming unconditional `P ≠ NP` before these blockers are discharged
is incorrect and must be treated as outdated.
