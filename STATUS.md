# Project Status (current)

Updated: 2026-03-16

Authoritative checklist: `CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Release positioning for current tree: `RELEASE_RC.md`.

## Current verified state

- Active `axiom` declarations in `pnp3/`: 0
- Active `sorry/admit` in `pnp3/`: 0
- `./scripts/check.sh` passes (rechecked on 2026-03-16)
- Current audit/regression tests pass (rechecked on 2026-03-16):
  `AxiomsAudit`, `BarrierAudit`, `BarrierBypassAudit`,
  `BridgeLocalityRegression`

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
- The next honest positive frontier is now a contradiction theorem from this
  semantically fixed gap-target payload, or another equally formula-free
  strengthening, without pulling formula-specific constructors back into the
  consumer.

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
- `AsymptoticFormulaTrackHypothesis` now carries explicit `sliceEq`, and
  `asymptotic_formula_collapse` consumes it from the hypothesis package.
- Fixed-slice witnesses remain as auxiliary support (`strictFixed`) for
  helper/localized routes (not as the primary formula-final endpoint input).
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

Active DAG final wrapper `P_ne_NP_final` requires one external input:

1. `NP_not_subset_PpolyDAG` (`hNPDag`)

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
