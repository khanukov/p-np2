# TODO / Roadmap (current)

Updated: 2026-03-16

Canonical blocker checklist lives in `CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
Current release checklist/w wording guardrail: `RELEASE_RC.md`.

## Snapshot

- Active `axiom` in `pnp3/`: 0
- Active `sorry/admit` in `pnp3/`: 0
- Baseline checks: `./scripts/check.sh` and current audit tests pass
- Final API remains conditional (`pnp3/Magnification/FinalResult.lean`)

## Current frontier (2026-03-16)

1. The current singleton `β`-route is now only a decision layer:
   `CurrentSingletonRouteWitnessProp` records when the theorem layer already
   admits the empty selector witness. Without a family-specific nat comparison
   theorem, this route remains nongeneric.
2. The source semantic certificate now has a named atlas/downstream bridge:
   `pnp3/Magnification/AC0AtlasBridge.lean` exposes
   `SemanticSwitchingCertificatePartial -> BoundedAtlasScenario/ScenarioBudget`.
3. Two generic downstream routes are now formally closed:
   `ScenarioBudget -> strict large-family gap` and
   `ApproxClass -> small mismatch`.
4. The recommended active contradiction route is now the family-level package
   `SemanticSwitchingApproxFamilyPackagePartial` / provider
   `SemanticSwitchingApproxFamilyProviderPartial` in
   `pnp3/Magnification/AC0ApproxFamilyBridge.lean`.
5. This route feeds the already formalized counting contradiction
   `Counting.incompatibility` directly, bypassing the dead
   `ScenarioBudget -> AntiChecker` branch.
6. A symmetry-transport layer now exists for `UnionClass`/`ApproxClass`, but
   it transports the dictionary together with the function. The current
   orbit-lift barrier is therefore not `ApproxClass` closure; it is the need
   for one large finite family `Y` living in one common fixed dictionary.
7. The immediate fixed-dictionary probe is now explicit: for the current
   source-produced `scenario.atlas.dict`, find a nontrivial `π` with
   `dict.map (permuteSubcube π.symm) = dict`, or conclude that the stabilizer
   is too small to support the orbit route.
8. Provenance-specific unfolding shows that
   `commonPDT_from_AC0_with_polylog` is only a cast/repackaging of
   `hpoly.shrinkage.commonPDT`. The current source theorem therefore does not
   expose a canonical tree shape that would make a generic stabilizer theorem
   plausible.
9. The earliest exported current internal semantic package is already
   singleton:
   `AC0LocalityBridge.formulaSemanticMultiSwitchingProvider_internal_singleton_family`
   shows that `formulaSemanticMultiSwitchingProvider_internal` exports
   family payload `[f]`.
10. The next minimal stronger-source target is now explicit:
   `AC0LocalityBridge.SemanticSwitchingNontrivialFamilyPackagePartial` asks
   only for one source-produced certificate with `2 ≤ F.length`.
   This is the first meaningful frontier above the current singleton provider.
11. The current active internal source line does not realize even this minimal
    frontier:
    `AC0LocalityBridge.formulaSemanticMultiSwitchingProvider_internal_cert_length_eq_one`
    and
    `AC0LocalityBridge.formulaSemanticMultiSwitchingProvider_internal_not_nontrivial_family`
    show that its explicit certificate already has `F.length = 1`.
    Treat the current source-family branch as locally exhausted.
12. The explicit current internal route remains singleton before counting:
   `LowerBounds.current_source_route_no_two_point_family` rules out a direct
   two-point family lift from the already packaged singleton `ApproxClass`
   witness.
13. The current source-family branch should now be treated as locally closed:
    the active internal provider is singleton at package, certificate, and
    downstream `ApproxClass` entry layers.
14. The new active endpoint probe is now singleton/provenance-based:
    `LowerBounds.SemanticSwitchingSingletonProvenancePackagePartial`
    packages one source-produced bounded atlas scenario, one linked function,
    and the explicit identity `pack.cert.F = [f]`.
15. This package is realized by the current internal route through
    `LowerBounds.singletonProvenancePackage_of_internal_provider`.
16. The singleton package also exposes the exact bounded witness already
    supplied by the source-produced scenario:
    `LowerBounds.singletonProvenance_boundedWitness`.
17. The bridge
    `LowerBounds.smallMismatchPackage_of_singletonProvenancePackage_of_mismatch_card_le`
    now shows that the singleton/provenance layer is missing only one extra
    input before it reaches the stronger small-mismatch branch.
18. A new density-oriented singleton endpoint now packages the exact current
    internal route output more faithfully:
    source-produced singleton provenance, bounded witness `S`,
    `errU f S ≤ ε`, and `ε ≤ 1 / (n + 2)`.
19. This density layer produces the natural mismatch testset
    `T = mismatchSet (coveredB S) f`, shows
    `f ∈ ApproxOnTestset ... T`, and proves the density bound
    `|T| / 2^n ≤ 1 / (n + 2)`.
20. A decisive abstract probe on the old singleton-density endpoint is now
    closed negatively: `testsetCapacity < 1` is impossible for every
    `BoundedAtlasScenario`, since `testsetCapacity` is a natural number with
    a general lower bound `1 ≤ testsetCapacity`.
21. Therefore the old `testsetCapacity < 1` contradiction route is dead not
    just for the current formula source line, but already at the abstract
    scenario level. This is the first singleton-density no-go that appears
    plausibly reusable on a future DAG-side route.
22. A new formula-free consumer layer now factors the active internal route
    through `LowerBounds.AbstractSingletonDensityPayload`, carrying only
    scenario-level data:
    `sc`, `f ∈ sc.family`, bounded witness `S`, `errU ≤ ε`, and
    `ε ≤ 1 / (n + 2)`.
23. This abstract payload already rederives the natural mismatch testset,
    `ApproxOnTestset` membership, density bounds, and the abstract no-go for
    `testsetCapacity < 1` without referring to formula-specific source
    constructors.
24. The raw abstract singleton-density payload is now explicitly known to be
    consistent on a trivial empty-dictionary / constant-zero scenario, so
    `AbstractSingletonDensityPayload -> False` is not the right target.
25. The compatibility wrapper
    `LowerBounds.AbstractLinkedSingletonDensityPayload` is now explicitly known
    to be vacuous: any raw payload can realize it by choosing `target := f`.
26. The first non-vacuous abstract strengthening is now
    `LowerBounds.AbstractTargetedSingletonDensityPayload`, but this generic
    target class is still too weak because it remains consistent for trivial
    externally fixed targets such as the constant-zero function.
27. The new semantically fixed frontier is now
    `LowerBounds.AbstractGapTargetedSingletonDensityPayload`, where the target
    is pinned to the gap-PartialMCSP slice itself rather than chosen freely.
28. This semantically fixed payload is now known to admit both a formula-side
    realization and a strict DAG-side realization. The active missing piece is
    therefore no longer a source package for this target, but a consumer /
    contradiction theorem from that common payload.
29. The DAG-facing route is now formally reduced to a single missing theorem:
    a contradiction consumer from
    `LowerBounds.AbstractGapTargetedSingletonDensityPayload`.
30. The cheapest consumer subroute is now explicit in code: the empty-witness
    route reduces to proving the formula-free numeric inequality
    `circuitCountBound * (3/4)^tableLen ≤ sc.atlas.epsilon`.
31. The empty-witness subroute is now known to be too weak: even when that
    numeric inequality closes, it yields only admissibility of `Rf = []`, not
    contradiction.
32. The next consumer-facing strengthening is now
    `LowerBounds.AbstractGapWitnessedPayload`, which adds one explicit
    non-empty bounded witness `Rf` over the same fixed gap-target payload.
33. The strongest purely witness-level consequence currently extracted from
    that new payload is just `∃ x, coveredB Rf x = true`. The next honest
    consumer probe must therefore use target semantics more deeply than
    witness existence and density alone.
34. The first such semantic strengthening is now
    `LowerBounds.AbstractGapCubeSoundWitnessPayload`, which assumes every
    point in every witness cube is a YES-point of the fixed gap target.
35. This semantic strengthening already closes the previous red goal
    `f x = true` on covered points and yields existence of a YES-input for the
    fixed gap slice.
36. A thin contradiction theorem is now available: YES-sound witness cubes
    would already be inconsistent if one could also show that every witness
    cube contains some NO-point of the fixed gap target.
37. So the next honest frontier is no longer pointwise YES-soundness but the
    negative/local invariant "every non-empty witness cube contains a
    NO-point."
38. The singleton small-mismatch package/provider remains in the codebase as a
    stronger-source side branch. The active positive frontier is now a new
    contradiction theorem that consumes the semantically fixed gap-target
    payload, or some equally formula-free strengthening, without reintroducing
    formula-specific source constructors into the consumer.
    directly, without exact polylog-small mismatch cardinality and without the
    dead `testsetCapacity < 1` endpoint.

## What is already closed

1. AC0/formula separation wiring is present and compiles.
2. Internal linear step-spec provider is closed:
   `stepCompiledLinearCandidateStepSpecProvider_internal`.
3. Linear route has closed internal size and correctness witnesses:
   `compiledRuntimeCircuitSizeBoundLinear_internal`,
   `compiledRuntimeAcceptCorrectnessLinear_internal`.
4. Axiom/sorry hygiene is clean in active `pnp3/`.

## What still blocks unconditional `P ≠ NP`

1. Internalize `hNPDag`: `NP_not_subset_PpolyDAG`.

Inclusion-side status:

1. Closed no-arg evaluator/output-wire agreement:
   `compiledAcceptOutputWireAgreementLinear_internal`.
2. Closed no-arg inclusion endpoint:
   `proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG`.
3. Default `P_ne_NP_final*` wiring already consumes this no-arg
   inclusion endpoint.

## A3 + A4 milestone (closed in active route)

Status: closed on 2026-03-14 in active `Magnification.FinalResult` API.

What was changed:

1. Removed hidden pointwise-at-`N0` use from active final endpoints:
   `NP_not_subset_PpolyFormula_final*` and `NP_not_subset_PpolyReal_final*`
   now take explicit `(n, hn : N0 ≤ n)`.
2. Replaced fixed-parameter NP-family wrapper with asymptotic NP bridge package:
   `AsymptoticNPPullback` carries
   `NP_strict (gapPartialMCSP_AsymptoticLanguage spec)` and per-`n` strict NP
   witnesses for `gapPartialMCSP_Language (pAt n hn)`.
3. Removed now-obsolete intermediate wrappers:
   old `StrictGapNPFamily` / `GapPartialMCSPTMWitnessFamily` path is deleted.
4. Constructive TM route no longer requires an external NP pullback function:
   `toFixed` is internalized from explicit TM-witness streams.
5. Barrier wrapper no longer hardcodes `N0`; it now takes explicit `(n, hn)`.

Verification:

1. `lake build` passes.
2. `lake build 2>&1 | rg "warning:"` is empty.
3. Regression/audit tests compile with the new signatures
   (`Tests/BridgeLocalityRegression`, `Tests/AxiomsAudit`, barrier audits).

## A9 milestone (closed end-to-end in active route)

Status: closed on 2026-03-14 in `Magnification.AC0LocalityBridge`.

What was changed:

1. `FormulaSupportBoundsFromMultiSwitchingContract` now requires an explicit
   semantic link: some `f ∈ F` extensionally equals the extracted formula
   semantics `FormulaCircuit.eval c` (after length cast).
2. Removed the vacuous reverse constructor
   `multiswitching_contract_of_formula_support_bounds` that previously built
   the contract via an unrelated empty AC0 family.
3. Added audit helper theorem `AC0LocalityBridge.package_semantic_link` and
   wired it into `Tests/AxiomsAudit`.
4. Added `formula_support_bounds_and_semantic_link_from_multiswitching` so the
   active locality bridge exports both numeric bounds and semantic linkage in
   one theorem (link no longer disappears at the projection boundary).
5. Added a split-constructor path:
   `multiswitching_contract_of_semantic_provider_and_support_bounds` builds the
   full strengthened A9 contract from two independent inputs:
   semantic AC0/multi-switching provenance + numeric support bounds.
6. Added an internal constructive semantic provider:
   `formulaSemanticMultiSwitchingProvider_internal`.
7. Added a fully internalized constructor:
   `multiswitching_contract_internalized_of_support_bounds` derives the
   strengthened A9 contract directly from support-bounds assumptions.

Interpretation:

1. The contract can no longer be satisfied by a completely irrelevant AC0
   family payload.
2. Semantic linkage is now constructive in-repo (internal provider exists),
   while numeric obligations remain exactly the explicit support-bounds inputs.

## A8 milestone (closed in canonical CCDT bridge)

Status: closed on 2026-03-14 in `ThirdPartyFacts.Facts_Switching`.

What was changed:

1. Added constructive `LeafPartitionWithin` framework for canonical trees.
2. Proved canonical CNF DT leaf completeness/uniqueness on compatible inputs:
   `canonicalDT_CNF_aux_leaf_of_compatible`,
   `canonicalDT_CNF_aux_leaf_unique_of_compatible`.
3. Proved leaf refinement-to-root for both canonical DT and canonical CCDT:
   `canonicalDT_CNF_aux_leaves_refine_root`,
   `canonicalCCDT_CNF_aux_leaves_refine_root`.
4. Proved canonical CCDT leaf partition at free root:
   `canonicalCCDT_CNF_aux_leafPartition_free`.
5. Removed external `hpart : LeafPartition ...` argument from
   `shrinkage_negDnfFamily_to_dnf_canonicalCCDT`; partition is now derived
   internally from canonical CCDT structure.

Verification:

1. `lake build pnp3/ThirdPartyFacts/Facts_Switching.lean` passes.
2. `lake build` passes.
3. `./scripts/check.sh` passes.

## Formula-track milestone context

Status: infrastructure substantially internalized on 2026-03-15 for active
`codex-refactoring` route.

Scope:

1. Primary target is formula-track only:
   unconditional `NP_not_subset_PpolyFormula` via asymptotic language collapse.
2. This does not close unconditional `P ≠ NP`; DAG blocker
   `NP_not_subset_PpolyDAG` remains independent.
3. Fixed-slice (`gapPartialMCSP_Language p`) theorems stay as helper lemmas, not
   the final claim surface for this milestone.

Main theorem target:

1. Add a direct asymptotic collapse theorem (no external provider/transfer
   assumptions in theorem statement):
   `asymptotic_formula_collapse (spec) :
      PpolyFormula (gapPartialMCSP_AsymptoticLanguage spec) → False`.

Implementation plan:

1. Add `pnp3/Magnification/AsymptoticFormulaCollapse.lean` and keep the collapse
   proof there as the single source of truth for formula-target finalization.
2. Internalize support-bounds extraction as a constructive theorem:
   `formula_support_bounds_internal : FormulaSupportRestrictionBoundsPartial`.
3. Build `StructuredLocalityProviderPartial` internally from support bounds
   (through existing certificate/engine constructors), without default
   `Nonempty` wrappers in the core proof path.
4. Rewire `FinalResult.lean` so active formula finals are grounded in the new
   asymptotic collapse theorem; keep fixed-slice route only as supporting lemmas.
5. Resolve `strictAsymptotic`/`strictFixed` mismatch:
   ensure the active proof path consumes the asymptotic witness directly and
   keeps slice witnesses auxiliary.
6. Add audit/regression checks so formula-final regressions cannot silently
   reintroduce external provider-style assumptions in the core theorem.

Progress (2026-03-15):

1. Added `pnp3/Magnification/AsymptoticFormulaCollapse.lean` as the dedicated
   collapse module for this milestone.
2. Added explicit constructive bridge helpers in that module:
   `ppolyFormula_fixed_of_asymptotic_slice`,
   `asymptotic_formula_collapse_of_slice_agreement`,
   and strict-NP wrapper
   `NP_not_subset_PpolyFormula_of_asymptotic_formula_collapse`.
3. Rewired `FinalResult.lean` so
   `NP_not_subset_PpolyFormula_final_with_provider` now consumes
   `hNPbridge.strictAsymptotic` on the active path (instead of relying on
   `strictFixed` as the endpoint input).
4. Added explicit `sliceEq` to `AsymptoticFormulaTrackHypothesis`; active
   `asymptotic_formula_collapse` now obtains slice agreement from this package
   directly (no extra theorem argument at call sites).
5. Removed obsolete intermediate formula-final wrapper that duplicated the old
   fixed-slice endpoint route.
6. Moved active `MagnificationAssumptions.switching` payload from a raw
   `StructuredLocalityProviderPartial` field to
   `FormulaSupportRestrictionBoundsPartial`; provider is now derived internally
   at formula/real final wrappers.
7. Added provider-free formula/real final wrappers:
   `NP_not_subset_PpolyFormula_final_with_supportBounds`,
   `NP_not_subset_PpolyReal_final_with_supportBounds`.
8. Raised final switching boundary to the strengthened A9 contract:
   `MagnificationAssumptions.switching` now carries
   `FormulaSupportBoundsFromMultiSwitchingContract`, and active
   `NP_not_subset_PpolyFormula_final` / `NP_not_subset_PpolyReal_final`
   derive support-bounds internally via
   `formula_support_bounds_from_multiswitching`.

Remaining for this milestone:

1. Probe construction of the family-level direct contradiction package
   `SemanticSwitchingApproxFamilyProviderPartial` and localize the first red
   goal in the large finite family `Y`, with special attention to the new
   common-dictionary barrier exposed by symmetry transport.
2. Concretely probe the fixed-dictionary stabilizer:
   try to produce a nontrivial `π` with
   `scenario.atlas.dict.map (permuteSubcube π.symm) = scenario.atlas.dict`.
3. If this fails generically, decide whether to:
   strengthen the source theorem to expose a canonical shrinkage/PDT witness,
   or abandon the orbit route in favor of a family lift not based on tree
   symmetries.
4. Since the current explicit singleton route cannot even produce two distinct
   functions, any fixed-dictionary family lift must come from a richer
   source theorem than the currently packaged singleton witness.
5. Decide whether the next research branch is:
   a family lift inside one fixed atlas dictionary, or a revised counting
   endpoint that can tolerate transported dictionaries.
6. Keep the singleton small-mismatch branch as a secondary stronger-source
   program only if the family-level route stalls for clearly source-side
   reasons.
7. If a concrete intended asymptotic family is introduced, add a family-
   specific nat comparison theorem for the singleton decision layer; otherwise
   treat the chosen-`β` route as nongeneric.
8. Only after (1)-(7), decide whether an additional internalization step is
   still needed for the asymptotic formula-collapse endpoint.

Acceptance criteria for this milestone:

1. A direct theorem of the shape
   `PpolyFormula (gapPartialMCSP_AsymptoticLanguage spec) → False` compiles in
   active code.
2. Active formula-separation final endpoint is derived from this theorem.
3. `./scripts/check.sh` and existing audits remain green.
4. Documentation explicitly distinguishes:
   formula-track unconditional target vs DAG-side `P ≠ NP` blocker.

## Execution order

1. Keep docs honest: no unconditional claim while DAG blockers remain.
2. Complete asymptotic formula-collapse milestone above.
3. Then continue DAG-side work (`NP_not_subset_PpolyDAG`) for unconditional
   `P ≠ NP`.
4. Only after (3), switch global wording to unconditional.

## Done criteria

1. Final route no longer needs external DAG separation input.
2. `./scripts/check.sh` and current audit tests pass unchanged.
3. Top-level docs report unconditional status consistently.
