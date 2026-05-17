# A05 audit: `pnp3/LowerBounds/`

Task: A05  
Engineer handle: codex  
Branch: `khanukov/phase1-A05-codex`  
Audit date: 2026-05-17

## 1. Executive verdict

**Verdict: PARTIAL_BUT_USEFUL.**

`pnp3/LowerBounds/` contains substantial kernel-checked infrastructure and several real contradiction lemmas for fixed-slice Partial-MCSP solver interfaces, especially the AC0/Step-C and local-solver anti-checker surfaces. However, the strongest advertised AC0 endpoint is only as strong as the repository's enriched `SmallAC0Solver_Partial` interface: that solver structure already contains circuit evidence and an `AC0EasyFamilyDataPartial` large-family payload, so the public no-solver theorem is not an external AC0 lower bound in the usual sense. The directory also contains a large DAG/asymptotic migration layer whose endpoints are conditional on explicit bridge/provider/source hypotheses and sometimes derive `NP_not_subset_PpolyDAG` only after assuming a language bridge plus a weak route payload. Several historical routes are deliberately quarantined as failed/vacuous/support-bound routes. The safe conclusion is: useful kernel-checked lower-bound plumbing exists, but there is no new unconditional P-vs-NP mainline progress and many surfaces are staged, conditional, or audit-only.

## 2. Executive summary

The lower-bound formalization level is **mixed**:

- **Fixed-slice Partial-MCSP AC0 / Step-C:** kernel-checked contradiction lemmas exist against `SmallAC0Solver_Partial`, `SmallAC0Solver_Partial_Syntactic`, and `ConstructiveSmallAC0Solver_Partial`.
- **Anti-checker / local solver:** kernel-checked counting and locality contradictions exist, including a direct local-solver contradiction via `no_local_function_solves_mcsp`.
- **Formula lower-bound chain:** `LB_Formulas_Core_Partial.lean` is mostly a thin kernel-checked adapter over `AntiChecker_Partial.lean`; it exposes semantic, constructive, closed, provider, syntactic-easy, and multi-switching variants.
- **Magnification pipeline connection:** the public AC0 endpoint imports `Magnification.PipelineStatements_Partial`, and singleton/provenance/density endpoints import `Magnification.AC0AtlasBridge`. The active chain is best understood as partial-MCSP/singleton/atlas plumbing, not a completed OPS-style lower-bound-to-P-vs-NP route.
- **DAG-track:** there is extensive typed interface and theorem infrastructure for DAG stable restrictions, accepted families, promise-YES subcubes, and asymptotic slice bridges. The strongest `NP_not_subset_PpolyDAG` conclusions are conditional on explicit NP witnesses plus bridge/weak-route payloads.
- **Legacy / refuted:** old fixed-slice support-half and empty `GapSliceFamily` routes are isolated under `FailedRoute_*` files, but live files still contain support-bound and weak-route names that should be treated carefully.

## 3. Files audited

I discovered the audit scope with `find pnp3/LowerBounds -name "*.lean" -print | sort` and inspected all 24 Lean files in `pnp3/LowerBounds/`.

| File | Approximate role | Inspection level | Notes |
| --- | --- | --- | --- |
| `pnp3/LowerBounds/AC0_GapMCSP.lean` | Paper-facing wrapper for Partial-MCSP not-in-AC0 predicates/theorems | Read fully | Small adapter over final endpoint. |
| `pnp3/LowerBounds/AC0_GapMCSP_Final.lean` | Public fixed-slice AC0 endpoint | Read fully | Unconditional only relative to enriched `SmallAC0Solver_Partial` interface. |
| `pnp3/LowerBounds/AcceptedFamilyBarrier.lean` | Generic accepted-family counting contradiction | Read fully | Safe reusable finite counting theorem. |
| `pnp3/LowerBounds/AntiChecker_Partial.lean` | Main Partial-MCSP anti-checker, AC0/Step-C and local solver infrastructure | Header, structures, theorem signatures, and key proof bodies around Step-C/local endpoints inspected; searched throughout | 2,068 LOC; not line-by-line proof reconstruction. |
| `pnp3/LowerBounds/ApproxClassContradiction.lean` | Singleton `ApproxClass` packaging from source-side semantic switching | Read fully | Explicitly says no contradiction yet. |
| `pnp3/LowerBounds/ApproxClassNoGo.lean` | Formal insufficiency/no-go for `ApproxClass` alone | Read fully | Negative endpoint; useful guardrail. |
| `pnp3/LowerBounds/AsymptoticDAGBarrier.lean` | Import aggregator for DAG barrier interfaces/theorems | Read fully | No declarations beyond imports/namespaces. |
| `pnp3/LowerBounds/AsymptoticDAGBarrierInterfaces.lean` | Slice-family, locality, accepted-family, DAG implication interfaces | Read structurally and searched | Key Prop interfaces audited; no proof-heavy content. |
| `pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean` | Theorems connecting slice interfaces to no-DAG and `NP_not_subset_PpolyDAG` endpoints | Header, key endpoint signatures, hard-payload hits, and weak-route sections inspected; searched throughout | 2,252 LOC; not every proof body reconstructed. |
| `pnp3/LowerBounds/DAGStableRestrictionProducer.lean` | Large DAG stable-restriction / support / accepted-family producer layer | Header, top-level signatures, provider/source names, hard-payload hits, and suspicious noncomputable/class occurrences inspected; searched throughout | 8,154 LOC; too large for proof-by-proof audit in one worker pass. |
| `pnp3/LowerBounds/DAGUnconditionalBlocker.lean` | Small route blocker / aggregator | Read fully | Mostly imports or short wrappers. |
| `pnp3/LowerBounds/FailedRoute_EventualTableForceSlackObstruction.lean` | Failed eventual table-force route obstruction | Read fully | Audit-only impossibility facts. |
| `pnp3/LowerBounds/FailedRoute_FixedSliceSupportHalfCore.lean` | Core impossibility for fixed-slice support-half route under `PpolyDAG` membership | Read fully | Refutes historical route shape. |
| `pnp3/LowerBounds/FailedRoute_FixedSliceSupportHalfImpossible.lean` | User-facing restatements of support-half impossibility | Read fully | Audit-only. |
| `pnp3/LowerBounds/FailedRoute_GapSliceFamilyVacuous.lean` | Empty `GapSliceFamily` / vacuity proof | Read fully | Important guardrail. |
| `pnp3/LowerBounds/FailedRoutes.lean` | Aggregator for closed/deprecated route facts | Read fully | Audit-only import path. |
| `pnp3/LowerBounds/LB_Formulas.lean` | Formula/AC0 lower-bound route surface and adapters | Header, top-level theorem signatures, provider/instance/Classical occurrences, and downstream names inspected; searched throughout | 2,346 LOC; proof bodies not fully reconstructed. |
| `pnp3/LowerBounds/LB_Formulas_Core_Partial.lean` | Core Partial-MCSP formula/AC0 LB adapter | Read fully | Feasible full audit completed. |
| `pnp3/LowerBounds/MCSPGapLocality.lean` | Locality contradiction for Partial-MCSP promise | Header, top-level statements, proof outline, and hidden-payload search inspected | 564 LOC; key local theorem inspected. |
| `pnp3/LowerBounds/RouteBSourceClosure.lean` | Route-B source closure interfaces and adapters | Read fully | Contains route-source abbreviations and bridge to stable restriction. |
| `pnp3/LowerBounds/RouteNextStep_AcceptedFamily.lean` | Next-step accepted-family route to `NP_not_subset_PpolyDAG` | Read fully | Conditional on weak route + bridge + NP witness. |
| `pnp3/LowerBounds/SingletonDensityContradiction.lean` | Large singleton density / targeted payload / support-bound contradiction layer | Header, key payloads, endpoint signatures, refuted-route names, and hard-payload hits inspected; searched throughout | 2,803 LOC; not every proof body reconstructed. |
| `pnp3/LowerBounds/SingletonDensityEndpoint.lean` | Singleton density package and mismatch-testset endpoint | Read fully | Stops before contradiction except conditional old endpoint/no-go. |
| `pnp3/LowerBounds/SingletonProvenanceEndpoint.lean` | Singleton provenance package from internal provider | Read fully | Safe packaging; uses `Classical.choose hFormula` for formula witness extraction. |

Optional/context files inspected or searched: `RESEARCH_CONSTITUTION.md`, `seed_packs/phase1_20engineer_parallel_dispatch/README.md`, `seed_packs/phase1_20engineer_parallel_dispatch/COMMON_WORKER_INSTRUCTIONS.md`, `seed_packs/phase1_20engineer_parallel_dispatch/tasks/A05_audit_pnp3_lowerbounds.md`, `pnp3/Magnification/PipelineStatements_Partial.lean`, `pnp3/Magnification/Facts_Magnification_Partial.lean`, and `pnp3/Magnification/AC0AtlasBridge.lean` by targeted searches / focused downstream inspection.

## 4. Top-level theorem / structure inventory

This is an inventory of important declarations, not a full list of all 897 top-level declarations found by `rg`.

| Declaration | File | Type/signature summary | Classification | Hard-payload dependency |
| --- | --- | --- | --- | --- |
| `SmallAC0ParamsPartial` | `AntiChecker_Partial.lean` | AC0 parameters aligned to `partialInputLen p` with a union-bound smallness condition. | canonical interface | No `ResearchGapWitness`; no `NP_not_subset_PpolyDAG`. |
| `AC0EasyFamilyDataPartial` | `AntiChecker_Partial.lean` | Packages a family, AC0 witness, and lower bound `2^(2^n) ≤ |F|`. | staged Prop / potential wrapper risk | No hard final payload, but its `card_lower` is the decisive counting payload. |
| `SmallAC0Solver_Partial` | `AntiChecker_Partial.lean` | Solver for `GapPartialMCSPPromise p` with semantic decider, correctness, AC0 circuit equality, and `easyData`. | suspicious / needs review | No final payload, but embeds the hard Step-C data inside the solver. |
| `ConstructiveSmallAC0Solver_Partial` | `AntiChecker_Partial.lean` | Thin extension of `SmallAC0Solver_Partial`. | wrapper | Inherits embedded `easyData`. |
| `SmallAC0Solver_Partial_Syntactic` | `AntiChecker_Partial.lean` | Thin syntactic wrapper over `SmallAC0Solver_Partial`. | wrapper | Inherits embedded `easyData`. |
| `SmallLocalCircuitSolver_Partial` | `AntiChecker_Partial.lean` | Solver interface with local-dependence field. | canonical/conditional | No final payload; depends on locality certificate field. |
| `noSmallAC0Solver_partial_of_family_card` | `AntiChecker_Partial.lean` | Counting contradiction from AC0 witness plus family cardinality lower bound. | canonical conditional theorem | No final payload; requires large-family premise. |
| `AC0EasyFamily` | `AntiChecker_Partial.lean` | Noncomputable syntactic easy-family definition. | interface | No final payload; uses finite enumeration. |
| `EasyFamilyAC0MultiSwitchingWitness` | `AntiChecker_Partial.lean` | Typeclass carrying a multi-switching witness for `AC0EasyFamily`. | hidden-payload risk if globally instantiated | No final payload, but instance search can supply a hard witness. |
| `AC0CompressionHypothesis` | `AntiChecker_Partial.lean` | For each solver, `AC0EasyFamily` has all-functions cardinality. | staged Prop / mathematical gap | No final payload; this is a hard compression/magnification-style assumption. |
| `StepCClosureDataPartial` | `AntiChecker_Partial.lean` | For every solver, builds `AC0EasyFamilyDataPartial`. | staged interface / wrapper risk | No final payload; can hide Step-C payload. |
| `StepCSyntacticLiftDataPartial` | `AntiChecker_Partial.lean` | Lifts semantic solvers to syntactic wrappers with equality. | harmless after current solver enrichment | Because solver already stores the payload, this is now tautological. |
| `StepCClosureDataPartialProvider` | `AntiChecker_Partial.lean` | Solver-local provider of family, subset `Y`, and strict capacity gap. | hidden-payload risk | No final payload; provider fields are strong enough to close contradiction. |
| `noSmallAC0Solver_partial_closed_internalized` | `AntiChecker_Partial.lean` | Refutes any `SmallAC0Solver_Partial p`. | kernel-checked but interface-relative | Depends on `SmallAC0Solver_Partial.easyData` via default syntactic lift. |
| `noSmallLocalCircuitSolver_partial_v2` | `AntiChecker_Partial.lean` | Refutes `SmallLocalCircuitSolver_Partial p` using locality + MCSP gap. | canonical conditional theorem | No final payload; depends on `decideLocal` field. |
| `LB_Formulas_core_partial_*` family | `LB_Formulas_Core_Partial.lean` | Thin adapters from Step-C/easy-family/closure/syntactic/multi-switching inputs to `False`. | conditional / wrapper | No final payload; inherits Step-C payload assumptions or embedded solver payload. |
| `GapPartialMCSP_NotInSmallAC0` | `AC0_GapMCSP_Final.lean` | `¬ ∃ SmallAC0Solver_Partial p, True`. | interface-relative endpoint | No final payload. |
| `gapPartialMCSP_noSmallAC0Solver` | `AC0_GapMCSP_Final.lean` | Pointwise refutation of `SmallAC0Solver_Partial p`. | kernel-checked endpoint, not external AC0 LB | Uses internalized solver payload. |
| `GapPartialMCSP_not_in_AC0` | `AC0_GapMCSP.lean` | Paper-facing negation of `GapPartialMCSP_in_AC0`. | wrapper endpoint | Same as above. |
| `AcceptedFamilyCertificate` | `AcceptedFamilyBarrier.lean` | Finite family larger than circuit-count bound accepted by `f`. | safe interface | No final payload. |
| `no_function_solves_mcsp_of_acceptedFamilyCertificate` | `AcceptedFamilyBarrier.lean` | Accepted-family certificate contradicts promise correctness. | canonical counting theorem | No final payload. |
| `GapSliceFamily` | `AsymptoticDAGBarrierInterfaces.lean` | Historical all-length slice-family carrier. | legacy/refuted carrier | Later proved empty. |
| `GapSliceFamilyEventually` | `AsymptoticDAGBarrierInterfaces.lean` | Eventual/asymptotic slice-family carrier. | staged interface | No final payload by itself. |
| `SmallDAGImplies*` interfaces | `AsymptoticDAGBarrierInterfaces.lean` | Prop statements for DAG-to-locality/value/subcube/accepted-family consequences. | staged Prop | No final payload by themselves. |
| `NP_not_subset_PpolyDAG_of_*WeakRoute*` | `AsymptoticDAGBarrierTheorems.lean` | Derive `NP_not_subset_PpolyDAG` from slice weak-route payloads plus bridge and NP witness. | conditional mainline-shaped wrappers | Conclusion is hard payload; hypotheses contain bridge/route assumptions. |
| `DAGStableRestrictionCertificate` and providers | `DAGStableRestrictionProducer.lean` | Certificate/provider chain toward stable restriction and DAG route blockers. | staged/conditional | Some endpoints conclude `NP_not_subset_PpolyDAG` with TM/bridge hypotheses. |
| `Abstract*SingletonDensityPayload` | `SingletonDensityContradiction.lean` | Abstract singleton/density/targeted payload structures. | staged; some deliberately insufficient | No final payload except downstream conditional endpoints. |
| `RefutedRoute_NP_not_subset_PpolyDAG_of_supportBounds` | `SingletonDensityContradiction.lean` | Support-bound route restatement to `NP_not_subset_PpolyDAG`. | refuted/audit-only | Concludes hard payload via route already marked refuted. |
| `gapSliceFamily_isEmpty` | `FailedRoute_GapSliceFamilyVacuous.lean` | Proves historical `GapSliceFamily` is empty. | refuted/vacuous guardrail | No final payload. |
| `not_gapPartialMCSP_supportHalfObligation_of_inPpolyDAG` | `FailedRoute_FixedSliceSupportHalfImpossible.lean` | Support-half blocker impossible under fixed-slice `PpolyDAG`. | failed-route guardrail | Mentions `PpolyDAG` membership; no final payload. |

## 5. Kernel-checked content

The following content is actually proven by Lean in the current tree (as confirmed by `./scripts/check.sh` passing):

1. **Counting contradiction for oversized AC0-easy family.** `noSmallAC0Solver_partial_of_family_card` proves `False` from a concrete `SmallAC0Solver_Partial p`, an AC0 witness for a family `F`, and `2^(2^n) ≤ F.toFinset.card`. The proof constructs a scenario from the AC0 witness, uses union/capacity bounds, and derives `2^N ≤ capacity < 2^N`.
2. **Packaged easy-family contradiction.** `noSmallAC0Solver_partial_of_easyFamilyData` proves `False` from a solver plus `AC0EasyFamilyDataPartial solver.params.ac0`.
3. **Constructive and closed Step-C contradictions.** `noConstructiveSmallAC0Solver_partial`, `noSmallAC0Solver_partial_closed`, `noSmallAC0Solver_partial_closed_noExists`, and their `LB_Formulas_core_partial_*` wrappers prove contradiction once the solver or closure data supplies the easy-family payload.
4. **Current internalized no-small-AC0 endpoint.** `noSmallAC0Solver_partial_closed_internalized`, `LB_Formulas_core_partial_closed_internalized`, `gapPartialMCSP_noSmallAC0Solver`, and `gapPartialMCSP_notInSmallAC0` prove no object of type `SmallAC0Solver_Partial p` exists. This is kernel-checked, but the type itself includes AC0 circuit and `easyData` fields.
5. **Local-solver contradiction.** `noSmallLocalCircuitSolver_partial_v2` proves that a `SmallLocalCircuitSolver_Partial p` cannot solve the partial-MCSP promise if it depends on at most `tableLen/2` coordinates. This relies on `MCSPGapLocality.no_local_function_solves_mcsp`.
6. **Accepted-family contradiction.** `no_function_solves_mcsp_of_acceptedFamilyCertificate` proves any promise solver accepting a family larger than the count of small circuits is impossible.
7. **ApproxClass insufficiency.** `ApproxClassNoGo.lean` proves counterexamples showing `ApproxClass` membership alone does not imply small mismatch-cardinality. This is negative kernel-checked content.
8. **Vacuity/failed-route guardrails.** `gapSliceFamily_isEmpty`, `not_nonempty_gapSliceFamily`, and support-half impossibility lemmas are kernel-checked and quarantine historical routes.
9. **Conditional DAG endpoints.** Several theorems in `AsymptoticDAGBarrierTheorems.lean`, `DAGStableRestrictionProducer.lean`, `RouteNextStep_AcceptedFamily.lean`, and `SingletonDensityContradiction.lean` prove `NP_not_subset_PpolyDAG` from explicit bridge/source/weak-route hypotheses. These are kernel-checked implications, not closed hard-payload constructions.

## 6. Staged / placeholder / Prop-only content

Important staged content:

- `AC0EasyFamilyDataPartial`: honest staging of family-level AC0 evidence and the decisive large-cardinality lower bound. Risk: if bundled into a solver interface, downstream no-solver theorems look stronger than they are.
- `SmallAC0Solver_Partial`: potential wrapper risk because the solver includes `easyData`. A future reader may interpret `¬ ∃ SmallAC0Solver_Partial p` as a standard AC0 lower bound, but the type excludes solvers that do not already carry the counting payload.
- `AC0CompressionHypothesis`: honest mathematical staging; the hypothesis is exactly the hard cardinality/compression-style bridge, not proven from a bare solver.
- `StepCClosureDataPartial`: honest interface if treated as a required payload; wrapper risk if described as an implementation detail.
- `StepCClosureDataPartialProvider`: provider-class staging; dangerous only if instances are introduced silently.
- `SmallDAGImpliesCoordinateLocalityAt`, `SmallDAGImpliesPromiseValueLocalityAt`, `SmallDAGImpliesPromiseYesSubcubeAt`, `SmallDAGImpliesAcceptedFamilyAt`: typed Prop interfaces for future DAG route obligations.
- `DAGStableRestriction*`, `SmallDAGWitness*`, `*ProviderOnSlices`, and `*Source*` structures/defs in `DAGStableRestrictionProducer.lean`: mostly conditional adapters and packaged obligations. They are useful but should not be counted as proving the source obligations unless a concrete provider is supplied without circular assumptions.
- `AbstractSingletonDensityPayload`, `AbstractLinkedSingletonDensityPayload`, `AbstractTargetedSingletonDensityPayload`, `AbstractGapTargetedSingletonDensityPayload`: staged payloads; the file itself documents that weaker versions are insufficient or can be trivialized.
- `SemanticSwitchingSingletonProvenancePackagePartial` and `SemanticSwitchingSingletonDensityPackagePartial`: endpoint-facing package objects from the current internal formula route; safe as provenance/density interfaces, not contradiction endpoints.

I did not find Lean `axiom`, `opaque`, `sorry`, or `admit` introduced in the audited directory. The main risk is not explicit axiomatization; it is strong data hidden inside structures/classes and then consumed by short wrapper theorems.

## 7. Refuted / vacuous / legacy route check

Required search command summary:

- Hard-payload search over `pnp3/LowerBounds`: 73 matches across 7 files.
- Legacy/refuted/placeholder search over `pnp3/LowerBounds`: 174 matches across 9 files.
- Hidden-payload search over `pnp3/LowerBounds`: 179 matches across 12 files.

Findings:

1. **`GapSliceFamily` is formally vacuous.** `FailedRoute_GapSliceFamilyVacuous.lean` proves `IsEmpty GapSliceFamily`, `¬ Nonempty GapSliceFamily`, and a universal-vacuity helper. Any theorem over the old non-eventual `GapSliceFamily` carrier should be treated as vacuous unless migrated to `GapSliceFamilyEventually` or another nonempty carrier.
2. **Fixed-slice support-half route is closed/historical.** `FailedRoute_FixedSliceSupportHalfCore.lean` and `FailedRoute_FixedSliceSupportHalfImpossible.lean` prove support-half/source blockers are incompatible with fixed-slice `PpolyDAG` membership. They are audit guardrails, not active route progress.
3. **Eventual table-force plus slice-constant route is obstructed.** `FailedRoute_EventualTableForceSlackObstruction.lean` records a failed table-force route under slice-const assumptions.
4. **`RefutedRoute_NP_not_subset_PpolyDAG_of_supportBounds` exists.** This is explicitly named as a refuted/support-bounds route in `SingletonDensityContradiction.lean`. It should remain audit-only and should not be used by candidate/final endpoints.
5. **`_Partial` is pervasive and mostly descriptive.** In the active AC0/Partial-MCSP files `_Partial` usually identifies the fixed-slice Partial-MCSP track, not a proof placeholder. In historical contexts it also signals older partial-route migration.
6. **`TODO` occurrences remain in `AntiChecker_Partial.lean`.** The visible TODO says the Step-C interfaces are internalized and future work is optional refactoring/API simplification. This is not a missing proof marker, but it is doc drift risk because the endpoint still relies on enriched solver fields.
7. **Weak-route names occur in DAG/asymptotic files.** These are conditional bridge theorems, not closed route success. They should be kept separate from mainline claims unless paired with real `VerifiedNPDAGLowerBoundSource`/`PpolyDAG` bridge work.

## 8. Hidden payload / Rule 16 check

Pattern search looked for `class`, `instance`, `default_instance`, `attribute [instance]`, `Fact`, `opaque`, `Classical.choose`, and `noncomputable def`.

| Occurrence family | Files | Classification | Interpretation |
| --- | --- | --- | --- |
| `EasyFamilyAC0MultiSwitchingWitness` class and `easyFamily_multiSwitchingProvider` instance | `AntiChecker_Partial.lean` | hidden-payload risk | If global instances are added, theorem statements with typeclass arguments may silently consume hard multi-switching/easy-family payloads. |
| `StepCClosureDataPartialProvider` class | `AntiChecker_Partial.lean` | hidden-payload risk | Provider fields include enough data to prove contradiction; safe only if no default/global payload instances are introduced. |
| `stepCSyntacticLiftDataPartial_default` and `stepCClosureData_of_syntacticLift` | `AntiChecker_Partial.lean` | suspicious but explainable | Because `SmallAC0Solver_Partial` already stores `easyData`, the default lift/closure becomes trivial. This is a wrapper risk rather than a hidden theorem. |
| `Classical.choose hFormula` | `ApproxClassContradiction.lean`, `SingletonProvenanceEndpoint.lean`, `SingletonDensityEndpoint.lean`, `SingletonDensityContradiction.lean` | harmless standard witness extraction if kept local | Extracts the `InPpolyFormula` witness from `PpolyFormula`; not a final hard payload by itself. |
| Numerous `noncomputable def ...Provider...Source...` in `DAGStableRestrictionProducer.lean` | `DAGStableRestrictionProducer.lean` | needs review / possible hidden-payload risk | Most are adapters from explicit hypotheses. Because names include Provider/Source and file is 8k LOC, future candidate work should audit any endpoint dependency closure before reuse. |
| `Classical.choose` in DAG producer around existence packages | `DAGStableRestrictionProducer.lean` | standard extraction or needs review depending on source | Many appear to unpack explicit existential hypotheses; not automatically forbidden, but each candidate endpoint should check whether the chosen object came from an honest theorem or a staged provider. |
| `opaque` | audited directory | none found | No opaque payload in this directory. |
| `default_instance` / `attribute [instance]` | audited directory | none found by required pattern | Lower risk of silent default payloads in the audited files. |

Rule-16-style conclusion: no obvious forbidden global final payload was found, but `SmallAC0Solver_Partial.easyData`, `StepCClosureDataPartialProvider`, and provider/source-heavy DAG adapters are the places where hard work can be hidden under innocuous theorem names.

## 9. Barrier relevance

| Barrier / theme | Status in audited area | Content type |
| --- | --- | --- |
| Natural proofs | Indirectly relevant through AC0/easy-family/cardinality arguments; no full Razborov-Rudich barrier theorem in this directory. | Typed infrastructure / markdown comments. |
| Relativization | Not materially touched in `pnp3/LowerBounds/`; separate `Barrier` directory handles it. | Nothing significant here. |
| Algebrization | Not materially touched here. | Nothing significant here. |
| Locality | Central in `MCSPGapLocality.lean`, `AntiChecker_Partial.lean`, and DAG producer layers. | Actual theorems plus typed interfaces. |
| Hardwiring | Relevant in fixed-slice/DAG support discussions and support-half failed route. | Actual guardrail theorems and staged interfaces. |
| Support-cardinality-only | Explicitly appears as a failed/refuted route theme. | Audit-only/failed-route plus conditional adapters. |
| Syntax-only filters | Present in `AC0EasyFamily`, syntactic easy-function families, and formula/AC0 package routes. | Typed interface and kernel-checked finite definitions. |
| Normalization filters | Not a major theme in this directory. | Mostly nothing. |
| Search-to-decision | Not directly solved here; no `SearchMCSPWeakLowerBound` endpoint in this directory. | Nothing mainline. |
| MCSP / magnification | Central: Partial-MCSP, AC0/Step-C, singleton density, DAG asymptotic route. | Actual fixed-slice theorems plus many staged/conditional route interfaces. |

## 10. Anti-checker theorem map

The active anti-checker content is concentrated in `AntiChecker_Partial.lean` and `MCSPGapLocality.lean`.

### AC0 / Step-C side

- `SmallAC0Solver_Partial p` is not a bare AC0 circuit family. It includes:
  - semantic decider and witness;
  - promise correctness;
  - an AC0 circuit and extensional equality to the decision function;
  - `easyData : AC0EasyFamilyDataPartial params.ac0`.
- `noSmallAC0Solver_partial_of_family_card` proves contradiction from:
  - a concrete solver;
  - a family `F` with AC0 witness;
  - a cardinal lower bound `2^(2^n) ≤ |F|`.
- `noSmallAC0Solver_partial_of_easyFamilyData` packages the previous theorem through `AC0EasyFamilyDataPartial`.
- `noSmallAC0Solver_partial_closed_internalized` proves contradiction for every `SmallAC0Solver_Partial p` because the solver already contains `easyData` and default syntactic-lift closure retrieves it.
- Public endpoints in `AC0_GapMCSP_Final.lean` and `AC0_GapMCSP.lean` expose this as no structured small-AC0 solver / not-in-AC0 for the current internal interface.

**Threshold:** the counting contradiction uses all-functions-scale lower bound `2^(2^n) ≤ family.card` and the union/capacity target `unionBound bound bound ≤ 2^(2^n / (n+2))` from `SmallAC0ParamsPartial`. This is much stronger than a typical small AC0 solver premise and is currently embedded in the solver/easy-data route.

### Local-circuit side

- `SmallLocalCircuitSolver_Partial p` includes `decideLocal`, a certificate that the solver depends on at most `Partial.tableLen p.n / 2` input coordinates.
- `MCSPGapLocality.no_local_function_solves_mcsp` establishes that no such local function can solve the partial-MCSP promise: one can build YES and NO instances agreeing on the alive coordinates.
- `noSmallLocalCircuitSolver_partial_v2` extracts the locality field and applies the locality theorem.

**Threshold:** locality at `≤ tableLen / 2` live coordinates. This is a genuine fixed-slice promise contradiction once the locality certificate is supplied.

### Anti-checker compatibility/testset side

- `antiChecker_exists_large_Y_partial_*` and local variants construct or package large `Y` witnesses under easy-family / local-circuit witness hypotheses.
- `antiChecker_testset_incompatibility_local_partial*` proves contradiction from `Y`, a test set `T`, approximation on `T`, and a strict capacity inequality.
- These are useful adapters, but they should not be mistaken for a complete external lower bound without the explicit witness/large-family premises.

## 11. Formula LB chain

`LB_Formulas_Core_Partial.lean` is a thin, readable adapter layer over the anti-checker/Step-C machinery:

1. `StepCCoreSemanticHypothesisPartial p` defines the semantic core hypothesis: every solver plus easy-family package is impossible.
2. `LB_Formulas_core_partial_semantic` is direct elimination from that hypothesis.
3. `LB_Formulas_core_partial_of_easyFamilyData` delegates to `noSmallAC0Solver_partial_of_easyFamilyData`.
4. `LB_Formulas_core_partial_constructive` delegates to `noConstructiveSmallAC0Solver_partial`.
5. `LB_Formulas_core_partial_closed`, `*_fully_closed`, `*_of_syntacticLift`, `*_closed_of_provider`, and `*_closed_internalized` are wrappers for the corresponding `AntiChecker_Partial` closure/provider/internalized endpoints.
6. `LB_Formulas_core_partial`, `*_of_multiSwitching`, `*_of_multiSwitching_provider`, and `*_of_default_multiSwitching` expose older/direct hypothesis styles: AC0 witness plus `AC0CompressionHypothesis`, or multi-switching plus compression.

Downstream:

- `AC0_GapMCSP_Final.lean` imports `Magnification.PipelineStatements_Partial` and calls `LB_Formulas_core_partial_closed_internalized` to publish no structured small-AC0 solver.
- `AC0_GapMCSP.lean` wraps the final endpoint in paper-facing names.
- Singleton provenance/density files import `Magnification.AC0AtlasBridge` and expose source-produced singleton/density packages for future contradiction attempts.
- `pnp3/Magnification/Facts_Magnification_Partial.lean` exists and imports `LowerBounds.AntiChecker_Partial` plus `Magnification.PipelineStatements_Partial`. Its OPS-trigger theorems consume a `StructuredLocalityProviderPartial`/semantic counterpart that turns a formula hypothesis plus `PpolyFormula (gapPartialMCSP_Language p)` into `RestrictionLocalityPartial p`; they then use `noSmallLocalCircuitSolver_partial_v2` to derive formula/real noncontainment consequences under explicit `NP_strict` and embedding/provider hypotheses. This is a conditional trigger layer, not a closed OPS theorem from `LB_Formulas_Core_Partial` alone.
- `AC0AtlasBridge.lean` is the downstream path for singleton/provenance/density source packages used by `SingletonProvenanceEndpoint.lean` and `SingletonDensityEndpoint.lean`.

Conclusion: the formula LB chain feeds the Partial-MCSP AC0 endpoint and singleton/atlas route infrastructure, but it does not presently produce a full MCSP, AC0[p], or DAG-track lower bound without staged bridge assumptions.

## 12. Reuse map

Safe to reuse:

- `AcceptedFamilyCertificate` and `no_function_solves_mcsp_of_acceptedFamilyCertificate` for finite accepted-family contradictions.
- `MCSPGapLocality.no_local_function_solves_mcsp` and `noSmallLocalCircuitSolver_partial_v2` when a genuine locality certificate is available.
- `noSmallAC0Solver_partial_of_family_card` if future work can honestly supply an AC0-realizable family and the all-functions-scale cardinal lower bound.
- `AC0EasyFamilyDataPartial` as an explicit obligation type, if kept visible in theorem statements.
- `LB_Formulas_core_partial_of_easyFamilyData` / `LB_Formulas_core_partial_of_syntacticEasy` as adapters when their hypotheses are not hidden.
- `ApproxClassNoGo` negative theorems as guardrails against reviving insufficient singleton `ApproxClass` routes.
- `FailedRoute_*` modules as audit-only guardrails.
- `GapSliceFamilyEventually` and `AsymptoticDAGSliceBridgeAt` rather than old `GapSliceFamily` for any asymptotic DAG work.

Avoid or treat as read-only unless doing governance cleanup:

- Do not use `GapSliceFamily` route endpoints as evidence; the carrier is empty.
- Do not promote `RefutedRoute_NP_not_subset_PpolyDAG_of_supportBounds` or support-half route names into active endpoints.
- Do not advertise `gapPartialMCSP_not_in_AC0` as a standard external AC0 lower bound without explaining the enriched solver interface.
- Do not add global instances for `EasyFamilyAC0MultiSwitchingWitness`, `StepCClosureDataPartialProvider`, or DAG provider classes unless the PR is explicitly audited for hidden payload.
- Do not use provider/source-heavy DAG endpoints in candidate final chains without a dependency-closure audit.

## 13. Gap map

### A. Engineering gap

- The public AC0 endpoint names are stronger-sounding than their actual interface-relative content. A documentation/API cleanup could rename or annotate them to emphasize `SmallAC0Solver_Partial` is enriched.
- There is no compact dependency-closure map for the DAG provider/source endpoints in `DAGStableRestrictionProducer.lean`.
- The downstream `Facts_Magnification_Partial.lean` trigger layer exists, but the A05 task scope is `pnp3/LowerBounds/`; a separate pipeline audit should map how its provider hypotheses relate to `LB_Formulas_Core_Partial` and `PipelineStatements_Partial.lean`.
- Several route names mix active, weak, and historical terminology; a route registry could prevent accidental imports from audit-only modules.

### B. Formalization gap

- A bare external AC0 solver interface, without embedded `easyData`, is not refuted by the current internalized endpoint. The formal gap is an honest bridge from ordinary AC0 solver data to `AC0EasyFamilyDataPartial` or to the locality route.
- The DAG/asymptotic route still requires explicit bridge/source/weak-route payloads to derive `NP_not_subset_PpolyDAG`.
- Singleton density/provenance packages stop before a contradiction except through additional targeted/locality/stable-restriction assumptions.
- Provider/source classes need theorem-surface audits if they are to be reused by candidate endpoints.

### C. Mathematical gap

- Proving the hard `AC0CompressionHypothesis` or all-functions-scale cardinal lower bound from a bare small AC0 Partial-MCSP solver would be a real mathematical step and should not be assigned as routine engineering.
- Bridging restricted Partial-MCSP fixed-slice lower bounds to full MCSP or to `VerifiedNPDAGLowerBoundSource` remains open in this directory.
- Producing an honest `NP_not_subset_PpolyDAG` source requires more than support-cardinality/locality staging; it needs a non-vacuous bridge from small DAG witnesses to a contradiction on an NP language.
- Search-to-decision / `SearchMCSPWeakLowerBound` is not reduced here.

### D. Governance gap

- Audit-only/refuted names are mostly isolated, but live files still contain `supportBounds`, `WeakRoute`, and `NP_not_subset_PpolyDAG` endpoints. Future PR descriptions must distinguish conditional wrappers from source-obligation progress.
- The final/paper-facing AC0 names risk overclaiming because they hide the enriched solver interface behind `in_AC0` wording.
- `DAGStableRestrictionProducer.lean` is too large and provider-heavy for casual reuse; it needs a dedicated dependency-closure/no-hidden-payload audit before candidate import.

## 14. Recommended Phase 1+ tasks

### Task 1: Rename/document interface-relative AC0 endpoint

- **Title:** Clarify `GapPartialMCSP_not_in_AC0` as structured-solver exclusion.
- **Exact files to touch:** `pnp3/LowerBounds/AC0_GapMCSP.lean`, `pnp3/LowerBounds/AC0_GapMCSP_Final.lean`, relevant docs/tests only if already present.
- **Allowed scope:** Markdown/doc-comments and optionally theorem alias names that preserve old API.
- **Forbidden scope:** No proof strengthening, no solver interface changes, no `ResearchGapWitness`, no `NP_not_subset_PpolyDAG` endpoint.
- **Expected output:** Clear comments or aliases saying the theorem excludes `SmallAC0Solver_Partial`, whose type carries syntactic/easy-data payload.
- **Estimated time:** 0.5-1 day.
- **Dependency on other audits:** None.
- **Risk level:** Low.
- **Type:** Lean doc/API hygiene, not mathematical progress.

### Task 2: Dedicated hidden-payload audit for `DAGStableRestrictionProducer.lean`

- **Title:** Dependency-closure and provider audit for DAG stable-restriction producer.
- **Exact files to touch:** Markdown report under audit reports only; optionally no source files.
- **Allowed scope:** Read and map provider/source/class/noncomputable definitions and endpoints in `pnp3/LowerBounds/DAGStableRestrictionProducer.lean`.
- **Forbidden scope:** No Lean edits, no provider promotion, no endpoint changes.
- **Expected output:** Table of every provider/source endpoint, whether it consumes explicit hypotheses or hides payload through typeclass/choice.
- **Estimated time:** 2-3 days.
- **Dependency on other audits:** Should cross-check any A09 NoGoLog / route-governance audit if available.
- **Risk level:** Medium due to file size.
- **Type:** Markdown-only audit.

### Task 3: Bare-solver interface separation plan

- **Title:** Separate bare AC0 solver from enriched Step-C solver.
- **Exact files to touch:** Initially markdown design note; later possible Lean files `AntiChecker_Partial.lean`, `LB_Formulas_Core_Partial.lean`, and endpoint wrappers.
- **Allowed scope:** Phase 1 design should only propose names and dependency boundaries; later implementation may add a bare solver structure and adapters.
- **Forbidden scope:** Do not claim a theorem refuting bare solvers unless the bridge to `easyData` is proved; do not delete existing enriched endpoints.
- **Expected output:** A design that makes theorem statements reveal whether they assume only correctness/circuit data or also easy-family/cardinality payload.
- **Estimated time:** 1 day for design; 2-4 days for a later implementation PR.
- **Dependency on other audits:** Depends on route-governance approval because it may touch public API.
- **Risk level:** Medium.
- **Type:** Operator decision + possible Lean infrastructure.

### Task 4: Route registry/quarantine check for failed and weak DAG routes

- **Title:** Ensure failed/support-bound/weak-route endpoints cannot be imported as final progress.
- **Exact files to touch:** Governance docs/tests or audit registry; possible import lint if existing infrastructure supports it.
- **Allowed scope:** Add markdown registry entries or tests that flag `RefutedRoute_*`, `FailedRoute_*`, old `GapSliceFamily`, and support-bound endpoints.
- **Forbidden scope:** Do not move trust-root files; do not change mathematical theorem statements.
- **Expected output:** Machine- or doc-checkable map of audit-only route surfaces.
- **Estimated time:** 1-2 days.
- **Dependency on other audits:** Should coordinate with NoGoLog/governance audit.
- **Risk level:** Low to medium.
- **Type:** Governance / tests.

## 15. Stop / hold recommendations

- **Hold any task that treats `gapPartialMCSP_not_in_AC0` as an external AC0 lower bound** until the enriched solver interface is explicitly acknowledged.
- **Cancel or downgrade tasks based on old `GapSliceFamily`**; the carrier is formally empty and route statements are vacuous.
- **Hold any support-half / `supportBounds` route promotion** unless it is explicitly audit-only or proves a new non-vacuous bridge avoiding the closed fixed-slice route.
- **Hold any candidate endpoint importing `DAGStableRestrictionProducer.lean` provider/source endpoints** until a dependency-closure audit verifies no hidden hard payload.
- **Do not dispatch Phase 2/3/4/5 implementation from this audit alone.** The concrete follow-ups above are Phase 1 governance/API/audit tasks, not source-obligation reductions.

## 16. Honest caveats

- I did not reconstruct every proof body in `AntiChecker_Partial.lean`; I inspected the header, all major interfaces, and the key Step-C/local theorem regions.
- I did not reconstruct every proof body in `LB_Formulas.lean`, `AsymptoticDAGBarrierTheorems.lean`, `DAGStableRestrictionProducer.lean`, or `SingletonDensityContradiction.lean`; I audited top-level signatures, hard-payload mentions, provider/source patterns, and important endpoint regions.
- I verified that `./scripts/check.sh` passed, but I did not run `#print axioms` manually for each theorem surface.
- I did not reconstruct the full import graph; downstream claims are based on imports and targeted `rg` searches.
- I did not inspect every file under `pnp3/Magnification/`; I performed focused downstream inspection of `Facts_Magnification_Partial.lean` and targeted searches for the Partial-MCSP pipeline question.
- I did not verify mathematical adequacy of the SAL/Covering-Power estimates beyond confirming the Lean theorem dependencies and hypotheses.

## 17. Commands run

- `find .. -name AGENTS.md -print` — found repository instructions.
- `cat AGENTS.md` — read repository rules.
- `git status --short --branch && git rev-parse HEAD` — recorded starting state.
- `sed -n '1,220p' RESEARCH_CONSTITUTION.md` — read required constitution excerpt.
- `sed -n '1,220p' seed_packs/phase1_20engineer_parallel_dispatch/README.md` — read required README excerpt.
- `sed -n '1,260p' seed_packs/phase1_20engineer_parallel_dispatch/COMMON_WORKER_INSTRUCTIONS.md` — read common worker instructions excerpt.
- `cat seed_packs/phase1_20engineer_parallel_dispatch/tasks/A05_audit_pnp3_lowerbounds.md` — read exact task file.
- `find pnp3/LowerBounds -name "*.lean" -print | sort` — discovered all 24 Lean files in scope.
- `wc -l $(find pnp3/LowerBounds -name "*.lean" -print | sort)` — measured 19,991 LOC total.
- `rg -n "^(theorem|lemma|def|structure|class|axiom|opaque|inductive|abbrev|instance|noncomputable def)\b" pnp3/LowerBounds` — found 897 top-level declarations.
- `rg -n "ResearchGapWitness|NP_not_subset_PpolyDAG|VerifiedNPDAGLowerBoundSource|SearchMCSPMagnificationContract|SourceTheorem|gap_from" pnp3/LowerBounds` — found 73 hard-payload-related matches across 7 files.
- `rg -n "RefutedRoute|Vacuous|supportBounds|MagnificationAssumptions|FinalPayloadProvider|via_ex_falso|weakRoute|Legacy|_Partial|TODO|placeholder" pnp3/LowerBounds` — found 174 legacy/refuted/placeholder-pattern matches across 9 files.
- `rg -n "\bclass\b|\binstance\b|default_instance|attribute \[instance\]|\bFact\b|\bopaque\b|Classical\.choose|noncomputable def" pnp3/LowerBounds` — found 179 hidden-payload-pattern matches across 12 files.
- `rg -n "LB_Formulas_core_partial|gapPartialMCSP|SmallAC0Solver_Partial|Partial" pnp3/Magnification pnp3/LowerBounds` — targeted downstream search for Partial-MCSP pipeline usage.
- `sed -n '1,260p' pnp3/Magnification/Facts_Magnification_Partial.lean` — focused downstream inspection of the OPS trigger file.
- `./scripts/check.sh` — passed all 17 checks.

## 18. Scope compliance

- Created exactly one markdown audit report: `seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A05_pnp3_lowerbounds_codex.md`.
- Did not write Lean code.
- Did not modify source files, lakefile, specs, JSONL, NoGoLog, trust-root files, or endpoint files.
- Did not construct `ResearchGapWitness`, `VerifiedNPDAGLowerBoundSource`, `NP_not_subset_PpolyDAG`, or `P_ne_NP`.
