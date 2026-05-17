# A10 audit report: `_Partial` / `_Legacy` / TODO / placeholder markers
Task ID: A10  
Engineer handle: codex  
Branch: khanukov/phase1-A10-codex  
Scope: markdown-only Phase 0 audit; no Lean/source/spec/JSONL edits.
## 1. Executive verdict

**PARTIAL_BUT_USEFUL.** This audit completed the requested repository-wide marker searches across `pnp3` and `pnp4` and found a clear separation between kernel-checked infrastructure and legacy/refuted/staged surfaces. The marker inventory is comprehensive for the requested regexes, but I did not reconstruct every import dependency or re-prove mathematical adequacy of every theorem body. The main concerning hot spots are the legacy/refuted magnification support-bounds cone, the `VacuousFinalPayloadProvider` typeclass channel that is already quarantined by guard scripts, and one active `True -- placeholder` definition in `pnp3/Core/PDT.lean`. I found no Lean `axiom` declarations in active `pnp3`/`pnp4` code, and `./scripts/check.sh` passed.
## Executive summary
- `_Partial|_Legacy` search hits in Lean files: **34 files** contain the markers, mostly through imports/references. Actual path names ending in `_Partial.lean`: **8**. Actual `_Legacy.lean` path names: **0**.
- `TODO|FIXME|XXX|HACK`: **24 hits** in **16 files**; all hits are `TODO`, no `FIXME`, `XXX`, or `HACK` hits in this search.
- `placeholder`: **37 hits** in **18 files**; **27** are in Lean files.
- `True\s*--\s*placeholder`: **1 hit**, at `pnp3/Core/PDT.lean:325`.
- `noncomputable` all occurrences: **505** from the raw task regex; `noncomputable def` declarations: **455** in **54 files**.
- `Classical.choose`: **274 hits** in **31 files**.
- `axiom\s` raw search: **13 textual hits**, but `rg -n "^\s*axiom\b" --type lean pnp3 pnp4` returns no Lean declarations.
- Concerning hot spots: `pnp3/Magnification/FinalResultAuditRoutes.lean` provider/typeclass quarantine; `pnp3/Magnification/FinalResultMainline.lean` legacy `MagnificationAssumptions`; `pnp3/Magnification/LocalityProvider_Partial.lean` and `pnp3/Magnification/LocalityInterfaces_Partial.lean` staged support/locality obligations; `pnp3/Core/PDT.lean` true placeholder; and `pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/CopyAtOffset.lean` harmless proof-local `True` theorem.
## 2. Files audited
### Required / governance files
| path | approximate role | read mode | reason if not fully read |
|---|---|---|---|
| `RESEARCH_CONSTITUTION.md` | research-governance trust and route rules | read fully | n/a |
| `seed_packs/phase1_20engineer_parallel_dispatch/README.md` | phase dispatch overview | read fully | n/a |
| `seed_packs/phase1_20engineer_parallel_dispatch/COMMON_WORKER_INSTRUCTIONS.md` | common worker rules; A10 prompt overrides E<NN> naming | read fully | n/a |
| `seed_packs/phase1_20engineer_parallel_dispatch/tasks/A10_audit_partial_legacy_markers.md` | exact task file | read fully | n/a |

### Marker-positive / scope files
The table below lists every positive-match file from the repository-wide searches and the `_Partial`/`_Legacy` inventory. Most files were searched structurally rather than read proof-by-proof; appendix sections preserve exact hit lines for audit replay.

| path | approximate role | read mode | reason if not fully read |
|---|---|---|---|
| `pnp3/AC0/MultiSwitching/CanonicalDT.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/AC0/MultiSwitching/CommonBad.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/AC0/MultiSwitching/CommonBad_Func.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/AC0/MultiSwitching/CommonCCDT.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/AC0/MultiSwitching/CommonCCDT_Func.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/AC0/MultiSwitching/Counting.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/AC0/MultiSwitching/Definitions.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/AC0/MultiSwitching/Encoding.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/AC0/MultiSwitching/EncodingCommon.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/AC0/MultiSwitching/EncodingCommon_Func.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/AC0/MultiSwitching/ShrinkageFromGood.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/AC0/MultiSwitching/Trace.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/AC0/MultiSwitching/TraceBridge.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Barrier/Bypass.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Candidates/README.md` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Candidates/_template/barrier_certificate.md` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Candidates/_template/critic_report.md` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Candidates/_template/manifest.toml` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Candidates/_template/proof.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Candidates/_template/self_attack.md` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Candidates/_template/sketch.md` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Complexity/Interfaces.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Complexity/PpolyDAG_StraightLineCore.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Complexity/PpolyFormula_from_PpolyDAG_FixedSlice.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Complexity/PsubsetPpolyDAG_Internal.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Complexity/PsubsetPpolyInternal/CircuitTree.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Complexity/PsubsetPpolyInternal/ComplexityInterfaces.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Complexity/PsubsetPpolyInternal/StraightLine.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Complexity/PsubsetPpolyInternal/TreeToStraight.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Complexity/PsubsetPpolyInternal/TuringEncoding.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/BinaryCounter.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/CopyAtOffset.lean` | positive marker/hard-payload/rule16 search result | read structurally | n/a |
| `pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/Foundation.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/GateWrappers.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Core/BooleanBasics.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Core/PDT.lean` | positive marker/hard-payload/rule16 search result | read structurally | n/a |
| `pnp3/Counting/Atlas_to_LB_Core.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Counting/BinomialBounds.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Counting/CircuitCounting.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Counting/Count_EasyFuncs.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Counting/ShannonCounting.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Docs/AC0_Formalization_Abstract.md` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Docs/AC0_Publishable_Result.md` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Docs/AC0_Related_Work.md` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Docs/AsymptoticDAGBarrier_Status.md` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Docs/CLOSURE_ROUTE_POLICY.md` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Docs/CompiledRuntime_SizeClosure_Runbook.md` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Docs/GapTarget_StableRestriction_Route.md` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Docs/INTRO_RELATED_WORK.md` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Docs/MultiSwitching_DepthInduction_TODO.md` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Docs/MultiSwitching_NextStep.md` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Docs/Parameters.md` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Docs/PhaseI_Verifier_Design.md` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Docs/PsubsetPpolyDAG_Closure_Strategy.md` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Docs/PsubsetPpoly_AUDIT_HANDOFF.md` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Docs/PsubsetPpoly_Internal_TODO.md` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Docs/RESEARCH_BLOCKER_FormulaHalfSizeBoundPartial.md` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Docs/Release_2026-03-14_Intermediate.md` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Docs/Research_Method_Boundary.md` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Docs/Simulation_FineGrained_Status.md` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Docs/Unconditional_NP_not_subset_PpolyDAG_Plan.md` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Docs/Unconditionality_FAQ_ru.md` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Docs/UnrestrictedDAG_Blocker_Reassessment_2026-03-30.md` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Docs/archive/PsubsetPpoly_AUDIT_HANDOFF_legacy_snapshot_2026-03-14.md` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Docs/archive/PsubsetPpoly_Internal_TODO_legacy_snapshot_2026-03-14.md` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Docs/archive/UnconditionalPneNpFrontier_legacy_snapshot_2026-04-15.md` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/LowerBounds/AC0_GapMCSP.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/LowerBounds/AC0_GapMCSP_Final.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/LowerBounds/AcceptedFamilyBarrier.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/LowerBounds/AntiChecker_Partial.lean` | partial-table anti-checker and AC0/local-circuit incompatibility route | read structurally | n/a |
| `pnp3/LowerBounds/ApproxClassContradiction.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/LowerBounds/AsymptoticDAGBarrierInterfaces.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/LowerBounds/DAGStableRestrictionProducer.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/LowerBounds/FailedRoute_EventualTableForceSlackObstruction.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/LowerBounds/FailedRoutes.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/LowerBounds/LB_Formulas.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/LowerBounds/LB_Formulas_Core_Partial.lean` | partial formula lower-bound core/closure interface | read structurally | n/a |
| `pnp3/LowerBounds/MCSPGapLocality.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/LowerBounds/RouteBSourceClosure.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/LowerBounds/RouteNextStep_AcceptedFamily.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/LowerBounds/SingletonDensityContradiction.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/LowerBounds/SingletonDensityEndpoint.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/LowerBounds/SingletonProvenanceEndpoint.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Magnification/AC0ApproxFamilyBridge.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Magnification/AC0AtlasBridge.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Magnification/AC0LocalityBridge.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Magnification/AsymptoticDAGCollapse.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Magnification/AsymptoticFormulaCollapse.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Magnification/AuditRoutes/ArbitraryLogWidthTT/Composition.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Magnification/AuditRoutes/CrossLengthCoherence_NoGo.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Magnification/AuditRoutes/DistinguisherMatrixProvenance/V_codexd3a/AntiCollapsePrime.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Magnification/AuditRoutes/DistinguisherMatrixProvenance/V_gpt55/ToySeparation.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Magnification/AuditRoutes/LogWidthAdversary/Composition.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Magnification/AuditRoutes/LogWidthAdversary/Family_NatLog2.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/Survivor.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_B_gpt55/Sketch.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_C_GPT55/Sketch.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Magnification/AuditRoutes/SupportCardinalityBarrier/Barrier.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Magnification/AuditRoutes/SupportCardinalityBarrier/InSupportFunctionalDiversityApplication.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Magnification/Bridge_to_Magnification_Partial.lean` | bridge from partial lower-bound statements into magnification packaging | read structurally | n/a |
| `pnp3/Magnification/Facts_Magnification_Partial.lean` | facts/locality partial magnification adapters | read structurally | n/a |
| `pnp3/Magnification/FinalResult.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Magnification/FinalResultAuditRoutes.lean` | positive marker/hard-payload/rule16 search result | read structurally | n/a |
| `pnp3/Magnification/FinalResultCore.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Magnification/FinalResultLegacyTM.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Magnification/FinalResultMainline.lean` | positive marker/hard-payload/rule16 search result | read structurally | n/a |
| `pnp3/Magnification/FinalResultWeakRoutes.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Magnification/LocalityInterfaces_Partial.lean` | typed partial locality/support-bound interfaces | read structurally | n/a |
| `pnp3/Magnification/LocalityLift_Partial.lean` | partial locality lift bridge | read structurally | n/a |
| `pnp3/Magnification/LocalityProvider_Partial.lean` | partial locality/support-bound provider construction and staging | read structurally | n/a |
| `pnp3/Magnification/PipelineStatements_Partial.lean` | partial pipeline-level public statements | read structurally | n/a |
| `pnp3/Magnification/UnconditionalResearchGap.lean` | positive marker/hard-payload/rule16 search result | read structurally | n/a |
| `pnp3/Models/Model_PartialMCSP.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Models/PartialTruthTable.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/README.md` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/RefutedPredicates/Registry.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Spec/FrozenSpec.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Tests/AC0PublishableSurface.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Tests/AxiomsAudit.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Tests/BarrierAudit.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Tests/BridgeLocalityRegression.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Tests/FixedParams_Probe_NoGo.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Tests/RouteSurfaceAudit.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Tests/SmokeTests.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Tests/TargetLockProbe.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Tests/TestDriver.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/Tests/WeakRouteSurfaceTests.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/ThirdPartyFacts/DEPTH2_STATUS.md` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/ThirdPartyFacts/Facts_Switching.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/ThirdPartyFacts/PartialLocalityLift.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/ThirdPartyFacts/PartialTransport.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp3/ThirdPartyFacts/PpolyFormula.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp4/Pnp4/AlgorithmsToLowerBounds/AC0pCoinAsymptotic.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp4/Pnp4/AlgorithmsToLowerBounds/AC0pCoinLowerBound.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp4/Pnp4/AlgorithmsToLowerBounds/BasicCircuitClasses.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp4/Pnp4/AlgorithmsToLowerBounds/BridgeToPpolyDAG.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp4/Pnp4/AlgorithmsToLowerBounds/CoinMaskingTranslation.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp4/Pnp4/AlgorithmsToLowerBounds/CoinProblem.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp4/Pnp4/AlgorithmsToLowerBounds/FormulaCircuitAsymptotic.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp4/Pnp4/AlgorithmsToLowerBounds/FormulaCircuitPublishedLowerBound.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp4/Pnp4/AlgorithmsToLowerBounds/FormulaCircuitTargetModel.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp4/Pnp4/AlgorithmsToLowerBounds/LocalPRG.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp4/Pnp4/AlgorithmsToLowerBounds/LocalPRGHardnessSpec.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp4/Pnp4/AlgorithmsToLowerBounds/MCSPCoinReduction.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp4/Pnp4/AlgorithmsToLowerBounds/MCSPCoinReductionContract.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp4/Pnp4/AlgorithmsToLowerBounds/MCSP_AC0p_Final.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp4/Pnp4/AlgorithmsToLowerBounds/MCSP_AC0p_Quantitative.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp4/Pnp4/AlgorithmsToLowerBounds/MCSP_Formula_Final.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp4/Pnp4/AlgorithmsToLowerBounds/MCSP_Formula_Theorem2Quantitative.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp4/Pnp4/AlgorithmsToLowerBounds/MCSP_LocalPRG_Transfer.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp4/Pnp4/AlgorithmsToLowerBounds/SuperPolynomialBridge.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp4/Pnp4/AlgorithmsToLowerBounds/TruthTableMCSP.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp4/Pnp4/Frontier/CompressionMagnification.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp4/Pnp4/Frontier/ContractExpansion/C_DAG_Adapter.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguage.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageNP.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageRuntime.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp4/Pnp4/Frontier/PvsNPBridgeRequirements.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp4/Pnp4/Frontier/SearchMCSPConcreteTargets.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp4/Pnp4/Frontier/SearchMCSPMagnification.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `pnp4/README.md` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |
| `seed_packs/phase1_20engineer_parallel_dispatch/tasks/A10_audit_partial_legacy_markers.md` | positive marker/hard-payload/rule16 search result | searched only | large file or matched only as contextual marker; exact hits recorded in appendices |

## 3. Top-level theorem / structure inventory
| declaration | file | type/signature summary | classification | hard payload dependency |
|---|---|---|---|---|
| `PDT.WellFormed` | `pnp3/Core/PDT.lean` | `{n} → PDT n → Prop := True` | staged Prop / placeholder | none; local PDT interface |
| `run_after_j_seek_to_dst_steps` | `pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/CopyAtOffset.lean` | proof-local theorem returning `True` | audit-only / harmless placeholder | none |
| `MagnificationAssumptions` | `pnp3/Magnification/FinalResultMainline.lean` | package of switching + anti-checker assumptions | legacy / refuted-route-adjacent | contains switching support-bounds surface; not a safe final endpoint |
| `MagnificationAssumptions_fromPipeline` | `pnp3/Magnification/FinalResultMainline.lean` | pipeline-aware package replacing single refuted switching contract | conditional / staged interface | depends on pipeline assumptions, not directly on `ResearchGapWitness` |
| `FormulaSupportBoundsFromMultiSwitchingContract` | `pnp3/Magnification/AC0LocalityBridge.lean` | structure packaging AC0/multiswitching support bounds for formula witnesses | refuted route / weak route | refuted support-bounds hard payload, not `ResearchGapWitness` |
| `FormulaSupportBoundsPartial_fromPipeline` | `pnp3/Magnification/LocalityProvider_Partial.lean` | Prop that packages partial support-bounds pipeline obligations | staged Prop / potential wrapper risk | support-bounds route; not `VerifiedNPDAGLowerBoundSource` |
| `VacuousFinalPayloadProvider` | `pnp3/Magnification/FinalResultAuditRoutes.lean` | typeclass provider for refuted/vacuous payload channel | audit-only / hidden-payload risk but quarantined | provides route payload through typeclass; forbidden outside audit/test/docs by guard |
| `Vacuous_P_ne_NP_via_FinalPayloadProvider` | `pnp3/Magnification/FinalResultAuditRoutes.lean` | theorem from provider typeclass to final claim | vacuous / audit-only | depends on `VacuousFinalPayloadProvider`; not reusable |
| `ResearchGapWitness` | `pnp3/Magnification/UnconditionalResearchGap.lean` | target witness whose `dagSeparation` is `NP_not_subset_PpolyDAG` | canonical target / unimplemented gap | is the hard payload itself |
| `VerifiedNPDAGLowerBoundSource` | `pnp4/Pnp4/AlgorithmsToLowerBounds/BridgeToPpolyDAG.lean` | pnp4 source object for NP lower bound against PpolyDAG | canonical pnp4 endpoint | hard payload source for `NP_not_subset_PpolyDAG` |
| `SearchMCSPMagnificationContract` | `pnp4/Pnp4/Frontier/SearchMCSPMagnification.lean` | contract turning search-MCSP weak lower bound into verified DAG source | conditional mainline interface | depends on `VerifiedNPDAGLowerBoundSource` via contract field |

## 4. Kernel-checked content
- `./scripts/check.sh` completed all 17 steps successfully, including full Lean build, source-hygiene scan, doc-honesty lint, Rule 16 quarantine, refuted-route quarantine, target-lock guard, smoke probes, JSONL validation, and axiom-surface dumps.
- Kernel-checked marker-area facts include actual Lean theorems such as `PDT.leaves_le_pow2_depth`, MCSP/truth-table monotonicity surfaces, pnp4 bridge/audit theorems, and numerous partial-route adapters. Their existence is not itself P-vs-NP progress unless they reduce `SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource`.
- The `_Partial` modules are not merely comments: they build under the kernel, and many declarations are theorem/structure surfaces. However, many important endpoints take explicit assumptions/packages or route through known weak/refuted support-bound predicates, so kernel-checking confirms conditional implications, not the missing lower bound.
- There are no active Lean `axiom` declarations in `pnp3`/`pnp4` by the stricter declaration regex.

## 5. Staged / placeholder / Prop-only content
- `PDT.WellFormed` is an actual `True -- placeholder` definition. Classification: honest staging if only used as a future invariant placeholder; potential wrapper risk if downstream proofs treat it as semantic well-formedness.
- `run_after_j_seek_to_dst_steps` returns `True` and is explicitly labelled as handled by direct composition instead. Classification: harmless proof-local placeholder, but the name should not be exported as meaningful runtime semantics.
- `FormulaSupportBoundsPartial_fromPipeline` and related partial provider surfaces package mathematical obligations as `Prop`. Classification: honest staging / potential wrapper risk; do not treat fields as proved lower bounds.
- `PrefixExtensionLanguageRuntime` / `PrefixExtensionLanguageNP` comments explicitly say they avoid vacuous `True` placeholders; search hits there are governance-positive rather than suspicious.

## 6. Refuted / vacuous / legacy route check
- Search for refuted/vacuous/legacy markers returned **826 hits** in **87 files**.
- The audited area contains `RefutedRoute_*` names, `MagnificationAssumptions`, support-bounds terminology, `VacuousFinalPayloadProvider`, `_Partial` files, and TODO/placeholder comments. These are mostly isolated in `pnp3/Magnification/FinalResultAuditRoutes.lean`, `pnp3/Magnification/FinalResultMainline.lean`, tests, docs, and partial-route modules.
- The most dangerous historical channel is `VacuousFinalPayloadProvider`; it is explicitly renamed as vacuous/refuted and covered by `scripts/check.sh` Rule-16/typeclass-payload quarantine. Future workers should not import or instantiate it for candidate work.
- `_Legacy` file inventory is empty by path name; legacy route content remains by declaration/comment names (`MagnificationAssumptions`, `FinalResultLegacyTM.lean`, audit route wrappers).

## 7. Hidden payload / Rule 16 check
- Rule-16-style search returned **1084 hits** in **96 files**. Most are ordinary `class`/`instance`/`Fact` uses, standard `noncomputable def`s, or `Classical.choose` witness extraction.
- **Hidden-payload risk:** `VacuousFinalPayloadProvider`, `Fact hasDefaultFormulaSupportRestrictionBoundsPartial`, and related instances in `FinalResultAuditRoutes.lean`; these are audit-only and already quarantined.
- **Harmless infrastructure:** ordinary Mathlib/Lean class and instance syntax in circuit/AC0/TM support modules, surface test wrappers, and exponent/witness extraction from explicit existential hypotheses.
- **Standard exponent/existence extraction:** many `Classical.choose` occurrences extract `InPpolyFormula`, formula/DAG families, finite maxima, canonical restrictions, or witnesses from explicit hypotheses. These add `Classical.choice` to axiom surfaces but do not by themselves create hidden P-vs-NP payload.
- **Forbidden if used by candidate:** any provider/default/typeclass route that supplies final payload, support bounds, `ResearchGapWitness`, `NP_not_subset_PpolyDAG`, or equivalent lower-bound source without an explicit theorem. I found no new candidate instance in this audit; this is a warning for future work.

## 8. Barrier relevance
- **natural proofs:** actual barrier/audit theorems and smoke tests exist in barrier/provenance areas; marker audit found references.
- **relativization:** trust-root barrier modules build; A10 did not deep-audit proofs.
- **algebrization:** trust-root barrier modules build; A10 did not deep-audit proofs.
- **locality:** typed interfaces and staged Props in `_Partial` locality modules.
- **hardwiring:** actual support-cardinality/hardwiring barrier modules and audit tests appear in search output.
- **support-cardinality-only:** actual audit barrier theorems/tests exist; support-bounds route is quarantined/refuted.
- **syntax-only filters:** ProvenanceFilterV2 audit modules appear; treated as audit routes, not final progress.
- **normalization filters:** ProvenanceFilterV2 normalise meta-barrier appears in build output; no A10 deep proof audit.
- **search-to-decision:** pnp4 MCSP/search magnification contracts are typed interfaces; not resolved by marker cleanup.
- **MCSP / magnification:** central to partial-route markers; many conditional interfaces, no new hard source constructed.

## 9. Reuse map
Safe to reuse:
- Search scripts/commands and this marker inventory as a triage map.
- Kernel-checked low-level infrastructure (`PDT` leaf bounds, truth-table MCSP propositional surfaces, explicit pnp4 bridge interfaces) when their hypotheses are understood.
- `SearchMCSPMagnificationContract`, `VerifiedNPDAGLowerBoundSource`, and bridge modules as canonical endpoints/interfaces, not as solved payloads.
- Tests and audits that quarantine refuted/vacuous routes (`AxiomsAudit`, barrier audits, route-surface tests).

Avoid:
- `VacuousFinalPayloadProvider`, default support-bounds instances, and any provider/typeclass final-payload route.
- Treating `PDT.WellFormed := True` as semantic well-formedness.
- Treating `_Partial` support/locality provider surfaces as unconditional lower bounds.
- Rebranding `MagnificationAssumptions` or `RefutedRoute_*` as mainline progress.

## 10. Gap map
### A. Engineering gap
- Replace or quarantine `PDT.WellFormed := True` if any downstream consumer needs real PDT invariants.
- Consider renaming/protecting proof-local `run_after_j_seek_to_dst_steps : True` to avoid semantic misread.
- Reduce `noncomputable def`/`Classical.choose` noise in tests and infrastructure only where it improves audit clarity without changing mathematics.

### B. Formalization gap
- Several `_Partial`/support/locality provider surfaces state obligations as packages/Props; concrete witnesses/proofs are not supplied by marker cleanup.
- pnp4 search-MCSP contracts remain conditional interfaces pending a genuine lower-bound source.

### C. Mathematical gap
- The hard missing object remains `ResearchGapWitness.dagSeparation : NP_not_subset_PpolyDAG` or pnp4 `VerifiedNPDAGLowerBoundSource`/`SearchMCSPWeakLowerBound`.
- Support-cardinality/locality/provenance routes are explicitly known to hit barriers/refutations unless bridged to PpolyDAG without the refuted assumptions.

### D. Governance gap
- Legacy/refuted naming is mostly explicit, but marker density is high enough that new workers can confuse audited/vacuous wrappers with usable endpoints.
- Documentation references to older TODOs and legacy snapshots are benign but noisy.

## 11. Recommended Phase 1+ tasks
### 1. PDT well-formedness quarantine or replacement
- exact files to touch: `pnp3/Core/PDT.lean` plus direct consumers only
- allowed scope: Lean: either replace `PDT.WellFormed := True` with minimal real invariants or rename as explicitly staged
- forbidden scope: No lower-bound routes; no final endpoints
- expected output: kernel-checked invariant or explicit staging name
- estimated time: 0.5-1 day
- dependency on other audits: none
- risk level: medium
- type: Lean
### 2. CopyAtOffset placeholder theorem cleanup
- exact files to touch: `pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/CopyAtOffset.lean`
- allowed scope: Lean cleanup: make the `True` theorem private/remove if unused or document as local helper
- forbidden scope: No TM semantics rewrites beyond local proof hygiene
- expected output: no exported semantic-looking theorem returning `True`
- estimated time: 0.5 day
- dependency on other audits: none
- risk level: low
- type: Lean
### 3. Audit-route provider quarantine documentation tightening
- exact files to touch: `pnp3/Magnification/FinalResultAuditRoutes.lean`, tests/docs that mention provider names
- allowed scope: Markdown/comments/tests only unless operator approves; clarify vacuous provider isolation
- forbidden scope: No provider promotion; no instances outside audit
- expected output: clearer audit-only labels and route-surface tests if missing
- estimated time: 0.5-1 day
- dependency on other audits: A01/A05 cross-check
- risk level: medium
- type: Lean+markdown or markdown-only
### 4. Noncomputable/choose hotspot classification follow-up
- exact files to touch: new markdown report under audit_reports or docs only
- allowed scope: Markdown-only deep dive on top five files by counts
- forbidden scope: No code edits
- expected output: per-file classification of top hotspots and risk ranking
- estimated time: 1 day
- dependency on other audits: A10 report
- risk level: low
- type: markdown-only
### 5. Partial-route public surface map
- exact files to touch: `pnp3/Tests/WeakRouteSurfaceTests.lean`, `pnp3/Tests/AxiomsAudit.lean`, relevant `_Partial` modules
- allowed scope: Lean test/audit additions only to expose which partial statements are conditional/refuted/staged
- forbidden scope: No new theorem claims, no bridge construction
- expected output: updated surface/audit wrappers for existing partial declarations
- estimated time: 1-2 days
- dependency on other audits: A01/A05/A09
- risk level: medium
- type: Lean
### 6. Doc drift cleanup for TODO/legacy references
- exact files to touch: docs with TODO/legacy marker hits
- allowed scope: Markdown-only edit to separate active TODOs from historical snapshots
- forbidden scope: No mathematical claims; no source edits
- expected output: short active-vs-archived TODO index
- estimated time: 0.5-1 day
- dependency on other audits: operator decision
- risk level: low
- type: markdown-only

## 12. Stop / hold recommendations
- Hold or downgrade any task that would build on `FormulaSupportBoundsFromMultiSwitchingContract`, `FormulaSupportBoundsPartial_fromPipeline`, default support bounds, or `VacuousFinalPayloadProvider` as if they were mainline lower-bound evidence.
- Hold any task proposing to “complete” `P_ne_NP` by wrapping `ResearchGapWitness`, `NP_not_subset_PpolyDAG`, or `VerifiedNPDAGLowerBoundSource` rather than proving/supplying the hard payload.
- Do not touch trust-root files in a marker cleanup wave unless the operator opens a separate Foundational PR.

## 13. Honest caveats
- I did not inspect every proof body in every marker-positive file; large files were searched structurally and summarized by marker hits.
- I verified signatures and command results, not the mathematical adequacy of each conditional route theorem.
- I did not reconstruct the complete import graph or dependency closure for every theorem listed in pnp3/pnp4 axiom audits.
- Noncomputable/Classical.choose categorization is by file/usage pattern and sampled interpretation; a later deep dive should classify each of the 455 `noncomputable def`s if operator needs per-declaration risk tags.
- This audit should be cross-checked with A01/A05 for magnification partials and A09 for NoGoLog/refuted-route governance.

## `_Partial` file inventory
- `pnp3/LowerBounds/AntiChecker_Partial.lean` — partial-table anti-checker and AC0/local-circuit incompatibility route.
- `pnp3/LowerBounds/LB_Formulas_Core_Partial.lean` — partial formula lower-bound core/closure interface.
- `pnp3/Magnification/Bridge_to_Magnification_Partial.lean` — bridge from partial lower-bound statements into magnification packaging.
- `pnp3/Magnification/Facts_Magnification_Partial.lean` — facts/locality partial magnification adapters.
- `pnp3/Magnification/LocalityInterfaces_Partial.lean` — typed partial locality/support-bound interfaces.
- `pnp3/Magnification/LocalityLift_Partial.lean` — partial locality lift bridge.
- `pnp3/Magnification/LocalityProvider_Partial.lean` — partial locality/support-bound provider construction and staging.
- `pnp3/Magnification/PipelineStatements_Partial.lean` — partial pipeline-level public statements.

## `_Legacy` file inventory
No Lean file path ending in `_Legacy.lean` was found. Legacy content exists by declaration/module naming (notably `FinalResultLegacyTM.lean`, `MagnificationAssumptions`, and `RefutedRoute_*`).

## TODO/FIXME/HACK locations
All hits are categorized as `TODO`; no `FIXME`, `XXX`, or `HACK` hits were found by the requested regex.
```text
pnp3/Docs/MultiSwitching_NextStep.md:10:- `TODO.md`
pnp3/Docs/MultiSwitching_NextStep.md:12:- `pnp3/Docs/MultiSwitching_DepthInduction_TODO.md`
pnp3/Docs/Unconditional_NP_not_subset_PpolyDAG_Plan.md:166:5. `README.md`, `STATUS.md`, `TODO.md`, and checklist docs are consistent.
pnp3/Docs/PsubsetPpoly_Internal_TODO.md:1:# PsubsetPpoly Internal Closure TODO (current inclusion-side status)
pnp3/Docs/PsubsetPpoly_Internal_TODO.md:10:- `/root/p-np2/TODO.md`
pnp3/Docs/CLOSURE_ROUTE_POLICY.md:71:Canonical docs (`STATUS.md`, `TODO.md`,
pnp3/Docs/PsubsetPpolyDAG_Closure_Strategy.md:15:> `pnp3/Docs/PsubsetPpoly_Internal_TODO.md`,
pnp3/Docs/PsubsetPpolyDAG_Closure_Strategy.md:224:   - синхронизировать этот файл с `PsubsetPpoly_Internal_TODO.md`.
pnp3/Docs/archive/PsubsetPpoly_Internal_TODO_legacy_snapshot_2026-03-14.md:1:# PsubsetPpoly Internal Closure TODO (single-pass runbook)
pnp3/Docs/archive/PsubsetPpoly_Internal_TODO_legacy_snapshot_2026-03-14.md:396:- [x] TODO обновлён по факту
pnp3/Docs/Parameters.md:8:`STATUS.md` и `TODO.md`.
pnp3/Docs/CompiledRuntime_SizeClosure_Runbook.md:12:> `pnp3/Docs/PsubsetPpoly_Internal_TODO.md` и
pnp3/Docs/MultiSwitching_DepthInduction_TODO.md:7:Статус файла: рабочий TODO/roadmap по подпроцесcу depth>2.
pnp3/Docs/MultiSwitching_DepthInduction_TODO.md:9:состояния используйте `STATUS.md` и `TODO.md`.
pnp3/Docs/Release_2026-03-14_Intermediate.md:51:- Current status: `pnp3/Docs/PsubsetPpoly_Internal_TODO.md`
pnp3/README.md:88:- `/root/p-np2/TODO.md`
pnp3/ThirdPartyFacts/DEPTH2_STATUS.md:12:- `TODO.md`
pnp3/ThirdPartyFacts/DEPTH2_STATUS.md:14:- `pnp3/Docs/MultiSwitching_DepthInduction_TODO.md`
pnp3/AC0/MultiSwitching/Encoding.lean:1351:### Декодирование малого encoding (TODO depth>2)
pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean:356:construction and §6 for the lemma TODOs).  The surrounding
pnp3/Tests/AxiomsAudit.lean:98:-- Это именно те утверждения, которые в TODO помечены для перепроверки.
pnp3/LowerBounds/AntiChecker_Partial.lean:681:  TODO (следующий шаг): связать множество `F` с семейством «малых» AC⁰‑решателей
pnp3/LowerBounds/AntiChecker_Partial.lean:1983:  В TODO требовалась вероятностная формулировка: случайная partial‑таблица
pnp3/LowerBounds/AntiChecker_Partial.lean:2016:  TODO (следующие шаги):
```

## `placeholder` keyword locations
```text
pnp3/Core/PDT.lean:325:def PDT.WellFormed {n : Nat} (_t : PDT n) : Prop := True  -- placeholder
pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageRuntime.lean:41:bounds instead of a vacuous `True` placeholder.  Runtime claims below are still
pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageNP.lean:39:`True` or any vacuous placeholder.
pnp3/Docs/PhaseI_Verifier_Design.md:391:   so no `sorry`/`admit` placeholders are needed.
pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/Foundation.lean:23:The file introduces no axioms and no unfinished proof placeholders;
pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/CopyAtOffset.lean:329:    : True := trivial  -- placeholder: we handle B via direct composition instead.
pnp3/ThirdPartyFacts/Facts_Switching.lean:1625:  по глубине.  Это уже не placeholder‑лемма уровня `M²`: polylog‑bound
pnp3/Complexity/PsubsetPpolyInternal/ComplexityInterfaces.lean:10:standalone `P ⊆ P/poly` proof.  Unlike the previous placeholder version, we
pnp3/Candidates/_template/critic_report.md:6:> `spec/critic_protocol.md`.  Every line below is a placeholder.  The
pnp3/Candidates/_template/critic_report.md:10:> per-section `Template placeholder` markers, and refuses to count
pnp3/Candidates/_template/critic_report.md:25:- **summary:** Template placeholder — replace with whether the
pnp3/Candidates/_template/critic_report.md:37:- **summary:** Template placeholder — replace with whether the
pnp3/Candidates/_template/critic_report.md:47:- **summary:** Template placeholder — replace with whether the
pnp3/Candidates/_template/critic_report.md:57:- **summary:** Template placeholder — replace with the result of
pnp3/Candidates/_template/critic_report.md:68:- **summary:** Template placeholder — replace with whether the
pnp3/Candidates/_template/critic_report.md:79:- **summary:** Template placeholder — replace with whether the
pnp3/Candidates/_template/critic_report.md:98:> * remove every `Template placeholder` / `Template — fill` /
pnp3/Candidates/_template/proof.lean:5:and `gap_from_template` declarations below are placeholders that
pnp3/Candidates/_template/proof.lean:8:replace the placeholders with concrete claims, and run
pnp3/Magnification/UnconditionalResearchGap.lean:34:1. Prove `ResearchGapWitness` in this file, by replacing the placeholder
pnp3/Magnification/FinalResultAuditRoutes.lean:607:  -- inconsistent.  The placeholder-free chain below reuses the legacy
pnp3/Tests/FixedParams_Probe_NoGo.lean:126:/-- Smoke: the FP-3b.1 placeholder language elaborates. -/
pnp3/Tests/FixedParams_Probe_NoGo.lean:131:/-- Smoke: the FP-3b.1 placeholder family elaborates. -/
pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean:166:## FP-3 anchor — `ProvenanceFilter_v1` (informal placeholder, NO Lean
pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean:296:  length — a trivial placeholder family;
pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean:344:/-- **FP-3b.1 placeholder adversary family.**
pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean:379:/-- **FP-3b.1 placeholder InPpolyFormula record.**
pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean:418:The placeholder record below (`adversaryFamily := fun _ => const
pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean:461:example : True := trivial   -- placeholder so the docstring above
pnp3/Magnification/AuditRoutes/LogWidthAdversary/Family_NatLog2.lean:11:`Nat.log_le_self`) and conjoins them.  Thus it is not the constant placeholder
pnp3/Magnification/AuditRoutes/LogWidthAdversary/Composition.lean:32:The proof has no proof-suspension placeholders, no `axiom`, and stays inside
pnp3/Magnification/AuditRoutes/LogWidthAdversary/Composition.lean:225:no proof-suspension placeholders, no `axiom`. -/
pnp3/Magnification/AuditRoutes/CrossLengthCoherence_NoGo.lean:52:* No proof-suspension placeholders of any kind (the v0.4.2
pnp3/Magnification/AuditRoutes/CrossLengthCoherence_NoGo.lean:89:/-- **Naive** cross-length coherence (a placeholder predicate).
pnp3/Magnification/AuditRoutes/CrossLengthCoherence_NoGo.lean:101:/-- **Strong** cross-length coherence (a placeholder predicate).
pnp3/Magnification/AuditRoutes/CrossLengthCoherence_NoGo.lean:107:this is just a named placeholder — the actual definition will
pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_B_gpt55/Sketch.lean:62:the Lean predicate below uses `Bool.xor` rather than a vacuous placeholder; it
```

## `Prop` placeholder pattern (`True -- placeholder`)
```text
pnp3/Core/PDT.lean:325:def PDT.WellFormed {n : Nat} (_t : PDT n) : Prop := True  -- placeholder
```

## `noncomputable def` audit
Categorization summary by file count: pnp3 `Simulation.lean`, AC0 encoding/switching modules, pnp4 probability/MCSP translations, and tests are mostly standard finite-choice/extraction infrastructure; `FinalResultAuditRoutes.lean` provider-related noncomputable definitions are audit-only/high-risk if reused; partial support/locality route noncomputable definitions are conditional and should not be promoted. Full declaration list follows.
```text
pnp3/Core/BooleanBasics.lean:1221:noncomputable def restrictionOfFreeEquiv
pnp3/Core/BooleanBasics.lean:3142:noncomputable def assignResult (choice : Selection w) :
pnp3/Core/BooleanBasics.lean:3154:noncomputable def nextRestriction (choice : Selection w) : Restriction n :=
pnp3/Core/BooleanBasics.lean:3646:noncomputable def finalRestriction :
pnp3/Core/BooleanBasics.lean:3656:noncomputable def indicesList :
pnp3/Core/BooleanBasics.lean:3667:noncomputable def valuesList :
pnp3/Core/BooleanBasics.lean:3678:noncomputable def positionList :
pnp4/Pnp4/Frontier/ContractExpansion/C_DAG_Adapter.lean:44:noncomputable def InPpolyDAG_to_C_DAG_family
pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguage.lean:124:noncomputable def PrefixExtensionLanguage
pnp4/Pnp4/AlgorithmsToLowerBounds/LocalPRGHardnessSpec.lean:91:noncomputable def thresholdMCSPLanguage
pnp4/Pnp4/AlgorithmsToLowerBounds/CoinMaskingTranslation.lean:110:noncomputable def expectationProductBias
pnp4/Pnp4/AlgorithmsToLowerBounds/CoinMaskingTranslation.lean:168:noncomputable def maskedAcceptanceAverage
pnp4/Pnp4/AlgorithmsToLowerBounds/CoinMaskingTranslation.lean:328:noncomputable def maskedAcceptanceAdvantage
pnp4/Pnp4/AlgorithmsToLowerBounds/CoinMaskingTranslation.lean:336:noncomputable def fixedMaskAcceptanceAdvantage
pnp4/Pnp4/AlgorithmsToLowerBounds/CoinMaskingTranslation.lean:488:noncomputable def bestMaskForCircuit
pnp4/Pnp4/AlgorithmsToLowerBounds/AC0pCoinAsymptotic.lean:15:noncomputable def halfVsFairMCSPCoinAsymptoticLanguage
pnp4/Pnp4/AlgorithmsToLowerBounds/MCSP_LocalPRG_Transfer.lean:166:noncomputable def treeMCSPCountRatio
pnp4/Pnp4/AlgorithmsToLowerBounds/MCSP_LocalPRG_Transfer.lean:235:noncomputable def exactTreeMCSPThresholdDecision
pnp4/Pnp4/AlgorithmsToLowerBounds/MCSP_LocalPRG_Transfer.lean:256:noncomputable def exactTreeMCSPThresholdHardDecision
pnp4/Pnp4/AlgorithmsToLowerBounds/MCSP_LocalPRG_Transfer.lean:274:noncomputable def treeMCSPPredicateDecision
pnp4/Pnp4/AlgorithmsToLowerBounds/MCSP_LocalPRG_Transfer.lean:290:noncomputable def notTreeMCSPPredicateDecision
pnp4/Pnp4/AlgorithmsToLowerBounds/MCSP_LocalPRG_Transfer.lean:316:noncomputable def treeMCSPPredicateOracle
pnp4/Pnp4/AlgorithmsToLowerBounds/MCSP_LocalPRG_Transfer.lean:478:noncomputable def exactTreeMCSPThresholdLanguage
pnp4/Pnp4/AlgorithmsToLowerBounds/MCSP_LocalPRG_Transfer.lean:500:noncomputable def implementedThresholdOracleOfCircuit
pnp4/Pnp4/AlgorithmsToLowerBounds/FormulaCircuitAsymptotic.lean:155:noncomputable def formulaCircuitAsymptoticLanguageOfSliceSpec
pnp4/Pnp4/AlgorithmsToLowerBounds/FormulaCircuitAsymptotic.lean:264:noncomputable def formulaCircuitAsymptoticLanguage
pnp4/Pnp4/AlgorithmsToLowerBounds/MCSP_Formula_Final.lean:53:noncomputable def CKLMFormulaCircuitLanguage
pnp4/Pnp4/AlgorithmsToLowerBounds/CoinProblem.lean:19:noncomputable def productBiasWeight
pnp4/Pnp4/AlgorithmsToLowerBounds/CoinProblem.lean:27:noncomputable def acceptanceProbability
pnp4/Pnp4/AlgorithmsToLowerBounds/CoinProblem.lean:215:noncomputable def acceptanceGap
pnp4/Pnp4/AlgorithmsToLowerBounds/CoinProblem.lean:226:noncomputable def SolvesCoinProblem
pnp4/Pnp4/AlgorithmsToLowerBounds/CoinProblem.lean:288:noncomputable def ClassSolvesCoinProblem
pnp4/Pnp4/AlgorithmsToLowerBounds/CoinProblem.lean:299:noncomputable def BoundedClassSolvesCoinProblem
pnp4/Pnp4/AlgorithmsToLowerBounds/LocalPRG.lean:16:noncomputable def bitVecAcceptanceProbability
pnp4/Pnp4/AlgorithmsToLowerBounds/LocalPRG.lean:23:noncomputable def uniformTruthTableAcceptanceProbability
pnp4/Pnp4/AlgorithmsToLowerBounds/LocalPRG.lean:46:noncomputable def seedAcceptanceProbability
pnp4/Pnp4/AlgorithmsToLowerBounds/LocalPRG.lean:123:noncomputable def FoolsBoundedTruthTableClass
pnp4/Pnp4/AlgorithmsToLowerBounds/LocalPRG.lean:138:noncomputable def OneSidedFoolsBoundedTruthTableClass
pnp4/Pnp4/AlgorithmsToLowerBounds/MCSP_AC0p_Quantitative.lean:172:noncomputable def AC0pCoinQuantitativeLanguage
pnp4/Pnp4/AlgorithmsToLowerBounds/MCSPCoinReductionContract.lean:231:noncomputable def CoinDistinguisherFamily.of_adjacentBiasMCSP
pnp4/Pnp4/AlgorithmsToLowerBounds/MCSPCoinReductionContract.lean:311:noncomputable def CircuitCoinDistinguisherFamily.of_adjacentBiasMCSP_circuit
pnp4/Pnp4/AlgorithmsToLowerBounds/MCSPCoinReductionContract.lean:504:noncomputable def coinTranslationPreservesClass_of_maskingSetup
pnp4/Pnp4/AlgorithmsToLowerBounds/MCSPCoinReductionContract.lean:623:noncomputable def coinTranslationPreservesClass_of_maskingSetup_AC0p
pnp4/Pnp4/AlgorithmsToLowerBounds/MCSPCoinReductionContract.lean:645:noncomputable def halfVsFairCoinDistinguisherFamily
pnp4/Pnp4/AlgorithmsToLowerBounds/MCSPCoinReductionContract.lean:669:noncomputable def CircuitCoinDistinguisherFamily.translate_to_halfVsFair
pnp4/Pnp4/AlgorithmsToLowerBounds/MCSPCoinReductionContract.lean:1304:noncomputable def HalfVsFairMCSPCoinRejectionContract.of_biasedLowComplexityMassFacts
pnp4/Pnp4/AlgorithmsToLowerBounds/MCSPCoinReductionContract.lean:1367:noncomputable def halfVsFairMCSPCoinLanguage
pnp4/Pnp4/AlgorithmsToLowerBounds/MCSPCoinReductionContract.lean:1389:noncomputable def HalfVsFairMCSPCoinReductionContract.toWitness
pnp4/Pnp4/AlgorithmsToLowerBounds/FormulaCircuitPublishedLowerBound.lean:27:noncomputable def formulaCircuitThresholdLanguage
pnp4/Pnp4/AlgorithmsToLowerBounds/MCSP_Formula_Theorem2Quantitative.lean:140:noncomputable def CKLMFormulaCircuitQuantitativeLanguage
pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/GateWrappers.lean:4759:noncomputable def canonicalPrior {n : Nat} (gates : List (SLGate n))
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:31:noncomputable def stateEquiv (M : TM) : M.state ≃ Fin (stateCard M) :=
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:35:noncomputable def stateIndex (M : TM) (q : M.state) : Fin (stateCard M) :=
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:39:noncomputable def stateList (M : TM) : List M.state :=
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:47:noncomputable def stateSymbolPairs (M : TM) : List (M.state × Bool) :=
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:165:noncomputable def bigOr {n : Nat} : List (Circuit n) → Circuit n
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:169:noncomputable def bigAnd {n : Nat} : List (Circuit n) → Circuit n
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:189:noncomputable def literal {n : Nat} (i : Fin n) (b : Bool) : Circuit n :=
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:192:noncomputable def minterm {n : Nat} (a : Point n) : Circuit n :=
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:233:noncomputable def satisfyingPoints {n : Nat} (f : Point n → Bool) : List (Point n) :=
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:242:noncomputable def truthTableCircuit {n : Nat} (f : Point n → Bool) : Circuit n :=
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:286:noncomputable def evalTape (cc : ConfigCircuits M n) (x : Point n) :
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:290:noncomputable def evalHead (cc : ConfigCircuits M n) (x : Point n) :
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:294:noncomputable def evalState (cc : ConfigCircuits M n) (x : Point n) :
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:305:noncomputable def initial (M : TM) (n : Nat) : ConfigCircuits M n where
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:351:noncomputable def decodeHead (cc : ConfigCircuits M n) (x : Point n) :
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:359:noncomputable def decodeState (cc : ConfigCircuits M n) (x : Point n) :
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:367:noncomputable def decodedConfig (cc : ConfigCircuits M n) (x : Point n) :
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:431:noncomputable def nextTapeCircuit (M : TM) {n : Nat}
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:437:noncomputable def nextHeadCircuit (M : TM) {n : Nat}
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:443:noncomputable def nextStateCircuit (M : TM) {n : Nat}
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:448:noncomputable def stepCircuitsTruthTable (M : TM) {n : Nat}
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:515:noncomputable def runtimeCircuits (M : TM) (n : Nat) : ConfigCircuits M n :=
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:525:noncomputable def symbol (M : TM) {n : Nat}
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:531:noncomputable def guardSymbol (M : TM) {n : Nat}
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:536:noncomputable def branchIndicator (M : TM) {n : Nat}
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:541:noncomputable def writeTerm (M : TM) {n : Nat}
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:548:noncomputable def writeBit (M : TM) {n : Nat}
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:554:noncomputable def acceptCircuit (M : TM) {n : Nat}
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:633:noncomputable def headStateSymbolPairsAux (M : TM) (n : Nat) :
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:639:noncomputable def headStateSymbolPairs (M : TM) (n : Nat) :
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:688:noncomputable def initFalse (sc : StraightConfig M n) :
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:694:noncomputable def appendConstCurrent (bw : BuiltWire (n := n) base)
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:701:noncomputable def appendNotCurrent (bw : BuiltWire (n := n) base)
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:708:noncomputable def appendAndCurrent (bw : BuiltWire (n := n) base)
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:715:noncomputable def appendOrCurrent (bw : BuiltWire (n := n) base)
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:724:noncomputable def appendAndBase (bw : BuiltWire (n := n) base)
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:732:noncomputable def appendOrBase (bw : BuiltWire (n := n) base)
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:797:noncomputable def buildSymbolAux (sc : StraightConfig M n) :
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:809:noncomputable def buildSymbol (sc : StraightConfig M n) :
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:840:noncomputable def buildGuardSymbol (sc : StraightConfig M n) (b : Bool) :
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:851:noncomputable def buildBranchIndicator (sc : StraightConfig M n)
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:863:noncomputable def buildWriteTerm (sc : StraightConfig M n)
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:884:noncomputable def BuiltCarry.init (bw : BuiltWire (n := n) base) :
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:889:noncomputable def BuiltCarry.appendConst (bc : BuiltCarry (n := n) base) (val : Bool) :
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:900:noncomputable def BuiltCarry.appendNot (bc : BuiltCarry (n := n) base)
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:912:noncomputable def BuiltCarry.appendAnd (bc : BuiltCarry (n := n) base)
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:924:noncomputable def BuiltCarry.appendOr (bc : BuiltCarry (n := n) base)
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:941:noncomputable def buildSymbolFromCarry (sc : StraightConfig M n) :
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:957:noncomputable def buildBranchFromCarry (sc : StraightConfig M n)
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:968:noncomputable def buildWriteTermFromCarry (sc : StraightConfig M n)
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:982:noncomputable def buildWriteBitAux (sc : StraightConfig M n) :
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:993:noncomputable def buildStateTermFromCarry (sc : StraightConfig M n)
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:1007:noncomputable def buildNextStateAux (sc : StraightConfig M n) (qTarget : M.state) :
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:1018:noncomputable def buildNextState (sc : StraightConfig M n) (qTarget : M.state) :
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:1026:noncomputable def buildHeadTermFromCarry (sc : StraightConfig M n)
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:1046:noncomputable def buildNextHeadAux (sc : StraightConfig M n)
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:1059:noncomputable def buildNextHead (sc : StraightConfig M n)
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:1076:noncomputable def buildNextTapeFromCarry (sc : StraightConfig M n)
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:1096:noncomputable def buildWriteBit (sc : StraightConfig M n) :
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:2186:noncomputable def buildWriteBitAuxEval
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:2215:noncomputable def buildNextStateAuxEval
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:2246:noncomputable def buildNextHeadAuxEval
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:2375:noncomputable def buildNextTape (sc : StraightConfig M n)
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:2543:noncomputable def linearStepBlueprint (sc : StraightConfig M n) :
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:2554:noncomputable def linearWriteBitWire (sc : StraightConfig M n) :
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:2562:noncomputable def linearNextStateWire (sc : StraightConfig M n) (qTarget : M.state) :
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:2570:noncomputable def linearNextHeadWire (sc : StraightConfig M n)
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:2579:noncomputable def linearNextTapeWire (sc : StraightConfig M n)
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:2641:noncomputable def buildNextTapeAllAux (sc : StraightConfig M n) :
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:2685:noncomputable def buildNextTapeAll (sc : StraightConfig M n) :
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:2717:noncomputable def buildNextTapeAllAuxLookup
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:2764:noncomputable def buildNextTapeAllLookup
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:3211:noncomputable def buildNextHeadAllAux (sc : StraightConfig M n) :
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:4679:noncomputable def buildNextHeadAllAuxLookup
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:4748:noncomputable def buildNextStateAllAux (sc : StraightConfig M n) :
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:4761:noncomputable def buildNextTapeAllAuxEval
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:4772:noncomputable def buildNextHeadAllAuxEval
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:4786:noncomputable def buildNextStateAllAuxEval
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:6051:noncomputable def buildNextStateAllAuxLookup
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:6411:noncomputable def liftConfig
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:6428:noncomputable def toTreeWire (C : StraightLineCircuit n) :
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:6433:noncomputable def toConfigCircuits (sc : StraightConfig M n) : ConfigCircuits M n where
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:6514:noncomputable def stateTermEval
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:6538:noncomputable def stateTermAnyEval
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:6801:noncomputable def headTermEval
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:6865:noncomputable def headTermAnyEval
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:7431:noncomputable def writeTermEval
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:7452:noncomputable def writeTermAnyEval
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:7786:noncomputable def constBaseCircuit (n : Nat) : StraightLineCircuit n where
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:7795:noncomputable def initialStraightConfig (M : TM) (n : Nat) : StraightConfig M n where
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:7930:noncomputable def stepCompiledTruthTable (M : TM) {n : Nat} (sc : StraightConfig M n) :
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:9024:noncomputable def runtimeConfigCompiled (M : TM) (n : Nat) : StraightConfig M n :=
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:9031:noncomputable def runtimeConfigCompiledLinear (M : TM) (n : Nat) : StraightConfig M n :=
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:9078:noncomputable def acceptCircuitOf (M : TM) {n : Nat}
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:9085:noncomputable def acceptCircuitCompiled (M : TM) (n : Nat) : StraightLineCircuit n :=
pnp3/Complexity/PsubsetPpolyInternal/StraightLine.lean:86:noncomputable def toCircuitWireOf {n : Nat} (C : Circuit n)
pnp3/Complexity/PsubsetPpolyInternal/StraightLine.lean:184:noncomputable def toCircuitWireAux {n : Nat} (C : Circuit n) :
pnp3/Complexity/PsubsetPpolyInternal/StraightLine.lean:212:noncomputable def toCircuitGateAux {n : Nat} (C : Circuit n) :
pnp3/Complexity/PsubsetPpolyInternal/StraightLine.lean:230:noncomputable def toCircuitWire {n : Nat} (C : Circuit n) :
pnp3/Complexity/PsubsetPpolyInternal/StraightLine.lean:235:noncomputable def toCircuit {n : Nat} (C : Circuit n) :
pnp3/Complexity/PsubsetPpolyInternal/CircuitTree.lean:42:noncomputable def eval {n : ℕ} : Circuit n → Point n → Bool
pnp3/Complexity/PsubsetPpolyInternal/TreeToStraight.lean:345:noncomputable def compileTree : Boolcube.Circuit n → Compiled n
pnp3/Complexity/PsubsetPpolyInternal/TreeToStraight.lean:382:noncomputable def compileTreeCircuit (c : Boolcube.Circuit n) : Circuit n :=
pnp3/Complexity/PsubsetPpolyInternal/TreeToStraight.lean:422:noncomputable def packFin (m : Nat) (f : Fin m → Boolcube.Circuit n) : CompiledFin n m := by
pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean:41:noncomputable def check_InPpolyDAG_to_C_DAG_family
pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean:87:noncomputable def check_PrefixExtensionLanguage
pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean:178:noncomputable def check_expectationProductBias
pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean:213:noncomputable def check_maskedAcceptanceAverage
pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean:267:noncomputable def check_maskedAcceptanceAdvantage
pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean:273:noncomputable def check_fixedMaskAcceptanceAdvantage
pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean:363:noncomputable def check_bestMaskForCircuit
pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean:413:noncomputable def check_coinTranslationPreservesClass_of_maskingSetup
pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean:436:noncomputable def check_coinTranslationPreservesClass_of_maskingSetup_AC0p
pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean:1258:noncomputable def check_coin_distinguisher_family_of_adjacentBiasMCSP
pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean:1263:noncomputable def check_circuit_coin_distinguisher_family_of_adjacentBiasMCSP_circuit
pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean:1287:noncomputable def check_coin_distinguisher_family_of_adjacentBiasMCSP_solves
pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean:1321:noncomputable def check_half_vs_fair_coin_distinguisher_family
pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean:1333:noncomputable def check_circuit_coin_distinguisher_family_translate_to_halfVsFair
pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean:1458:noncomputable def check_adjacent_bias_to_half_vs_fair_coin_solver_translation_contract
pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean:1486:noncomputable def check_half_vs_fair_mcsp_coin_rejection_contract_of_biasedLowComplexityMassFacts
pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean:1570:noncomputable def check_half_vs_fair_mcsp_coin_language
pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean:1576:noncomputable def check_half_vs_fair_mcsp_coin_asymptotic_language
pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean:1697:noncomputable def check_ac0p_coin_quantitative_language
pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean:1834:noncomputable def check_treeMCSPPredicateDecision
pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean:1866:noncomputable def check_treeMCSPPredicateOracle
pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean:1975:noncomputable def check_tree_mcsp_count_ratio
pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean:1979:noncomputable def check_exact_tree_mcsp_threshold_language
pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean:2101:noncomputable def check_CKLM_formulaCircuit_language
pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean:2111:noncomputable def check_CKLM_formulaCircuit_quantitative_language
pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean:2121:noncomputable def check_formulaCircuit_asymptotic_language
pnp3/Complexity/PpolyFormula_from_PpolyDAG_FixedSlice.lean:33:noncomputable def toFormula {n : Nat} (C : DagCircuit n) : FormulaCircuit n :=
pnp3/Complexity/Interfaces.lean:528:noncomputable def concatBitstring {n m : Nat} (x : Bitstring n) (w : Bitstring m) :
pnp3/Counting/ShannonCounting.lean:119:noncomputable def circuitToTable {n : Nat} (C : Circuit n) : TotalFunction n :=
pnp3/Counting/ShannonCounting.lean:146:noncomputable def easyFunctions (n s : Nat) : Finset (TotalFunction n) :=
pnp3/Counting/ShannonCounting.lean:163:noncomputable def yesInputSet (p : GapPartialMCSPParams) :
pnp3/Counting/ShannonCounting.lean:169:noncomputable def easyRawEncodingUnion (p : GapPartialMCSPParams) :
pnp3/Counting/ShannonCounting.lean:277:noncomputable def consistentFinset {n : Nat} (T : PartialFunction n) :
pnp3/Counting/Count_EasyFuncs.lean:86:noncomputable def allFunctionsFamily (n : Nat) : Core.Family n :=
pnp3/Models/PartialTruthTable.lean:587:noncomputable def tablesWithDefinedSet {n : Nat}
pnp3/Models/PartialTruthTable.lean:743:noncomputable def consistentPartialEquiv {n : Nat} (f : TotalFunction n) :
pnp3/Models/PartialTruthTable.lean:945:noncomputable def rawEncodingsConsistentWithTotal {n : Nat}
pnp3/Models/PartialTruthTable.lean:1068:noncomputable def consistentTotalEquiv {n : Nat} (T : PartialFunction n) :
pnp3/Models/PartialTruthTable.lean:1111:noncomputable def tablesWithDefinedSetList {n : Nat}
pnp3/Models/Model_PartialMCSP.lean:539:noncomputable def gapPartialMCSP_AsymptoticLanguage
pnp3/Models/Model_PartialMCSP.lean:560:noncomputable def gapPartialMCSP_Language (p : GapPartialMCSPParams) : Language := by
pnp3/Counting/BinomialBounds.lean:172:noncomputable def unionBound (D k : Nat) : Nat :=
pnp3/Counting/BinomialBounds.lean:542:noncomputable def hammingBallBudget (N : Nat) (ε : Rat) : Nat :=
pnp3/Counting/BinomialBounds.lean:550:noncomputable def hammingBallBound
pnp3/Counting/BinomialBounds.lean:916:noncomputable def capacityBound
pnp3/Counting/Atlas_to_LB_Core.lean:816:noncomputable def approxWitness
pnp3/Counting/Atlas_to_LB_Core.lean:1036:noncomputable def approxOnTestsetWitness
pnp3/ThirdPartyFacts/Facts_Switching.lean:92:noncomputable def leafOf {n : Nat} {leaves : List (Subcube n)}
pnp3/ThirdPartyFacts/Facts_Switching.lean:327:noncomputable def shrinkage_negDnfFamily_to_dnf
pnp3/ThirdPartyFacts/Facts_Switching.lean:872:noncomputable def shrinkage_negDnfFamily_to_dnf_canonicalCCDT
pnp3/ThirdPartyFacts/Facts_Switching.lean:976:noncomputable def dnfToSubcubes {n : Nat} (F : DNF n)
pnp3/ThirdPartyFacts/Facts_Switching.lean:1071:noncomputable def subcubes {params : AC0Parameters} (c : AC0Circuit params) :
pnp3/ThirdPartyFacts/Facts_Switching.lean:1120:noncomputable def allSubcubes
pnp3/ThirdPartyFacts/Facts_Switching.lean:1212:noncomputable def ac0AllTermSubcubes
pnp3/ThirdPartyFacts/Facts_Switching.lean:1341:noncomputable def ac0AllPDTLeaves
pnp3/ThirdPartyFacts/Facts_Switching.lean:1459:noncomputable def ac0DepthBoundWitness_of_weak
pnp3/ThirdPartyFacts/Facts_Switching.lean:1607:noncomputable def ac0DepthBoundWitness_of_polylog
pnp3/ThirdPartyFacts/Facts_Switching.lean:2253:noncomputable def ac0PartialWitness
pnp3/ThirdPartyFacts/Facts_Switching.lean:2280:noncomputable def ac0PartialWitness_with_bound
pnp3/ThirdPartyFacts/Facts_Switching.lean:2310:noncomputable def ac0PartialWitness_with_polylog
pnp3/ThirdPartyFacts/Facts_Switching.lean:2334:noncomputable def partialCertificate_level_from_AC0
pnp3/ThirdPartyFacts/Facts_Switching.lean:2340:noncomputable def partialCertificate_from_AC0
pnp3/ThirdPartyFacts/Facts_Switching.lean:2694:noncomputable def localCircuitWitness
pnp3/ThirdPartyFacts/Facts_Switching.lean:2713:noncomputable def commonPDT_from_localCircuit
pnp3/ThirdPartyFacts/Facts_Switching.lean:2734:noncomputable def atlas_from_localCircuit
pnp3/ThirdPartyFacts/Facts_Switching.lean:2773:noncomputable def certificate_from_AC0
pnp3/ThirdPartyFacts/Facts_Switching.lean:2788:noncomputable def certificate_from_AC0_with_bound
pnp3/ThirdPartyFacts/Facts_Switching.lean:2807:noncomputable def certificate_from_AC0_with_polylog
pnp3/ThirdPartyFacts/Facts_Switching.lean:3059:noncomputable def commonPDT_from_AC0
pnp3/ThirdPartyFacts/Facts_Switching.lean:3085:noncomputable def commonPDT_from_AC0_with_polylog
pnp3/ThirdPartyFacts/Facts_Switching.lean:3247:noncomputable def atlas_from_AC0
pnp3/ThirdPartyFacts/Facts_Switching.lean:3253:noncomputable def atlas_from_AC0_with_polylog
pnp3/ThirdPartyFacts/PpolyFormula.lean:115:noncomputable def trivialFormulaizer (p : GapPartialMCSPParams) :
pnp3/Magnification/FinalResultMainline.lean:191:noncomputable def eventualCanonicalBridge_of_asymptotic
pnp3/Magnification/FinalResultMainline.lean:291:noncomputable def promiseYesSubcubeCertificateAt_of_eventualPromiseYesWeakRoute
pnp3/Magnification/UnconditionalResearchGap.lean:147:noncomputable def researchGapWitness : ResearchGapWitness := by
pnp3/Magnification/FinalResultAuditRoutes.lean:767:noncomputable def defaultAsymptoticFormulaTrackData
pnp3/AC0/MultiSwitching/CommonCCDT.lean:70:noncomputable def firstPendingIndex?
pnp3/AC0/MultiSwitching/CommonCCDT.lean:80:noncomputable def firstPendingFormula?
pnp3/AC0/MultiSwitching/CommonCCDT.lean:141:noncomputable def commonCCDT_CNF_aux
pnp3/AC0/MultiSwitching/CommonCCDT.lean:167:noncomputable def commonCCDTAlgorithmCNF
pnp3/AC0/MultiSwitching/CommonCCDT_Func.lean:264:noncomputable def commonCCDT_CNF_atom
pnp3/AC0/MultiSwitching/CommonCCDT_Func.lean:287:noncomputable def commonCCDT_Family_atom
pnp3/AC0/MultiSwitching/ShrinkageFromGood.lean:52:noncomputable def allPointSubcubes (n : Nat) : List (Subcube n) :=
pnp3/AC0/MultiSwitching/ShrinkageFromGood.lean:55:noncomputable def selectorsOfFunction {n : Nat} (f : Core.BitVec n → Bool) :
pnp3/AC0/MultiSwitching/ShrinkageFromGood.lean:266:noncomputable def defaultBitVec (n : Nat) : Core.BitVec n := fun _ => false
pnp3/AC0/MultiSwitching/ShrinkageFromGood.lean:268:noncomputable def leafValue {n : Nat} (β : Subcube n) (f : Core.BitVec n → Bool) : Bool :=
pnp3/AC0/MultiSwitching/ShrinkageFromGood.lean:271:noncomputable def selectorsFromLeaves {n : Nat} (t : PDT n)
pnp3/AC0/MultiSwitching/EncodingCommon_Func.lean:34:noncomputable def auxSimpleOfCommonTrace_atom
pnp3/AC0/MultiSwitching/EncodingCommon_Func.lean:42:noncomputable def auxOfCommonTrace_atom
pnp3/AC0/MultiSwitching/EncodingCommon_Func.lean:107:noncomputable def encodeBadFamilyDetCommon_aux_atom
pnp3/AC0/MultiSwitching/EncodingCommon_Func.lean:127:noncomputable def decodeBadFamilyDetCommon_aux_atom
pnp3/AC0/MultiSwitching/CanonicalDT.lean:31:noncomputable def chooseFreeLiteral
pnp3/AC0/MultiSwitching/CanonicalDT.lean:57:noncomputable def canonicalDT_CNF_aux
pnp3/AC0/MultiSwitching/CanonicalDT.lean:136:noncomputable def canonicalDT_CNF
pnp3/AC0/MultiSwitching/CanonicalDT.lean:203:noncomputable def firstLiveTerm? {n : Nat} (ρ : Restriction n) :
pnp3/AC0/MultiSwitching/CanonicalDT.lean:211:noncomputable def chooseFirstLiteral
pnp3/AC0/MultiSwitching/CanonicalDT.lean:231:noncomputable def canonicalDT_DNF_aux
pnp3/AC0/MultiSwitching/CanonicalDT.lean:312:noncomputable def canonicalDT_DNF
pnp3/AC0/MultiSwitching/CanonicalDT.lean:387:noncomputable def canonicalCCDT_CNF_aux
pnp3/AC0/MultiSwitching/TraceBridge.lean:106:noncomputable def firstBadIndexDet
pnp3/AC0/MultiSwitching/TraceBridge.lean:122:noncomputable def firstBadTraceDet
pnp3/AC0/MultiSwitching/TraceBridge.lean:162:noncomputable def chooseFreeLiteralChoice
pnp3/AC0/MultiSwitching/Encoding.lean:235:noncomputable def traceStepCode
pnp3/AC0/MultiSwitching/Encoding.lean:243:noncomputable def traceCodeOfTrace
pnp3/AC0/MultiSwitching/Encoding.lean:255:noncomputable def bitFixOfTraceStepCode
pnp3/AC0/MultiSwitching/Encoding.lean:259:noncomputable def auxSimpleOfTraceCode
pnp3/AC0/MultiSwitching/Encoding.lean:533:noncomputable def auxSimpleOfTrace
pnp3/AC0/MultiSwitching/Encoding.lean:560:noncomputable def literalIndexInClause
pnp3/AC0/MultiSwitching/Encoding.lean:628:noncomputable def literalIndexInClauseFin
pnp3/AC0/MultiSwitching/Encoding.lean:647:noncomputable def auxTraceSmallStepsList
pnp3/AC0/MultiSwitching/Encoding.lean:668:noncomputable def auxTraceSmallOfTrace
pnp3/AC0/MultiSwitching/Encoding.lean:679:noncomputable def traceAdviceOfTrace
pnp3/AC0/MultiSwitching/Encoding.lean:691:noncomputable def decodeAuxSimple
pnp3/AC0/MultiSwitching/Encoding.lean:790:noncomputable def canonicalTraceOfBadFamily
pnp3/AC0/MultiSwitching/Encoding.lean:799:noncomputable def familyTraceCodeSmallOfBad
pnp3/AC0/MultiSwitching/Encoding.lean:811:noncomputable def familyTraceCodeSmallOfBadDet
pnp3/AC0/MultiSwitching/Encoding.lean:847:noncomputable def encodeBadFamilyCNF
pnp3/AC0/MultiSwitching/Encoding.lean:881:noncomputable def encodeBadFamilyDetCNF
pnp3/AC0/MultiSwitching/Encoding.lean:905:noncomputable def decodeBadFamilyDetCNF
pnp3/AC0/MultiSwitching/Encoding.lean:1158:noncomputable def encodeBadFamilyDetCNF_small
pnp3/AC0/MultiSwitching/Encoding.lean:1211:noncomputable def decode_small_step
pnp3/AC0/MultiSwitching/Encoding.lean:1230:noncomputable def decode_small
pnp3/AC0/MultiSwitching/Encoding.lean:1367:noncomputable def encodeBadFamilyDetCNF_var
pnp3/AC0/MultiSwitching/Encoding.lean:1394:noncomputable def decodeBadFamilyDetCNF_var
pnp3/AC0/MultiSwitching/Encoding.lean:1442:noncomputable def auxOfTraceStep
pnp3/AC0/MultiSwitching/Encoding.lean:1451:noncomputable def auxOfTrace
pnp3/AC0/MultiSwitching/Encoding.lean:1478:noncomputable def auxSimpleOfAux
pnp3/AC0/MultiSwitching/Encoding.lean:1492:noncomputable def encodeBadFamilyDetCNF_aux
pnp3/AC0/MultiSwitching/Encoding.lean:1516:noncomputable def decodeBadFamilyDetCNF_aux
pnp3/AC0/MultiSwitching/Encoding.lean:1589:noncomputable def canonicalDepthAt
pnp3/AC0/MultiSwitching/Encoding.lean:1606:noncomputable def maxDepthIndexList
pnp3/AC0/MultiSwitching/Encoding.lean:1622:noncomputable def maxDepthIndex?
pnp3/AC0/MultiSwitching/Encoding.lean:1736:noncomputable def canonicalCCDTAlgorithmCNF
pnp3/AC0/MultiSwitching/Encoding.lean:1868:noncomputable def encodeBadEvent_canonicalCCDT
pnp3/AC0/MultiSwitching/Encoding.lean:1957:noncomputable def decodeBadFamilyCNF
pnp3/AC0/MultiSwitching/Encoding.lean:1992:noncomputable def encodeBadCNF
pnp3/AC0/MultiSwitching/Encoding.lean:2014:noncomputable def decodeBadCNF
pnp3/AC0/MultiSwitching/Encoding.lean:2110:noncomputable def encodingWitness_canonicalCCDT_CNF
pnp3/AC0/MultiSwitching/EncodingCommon.lean:52:noncomputable def auxSimpleOfCommonTrace
pnp3/AC0/MultiSwitching/EncodingCommon.lean:60:noncomputable def auxOfCommonTrace
pnp3/AC0/MultiSwitching/EncodingCommon.lean:132:noncomputable def encodeBadFamilyDetCommon_aux
pnp3/AC0/MultiSwitching/EncodingCommon.lean:153:noncomputable def decodeBadFamilyDetCommon_aux
pnp3/AC0/MultiSwitching/Trace.lean:93:noncomputable def stepOfSelection
pnp3/AC0/MultiSwitching/Trace.lean:108:noncomputable def stepsList :
pnp3/AC0/MultiSwitching/Trace.lean:126:noncomputable def toTrace
pnp3/AC0/MultiSwitching/Trace.lean:156:noncomputable def traceOfBadCNF {F : CNF n w} {t : Nat} {ρ : Restriction n}
pnp3/AC0/MultiSwitching/Trace.lean:192:noncomputable def firstBadIndex
pnp3/AC0/MultiSwitching/Trace.lean:209:noncomputable def firstBadTrace
pnp3/Magnification/AuditRoutes/DistinguisherMatrixProvenance/V_codexd3a/AntiCollapsePrime.lean:111:noncomputable def payloadFarNoSet (n ρ : Nat) : Finset (Bitstring n) := by
pnp3/Magnification/AC0LocalityBridge.lean:383:noncomputable def semanticSingletonWitness {n : Nat}
pnp3/Magnification/AC0LocalityBridge.lean:1091:noncomputable def current_singleton_preSingleton_selector_package
pnp3/Magnification/AC0LocalityBridge.lean:1356:noncomputable def formulaSemanticMultiSwitchingProvider_internal :
pnp3/Magnification/AC0LocalityBridge.lean:1418:noncomputable def semanticSwitchingCertificate_internal
pnp3/Magnification/LocalityProvider_Partial.lean:17:noncomputable def generalSolverOfFormula
pnp3/Magnification/LocalityProvider_Partial.lean:588:noncomputable def formulaRestrictionCertificateDataPartial_fromPipeline_of_old
pnp3/Magnification/LocalityProvider_Partial.lean:744:noncomputable def factsAssignmentOfSubcube {n : Nat}
pnp3/Magnification/LocalityProvider_Partial.lean:752:noncomputable def factsRestrictionOfSubcube {n : Nat}
pnp3/Magnification/LocalityProvider_Partial.lean:1218:noncomputable def
pnp3/Magnification/LocalityProvider_Partial.lean:1233:noncomputable def
pnp3/Magnification/LocalityProvider_Partial.lean:1246:noncomputable def restrictedBehaviorSem
pnp3/Magnification/LocalityProvider_Partial.lean:1259:noncomputable def restrictedBehaviorWitness
pnp3/Magnification/LocalityProvider_Partial.lean:1693:noncomputable def
pnp3/Magnification/LocalityProvider_Partial.lean:2555:noncomputable def formulaRestrictionCertificateData_of_generic_extracted_local_core_provider
pnp3/Magnification/LocalityProvider_Partial.lean:2566:noncomputable def formulaRestrictionCertificateData_of_supportBounds
pnp3/Magnification/LocalityProvider_Partial.lean:2666:noncomputable def formulaRestrictionCertificateData_fromPipeline_of_supportBoundsFromPipeline
pnp3/Magnification/LocalityProvider_Partial.lean:2763:noncomputable def defaultFormulaRestrictionCertificateDataPartial
pnp3/Magnification/LocalityProvider_Partial.lean:2830:noncomputable def formulaCertificateProvider_of_restrictionData
pnp3/Magnification/LocalityProvider_Partial.lean:2936:noncomputable def formulaCertificateProvider_fromPipeline_of_restrictionData_fromPipeline
pnp3/Magnification/LocalityProvider_Partial.lean:3008:noncomputable def structuredLocalityProviderPartial_fromPipeline_of_formulaCertificate_fromPipeline
pnp3/Magnification/LocalityProvider_Partial.lean:3047:noncomputable def structuredLocalityProviderPartial_fromPipeline_of_supportBoundsFromPipeline
pnp3/Magnification/LocalityProvider_Partial.lean:3102:noncomputable def formulaToGeneralLocalityData_of_halfSize
pnp3/Magnification/LocalityProvider_Partial.lean:3114:noncomputable def constructiveLocalityEnginePartial_of_formulaData
pnp3/Magnification/LocalityProvider_Partial.lean:3140:noncomputable def constructiveLocalityEnginePartial_of_formulaCertificate
pnp3/Magnification/LocalityProvider_Partial.lean:3498:noncomputable def directStructuredLocalityProviderContract_of_restrictionData
pnp3/Magnification/LocalityProvider_Partial.lean:3506:noncomputable def directStructuredLocalityProviderContract_of_supportBounds
pnp3/Magnification/LocalityProvider_Partial.lean:3515:noncomputable def directStructuredLocalityProviderContract_of_multiswitching_contract
pnp3/Magnification/LocalityProvider_Partial.lean:3552:noncomputable def defaultFormulaCertificateProviderPartial
pnp3/Tests/WeakRouteSurfaceTests.lean:690:noncomputable def check_dagUniformAcceptanceProbOnTotalsOfCircuit
pnp3/Tests/WeakRouteSurfaceTests.lean:697:noncomputable def check_dagSeedAcceptanceProbOnTotalsOfCircuit
pnp3/Tests/WeakRouteSurfaceTests.lean:877:noncomputable def check_canonicalEasyFamilyFinset
pnp3/Tests/WeakRouteSurfaceTests.lean:948:noncomputable def check_canonicalEasyRejectProbOnFamilyOfCircuit
pnp3/Tests/WeakRouteSurfaceTests.lean:1076:noncomputable def check_canonicalWitnessEasyDensitySourceAt_of_supportBudget
pnp3/Tests/WeakRouteSurfaceTests.lean:1274:noncomputable def check_promiseYesAcceptanceInvariantAtProviderOnSlices_of_promiseValueLocalityPackageProvider :
pnp3/Tests/WeakRouteSurfaceTests.lean:1307:noncomputable def check_dagStableRestrictionInvariantPackage_of_inPpolyDAG_supportHalf :
pnp3/Tests/WeakRouteSurfaceTests.lean:1321:noncomputable def check_dagStableRestrictionInvariantProvider_of_inPpolyDAG_supportHalf :
pnp3/Tests/WeakRouteSurfaceTests.lean:1348:noncomputable def check_dagRouteBSourceClosure_of_blocker :
pnp3/Tests/WeakRouteSurfaceTests.lean:1523:noncomputable def check_formulaRestrictionCertificateDataPartial_of_nontrivialSAlternativeProducerRoute :
pnp3/Tests/WeakRouteSurfaceTests.lean:1532:noncomputable def check_nontrivialSAlternativeProducerRoute_of_promiseValuePackageAndSupportBounds :
pnp3/Tests/WeakRouteSurfaceTests.lean:1543:noncomputable def check_formulaSupportRestrictionBoundsPartial_of_nontrivialSSliceSource :
pnp3/Tests/WeakRouteSurfaceTests.lean:1554:noncomputable def check_hasDefaultStructuredLocalityProviderPartial_of_nontrivialSSliceSource :
pnp3/Tests/WeakRouteSurfaceTests.lean:1565:noncomputable def check_formulaSupportRestrictionBoundsPartial_of_nontrivialSSliceSource_andMultiswitching :
pnp3/Tests/WeakRouteSurfaceTests.lean:1576:noncomputable def check_hasDefaultStructuredLocalityProviderPartial_of_nontrivialSSliceSource_andMultiswitching :
pnp3/Tests/WeakRouteSurfaceTests.lean:1633:noncomputable def check_promiseYesAcceptanceInvariantAtNontrivialS_of_promiseValueLocalityPackageAt :
pnp3/Tests/WeakRouteSurfaceTests.lean:1645:noncomputable def
pnp3/Tests/WeakRouteSurfaceTests.lean:1657:noncomputable def check_promiseYesSlackOnInvariantProviderOnSlices_of_promiseValueLocalityPackageProvider :
pnp3/Tests/WeakRouteSurfaceTests.lean:1671:noncomputable def check_noSmallDAG_of_promiseValueLocalityPackageProviderOnSlices_viaSemanticAndSlack :
pnp3/LowerBounds/SingletonDensityEndpoint.lean:100:noncomputable def naturalMismatchTestsetOfSingletonDensityPackage
pnp3/LowerBounds/LB_Formulas.lean:73:noncomputable def approxSubtypeOf
pnp3/LowerBounds/LB_Formulas.lean:134:noncomputable def scenarioCapacity {n : Nat} (sc : BoundedAtlasScenario n) : Nat :=
pnp3/LowerBounds/LB_Formulas.lean:244:noncomputable def BoundedAtlasScenario.ofCommonPDT
pnp3/LowerBounds/LB_Formulas.lean:285:noncomputable def BoundedAtlasScenario.ofShrinkage
pnp3/LowerBounds/LB_Formulas.lean:324:noncomputable def scenarioFromCommonPDT
pnp3/LowerBounds/LB_Formulas.lean:367:noncomputable def scenarioFromPartialCertificate
pnp3/LowerBounds/LB_Formulas.lean:721:noncomputable def scenarioFromShrinkage
pnp3/LowerBounds/LB_Formulas.lean:820:noncomputable def scenarioFromAC0
pnp3/LowerBounds/LB_Formulas.lean:859:noncomputable def scenarioFromAC0_with_bound
pnp3/LowerBounds/LB_Formulas.lean:898:noncomputable def scenarioFromAC0_with_polylog
pnp3/LowerBounds/LB_Formulas.lean:1027:noncomputable def scenarioFromLocalCircuit
pnp3/LowerBounds/LB_Formulas.lean:2259:noncomputable def scenarioBudgetFromAC0
pnp3/LowerBounds/LB_Formulas.lean:2305:noncomputable def scenarioBudgetFromLocal
pnp3/LowerBounds/AntiChecker_Partial.lean:355:noncomputable def consistentPartialsFinset {n : Nat} (f : TotalTable n) :
pnp3/LowerBounds/AntiChecker_Partial.lean:484:noncomputable def familyOfPartialSets {n : Nat} (F : Finset (TotalTable n)) :
pnp3/LowerBounds/AntiChecker_Partial.lean:489:noncomputable def unionPartialSets {n : Nat} (F : Finset (TotalTable n)) :
pnp3/LowerBounds/AntiChecker_Partial.lean:730:noncomputable def exists_hard_of_outside_family {n : Nat} (F : Finset (TotalTable n))
pnp3/LowerBounds/AntiChecker_Partial.lean:739:noncomputable def exists_hard_if_card_lt {n : Nat} (F : Finset (TotalTable n))
pnp3/LowerBounds/AntiChecker_Partial.lean:747:noncomputable def exists_hard_if_card_lt_tableLen {n : Nat} (F : Finset (TotalTable n))
pnp3/LowerBounds/AntiChecker_Partial.lean:1057:noncomputable def ac0SyntacticEasyFunctionsFinset
pnp3/LowerBounds/AntiChecker_Partial.lean:1065:noncomputable def AC0SyntacticEasyFamily
pnp3/LowerBounds/AntiChecker_Partial.lean:1097:noncomputable def AC0EasyFamily (params : ThirdPartyFacts.AC0Parameters) :
pnp3/LowerBounds/AntiChecker_Partial.lean:1147:noncomputable def ac0EasyFamilyData_of_syntacticHypotheses
pnp3/LowerBounds/AntiChecker_Partial.lean:1212:noncomputable def stepCSyntacticLiftDataPartial_default
pnp3/LowerBounds/AntiChecker_Partial.lean:1250:noncomputable def stepCClosureData_of_syntacticLift
pnp3/LowerBounds/AntiChecker_Partial.lean:1267:noncomputable def constructiveSmallAC0Solver_of_syntacticLift
pnp3/LowerBounds/AntiChecker_Partial.lean:1538:noncomputable def stepCClosureProvider_of_easyFamilyData
pnp3/LowerBounds/AntiChecker_Partial.lean:1564:noncomputable def stepCClosureProvider_of_constructive
pnp3/LowerBounds/AntiChecker_Partial.lean:1589:noncomputable def stepCClosureProvider_of_syntacticLift
pnp3/LowerBounds/RouteBSourceClosure.lean:49:noncomputable def dagRouteBSourceClosure_of_blocker
pnp3/LowerBounds/SingletonDensityContradiction.lean:299:noncomputable def abstractGapLocalityPayload_of_exists_locality
pnp3/LowerBounds/SingletonDensityContradiction.lean:316:noncomputable def abstractGapStableRestrictionPayload_of_exists_stableRestriction
pnp3/LowerBounds/SingletonDensityContradiction.lean:656:noncomputable def abstractGapWitnessedPayload_of_exists_nonemptyWitness
pnp3/LowerBounds/SingletonDensityContradiction.lean:1286:noncomputable def abstractLinkedSingletonDensityPayload_of_singletonDensityPackage
pnp3/LowerBounds/SingletonDensityContradiction.lean:1304:noncomputable def abstractTargetedSingletonDensityPayload_of_singletonDensityPackage
pnp3/LowerBounds/SingletonDensityContradiction.lean:1323:noncomputable def abstractGapTargetedSingletonDensityPayload_of_singletonDensityPackage
pnp3/LowerBounds/SingletonDensityContradiction.lean:1556:noncomputable def dagCanonicalPayload
pnp3/LowerBounds/SingletonDensityContradiction.lean:1603:noncomputable def dagScenarioWitness
pnp3/LowerBounds/SingletonDensityContradiction.lean:1834:noncomputable def dagWitnessedPayload
pnp3/LowerBounds/SingletonDensityContradiction.lean:1890:noncomputable def dagCubeSoundWitnessPayload
pnp3/LowerBounds/SingletonDensityContradiction.lean:1913:noncomputable def dagSelectorProvenancePayload
pnp3/LowerBounds/SingletonDensityContradiction.lean:2020:noncomputable def dagCandidateRestrictionOfSubcube
pnp3/LowerBounds/SingletonDensityContradiction.lean:2632:noncomputable def naturalMismatchTestsetOfAbstractSingletonDensityPayload
pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean:133:noncomputable def inPpolyDAGFamilyOnSlices_of_PpolyDAG
pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean:1296:noncomputable def canonicalGlobalLanguageEventually
pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean:1429:noncomputable def bridgeEventually_of_sliceConst
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:251:noncomputable def dagStableRestrictionInvariantPackage_of_inPpolyDAG_supportHalf
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:285:noncomputable def dagStableRestrictionInvariantProvider_of_inPpolyDAG_supportHalf
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:305:noncomputable def dagStableRestrictionInvariantProvider_of_supportHalfObligation
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:319:noncomputable def dagStableRestrictionCertificateProvider_of_inPpolyDAG_supportHalf
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:636:noncomputable def smallDAGWitnessRestrictionExtractionAt_of_support
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:705:noncomputable def smallDAGWitnessRestrictionExtractionProviderOnSlices_of_support
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:1464:noncomputable def smallDAGWitnessShrinkageCertificateAt_of_restrictionData
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:1498:noncomputable def smallDAGWitnessShrinkageCertificateProviderOnSlices_of_restrictionDataProvider
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:1531:noncomputable def dagStableRestrictionSlackPackageAt_of_restrictionExtractionAndHalfBound
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:1591:noncomputable def dagStableRestrictionSlackPackageAt_of_supportHalfBound
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:1610:noncomputable def dagStableRestrictionSlackPackageAt_of_restrictionExtractionAndNumeric
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:1636:noncomputable def dagStableRestrictionSlackPackageAt_of_shrinkageCertificate
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:1704:noncomputable def dagStableRestrictionSlackPackageAtProviderOnSlices_of_supportHalfBound
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:1719:noncomputable def dagStableRestrictionSlackPackageAtProviderOnSlices_of_shrinkageCertificateProvider
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:1731:noncomputable def dagStableRestrictionSlackPackageAtProviderOnSlices_of_restrictionExtractionAndNumericProvider
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:1815:noncomputable def requiredComplementBudget (p : GapPartialMCSPParams) : Nat :=
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:1855:noncomputable def promiseValueLocalityPackageAt_of_dagStableRestrictionSlackPackageAt_valueSupported
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:1928:noncomputable def promiseValueLocalityPackageAt_of_supportHalfBound_valueSupported
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:2051:noncomputable def acceptedFamilyCertificateAt_of_dagStableRestrictionSlackPackageAt
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:2218:noncomputable def acceptedFamilyCertificateAtProviderOnSlices_of_dagStableRestrictionSlackPackageAtProvider
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:2675:noncomputable def formulaRestrictionCertificateDataPartial_of_nontrivialSAlternativeProducerRoute
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:2768:noncomputable def promiseYesDecisionCertificateAt_of_promiseValueLocalityPackageAt
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:3119:noncomputable def promiseYesAcceptanceInvariantAt_of_promiseValueLocalityPackageAt
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:3265:noncomputable def promiseYesAcceptanceInvariantAtNontrivialS_of_promiseValueLocalityPackageAt
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:3288:noncomputable def
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:3305:noncomputable def nontrivialSAlternativeProducerRoute_of_promiseValuePackageAndSupportBounds
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:3394:noncomputable def promiseYesSubcubeCertificateAt_of_promiseValueLocalityPackageAt
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:3408:noncomputable def promiseYesSourceDecompositionAt_of_promiseValueLocalityPackageAt
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:3424:noncomputable def promiseYesSubcubeCertificateAt_of_dagStableRestrictionSlackPackageAt_valueSupported
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:3443:noncomputable def promiseYesSubcubeCertificateAt_of_supportHalfBound_valueSupported
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:3520:noncomputable def promiseYesAcceptanceInvariantAtProviderOnSlices_of_promiseValueLocalityPackageProvider
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:3547:noncomputable def promiseYesSubcubeCertificateAtProviderOnSlices_of_promiseValueLocalityPackageProvider_viaSemanticAndSlack
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:3563:noncomputable def promiseYesSubcubeCertificateAtProviderOnSlices_of_promiseValueLocalityPackageProvider
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:3737:noncomputable def acceptedFamilyCertificateAt_of_yesSubcubeCertificateAt
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:3792:noncomputable def yesSubcubeFamily
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:3885:noncomputable def acceptedFamilyCertificateAtProviderOnSlices_of_yesSubcubeCertificateProvider
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:3963:noncomputable def acceptanceRatioOnFinset
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:3986:noncomputable def dagUniformAcceptanceProbOnTotalsOfCircuit
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:4027:noncomputable def dagSeedAcceptanceProbOnTotalsOfCircuit
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:4094:noncomputable def dagUniformAcceptanceProbOnTotals
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:4164:noncomputable def dagSeedAcceptanceProbOnTotals
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:4320:noncomputable def canonicalEasyFamilyFinset
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:4924:noncomputable def canonicalEasyRejectProbOnFamilyOfCircuit
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:4934:noncomputable def canonicalEasyRejectProbOnFamily
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:5266:noncomputable def canonicalWitnessEasyDensitySourceAt_of_supportBudget
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:6320:noncomputable def canonicalWitnessEasyDensitySourceProviderOnSlices_of_extractionBudget
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:6356:noncomputable def canonicalWitnessEasyDensitySourceProviderOnSlices_of_supportBudget
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:6588:noncomputable def canonical_smallDAG_witnessEasyDensity_source_on_slices_of_extractionBudget
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:6631:noncomputable def canonical_smallDAG_witnessEasyDensity_source_on_slices_of_supportBudget
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:6665:noncomputable def canonical_smallDAG_witnessUniformLower_source_on_slices_of_supportBudget
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:6700:noncomputable def canonical_smallDAG_witnessTransferQuarter_source_on_slices_of_supportBudget
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:6742:noncomputable def canonical_smallDAG_witnessEasyDensity_source_on_slices_of_supportHalfBoundFamily
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:6775:noncomputable def canonical_smallDAG_witnessUniformLower_source_on_slices_of_supportHalfBoundFamily
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:6808:noncomputable def canonical_smallDAG_witnessTransferQuarter_source_on_slices_of_supportHalfBoundFamily
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:7153:noncomputable def acceptedFamilyCertificateAt_of_prgImageAcceptanceAt
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:7189:noncomputable def acceptedFamilyCertificateAtProviderOnSlices_of_prgImageAcceptanceProvider
```

## `Classical.choose` audit
Most occurrences extract explicit witnesses from hypotheses (`PpolyFormula`, `PpolyDAG`, finite max/existence, support/restriction certificates). The suspicious class is not `Classical.choose` itself but choose-backed default/provider payloads used by final/vacuous routes. Full location list follows.
```text
pnp3/Core/BooleanBasics.lean:730:          Classical.choose (exists_of_ne_none (i := i) h)
pnp3/Core/BooleanBasics.lean:740:      have hval : Classical.choose (exists_of_ne_none (i := i) hne) = b := by
pnp3/Core/BooleanBasics.lean:741:        have : some (Classical.choose (exists_of_ne_none (i := i) hne)) = some b := by
pnp3/Core/BooleanBasics.lean:3150:  refine ⟨Classical.choose hassign, ?_⟩
pnp3/Core/BooleanBasics.lean:3151:  exact Classical.choose_spec hassign
pnp4/Pnp4/Frontier/ContractExpansion/C_DAG_Adapter.lean:48:  let c := Classical.choose h.polyBound_poly
pnp4/Pnp4/Frontier/ContractExpansion/C_DAG_Adapter.lean:49:  have hc : ∀ n, h.polyBound n ≤ n ^ c + c := Classical.choose_spec h.polyBound_poly
pnp4/Pnp4/AlgorithmsToLowerBounds/CoinMaskingTranslation.lean:493:  Classical.choose
pnp4/Pnp4/AlgorithmsToLowerBounds/CoinMaskingTranslation.lean:519:  Classical.choose_spec
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:354:    Classical.choose h
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:362:    Classical.choose h
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:384:  let i0 : Fin (M.tapeLength n) := Classical.choose hExists
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:385:  have hi0 : evalHead cc x i0 = true := Classical.choose_spec hExists
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:402:  let q0 : M.state := Classical.choose hExists
pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean:403:  have hq0 : evalState cc x q0 = true := Classical.choose_spec hExists
pnp3/Complexity/Interfaces.lean:535:      let t := Classical.choose (Nat.exists_eq_add_of_le hge)
pnp3/Complexity/Interfaces.lean:537:        Classical.choose_spec (Nat.exists_eq_add_of_le hge)
pnp3/Models/Model_PartialMCSP.lean:545:    let n : Nat := Classical.choose hShape
pnp3/Models/Model_PartialMCSP.lean:546:    have hN : N = Partial.inputLen n := Classical.choose_spec hShape
pnp3/ThirdPartyFacts/Facts_Switching.lean:94:  Classical.choose (hpart x)
pnp3/ThirdPartyFacts/Facts_Switching.lean:99:  have hspec := Classical.choose_spec (hpart x)
pnp3/ThirdPartyFacts/Facts_Switching.lean:106:  have hspec := Classical.choose_spec (hpart x)
pnp3/ThirdPartyFacts/Facts_Switching.lean:491:          let ρ0 := Classical.choose
pnp3/ThirdPartyFacts/Facts_Switching.lean:494:          let ρ1 := Classical.choose
pnp3/ThirdPartyFacts/Facts_Switching.lean:499:              (Classical.choose_spec
pnp3/ThirdPartyFacts/Facts_Switching.lean:504:              (Classical.choose_spec
pnp3/ThirdPartyFacts/Facts_Switching.lean:560:          let ρ0 := Classical.choose
pnp3/ThirdPartyFacts/Facts_Switching.lean:563:          let ρ1 := Classical.choose
pnp3/ThirdPartyFacts/Facts_Switching.lean:568:              (Classical.choose_spec
pnp3/ThirdPartyFacts/Facts_Switching.lean:573:              (Classical.choose_spec
pnp3/ThirdPartyFacts/Facts_Switching.lean:649:          let ρ0 := Classical.choose
pnp3/ThirdPartyFacts/Facts_Switching.lean:652:          let ρ1 := Classical.choose
pnp3/ThirdPartyFacts/Facts_Switching.lean:657:              (Classical.choose_spec
pnp3/ThirdPartyFacts/Facts_Switching.lean:662:              (Classical.choose_spec
pnp3/ThirdPartyFacts/Facts_Switching.lean:979:  List.pmap (fun t ht => Classical.choose ht) F.terms (by
pnp3/ThirdPartyFacts/Facts_Switching.lean:1006:          have hβ := Classical.choose_spec (hcons t List.mem_cons_self)
pnp3/ThirdPartyFacts/Facts_Switching.lean:1008:            (β := Classical.choose (hcons t List.mem_cons_self)) hβ x
pnp3/ThirdPartyFacts/Facts_Switching.lean:1011:              (List.pmap (fun t ht => Classical.choose ht) rest (by
pnp3/ThirdPartyFacts/Facts_Switching.lean:1017:              memB (Classical.choose (hcons t List.mem_cons_self)) x =
pnp3/ThirdPartyFacts/Facts_Switching.lean:1021:              (List.pmap (fun t ht => Classical.choose ht) rest (by
pnp3/ThirdPartyFacts/Facts_Switching.lean:1485:            (Classical.choose (witness.covers f hf)).subcubes
pnp3/ThirdPartyFacts/Facts_Switching.lean:1491:          let c := Classical.choose (witness.covers f hf)
pnp3/ThirdPartyFacts/Facts_Switching.lean:1492:          have hc : c ∈ witness.circuits := (Classical.choose_spec (witness.covers f hf)).left
pnp3/ThirdPartyFacts/Facts_Switching.lean:1507:          let c := Classical.choose (witness.covers f hf)
pnp3/ThirdPartyFacts/Facts_Switching.lean:1509:            (Classical.choose_spec (witness.covers f hf)).right
pnp3/ThirdPartyFacts/Facts_Switching.lean:1556:            (Classical.choose (witness.covers f hf)).subcubes
pnp3/ThirdPartyFacts/Facts_Switching.lean:1570:          let c := Classical.choose (witness.covers f hf)
pnp3/ThirdPartyFacts/Facts_Switching.lean:1572:            (Classical.choose_spec (witness.covers f hf)).right
pnp3/ThirdPartyFacts/Facts_Switching.lean:2230:от многократного обращения к `Classical.choose`.
pnp3/ThirdPartyFacts/Facts_Switching.lean:2259:  let ℓ := Classical.choose h
pnp3/ThirdPartyFacts/Facts_Switching.lean:2260:  let rest := Classical.choose_spec h
pnp3/ThirdPartyFacts/Facts_Switching.lean:2261:  let C := Classical.choose rest
pnp3/ThirdPartyFacts/Facts_Switching.lean:2262:  have hprop := Classical.choose_spec rest
pnp3/ThirdPartyFacts/Facts_Switching.lean:2287:  let ℓ := Classical.choose h
pnp3/ThirdPartyFacts/Facts_Switching.lean:2288:  let rest := Classical.choose_spec h
pnp3/ThirdPartyFacts/Facts_Switching.lean:2289:  let C := Classical.choose rest
pnp3/ThirdPartyFacts/Facts_Switching.lean:2290:  have hprop := Classical.choose_spec rest
pnp3/ThirdPartyFacts/Facts_Switching.lean:2317:  let ℓ := Classical.choose h
pnp3/ThirdPartyFacts/Facts_Switching.lean:2318:  let rest := Classical.choose_spec h
pnp3/ThirdPartyFacts/Facts_Switching.lean:2319:  let C := Classical.choose rest
pnp3/ThirdPartyFacts/Facts_Switching.lean:2320:  have hprop := Classical.choose_spec rest
pnp3/ThirdPartyFacts/PpolyFormula.lean:98:  refine ⟨{ polyBound := fun n => n ^ (Classical.choose (hF.familyPoly w)) + Classical.choose (hF.familyPoly w)
pnp3/ThirdPartyFacts/PpolyFormula.lean:103:  · refine ⟨Classical.choose (hF.familyPoly w), ?_⟩
pnp3/ThirdPartyFacts/PpolyFormula.lean:107:    exact Classical.choose_spec (hF.familyPoly w) n
pnp3/AC0/MultiSwitching/CommonBad.lean:241:              let ρ0 := Classical.choose
pnp3/AC0/MultiSwitching/CommonBad.lean:244:              let ρ1 := Classical.choose
pnp3/AC0/MultiSwitching/CommonBad.lean:249:                  (Classical.choose_spec
pnp3/AC0/MultiSwitching/CommonBad.lean:254:                  (Classical.choose_spec
pnp3/AC0/MultiSwitching/CommonBad.lean:437:          let ρ0 := Classical.choose
pnp3/AC0/MultiSwitching/CommonBad.lean:440:          let ρ1 := Classical.choose
pnp3/AC0/MultiSwitching/CommonBad.lean:445:              (Classical.choose_spec
pnp3/AC0/MultiSwitching/CommonBad.lean:450:              (Classical.choose_spec
pnp3/AC0/MultiSwitching/CommonCCDT.lean:156:          let ρ0 := Classical.choose
pnp3/AC0/MultiSwitching/CommonCCDT.lean:159:          let ρ1 := Classical.choose
pnp3/AC0/MultiSwitching/CommonCCDT.lean:263:              let ρ0 := Classical.choose
pnp3/AC0/MultiSwitching/CommonCCDT.lean:266:              let ρ1 := Classical.choose
pnp3/AC0/MultiSwitching/CommonCCDT.lean:365:              let ρ0 := Classical.choose
pnp3/AC0/MultiSwitching/CommonCCDT.lean:368:              let ρ1 := Classical.choose
pnp3/AC0/MultiSwitching/CommonCCDT.lean:373:                  (Classical.choose_spec
pnp3/AC0/MultiSwitching/CommonCCDT.lean:378:                  (Classical.choose_spec
pnp3/AC0/MultiSwitching/CommonCCDT.lean:475:              let ρ0 := Classical.choose
pnp3/AC0/MultiSwitching/CommonCCDT.lean:478:              let ρ1 := Classical.choose
pnp3/AC0/MultiSwitching/CommonCCDT.lean:483:                  (Classical.choose_spec
pnp3/AC0/MultiSwitching/CommonCCDT.lean:488:                  (Classical.choose_spec
pnp3/AC0/MultiSwitching/EncodingCommon_Func.lean:115:  let trace := Classical.choose hbad
pnp3/AC0/MultiSwitching/EncodingCommon_Func.lean:117:    Classical.choose_spec hbad
pnp3/AC0/MultiSwitching/EncodingCommon_Func.lean:140:  let trace := Classical.choose hbad
pnp3/AC0/MultiSwitching/EncodingCommon_Func.lean:142:    Classical.choose_spec hbad
pnp3/AC0/MultiSwitching/CanonicalDT.lean:34:  Classical.choose (List.exists_cons_of_ne_nil w.nonempty)
pnp3/AC0/MultiSwitching/CanonicalDT.lean:41:  rcases Classical.choose_spec (List.exists_cons_of_ne_nil w.nonempty) with ⟨tail, hspec⟩
pnp3/AC0/MultiSwitching/CanonicalDT.lean:73:          let ρ0 := Classical.choose
pnp3/AC0/MultiSwitching/CanonicalDT.lean:76:          let ρ1 := Classical.choose
pnp3/AC0/MultiSwitching/CanonicalDT.lean:105:    let ρ0 := Classical.choose
pnp3/AC0/MultiSwitching/CanonicalDT.lean:108:    let ρ1 := Classical.choose
pnp3/AC0/MultiSwitching/CanonicalDT.lean:118:      (Classical.choose_spec
pnp3/AC0/MultiSwitching/CanonicalDT.lean:124:      (Classical.choose_spec
pnp3/AC0/MultiSwitching/CanonicalDT.lean:158:          let ρ0 := Classical.choose
pnp3/AC0/MultiSwitching/CanonicalDT.lean:161:          let ρ1 := Classical.choose
pnp3/AC0/MultiSwitching/CanonicalDT.lean:213:  Classical.choose (List.exists_cons_of_ne_nil hfree)
pnp3/AC0/MultiSwitching/CanonicalDT.lean:219:  rcases Classical.choose_spec (List.exists_cons_of_ne_nil hfree) with ⟨tail, hspec⟩
pnp3/AC0/MultiSwitching/CanonicalDT.lean:252:            let ρ0 := Classical.choose
pnp3/AC0/MultiSwitching/CanonicalDT.lean:255:            let ρ1 := Classical.choose
pnp3/AC0/MultiSwitching/CanonicalDT.lean:283:    let ρ0 := Classical.choose
pnp3/AC0/MultiSwitching/CanonicalDT.lean:286:    let ρ1 := Classical.choose
pnp3/AC0/MultiSwitching/CanonicalDT.lean:295:      (Classical.choose_spec
pnp3/AC0/MultiSwitching/CanonicalDT.lean:301:      (Classical.choose_spec
pnp3/AC0/MultiSwitching/CanonicalDT.lean:346:              let ρ0 := Classical.choose
pnp3/AC0/MultiSwitching/CanonicalDT.lean:349:              let ρ1 := Classical.choose
pnp3/AC0/MultiSwitching/TraceBridge.lean:130:  exact Classical.choose (firstBadIndexDet_spec (F := F) (t := t) (ρ := ρ) hbad).2
pnp3/AC0/MultiSwitching/TraceBridge.lean:229:          let ρ0 := Classical.choose
pnp3/AC0/MultiSwitching/TraceBridge.lean:232:          let ρ1 := Classical.choose
pnp3/AC0/MultiSwitching/TraceBridge.lean:244:              (Classical.choose_spec
pnp3/AC0/MultiSwitching/TraceBridge.lean:250:              (Classical.choose_spec
pnp3/AC0/MultiSwitching/TraceBridge.lean:401:          let ρ0 := Classical.choose
pnp3/AC0/MultiSwitching/TraceBridge.lean:404:          let ρ1 := Classical.choose
pnp3/AC0/MultiSwitching/TraceBridge.lean:416:              (Classical.choose_spec
pnp3/AC0/MultiSwitching/TraceBridge.lean:422:              (Classical.choose_spec
pnp3/AC0/MultiSwitching/TraceBridge.lean:602:      let ρ0 := Classical.choose
pnp3/AC0/MultiSwitching/TraceBridge.lean:605:      let ρ1 := Classical.choose
pnp3/AC0/MultiSwitching/TraceBridge.lean:637:                (Classical.choose_spec
pnp3/AC0/MultiSwitching/TraceBridge.lean:659:                (Classical.choose_spec
pnp3/AC0/MultiSwitching/EncodingCommon.lean:140:  let trace := Classical.choose hbad
pnp3/AC0/MultiSwitching/EncodingCommon.lean:142:    Classical.choose_spec hbad
pnp3/AC0/MultiSwitching/EncodingCommon.lean:166:  let trace := Classical.choose hbad
pnp3/AC0/MultiSwitching/EncodingCommon.lean:168:    Classical.choose_spec hbad
pnp3/Counting/Atlas_to_LB_Core.lean:826:    let g := Classical.choose f.property
pnp3/Counting/Atlas_to_LB_Core.lean:827:    have hg : g ∈ UnionClass R k := (Classical.choose_spec f.property).1
pnp3/Counting/Atlas_to_LB_Core.lean:829:      (Classical.choose_spec f.property).2
pnp3/Counting/Atlas_to_LB_Core.lean:1046:    let g := Classical.choose hf
pnp3/Counting/Atlas_to_LB_Core.lean:1047:    have hWitness := Classical.choose_spec hf
pnp3/Counting/Atlas_to_LB_Core.lean:1065:    set g₁ := Classical.choose h₁
pnp3/Counting/Atlas_to_LB_Core.lean:1066:    set g₂ := Classical.choose h₂
pnp3/Magnification/FinalResultMainline.lean:313:  let yYes := Classical.choose hExists
pnp3/Magnification/FinalResultMainline.lean:314:  have hySpec := Classical.choose_spec hExists
pnp3/Magnification/FinalResultMainline.lean:315:  let S := Classical.choose hySpec.2.2
pnp3/Magnification/FinalResultMainline.lean:316:  have hSSpec := Classical.choose_spec hySpec.2.2
pnp3/Magnification/FinalResultMainline.lean:357:      Classical.choose (hEventuallyYes β hβ.1 hβ.2)
pnp3/Magnification/FinalResultMainline.lean:364:      F.N0 ≤ Classical.choose (hEventuallyYes β hβPos hβLt) ∧
pnp3/Magnification/FinalResultMainline.lean:365:        ∀ m ≥ Classical.choose (hEventuallyYes β hβPos hβLt),
pnp3/Magnification/FinalResultMainline.lean:368:    Classical.choose_spec (hEventuallyYes β hβPos hβLt)
pnp3/Magnification/FinalResultMainline.lean:1472:    Classical.choose hDag
pnp3/Magnification/FinalResultMainline.lean:1488:    Classical.choose hDag
pnp3/Magnification/FinalResultMainline.lean:1531:    Classical.choose hDag
pnp3/Magnification/UnconditionalResearchGap.lean:76:            ((Classical.choose hFormula).family (Models.partialInputLen p))
pnp3/Magnification/FinalResultAuditRoutes.lean:585:              ((Classical.choose hFormula).family (Models.partialInputLen p))
pnp3/Magnification/AC0AtlasBridge.lean:83:        ((Classical.choose hFormula).family (Models.partialInputLen p))
pnp3/Magnification/AC0AtlasBridge.lean:116:      Classical.choose hFormula
pnp3/Magnification/AC0AtlasBridge.lean:192:      Classical.choose hFormula
pnp3/Magnification/AC0AtlasBridge.lean:253:      Classical.choose hFormula
pnp3/Magnification/AC0AtlasBridge.lean:311:      Classical.choose hFormula
pnp3/Magnification/AC0AtlasBridge.lean:345:      Classical.choose hFormula
pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean:229:existential, because `Classical.choose` of `PpolyFormula L = ∃ _, True`
pnp3/Magnification/AC0LocalityBridge.lean:47:        Classical.choose hFormula
pnp3/Magnification/AC0LocalityBridge.lean:98:        Classical.choose hFormula
pnp3/Magnification/AC0LocalityBridge.lean:137:      Classical.choose hFormula
pnp3/Magnification/AC0LocalityBridge.lean:429:    Classical.choose (pointTerm_consistent x) = Core.pointSubcube x := by
pnp3/Magnification/AC0LocalityBridge.lean:430:  let β := Classical.choose (pointTerm_consistent x)
pnp3/Magnification/AC0LocalityBridge.lean:433:    Classical.choose_spec (pointTerm_consistent x)
pnp3/Magnification/AC0LocalityBridge.lean:905:      Classical.choose hFormula
pnp3/Magnification/AC0LocalityBridge.lean:927:      Classical.choose hFormula
pnp3/Magnification/AC0LocalityBridge.lean:985:      Classical.choose hFormula
pnp3/Magnification/AC0LocalityBridge.lean:1034:      Classical.choose hFormula
pnp3/Magnification/AC0LocalityBridge.lean:1097:    Classical.choose hFormula
pnp3/Magnification/AC0LocalityBridge.lean:1118:  let Rf := Classical.choose hWitness
pnp3/Magnification/AC0LocalityBridge.lean:1119:  have hRf := Classical.choose_spec hWitness
pnp3/Magnification/AC0LocalityBridge.lean:1145:    Classical.choose hFormula
pnp3/Magnification/AC0LocalityBridge.lean:1166:  let Rf := Classical.choose hWitness
pnp3/Magnification/AC0LocalityBridge.lean:1167:  have hRf : Rf = C.selectors f := (Classical.choose_spec hWitness).1
pnp3/Magnification/AC0LocalityBridge.lean:1222:    Classical.choose hFormula
pnp3/Magnification/AC0LocalityBridge.lean:1362:    Classical.choose hFormula
pnp3/Magnification/AC0LocalityBridge.lean:1387:      Classical.choose hFormula
pnp3/Magnification/AC0LocalityBridge.lean:1424:    Classical.choose hFormula
pnp3/Magnification/AC0LocalityBridge.lean:1514:      Classical.choose hFormula
pnp3/Magnification/AC0LocalityBridge.lean:1538:      Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:23:    Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:51:        ((Classical.choose hFormula).family (Models.partialInputLen p))).card
pnp3/Magnification/LocalityProvider_Partial.lean:60:    Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:84:        ((Classical.choose hFormula).family (Models.partialInputLen p))
pnp3/Magnification/LocalityProvider_Partial.lean:93:    Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:244:      Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:322:      Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:414:      Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:511:      Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:561:        Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:608:      Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:802:    Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:1722:    Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:1763:    Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:1801:        Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:1823:        Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:1847:        Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:1874:      Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:1896:    Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:1923:      Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:1940:    Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:1967:      Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:1985:    Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:2034:    Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:2091:    Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:2150:    Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:2179:    Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:2216:    Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:2290:      Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:2312:    Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:2376:    Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:2442:        Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:2493:        Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:2530:        Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:2573:      Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:2673:      Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:2857:      Classical.choose hData
pnp3/Magnification/LocalityProvider_Partial.lean:2858:    have hDataSpec := Classical.choose_spec hData
pnp3/Magnification/LocalityProvider_Partial.lean:2920:        Classical.choose hFormula
pnp3/Magnification/LocalityProvider_Partial.lean:2963:      Classical.choose hData
pnp3/Magnification/LocalityProvider_Partial.lean:2964:    have hDataSpec := Classical.choose_spec hData
pnp3/Magnification/LocalityProvider_Partial.lean:3068:      ((Classical.choose hFormula).family (Models.partialInputLen p))
pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean:514:                ((Classical.choose hFormula).family (Models.partialInputLen p))
pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean:545:                ((Classical.choose hFormula).family (Models.partialInputLen p))
pnp3/LowerBounds/SingletonDensityEndpoint.lean:66:      ((Classical.choose hFormula).family (Models.partialInputLen p))
pnp3/LowerBounds/LB_Formulas.lean:334:    let k := Classical.choose witness
pnp3/LowerBounds/LB_Formulas.lean:335:    have hkSpec := Classical.choose_spec witness
pnp3/LowerBounds/LB_Formulas.lean:360:  set k := Classical.choose witness with hk
pnp3/LowerBounds/LB_Formulas.lean:409:  set k := Classical.choose witness with hk
pnp3/LowerBounds/LB_Formulas.lean:411:  have hk_spec := Classical.choose_spec witness
pnp3/LowerBounds/SingletonDensityContradiction.lean:305:  let alive := Classical.choose hLoc
pnp3/LowerBounds/SingletonDensityContradiction.lean:306:  have hAlive := Classical.choose_spec hLoc
pnp3/LowerBounds/SingletonDensityContradiction.lean:322:  let r := Classical.choose hStable
pnp3/LowerBounds/SingletonDensityContradiction.lean:323:  have hr := Classical.choose_spec hStable
pnp3/LowerBounds/SingletonDensityContradiction.lean:667:  let Rf := Classical.choose hWitness
pnp3/LowerBounds/SingletonDensityContradiction.lean:668:  have hRf := Classical.choose_spec hWitness
pnp3/LowerBounds/SingletonDensityContradiction.lean:1071:from producer-specific DAG lemmas or from ad hoc `Classical.choose_spec`
pnp3/LowerBounds/SingletonDensityContradiction.lean:1294:      ((Classical.choose hFormula).family (Models.partialInputLen p))
pnp3/LowerBounds/SingletonDensityContradiction.lean:1312:          ((Classical.choose hFormula).family (Models.partialInputLen p))
pnp3/LowerBounds/SingletonDensityContradiction.lean:1335:      (Classical.choose hFormula).correct
pnp3/LowerBounds/SingletonDensityContradiction.lean:1560:  Classical.choose
pnp3/LowerBounds/SingletonDensityContradiction.lean:1571:  exact (Classical.choose_spec
pnp3/LowerBounds/SingletonDensityContradiction.lean:1583:  exact (Classical.choose_spec
pnp3/LowerBounds/SingletonDensityContradiction.lean:1593:  exact (Classical.choose_spec
pnp3/LowerBounds/SingletonDensityContradiction.lean:1607:  Classical.choose
pnp3/LowerBounds/SingletonDensityContradiction.lean:1619:  exact (Classical.choose_spec
pnp3/LowerBounds/SingletonDensityContradiction.lean:1633:  exact (Classical.choose_spec
pnp3/LowerBounds/SingletonDensityContradiction.lean:1646:  exact (Classical.choose_spec
pnp3/LowerBounds/SingletonDensityContradiction.lean:2796:            ((Classical.choose hFormula).family (Models.partialInputLen p))
pnp3/LowerBounds/ApproxClassContradiction.lean:34:      Classical.choose hFormula
pnp3/LowerBounds/ApproxClassContradiction.lean:73:      Classical.choose hFormula
pnp3/LowerBounds/ApproxClassContradiction.lean:91:      Classical.choose hFormula
pnp3/LowerBounds/SingletonProvenanceEndpoint.lean:41:        ((Classical.choose hFormula).family (Models.partialInputLen p))
pnp3/LowerBounds/SingletonProvenanceEndpoint.lean:67:      ((Classical.choose hFormula).family (Models.partialInputLen p))
pnp3/LowerBounds/SingletonProvenanceEndpoint.lean:139:      let S := Classical.choose (singletonProvenance_boundedWitness pkg)
pnp3/LowerBounds/SingletonProvenanceEndpoint.lean:144:  let S := Classical.choose (singletonProvenance_boundedWitness pkg)
pnp3/LowerBounds/SingletonProvenanceEndpoint.lean:145:  have hS := Classical.choose_spec (singletonProvenance_boundedWitness pkg)
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:292:    Classical.choose hDag
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:1657:  let r := Classical.choose stableData
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:1660:    (Classical.choose_spec stableData).1
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:1664:    (Classical.choose_spec stableData).2
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:2776:  let x_yes := Classical.choose
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:2778:  have hYesSpec := Classical.choose_spec
pnp3/LowerBounds/DAGStableRestrictionProducer.lean:2780:  have hData := Classical.choose_spec hYesSpec
pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean:144:  exact Classical.choose (hDag n β)
pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean:248:surface by extracting strict witnesses pointwise via `Classical.choose`.
pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean:266:  let n0 : Nat := Classical.choose hExists
pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean:270:    Classical.choose_spec hExists
pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean:273:  exact Classical.choose (hn0 n hn)
pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean:1623:    fun n β => Classical.choose (hSlices n β)
pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean:1675:    fun n β => Classical.choose (hSlices n β)
pnp3/LowerBounds/AntiChecker_Partial.lean:734:  refine ⟨Classical.choose h, ?_, ?_⟩
pnp3/LowerBounds/AntiChecker_Partial.lean:735:  · exact (Classical.choose_spec h).1
pnp3/LowerBounds/AntiChecker_Partial.lean:736:  · exact not_covered_of_not_mem_union (F := F) (Classical.choose_spec h).2
pnp3/LowerBounds/AntiChecker_Partial.lean:1546:  let F : Family solver.params.ac0.n := Classical.choose hEx
pnp3/LowerBounds/AntiChecker_Partial.lean:1547:  let hExY := Classical.choose_spec hEx
pnp3/LowerBounds/AntiChecker_Partial.lean:1548:  let Y : Finset (Core.BitVec solver.params.ac0.n → Bool) := Classical.choose hExY
pnp3/LowerBounds/AntiChecker_Partial.lean:1549:  let hExF := Classical.choose_spec hExY
pnp3/LowerBounds/AntiChecker_Partial.lean:1550:  let hF : ThirdPartyFacts.AC0FamilyWitnessProp solver.params.ac0 F := Classical.choose hExF
pnp3/LowerBounds/AntiChecker_Partial.lean:1551:  let hPack := Classical.choose_spec hExF
```

## `axiom` declarations
Raw `axiom\s` textual hits follow; these are comments/docs, not active Lean declarations. The stricter Lean declaration search returned no output.
```text
pnp3/Docs/Research_Method_Boundary.md:51:`./scripts/check.sh`, axiom audits, route-policy guards, and CI workflows are
pnp3/Docs/Unconditional_NP_not_subset_PpolyDAG_Plan.md:143:for `ResearchGapWitness`.  Green CI, axiom audits, route-policy guards, and
pnp3/Docs/PhaseI_Verifier_Design.md:241:4. `#print axioms` for each new theorem — confirm no axiom leaks.
pnp3/Docs/PhaseI_Verifier_Design.md:403:   axiom inventory unchanged (`propext = 349`, `Classical.choice = 345`,
pnp3/Docs/PhaseI_Verifier_Design.md:481:All 6 `check.sh` steps pass with axiom surface unchanged:
pnp3/Docs/PhaseI_Verifier_Design.md:527:in `GateWrappers.lean`.  No sorry/admit/axiom additions.
pnp3/Docs/PhaseI_Verifier_Design.md:564:**Cumulative session 49**: ~1400 LOC.  No sorry/admit/axiom additions.
pnp3/Docs/PhaseI_Verifier_Design.md:666:6 steps pass; axiom inventory unchanged (propext=349, Classical.choice=345,
pnp3/Docs/PhaseI_Verifier_Design.md:781:- New theorem axiom dependencies (via `#print axioms`):
pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean:324:   without introducing typeclass / axiom / opaque payload, and
pnp3/Tests/TargetLockProbe.lean:12:The complementary phantom-axiom check (no top-level
pnp3/Tests/TargetLockProbe.lean:13:`axiom P_ne_NP_unconditional` in pnp3/pnp4) lives in the shell
pnp3/LowerBounds/AntiChecker_Partial.lean:2028:  construction (via the P/poly → locality axiom and the locality lift).
```

## Hard-payload search summary
`ResearchGapWitness|NP_not_subset_PpolyDAG|VerifiedNPDAGLowerBoundSource|SearchMCSPMagnificationContract|SourceTheorem|gap_from` returned 623 hits in 59 files. This confirms the marker area intersects final-target docs and bridge interfaces, but A10 did not find a new closed hard payload.

## Command log
- `./scripts/check.sh` → PASS; all checks passed
- `rg -nl "_Partial|_Legacy" --type lean pnp3 pnp4` → 34 files with marker references
- `rg -n "TODO|FIXME|XXX|HACK" pnp3 pnp4` → 24 hits; all TODO
- `rg -n "placeholder" pnp3 pnp4` → 37 hits
- `rg -n "True\s*--\s*placeholder" pnp3 pnp4` → 1 hit
- `rg -n "noncomputable" pnp3 pnp4` → 505 raw hits
- `rg -n "^\s*noncomputable\s+def\b" pnp3 pnp4` → 455 noncomputable def declarations
- `rg -n "Classical\.choose" pnp3 pnp4` → 274 hits
- `rg -n "axiom\s" pnp3 pnp4` → 13 textual hits; no declarations
- `rg -n "^\s*axiom\b" --type lean pnp3 pnp4` → no output / exit 1
- `rg -n "ResearchGapWitness|NP_not_subset_PpolyDAG|VerifiedNPDAGLowerBoundSource|SearchMCSPMagnificationContract|SourceTheorem|gap_from" pnp3 pnp4 ...` → 623 hits
- `rg -n "RefutedRoute|Vacuous|supportBounds|MagnificationAssumptions|FinalPayloadProvider|via_ex_falso|weakRoute|Legacy|_Partial|TODO|placeholder" pnp3 pnp4 ...` → 826 hits
- `rg -n "\bclass\b|\binstance\b|default_instance|attribute \[instance\]|\bFact\b|\bopaque\b|Classical\.choose|noncomputable def" pnp3 pnp4 ...` → 1084 hits

## Final structured output block
```text
Task: A10
Engineer handle: codex
Branch: khanukov/phase1-A10-codex
Commit before: d27b069127f63a3f24ab30d1a91c86c84f8b79c7
Commit after: <filled by final PR message>

Files added/modified:
  - seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A10_partial_legacy_markers_codex.md

Outcome:
  AUDIT_LANDED

Executive verdict:
  PARTIAL_BUT_USEFUL

Files audited:
  - required governance/task files plus repository-wide pnp3/pnp4 marker-positive files listed above

Key findings:
  1. No active Lean axiom declarations; ./scripts/check.sh passed.
  2. Actual _Partial path inventory has 8 files; no _Legacy.lean path exists.
  3. The main risks are known/refuted support-bounds/provider routes and one `True -- placeholder` PDT invariant.

Kernel-checked content found:
  - Conditional route infrastructure, tests, and bridge interfaces build under the kernel.

Staged / placeholder content found:
  - `PDT.WellFormed := True`, one proof-local `: True` placeholder, and multiple support/locality Prop packages.

Refuted / vacuous / legacy route findings:
  - RefutedRoute and Vacuous provider paths are present but explicitly quarantined/audit-only.

Hidden payload / Rule 16 findings:
  - Provider/default support-bound typeclass paths are high risk if reused; current checks quarantine them.

Recommended Phase 1+ tasks:
  - 6 concrete cleanup/audit tasks listed above.

Hold / cancel recommendations:
  - Hold any task promoting support-bounds/vacuous-provider wrappers as mainline progress.

Commands run:
  - ./scripts/check.sh → PASS
  - rg marker searches → summarized counts above

Scope violations:
  none

Honest caveats:
  - Large files were structurally searched; not every proof body was read.
```
