# A08 Audit: `pnp4/Pnp4/Frontier/`

Task: A08  
Engineer handle: codex  
Branch: `khanukov/phase1-A08-codex`  
Date: 2026-05-17

## 1. Executive verdict

**Verdict: PARTIAL_BUT_USEFUL.**

The pnp4 Frontier is complete as an **interface map** for source-theorem production, but it is not complete as a source theorem or as a proof-producing route to `ResearchGapWitness`.  The kernel-checked content mostly proves adapter/repackaging facts: if a `VerifiedNPDAGLowerBoundSource` or a `SearchMCSPMagnificationContract` is supplied, the existing final bridge can be invoked; if a codec supplies encode/decode facts, its relation is sound/complete for the tree-MCSP predicate; if a parser accepts a prefix input and a full witness extends the prefix, the prefix language accepts.  The central load-bearing steps remain staged as `Prop` fields: NP membership for the prefix language, parser/runtime polynomial time, concrete serialization, the weak search-MCSP lower bound, and especially magnification from that weak lower bound to `VerifiedNPDAGLowerBoundSource`.  This is useful infrastructure because it sharply separates restricted AC0[p] work from mainline `PpolyDAG` requirements and prevents a restricted lower bound from being misreported as P-vs-NP progress.

## 2. Executive summary: is the pnp4 Frontier complete for source-theorem production?

No: it is **not complete for source-theorem production** if “source theorem” means a concrete theorem that can honestly construct `ResearchGapWitness` or close `NP_not_subset_PpolyDAG`.  It is complete enough to describe the expected API shape:

```text
AC0[p] LB
  -- only restricted milestone; no direct endpoint proof here
  ↓ requires explicit bridge/magnification not proved in Frontier
SearchMCSPWeakCircuitLowerBound target
  + SearchMCSPMagnificationContract target
  → VerifiedNPDAGLowerBoundSource
  → NP_not_subset_PpolyDAG
  → P_ne_NP
```

But the arrows `AC0[p] LB → magnification contract`, `weak search-MCSP lower bound`, `prefix language ∈ NP`, and `magnification contract → VerifiedNPDAGLowerBoundSource` are not proved from concrete mathematics in this directory.  The directory should be read as a governance/API boundary plus some local proof infrastructure, not as a completed lower-bound route.

## 3. Files audited

| File | Approximate role | Depth | Notes |
|---|---|---:|---|
| `RESEARCH_CONSTITUTION.md` | Phase-0 governance and trust-root rules | Read structurally, key rules read | Used to check source-theorem, ResearchGapWitness, refuted-route, and hidden-payload policy. |
| `seed_packs/phase1_20engineer_parallel_dispatch/README.md` | Shared phase instructions | Read structurally | Older E-task wording ignored where A08 prompt overrides. |
| `seed_packs/phase1_20engineer_parallel_dispatch/COMMON_WORKER_INSTRUCTIONS.md` | Shared worker/build/report instructions | Read structurally | Applied stricter markdown-only and check requirements from user prompt. |
| `seed_packs/phase1_20engineer_parallel_dispatch/tasks/A08_audit_pnp4_frontier.md` | A08 task specification | Fully read | Defines the 8 Frontier files and required report sections. |
| `pnp4/Pnp4/Frontier/CompressionMagnification.lean` | Generic compression/search-MCSP mainline wrapper to final bridge | Fully read | Small file; all declarations inspected. |
| `pnp4/Pnp4/Frontier/SearchMCSPConcreteTargets.lean` | Concrete tree-MCSP search target and source package | Fully read | All definitions/theorems inspected. |
| `pnp4/Pnp4/Frontier/PvsNPBridgeRequirements.lean` | AC0[p] restricted-source vs verified-DAG-source bridge boundary | Fully read | All declarations inspected. |
| `pnp4/Pnp4/Frontier/SearchMCSPMagnification.lean` | Generic search/compression problem, weak lower-bound target, magnification contract | Fully read | All declarations inspected. |
| `pnp4/Pnp4/Frontier/ContractExpansion/C_DAG_Adapter.lean` | Adapter between pnp4 `CircuitFamilyClass` and frozen pnp3 `PpolyDAG` | Fully read | Contains the only `Classical.choose` in audit scope. |
| `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguage.lean` | R1-B prefix-extension language skeleton | Fully read | Contains noncomputable Boolean wrapper and staged NP verifier plan. |
| `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageNP.lean` | R1-B1 parser/decidability progress for tree-MCSP prefix language | Fully read | Decidability is discharged for codec-induced relations; runtime remains staged. |
| `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageRuntime.lean` | R1-B2a ambient runtime-budget interface | Fully read | Contains one arithmetic theorem plus staged runtime fields. |
| `pnp4/Pnp4/AlgorithmsToLowerBounds/BridgeToPpolyDAG.lean` | Immediate dependency defining `VerifiedNPDAGLowerBoundSource` | Fully read | Needed to interpret hard payload fields. |
| `pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean` | Public surface wrappers | Searched and relevant sections skimmed | Used to confirm Frontier surfaces are imported and partially tested. |
| `pnp4/Pnp4/Tests/AxiomsAudit.lean` | Axiom-print audit surface | Searched and relevant sections skimmed | Used to confirm key Frontier theorem surfaces are audited. |
| `pnp3/Magnification/UnconditionalResearchGap.lean` | ResearchGapWitness/final-target dependency | Searched, key declarations inspected | Needed to map gap to `ResearchGapWitness`; not a file under direct A08 edit scope. |
| `pnp3/Complexity/Interfaces.lean` | Frozen pnp3 complexity interfaces | Searched, key declarations inspected | Needed to interpret `NP_not_subset_PpolyDAG`, `PpolyDAG`, and `P_ne_NP`. |
| `outputs/nogolog.jsonl` | NoGoLog optional cross-check | Searched only for Frontier route terms | No direct A08 route name hit used in conclusions. |
| `seed_packs/first_move_search_2026/reports/fp3b_epoch_strategic_retrospective_claudeopus.md` | Optional retrospective | Skimmed structurally | Used only as context; no direct formal conclusion depends on it. |

## 4. Top-level theorem / structure inventory

### 4.1 Final-bridge and hard-payload boundary

| Declaration | File | Type/signature summary | Classification | Hard-payload dependency |
|---|---|---|---|---|
| `VerifiedNPDAGLowerBoundSource` | `pnp4/Pnp4/AlgorithmsToLowerBounds/BridgeToPpolyDAG.lean` | Structure with `L`, `inNP : NP L`, `notInPpolyDAG : ¬ PpolyDAG L`. | canonical | It is the hard payload. |
| `NP_not_subset_PpolyDAG_of_verified_source` | same | `VerifiedNPDAGLowerBoundSource → NP_not_subset_PpolyDAG`. | canonical | Requires `VerifiedNPDAGLowerBoundSource`; constructs `NP_not_subset_PpolyDAG`. |
| `P_ne_NP_of_verified_source` | same | `VerifiedNPDAGLowerBoundSource → P_ne_NP`. | conditional | Requires `VerifiedNPDAGLowerBoundSource`; uses existing `P ⊆ PpolyDAG` bridge. |
| `NP_not_subset_Ppoly` | `CompressionMagnification.lean` | Abbrev for pnp3 `NP_not_subset_PpolyDAG`. | canonical naming alias | Exactly `NP_not_subset_PpolyDAG`; no proof. |
| `P_ne_NP_of_NP_not_subset_Ppoly` | `CompressionMagnification.lean` | `NP_not_subset_Ppoly → P_ne_NP`. | conditional | Requires `NP_not_subset_PpolyDAG`. |

### 4.2 `PvsNPBridgeRequirements`: restricted source is not mainline by itself

| Declaration | File | Type/signature summary | Classification | Hard-payload dependency |
|---|---|---|---|---|
| `AC0pRestrictedLowerBoundSource` | `PvsNPBridgeRequirements.lean` | Packages `model`, prime `p`, language `L`, and `¬ InAC0p model p L`. | weak route / restricted side track | No `VerifiedNPDAGLowerBoundSource`; no `NP_not_subset_PpolyDAG`. |
| `AC0pRestrictedLowerBoundSource.restrictedConclusion` | same | Extracts `¬ InAC0p src.model src.p src.L`. | canonical restricted theorem | Depends only on `src.notInAC0p`. |
| `PvsNPBridgeRequirement` | same | Structure with `verifiedSource : VerifiedNPDAGLowerBoundSource`. | staged hard-payload wrapper | Directly wraps `VerifiedNPDAGLowerBoundSource`; not progress unless inhabited honestly. |
| `P_ne_NP_of_pnp4_bridge_requirement` | same | `PvsNPBridgeRequirement → P_ne_NP`. | conditional | Requires wrapped `VerifiedNPDAGLowerBoundSource`. |
| `RestrictedToVerifiedDAGBridge` | same | For a restricted source, supplies `verifiedSource`. | staged Prop/hard-payload wrapper | This is exactly the missing mathematical bridge. |
| `P_ne_NP_of_restricted_source_and_dag_bridge` | same | Restricted source + bridge → `P_ne_NP`. | conditional | Requires bridge field `VerifiedNPDAGLowerBoundSource`; restricted source alone does no endpoint work. |

### 4.3 `CompressionMagnification`: generic mainline wrapper

| Declaration | File | Type/signature summary | Classification | Hard-payload dependency |
|---|---|---|---|---|
| `SearchMCSPWeakLowerBound` | `CompressionMagnification.lean` | Structure with arbitrary `weakLowerBound : Prop`, a proof, and `weakLowerBound → VerifiedNPDAGLowerBoundSource`. | staged hard-payload wrapper / potential wrapper risk | Its `magnifiesToVerifiedDAGSource` field is the hard theorem. |
| `SearchMCSPWeakLowerBound.verifiedSource` | same | Applies `magnifiesToVerifiedDAGSource` to `weakLowerBoundProof`. | conditional extractor | Produces `VerifiedNPDAGLowerBoundSource` from package field. |
| `NP_not_subset_Ppoly_of_searchMCSPWeakLowerBound` | same | `SearchMCSPWeakLowerBound → NP_not_subset_Ppoly`. | conditional | Depends on package’s `VerifiedNPDAGLowerBoundSource`. |
| `P_ne_NP_of_searchMCSPWeakLowerBound` | same | `SearchMCSPWeakLowerBound → P_ne_NP`. | conditional | Depends on `SearchMCSPWeakLowerBound.verifiedSource`. |
| `PvsNPMainlineProgress` | same | Structure with `verifiedSource`. | staged hard-payload wrapper | Directly wraps `VerifiedNPDAGLowerBoundSource`. |
| `P_ne_NP_of_mainlineProgress` | same | `PvsNPMainlineProgress → P_ne_NP`. | conditional | Requires wrapped `VerifiedNPDAGLowerBoundSource`. |
| `PvsNPMainlineProgress.of_searchMCSPWeakLowerBound` | same | Converts search-MCSP package to progress wrapper. | conditional adapter | Depends on magnification field. |

### 4.4 `SearchMCSPMagnification`: concrete weak-lower-bound contract surface

| Declaration | File | Type/signature summary | Classification | Hard-payload dependency |
|---|---|---|---|---|
| `SearchMCSPCompressionProblem` | `SearchMCSPMagnification.lean` | Generic search/compression problem with instance length, witness length, promise, relation, totality on promise. | useful interface | No hard endpoint; relation/totality fields are local obligations. |
| `searchSolverOutput` | same | Evaluates one circuit per witness bit on an input. | canonical helper | No hard endpoint. |
| `BoundedSearchSolver` | same | Non-uniform solver family with `size_le` and `solves`. | useful interface | No hard endpoint. |
| `SearchProblemNoBoundedSolver` | same | `¬ Nonempty (BoundedSearchSolver problem C sizeBound)`. | staged lower-bound Prop | This is a weak lower-bound proposition, not a proof. |
| `SearchMCSPWeakCircuitLowerBoundTarget` | same | Packages `problem`, `circuitClass`, `sizeBound`. | useful interface | No hard endpoint. |
| `SearchMCSPWeakCircuitLowerBoundTarget.noBoundedSolver` | same | Target-specific weak lower-bound proposition. | staged Prop | Weak lower-bound statement only. |
| `SearchMCSPWeakCircuitLowerBound` | same | Structure with `noBoundedSolver : target.noBoundedSolver`. | staged weak route | Requires proof of weak lower bound. |
| `SearchMCSPMagnificationContract` | same | Structure with `target.noBoundedSolver → VerifiedNPDAGLowerBoundSource`. | staged hard-payload wrapper / hidden-hard-theorem risk if misused | Exactly the magnification hard payload. |
| `SearchMCSPWeakLowerBound.of_weakCircuitLowerBound` | same | Packages concrete weak LB plus magnification into generic package. | conditional adapter | Requires `SearchMCSPMagnificationContract`. |
| `SearchMCSPWeakCircuitLowerBound.verifiedSource` | same | Extracts `VerifiedNPDAGLowerBoundSource`. | conditional | Requires weak lower bound and magnification contract. |
| `NP_not_subset_Ppoly_of_weakCircuitLowerBound` | same | Weak LB + magnification → `NP_not_subset_Ppoly`. | conditional | Requires magnification to verified source. |
| `P_ne_NP_of_weakCircuitLowerBound` | same | Weak LB + magnification → `P_ne_NP`. | conditional | Requires verified source via contract. |
| `PvsNPMainlineProgress.of_weakCircuitLowerBound` | same | Converts concrete weak LB + contract to progress wrapper. | conditional adapter | Requires verified source via contract. |

### 4.5 `SearchMCSPConcreteTargets`: tree-MCSP target

| Declaration | File | Type/signature summary | Classification | Hard-payload dependency |
|---|---|---|---|---|
| `TreeMCSPSearchWitnessEncoding` | `SearchMCSPConcreteTargets.lean` | Interface with witness bits, verification relation, soundness, completeness for `treeMCSPPredicate`. | useful interface | No endpoint; fields are local proof obligations. |
| `TreeCircuitWitnessCodec` | same | Encode/decode interface for tree circuits, with `decode_encode` for size-bounded circuits. | useful interface | No endpoint. |
| `TreeCircuitWitnessCodec.verifies` | same | Prop: decoded circuit exists, has size bound, computes truth table. | canonical definition | No endpoint. |
| `TreeCircuitWitnessCodec.sound` | same | Codec verification implies `treeMCSPPredicate`. | canonical local theorem | No hard endpoint. |
| `TreeCircuitWitnessCodec.complete` | same | `treeMCSPPredicate` implies some encoded codec witness verifies. | canonical local theorem | No hard endpoint; depends on codec `decode_encode`. |
| `TreeMCSPSearchWitnessEncoding.ofCodec` | same | Builds generic encoding from codec. | adapter | No hard endpoint. |
| `treeMCSPSearchProblem` | same | Search problem with truth-table instances and codec/encoding witnesses. | useful interface | No hard endpoint. |
| `treeMCSPSearchWeakLowerBoundTarget` | same | Target shape for no bounded solver against tree-MCSP search. | staged lower-bound target | No proof. |
| `TreeMCSPSearchMagnificationSource` | same | Packages threshold, encoding, class, size bound, weak lower bound, and magnification contract. | staged hard-payload wrapper | Requires both weak LB and `SearchMCSPMagnificationContract`. |
| `TreeMCSPSearchMagnificationSource.verifiedSource` | same | Extracts `VerifiedNPDAGLowerBoundSource`. | conditional | Requires package fields. |
| `NP_not_subset_Ppoly_of_treeMCSPSearchMagnificationSource` | same | Concrete tree-MCSP source → `NP_not_subset_Ppoly`. | conditional | Depends on magnification contract. |
| `P_ne_NP_of_treeMCSPSearchMagnificationSource` | same | Concrete tree-MCSP source → `P_ne_NP`. | conditional | Depends on magnification contract. |
| `PvsNPMainlineProgress.of_treeMCSPSearchMagnificationSource` | same | Converts concrete source to mainline wrapper. | conditional adapter | Depends on verified source from package. |

### 4.6 ContractExpansion track

| Declaration | File | Type/signature summary | Classification | Hard-payload dependency |
|---|---|---|---|---|
| `C_DAG` | `C_DAG_Adapter.lean` | `CircuitFamilyClass` whose family/eval/size are pnp3 `DagCircuit`. | canonical adapter | No hard payload; preserves endpoint semantics. |
| `PolynomiallyBoundedFamily` | same | pnp4 length-indexed family with exponent, size bound, correctness. | useful interface | No endpoint. |
| `InPpolyDAG_to_C_DAG_family` | same | Converts pnp3 `InPpolyDAG L` to pnp4 `PolynomiallyBoundedFamily C_DAG L`. | canonical adapter | Uses `Classical.choose` to extract exponent; no new endpoint. |
| `C_DAG_family_to_InPpolyDAG` | same | Converts pnp4 `C_DAG` family back to pnp3 `InPpolyDAG`. | canonical adapter | No hard endpoint. |
| `PpolyDAG_decider_as_C_DAG_decider` | same | From `PpolyDAG L` extracts one global exponent and per-length `C_DAG` deciders. | canonical adapter | Requires `PpolyDAG L`, does not prove lower bound. |
| `PrefixInput` | `PrefixExtensionLanguage.lean` | Parsed tuple `tag,n,x,i,p,pad` with `i ≤ witnessBits n`. | useful interface | No endpoint. |
| `PrefixInput.prefixAgrees` | same | Prefix/full-witness agreement on first `i` coordinates. | canonical local definition | No endpoint. |
| `PrefixParser` | same | Abstract parser with `tag`, length convention `M`, and `parse`. | staged parser interface | Parser implementation not supplied. |
| `parsePrefixInput` | same | Parser entry point. | harmless adapter | No endpoint. |
| `wellFormed` | same | Parser accepts iff some parsed input. | harmless interface | No endpoint. |
| `PrefixExtendableInput` | same | Exists full witness extending prefix and satisfying relation. | staged semantic predicate | No endpoint; relation may be arbitrary problem field. |
| `PrefixExtendable` | same | Parsed-input version of prefix extendability. | staged semantic predicate | No endpoint. |
| `PrefixExtensionLanguage` | same | Noncomputable pnp3 language using classical decidability of `PrefixExtendable`. | useful but noncomputable interface | No NP proof; potential wrapper risk only if treated as NP. |
| `PrefixExtensionLanguage_accepts_iff` | same | Boolean wrapper accepts iff `PrefixExtendable`. | canonical local theorem | No endpoint. |
| `PrefixExtensionLanguage_rejects_malformed` | same | Parser failure implies language rejects. | canonical local theorem | No endpoint. |
| `PrefixExtensionLanguage_accepts_of_parse_and_witness` | same | Parse success + agreeing relation witness implies acceptance. | canonical local theorem | No endpoint. |
| `PrefixExtensionNPVerifierBudget` | same | Named `Prop` checklist for NP verifier obligations. | honest staging | No hard endpoint; many unproved fields. |
| `PrefixExtensionNPVerifierPlan` | same | Plan with budget and verifier-check propositions. | honest staging / audit-only | No theorem. |
| `treeMCSPPrefixParser` | `PrefixExtensionLanguageNP.lean` | Constructor for tree-MCSP prefix parser from explicit parser function. | adapter | No endpoint. |
| `TreeMCSPPrefixParserObligations` | same | Parser data plus polynomial time, malformed rejection, length-convention Props. | honest staging | No endpoint. |
| `treeMCSPSearchRelation_decidable_of_encoding` | same | If encoding verifier is decidable, target relation is decidable. | canonical local theorem/def | No endpoint. |
| `TreeCircuitWitnessCodec.verifiesDecidable` | same | Codec-induced relation is decidable by decoding and finite truth-table check. | canonical local decidability theorem/def | No endpoint; decidability only, not polytime. |
| `treeMCSPSearchRelation_decidable_of_codec` | same | Decidability for target induced by codec. | canonical local theorem/def | No endpoint. |
| `TreeMCSPPrefixCoreBudgetProgress` | same | Record of parser polynomial time, relation decidability, relation polynomial time, witness length, blockers. | honest staging | Runtime fields remain Props. |
| `TreeMCSPPrefixCoreBudgetProgress.ofEncodingDecidable` | same | Builds progress record from explicit decidability and Prop obligations. | adapter / honest staging | No endpoint. |
| `treeMCSPPrefixAmbientLength` | `PrefixExtensionLanguageRuntime.lean` | `tableLen n + overhead n + witnessBits n + padBits n`. | canonical arithmetic definition | No endpoint. |
| `tableLen_le_treeMCSPPrefixAmbientLength` | same | Proves truth-table length is ≤ ambient length. | canonical arithmetic theorem | No endpoint. |
| `PolynomiallyBoundedInAmbient` | same | `∃ c, f n ≤ M n^c + c`. | useful arithmetic predicate | No endpoint. |
| `threshold_poly_in_M`, `witnessBits_poly_in_M` | same | Specializations of polynomial bound predicate. | staged arithmetic Props | No endpoint. |
| `RuntimeAwareTreeCircuitCodec` | same | Codec plus witness/threshold bounds and runtime Props. | honest staging | Runtime fields are Props. |
| `RuntimeAwarePrefixParser` | same | Parser plus runtime Prop and exact malformed/length facts. | honest staging with some concrete fields | No endpoint. |
| `TreeMCSPPrefixRuntimeBudget` | same | Runtime budget checklist for tree-MCSP prefix verification. | honest staging | No NP proof; no endpoint. |
| `treeMCSPPrefixRuntimeBudget_tableLen` | same | Discharges tableLen part for canonical ambient length. | canonical arithmetic helper | No endpoint. |

## 5. Kernel-checked content

Kernel-checked, nontrivial local content found:

1. **Final bridge adapters are checked but conditional.**  `VerifiedNPDAGLowerBoundSource` unpacks to `NP_not_subset_PpolyDAG`, and the existing pnp3 theorem plus internal `P ⊆ PpolyDAG` proves `P_ne_NP` from such a source.  Frontier theorems that conclude `P_ne_NP` all require one of: `NP_not_subset_Ppoly`, a `VerifiedNPDAGLowerBoundSource`, `PvsNPBridgeRequirement`, `RestrictedToVerifiedDAGBridge`, `SearchMCSPWeakLowerBound`, `SearchMCSPWeakCircuitLowerBound` plus `SearchMCSPMagnificationContract`, or `TreeMCSPSearchMagnificationSource`.
2. **AC0[p] restricted extraction is checked.**  `AC0pRestrictedLowerBoundSource.restrictedConclusion` proves only `¬ InAC0p src.model src.p src.L`; it does not infer NP membership or any DAG lower bound.
3. **Search-MCSP packaging is checked.**  The definitions correctly route `SearchMCSPWeakCircuitLowerBound + SearchMCSPMagnificationContract` into the older generic `SearchMCSPWeakLowerBound` surface, then into `VerifiedNPDAGLowerBoundSource`, `NP_not_subset_PpolyDAG`, and `P_ne_NP`.  The kernel checks the dataflow; it does not check the missing magnification theorem because that theorem is a field.
4. **Tree-circuit codec soundness/completeness is checked.**  `TreeCircuitWitnessCodec.sound` proves that a decoded small tree circuit computing the truth table implies `treeMCSPPredicate`.  `TreeCircuitWitnessCodec.complete` proves that a `treeMCSPPredicate` witness can be encoded, using `decode_encode`, to produce a verifying witness.
5. **C_DAG adapter is checked.**  `InPpolyDAG_to_C_DAG_family` and `C_DAG_family_to_InPpolyDAG` are record-repackaging equivalences between pnp3 DAG witnesses and pnp4 `CircuitFamilyClass` families.  `PpolyDAG_decider_as_C_DAG_decider` extracts a global exponent and per-length `C_DAG` decider from a pnp3 `PpolyDAG L` witness.
6. **Prefix-extension semantic wrapper facts are checked.**  The Boolean language accepts iff `PrefixExtendable`; parser failure rejects; parse success plus a full agreeing relation witness accepts.
7. **Relation decidability for codec-induced tree-MCSP is checked.**  The generic target relation is decidable when the encoding relation is decidable, and the codec-induced relation itself is decidable by case-splitting on decode and using finite decidability of truth-table agreement.  This is not a polynomial-time theorem.
8. **Ambient-length arithmetic is checked.**  `tableLen_le_treeMCSPPrefixAmbientLength` and `treeMCSPPrefixRuntimeBudget_tableLen` establish that the truth-table component is bounded by the canonical ambient length.

Nothing in the audited files kernel-checks a concrete `SearchMCSPWeakCircuitLowerBound` for a nontrivial target, a concrete `SearchMCSPMagnificationContract`, a theorem `PrefixExtensionLanguage_in_NP`, a `ResearchGapWitness`, or a closed zero-argument `P_ne_NP` theorem.

## 6. Staged / placeholder / Prop-only content

| Staged item | Location | What is packaged | Assessment |
|---|---|---|---|
| `SearchMCSPWeakLowerBound.weakLowerBound : Prop` | `CompressionMagnification.lean` | Arbitrary weak LB proposition plus proof and hard magnification field. | Potential wrapper risk: safe only if the magnification field is audited as real theorem. |
| `SearchMCSPWeakLowerBound.magnifiesToVerifiedDAGSource` | same | `weakLowerBound → VerifiedNPDAGLowerBoundSource`. | Possible hidden hard theorem; this is main missing math. |
| `PvsNPMainlineProgress.verifiedSource` | same | A `VerifiedNPDAGLowerBoundSource`. | Hard-payload wrapper; harmless as naming if not reported as construction. |
| `PvsNPBridgeRequirement.verifiedSource` | `PvsNPBridgeRequirements.lean` | A `VerifiedNPDAGLowerBoundSource`. | Hard-payload wrapper; safe as governance boundary. |
| `RestrictedToVerifiedDAGBridge.verifiedSource` | same | Restricted source to verified DAG source. | Possible hidden hard theorem; required bridge is not discharged. |
| `SearchProblemNoBoundedSolver` | `SearchMCSPMagnification.lean` | Nonexistence of bounded solver. | Honest lower-bound Prop; no proof supplied by the definition. |
| `SearchMCSPWeakCircuitLowerBound.noBoundedSolver` | same | Proof of target no-bounded-solver Prop. | Honest staging of weak LB. |
| `SearchMCSPMagnificationContract.magnifiesToVerifiedDAGSource` | same | Weak LB implies verified DAG lower-bound source. | Main hard theorem wrapped as a field. |
| `TreeMCSPSearchMagnificationSource` | `SearchMCSPConcreteTargets.lean` | Concrete weak LB plus magnification contract. | Honest source package; dangerous only if fields are filled vacuously. |
| `PrefixParser.parse` | `PrefixExtensionLanguage.lean` | Abstract parser. | Harmless interface; concrete serialization absent. |
| `PrefixExtensionLanguage` | same | Noncomputable language from semantic `PrefixExtendable`. | Harmless interface if not treated as NP; no runtime proof. |
| `PrefixExtensionNPVerifierBudget` | same | Parser/runtime/codec Props. | Honest staging; no hidden theorem because fields are not inhabited. |
| `PrefixExtensionNPVerifierPlan` | same | Budget plus intended verifier checks as Props. | Audit-only plan; not a theorem. |
| `TreeMCSPPrefixParserObligations` | `PrefixExtensionLanguageNP.lean` | Parser function and parser obligations as Props. | Honest staging; no default `True` fillers in this file. |
| `TreeMCSPPrefixCoreBudgetProgress` | same | Relation decidability plus runtime Props. | Partly discharged; runtime remains staged. |
| `PolynomiallyBoundedInAmbient`, `threshold_poly_in_M`, `witnessBits_poly_in_M` | `PrefixExtensionLanguageRuntime.lean` | Arithmetic polynomial-bound Props. | Honest arithmetic staging; concrete witnesses not automatic. |
| `RuntimeAwareTreeCircuitCodec`, `RuntimeAwarePrefixParser`, `TreeMCSPPrefixRuntimeBudget` | same | Runtime and length-budget fields. | Honest staging; still not NP membership. |

## 7. Refuted / vacuous / legacy route check

Search terms checked in `pnp4/Pnp4/Frontier`: `RefutedRoute`, `Vacuous`, `supportBounds`, `MagnificationAssumptions`, `FinalPayloadProvider`, `via_ex_falso`, `weakRoute`, `Legacy`, `_Partial`, `TODO`, `placeholder`, `weak route`, `legacy route`, and `default support bounds`.

Findings:

- No `RefutedRoute`, `FinalPayloadProvider`, `supportBounds`, `MagnificationAssumptions`, `via_ex_falso`, `_Partial`, `_Legacy`, or `weakRoute` declaration occurs in the audited Frontier files.
- The only `placeholder` hits are comments stating that vacuous `True` placeholders are deliberately avoided in `PrefixExtensionLanguageNP.lean` and `PrefixExtensionLanguageRuntime.lean`.
- The phrase “weak lower-bound” appears throughout the SearchMCSP interfaces, but this is an intended weak-lower-bound target shape, not a legacy/refuted channel.
- No default support-bound route or refuted audit route appears to be imported by these files.

Isolation assessment: the audited area is well isolated from the known refuted/vacuous route names.  Its risk is not legacy import contamination; its risk is overinterpreting staged fields as proofs.

## 8. Hidden payload / Rule 16 check

Search terms checked in `pnp4/Pnp4/Frontier`: `class`, `instance`, `default_instance`, `attribute [instance]`, `Fact`, `opaque`, `Classical.choose`, `noncomputable def`, and Provider/Payload/Witness/Source/Default-like names.

Classified occurrences:

| Occurrence | Classification | Interpretation |
|---|---|---|
| `Classical.choose` and `Classical.choose_spec` in `InPpolyDAG_to_C_DAG_family` | standard exponent extraction | Extracts the polynomial exponent from an existing `InPpolyDAG` witness.  This is not a hidden lower-bound payload and does not construct `PpolyDAG` or its negation. |
| `noncomputable def InPpolyDAG_to_C_DAG_family` | harmless infrastructure | Noncomputability follows from exponent choice from a hypothesis; adapter-only. |
| `noncomputable def PrefixExtensionLanguage` | harmless interface with caveat | Uses classical decidability to turn `PrefixExtendable` into a Boolean pnp3 language.  Safe only because NP/runtime proof is explicitly separated; forbidden if later used to assert NP membership without budget proof. |
| `Source`-named structures such as `AC0pRestrictedLowerBoundSource`, `TreeMCSPSearchMagnificationSource`, and `VerifiedNPDAGLowerBoundSource` references | hidden-payload risk if misreported | They are explicit packages.  `VerifiedNPDAGLowerBoundSource` is the hard payload; wrappers around it are not progress unless inhabited from real proofs. |
| `Witness`-named codec/encoding structures | harmless infrastructure | These are local tree-MCSP witness encodings, not `ResearchGapWitness`. |
| `instance`/`infer_instance` inside `TreeCircuitWitnessCodec.verifiesDecidable` | harmless infrastructure | Uses decidability instances for conjunction/finite forall after decode.  No endpoint proof. |
| `class` text in comments/types such as `CircuitFamilyClass` | harmless infrastructure | pnp4 circuit-family abstraction only. |
| `opaque`, `Fact`, `default_instance`, `attribute [instance]` | none found in audit scope | No finding. |

Rule-16 conclusion: no automatic instance, opaque definition, provider, or default payload constructs a final source in the audited files.  The main danger remains manually supplying a `SearchMCSPMagnificationContract`, `PvsNPBridgeRequirement`, or `TreeMCSPSearchMagnificationSource` with an unaudited hard field.

## 9. Barrier relevance

| Barrier / theme | Frontier status |
|---|---|
| Natural proofs | Nothing formal in audited files.  No theorem or interface directly models natural proofs. |
| Relativization | Nothing formal in audited files. |
| Algebrization | Nothing formal in audited files. |
| Locality | Nothing formal in audited files. |
| Hardwiring | Indirectly relevant through `PpolyDAG`/`C_DAG` adapters; actual hardwiring exclusion is not proved here. |
| Support-cardinality-only | Nothing formal and no support-bound route in audited files. |
| Syntax-only filters | Nothing formal beyond parser/codec syntax interfaces; no syntax-only lower-bound filter is used as endpoint. |
| Normalization filters | Nothing formal in audited files. |
| Search-to-decision | Typed interface/staged: `SearchMCSPCompressionProblem`, `BoundedSearchSolver`, and prefix-extension language are search-oriented, but no search-to-decision lower-bound theorem is completed. |
| MCSP / magnification | Central typed interface/staged Prop: SearchMCSP weak targets, concrete tree-MCSP targets, and `SearchMCSPMagnificationContract`.  Kernel-checked only as dataflow once contract is supplied. |
| AC0[p] restricted lower bounds | Typed restricted interface in `PvsNPBridgeRequirements.lean`; explicitly not sufficient without DAG bridge. |
| Compression magnification | Typed interface and conditional final bridge in `CompressionMagnification.lean`; actual magnification theorem staged as field. |

## 10. Critical theorem map

### 10.1 `SearchMCSPMagnification`: magnification contract surface

The file defines the correct shape of the contract:

```text
SearchMCSPCompressionProblem
  + CircuitFamilyClass C
  + sizeBound
  → target : SearchMCSPWeakCircuitLowerBoundTarget
  → target.noBoundedSolver : Prop
  → SearchMCSPWeakCircuitLowerBound target       -- proof of weak LB
  → SearchMCSPMagnificationContract target       -- hard magnification field
  → VerifiedNPDAGLowerBoundSource
  → NP_not_subset_PpolyDAG / P_ne_NP
```

What is proven: record repackaging and final consequences **conditional** on `hWeak` and `hMag`.  What is staged: the lower bound `target.noBoundedSolver` and the magnification field `target.noBoundedSolver → VerifiedNPDAGLowerBoundSource`.

### 10.2 `PvsNPBridgeRequirements`: `VerifiedNPDAGLowerBoundSource` requirement

The file correctly enforces the separation between restricted AC0[p] lower bounds and mainline P-vs-NP progress:

```text
AC0pRestrictedLowerBoundSource
  → ¬ InAC0p model p L                      -- proven extraction
  ↛ NP_not_subset_PpolyDAG                   -- no theorem
  + RestrictedToVerifiedDAGBridge restricted -- staged hard bridge
  → VerifiedNPDAGLowerBoundSource
  → P_ne_NP
```

The bridge map is honest: restricted lower bounds are side-track unless paired with a verified DAG source bridge.

### 10.3 `CompressionMagnification`: compression-style magnification

This file provides the generic endpoint wrapper:

```text
SearchMCSPWeakLowerBound
  fields:
    weakLowerBound : Prop
    weakLowerBoundProof : weakLowerBound
    magnifiesToVerifiedDAGSource : weakLowerBound → VerifiedNPDAGLowerBoundSource
  → VerifiedNPDAGLowerBoundSource
  → NP_not_subset_PpolyDAG
  → P_ne_NP
```

The kernel checks the chain after the package exists.  It does not prove the package exists for any concrete target.

### 10.4 `SearchMCSPConcreteTargets`: tree-MCSP target instance

This file turns tree-MCSP into the generic search target:

```text
TreeCircuitWitnessCodec
  → TreeMCSPSearchWitnessEncoding.ofCodec
  → treeMCSPSearchProblem threshold encoding
  → treeMCSPSearchWeakLowerBoundTarget threshold encoding C sizeBound
  + weak lower bound
  + SearchMCSPMagnificationContract
  → TreeMCSPSearchMagnificationSource
  → VerifiedNPDAGLowerBoundSource
  → NP_not_subset_PpolyDAG / P_ne_NP
```

Local codec soundness and completeness are proven.  The weak lower bound and the magnification contract are not proven.

## 11. ContractExpansion track audit

### 11.1 R1-A `C_DAG_Adapter`: alignment status

Status: **aligned and kernel-checked as an adapter.**

- `C_DAG` uses exactly pnp3 `DagCircuit` family, evaluator, and size.
- `InPpolyDAG_to_C_DAG_family` converts existing pnp3 witnesses to pnp4 families, with a standard `Classical.choose` for the polynomial exponent.
- `C_DAG_family_to_InPpolyDAG` converts back to pnp3 `InPpolyDAG`.
- `PpolyDAG_decider_as_C_DAG_decider` exposes per-length DAG deciders from `PpolyDAG L`.

This is safe adapter infrastructure and should not be touched unless pnp3 DAG semantics change through a Foundational PR.

### 11.2 R1-B `PrefixExtensionLanguage`: language definition + NP budget

Status: **semantic language skeleton complete; NP theorem not proved.**

- The parser boundary and parsed input shape are present.
- `PrefixExtendable` states the intended existential full-witness semantics.
- `PrefixExtensionLanguage` is a Boolean language using classical decidability.
- Acceptance/rejection lemmas are proved.
- `PrefixExtensionNPVerifierBudget` and `PrefixExtensionNPVerifierPlan` explicitly stage missing NP-verifier obligations as `Prop` fields.

No `PrefixExtensionLanguage_in_NP` theorem exists in this file.

### 11.3 R1-B1 `PrefixExtensionLanguageNP`: codec-case `Decidable`

Status: **relation decidability is partly discharged; runtime is not.**

- Generic encoding relation decidability is reduced to an explicit `hdec` assumption.
- Codec-induced verification is decidable by decoding and finite truth-table checking.
- The target relation for a codec-derived tree-MCSP search problem is decidable.
- `TreeMCSPPrefixCoreBudgetProgress` still carries `parser_polynomial_time`, `relation_polynomial_time`, `witness_length_polynomial`, and blockers as Props.

This is real local progress but not NP membership.

### 11.4 R1-B2a `PrefixExtensionLanguageRuntime`: runtime budget

Status: **one arithmetic fact discharged; global runtime/NP formalism staged.**

- `treeMCSPPrefixAmbientLength` includes truth-table length, overhead, witness bits, and padding.
- `tableLen_le_treeMCSPPrefixAmbientLength` is proved.
- Polynomial boundedness predicates for threshold and witness bits are defined.
- Runtime-aware codec/parser/budget structures collect required facts.
- Most runtime statements remain `Prop` fields because no global polynomial-time parser/codec machine formalism is exposed here.

### 11.5 What is staged as `Prop`, what is discharged

Discharged:

- C_DAG/InPpolyDAG adapter conversions.
- Prefix-language semantic acceptance/rejection lemmas.
- Codec soundness/completeness for tree-MCSP witness encoding.
- Codec-induced relation decidability.
- Ambient truth-table-length inequality.

Staged as `Prop` or package fields:

- Parser implementation correctness beyond abstract parse.
- Parser polynomial time.
- Concrete serialization/codec availability.
- Witness length polynomial bound unless supplied to runtime budget.
- Relation polynomial time and truth-table verification runtime.
- Prefix language NP membership.
- Weak search-MCSP lower bound.
- Magnification to `VerifiedNPDAGLowerBoundSource`.

## 12. Gap to `ResearchGapWitness`

The audited Frontier files do not mention `ResearchGapWitness` directly.  The route to it must go through the frozen target:

```text
Tree/MCSP/Compression concrete target
  → SearchMCSPWeakCircuitLowerBound target              [missing mathematical/formal proof]
  → SearchMCSPMagnificationContract target              [missing mathematical magnification]
  → VerifiedNPDAGLowerBoundSource                       [staged hard source]
  → NP_not_subset_PpolyDAG                               [kernel-checked unpacking]
  → ResearchGapWitness.dagSeparation                    [not constructed here]
  → P_ne_NP                                             [existing conditional bridge]
```

Precise missing pieces:

1. A concrete `L` with `NP L` and `¬ PpolyDAG L`, or an honest theorem producing `VerifiedNPDAGLowerBoundSource`.
2. If using the search-MCSP route, a real proof of the selected weak lower bound `target.noBoundedSolver`.
3. A real magnification theorem converting that weak lower bound into `VerifiedNPDAGLowerBoundSource`.
4. For the prefix-extension track, concrete parser/serialization/runtime proofs plus a theorem that the prefix-extension language is in NP.
5. A non-circular theorem connecting restricted AC0[p] work to a `PpolyDAG` lower bound, not just to `¬ InAC0p`.

## 13. Cross-track integration

### 13.1 How `AlgorithmsToLowerBounds/` feed into Frontier

- `BridgeToPpolyDAG.lean` provides the hard endpoint structure `VerifiedNPDAGLowerBoundSource` and the checked bridge to `NP_not_subset_PpolyDAG`/`P_ne_NP`.
- `AC0pSuperPolynomialBridge` and related `AlgorithmsToLowerBounds` modules feed `AC0pRestrictedLowerBoundSource` and restricted conclusions, but Frontier correctly keeps them side-track until a DAG bridge is supplied.
- `TruthTableMCSP` supplies `TruthTable`, `treeMCSPPredicate`, `treeCircuitClass`, and `ComputesTruthTable`, which `SearchMCSPConcreteTargets` uses to define concrete tree-MCSP search targets.

### 13.2 How pnp3 `_Partial.lean` integrates

- `SearchMCSPConcreteTargets` and `PrefixExtensionLanguageRuntime` use `Pnp3.Models.Partial.tableLen n` as the truth-table instance length and ambient-length component.
- The integration is arithmetic/encoding-level only.  It does not import a pnp3 partial lower-bound route, refuted support bounds, or a final payload provider.
- Any future use of pnp3 `_Partial.lean` artifacts must be treated as infrastructure unless it reaches `VerifiedNPDAGLowerBoundSource` or `PpolyDAG` through an explicit bridge.

## 14. Reuse map

Safe to reuse:

- `VerifiedNPDAGLowerBoundSource` and `P_ne_NP_of_verified_source` as the canonical endpoint bridge, provided the source is honestly inhabited.
- `AC0pRestrictedLowerBoundSource` to label restricted AC0[p] milestones, provided they are not reported as mainline.
- `C_DAG` and its adapter theorems for aligning pnp4 circuit-family statements with pnp3 `PpolyDAG`.
- `SearchMCSPCompressionProblem`, `BoundedSearchSolver`, `SearchMCSPWeakCircuitLowerBoundTarget`, and `SearchProblemNoBoundedSolver` as search-lower-bound interfaces.
- `TreeCircuitWitnessCodec`, `TreeMCSPSearchWitnessEncoding.ofCodec`, and codec soundness/completeness for tree-MCSP witness encodings.
- `PrefixInput`, `PrefixParser`, `PrefixExtendable`, and prefix-language semantic lemmas for parser/serialization work.
- `TreeCircuitWitnessCodec.verifiesDecidable` and `treeMCSPSearchRelation_decidable_of_codec` as the decidability part of R1-B1.
- `treeMCSPPrefixAmbientLength` and `tableLen_le_treeMCSPPrefixAmbientLength` for runtime-budget audits.
- Surface tests and axiom audit imports for existing Frontier declarations.

Avoid / do not touch without explicit operator decision:

- Trust-root pnp3 complexity semantics and pnp4 `BridgeToPpolyDAG` endpoint shape.
- `C_DAG` semantics; changing it would be equivalent to changing endpoint alignment.
- Any attempt to fill `SearchMCSPMagnificationContract` with a wrapper around `VerifiedNPDAGLowerBoundSource` rather than a real theorem.
- Any attempt to report `AC0pRestrictedLowerBoundSource` as P-vs-NP mainline progress.
- Any `PrefixExtensionLanguage_in_NP` theorem unless every parser/codec/runtime budget field is concretely discharged.
- Any construction of `ResearchGapWitness`, `VerifiedNPDAGLowerBoundSource`, or `P_ne_NP` in Phase 0 audit work.

## 15. Gap map

### A. Engineering gaps

1. Concrete parser/serialization for `PrefixInput` is not implemented.
2. No concrete `TreeCircuitWitnessCodec` bit serialization is provided.
3. Public surface tests import the ContractExpansion modules and check selected declarations, but the AxiomsAudit imports `PrefixExtensionLanguageRuntime` rather than directly importing `PrefixExtensionLanguageNP`; this is currently okay through transitive import but could be made explicit in a future hygiene PR.
4. No machine-cost API ties parser/codec definitions to polynomial-time verifier statements.

### B. Formalization gaps

1. `PrefixExtensionLanguage_in_NP` is absent.
2. Parser well-formedness, malformed rejection, and exact length convention are mostly obligations rather than concrete theorems.
3. Runtime fields for decoding, parser, circuit evaluation, truth-table lookup, and relation checking are Props.
4. Polynomial bounds for threshold and witness bits need concrete witnesses for any chosen target.
5. A formal bridge from prefix-extension NP membership and weak search lower bound to a `VerifiedNPDAGLowerBoundSource` is not present.

### C. Mathematical gaps

1. Prove a nontrivial weak search-MCSP lower bound `target.noBoundedSolver` for a concrete target.
2. Prove the magnification theorem `target.noBoundedSolver → VerifiedNPDAGLowerBoundSource` for that target.
3. Bridge restricted AC0[p] lower bounds to `PpolyDAG`/`VerifiedNPDAGLowerBoundSource` without circularity.
4. Avoid known barriers: support-cardinality-only, syntax-only, or local restricted lower bounds cannot be treated as DAG lower bounds.
5. Any direct `NP_not_subset_PpolyDAG` proof remains the central open mathematical payload.

### D. Governance gaps

1. The Frontier route is mostly honest, but names ending in `Source` and theorems concluding `P_ne_NP` can be misleading unless PR descriptions emphasize their hypotheses.
2. Future tasks should distinguish “construct interface package” from “prove source theorem”; these are not the same.
3. The contract-expansion R1 labels are only in comments/file names; a central markdown route map could reduce drift.
4. Cross-audit coordination with A07/A10/A01 is needed before dispatching implementation tasks that might duplicate adapter or partial-track work.

## 16. Recommended Phase 1+ tasks

### Task 1: Explicit contract-expansion route map and no-overclaim doc

- **Exact files to touch:** `seed_packs/phase1_20engineer_parallel_dispatch/route_maps/A08_pnp4_frontier_contract_expansion.md` or another operator-approved markdown path.
- **Allowed scope:** Markdown-only diagram of `AC0[p] LB → SearchMCSPWeakCircuitLowerBound → SearchMCSPMagnificationContract → VerifiedNPDAGLowerBoundSource → ResearchGapWitness`, marking proven vs staged arrows.
- **Forbidden scope:** Lean edits; constructing sources; changing endpoint semantics; claiming P-vs-NP progress.
- **Expected output:** One route-map document consumed by Phase 1 dispatchers.
- **Estimated time:** 0.5 day.
- **Dependency on other audits:** Should cross-check A07 and A10.
- **Risk level:** Low.
- **Type:** markdown-only / operator decision.

### Task 2: Parser/serialization engineering plan for `PrefixInput`

- **Exact files to touch:** New task-specific markdown spec under operator-approved seed-pack path; later Lean files only if separately dispatched.
- **Allowed scope:** Specify concrete encoding of `tag,n,x,i,p,pad`, exact ambient length `M`, and proof obligations matching existing `PrefixParser`/`RuntimeAwarePrefixParser` fields.
- **Forbidden scope:** Proving `PrefixExtensionLanguage_in_NP`; touching final bridges; using `Classical.choose` to hide serialization.
- **Expected output:** A precise parser implementation task with acceptance tests and no lower-bound claims.
- **Estimated time:** 1 day for spec; Lean implementation separate.
- **Dependency on other audits:** Depends on A08; should consult A01 if pnp3 partial encodings are reused.
- **Risk level:** Medium.
- **Type:** markdown-only first, Lean later.

### Task 3: Concrete tree-circuit witness codec task

- **Exact files to touch:** Future Lean module under `pnp4/Pnp4/Frontier/ContractExpansion/` or `pnp4/Pnp4/AlgorithmsToLowerBounds/` only after operator assigns a path; surface tests and axioms audit if public.
- **Allowed scope:** Implement a concrete codec instantiating `TreeCircuitWitnessCodec` and prove `decode_encode`; expose decidability through existing `treeMCSPSearchRelation_decidable_of_codec`.
- **Forbidden scope:** Weak lower-bound proof; magnification contract; `VerifiedNPDAGLowerBoundSource`; endpoint theorem.
- **Expected output:** Codec object plus local soundness/decidability reuse, no complexity lower-bound claim.
- **Estimated time:** 2–4 days depending on existing circuit syntax support.
- **Dependency on other audits:** A08; possibly A07 for `TruthTableMCSP` details.
- **Risk level:** Medium.
- **Type:** Lean infrastructure.

### Task 4: Runtime API design for prefix verifier polynomial time

- **Exact files to touch:** Operator-approved design markdown first; later pnp4 runtime interface module if approved.
- **Allowed scope:** Define how parser runtime, decode runtime, circuit-evaluation runtime, truth-table lookup runtime, and relation runtime should map to `ComplexityInterfaces.NP`/`NP_TM`.
- **Forbidden scope:** Filling hard lower-bound or magnification fields; changing `ComplexityInterfaces.NP` semantics.
- **Expected output:** A non-circular runtime interface that can discharge `PrefixExtensionNPVerifierBudget` fields.
- **Estimated time:** 2 days for design; Lean implementation separate.
- **Dependency on other audits:** A08 and A01; maybe A10 for legacy marker cleanup.
- **Risk level:** Medium-high due to trust-root boundary.
- **Type:** operator decision / formalization planning.

### Task 5: Surface/audit hygiene for ContractExpansion NP module

- **Exact files to touch:** `pnp4/Pnp4/Tests/AxiomsAudit.lean`, `pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean` only if operator approves Lean hygiene.
- **Allowed scope:** Add explicit imports/checks for `PrefixExtensionLanguageNP` declarations currently reached transitively, such as `TreeCircuitWitnessCodec.verifiesDecidable` and `treeMCSPSearchRelation_decidable_of_codec`.
- **Forbidden scope:** Modifying theorem statements; adding source theorem; changing route semantics.
- **Expected output:** Tests make existing public surfaces explicit.
- **Estimated time:** 0.5 day.
- **Dependency on other audits:** A08 only.
- **Risk level:** Low.
- **Type:** Lean test hygiene.

## 17. Stop / hold recommendations

- **Hold any task claiming AC0[p] lower bounds are mainline P-vs-NP progress** unless it includes an explicit `PpolyDAG`/`VerifiedNPDAGLowerBoundSource` bridge.
- **Downgrade any task named “prove P ≠ NP from SearchMCSP”** to “stage/verify SearchMCSP contract obligations” unless it includes a credible proof of `SearchMCSPMagnificationContract` and weak lower bound.
- **Hold any `PrefixExtensionLanguage_in_NP` implementation** until parser serialization, runtime semantics, and codec witness length bounds are specified.
- **Do not touch `C_DAG` or pnp3 trust-root endpoint semantics** in Phase 1 infrastructure work.
- **No current A08 follow-up should construct `ResearchGapWitness`**; that would be a candidate/mainline proof task, not an audit/infrastructure task.

## 18. Honest caveats

- I verified signatures and proof intent, but did not reconstruct the complete dependency closure of every imported `AlgorithmsToLowerBounds` theorem.
- I did not inspect every proof body in `TruthTableMCSP` or AC0[p] bridge modules; I only checked how Frontier consumes them.
- I did not prove that all `#print axioms` outputs are semantically acceptable beyond running the repository check script.
- I searched NoGoLog only for relevant Frontier route names; I did not perform a full NoGoLog audit.
- I did not inspect every pnp3 `_Partial.lean` proof body; I only verified the direct `tableLen` integration in the audited files.
- This audit should be cross-checked with A07 for `AlgorithmsToLowerBounds/` and A10 for legacy/placeholder markers.

## 19. Commands run

- `git status --short --branch` / `git branch --show-current` / `git rev-parse HEAD` — used to establish branch/commit state before creating the A08 branch.
- `sed -n '1,260p' seed_packs/phase1_20engineer_parallel_dispatch/tasks/A08_audit_pnp4_frontier.md` — read exact task file.
- `sed -n ... RESEARCH_CONSTITUTION.md`, `README.md`, and `COMMON_WORKER_INSTRUCTIONS.md` — read required instructions structurally.
- `wc -l ...` over the 8 audited Frontier files plus key dependencies — scoped audit sizing.
- `sed`/`nl -ba` over all 8 listed Frontier files — full file inspection.
- `rg -n "ResearchGapWitness|NP_not_subset_PpolyDAG|VerifiedNPDAGLowerBoundSource|SearchMCSPMagnificationContract|SourceTheorem|gap_from" pnp4/Pnp4/Frontier` — 17 hard-payload hits, all interpreted above.
- `rg -n "RefutedRoute|Vacuous|supportBounds|MagnificationAssumptions|FinalPayloadProvider|via_ex_falso|weakRoute|Legacy|_Partial|TODO|placeholder|weak route|legacy route|default support bounds" pnp4/Pnp4/Frontier` — 2 comment hits for avoided placeholders; no route declarations.
- `rg -n "\bclass\b|\binstance\b|default_instance|attribute \[instance\]|\bFact\b|\bopaque\b|Classical\.choose|noncomputable def|Provider|Payload|Witness|Source|Default" pnp4/Pnp4/Frontier` — 90 broad hits, reduced to the classifications in Section 8.
- `rg -n "Pnp4\.Frontier\.(...)" lakefile.lean pnp4/Pnp4/Tests/...` — confirmed listed modules are in `lakefile.lean` and imported by tests/audit surface.
- `rg -n "check_.*(SearchMCSP|PvsNP|Prefix|C_DAG|treeMCSP|TreeCircuit|TreeMCSP|PolynomiallyBounded|RuntimeAware|BridgeRequirement|AC0pRestricted)" pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean` — checked public surface coverage.
- `./scripts/check.sh` — repository check run required by task; final status recorded in PR/final response.

## 20. Scope violations

None.  This audit created exactly one markdown report and did not edit Lean/source files, JSONL files, trust-root files, NoGoLog entries, lakefile, specs, outputs, or attempts.
