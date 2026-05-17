# A06 audit: `pnp3/Models/` and non-trust-root `pnp3/Complexity/`

Task: A06
Engineer handle: codex
Scope: markdown-only Phase 0 audit
Audited area: `pnp3/Models/*.lean` plus `pnp3/Complexity/*.lean` outside `Interfaces.lean` and `PsubsetPpolyInternal/`

## 1. Executive verdict

**Verdict: PARTIAL_BUT_USEFUL**

The audited area contains real, kernel-checked infrastructure for partial truth tables, fixed-parameter gap partial-MCSP languages, promise-problem solving, straight-line-to-DAG adapters, a fixed-slice DAG-to-formula hardwiring theorem, and the active `P_subset_PpolyDAG` inclusion route.  It is not a complete MCSP/circuit-model formalization: exact total MCSP, pnp4-style search-MCSP, and a concrete NP verifier for partial MCSP are not implemented here as closed constructions.  Several important objects are honest interfaces or packaging structures whose fields still require external witnesses, especially the partial-MCSP TM witness structures and the pnp4 `SearchMCSPCompressionProblem` analogue.  I found no direct construction or dependency on `ResearchGapWitness`, `NP_not_subset_PpolyDAG`, `VerifiedNPDAGLowerBoundSource`, `SearchMCSPMagnificationContract`, `SourceTheorem`, or `gap_from` within the audited files.  The safest reuse is the truth-table/partial-table infrastructure, promise interface, straight-line-to-DAG adapter, and the already-closed `P_subset_PpolyDAG` inclusion route; the weakest or most misleading reuse would be to treat fixed-slice hardwiring or partial-MCSP Prop wrappers as lower-bound progress.

## 2. Executive summary: MCSP/circuit-model completeness

The current pnp3 MCSP/model layer is **substantial infrastructure, not a complete mainline MCSP route**.

Implemented and kernel-checked:

- A finite partial truth-table model `PartialFunction n := Fin (2^n) → Option Bool` with mask/value encoding, decoding, cardinality lemmas, restriction operations, and consistency/counting equivalences.
- A separate tree-like `Pnp3.Models.Circuit n` model used for partial MCSP, with size and evaluation.
- Fixed-parameter gap partial-MCSP predicates `PartialMCSP_YES` / `PartialMCSP_NO`, a language `gapPartialMCSP_Language p`, a promise problem `GapPartialMCSPPromise p`, and basic YES/NO-to-language theorems.
- An asymptotic partial-MCSP language surface over valid lengths `2 * 2^n`, but without a concrete NP verifier.
- A canonical DAG circuit trust-root model in `Complexity.Interfaces` is reused but not modified by this audit.
- A straight-line-to-DAG adapter and active proof of `P_subset_PpolyDAG` from compiled TM runtime circuits.

Staged or incomplete:

- `gapPartialMCSP_in_NP` and asymptotic NP membership are only obtained from externally supplied `GapPartialMCSP_TMWitness` / `GapPartialMCSP_Asymptotic_TMWitness` structures.
- There is no pnp3 search-MCSP compression problem equivalent to pnp4 `SearchMCSPCompressionProblem`; pnp3 is mostly decision/promise-language oriented here.
- Fixed-slice `PpolyDAG → PpolyFormula` for `gapPartialMCSP_Language p` is real but deliberately non-mainline and potentially dangerous if overgeneralized: it hardwires one finite input length and fills other lengths with constant false.

## 3. Files audited

| File | Approximate role | Audit depth | Notes |
|---|---|---:|---|
| `RESEARCH_CONSTITUTION.md` | Governance and trust-root rules | Read structurally | Required reading; used to classify mainline vs side-track and hidden payload risk. |
| `seed_packs/phase1_20engineer_parallel_dispatch/README.md` | Phase dispatch rules | Read structurally | Required reading; older E-task language overridden by prompt. |
| `seed_packs/phase1_20engineer_parallel_dispatch/COMMON_WORKER_INSTRUCTIONS.md` | Common worker rules | Read structurally | Required reading; implementation sections treated as non-applicable because A06 is markdown-only Phase 0. |
| `seed_packs/phase1_20engineer_parallel_dispatch/tasks/A06_audit_pnp3_models_complexity.md` | Exact task scope | Read fully | Defines audited files and required report sections. |
| `pnp3/Models/PartialTruthTable.lean` | Partial truth-table representation and finite combinatorics | Read top-level declarations and key proof sections; searched fully | Large file; I inspected the public API and representative proofs, but did not reconstruct every cardinality proof line by line. |
| `pnp3/Models/Model_PartialMCSP.lean` | Partial-MCSP circuit model, gap predicates, languages, promise interface, NP witness packaging | Read fully at top-level and key proof bodies | Main MCSP file for this audit. |
| `pnp3/Complexity/Promise.lean` | Generic promise-problem interface | Read fully | Small file. |
| `pnp3/Complexity/PpolyDAG_StraightLineCore.lean` | Straight-line circuit adapter to canonical `DagCircuit` / `PpolyDAG` | Read fully | Important active adapter; names still include `Legacy` internally. |
| `pnp3/Complexity/PpolyDAG_from_StraightLine.lean` | Public re-export/entrypoint | Read fully | Import-only compatibility module. |
| `pnp3/Complexity/PsubsetPpolyDAG_Internal.lean` | Straight-line non-uniform class and reduction to `PpolyDAG` | Read fully | Non-trust-root but imports canonical interface. |
| `pnp3/Complexity/PpolyFormula_from_PpolyDAG_FixedSlice.lean` | Fixed-slice DAG-to-formula hardwiring for partial MCSP | Read fully | Real theorem, but weak/fixed-slice only. |
| `pnp3/Complexity/Simulation/TM_Encoding.lean` | Thin aliases to internal TM semantics and unpacking `P` witnesses | Read fully | Mostly adapter aliases. |
| `pnp3/Complexity/Simulation/Circuit_Compiler.lean` | Active compiled-runtime proof of `P_subset_PpolyDAG` | Read top-level and key endpoints; searched fully | Long arithmetic/proof file; I focused on public contracts and endpoint route. |
| `pnp3/Complexity/Interfaces.lean` | Trust-root interfaces | Skimmed/queried only | Read only as context; excluded from audit scope and not recommended for edits. |
| `pnp3/Magnification/UnconditionalResearchGap.lean` | Trust-root final-gap interface | Skimmed/queried only | Optional context for dependency checks; not in edit scope. |
| `pnp4/Pnp4/Frontier/SearchMCSPMagnification.lean` | pnp4 search-MCSP target surface | Searched and read relevant structure | Used only for cross-reference against `SearchMCSPCompressionProblem`. |
| `pnp4/Pnp4/Frontier/SearchMCSPConcreteTargets.lean` | Concrete pnp4 tree-MCSP search problem | Searched and read relevant definition | Used only for cross-reference against pnp3 partial-MCSP models. |

Discovered files matching the A06 command:

```text
pnp3/Complexity/PpolyDAG_StraightLineCore.lean
pnp3/Complexity/PpolyDAG_from_StraightLine.lean
pnp3/Complexity/PpolyFormula_from_PpolyDAG_FixedSlice.lean
pnp3/Complexity/Promise.lean
pnp3/Complexity/PsubsetPpolyDAG_Internal.lean
pnp3/Complexity/Simulation/Circuit_Compiler.lean
pnp3/Complexity/Simulation/TM_Encoding.lean
pnp3/Models/Model_PartialMCSP.lean
pnp3/Models/PartialTruthTable.lean
```

## 4. Top-level theorem / structure inventory

### `pnp3/Models/PartialTruthTable.lean`

| Declaration | Type/signature summary | Classification | Hard-payload dependency |
|---|---|---|---|
| `Partial.tableLen` | `Nat → Nat`, defined as `2^n` | canonical infrastructure | None |
| `Partial.inputLen` | `Nat → Nat`, defined as `2 * tableLen n` | canonical infrastructure | None |
| `Partial.maskIndex`, `Partial.valIndex` | Encode mask/value halves of a partial table input | canonical infrastructure | None |
| `Partial.maskPart`, `Partial.valPart` | Split encoded partial-table bitstrings | canonical infrastructure | None |
| `PartialFunction` / `PartialTruthTable` | `Fin (Partial.tableLen n) → Option Bool` | canonical infrastructure | None |
| `Fintype` / `DecidableEq` instances for `PartialFunction` | Finite/enumerable partial functions | harmless infrastructure | None |
| `decodePartial`, `encodePartial` | Decode/encode mask++values partial-table format | canonical infrastructure | None |
| `encodePartial_decodePartial_*` | Lemmas about encode-after-decode on mask/value coordinates | canonical infrastructure | None |
| `card_partialTables` | Cardinality of partial functions is `3^(tableLen n)` | canonical theorem | None |
| `forget`, `setDefined`, `mergeLeft` | Partial-table transformations | canonical infrastructure | None |
| `definedPositions`, `undefinedPositions`, `definedCount`, `undefinedCount` | Finset/count helpers | canonical infrastructure | None |
| `card_tablesWithDefinedSet_le_pow` | Bound for partial tables with a fixed defined set | canonical theorem | None |
| `TotalFunction`, `consistentWithTotal`, `consistentTotal` | Total extension compatibility | canonical infrastructure | None |
| `consistentPartialEquiv`, `consistentTotalEquiv` | Equivalences for counting compatible partial/total tables | canonical theorem/infrastructure | None |
| `card_consistentPartial_withTotal`, `card_rawEncodingsConsistentWithTotal_eq_three_pow`, `card_consistentTotal` | Counting compatible encodings/extensions | canonical theorem | None |
| `applyRestrictionToInput`, `applyRestrictionToAssignment`, `applyRestrictionToTable` | Restriction maps | canonical infrastructure | None |
| `decodePartial_applyRestrictionToInput`, `decodePartial_encodePartial`, `restriction_preserves_type` | Round-trip/restriction preservation | canonical theorem | None |

### `pnp3/Models/Model_PartialMCSP.lean`

| Declaration | Type/signature summary | Classification | Hard-payload dependency |
|---|---|---|---|
| `Circuit` | Inductive tree Boolean circuit over `n` inputs | canonical infrastructure for partial MCSP, but separate from canonical `DagCircuit` | None |
| `Circuit.size`, `Circuit.eval` | Tree circuit size/evaluation | canonical infrastructure | None |
| `bitVecToNat`, `assignmentIndex` | Assignment-to-truth-table indexing | canonical infrastructure | None |
| `assignmentIndex_surjective` | Every table index is hit by some assignment | canonical theorem | None |
| `circuitCountBound` | Recursive over-count of tree circuits of size `≤ s` | canonical/side infrastructure | None |
| `GapPartialMCSPParams` | Parameters `n`, `sYES`, `sNO`, gap, largeness, positivity, counting bound | staged parameter package | None |
| `partialInputLen`, `polylogBudget` | Input length and locality budget helper | canonical infrastructure | None |
| `truthTableFunction`, `circuitComputes` | Interpret total truth table and tree circuit agreement | canonical infrastructure | None |
| `is_consistent` | Tree circuit consistent with defined entries of partial table | canonical infrastructure | None |
| `totalTableToPartial`, `encodeTotalAsPartial` | Total-to-partial embedding | canonical adapter | None |
| `is_consistent_total_iff`, `decodePartial_encodeTotal` | Total/partial bridge theorems | canonical theorem | None |
| `PartialMCSP_YES`, `PartialMCSP_NO` | Fixed-parameter gap partial-MCSP predicates | staged Prop / honest specification | None |
| `is_consistent_bool`, `gapPartialMCSP_standardVerifier` | Boolean consistency checker and certificate verifier | useful infrastructure | None |
| `gapPartialMCSP_standardVerifier_accepts_of_yes` | A YES witness gives verifier acceptance | canonical theorem, one-sided | None |
| `restrictInput`, `restrictTable`, `restriction_preserves_type_partial` | Partial-MCSP restriction bridge | canonical theorem | None |
| `PartialMCSPInput` | Input type abbreviation for fixed parameters | infrastructure | None |
| `PartialMCSP_YES_at` | Unpacked YES predicate for asymptotic language | staged Prop | None |
| `GapPartialMCSPAsymptoticSpec` | Functions `sYES`, `sNO` plus gap/positivity | staged parameter package | None |
| `partialInputLen_injective` | `Partial.inputLen` injective | canonical theorem | None |
| `gapPartialMCSP_AsymptoticLanguage` | Noncomputable language over all input lengths | canonical interface, but uses `Classical.choose` | None |
| `gapPartialMCSP_Language` | Fixed-parameter language, true iff YES on the one encoded length | canonical interface | None |
| `GapPartialMCSPPromise` | Promise problem induced by fixed language | harmless interface | None |
| `partial_no_not_yes` | NO excludes YES by gap | canonical theorem | None |
| `gapPartialMCSP_language_true_iff_yes` | Correct-length language iff YES | canonical theorem | None |
| `gapPartialMCSP_language_false_of_no` | NO implies language false | canonical theorem | None |
| `gapPartialMCSP_yes_of_small`, `gapPartialMCSP_no_of_large` | YES/NO predicates land in promise sets | canonical theorem | None |
| `solvesPromise_gapPartialMCSP_iff` | Promise solver iff pointwise equality to language | canonical theorem | None |
| `gapPartialMCSP_in_NP`, `gapPartialMCSP_Asymptotic_in_NP` | NP membership abbreviations | staged target Prop | None |
| `GapPartialMCSP_TMWitness`, `GapPartialMCSP_Asymptotic_TMWitness` | Concrete TM witness packages with runtime/correctness fields | honest staging / possible wrapper risk if overclaimed | Requires external TM/correctness payload, but not RGW/NP lower bound |
| `gapPartialMCSP_in_NP_TM_of_witness`, `gapPartialMCSP_Asymptotic_in_NP_TM_of_witness` | Package a witness as NP membership | conditional theorem | Depends on supplied witness structure |
| `gapPartialMCSP_in_NP_of_TM`, `gapPartialMCSP_Asymptotic_in_NP_of_TM` | Coerce strict TM NP membership to canonical NP | conditional theorem | Depends on supplied NP/TM membership proof |

### `pnp3/Complexity/Promise.lean`

| Declaration | Type/signature summary | Classification | Hard-payload dependency |
|---|---|---|---|
| `PromiseProblem` | `Yes`, `No`, and `Disjoint Yes No` | harmless interface | None |
| `SolvesPromise` | Solver accepts all YES and rejects all NO | harmless interface | None |

### `pnp3/Complexity/PpolyDAG_StraightLineCore.lean` and re-export

| Declaration | Type/signature summary | Classification | Hard-payload dependency |
|---|---|---|---|
| `LegacyStraightOp` | Straight-line operations `const/not/and/or` | legacy name but active adapter input | None |
| `LegacyStraightLineCircuit` | Gate count, predecessor-only gates, output wire | legacy name but active adapter input | None |
| `StraightLineCircuit` | Abbrev for legacy-named structure | canonical adapter name | None |
| `toDagWire`, `toDagOp`, `toDag`, `withOutput` | Translate straight-line circuits to canonical `DagCircuit` | canonical adapter | None |
| `eval`, `evalWire` | Semantics via translated `DagCircuit` | canonical adapter | None |
| `eval_toDag`, `size_toDag`, `eval_eq_evalWire` | Definitional adapter facts | canonical theorem | None |
| `ppolyDAG_of_straightLine_family` | Polynomially bounded straight-line family implies `PpolyDAG L` | canonical theorem | Depends on supplied family/correctness, no hard lower-bound payload |
| `PpolyDAG_from_StraightLine.lean` | Imports the core adapter only | compatibility module | None |

### `pnp3/Complexity/PsubsetPpolyDAG_Internal.lean`

| Declaration | Type/signature summary | Classification | Hard-payload dependency |
|---|---|---|---|
| `InPpolyStraightLine` | Constructive package for straight-line family deciding `L` | staged/conditional witness package | Depends on supplied family/correctness |
| `PpolyStraightLine` | Existential Prop over `InPpolyStraightLine` | staged Prop | Depends on supplied witness |
| `ppolyDAG_of_ppolyStraightLine` | Straight-line nonuniformity implies `PpolyDAG` | canonical theorem | Depends on supplied `PpolyStraightLine` witness |
| `P_subset_PpolyStraightLine` | Inclusion target `∀ L, P L → PpolyStraightLine L` | staged Prop | Depends on future/provided inclusion proof |
| `P_subset_PpolyDAG_of_P_subset_PpolyStraightLine` | Inclusion reduction | conditional theorem | Depends on supplied inclusion proof |

### `pnp3/Complexity/PpolyFormula_from_PpolyDAG_FixedSlice.lean`

| Declaration | Type/signature summary | Classification | Hard-payload dependency |
|---|---|---|---|
| `DagCircuit.toFormula` | Noncomputable DNF formula for a fixed DAG truth table | weak/fixed-slice infrastructure | None |
| `DagCircuit.eval_toFormula` | Formula computes same function as fixed DAG | canonical theorem for fixed finite slice | None |
| `ppolyFormula_of_ppolyDAG_gapPartialMCSP_fixedSlice` | `PpolyDAG (gapPartialMCSP_Language p) → PpolyFormula (...)` | weak route / fixed-slice hardwiring theorem | Depends on supplied `PpolyDAG` upper-bound witness, not lower-bound payload |

### `pnp3/Complexity/Simulation/TM_Encoding.lean`

| Declaration | Type/signature summary | Classification | Hard-payload dependency |
|---|---|---|---|
| `Move`, `TM`, `Configuration`, `TM.*` abbrevs | Aliases to internal TM semantics | harmless adapter | None |
| `exists_poly_tm_for_P` | Unpacks `P L` into a TM, exponent, runtime bound, correctness | canonical theorem/adapter | Depends on supplied `P L` proof |

### `pnp3/Complexity/Simulation/Circuit_Compiler.lean`

| Declaration | Type/signature summary | Classification | Hard-payload dependency |
|---|---|---|---|
| `CompiledAcceptCircuitEvalAgreementLinear` | Prop: adapter eval agrees with internal straight-line eval on accept circuit | staged Prop contract | None by itself |
| `CompiledAcceptOutputWireAgreementLinear` | Narrower output-wire agreement contract | staged Prop contract | None by itself |
| `compiledAcceptEvalAgreementLinear_of_outputWireAgreement` | Output-wire agreement implies accept-circuit agreement | canonical theorem | Depends on supplied output-wire agreement |
| `CompiledRuntimeCircuitSizeBoundLinear` | Prop: compiled runtime circuits are polynomial-size after `toDag` | staged Prop contract | None by itself |
| `CompiledRuntimeAcceptCorrectnessLinear` | Prop: compiled accept circuit equals TM acceptance | staged Prop contract | None by itself |
| `CompiledRuntimeBudgetPolyBound` | Prop: runtime budget is polynomially bounded | staged Prop, then internally proved | None by itself |
| `compiledRuntimeBudgetPolyBound_internal` | Internal proof of runtime budget polynomial bound | canonical theorem | Depends on TM runtime hypothesis only |
| `compiledRuntimeCircuitSizeBoundLinear_internal` | Internal proof of size bound | canonical theorem | Depends on TM runtime hypothesis only |
| `compiledRuntimeAcceptCorrectnessLinear_of_stepSpecProvider` | Correctness from supplied step-spec provider | conditional theorem | Depends on step-spec provider |
| `compiledAcceptOutputWireAgreementLinear_internal` | Closed adapter/internal eval-wire agreement | canonical theorem | No hard lower-bound payload |
| `PsubsetPpolyCompiledRuntimeLinearOutputContracts` | Bundle of three contracts | staged Prop/bundle | Depends on fields if supplied |
| `proved_P_subset_PpolyDAG_of_compiledRuntimeLinearOutputContracts` | Contracts imply `P_subset_PpolyDAG` | conditional theorem | Depends on contract bundle |
| `proved_P_subset_PpolyDAG_internal` | No-arg internal proof of `P_subset_PpolyDAG` | canonical theorem, upper-bound inclusion only | No RGW/NP lower-bound payload |
| `proved_P_subset_PpolyDAG_internal_defeq_linear` | Audit helper identifying endpoint route | audit-support theorem | None |

## 5. Kernel-checked content

The following content is actually kernel-checked in the audited files:

1. **Partial truth-table encoding and combinatorics.**  The repository proves facts about `Partial.tableLen`, `Partial.inputLen`, mask/value indexing, finite instances for partial functions, encode/decode behavior, defined/undefined sets, counting bounds, compatible total functions, and restriction preservation.  These are concrete finite combinatorics and encoding facts, not lower bounds.

2. **Partial-MCSP fixed-parameter semantics.**  The file proves that `assignmentIndex` is surjective, total tables embedded as partial tables agree with `circuitComputes`, encoded total tables decode back to their embedded partial table, NO instances cannot also be YES instances under the `sYES + 1 ≤ sNO` gap, and the fixed language returns true exactly on the YES predicate at the correct length.  It also proves NO implies false, YES/NO map into the promise sets, and solving the promise problem is equivalent to pointwise equality with the language.

3. **One-sided verifier completeness for partial MCSP.**  `gapPartialMCSP_standardVerifier_accepts_of_yes` proves that if a YES witness circuit exists, the standard verifier accepts some encoded certificate.  This is not a full NP-membership proof because the TM machine/runtime/correctness package is only supplied later through `GapPartialMCSP_TMWitness`.

4. **Straight-line-to-DAG upper-bound adapter.**  The straight-line adapter translates predecessor-only straight-line circuits into canonical `DagCircuit`s, preserves evaluation definitionally through `eval`, and proves that any polynomially bounded straight-line family gives `PpolyDAG L`.

5. **Active `P ⊆ PpolyDAG` route.**  The compiled-runtime route proves polynomial budget/size obligations, output-wire evaluator agreement, and the final no-argument theorem `proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG`.  This is an **upper-bound inclusion** and must not be confused with a lower bound or with P-vs-NP progress.

6. **Fixed-slice DAG-to-formula hardwiring.**  `DagCircuit.eval_toFormula` proves the noncomputable DNF produced from one DAG's truth table computes the same finite function.  `ppolyFormula_of_ppolyDAG_gapPartialMCSP_fixedSlice` proves that for the fixed-slice language `gapPartialMCSP_Language p`, a `PpolyDAG` family yields a `PpolyFormula` family by hardwiring the relevant length and using constant false off-slice.  This theorem is kernel-checked but intentionally weak and should not be generalized without care.

## 6. Staged / placeholder / Prop-only content

| Object | Staging type | Assessment |
|---|---|---|
| `PartialMCSP_YES`, `PartialMCSP_NO`, `PartialMCSP_YES_at` | Existential/universal `Prop` predicates | Honest specification of decision/promise predicates.  Not a theorem by itself. |
| `GapPartialMCSPParams` | Structure with assumptions as fields | Honest parameter package; `circuit_bound_ok` is a mathematical assumption field, not proved from `n_large`. |
| `GapPartialMCSPAsymptoticSpec` | Structure with threshold functions and fields | Honest interface; no asymptotic lower/upper theorem is hidden. |
| `gapPartialMCSP_in_NP`, `gapPartialMCSP_Asymptotic_in_NP` | Abbrev to `NP_TM` | Staged target Prop; does not construct a verifier. |
| `GapPartialMCSP_TMWitness`, `GapPartialMCSP_Asymptotic_TMWitness` | Structures packaging machine/runtime/correctness | Honest staging, but wrapper risk if someone treats the structure value as already available. |
| `CompiledAcceptCircuitEvalAgreementLinear`, `CompiledAcceptOutputWireAgreementLinear`, `CompiledRuntimeCircuitSizeBoundLinear`, `CompiledRuntimeAcceptCorrectnessLinear`, `CompiledRuntimeBudgetPolyBound` | Prop contracts | Initially staged contracts; several are discharged internally in the compiler route.  Safe when using named `_internal` theorems; risky if supplied as opaque assumptions elsewhere. |
| `PsubsetPpolyCompiledRuntimeLinearOutputContracts` | Prop bundle | Harmless as a bundle when instantiated by internal theorems; potential wrapper risk if an external provider is accepted without audit. |
| `PpolyStraightLine`, `P_subset_PpolyStraightLine` | Existential/inclusion Props | Honest upper-bound staging.  Not lower-bound progress. |
| `PromiseProblem`, `SolvesPromise` | Generic interface | Harmless interface. |

No `axiom`, `sorry`, `admit`, or `opaque` was found in the audited files by the required searches.

## 7. MCSP variants cross-reference

| Variant | pnp3 audited status | Main declarations | pnp4 `SearchMCSPCompressionProblem` alignment | Notes |
|---|---|---|---|---|
| Partial-MCSP | Implemented as fixed-parameter decision/promise language over partial truth tables | `PartialTruthTable`, `PartialMCSP_YES`, `PartialMCSP_NO`, `gapPartialMCSP_Language`, `GapPartialMCSPPromise` | **Partial alignment only** | pnp3 instances are `2 * 2^n` mask/value encodings; pnp4 search problems use `instanceBits`, `witnessBits`, `promise`, `relation`, `totalOnPromise`. |
| Gap partial-MCSP | Implemented with thresholds `sYES`, `sNO` and gap proof | `GapPartialMCSPParams`, `PartialMCSP_YES`, `PartialMCSP_NO`, `partial_no_not_yes` | **Partial alignment only** | pnp3 has decision promise; pnp4 mainline wants search relation and totality on promise. |
| Asymptotic partial-MCSP | Staged language surface exists | `GapPartialMCSPAsymptoticSpec`, `gapPartialMCSP_AsymptoticLanguage` | **Weak alignment** | Valid-length selection uses `Classical.choose`; no search witness relation. |
| Exact total MCSP | Not implemented in A06 audited pnp3 files as a first-class exact-MCSP model | Total embedding helpers only: `totalTableToPartial`, `encodeTotalAsPartial`, `is_consistent_total_iff` | **No direct alignment** | Some archive/pnp4 files have other MCSP notions, but not this audited pnp3 scope. |
| Gap total MCSP | Not implemented as separate pnp3 audited model | Only total-to-partial bridge helpers | **No direct alignment** | Future work should avoid duplicating pnp4 truth-table MCSP unless an explicit adapter is needed. |
| Search-MCSP | Not implemented in pnp3 audited files | None; only verifier/certificate helper for decision YES | **Missing** | pnp4 `SearchMCSPCompressionProblem` has a relation and totality field; pnp3 partial MCSP does not define witness-bit length/relation as a search problem. |
| Tree-MCSP search | Not implemented in pnp3 audited files | None | **pnp4-owned** | pnp4 concrete target uses `treeMCSPSearchProblem`; pnp3 has a tree-like `Circuit`, but no pnp4-compatible search surface. |
| Formula-MCSP | Not implemented as a decision/search model here | Fixed-slice bridge only | **No direct alignment** | The fixed-slice bridge produces formula upper bounds from DAG upper bounds for `gapPartialMCSP_Language p`; it is not a formula-MCSP definition. |

## 8. Circuit model audit

There are at least three circuit notions relevant to this audit:

1. **`ComplexityInterfaces.DagCircuit`** in the trust root.  It is the canonical nonuniform DAG target behind `PpolyDAG`.  A `DagCircuit n` has a gate count, gate function, output wire, `size`, and evaluator.  This audit did not modify it.

2. **`ComplexityInterfaces.FormulaCircuit`** in the trust root.  It is the canonical formula target behind `PpolyFormula`.  The audited fixed-slice bridge builds a `FormulaCircuit` by enumerating satisfying assignments of one fixed DAG.

3. **`Pnp3.Models.Circuit`** in `Model_PartialMCSP.lean`.  This is a local inductive/tree Boolean circuit with constructors `input`, `const`, `not`, `and`, `or`, with recursive size and evaluation.  Partial-MCSP YES/NO predicates quantify over this local circuit type, not over `DagCircuit` or `FormulaCircuit`.

Relationship summary:

- `Pnp3.Models.Circuit` is **not definitionally equal** to `DagCircuit` or `FormulaCircuit`.
- `PartialMCSP_YES` and `PartialMCSP_NO` use `Pnp3.Models.Circuit`; therefore they are tree-circuit partial-MCSP notions unless an adapter theorem is added later.
- `StraightLineAdapter.LegacyStraightLineCircuit` / `StraightLineCircuit` is another syntax used for upper-bound compilation; it translates to `DagCircuit` through `toDag`.
- `DagCircuit.toFormula` is a truth-table/DNF hardwiring construction for a fixed DAG, not a size-efficient general DAG-to-formula simulation.
- Future workers should be explicit about which circuit model a theorem uses.  In particular, a lower bound against `Pnp3.Models.Circuit` or `FormulaCircuit` is not a lower bound against `PpolyDAG` unless bridged explicitly.

## 9. Truth-table infrastructure

`PartialTruthTable.lean` is the strongest reusable part of the audited MCSP layer.

Implemented:

- `Partial.tableLen n = 2^n` and `Partial.inputLen n = 2 * tableLen n`.
- Mask/value-half indexing through `maskIndex` and `valIndex`.
- Encoding format `mask ++ values` through `encodePartial`, `decodePartial`, `maskPart`, `valPart`.
- Finite typeclass support for `PartialFunction n` and related subtype/index constructions.
- Defined/undefined position operations and count lemmas.
- Total-function compatibility and extension counting.
- Restriction operations on raw encoded inputs, assignments, and partial tables.
- Round-trip theorem `decodePartial_encodePartial` and restriction preservation theorem `restriction_preserves_type`.

Caveat:

- This file provides strong finite infrastructure, but it does not define a search problem or compression relation.  It should be reused as data representation, not cited as a lower-bound theorem.

## 10. Non-trust-root `pnp3/Complexity/` file-by-file audit and external usage

### `Promise.lean`

- Defines the basic promise-problem interface.
- Used externally by lower-bound, barrier, archive, and partial-MCSP modules.
- Safe to reuse as a lightweight interface.
- No hard payload.

### `PpolyDAG_StraightLineCore.lean`

- Defines the straight-line circuit syntax and adapter to canonical `DagCircuit`.
- Despite `Legacy` names, the module doc says it is the canonical non-legacy entrypoint for the active route.
- Used by the internal `P ⊆ PpolyDAG` compiler route and straight-line semantics.
- Safe to reuse for upper-bound construction; do not use as lower-bound evidence.

### `PpolyDAG_from_StraightLine.lean`

- Compatibility/import entrypoint only.
- Safe to import, but new code should prefer the namespace/module indicated by its doc-comment.

### `PsubsetPpolyDAG_Internal.lean`

- Packages straight-line nonuniform families and proves reduction into canonical `PpolyDAG`.
- Used by `Magnification/FinalResultMainline.lean` and `Complexity/Simulation/Circuit_Compiler.lean`.
- Safe upper-bound adapter; not lower-bound progress.

### `PpolyFormula_from_PpolyDAG_FixedSlice.lean`

- Proves fixed-slice hardwiring from DAG upper bound to formula upper bound for one `gapPartialMCSP_Language p`.
- Used by tests and magnification/falsifiability probes.
- Reuse only for audits/probes that explicitly need fixed-slice behavior.  Do not generalize to `PpolyDAG ⊆ PpolyFormula`, and do not interpret as a nontrivial lower-bound bridge.

### `Simulation/TM_Encoding.lean`

- Thin adapter over internal TM definitions and unpacking theorem for `P L`.
- Safe to reuse when extracting machine/runtime/correctness from `P`.
- Does not construct lower-bound payload.

### `Simulation/Circuit_Compiler.lean`

- Active, kernel-checked upper-bound route to `P_subset_PpolyDAG`.
- Used by pnp4 `BridgeToPpolyDAG` and `CompressionMagnification` as the upper-bound inclusion ingredient.
- Safe to reuse as the canonical `P ⊆ PpolyDAG` theorem.  It should not be touched in Phase 1 unless the task is specifically an upper-bound/compiler audit or API hygiene task.

### `PsubsetPpolyDAG_Internal.lean` versus trust-root exclusions

- This file is non-trust-root by the A06 discovery command, but it imports and targets trust-root classes from `Complexity.Interfaces`.
- Recommended edits should be avoided unless a dedicated compiler/adapter task requests them; accidental changes here could affect pnp4 bridges.

## 11. Refuted / vacuous / legacy route check

Required search terms found:

- `Legacy` appears in `LegacyStraightOp` and `LegacyStraightLineCircuit` names.  Interpretation: **legacy naming, active adapter**.  The file's doc-comment says the module is the canonical non-legacy entrypoint, and `StraightLineCircuit` is a neutral abbrev.  This is not a refuted route by itself, but the names are a governance/doc drift risk.
- `_Partial` appears in the filename `Model_PartialMCSP.lean`, not as a route-marker issue.
- No occurrences found in the audited files for `RefutedRoute`, `Vacuous`, `supportBounds`, `MagnificationAssumptions`, `FinalPayloadProvider`, `via_ex_falso`, `weakRoute`, `_Legacy` theorem suffixes, `TODO`, or `placeholder`.

Isolation assessment:

- The fixed-slice theorem is a **weak route** semantically even though it is not named `weakRoute`: it is isolated in a file whose name includes `FixedSlice`, and the doc-comment explicitly warns against generic `PpolyDAG ⊆ PpolyFormula` overstatement.
- The straight-line legacy names are used in active upper-bound infrastructure; renaming them would be broad and should not be done casually in Phase 1.

## 12. Hidden payload / Rule 16 check

Required hidden-payload search terms found and interpretation:

| Occurrence | Classification | Interpretation |
|---|---|---|
| `instance (n : Nat) : Fintype (PartialFunction n)` | harmless infrastructure | Needed for finite enumeration/counting. |
| `noncomputable instance (n : Nat) : DecidableEq (PartialFunction n)` | harmless infrastructure | Classical decidability for finite function type; no lower-bound payload. |
| `noncomputable def tablesWithDefinedSet`, `tablesWithDefinedSetList` | harmless infrastructure | Finset/list enumeration helpers. |
| `noncomputable instance` for compatibility subtypes/index types | harmless infrastructure | Supports cardinality proofs over finite subtypes. |
| `consistentPartialEquiv`, `consistentTotalEquiv`, `rawEncodingsConsistentWithTotal` | standard finite equivalence/counting infrastructure | No hidden complexity payload. |
| `DagCircuit.toFormula` | standard finite truth-table expansion | Noncomputable because it enumerates satisfying assignments; fixed-slice and potentially exponential, not a hidden lower-bound theorem. |
| `gapPartialMCSP_AsymptoticLanguage` with `Classical.choose` | standard exponent/shape extraction? actually valid-length witness extraction | Harmless if documented as language definition; possible determinism/readability risk.  It chooses `n` from `∃ n, N = Partial.inputLen n`.  `partialInputLen_injective` exists but is not used to canonicalize the choice visibly. |
| `gapPartialMCSP_Language` | harmless classical by-cases over length/YES Prop | It decides a Prop by classical choice for a language definition, not a lower-bound payload. |
| `class` hits in comments only | harmless | No Lean `class` declarations in the audited files. |
| `opaque`, `default_instance`, `attribute [instance]`, `Fact`, `Provider/Payload/Witness/Source/Default` noncomputable defs | none found in audited files | No direct hidden-payload risk from those patterns. |

No occurrence in this audited scope constructs `ResearchGapWitness`, `NP_not_subset_PpolyDAG`, `VerifiedNPDAGLowerBoundSource`, `SearchMCSPMagnificationContract`, `SourceTheorem`, or `gap_from`.

## 13. Barrier relevance

| Barrier / topic | Audited-file status | Notes |
|---|---|---|
| Natural proofs | Nothing direct | No natural-proofs theorem/interface in A06 files. |
| Relativization | Nothing direct | No relativization theorem/interface in A06 files. |
| Algebrization | Nothing direct | No algebrization theorem/interface in A06 files. |
| Locality | Typed helper only | `polylogBudget`, partial restrictions, and imports by locality modules are relevant, but locality theorems are outside A06 files. |
| Hardwiring | Actual theorem | `DagCircuit.toFormula` and `ppolyFormula_of_ppolyDAG_gapPartialMCSP_fixedSlice` hardwire a fixed truth table/slice. |
| Support-cardinality-only | Indirect/audit relevance | Partial-table cardinality/counting exists; no support-bound route names in A06 files. |
| Syntax-only filters | Nothing direct | No provenance/syntax filter here. |
| Normalization filters | Nothing direct | No normalization filter here. |
| Search-to-decision | Missing | pnp3 audited files have verifier/promise decision surfaces, not pnp4 search problem relation. |
| MCSP / magnification | Typed interface and partial actual theorems | Partial-MCSP models and promise semantics exist; no mainline magnification contract or verified DAG lower-bound source exists here. |

## 14. Reuse map

### Safe definitions and theorems

- `Partial.tableLen`, `Partial.inputLen`, `Partial.maskIndex`, `Partial.valIndex`, `encodePartial`, `decodePartial`.
- `PartialFunction`, `PartialTruthTable`, `definedPositions`, `undefinedPositions`, `definedCount`, `undefinedCount`.
- `decodePartial_encodePartial`, `restriction_preserves_type`, `decodePartial_applyRestrictionToInput`.
- `Pnp3.Models.Circuit`, `Circuit.size`, `Circuit.eval`, `is_consistent` for tree-like partial-MCSP statements.
- `totalTableToPartial`, `encodeTotalAsPartial`, `is_consistent_total_iff`, `decodePartial_encodeTotal` for total-to-partial adapters.
- `PartialMCSP_YES`, `PartialMCSP_NO`, `partial_no_not_yes`, `gapPartialMCSP_language_true_iff_yes`, `gapPartialMCSP_language_false_of_no`, `solvesPromise_gapPartialMCSP_iff`.
- `PromiseProblem`, `SolvesPromise`.
- `StraightLineAdapter.toDag`, `StraightLineAdapter.eval`, `ppolyDAG_of_straightLine_family`.
- `ppolyDAG_of_ppolyStraightLine` and `proved_P_subset_PpolyDAG_internal` for upper-bound inclusion work.

### Adapter modules

- `Complexity.PpolyDAG_from_StraightLine` is a compatibility import.
- `Complexity.Simulation.TM_Encoding` is a useful alias/unpacking layer.
- `Complexity.PpolyFormula_from_PpolyDAG_FixedSlice` is useful only for fixed-slice hardwiring audits/probes.

### Tests / audits worth knowing

- `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean` imports the fixed-slice bridge and appears designed to catch overstrong support-bound assumptions.
- `pnp3/Tests/WeakRouteSurfaceTests.lean` references partial-MCSP surfaces extensively.
- `pnp4/Pnp4/Tests/AxiomsAudit.lean` and pnp4 frontier modules audit the pnp4 search-MCSP mainline, but those were outside the A06 file scope.

### Avoid / do not touch without a dedicated task

- Do not edit `Complexity.Interfaces.lean`, `PsubsetPpolyInternal/**`, or `UnconditionalResearchGap.lean` from this audit.
- Do not treat `GapPartialMCSP_TMWitness` as already constructed.
- Do not treat `ppolyFormula_of_ppolyDAG_gapPartialMCSP_fixedSlice` as a generic simulation or lower-bound bridge.
- Do not rename `LegacyStraight*` without a broad import/API migration task; the names are misleading but active.
- Do not add a pnp3 search-MCSP wrapper claiming pnp4 mainline alignment unless it carries explicit `promise`, `relation`, `witnessBits`, and totality fields comparable to pnp4.

## 15. Gap map

### A. Engineering gaps

1. **pnp3 ↔ pnp4 MCSP adapter map is missing.**  There is no small markdown/Lean-free map explaining how pnp3 `PartialTruthTable`/`PartialMCSP_YES` relates to pnp4 `treeMCSPSearchProblem` and `SearchMCSPCompressionProblem`.
2. **Circuit model naming is ambiguous.**  `Circuit`, `DagCircuit`, `FormulaCircuit`, `LegacyStraightLineCircuit`, and `StraightLineCircuit` coexist with no compact local guide.
3. **External usage map is not centralized.**  Many modules import `Model_PartialMCSP`; a future engineering task could add documentation/tests showing which importers rely on which declarations.
4. **Asymptotic language uses `Classical.choose` on valid length.**  This is harmless, but a lemma exposing independence from the chosen witness would improve API confidence if future work relies on it.

### B. Formalization gaps

1. **Concrete NP membership for partial-MCSP is staged, not proved.**  `GapPartialMCSP_TMWitness` and `GapPartialMCSP_Asymptotic_TMWitness` expose the obligations, but no actual TM/verifier construction is provided in A06 files.
2. **Search-MCSP relation is missing in pnp3.**  There is no `witnessBits`, `relation`, or `totalOnPromise` analogue for partial/tree MCSP in the audited pnp3 files.
3. **Circuit-model adapters are incomplete.**  There is no audited adapter showing equivalence or one-way simulation between `Pnp3.Models.Circuit` and canonical `FormulaCircuit`/`DagCircuit` for the exact predicates used by partial MCSP.
4. **Exact/gap total MCSP surfaces are only partially represented through embeddings into partial tables.**  Total MCSP is not first-class in this scope.

### C. Mathematical gaps

1. **No lower bound against `PpolyDAG`.**  Nothing in A06 constructs or reduces `VerifiedNPDAGLowerBoundSource` or `NP_not_subset_PpolyDAG`.
2. **No MCSP magnification theorem.**  The audited files do not prove that a weak search/compression lower bound magnifies to a verified DAG lower-bound source.
3. **No search-to-decision lower-bound bridge.**  Decision/promise partial MCSP and pnp4 search-MCSP remain distinct.
4. **No barrier bypass.**  The fixed-slice theorem demonstrates hardwiring risk rather than bypassing a barrier.

### D. Governance gaps

1. **`LegacyStraight*` naming is misleading.**  The module doc says it is active/canonical, but names still look legacy.
2. **Fixed-slice bridge requires prominent quarantine.**  It is correctly named and documented, but future tasks should keep it in audit/probe contexts.
3. **No central “do not overclaim MCSP model” document.**  A small documentation task could prevent engineers from treating partial-MCSP decision definitions as pnp4 search-MCSP mainline progress.

## 16. Recommended Phase 1+ tasks

### Task 1 — Markdown MCSP model crosswalk

- **Title:** Document pnp3 partial-MCSP versus pnp4 search-MCSP surfaces.
- **Exact files to touch:** New markdown file only, e.g. `seed_packs/phase1_20engineer_parallel_dispatch/audit_followups/A06_mcsp_crosswalk.md` or operator-chosen docs path.
- **Allowed scope:** Describe declarations and differences; no Lean code.
- **Forbidden scope:** No new definitions, no theorem statements, no source/trust-root edits, no mainline-progress claims.
- **Expected output:** Table mapping `PartialTruthTable`, `PartialMCSP_YES/NO`, `gapPartialMCSP_Language`, `SearchMCSPCompressionProblem`, and `treeMCSPSearchProblem`.
- **Estimated time:** 0.5–1 day.
- **Dependency on other audits:** Cross-check with pnp4 frontier audit if available.
- **Risk level:** Low.
- **Type:** Markdown-only / operator decision.

### Task 2 — Lean API audit test for circuit model separation

- **Title:** Add surface tests documenting that pnp3 partial-MCSP `Circuit` is distinct from canonical `DagCircuit`/`FormulaCircuit`.
- **Exact files to touch:** Operator-selected test file, likely under `pnp3/Tests/` only.
- **Allowed scope:** `#check`/small wrapper definitions for existing declarations; no new theorem payload.
- **Forbidden scope:** No adapters, no trust-root edits, no lower-bound claims.
- **Expected output:** Compilation-only tests that expose the three circuit APIs and prevent accidental import/name drift.
- **Estimated time:** 0.5 day.
- **Dependency on other audits:** None.
- **Risk level:** Low.
- **Type:** Lean infrastructure.

### Task 3 — Formalize pnp3 partial-MCSP search-problem interface only if operator wants pnp3/pnp4 adapter work

- **Title:** Stage a pnp3 search-MCSP interface compatible in shape with pnp4 `SearchMCSPCompressionProblem`.
- **Exact files to touch:** New pnp3 interface file only, e.g. operator-selected `pnp3/Models/PartialMCSPSearch.lean`, plus lake/test registrations if allowed.
- **Allowed scope:** Define an honest structure with `instanceBits`, `witnessBits`, `promise`, `relation`, `totalOnPromise` for existing pnp3 partial-MCSP data.
- **Forbidden scope:** No lower-bound theorem, no magnification contract, no `VerifiedNPDAGLowerBoundSource`, no `ResearchGapWitness`, no pretending totality is proved unless it is a field or proven from existing witnesses.
- **Expected output:** Typed interface or structure only, clearly marked as infrastructure.
- **Estimated time:** 1–2 days.
- **Dependency on other audits:** Should wait for pnp4 search-MCSP/frontier audit to avoid duplicating canonical pnp4 surfaces.
- **Risk level:** Medium because wrapper risk is high if wording is careless.
- **Type:** Lean infrastructure / operator decision.

### Task 4 — Asymptotic-language shape-choice lemma

- **Title:** Add helper lemmas around `gapPartialMCSP_AsymptoticLanguage` valid-length selection.
- **Exact files to touch:** `pnp3/Models/Model_PartialMCSP.lean` and corresponding tests only, if approved.
- **Allowed scope:** Prove API lemmas using `partialInputLen_injective` so users can rewrite the asymptotic language at valid lengths without reasoning about `Classical.choose`.
- **Forbidden scope:** No NP membership, no lower-bound/magnification statements, no source/trust-root edits.
- **Expected output:** Rewriting lemmas for valid and invalid input lengths.
- **Estimated time:** 1 day.
- **Dependency on other audits:** None.
- **Risk level:** Low-to-medium due to dependent casts.
- **Type:** Lean formalization/API hygiene.

## 17. Stop / hold recommendations

- **Hold any task that claims pnp3 partial-MCSP already aligns with pnp4 `SearchMCSPCompressionProblem`.**  The audited pnp3 files do not have a search relation or witness-bit interface.
- **Downgrade any task treating `GapPartialMCSP_TMWitness` fields as already constructed.**  They are obligations, not evidence.
- **Cancel or rename any task that treats `ppolyFormula_of_ppolyDAG_gapPartialMCSP_fixedSlice` as generic `PpolyDAG ⊆ PpolyFormula`.**  It is fixed-slice hardwiring only.
- **Hold renaming of `LegacyStraight*` unless it is a dedicated compatibility migration.**  The names are misleading but active and externally imported.
- **No Phase 2/3/4/5 task should be dispatched from A06 alone.**  A06 found infrastructure gaps, not a missing mainline proof step.

## 18. What depends on `ResearchGapWitness` or `NP_not_subset_PpolyDAG`?

Within the audited file scope: **nothing found**.

The required search for `ResearchGapWitness|NP_not_subset_PpolyDAG|VerifiedNPDAGLowerBoundSource|SearchMCSPMagnificationContract|SourceTheorem|gap_from` over the audited scope returned no matches.  The audited area is therefore not directly constructing the frozen target, not reducing to `VerifiedNPDAGLowerBoundSource`, and not using `ResearchGapWitness` as a wrapper.

## 19. What is safe to reuse?

Safe to reuse:

- Partial truth-table finite infrastructure and encoding/decoding lemmas.
- Promise problem interface.
- Fixed-parameter partial-MCSP predicates and language equivalence lemmas.
- Straight-line-to-DAG adapter for upper-bound/inclusion work.
- `proved_P_subset_PpolyDAG_internal` as the upper-bound theorem that every `P` language has polynomial DAG circuits.

Safe only with warning labels:

- `GapPartialMCSP_TMWitness` and asymptotic witness structures, if clearly described as obligations.
- `ppolyFormula_of_ppolyDAG_gapPartialMCSP_fixedSlice`, if explicitly described as fixed-slice hardwiring and not lower-bound progress.

Should not be touched from ordinary Phase 1 tasks:

- Trust-root `Interfaces.lean`, `PsubsetPpolyInternal/**`, and `UnconditionalResearchGap.lean`.
- Compiler-route internals unless the task is specifically compiler-route API hygiene.
- pnp4 frontier mainline structures unless coordinating with a pnp4 audit/follow-up.

## 20. Commands run

Discovery and audit commands:

```bash
find pnp3/Models pnp3/Complexity -name "*.lean" | grep -v PsubsetPpolyInternal | grep -v "^pnp3/Complexity/Interfaces.lean" | sort
```

Result: 9 audited Lean files discovered.

```bash
rg -n "ResearchGapWitness|NP_not_subset_PpolyDAG|VerifiedNPDAGLowerBoundSource|SearchMCSPMagnificationContract|SourceTheorem|gap_from" <audit-scope>
```

Result: no matches in audited scope.

```bash
rg -n "RefutedRoute|Vacuous|supportBounds|MagnificationAssumptions|FinalPayloadProvider|via_ex_falso|weakRoute|Legacy|_Partial|TODO|placeholder" <audit-scope>
```

Result: matches for `LegacyStraight*`, import/file-name occurrences involving `Model_PartialMCSP`; no `RefutedRoute`, `Vacuous`, `supportBounds`, `FinalPayloadProvider`, `via_ex_falso`, `weakRoute`, `TODO`, or `placeholder` matches.

```bash
rg -n "\bclass\b|\binstance\b|default_instance|attribute \[instance\]|\bFact\b|\bopaque\b|Classical\.choose|noncomputable def" <audit-scope>
```

Result: harmless finite instances/noncomputable enumerations in `PartialTruthTable.lean`, fixed-slice `DagCircuit.toFormula`, `Classical.choose` in `gapPartialMCSP_AsymptoticLanguage`, and classical `gapPartialMCSP_Language`; no `opaque`, `default_instance`, `attribute [instance]`, or suspicious provider/default payload definitions.

```bash
rg -n "import (Models\.(Model_PartialMCSP|PartialTruthTable)|Complexity\.(Promise|PpolyDAG_StraightLineCore|PpolyDAG_from_StraightLine|PpolyFormula_from_PpolyDAG_FixedSlice|PsubsetPpolyDAG_Internal|Simulation\.(Circuit_Compiler|TM_Encoding)))" . -g'*.lean'
```

Result: many imports of `Model_PartialMCSP`, `Promise`, fixed-slice bridge, and compiler route in lower-bound, magnification, tests, and pnp4 bridge files; summarized in section 10.

```bash
./scripts/check.sh
```

Result: passed.  The command completed all 17 steps and ended with `All checks passed.`

## 21. Honest caveats

- I did not reconstruct every proof body in `PartialTruthTable.lean`; I audited all top-level declarations and representative proof purposes.
- I did not reconstruct every arithmetic proof in `Simulation/Circuit_Compiler.lean`; I focused on public contracts, internal endpoints, and hard-payload searches.
- I did not audit archived files beyond import references.
- I did not inspect every pnp3 lower-bound or magnification module importing `Model_PartialMCSP`; those are outside A06 scope and should be covered by other audits.
- I used pnp4 `SearchMCSPMagnification.lean` and `SearchMCSPConcreteTargets.lean` only for cross-reference; this report is not a pnp4 frontier audit.
- I verified signatures and route shape, not mathematical adequacy of the underlying MCSP thresholds.
- This audit should be cross-checked with any NoGoLog/refuted-route audit for historical route failures involving partial MCSP or fixed-slice formula hardwiring.
