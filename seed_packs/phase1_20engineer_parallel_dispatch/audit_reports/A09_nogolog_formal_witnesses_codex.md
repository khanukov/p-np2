# A09 audit: `outputs/nogolog.jsonl` formal witness fields

Task ID: A09  
Engineer handle: codex  
Branch: `khanukov/phase1-A09-codex`  
Audit report path: `seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A09_nogolog_formal_witnesses_codex.md`

## 1. Executive verdict

**Verdict: PARTIAL_BUT_USEFUL**

The NoGoLog currently has 9 JSONL entries, and 8 have non-null `formal_witness` fields. Every non-null `formal_witness` points to an existing Lean file, and every referenced Lean module builds under both `lake build PnP3 Pnp4` and `./scripts/check.sh`. However, the audit is not `COMPLETE_FOR_ITS_SCOPE` because three formal-witness line numbers are stale or imprecise: NOGO-000002 points inside a doc-comment near the theorem, while NOGO-000004 and NOGO-000005 point to line 208 of the scope-comment rather than the actual theorem at line 226. Also, NOGO-000003 has `status: needs_review` and no `formal_witness`, contradicting the task prompt's older statement that each NoGo has `status: formalized`; the JSONL itself is internally clear that NOGO-000003 is not formalized and is later scope-corrected / superseded.

## 2. Executive summary

Not all `formal_witness` fields are exact by file-line semantics, but all non-null formal witnesses are semantically backed by kernel-checked Lean declarations in the referenced files.

- **Valid exact file + exact theorem line:** NOGO-000001, NOGO-000006, NOGO-000007, NOGO-000008, NOGO-000009.
- **Valid file + nearby matching theorem, but stale/non-theorem line:** NOGO-000002, NOGO-000004, NOGO-000005.
- **No formal witness by design/current state:** NOGO-000003 (`status: needs_review`, `formal_witness: null`).
- **Build status:** all referenced formal-witness and regression-test modules are included in successful builds.
- **Overstatement risk:** NOGO-000004 and NOGO-000005 are honest about the prefix-AND-only scope. NOGO-000006 supplies the later arbitrary all-essential payload upgrade. NOGO-000007 states it generalizes NOGO-000006 without superseding it; the JSONL `supersedes` field being unset is consistent with its own notes, but inconsistent with the task prompt's wording that “NOGO-000007 generalizes 000006; verify the chain” if that wording is read as requiring `supersedes = NOGO-000006`.

## 3. Files audited

| Path | Approximate role | Read mode | Reason if not fully read |
|---|---|---:|---|
| `RESEARCH_CONSTITUTION.md` | Governance trust-root and NoGo rules | Skimmed structurally | Required reading; only governance-relevant rules were needed. |
| `seed_packs/phase1_20engineer_parallel_dispatch/README.md` | Dispatch wave instructions | Skimmed structurally | Required reading; older E-number naming overridden by user prompt. |
| `seed_packs/phase1_20engineer_parallel_dispatch/COMMON_WORKER_INSTRUCTIONS.md` | Common worker rules | Skimmed structurally | Required reading; stricter markdown-only/no-source-edits rule applied. |
| `seed_packs/phase1_20engineer_parallel_dispatch/tasks/A09_audit_nogolog_formal_witnesses.md` | Exact A09 task | Read fully | Defines report sections and acceptance criteria. |
| `outputs/nogolog.jsonl` | NoGoLog entries to audit | Read fully | 9 lines parsed as JSON; all entries included below. |
| `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean` | NOGO-000001/000002 witness file; FP-3 candidate Prop and no-go wrapper | Skimmed structurally, witness regions read | Large audit module; read declarations and surrounding comments relevant to line 155 and line 257. |
| `pnp3/Magnification/AuditRoutes/LogWidthAdversary/Composition.lean` | NOGO-000004/000005 witness file | Skimmed structurally, witness region read | Focused on theorem and scope comment around lines 200-226. |
| `pnp3/Magnification/AuditRoutes/ArbitraryLogWidthTT/Composition.lean` | NOGO-000006 witness file | Skimmed structurally, witness region read | Focused on theorem around line 101. |
| `pnp3/Magnification/AuditRoutes/SupportCardinalityBarrier/InSupportFunctionalDiversityApplication.lean` | NOGO-000007 witness file | Read fully; small file | 105-line file, fully inspected. |
| `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/AdversarialRobustness/RewriteAttack.lean` | NOGO-000008 witness/regression file | Skimmed structurally, witness region read | Focused on theorem around line 207 and supporting filter-admission theorem. |
| `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_NormaliseMetaBarrier/Barrier.lean` | NOGO-000009 witness/regression file | Skimmed structurally, witness region read | Focused on structural normaliser definitions and theorem around line 268. |
| `pnp3/Tests/FixedParams_Probe_NoGo.lean` | Regression test for NOGO-000001/000002/000003 | Read first 120 lines and relevant structure | Enough to verify imports and regression theorems for audited entries. |
| `pnp3/Tests/AuditRoutes_LogWidthAdversary_Smoke.lean` | Regression test for NOGO-000004/000005 | Read fully; small file | Contains `#check` surface for headline theorem. |
| `pnp3/Tests/AuditRoutes_ArbitraryLogWidthTT_Smoke.lean` | Regression test for NOGO-000006 | Read fully; small file | Contains `#check` surface for headline theorem. |
| `pnp3/Tests/AuditRoutes_SupportCardinalityBarrier_Smoke.lean` | Regression test for NOGO-000007 | Read fully; small file | Contains `#check` surface for T6 theorem. |

## 4. Per-NoGo verification table

| NoGo ID | status | formal_witness path | File exists? | Theorem at line? | Signature matches `structural_pattern`? | Kernel-checked? |
|---|---|---|---:|---:|---:|---:|
| NOGO-000001 | `formalized` | `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean:155` | Yes | Yes: `NoGo_FixedParamsRoute_with_OverbroadUniformProvenance` | Yes. It proves `False` from `FixedParamsRoute ac0 sb` plus `OverbroadUniformProvenance ac0`, matching the refuted composition claim. | Yes |
| NOGO-000002 | `formalized` | `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean:257` | Yes | **No exact theorem at line 257.** The matching theorem is nearby at line 265: `FP3Attempt.InSupportFunctionalDiversity_excludes_uniformPolyBound`. | Partially. The theorem only excludes uniformly bounded `polyBound` witnesses; the current JSONL structural pattern still says “alternating-slice / multi-slice hardwiring”, which the source comment says was corrected to log-width TT as the real residual concern. | Yes, nearby theorem builds |
| NOGO-000003 | `needs_review` | `null` | N/A | N/A | N/A. It is explicitly not formalized; later entries narrow and supersede/correct it. | N/A |
| NOGO-000004 | `formalized` | `pnp3/Magnification/AuditRoutes/LogWidthAdversary/Composition.lean:208` | Yes | **No exact theorem at line 208.** The matching theorem is nearby at line 226: `logWidthAdversary_satisfies_diversity`. | Yes for prefix-AND specialization. The file explicitly says it does not formalize arbitrary all-essential payloads. | Yes |
| NOGO-000005 | `formalized` | `pnp3/Magnification/AuditRoutes/LogWidthAdversary/Composition.lean:208` | Yes | **No exact theorem at line 208.** Same matching theorem as NOGO-000004 at line 226. | Yes. This entry is a scope-correction stating exactly that the theorem is prefix-AND-only. | Yes |
| NOGO-000006 | `formalized` | `pnp3/Magnification/AuditRoutes/ArbitraryLogWidthTT/Composition.lean:101` | Yes | Yes: `arbitraryLogWidthTT_satisfies_diversity` | Yes. It quantifies over every `PayloadFamily F` with `AllEssentialPayload F` and proves the constructed witness satisfies `FP3Attempt.InSupportFunctionalDiversity`. | Yes |
| NOGO-000007 | `formalized` | `pnp3/Magnification/AuditRoutes/SupportCardinalityBarrier/InSupportFunctionalDiversityApplication.lean:89` | Yes | Yes: `any_honest_sublinear_support_witness_has_hardwiring_twin` | Yes. It proves that any accepted honest sublinear-support witness has a canonical hardwiring twin also accepted by the same support-cardinality-only filter. | Yes |
| NOGO-000008 | `formalized` | `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/AdversarialRobustness/RewriteAttack.lean:207` | Yes | Yes: `v2A_rewrite_attack_prefixAnd` | Yes, with one caveat: the theorem proves existence of a rewritten witness for the same adversary language admitted by the V2-A filter; the “semantically identical” detail is backed by supporting theorem `rewritePrefixAndFamily_eval_eq`, not in the headline theorem statement. | Yes |
| NOGO-000009 | `formalized` | `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_NormaliseMetaBarrier/Barrier.lean:268` | Yes | Yes: `v2_a_structural_normalisation_meta_barrier` | Yes. It proves any structural normaliser satisfying seed-elimination and `AND true` reduction rejects the normalised seeded-prefix witness under V2-A's mixed-gate clause. | Yes |

## 5. Top-level theorem / structure inventory

| Declaration | File | Type/signature summary | Classification | Hard-payload dependency |
|---|---|---|---|---|
| `HardwiringObstruction` | `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean` | Definitional access to an existing hardwiring obstruction/PpolyFormula witness. | audit-only | No `ResearchGapWitness`; audit wrapper. |
| `HardwiringGuard` | `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean` | Prop naming a hardwiring guard. | staged Prop / audit-only | No hard payload. |
| `hardwiring_guard_holds` | `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean` | Proves the audit guard. | audit-only | No hard payload. |
| `NoGo_FixedParamsRoute_with_OverbroadUniformProvenance` | `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean` | `(p) (ac0) (sb) -> OverbroadUniformProvenance ac0 -> FixedParamsRoute ac0 sb -> False`. | refuted route / audit-only | No `ResearchGapWitness`; it is an obstruction to a route. |
| `FP3Attempt.InSupportFunctionalDiversity` | `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean` | Prop on `InPpolyFormula L`: support cardinality unbounded and IO below `n`. | staged Prop / weak route | No hard payload, but potential wrapper risk if promoted as provenance. |
| `FP3Attempt.InSupportFunctionalDiversity_excludes_uniformPolyBound` | `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean` | Uniformly bounded `polyBound` implies not `InSupportFunctionalDiversity`. | audit-only / weak route | No hard payload. |
| `logWidthAdversary_satisfies_diversity` | `pnp3/Magnification/AuditRoutes/LogWidthAdversary/Composition.lean` | Prefix-AND Nat.log2 adversary witness satisfies `InSupportFunctionalDiversity`. | refuted/weak route witness | No hard payload; explicitly no `gap_from_*`. |
| `arbitraryLogWidthTT_satisfies_diversity` | `pnp3/Magnification/AuditRoutes/ArbitraryLogWidthTT/Composition.lean` | Arbitrary all-essential log-width payload witness satisfies `InSupportFunctionalDiversity`. | refuted/weak route witness | No `ResearchGapWitness`, no `SourceTheorem`, no final endpoint. |
| `inSupportFunctionalDiversity_is_support_cardinality_only` | `pnp3/Magnification/AuditRoutes/SupportCardinalityBarrier/InSupportFunctionalDiversityApplication.lean` | `IsSupportCardinalityOnly @FP3Attempt.InSupportFunctionalDiversity`. | audit-only barrier theorem | No hard payload. |
| `any_honest_sublinear_support_witness_has_hardwiring_twin` | `pnp3/Magnification/AuditRoutes/SupportCardinalityBarrier/InSupportFunctionalDiversityApplication.lean` | Transports acceptance from honest witness to canonical hardwiring twin with same support profile. | audit-only barrier theorem | No hard payload. |
| `v2A_rewrite_attack_prefixAnd` | `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/AdversarialRobustness/RewriteAttack.lean` | Exists language and rewritten witness accepted by V2-A filter, equal to adversary language. | refuted route / audit-only | No hard payload. |
| `LocalFormulaOps` | `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_NormaliseMetaBarrier/Barrier.lean` | Structure of bottom-up formula operations. | harmless interface | No hard payload. |
| `StructuralNormaliser` | `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_NormaliseMetaBarrier/Barrier.lean` | Structure with local ops, normalise, and fold equation. | typed interface / audit-only | No hard payload; class-like design is a Lean `structure`, not typeclass. |
| `normalisedWitness` | `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_NormaliseMetaBarrier/Barrier.lean` | Builds an `InPpolyFormula` by applying normaliser pointwise. | adapter definition / audit-only | No hard payload. |
| `v2_a_structural_normalisation_meta_barrier` | `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_NormaliseMetaBarrier/Barrier.lean` | Seed-eliminating structural normaliser makes the normalised seeded-prefix witness fail V2-A. | audit-only barrier theorem | No hard payload. |

None of the audited headline witnesses constructs or consumes `ResearchGapWitness`, `VerifiedNPDAGLowerBoundSource`, `SearchMCSPMagnificationContract`, or `NP_not_subset_PpolyDAG`. The only occurrences of those phrases in the audited scope are comments/JSONL notes warning that no final bridge is introduced.

## 6. Kernel-checked content

The following content is actually proven by Lean and checked in the successful build:

1. **NOGO-000001:** `NoGo_FixedParamsRoute_with_OverbroadUniformProvenance` proves `False` from `OverbroadUniformProvenance ac0` and `FixedParamsRoute ac0 sb`, re-exporting an existing falsifiability-probe theorem.
2. **NOGO-000002 nearby witness:** `FP3Attempt.InSupportFunctionalDiversity_excludes_uniformPolyBound` proves any `InPpolyFormula` record whose `polyBound` is uniformly bounded by a constant cannot satisfy the FP-3 support-diversity Prop. This is kernel-checked, but the JSONL line number and structural-pattern wording are stale relative to the corrected source comment.
3. **NOGO-000004/000005 nearby witness:** `logWidthAdversary_satisfies_diversity` proves the Nat.log2 prefix-AND witness satisfies `FP3Attempt.InSupportFunctionalDiversity`. It is not an arbitrary-payload theorem.
4. **NOGO-000006:** `arbitraryLogWidthTT_satisfies_diversity` proves arbitrary all-essential log-width truth-table payloads satisfy the same diversity filter.
5. **NOGO-000007:** `inSupportFunctionalDiversity_is_support_cardinality_only` and `any_honest_sublinear_support_witness_has_hardwiring_twin` prove the support-cardinality-only transport barrier for the FP-3 filter.
6. **NOGO-000008:** `v2A_rewrite_attack_prefixAnd` proves existence of a rewritten witness for the Nat.log2 adversary language accepted by `ProvenanceFilter_v2_V2_A_gpt55_Filter`; supporting theorems in the same file establish semantic equality and gate-count/depth admissibility.
7. **NOGO-000009:** `v2_a_structural_normalisation_meta_barrier` proves a structural normaliser with seed elimination and `AND true` reduction rejects the normalised seeded-prefix witness under V2-A.

## 7. Staged / placeholder / Prop-only content

| Item | Status | Assessment |
|---|---|---|
| `FP3Attempt.InSupportFunctionalDiversity` | Prop-only filter over `InPpolyFormula` support cardinalities. | Honest staging and audit-only. It is dangerous only if promoted as a provenance filter because NOGO-000006/000007 show support-cardinality-only filters admit hardwiring. |
| `HardwiringGuard` | Prop name used for audit guard. | Harmless audit interface. |
| NOGO-000003 JSONL entry | `status: needs_review`, `formal_witness: null`. | Honest unformalized/stale sketch, not a kernel-checked theorem. It should not be counted as formalized. |
| `StructuralNormaliser` | Structure packaging operations and a normalisation equation. | Harmless typed interface for a meta-barrier; not a hidden payload provider. |
| `normalisedWitness` | Adapter definition producing an `InPpolyFormula`. | Harmless interface/adaptor in audit route; it does not claim separation. |

## 8. Refuted / vacuous / legacy route check

Search terms included `RefutedRoute`, `Vacuous`, `supportBounds`, `MagnificationAssumptions`, `FinalPayloadProvider`, `via_ex_falso`, `weakRoute`, `Legacy`, `_Partial`, `TODO`, and `placeholder` over the audited scope.

Findings:

- 11 matches total in the audited scope.
- The matches are comments/docstrings in `FixedParamsProbe.lean`, `LogWidthAdversary/Composition.lean`, and `FixedParams_Probe_NoGo.lean` describing old placeholders, route caveats, or forbidden final-bridge language.
- No audited headline theorem uses `via_ex_falso`, `FinalPayloadProvider`, `MagnificationAssumptions`, or `supportBounds` as a payload channel.
- NOGO-000001 is explicitly a theorem to `False`, and its source comment says it is an obstruction, not a bridge.
- NOGO-000004/000005/000006/000007 are weak/audit route obstructions against support-cardinality-only provenance filters. They must stay in audit-route territory.
- NOGO-000008/000009 are audit-route obstructions against syntactic V2 filter designs. They do not close semantic-quotient successors.

## 9. Hidden payload / Rule 16 check

Search terms included `class`, `instance`, `default_instance`, `attribute [instance]`, `Fact`, `opaque`, `Classical.choose`, and `noncomputable def` over the audited scope.

Findings:

- 8 textual matches total.
- In `FixedParamsProbe.lean`, all matches are comments/docstrings warning against typeclass/opaque payloads or explaining why `Classical.choose` is not used to extract a witness family. Classification: **harmless infrastructure / warning comments**.
- In `FixedParams_Probe_NoGo.lean`, the `instance` match occurs in a comment saying the Probe-2 hardwired record is an instance of an abstract pattern. Classification: **harmless comment**.
- In `outputs/nogolog.jsonl`, NOGO-000009's note mentions “Class-parametric meta-barrier” in ordinary prose, not a Lean typeclass. Classification: **harmless JSONL prose**.
- No `class`, Lean `instance`, `default_instance`, `attribute [instance]`, `Fact`, `opaque`, `Classical.choose`, or `noncomputable def` declaration appears in the audited active Lean code regions as a payload provider.
- `StructuralNormaliser` is a Lean `structure`, not a typeclass; its fields are explicit arguments to the theorem. Classification: **harmless typed interface**, not Rule-16 hidden payload.

## 10. Barrier relevance

| Barrier / issue | Content in audited area | Form |
|---|---|---|
| Natural proofs | Mentioned around V2-A successor concerns in JSONL; not proven here. | Markdown/JSONL comment only in this audit scope. |
| Relativization | No relevant content found. | Nothing. |
| Algebrization | No relevant content found. | Nothing. |
| Locality | Method family `ac0_locality_support` appears in NoGoLog. | JSONL metadata, not theorem content here. |
| Hardwiring | Central to all NoGo entries. | Actual theorems for concrete/parametric hardwiring acceptance or route contradiction. |
| Support-cardinality-only | Central to NOGO-000004 through NOGO-000007. | Actual theorems plus typed interface (`IsSupportCardinalityOnly`). |
| Syntax-only filters | Central to NOGO-000008. | Actual theorem against V2-A syntactic filter. |
| Normalization filters | Central to NOGO-000009. | Actual theorem against structural normalisation patch. |
| Search-to-decision | Not present in audited witness files. | Nothing. |
| MCSP / magnification | Background route names and fixed-params audit context. | Audit-route theorem surfaces; no mainline MCSP magnification bridge. |

## 11. Reuse map

Safe to reuse:

- `NoGo_FixedParamsRoute_with_OverbroadUniformProvenance` as an audit obstruction only.
- `FP3Attempt.InSupportFunctionalDiversity` only as an already-refuted audit filter shape.
- `FP3Attempt.InSupportFunctionalDiversity_excludes_uniformPolyBound` as a limited theorem about uniformly bounded support/poly-bound witnesses.
- `logWidthAdversary_satisfies_diversity` for prefix-AND-only scope.
- `arbitraryLogWidthTT_satisfies_diversity` for arbitrary all-essential payload scope.
- `inSupportFunctionalDiversity_is_support_cardinality_only` and `any_honest_sublinear_support_witness_has_hardwiring_twin` as support-cardinality barrier tools.
- `v2A_rewrite_attack_prefixAnd` as a rewrite attack against the specific V2-A syntactic filter.
- `v2_a_structural_normalisation_meta_barrier` as a barrier against structural seed-eliminating normalisation patches.
- Regression test modules listed in the JSONL can be reused as name-surface smoke tests.

Avoid:

- Do not treat any NoGo theorem as `ResearchGapWitness`, `VerifiedNPDAGLowerBoundSource`, `NP_not_subset_PpolyDAG`, or P-vs-NP mainline progress.
- Do not reuse stale JSONL line numbers as exact theorem anchors for NOGO-000002, NOGO-000004, or NOGO-000005 without correcting them in a governance/ledger repair task.
- Do not treat NOGO-000003 as formalized.
- Do not promote support-cardinality-only filters to accepted provenance filters.
- Do not claim NOGO-000009 covers semantic quotient / truth-table-based V2-A.2 successors; the JSONL itself says those are outside `StructuralNormaliser`.

## 12. Gap map

### A. Engineering gap

- JSONL `formal_witness` line numbers are stale for NOGO-000002, NOGO-000004, and NOGO-000005.
- The task prompt says all NoGo entries have `status: formalized`, but the current JSONL has NOGO-000003 as `needs_review` with `formal_witness: null`; docs/tasks should not assume otherwise.
- Regression tests for NOGO-000008 and NOGO-000009 point to the theorem file itself rather than a dedicated `pnp3/Tests/...` smoke file. This compiles, but it is less uniform than NOGO-000001 through NOGO-000007.

### B. Formalization gap

- No formalization gap for the non-null witness claims after accounting for line-number staleness and scope corrections.
- NOGO-000003's original arbitrary log-width TT sketch is not formalized under NOGO-000003; that is intentionally superseded/corrected by NOGO-000004/000005 and then upgraded by NOGO-000006.

### C. Mathematical gap

- None of the audited entries supplies or reduces `ResearchGapWitness`, `NP_not_subset_PpolyDAG`, `VerifiedNPDAGLowerBoundSource`, or `SearchMCSPWeakLowerBound`.
- The audited results are negative/audit barriers for candidate provenance filters; they do not prove lower bounds.
- Semantic quotient successors to the V2 syntactic-filter family remain outside NOGO-000009's theorem statement.

### D. Governance gap

- Stale exact file-line pointers should be repaired or the schema should clarify that `formal_witness` is a file-near-line pointer rather than exact theorem line.
- NOGO-000007's JSONL says it generalizes but intentionally does not supersede NOGO-000006. That is internally coherent, but future task prompts should mirror this wording rather than saying “supersedes chain” if no `supersedes` field is intended.
- NOGO-000002's structural-pattern wording appears stale relative to source comments saying the “alternating-slice full-width TT” caveat was incorrect and the real residual concern is log-width TT.

## 13. Compilation check

`lake build PnP3 Pnp4` completed successfully. `./scripts/check.sh` also completed successfully. In the full build output, the referenced modules were built/replayed successfully, including:

- `Magnification.AuditRoutes.FixedParamsProbe`
- `Tests.FixedParams_Probe_NoGo`
- `Magnification.AuditRoutes.LogWidthAdversary.Composition`
- `Tests.AuditRoutes_LogWidthAdversary_Smoke`
- `Magnification.AuditRoutes.ArbitraryLogWidthTT.Composition`
- `Tests.AuditRoutes_ArbitraryLogWidthTT_Smoke`
- `Magnification.AuditRoutes.SupportCardinalityBarrier.InSupportFunctionalDiversityApplication`
- `Tests.AuditRoutes_SupportCardinalityBarrier_Smoke`
- `Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.AdversarialRobustness.RewriteAttack`
- `Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_NormaliseMetaBarrier.Barrier`

Per NoGo:

| NoGo ID | Formal-witness module compiles? | Regression-test module compiles? |
|---|---:|---:|
| NOGO-000001 | Yes | Yes |
| NOGO-000002 | Yes | Yes |
| NOGO-000003 | N/A: no formal witness | Yes |
| NOGO-000004 | Yes | Yes |
| NOGO-000005 | Yes | Yes |
| NOGO-000006 | Yes | Yes |
| NOGO-000007 | Yes | Yes |
| NOGO-000008 | Yes | Yes, same file |
| NOGO-000009 | Yes | Yes, same file |

## 14. `status` field consistency

- NOGO-000001, 000004, 000005, 000006, 000007, 000008, and 000009 are consistent with `status: formalized` after interpreting three stale line numbers as nearby-theorem pointers.
- NOGO-000002 is only partially consistent: the nearby theorem is formalized, but the structural-pattern text appears stale/overbroad relative to source comments.
- NOGO-000003 is consistent with its actual JSONL status (`needs_review`) and lack of formal witness. It is inconsistent only with the task prompt's outdated blanket statement that each NoGo has `status: formalized`.

## 15. `supersedes` chain

Observed JSONL chain:

- NOGO-000003 supersedes NOGO-000002, but remains `needs_review` and unformalized.
- NOGO-000004 supersedes NOGO-000003 with a formalized prefix-AND log-width adversary.
- NOGO-000005 supersedes NOGO-000004 as a scope correction: it keeps the same formal theorem but states the prefix-AND-only limitation.
- NOGO-000006 supersedes NOGO-000005 with the arbitrary all-essential log-width payload theorem.
- NOGO-000007 intentionally has no `supersedes` value. Its `why_generalizes` text says it generalizes NOGO-000006 without superseding it.
- NOGO-000008 and NOGO-000009 do not set `supersedes`; NOGO-000009's `why_generalizes` text says it closes a patch design space for NOGO-000008 but does not preempt semantic successors.

Assessment: the formal chain through NOGO-000006 is coherent. The NOGO-000007 generalization is also coherent, but the governance representation is prose-only rather than `supersedes`-field-based.

## 16. Regression test verification

Every NoGo entry has a `regression_test` field. Every referenced regression file exists and builds.

- `pnp3/Tests/FixedParams_Probe_NoGo.lean` exists and builds; it contains regression theorems for the FixedParams/FP-3 surface and imports `FixedParamsProbe`.
- `pnp3/Tests/AuditRoutes_LogWidthAdversary_Smoke.lean` exists and builds; it `#check`s `logWidthAdversary_satisfies_diversity`.
- `pnp3/Tests/AuditRoutes_ArbitraryLogWidthTT_Smoke.lean` exists and builds; it `#check`s `arbitraryLogWidthTT_satisfies_diversity`.
- `pnp3/Tests/AuditRoutes_SupportCardinalityBarrier_Smoke.lean` exists and builds; it `#check`s the support-cardinality barrier theorem.
- For NOGO-000008 and NOGO-000009, the `regression_test` is the formal-witness file itself. This is build-checked, though a dedicated smoke test would be more uniform.

## 17. Recommended Phase 1+ tasks

### Task 1: Repair stale NoGoLog formal-witness anchors

- **Exact files to touch:** `outputs/nogolog.jsonl` only.
- **Allowed scope:** Update `formal_witness` line numbers for NOGO-000002, NOGO-000004, and NOGO-000005 to the actual theorem lines, or update schema/documentation to explicitly allow nearby comment anchors.
- **Forbidden scope:** No Lean edits; no new NoGo entries; no status promotions; no theorem changes; no `ResearchGapWitness` or endpoint work.
- **Expected output:** JSONL-only governance repair PR with validation via `./scripts/check.sh`.
- **Estimated time:** 1 hour.
- **Dependency on other audits:** None, though useful to coordinate with any NoGoLog schema audit.
- **Risk level:** Low.
- **Type:** Markdown/JSONL governance repair, operator decision required because this audit was markdown-only and could not edit JSONL.

### Task 2: Clarify NOGO-000002 structural-pattern wording

- **Exact files to touch:** `outputs/nogolog.jsonl`; optionally a governance changelog if required by operator policy.
- **Allowed scope:** Align NOGO-000002 wording with the source comment: the old alternating-slice/full-width TT caveat was corrected; the actual remaining concern is log-width TT, later handled by NOGO-000004 through NOGO-000006.
- **Forbidden scope:** No Lean edits; no status promotion; no deletion of historical information unless moved into notes.
- **Expected output:** JSONL wording patch preserving historical audit trail while preventing overstatement.
- **Estimated time:** 1-2 hours.
- **Dependency on other audits:** Could benefit from A09 integrator review; no technical dependency.
- **Risk level:** Low to medium because ledger edits are governance-sensitive.
- **Type:** Operator decision / JSONL governance repair.

### Task 3: Decide whether NOGO-000008/000009 need dedicated smoke tests

- **Exact files to touch:** If approved later, add dedicated test files such as `pnp3/Tests/AuditRoutes_V2A_RewriteAttack_Smoke.lean` and `pnp3/Tests/AuditRoutes_V2A_NormaliseMetaBarrier_Smoke.lean`, plus `lakefile.lean` if test registration is manual.
- **Allowed scope:** Add `#check` smoke surfaces only, mirroring existing smoke tests.
- **Forbidden scope:** No theorem changes; no filter redesign; no candidate implementation; no endpoint work.
- **Expected output:** Uniform regression-test surface for NOGO-000008/000009.
- **Estimated time:** 2-3 hours.
- **Dependency on other audits:** Could wait for a broader V2 audit.
- **Risk level:** Medium because it touches Lean tests and possibly lakefile; not required for current correctness because the witness files already build.
- **Type:** Lean test-only, optional.

## 18. Stop / hold recommendations

- Hold any task that treats NOGO-000003 as formalized; it is explicitly `needs_review` and has no formal witness.
- Hold any task that treats NOGO-000004 or NOGO-000005 as arbitrary-payload formalization; that stronger scope is NOGO-000006.
- Hold any task that treats NOGO-000007 as a formal `supersedes` chain item unless the operator explicitly wants the JSONL field changed; current JSONL says “generalizes without superseding”.
- Downgrade/rename any Phase 1+ task that attempts to reuse `FP3Attempt.InSupportFunctionalDiversity` as a viable provenance filter; it is already an audit-only refuted support-cardinality filter.
- Cancel any implementation task that would turn these NoGo witnesses into `ResearchGapWitness`, `SourceTheorem`, `gap_from`, `VerifiedNPDAGLowerBoundSource`, `NP_not_subset_PpolyDAG`, or P-vs-NP endpoint work.

## 19. Honest caveats

- I did not reconstruct full dependency closures with `#print axioms` for each individual NoGo theorem; I relied on `lake build PnP3 Pnp4`, `./scripts/check.sh`, the repository AxiomsAudit outputs, and source inspection.
- I did not fully read every proof body in the larger V2 files; I inspected the theorem statements, surrounding supporting declarations, and build status.
- I did not inspect every imported file behind the witness modules, only the files directly referenced by `formal_witness` and `regression_test` plus required instructions.
- I verified signature/claim matching at audit granularity, not mathematical adequacy beyond the stated theorem hypotheses.
- This audit should be cross-checked with any broader NoGoLog schema/version audit if one exists.

## 20. Commands run

- `git branch -a && git checkout -B khanukov/phase1-A09-codex`
- `python3 - <<'PY' ... outputs/nogolog.jsonl ... PY` to parse all 9 JSONL entries and inspect fields.
- `nl -ba <file> | sed -n '<range>p'` for witness and regression files.
- `rg -n "ResearchGapWitness|NP_not_subset_PpolyDAG|VerifiedNPDAGLowerBoundSource|SearchMCSPMagnificationContract|SourceTheorem|gap_from" <audit-scope>`: 17 textual matches, all comments/JSONL notes in audited scope; no hard-payload construction in headline witnesses.
- `rg -n "RefutedRoute|Vacuous|supportBounds|MagnificationAssumptions|FinalPayloadProvider|via_ex_falso|weakRoute|Legacy|_Partial|TODO|placeholder" <audit-scope>`: 11 textual matches, all comments/docstrings in audited scope.
- `rg -n "\bclass\b|\binstance\b|default_instance|attribute \[instance\]|\bFact\b|\bopaque\b|Classical\.choose|noncomputable def" <audit-scope>`: 8 textual matches, all comments/JSONL prose; no hidden payload declaration in audited code.
- `./scripts/check.sh`: passed.
- `lake build PnP3 Pnp4`: passed with pre-existing warnings.

## 21. Scope violations

None. I created exactly one markdown audit report and did not edit Lean source, JSONL, lakefile, specs, outputs/attempts, trust-root files, or NoGoLog entries.
