# A11 Phase 0 synthesis and dispatch decision

Task: A11  
Engineer handle: gpt55  
Branch: work  
Commit before: fe03a5751cf3282c15fc2e45645a5fb66386551a  
Commit after: TBD

Files added/modified:
  - `seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A11_phase0_synthesis_gpt55.md`

Outcome:
  SYNTHESIS_LANDED

## 1. Executive verdict

**PHASE0_REVEALS_MAJOR_GOVERNANCE_REPAIR_NEEDED**

All A01-A10 reports are present, and their shared technical conclusion is coherent: the repository has substantial kernel-checked infrastructure, but the load-bearing P-vs-NP source obligations remain unproved or explicitly wrapped as staged fields. The most important audit outcome is therefore not "open every planned implementation task". It is a governance correction: the seed pack still says all non-audit tasks are dispatchable now, while the audits show that several tasks would merely add theorem-as-field packages, `True` placeholders, or manual decision-support wrappers unless rescoped.

Immediate limited Phase 1+ work is useful only as infrastructure/cleanup. No immediate task should claim source-theorem progress, produce `ResearchGapWitness`, produce `VerifiedNPDAGLowerBoundSource`, or bridge restricted AC0/formula/local-PRG facts into `P_ne_NP` without a new mathematical theorem.

## 2. Audit coverage table

| Audit | Present? | Executive verdict | Main area | Confidence | Main caveat |
| --- | --- | --- | --- | --- | --- |
| A01 | yes | PARTIAL_BUT_USEFUL | `pnp3/Magnification/*_Partial.lean` partial-MCSP formula/locality pipeline | Medium-high | Strong adapters exist, but locality/provider and formula lower-bound payloads remain staged; no DAG/source bridge. |
| A02 | yes | PARTIAL_BUT_USEFUL | `pnp3/Magnification/FinalResult*.lean` final-result pipeline | High | Conditional wiring from `NP_not_subset_PpolyDAG`/`ResearchGapWitness` to `P_ne_NP` is checked; vacuous/provider final endpoints are quarantined and must not be reused. |
| A03 | yes | PARTIAL_BUT_USEFUL | pnp3 AC0 bridges and asymptotic collapse files | Medium-high | AC0-to-DAG is not complete; strongest DAG endpoint needs already-supplied asymptotic DAG collapse plus NP-strict source. |
| A04 | yes | PARTIAL_BUT_USEFUL | `pnp3/Barrier/` minimal barrier files | Medium | Interfaces are tiny and mostly Prop-level; useful as labels, not operational barrier formalizations. |
| A05 | yes | PARTIAL_BUT_USEFUL | `pnp3/LowerBounds/` | Medium-high | Real partial-MCSP/anti-checker/lower-bound infrastructure exists, but key theorem endpoints are conditional or side-track formula/locality artifacts. |
| A06 | yes | PARTIAL_BUT_USEFUL | `pnp3/Models/` and non-trust-root `pnp3/Complexity/` | Medium-high | Encoding/compiler/upper-bound facts are checked; `P ⊆ PpolyDAG` is an upper-bound inclusion, not a lower bound. |
| A07 | yes | PARTIAL_BUT_USEFUL | `pnp4/Pnp4/AlgorithmsToLowerBounds/` | High | Finite MCSP, coin, AC0[p], local-PRG, and bridge surfaces are useful, but published lower bounds/reductions are contracts and the DAG source is not constructed. |
| A08 | yes | PARTIAL_BUT_USEFUL | `pnp4/Pnp4/Frontier/` and ContractExpansion | High | Correct mainline API shape exists; weak search lower bound, NP membership/runtime, parser serialization, and magnification-to-DAG remain staged. |
| A09 | yes | PARTIAL_BUT_USEFUL | `outputs/nogolog.jsonl` formal witness validation | Medium | Several NoGo witnesses are kernel-checked nearby, but NOGO-000003 is not formalized and some JSONL line/scope claims are stale. |
| A10 | yes | PARTIAL_BUT_USEFUL | cross-cutting `_Partial`/legacy/TODO/placeholder search | Medium | Repository-wide markers are mapped, but large files were partly structurally searched; main risks are refuted support-bounds/provider routes and placeholder invariants. |

Audits present:
  A01: yes
  A02: yes
  A03: yes
  A04: yes
  A05: yes
  A06: yes
  A07: yes
  A08: yes
  A09: yes
  A10: yes

## 3. Repo state summary

### pnp3 Magnification partials

The partial-MCSP magnification layer contains real Lean infrastructure: partial Step-C statements, locality-lift facades, formula-to-general-solver adapters, locality/provider interfaces, and conditional bridges to `NP_not_subset_PpolyFormula` and `NP_not_subset_PpolyReal`. It is not a DAG lower-bound route. The hard work is still the structured locality provider, strict NP witness for the partial-MCSP language, and non-refuted formula/locality payload.

### pnp3 FinalResult pipeline

The honest mainline final bridge is already present and kernel-checked in conditional form: a supplied `NP_not_subset_PpolyDAG` or `ResearchGapWitness` yields `P_ne_NP`. That is valuable boundary wiring. The zero-argument/provider-style endpoints in the audited final-result area are audit-only, vacuous, or refuted-route compatibility surfaces and should remain quarantined.

### AC0 / asymptotic / bridge files

The pnp3 AC0 bridge files contain conditional semantic switching, atlas/scenario-budget, small-mismatch, approximate-family, and asymptotic-collapse adapters. The only DAG-shaped conclusion depends on an already supplied asymptotic `PpolyDAG` collapse plus an `NP_strict` hypothesis. The pnp4 AC0[p] files correctly stop at restricted `¬ InAC0p`/finite-slice conclusions unless an explicit verified DAG bridge is supplied.

### Barrier files

The current pnp3 barrier files are minimal labels/interfaces. They are not operational Razborov-Rudich, BGS, or Aaronson-Wigderson formalizations. They can guide classification, but packaging a barrier statement as a record field would not produce new mathematical content.

### LowerBounds

`pnp3/LowerBounds/` contains meaningful partial-MCSP semantics, anti-checker, singleton/provenance, fixed-slice, and asymptotic lower-bound infrastructure. The useful pieces are conditional theorem surfaces and finite combinatorics. Support-cardinality/provenance endpoints are dangerous when generalized; several are audit/no-go artifacts rather than viable routes.

### Models / Complexity

The model and non-trust-root complexity files provide concrete finite encodings, partial truth-table combinatorics, standard verifier completeness fragments, straight-line-to-DAG adapters, and a checked `P_subset_PpolyDAG` upper-bound inclusion. These are canonical infrastructure, not source lower bounds.

### pnp4 AlgorithmsToLowerBounds

This directory is a strong infrastructure layer for finite MCSP slices, coin-problem algebra, masking/averaging translations, local-PRG transfer, AC0[p] contracts, formula target models, and the minimal bridge from a supplied `VerifiedNPDAGLowerBoundSource` to pnp3 final targets. The missing arrow is construction of `VerifiedNPDAGLowerBoundSource` from those restricted routes.

### pnp4 Frontier / ContractExpansion

The Frontier directory cleanly expresses the intended mainline frontier: `SearchMCSPWeakLowerBound` plus a magnification contract can produce `VerifiedNPDAGLowerBoundSource`; `PvsNPBridgeRequirements` separates restricted AC0[p] milestones from verified DAG sources; ContractExpansion supplies tree-MCSP/prefix-language APIs and adapter proofs. The implementation remains staged at parser serialization, NP/runtime budget, weak lower bound, and magnification fields.

### NoGoLog

The NoGoLog has useful formal-witness coverage for several hardwiring/support-cardinality/syntax-only failures, but it is not a fully automatic route-killer. NOGO-000003 is explicitly not formalized; some line numbers and relationship claims need stale-metadata repair. No task should pretend manual NoGo applicability is automatic detection.

### Legacy / partial markers

`_Partial` is not automatically bad: much of it is live infrastructure. The serious legacy risks are refuted support-bound routes, `VacuousFinalPayloadProvider`, `MagnificationAssumptions`, provider/default channels, and placeholder invariants such as `PDT.WellFormed := True`.

## 4. What is actually kernel-checked?

### A. Canonical useful artifacts

- Conditional final bridge from an explicit DAG lower bound / research-gap witness to `P_ne_NP`.
- Partial-MCSP finite semantics, promise/language facts, YES/NO separation under stated gaps, and standard-verifier completeness fragments.
- Formula/locality adapters that turn explicit provider/lower-bound packages into formula/real noncontainment conclusions.
- Straight-line-to-DAG and compiled-runtime upper-bound infrastructure, including `P_subset_PpolyDAG`.
- pnp4 finite MCSP truth-table, coin-problem, masking/averaging, local-PRG transfer, and finite lower-bound adapter lemmas.
- pnp4 `BridgeToPpolyDAG` consequences from a supplied `VerifiedNPDAGLowerBoundSource`.
- Frontier adapter facts for C-DAG/PpolyDAG conversion, tree-MCSP witness codec soundness/completeness, prefix-extension language semantics, parser-failure rejection, relation decidability, and ambient-length arithmetic.
- Several NoGo audit witnesses showing concrete or parametric failure modes for support-cardinality and syntactic/normalization filters.

### B. Conditional wrappers

- `ResearchGapWitness → P_ne_NP` and `NP_not_subset_PpolyDAG → P_ne_NP`.
- `VerifiedNPDAGLowerBoundSource → NP_not_subset_PpolyDAG → P_ne_NP`.
- `SearchMCSPWeakLowerBound` / `SearchMCSPMagnificationContract` wrappers that yield verified DAG source only after the hard field is supplied.
- `RestrictedToVerifiedDAGBridge` and `PvsNPBridgeRequirement` wrappers from restricted lower-bound evidence to a verified DAG source.
- Structured locality, shrinkage, certificate, parser/runtime, and budget wrappers.

### C. Audit-only theorems

- Theorems proving refuted route conditions imply contradiction or exposing overbroad provenance filters.
- NoGo witnesses for support-cardinality-only, arbitrary log-width truth-table, prefix/hardwiring, V2-A syntactic, and structural normalization failures.
- Route-surface and axiom-audit wrappers whose purpose is visibility, not progress.

### D. Refuted/vacuous route witnesses

- `RefutedRoute_*` surfaces and support-bound conclusions depending on known inconsistent support predicates.
- `VacuousFinalPayloadProvider` and related final-payload-provider endpoints.
- Compatibility surfaces around `MagnificationAssumptions` and old universal support-bound routes.
- Any endpoint whose contradiction is obtained through a refuted support-bound predicate rather than a genuine lower-bound proof.

### E. Adapter/infrastructure theorems

- `PpolyDAG`/`C_DAG` family adapters and exponent extraction from an existing `PpolyDAG` witness.
- Tree-circuit codec encode/decode/verification adapters.
- Prefix parser semantic adapters and malformed-input rejection.
- Polynomial/ambient-length arithmetic for table lengths and runtime budgets.
- Surface-test wrappers and `#print axioms` audit hooks.

## 5. What is staged / placeholder / wrapper?

Major staged patterns discovered across A01-A10:

- `ResearchGapWitness` is the honest final target wrapper; its `dagSeparation` field is exactly the hard mathematical payload.
- `VerifiedNPDAGLowerBoundSource` is the pnp4 source wrapper for the same hard payload. Supplying this record is not progress unless its fields come from a real theorem.
- `SearchMCSPMagnificationContract` packages the main missing magnification theorem as a field from weak search-MCSP lower bound to verified DAG lower-bound source.
- `SearchMCSPWeakLowerBound` and `SearchMCSPWeakCircuitLowerBound` package lower-bound Props and proofs; useful only when the Prop is nontrivial and independently proved.
- Prop-field budget records appear throughout parser/runtime, prefix-language, local-PRG, formula, AC0[p], and locality layers.
- The partial/legacy route surface is broad: many `_Partial` files are useful, while old support-bound/final-provider paths are audit-only.
- Refuted support-bounds remain callable in places; they must not feed new endpoints.
- `FinalPayloadProvider` / typeclass channels are specifically dangerous because they can hide final payloads behind provider resolution; current quarantines should remain.
- Noncomputable default payloads using `Classical.choice`/`Classical.choose` are acceptable for explicit witness extraction from hypotheses, but unsafe if turned into default lower-bound providers.
- `PDT.WellFormed := True`, trivial marker theorems, and task-proposed `witness_marker : Prop := True` patterns are placeholders, not formal progress.

## 6. What is mathematically missing?

### Gap 1: Non-vacuous `NP_not_subset_PpolyDAG`

- **Where it appears:** `ResearchGapWitness.dagSeparation`, `P_ne_NP_final_dag_only`, `BridgeToPpolyDAG`, A02/A07/A08 final bridge surfaces.
- **Why it is not just engineering:** This is the central circuit lower-bound theorem: exhibit an NP language with no polynomial-size DAG circuit family. No amount of record repackaging proves it.
- **What would close it:** A theorem establishing `NP_not_subset_PpolyDAG` for a concrete NP language, or an honestly proved `VerifiedNPDAGLowerBoundSource` whose dependency closure does not use refuted/vacuous channels.
- **Current Phase 1 task coverage:** None. X/L/B/K tasks do not prove this; they can only add infrastructure or typed surfaces.

### Gap 2: Search-MCSP weak lower bound plus magnification to verified DAG source

- **Where it appears:** `SearchMCSPWeakLowerBound`, `SearchMCSPWeakCircuitLowerBound`, `SearchMCSPMagnificationContract`, `TreeMCSPSearchMagnificationSource`, `CompressionMagnification`.
- **Why it is not just engineering:** The weak lower bound and its magnification into a DAG lower bound are substantive complexity-theoretic claims, not serialization or API work.
- **What would close it:** A proved weak search-MCSP lower bound for a concrete target plus a proved magnification theorem yielding `VerifiedNPDAGLowerBoundSource`.
- **Current Phase 1 task coverage:** X02 may help concrete parser/runtime infrastructure but does not prove weak lower bounds or magnification. L01 is a literature surface only under its current spec.

### Gap 3: Restricted lower bounds to `PpolyDAG` bridge

- **Where it appears:** AC0[p], formula, local-PRG, coin-problem, and asymptotic bridge files; `PvsNPBridgeRequirements` and `RestrictedToVerifiedDAGBridge`.
- **Why it is not just engineering:** Restricted circuit lower bounds do not imply `NP_not_subset_PpolyDAG` without a mathematically valid bridge that avoids known natural-proof/locality/hardwiring failures.
- **What would close it:** A theorem proving that a particular restricted lower-bound source yields a verified DAG lower-bound source, with hardwiring/provenance exclusions genuinely handled.
- **Current Phase 1 task coverage:** None as written. B tasks could classify barriers but not supply the bridge.

### Gap 4: Partial-MCSP locality/provider payload

- **Where it appears:** `StructuredLocalityProviderPartial`, shrinkage/certificate providers, `FormulaRestrictionCertificateDataPartial`, formula/locality endpoints.
- **Why it is not just engineering:** The provider asserts nontrivial locality/shrinkage and formula-to-general extraction facts. Old universal support-bound variants are known inconsistent or vacuous.
- **What would close it:** A provenance-restricted, non-refuted locality theorem that applies to the concrete partial-MCSP route and survives hardwiring attacks.
- **Current Phase 1 task coverage:** None directly. A limited cleanup task could quarantine unsafe variants, but not prove the provider theorem.

### Gap 5: Prefix-extension language NP membership and concrete parser correctness/runtime

- **Where it appears:** `PrefixExtensionLanguage`, `PrefixExtensionLanguageNP`, `PrefixExtensionLanguageRuntime`, X01/X02.
- **Why it is not just engineering:** Some parts are engineering, but proving NP membership with a concrete verifier, length convention, certificate encoding, and runtime bounds is formal-methods work needed before using the language as a legitimate NP target. It still would not prove a lower bound.
- **What would close it:** Concrete computable parser/encoder with round-trip and malformed-rejection proofs, plus verifier/TM/runtime connection to the frozen NP interface.
- **Current Phase 1 task coverage:** X01/X02 address pieces, but should be held/re-scoped until the M(n)/tableLen and NP_TM bridge details are made precise.

## 7. What is engineering / formalization work?

| Task title | Exact files | Dependency | Expected value | Risk | Dispatch? |
| --- | --- | --- | --- | --- | --- |
| Quarantine legacy support-bound/final-provider surfaces | `pnp3/Magnification/FinalResultAuditRoutes.lean`, `FinalResultMainline.lean`, route-surface tests/docs only after governance approval | A01/A02/A10 | Reduce accidental import/reuse of refuted channels | High if it changes public API or trust-root semantics | Later after spec repair; not in this markdown-only wave |
| Add explicit audit tags/comments for old support-bound constructors | specific support-bound declarations in `pnp3/Magnification/LocalityProvider_Partial.lean`, `AC0LocalityBridge.lean` | A01/A03/A10 | Makes wrapper risk visible to future engineers | Medium: comment-only or naming-only should not disturb proofs | Later; infrastructure only |
| Repair NoGoLog stale metadata / formal-witness status | `outputs/nogolog.jsonl`, NoGo docs/tests | A09 | Prevents overclaiming formal NoGo coverage | Medium-high because JSONL edit policy and accepted/needs_review semantics matter | Later after operator-approved governance task |
| ContractExpansion parser feasibility spike | `pnp4/Pnp4/Frontier/ContractExpansion/*` new spike doc or revised X02 task only | A08 | Clarifies M(n), `tableLen`, serialization, and round-trip choices before Lean implementation | Low if markdown-only; high if directly coded without design | Dispatch now only as markdown/design, not X02 implementation |
| Add A11 gate and fix dispatch language | `README.md`, `COMMON_WORKER_INSTRUCTIONS.md`, task metadata | A11 | Align seed pack with audit reality and prevent premature B/K/X dispatch | Low | Dispatch now as governance/doc repair after A11 |
| Surface-test/audit additions for any future theorem surfaces | `pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean`, `AxiomsAudit.lean` | Any approved Lean task | Keeps public API honest | Low-medium | Later, coupled to approved Lean work |
| Barrier classifier template only | markdown template, possibly a small non-automatic Lean enum | A04/A09 | Useful operator checklist | Low if it does not claim automatic detection | Approve after governance repair; not as K01 automatic checker |

## 8. Planned Phase 2-5 task review

| Task | Decision | Why |
| --- | --- | --- |
| L01 | DOWNGRADE_TO_MARKDOWN | Current spec mostly creates typed structures with `correctness : Prop`, `witness_marker : Prop := True`, and a trivial compositional theorem. That is a literature-surface placeholder, not a formalized Hirahara reduction. A markdown design/literature map is more honest unless scope is rewritten to prove a real lemma already supported by local definitions. |
| L02 | DOWNGRADE_TO_MARKDOWN | Current spec packages deep bounded-arithmetic metatheorems as structure fields. This is valuable for literature mapping but not worth Lean theorem-as-field work now. |
| B01 | REWRITE_SCOPE | Do not approve if it only packages Razborov-Rudich as a field `barrierTheorem`. Re-scope to a markdown/Lean interface that forbids theorem-as-field overclaiming, or to small operational definitions with no barrier theorem claim. |
| B02 | REWRITE_SCOPE | Current collapse/separation oracle placeholders and placeholder predicates cannot honestly be called concrete BGS witnesses. Re-scope to markdown design or minimal oracle interface with explicit no-content caveats. |
| B03 | DOWNGRADE_TO_MARKDOWN | Current expected theorems are `True := trivial` and algebrization is a placeholder. Markdown barrier template is more honest until algebraic-oracle machinery exists. |
| K01 | REWRITE_SCOPE | Do not approve an automatic NoGo checker that pretends manual certificate matching is automatic. A09 shows incomplete/stale NoGo witness coverage. Re-scope to operator-assistance with explicit `safety_unclear` default and no accepted-guard promotion. |
| K02 | APPROVE_AFTER_REPAIR | A pre-dispatch classification template is useful after governance docs are fixed. It must remain decision support, not automatic RED-light/no-go production. |
| X01 | HOLD_PENDING_DEPENDENCY | A generic `PolyTimeVerifierSpec.toNP_TM` bridge may be useful, but only after confirming it is not just an `NP_TM` wrapper and that toy verifier/runtime semantics match frozen interfaces. Needs D0/A06/A08 design review first. |
| X02 | HOLD_PENDING_DEPENDENCY | Parser implementation is useful, but A08 flags unresolved concrete serialization, `M(n)`/`tableLen`, runtime-budget, and NP-membership issues. Do not dispatch until X01/design dependencies and length convention are fixed. |

## 9. Phase 1+ dispatch list

At most five initial tasks should be opened, and only as infrastructure/governance/design. None is source-theorem progress.

### A11-G01 — Seed-pack governance repair

- **Title:** Add A11 gate and fix dispatch/gating language.
- **Exact scope:** Update dispatch docs so Phase 2-5 tasks are no longer all described as independently dispatchable now.
- **Files allowed:** `seed_packs/phase1_20engineer_parallel_dispatch/README.md`, `COMMON_WORKER_INSTRUCTIONS.md`, relevant task markdown only.
- **Forbidden scope:** Lean code, source theorem, NoGo JSONL changes, trust-root changes.
- **Expected deliverable:** Docs state A11 is the gate, B/K/X tasks require A11-approved rescope, and mainline progress requires `VerifiedNPDAGLowerBoundSource` or `SearchMCSPWeakLowerBound` reduction.
- **Estimated time:** 0.5-1 day.
- **Prerequisite audits:** A01-A11.
- **Why not duplicate:** No existing audit repaired the seed-pack dispatch contradiction.

### A11-G02 — NoGoLog metadata repair plan

- **Title:** Prepare operator-approved NoGoLog stale-metadata repair plan.
- **Exact scope:** Markdown report listing which JSONL fields/line numbers/statuses need edits; no JSONL edits in first pass.
- **Files allowed:** new report under `seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/` or `reports/`.
- **Forbidden scope:** Editing `outputs/nogolog.jsonl`, changing guard status, adding NoGo entries.
- **Expected deliverable:** Precise patch plan for NOGO-000003 and stale formal-witness references.
- **Estimated time:** 0.5-1 day.
- **Prerequisite audits:** A09, A10, A11.
- **Why not duplicate:** A09 identified issues but did not synthesize an operator patch plan.

### A11-D01 — ContractExpansion parser design clarification

- **Title:** Resolve tree-MCSP prefix parser length/serialization design before X02.
- **Exact scope:** Markdown design note for `M(n)`, `tableLen`, prefix input encoding, malformed input, round-trip theorem shape, and runtime caveats.
- **Files allowed:** new design report under seed pack reports/audit_reports; optionally X02 task markdown after governance approval.
- **Forbidden scope:** Lean parser implementation, NP membership theorem, source theorem.
- **Expected deliverable:** A concrete, reviewable X02 rescope that can be implemented without inventing conventions.
- **Estimated time:** 1-2 days.
- **Prerequisite audits:** A08, A06, A11.
- **Why not duplicate:** A08 diagnosed the staging; this task decides conventions.

### A11-D02 — Barrier task rescope pack

- **Title:** Rewrite B01-B03 as honest barrier documentation/interface tasks.
- **Exact scope:** Draft revised B-task specs that avoid theorem-as-field/trivial-marker claims and state operational prerequisites.
- **Files allowed:** task markdown only.
- **Forbidden scope:** Lean barrier theorem implementation, pnp3 barrier edits.
- **Expected deliverable:** Operator-ready replacement tasks or cancellation note for each B task.
- **Estimated time:** 1 day.
- **Prerequisite audits:** A04, A07, A08, A11.
- **Why not duplicate:** Existing B specs are implementation prompts that audits now show are over-scoped/misleading.

### A11-I01 — Legacy-wrapper quarantine inventory

- **Title:** Produce exact edit plan for quarantining refuted/provider/support-bound wrappers.
- **Exact scope:** Markdown inventory mapping each risky declaration to proposed action: leave, comment, rename, move, or test quarantine.
- **Files allowed:** new report only.
- **Forbidden scope:** Lean edits, route-policy guard edits, endpoint changes.
- **Expected deliverable:** A safe follow-up implementation plan, not implementation.
- **Estimated time:** 1-2 days.
- **Prerequisite audits:** A01, A02, A03, A10, A11.
- **Why not duplicate:** A10 is broad marker search; this would be a precise change plan before touching source.

Immediate dispatch approved:
  - A11-G01
  - A11-G02
  - A11-D01
  - A11-D02
  - A11-I01

## 10. Tasks to cancel / hold

Held tasks:
  - X01 pending D0/A06/A08 design review of frozen NP/NP_TM semantics and non-placeholder verifier construction.
  - X02 pending parser length/serialization design, X01 bridge decision, and M(n)/`tableLen` convention.
  - K01 pending A09 metadata repair and rewrite from automatic checker to conservative decision support.
  - K02 pending governance repair, then approve as non-automatic template/classifier.
  - B01/B02 pending rewrite; do not dispatch theorem-as-field barrier statements.

Cancelled / rewrite required:
  - L01 Lean implementation as currently written; downgrade to markdown or rewrite around a real formal lemma.
  - L02 Lean implementation as currently written; downgrade to markdown literature map.
  - B03 Lean implementation as currently written; `True := trivial` marker tasks should be cancelled or downgraded.
  - Any X01 variant that is only an `NP_TM` wrapper with no honest verifier/runtime content.
  - Any X02 variant that ignores unresolved `M(n)`/`tableLen`/serialization issues.
  - Any B01-B03 variant whose core result is only a theorem packaged as a record field.
  - Any K01/K02 variant that claims automatic NoGo detection from incomplete/manual certificates.

## 11. Governance repairs needed before next wave

- Fix `COMMON_WORKER_INSTRUCTIONS.md` references to `E<NN>` task naming; the seed pack now uses A/L/B/K/X IDs.
- Fix branch naming guidance so it does not mandate old `phase1-E<NN>` branch patterns.
- Remove or qualify README wording that says all 19 tasks are dispatchable now.
- Add A11 as the explicit gate before Phase 1+ / B / K / X / L implementation dispatch.
- Add B/K/X gating: B tasks require anti-placeholder scope; K tasks require A09/A11 status; X tasks require A08/D0 length/runtime design.
- Rename or downgrade L01/L02 as literature maps unless real theorem obligations are specified.
- Add a rule that theorem-as-field barrier packages and `True` marker theorems are not accepted as implementation progress.
- Add an explicit instruction that restricted AC0[p], formula, local-PRG, and coin-problem work is side-track unless paired with a verified DAG bridge.
- Require every future task prompt to state progress classification: Mainline / Side track / Infrastructure.
- Require A11-reviewed dispatch list to be copied into future operator prompts.

Governance repairs:
  - A11 gate addition.
  - COMMON E<NN> mismatch repair.
  - Branch naming repair.
  - Remove/qualify “all 19 dispatchable now”.
  - B/K/X gating.
  - Literature/barrier task renames or downgrades.
  - Explicit no theorem-as-field/no `True` marker acceptance rule.

## 12. Final operator decision

Dispatch now:
  - A11-G01 — seed-pack governance repair.
  - A11-G02 — NoGoLog metadata repair plan, markdown only.
  - A11-D01 — ContractExpansion parser design clarification, markdown only.
  - A11-D02 — Barrier task rescope pack, markdown only.
  - A11-I01 — Legacy-wrapper quarantine inventory, markdown only.

Hold:
  - X01 until NP/NP_TM bridge semantics and toy verifier/runtime obligations are reviewed.
  - X02 until parser serialization and M(n)/`tableLen` conventions are fixed.
  - K01 until A09 issues are repaired and task is rewritten as conservative decision support.
  - K02 until governance repair lands.
  - B01/B02 until rewritten to avoid theorem-as-field barrier claims.

Cancel:
  - L01/L02 Lean typed-surface implementations as currently specified; downgrade to markdown or rewrite.
  - B03 as currently specified; trivial marker theorem implementation should not be dispatched.
  - Any implementation route that wraps `ResearchGapWitness`, `VerifiedNPDAGLowerBoundSource`, `SourceTheorem`, `gap_from`, support-bounds, or final payload providers without proving the hard mathematical source.

Next:
  - Land A11.
  - Perform A11-G01 governance repair before authorizing any Lean implementation wave.
  - Reissue only the five listed markdown/design tasks, then review their outputs for a second gate.

Top 3 mathematical gaps:
  1. Non-vacuous `NP_not_subset_PpolyDAG` / `ResearchGapWitness.dagSeparation`.
  2. Concrete weak search-MCSP lower bound plus magnification to `VerifiedNPDAGLowerBoundSource`.
  3. Valid restricted-lower-bound-to-`PpolyDAG` bridge avoiding hardwiring/support-bound failures.

Top 3 engineering tasks:
  1. Seed-pack governance repair with A11 gate.
  2. ContractExpansion parser length/serialization design before X02.
  3. NoGoLog stale metadata repair plan before K01/K02.

Commands run:
  - `ls seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A*.md` -> PASS; A01-A10 reports are present.
  - `rg -n "Executive verdict|Verdict:" seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A*.md` -> PASS; all A01-A10 verdict sections found.
  - `./scripts/check.sh` -> FAIL/WARNING; Lean build and guard steps passed through Step 12.d, then Step 12.e coordinator HTTP service e2e hit `ConnectionResetError: [Errno 104] Connection reset by peer` during parallel `/v1/result` submission.

Scope violations:
  none

Honest caveats:
  - This synthesis relies on the merged audit reports as the primary evidence; it did not re-audit every Lean proof body.
  - Some A10 repository-wide findings came from structural search rather than full proof-by-proof reading of every matched file.
  - Optional context files were not needed for the core decision because A01-A10 were all present and sufficient.
