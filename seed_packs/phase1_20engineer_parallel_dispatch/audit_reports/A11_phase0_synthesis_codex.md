# A11 — Phase 0 synthesis and dispatch decision

Task: A11  
Engineer handle: codex  
Branch: main  
Commit before: fe03a5751cf3282c15fc2e45645a5fb66386551a  
Commit after: recorded in git commit containing this report  
Scope classification: Infrastructure / operator synthesis. Markdown-only; no Lean/source/spec/JSONL edits.

## 1. Executive verdict

**PHASE0_COMPLETE_DISPATCH_LIMITED_PHASE1_PLUS**

All A01-A10 audit reports are present. The audits agree on a strict conclusion: the repository has substantial kernel-checked infrastructure, but no Phase 0 report found a non-vacuous source of `ResearchGapWitness.dagSeparation`, `VerifiedNPDAGLowerBoundSource`, or `SearchMCSPWeakLowerBound`. Therefore Phase 1+ may dispatch only limited hygiene, documentation, and explicitly conditional infrastructure tasks. Do **not** dispatch a broad implementation wave that claims lower-bound-source progress.

## 2. Audit coverage table

| Audit | Present? | Executive verdict | Main area | Confidence | Main caveat |
| --- | --- | --- | --- | --- | --- |
| A01 | yes | PARTIAL_BUT_USEFUL | pnp3 `Magnification/*_Partial.lean` | High | Strong partial-MCSP/formula/locality plumbing, but no DAG/source bridge; support-bound paths are refuted/vacuous risk. |
| A02 | yes | PARTIAL_BUT_USEFUL | pnp3 `FinalResult*.lean` | High | Final pipeline is complete only after a supplied `NP_not_subset_PpolyDAG`/`ResearchGapWitness`; provider endpoints are quarantined. |
| A03 | yes | PARTIAL_BUT_USEFUL | pnp3 AC0/asymptotic/bridge files | Medium-high | AC0/formula collapse surfaces are side tracks unless paired with a real `PpolyDAG` bridge. |
| A04 | yes | PARTIAL_BUT_USEFUL | pnp3 barrier files | High | Barrier structures are minimal interfaces; no concrete RR/BGS/AW bypass witnesses. |
| A05 | yes | PARTIAL_BUT_USEFUL | pnp3 `LowerBounds/` | Medium-high | Many real finite/partial contradiction lemmas, but strongest endpoints are conditional, enriched-interface, or weak-route payloads. |
| A06 | yes | PARTIAL_BUT_USEFUL | pnp3 `Models/` and non-trust-root `Complexity/` | Medium-high | Mostly safe model/TM infrastructure; no final hard payload, some placeholder-like internal helper surfaces. |
| A07 | yes | PARTIAL_BUT_USEFUL | pnp4 `AlgorithmsToLowerBounds/` | High | AC0[p]/coin/local-PRG/formula results are contract surfaces; `VerifiedNPDAGLowerBoundSource` is only consumed, not produced. |
| A08 | yes | PARTIAL_BUT_USEFUL | pnp4 `Frontier/` and `ContractExpansion/` | High | SearchMCSP magnification is a staged contract; prefix-extension NP/runtime/parser work remains staged. |
| A09 | yes | PARTIAL_BUT_USEFUL | NoGoLog formal witnesses | High | Most formal witnesses compile, but some JSONL line anchors/status wording are stale; NOGO-000003 is not formalized. |
| A10 | yes | PARTIAL_BUT_USEFUL | partial/legacy/TODO/placeholder markers | Medium-high | Marker density is high; one active `True -- placeholder` and many noncomputable/choose hotspots need classification, not promotion. |

## 3. Repo state summary

- **pnp3 Magnification partials:** Kernel-checked conditional partial-MCSP formula/locality route exists. It can produce formula/real separation conclusions from explicit locality/lower-bound/provider hypotheses, but not `NP_not_subset_PpolyDAG` or `VerifiedNPDAGLowerBoundSource`.
- **pnp3 FinalResult pipeline:** The final bridge from an honest DAG separation to `P_ne_NP` is already wired. This is conditional infrastructure; it does not supply the missing DAG separation.
- **AC0 / asymptotic / bridge files:** AC0 and formula collapse surfaces mostly package restricted lower-bound or asymptotic implications. They remain side tracks without a DAG bridge; several support-bound assumptions are known weak/refuted.
- **Barrier files:** pnp3 barriers are minimal typed interfaces plus audit wrappers. They do not encode concrete oracle/algebraic/natural-proof witness machinery.
- **LowerBounds:** Substantial fixed-slice partial-MCSP, anti-checker, local-solver, and DAG/asymptotic interface work exists. The meaningful outputs are conditional or restricted; failed historical routes are quarantined but still visible.
- **Models / Complexity:** Core models and internal TM/circuit plumbing are reusable infrastructure. No audited model file closes a source theorem. Some internal helper predicates are intentionally skeletal.
- **pnp4 AlgorithmsToLowerBounds:** Rich finite truth-table MCSP, coin, masking, local-PRG, formula, and AC0[p] pipeline. Published theorem content is usually represented by contracts; the pnp3 bridge starts only from a fully supplied `VerifiedNPDAGLowerBoundSource`.
- **pnp4 Frontier / ContractExpansion:** The canonical mainline interfaces are present: weak SearchMCSP lower-bound packages, magnification contracts, tree-MCSP concrete targets, C-DAG adapter, and prefix-extension language/runtime scaffolding. Parser, runtime, NP-membership, and actual magnification fields remain obligations.
- **NoGoLog:** NoGo entries provide valuable negative/audit barriers against support-cardinality, syntax-only, hardwiring, and normalization filter routes. They are not lower bounds.
- **Legacy / partial markers:** `_Partial`, `RefutedRoute`, `Vacuous`, `FinalPayloadProvider`, support-bound/default-provider, noncomputable default, and placeholder patterns are present and mostly guarded, but operator prompts should assume they are easy to misuse.

## 4. What is actually kernel-checked?

### A. Canonical useful artifacts

- `ResearchGapWitness → P_ne_NP` and `NP_not_subset_PpolyDAG → P_ne_NP` style final-boundary theorems in pnp3.
- `VerifiedNPDAGLowerBoundSource → NP_not_subset_PpolyDAG → P_ne_NP` bridge in pnp4.
- Partial-MCSP Step-C/local solver contradiction lemmas and locality-lift adapters under explicit hypotheses.
- Finite `CircuitFamilyClass`, `SizeLowerBound`, `TruthTable`, tree-MCSP predicate, coin problem, masking, threshold-oracle, and local-PRG transfer lemmas.
- C-DAG adapter equivalences between pnp3 DAG witnesses and pnp4 circuit-family wrappers.
- Prefix-extension Boolean semantics, parser-failure rejection, relation decidability for codec-induced tree-MCSP, and ambient-length arithmetic lemmas.

### B. Conditional wrappers

- `MagnificationAssumptions_fromPipeline` and other final-result route packages.
- `FormulaLowerBoundHypothesisPartial`, `StructuredLocalityProviderPartial`, and partial provider/certificate packages.
- `AC0pHalfVsFairCoinLowerBoundContract`, `HalfVsFairMCSPCoinReductionContract`, `PublishedLocalPRGRouteContract`, `FormulaCircuitPublishedLowerBoundContract`, and CKLM theorem-facing contracts.
- `SearchMCSPWeakLowerBound`, `SearchMCSPWeakCircuitLowerBound`, `SearchMCSPMagnificationContract`, and `TreeMCSPSearchMagnificationSource`.
- `RestrictedToVerifiedDAGBridge` and `PvsNPBridgeRequirement` wrappers.

### C. Audit-only theorems

- Route-surface and axiom-audit checks for refuted/vacuous final routes.
- NoGo formal witnesses for support-cardinality-only, log-width truth-table, prefix-AND hardwiring, rewrite-attack, and structural-normalization obstructions.
- Barrier audit wrappers and theorem surfaces that document what failed routes imply only under refuted hypotheses.

### D. Refuted/vacuous route witnesses

- `VacuousFinalPayloadProvider` and `Vacuous_P_ne_NP_via_FinalPayloadProvider`.
- `RefutedRoute_*` final wrappers and ex-falso/provider routes.
- Support-bound based `FormulaSupportRestrictionBoundsPartial` / `FormulaSupportBoundsFromMultiSwitchingContract` paths when used without provenance restrictions.
- CKLM asymptotic growth route requiring an envelope condition already shown false for the current encoding.

### E. Adapter/infrastructure theorems

- pnp3/pnp4 circuit-model adapters, tree-circuit and formula-class adapters, exact threshold-language adapters, and finite arithmetic lemmas.
- Surface-test wrappers and `#print axioms` audit declarations.
- TM/copy/PDT helper theorems that support infrastructure but do not state source lower bounds.

## 5. What is staged / placeholder / wrapper?

Major staged patterns discovered across A01-A10:

- **`ResearchGapWitness` wrappers:** Final bridge is real, but a wrapper around `ResearchGapWitness` is exactly the missing payload unless it proves `dagSeparation` non-vacuously.
- **`VerifiedNPDAGLowerBoundSource` wrappers:** Canonical and useful as a pnp4 endpoint, but the `notInPpolyDAG` field is the hard theorem. Do not instantiate from restricted lower bounds without a real DAG bridge.
- **`SearchMCSPMagnificationContract`:** The field `magnifiesToVerifiedDAGSource` packages the main hard magnification theorem. Current code stages the obligation; it does not prove it.
- **Prop-field budget records:** `PrefixExtensionNPVerifierBudget`, `TreeMCSPPrefixParserObligations`, runtime budgets, local-PRG contracts, and barrier packages often store real mathematical/engineering obligations as `Prop` fields.
- **partial/legacy routes:** `_Partial` and legacy final-route modules are useful for audit and conditional side tracks, not automatic mainline progress.
- **refuted support-bounds:** Universal support-bound assumptions and support-cardinality filters have formal counterexamples/no-go witnesses.
- **`FinalPayloadProvider` / typeclass channels:** Quarantined audit-only; must not be reused to satisfy final payloads.
- **noncomputable default payloads:** `Nonempty` plus `Classical.choice` default provider paths can make a hard provider look available; require explicit provenance and no typeclass automation.
- **Trivial placeholders:** `PDT.WellFormed := True` and proof-local `True` helper theorems are engineering debt, not mathematical evidence.

## 6. What is mathematically missing?

### Gap 1 — Non-vacuous `NP_not_subset_PpolyDAG`

- **Where it appears:** pnp3 `ResearchGapWitness.dagSeparation`, pnp3 FinalResult, pnp4 `VerifiedNPDAGLowerBoundSource.notInPpolyDAG`.
- **Why not just engineering:** This is the target nonuniform lower bound for an NP language against polynomial-size DAG circuits. Wrapping it in structures or forwarding it through final theorems does not reduce the mathematical burden.
- **Needed to close:** A genuine theorem proving an explicit NP language is not in `PpolyDAG`, or an accepted theorem source with audited semantics that implies that statement.
- **Current Phase 1 task addresses it?** No. L/B/K/X tasks provide surfaces/tools/parser infrastructure, not a DAG lower-bound proof.

### Gap 2 — Search-MCSP weak lower bound plus magnification theorem

- **Where it appears:** pnp4 `SearchMCSPWeakLowerBound`, `SearchMCSPWeakCircuitLowerBound`, `SearchMCSPMagnificationContract`, `TreeMCSPSearchMagnificationSource`.
- **Why not just engineering:** The contract field converting weak lower bounds to `VerifiedNPDAGLowerBoundSource` is the compression/magnification theorem; supplying it requires real complexity theory, not a parser or record refactor.
- **Needed to close:** A concrete weak lower bound for the target search problem and a proof that the lower bound magnifies to a verified NP-vs-DAG source.
- **Current Phase 1 task addresses it?** L01 can help state search-to-decision context, X01/X02 can help parser/NP infrastructure, but none proves the weak lower bound or magnification contract.

### Gap 3 — Restricted lower bounds to `PpolyDAG` bridge

- **Where it appears:** AC0[p], formula, local-PRG, coin-problem, partial-MCSP endpoints in pnp3/pnp4.
- **Why not just engineering:** AC0[p]/formula lower bounds are strictly weaker/restricted circuit-class statements. The constitution requires a bridge to `PpolyDAG`/`VerifiedNPDAGLowerBoundSource`; such a bridge is not a type adaptation.
- **Needed to close:** A theorem showing the restricted lower-bound target yields an NP-language lower bound against polynomial-size DAG circuits, with hardwiring/provenance counterexamples excluded.
- **Current Phase 1 task addresses it?** No. A07/A08 explicitly find no such adapter.

### Gap 4 — Non-vacuous locality/provenance filters

- **Where it appears:** partial locality providers, support-bound routes, FP3/V2 filter NoGo entries.
- **Why not just engineering:** Existing NoGo theorems show whole families of support-cardinality/syntax/normalization filters accept hardwired or adversarial witnesses.
- **Needed to close:** A semantic provenance condition robust to known hardwiring, rewrite, and normalization attacks, plus proof it feeds a DAG source.
- **Current Phase 1 task addresses it?** No. K01/K02 can record/check operator certificates only if scoped as manual decision support.

### Gap 5 — Concrete barrier-bypass certificates

- **Where it appears:** pnp3 `Barrier/*`, planned B01-B03.
- **Why not just engineering:** Meaningful RR/BGS/AW bypasses require actual oracle worlds, naturalness failures, or algebraic-oracle separations for the route, not records with arbitrary `Prop` fields.
- **Needed to close:** Route-specific mathematical barrier certificates tied to a candidate theorem.
- **Current Phase 1 task addresses it?** Not as written; B01-B03 mostly propose field-packaging/skeletons.

## 7. What is engineering / formalization work?

| Task title | Exact files | Dependency | Expected value | Risk | Dispatch decision |
| --- | --- | --- | --- | --- | --- |
| Phase 0 pipeline map consolidation | New markdown under `seed_packs/phase1_20engineer_parallel_dispatch/docs/` or an operator-approved README | A01-A08 | Prevent duplicate work and distinguish mainline vs side-track contracts | Low | Dispatch now, markdown-only |
| Surface/audit inventory for existing pnp4 public wrappers | `pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean`, `pnp4/Pnp4/Tests/AxiomsAudit.lean` | A07/A08 | Improves accessibility/axiom hygiene without changing theorems | Medium | Dispatch after exact missing surfaces are enumerated |
| NoGoLog stale-anchor repair | `outputs/nogolog.jsonl` only under operator approval, possibly a markdown failure/repair plan first | A09 | Aligns formal_witness line anchors/status wording | Medium because JSONL is guarded | Later; operator-side governance task first |
| Prefix parser engineering design | Markdown design for `TreeMCSPParserImpl.lean`; no Lean yet | A08 | Fixes `M(n)`/`tableLen`/serialization conventions before X02 | Low | Dispatch now as markdown-only design |
| ContractExpansion NP/runtime test hygiene | pnp4 test files only | A08 | Makes existing codec/decidability/runtime surfaces explicit | Low-medium | Dispatch after design; no NP-membership claim |
| Partial/legacy marker quarantine notes | Markdown or doc-comment-only labels around public partial/support-bound surfaces | A01/A02/A10 | Reduces accidental misuse of refuted/provider routes | Medium | Dispatch after governance repair; avoid semantic changes |
| `PDT.WellFormed` placeholder classification | `pnp3/Core/PDT.lean` only if operator authorizes source hygiene | A10 | Replaces or labels an active `True` placeholder | Medium | Later; not lower-bound wave |
| Cross-route NoGo applicability manual template | Markdown template plus optional trivial Lean datatypes | A09/A10 | Helps operators classify route risks | Medium | Rewrite scope before dispatch |

## 8. Planned Phase 2-5 task review

| Task | Decision | Why |
| --- | --- | --- |
| L01 | DOWNGRADE_TO_MARKDOWN | As written it creates `Prop := True` markers and a reduction record, not a proof. Useful as a literature/design note for future SearchMCSP work; not worth Lean skeleton until tied to current interfaces. |
| L02 | DOWNGRADE_TO_MARKDOWN | Typed bounded-arithmetic surfaces would mostly be theorem-oracle fields. Valuable as governance/barrier context, but Lean records would not formalize the metatheorems. |
| B01 | REWRITE_SCOPE | Do not approve if it only packages RR barrier theorem as a field. Rewrite as markdown route-specific barrier-certificate template or require concrete checked conditions, not arbitrary `Prop` fields. |
| B02 | CANCEL | The task explicitly proposes placeholder collapse/separation oracles and placeholder predicates. That would create misleading kernel-checked skeletons without BGS content. |
| B03 | CANCEL | The task explicitly uses `∀ O, True`, `algebraicExtension : Prop`, and trivial theorem markers. This is theorem-as-field/placeholder work. |
| K01 | REWRITE_SCOPE | Do not pretend manual safety certificates automatically detect NoGo applicability. Rewrite as a markdown/manual certificate schema or a Lean datatype that reports operator-supplied classifications only. |
| K02 | APPROVE_AFTER_REPAIR | A barrier-classification template is useful if explicitly manual/operator-support and if docs fix B/K gating. Lean datatype is acceptable only with no automatic red-light claims. |
| X01 | HOLD_PENDING_DEPENDENCY | Potentially useful, but A08 warns NP bridge work must not accept staged Prop placeholders. First inspect current `NP`/`NP_TM` interfaces and produce a no-faking design; toy verifier may be hard. |
| X02 | REWRITE_SCOPE | Parser work is useful, but current M/tableLen/serialization/runtime issues require a markdown design first. Do not approve implementation until parser conventions and X01 dependency are resolved. |

## 9. Phase 1+ dispatch list

At most five initial tasks should open. None should claim source theorem progress.

### P1P-01 — Phase 0 route map and dispatch errata

- **Exact scope:** One markdown map from A01-A10 showing safe imports, side tracks, hard-payload boundaries, and task gating.
- **Files allowed:** New markdown under `seed_packs/phase1_20engineer_parallel_dispatch/docs/` or `audit_reports/`.
- **Forbidden scope:** Lean, JSONL, spec, trust-root edits; no endpoint/source theorem.
- **Expected deliverable:** Operator-readable route map plus dispatch checklist.
- **Estimated time:** 0.5-1 day.
- **Prerequisite audits:** A01-A10.
- **Why not duplicate:** A11 is a decision summary; this would be a maintained map/checklist.

### P1P-02 — Prefix parser convention design

- **Exact scope:** Markdown-only design resolving encoding, parse/encode round trip, `M(n)`, ambient length, tableLen, malformed rejection, and runtime-claim level for X02.
- **Files allowed:** New markdown under `seed_packs/phase1_20engineer_parallel_dispatch/docs/`.
- **Forbidden scope:** No Lean parser implementation; no `PrefixExtensionLanguage_in_NP`.
- **Expected deliverable:** Implementation-ready spec or explicit blockers.
- **Estimated time:** 1 day.
- **Prerequisite audits:** A08.
- **Why not duplicate:** A08 identifies staged runtime/parser obligations; it does not choose a concrete serialization.

### P1P-03 — NoGoLog anchor repair plan

- **Exact scope:** Markdown-only repair plan for stale NoGoLog line anchors/status wording and dedicated smoke-test decisions.
- **Files allowed:** New markdown under `seed_packs/phase1_20engineer_parallel_dispatch/docs/` or `failures/` if blocked.
- **Forbidden scope:** No JSONL edits in this task.
- **Expected deliverable:** Exact proposed JSONL/test changes for a later operator-approved governance PR.
- **Estimated time:** 0.5 day.
- **Prerequisite audits:** A09.
- **Why not duplicate:** A09 found issues; this scopes the repair without touching guarded logs.

### P1P-04 — Restricted lower-bound side-track guardrail design

- **Exact scope:** Markdown-only policy for AC0[p]/formula/local-PRG/coin route descriptions, including approved phrases and bridge requirements.
- **Files allowed:** New markdown under seed-pack docs.
- **Forbidden scope:** No check-script/spec edits in this first task.
- **Expected deliverable:** Guardrail text for later COMMON/README update.
- **Estimated time:** 0.5 day.
- **Prerequisite audits:** A01/A03/A05/A07.
- **Why not duplicate:** Audits identify the risk; this produces operator-ready policy text.

### P1P-05 — Existing surface-test gap inventory

- **Exact scope:** Markdown-only inventory of missing `check_` wrappers and `#print axioms` entries for existing pnp4 AlgorithmsToLowerBounds/Frontier public theorems.
- **Files allowed:** New markdown under audit/docs.
- **Forbidden scope:** No Lean test edits yet.
- **Expected deliverable:** Exact list of additions for a later small Lean hygiene task.
- **Estimated time:** 1 day.
- **Prerequisite audits:** A07/A08.
- **Why not duplicate:** Audits recommend test hygiene but do not enumerate a minimal non-duplicative patch list.

## 10. Tasks to cancel / hold

- **Cancel B02/B03 as written** because they explicitly authorize placeholder/trivial oracle and algebrization statements.
- **Hold or rewrite B01** unless it proves concrete RR conditions rather than storing the barrier theorem as a field.
- **Downgrade L01/L02 to markdown** until their surfaces are tied to current pnp4 interfaces without `Prop := True` marker claims.
- **Rewrite K01** to avoid presenting manual certificates as automatic NoGo detection.
- **Approve K02 only after governance repair** and only as operator-support classification, not automatic gating.
- **Hold X01** until a no-faking design confirms the bridge cannot accept staged Prop placeholders and a toy verifier is feasible.
- **Rewrite X02** after parser convention design resolves `M(n)`, `tableLen`, serialization, and runtime scope.
- **Hold any task promoting support-bounds/default providers/vacuous providers as lower-bound progress.**
- **Hold any task instantiating `VerifiedNPDAGLowerBoundSource` from AC0[p]/formula/local-PRG results without a real `PpolyDAG` theorem.**

## 11. Governance repairs needed before next wave

- Fix COMMON's `E<NN>` identity/branch/PR-template mismatch for A/L/B/K/X task IDs.
- Change README status from “All tasks are independent and run concurrently” / “All 19 tasks dispatch-able NOW” to A11-gated dispatch.
- Add A11 as the explicit gate before Phase 1+ / B / K / X / L implementation waves.
- Add task-classification labels: mainline, side track, infrastructure, audit-only.
- Add B/K/X gating text: B tasks require concrete witness criteria; K tasks are manual/operator-support unless proven otherwise; X tasks require parser/runtime/no-faking design.
- Rename or rewrite tasks that invite placeholders (`Prop := True`, theorem-as-field, trivial oracle markers).
- Require every future lower-bound task to state whether it reduces `SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource`; otherwise it is side-track/infrastructure.
- Add explicit warning that `BridgeToPpolyDAG.lean` consumes a verified source but does not produce one from restricted lower bounds.
- Add NoGoLog caveat: NOGO-000003 is `needs_review`; some formal witness anchors are stale.

## 12. Final operator decision

Dispatch now:
  - P1P-01 Phase 0 route map and dispatch errata (markdown-only).
  - P1P-02 Prefix parser convention design (markdown-only).
  - P1P-03 NoGoLog anchor repair plan (markdown-only).
  - P1P-04 Restricted lower-bound side-track guardrail design (markdown-only).
  - P1P-05 Existing surface-test gap inventory (markdown-only).

Hold:
  - X01 until no-faking/NP-interface design review.
  - X02 until parser convention design and X01 decision.
  - K02 until README/COMMON governance repair.
  - Any Lean hygiene task touching partial/support-bound/final-route surfaces until exact non-duplicative scope is approved.

Cancel:
  - B02 as written.
  - B03 as written.

Rewrite:
  - L01 as markdown literature/interface alignment, not `Prop := True` Lean surface.
  - L02 as markdown barrier/governance note, not theorem-oracle Lean surface.
  - B01 as concrete barrier-certificate work or markdown template, not theorem-as-field.
  - K01 as manual NoGo certificate support, not automatic detection.
  - X02 as an implementation task only after P1P-02.

Next:
  - Update dispatch docs with A11 gate and revised task decisions.
  - Open only the five markdown Phase 1+ tasks above.
  - After those land, consider one small Lean hygiene task at a time, with explicit “infrastructure only” classification.

## Final structured output

Task: A11  
Engineer handle: codex  
Branch: main  
Commit before: fe03a5751cf3282c15fc2e45645a5fb66386551a  
Commit after: recorded in git commit containing this report

Files added/modified:
  - `seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A11_phase0_synthesis_codex.md`

Outcome:
  SYNTHESIS_LANDED

Executive verdict:
  PHASE0_COMPLETE_DISPATCH_LIMITED_PHASE1_PLUS

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

Immediate dispatch approved:
  - P1P-01 route map / dispatch errata, markdown-only
  - P1P-02 prefix parser convention design, markdown-only
  - P1P-03 NoGoLog anchor repair plan, markdown-only
  - P1P-04 restricted-lower-bound guardrail design, markdown-only
  - P1P-05 existing surface-test gap inventory, markdown-only

Held tasks:
  - X01
  - X02
  - K02 pending governance repair
  - Lean hygiene tasks until exact scope is enumerated

Cancelled / rewrite required:
  - Cancel B02 as written
  - Cancel B03 as written
  - Rewrite L01, L02, B01, K01, X02

Top 3 mathematical gaps:
  1. Non-vacuous `NP_not_subset_PpolyDAG` / `VerifiedNPDAGLowerBoundSource`.
  2. Search-MCSP weak lower bound plus magnification to a verified DAG source.
  3. A real bridge from restricted AC0[p]/formula/local-PRG/coin lower bounds to `PpolyDAG` lower bounds.

Top 3 engineering tasks:
  1. A11 route map / dispatch errata and governance repair.
  2. Prefix parser convention design before X02.
  3. NoGoLog stale-anchor repair plan before JSONL edits.

Governance repairs:
  - COMMON `E<NN>` mismatch for A/L/B/K/X tasks.
  - Branch/PR naming mismatch.
  - Remove “all 19 dispatchable now” wording.
  - Add A11 gate.
  - Add B/K/X gating and no-placeholder rules.
  - Add task renames / downgrade language for L/B/K/X.

Commands run:
  - `ls seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A*.md` -> found A01-A10 plus this A11 report after creation
  - `rg -n "Executive verdict|Verdict:" seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A*.md` -> found verdict lines for A01-A10 and A11 after creation
  - `./scripts/check.sh` -> PASS (all 17 steps passed; existing Lean warnings only)

Scope violations:
  none

Honest caveats:
  - This is a synthesis of the merged audits; I did not re-audit every Lean proof body.
  - The dispatch decisions are intentionally conservative because multiple planned tasks invite theorem-as-field or placeholder work.
  - Some proposed Phase 1+ tasks require new docs paths not present in the original allowed scope; they are recommendations for operator action, not changes made by this task.
