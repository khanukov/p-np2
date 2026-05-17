# A11 — Phase 0 synthesis and dispatch decision

Task: A11  
Engineer handle: codex  
Branch: work (prompt requested `main`; repository checkout was `work`)  
Commit before: fe03a5751cf3282c15fc2e45645a5fb66386551a  
Commit after: TBD

Files added/modified:
  - `seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A11_phase0_synthesis_codex.md`

Outcome:
  SYNTHESIS_LANDED

## 1. Executive verdict

**PHASE0_COMPLETE_DISPATCH_LIMITED_PHASE1_PLUS**

All A01--A10 audit reports are present and consistent: the repository has substantial kernel-checked infrastructure, but Phase 0 did **not** discover a completed source theorem, a closed `ResearchGapWitness`, a closed `VerifiedNPDAGLowerBoundSource`, or a closed `SearchMCSPWeakLowerBound`. The only safe dispatch is a limited, explicitly infrastructure/governance Phase 1+ wave. Anything that merely packages a barrier theorem, support-bound condition, `Prop` field, `FinalPayloadProvider`, `ResearchGapWitness`, `VerifiedNPDAGLowerBoundSource`, or `SearchMCSPMagnificationContract` as a record field must be held or rewritten.

## 2. Audit coverage table

| Audit | Present? | Executive verdict | Main area | Confidence | Main caveat |
| --- | --- | --- | --- | --- | --- |
| A01 | yes | PARTIAL_BUT_USEFUL | pnp3 magnification `_Partial` files | medium-high | Partial-MCSP/formula/locality pipeline is conditional and not a DAG lower-bound source. |
| A02 | yes | PARTIAL_BUT_USEFUL | pnp3 `FinalResult*` pipeline | high | Final endpoint is clean only modulo an honest `ResearchGapWitness`; audit/weak/legacy routes are not reusable as progress. |
| A03 | yes | PARTIAL_BUT_USEFUL | AC0/asymptotic/bridge files | medium-high | AC0/formula routes remain restricted side tracks without a `PpolyDAG` bridge. |
| A04 | yes | PARTIAL_BUT_USEFUL | pnp3 barrier files | high | Barrier files are abstract interfaces/wrappers; `BarrierBypassPackage`-style fields are not concrete bypass certificates. |
| A05 | yes | PARTIAL_BUT_USEFUL | pnp3 `LowerBounds/` | medium | Useful fixed-slice and DAG plumbing exists, but strongest endpoints assume enriched solvers, bridges, or weak-route payloads. |
| A06 | yes | PARTIAL_BUT_USEFUL | pnp3 models/complexity | medium | Core encodings are useful infrastructure; they do not discharge source lower-bound obligations. |
| A07 | yes | PARTIAL_BUT_USEFUL | pnp4 `AlgorithmsToLowerBounds` | medium-high | Many endpoint-looking theorems are conditional wrappers, restricted AC0/formula tracks, or audit/no-go surfaces. |
| A08 | yes | PARTIAL_BUT_USEFUL | pnp4 Frontier / ContractExpansion | medium-high | Frontier has the right mainline contract shape, but hard fields are staged/conditional and parser/runtime layers remain incomplete. |
| A09 | yes | PARTIAL_BUT_USEFUL | NoGoLog formal witnesses | medium | NoGo entries are mostly anchored, but stale anchors/wording require repair before automating kill-machine checks. |
| A10 | yes | PARTIAL_BUT_USEFUL | partial/legacy/placeholder markers | medium | Marker density is high; placeholders and noncomputable/default channels need quarantine, not promotion. |

## 3. Repo state summary

- **pnp3 Magnification partials:** Kernel-checked partial-MCSP formula/locality interfaces and conditional bridges exist. They produce formula/real separation conclusions from explicit provider, locality, Step-C, and NP-strict premises; they do not produce `NP_not_subset_PpolyDAG`.
- **pnp3 FinalResult pipeline:** The canonical final pipeline is structurally honest when fed a real `ResearchGapWitness`. It also contains audit, weak, and legacy channels that are explicitly not progress and must stay quarantined.
- **AC0 / asymptotic / bridge files:** AC0[p], finite-slice, formula, and asymptotic collapse plumbing is useful restricted-track infrastructure. It is not mainline unless paired with a genuine DAG/source bridge.
- **Barrier files:** `pnp3/Barrier` provides minimal abstract interfaces and wrapper assumptions. It does not contain concrete RR/BGS/AW barrier-bypass witnesses.
- **LowerBounds:** Contains meaningful fixed-slice contradiction lemmas, accepted-family counting lemmas, local-solver contradictions, DAG interface layers, and failed-route quarantines. The DAG/mainline endpoints remain conditional on bridges or weak-route payloads.
- **Models / Complexity:** Provides semantic encodings, model definitions, and complexity interfaces that other routes rely on. This area is infrastructure and should not be changed casually because it touches trust-root semantics.
- **pnp4 AlgorithmsToLowerBounds:** Provides canonical pnp4 restricted and mainline wrappers, including `VerifiedNPDAGLowerBoundSource`-oriented APIs and AC0/formula restricted routes. The useful part is mostly adapter theorem infrastructure, not closed lower-bound evidence.
- **pnp4 Frontier / ContractExpansion:** Has the right shape for compression/search-MCSP magnification, prefix-extension language experiments, and contract expansion. The hard mathematical contract remains unproved; parser, codec, runtime, and witness layers are staged.
- **NoGoLog:** Small JSONL ledger is validated by checks and has useful formal witness anchors, but some anchors/wording need repair before mechanical cross-route applicability is credible.
- **Legacy / partial markers:** Active marker searches reveal staged `True` placeholders, `_Partial`/`_Legacy` names, refuted-route surfaces, high `noncomputable def`/`Classical.choose` density, and audit-only provider channels.

## 4. What is actually kernel-checked?

### A. Canonical useful artifacts

- The pnp3 trust-root target shape: `ResearchGapWitness.dagSeparation : NP_not_subset_PpolyDAG` and final conversion from such a witness to the final complexity target.
- Fixed-slice Partial-MCSP anti-checker/local-solver contradictions in `pnp3/LowerBounds`.
- Partial-MCSP formula/locality conditional bridges in `pnp3/Magnification/*_Partial.lean`.
- Accepted-family counting and DAG stable-restriction plumbing in `pnp3/LowerBounds`.
- pnp4 bridge APIs around `VerifiedNPDAGLowerBoundSource`, restricted AC0/formula routes, and search-MCSP contract statements.
- ContractExpansion language, decidability, and runtime-budget surfaces that compile as typed interfaces.

### B. Conditional wrappers

- `ResearchGapWitness` to final result wrappers.
- `VerifiedNPDAGLowerBoundSource` to `NP_not_subset_PpolyDAG` / final bridge wrappers.
- `SearchMCSPMagnificationContract` and compression-magnification wrappers.
- Formula/AC0/locality endpoints parameterized by explicit providers, Step-C hypotheses, NP-strict witnesses, bridge hypotheses, or weak-route payloads.
- Barrier wrappers parameterized by `BarrierBypassPackage` / explicit bypass assumptions.

### C. Audit-only theorems

- Barrier audit wrappers and `#print axioms` surfaces.
- Weak-route surface tests and final-route audit wrappers.
- NoGo witness theorems that document why earlier route shapes fail.
- Refuted-route quarantine tests and rule-guard declarations.

### D. Refuted/vacuous route witnesses

- `FinalPayloadProvider` / `VacuousFinalPayloadProvider` channels.
- `RefutedRoute_*` endpoints deriving conclusions from hypotheses known impossible or vacuous.
- Fixed-slice support-half / empty-family failed routes.
- Support-cardinality-only and hardwiring-vulnerable routes.

### E. Adapter/infrastructure theorems

- AC0/formula bridge adapters.
- pnp4 surface-test wrappers exposing public theorem signatures.
- pnp4 ContractExpansion parser/runtime/decidability adapters.
- pnp3-to-pnp4 import and theorem-surface hygiene around existing APIs.

## 5. What is staged / placeholder / wrapper?

Major staged patterns across A01--A10:

- `ResearchGapWitness` wrappers: honest final wrappers exist, but no closed witness is supplied.
- `VerifiedNPDAGLowerBoundSource` wrappers: pnp4 has the source-object boundary, but many tasks merely assume the object or store it in a field.
- `SearchMCSPMagnificationContract`: the correct frontier contract, but its hard lower-bound/magnification payload is staged as fields.
- `Prop`-field budget records: runtime, parser, barrier, constructivity/largeness/usefulness, and provider conditions often appear as arbitrary `Prop` fields.
- Partial/legacy routes: `_Partial`, `_Legacy`, `WeakRoute`, `FinalResultWeakRoutes`, and audit-route modules encode useful history but are not final progress.
- Refuted support bounds: support-cardinality routes are known vulnerable to hardwiring unless a real provenance restriction is proved.
- `FinalPayloadProvider` / typeclass channels: audit-only hidden-payload mechanisms must not leak into final dependency closures.
- Noncomputable default payloads: `default*` and provider constructors can make unavailable hard data look present.
- Placeholder predicates: e.g. well-formedness or theorem helpers returning `True`; harmless only if kept local and labelled.
- ContractExpansion parser/runtime placeholders: length conventions, parser polynomiality, and TM-step semantics are not discharged by current records.

## 6. What is mathematically missing?

### Gap 1 — Genuine NP lower bound against `PpolyDAG`

- **Where it appears:** `ResearchGapWitness.dagSeparation`, pnp4 `VerifiedNPDAGLowerBoundSource`, and every final bridge.
- **Why it is not engineering:** This is the actual P-vs-NP-hard lower-bound content. A record wrapper or adapter does not prove that some NP language avoids polynomial-size DAG circuits.
- **Needed to close it:** A real source theorem with provenance, semantics, and proof that yields `NP_not_subset_PpolyDAG` without refuted support-bound, provider, or typeclass tricks.
- **Current Phase 1 coverage:** No current Phase 1 task closes it. At most, tasks can map or quarantine interfaces.

### Gap 2 — Search-MCSP weak lower bound plus magnification theorem

- **Where it appears:** `SearchMCSPWeakLowerBound`, `SearchMCSPMagnificationContract`, pnp4 Frontier, and ContractExpansion.
- **Why it is not engineering:** It requires proving a nontrivial lower bound and a magnification implication, not just defining search/decision problem syntax.
- **Needed to close it:** A formal weak lower bound for the intended search-MCSP target plus a verified magnification theorem producing `VerifiedNPDAGLowerBoundSource`.
- **Current Phase 1 coverage:** No. L01 may stage search-to-decision literature, and X01/X02 may improve verifier/parser infrastructure, but neither proves the weak lower bound or magnification.

### Gap 3 — Formula/AC0/locality to DAG bridge

- **Where it appears:** A01/A03/A05 formula, AC0[p], local-PRG, and partial-MCSP routes.
- **Why it is not engineering:** Formula/AC0 lower bounds do not imply `NP_not_subset_PpolyDAG` without a mathematically valid bridge; DAGs are stronger/nonuniformly different targets.
- **Needed to close it:** A theorem translating the restricted lower-bound conclusion into an NP language lower bound against `PpolyDAG` under honest hypotheses.
- **Current Phase 1 coverage:** No current task does this. Any adapter that omits the bridge remains a side track.

### Gap 4 — Support-bound provenance / hardwiring exclusion

- **Where it appears:** support-cardinality, fixed-slice, atlas, and partial support-bound routes.
- **Why it is not engineering:** Truth-table/hardwired witnesses refute broad support-only route shapes; a rename or wrapper cannot remove the counterexample.
- **Needed to close it:** Formal provenance restrictions plus non-vacuity proofs excluding hardwired/truth-table counterexamples.
- **Current Phase 1 coverage:** Only an audit/non-vacuity follow-up could clarify it; no implementation task should rely on it as source progress.

### Gap 5 — Concrete barrier witnesses

- **Where it appears:** B01--B03 and pnp3 barrier wrappers.
- **Why it is not engineering:** Concrete RR/BGS/AW barriers require actual constructivity/largeness/usefulness, oracle, or algebraic-oracle semantics; arbitrary fields prove only a statement scheme.
- **Needed to close it:** Concrete witness models and nontrivial theorems showing a route avoids/triggers barriers.
- **Current Phase 1 coverage:** Existing B tasks as written mostly package fields; they require rewrite or downgrade.

### Gap 6 — NP/TM runtime semantics for prefix-extension language

- **Where it appears:** X01/X02 and ContractExpansion runtime budgets.
- **Why it is not engineering:** Showing membership in the repository's `NP` interface requires real TM/runtime/certificate semantics, not only parser decidability or `Prop` budgets.
- **Needed to close it:** Non-circular verifier specifications, concrete encodings, runtime bounds, and bridge proofs to `NP`.
- **Current Phase 1 coverage:** X01/X02 partially address infrastructure, but not the lower-bound endpoint and must be scoped carefully.

## 7. What is engineering / formalization work?

| Task title | Exact files | Dependency | Expected value | Risk | Dispatch? |
| --- | --- | --- | --- | --- | --- |
| NoGoLog stale-anchor repair | `outputs/nogolog.jsonl` plus formal witness files only if operator authorizes; otherwise a markdown repair plan | A09 | Makes future kill-machine references truthful | medium because JSONL/source edits are sensitive | later/after explicit operator repair task |
| Barrier task rewrite pack | README/task markdown under `seed_packs/phase1_20engineer_parallel_dispatch/tasks/B*.md` | A04 | Prevents B01--B03 from shipping theorem-as-field skeletons | low | now as markdown governance repair |
| ContractExpansion route map | new markdown report under seed pack or pnp4 docs | A08 | Clarifies which R1 fields are parser/runtime/witness/magnification gaps | low | now |
| Partial/legacy public surface map | `pnp3/Tests/WeakRouteSurfaceTests.lean`, `pnp3/Tests/AxiomsAudit.lean`, relevant partial modules | A01/A05/A09/A10 | Makes conditional/refuted declarations explicit | medium | later; Lean hygiene only |
| `PDT.WellFormed` quarantine/replacement | `pnp3/Core/PDT.lean` plus direct consumers | A10 | Removes a semantic-looking `True` placeholder | medium | later after scope review |
| CopyAtOffset placeholder cleanup | `pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/CopyAtOffset.lean` | A10 | Reduces confusing exported `True` theorem | low | later |
| Noncomputable/choose hotspot classification | new markdown report only | A10 | Prioritizes real risk instead of blanket cleanup | low | now/later |
| pnp4 restricted partial-formula adapter | new pnp4 restricted module, `lakefile.lean`, pnp4 tests | A01/A07 | Makes side-track formulas importable with honest labels | medium-high overclaim risk | later, not first wave |
| Prefix parser design note | markdown design first; later `TreeMCSPParserImpl.lean` | A08/X02 | De-risks X02 encoding and length conventions | medium | now as markdown, Lean later |

## 8. Planned Phase 2--5 task review

| Task | Decision | Explanation |
| --- | --- | --- |
| L01 | REWRITE_SCOPE | A typed Hirahara surface may be useful, but the proposed `witness_marker : Prop := True` and field-based reduction risk creating another literature wrapper. Rewrite as markdown/design or a clearly labelled interface task with no marker theorem. |
| L02 | REWRITE_SCOPE | Useful as barrier/literature context, but current structures put deep proof-theoretic metatheorems in fields. Rewrite as markdown/design or strictly audit-only interface, not implementation progress. |
| B01 | REWRITE_SCOPE | Do not approve a natural-proofs task that only packages constructivity/largeness/usefulness and a barrier theorem as fields. It may become an adapter skeleton only after governance repair. |
| B02 | REWRITE_SCOPE | As written it explicitly allows placeholder oracles and placeholder relativized predicates. That is not a concrete BGS witness formalization. Rewrite to statement-scheme markdown/interface or cancel concrete-witness claims. |
| B03 | REWRITE_SCOPE | Algebraic-oracle semantics are under-specified and mostly placeholder. Rewrite to design/interface; no AW barrier implementation should be claimed yet. |
| K01 | HOLD_PENDING_DEPENDENCY | Do not approve automatic NoGo detection until A09 stale anchors/wording are repaired and the tool is scoped as operator decision support, not automatic proof rejection. |
| K02 | APPROVE_AFTER_REPAIR | A markdown + light Lean classifier can be useful after B task wording is repaired; it must not auto-produce red lights or rely on nonexistent B01--B03 outputs. |
| X01 | HOLD_PENDING_DEPENDENCY | Potentially valuable, but only if it proves a non-circular bridge to existing `NP` semantics with a real toy verifier. Do not approve as an `NP_TM` wrapper around staged specs. |
| X02 | HOLD_PENDING_DEPENDENCY | Parser work should wait for an encoding/length/runtime design and preferably X01. The `M(n)`/`tableLen`/round-trip issue must be resolved before Lean implementation. |

## 9. Phase 1+ dispatch list

At most five initial tasks should be opened, and only as infrastructure/governance work.

### P1A — Governance patch for dispatch README/task gates

- **Title:** Add A11 gate and repair dispatch wording.
- **Exact scope:** Markdown-only updates to seed-pack dispatch docs.
- **Files allowed:** `seed_packs/phase1_20engineer_parallel_dispatch/README.md`, `COMMON_WORKER_INSTRUCTIONS.md`, task markdown files if operator approves.
- **Forbidden scope:** Lean/source/spec/NoGoLog edits; no endpoint/source theorem.
- **Expected deliverable:** README no longer says all non-audit tasks are independently dispatchable; B/K/X gates point to A11 decisions.
- **Estimated time:** 0.5 day.
- **Prerequisite audits:** A01--A11.
- **Why not duplicate:** No prior audit report changes the seed pack dispatch instructions.

### P1B — Rewrite B01--B03 as barrier interface/design tasks

- **Title:** Convert barrier implementation tasks into non-overclaiming design/interface tasks.
- **Exact scope:** Markdown-only task rewrites; require concrete witness criteria before Lean.
- **Files allowed:** `seed_packs/phase1_20engineer_parallel_dispatch/tasks/B01_*.md`, `B02_*.md`, `B03_*.md`.
- **Forbidden scope:** pnp3 barrier edits; theorem-as-field deliverables; claims of concrete RR/BGS/AW formalization.
- **Expected deliverable:** Clear approve/hold criteria for any later barrier Lean work.
- **Estimated time:** 0.5--1 day.
- **Prerequisite audits:** A04, A07, A08, A11.
- **Why not duplicate:** A04 identified the issue but did not update task specs.

### P1C — ContractExpansion parser/runtime design note

- **Title:** Resolve X02 encoding, `M(n)`, `tableLen`, and runtime-bound conventions before implementation.
- **Exact scope:** Markdown design document only.
- **Files allowed:** new design markdown under `seed_packs/phase1_20engineer_parallel_dispatch/design/` or `audit_reports/`.
- **Forbidden scope:** no `TreeMCSPParserImpl.lean`, no `PrefixExtensionLanguage_in_NP`, no source theorem.
- **Expected deliverable:** Encoding choice, length convention, malformed-input semantics, and TM/runtime handoff plan.
- **Estimated time:** 1 day.
- **Prerequisite audits:** A08, A10, A11.
- **Why not duplicate:** A08 describes the gap; this task fixes dispatch-ready implementation criteria.

### P1D — NoGoLog anchor repair plan

- **Title:** Repair plan for stale NoGo formal witness anchors.
- **Exact scope:** Markdown-first plan listing exact JSONL/source edits needed; optional follow-up implementation PR only after operator approval.
- **Files allowed:** new markdown report under `seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/`.
- **Forbidden scope:** no JSONL edits in this first task; no automatic NoGo checker.
- **Expected deliverable:** Per-entry repair checklist and risk classification.
- **Estimated time:** 0.5--1 day.
- **Prerequisite audits:** A09, A11.
- **Why not duplicate:** A09 found issues; it did not produce an operator repair patch.

### P1E — Noncomputable/default/provider hotspot classification

- **Title:** Classify high-risk default/provider/noncomputable surfaces.
- **Exact scope:** Markdown-only deep dive on top hotspots from A10.
- **Files allowed:** new markdown report under `audit_reports/`.
- **Forbidden scope:** no Lean cleanup, no semantics changes, no provider promotion.
- **Expected deliverable:** Ranked list of which hotspots are harmless, audit-only, or require quarantine.
- **Estimated time:** 1 day.
- **Prerequisite audits:** A02, A10, A11.
- **Why not duplicate:** A10 counted markers broadly; this ranks actionability.

## 10. Tasks to cancel / hold

- **Hold X01** until it is rewritten to forbid staged `Prop` specs and to require a real bridge into the existing `NP` interface plus a toy verifier that is not vacuous.
- **Hold X02** until X01/design dependencies settle `M(n)`, `tableLen`, parser round-trip, malformed rejection, and runtime semantics.
- **Rewrite B01--B03** before any dispatch; cancel any version that packages barrier theorems as arbitrary fields.
- **Hold K01** until A09 anchor repairs land and the output is framed as applicability evidence, not automatic NoGo detection.
- **Hold K02** until B task wording is repaired; a markdown classifier template can proceed after repair.
- **Rewrite L01/L02** if dispatched; typed literature surfaces should avoid `Prop := True` marker theorems and avoid claiming formalized metatheorems.
- **Hold any task promoting support-bound, weak-route, final-provider, or refuted-route wrappers as mainline progress.**

## 11. Governance repairs needed before next wave

- Add A11 as an explicit gate in the seed-pack README before Phase 1+ / B / K / X / L dispatch.
- Replace “all non-audit tasks independent/dispatchable now” wording with dependency-gated language.
- Fix branch naming/documentation mismatch between old E-task instructions and A/L/B/K/X tasks.
- Repair COMMON worker output references to E-numbered tasks where they do not apply.
- Add explicit B/K/X gating: B tasks require concrete-witness criteria; K tasks require A09 repair; X tasks require runtime/parser design.
- Rename or rewrite task titles that overstate “formalization” when the deliverable is only a typed surface or statement scheme.
- Require all future lower-bound tasks to state Mainline/Side track/Infrastructure classification before implementation.
- Add “no theorem-as-field progress” language for barrier/literature/frontier tasks.

## 12. Final operator decision

Dispatch now:
  - P1A governance patch for dispatch README/task gates.
  - P1B rewrite B01--B03 as barrier interface/design tasks.
  - P1C ContractExpansion parser/runtime design note.
  - P1D NoGoLog anchor repair plan.
  - P1E noncomputable/default/provider hotspot classification.

Hold:
  - L01, L02 until rewritten as non-overclaiming literature/design/interface tasks.
  - K01 until A09 anchor repair is complete and automatic-checker claims are removed.
  - K02 until B/K governance wording is repaired.
  - X01 until non-circular `NP` bridge criteria and toy verifier feasibility are confirmed.
  - X02 until X01/design dependencies settle parser length/runtime conventions.
  - Any pnp4 adapter from formula/AC0/partial routes to mainline targets unless a real DAG bridge is supplied.

Cancel:
  - Any version of B01--B03 that proves only a theorem packaged as a field.
  - Any version of X01 that is just an `NP_TM` wrapper around a staged `Prop` certificate.
  - Any version of X02 that ignores `M(n)`/`tableLen`/runtime semantics.
  - Any task claiming P-vs-NP mainline progress from support-bound/refuted/final-provider channels.

Next:
  - Operator should land A11, patch seed-pack governance, then dispatch only the five listed infrastructure/design tasks. No Phase 1+ source-theorem implementation should start until those gates are repaired.

---

## Final structured output

Task: A11  
Engineer handle: codex  
Branch: work (prompt requested `main`; checkout was `work`)  
Commit before: fe03a5751cf3282c15fc2e45645a5fb66386551a  
Commit after: TBD

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
  - P1A governance patch for dispatch README/task gates
  - P1B rewrite B01--B03 as barrier interface/design tasks
  - P1C ContractExpansion parser/runtime design note
  - P1D NoGoLog anchor repair plan
  - P1E noncomputable/default/provider hotspot classification

Held tasks:
  - L01
  - L02
  - K01
  - K02 until governance repair
  - X01
  - X02
  - any formula/AC0/partial adapter claiming mainline progress without a DAG bridge

Cancelled / rewrite required:
  - B01
  - B02
  - B03
  - theorem-as-field barrier tasks
  - staged-`Prop` NP wrapper tasks
  - support-bound/refuted/final-provider progress tasks

Top 3 mathematical gaps:
  1. A genuine `NP_not_subset_PpolyDAG` / `VerifiedNPDAGLowerBoundSource` payload.
  2. A real `SearchMCSPWeakLowerBound` plus magnification theorem.
  3. A valid bridge from restricted formula/AC0/locality lower bounds to `PpolyDAG`.

Top 3 engineering tasks:
  1. Seed-pack governance and dispatch-gate repair.
  2. B01--B03 task rewrite to avoid theorem-as-field barrier overclaiming.
  3. ContractExpansion parser/runtime design before X01/X02 Lean work.

Governance repairs:
  - Add A11 gate.
  - Replace “all dispatchable now” language.
  - Fix E-number / A-L-B-K-X task naming mismatch.
  - Gate B/K/X tasks on A04/A09/A08 repairs.
  - Require Mainline/Side track/Infrastructure classification.
  - Forbid theorem-as-field/source-wrapper progress claims.

Commands run:
  - `./scripts/check.sh` → PASS
  - `ls seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A*.md` → A01--A10 present before A11; A11 added by this task
  - `rg -n "Executive verdict|Verdict:" seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A*.md` → A01--A10 all reported `PARTIAL_BUT_USEFUL`

Scope violations:
  none

Honest caveats:
  - This synthesis relies on audit report conclusions rather than re-auditing every Lean proof body.
  - Optional retrospective and NoGoLog context were not used as primary evidence beyond the reports/checks.
  - Repository branch was `work`, not `main` as stated in the worker prompt.
