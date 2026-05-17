# A11: Phase 0 synthesis and dispatch decision

Task: A11  
Engineer handle: codex  
Branch: work (worker prompt requested `main`; repository checkout was `work`)  
Commit before: fe03a5751cf3282c15fc2e45645a5fb66386551a  
Commit after: `recorded in final response after commit`

Files added/modified:
  - `seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A11_phase0_synthesis_codex.md`

Outcome: SYNTHESIS_LANDED

## 1. Executive verdict

**PHASE0_COMPLETE_DISPATCH_LIMITED_PHASE1_PLUS**

All A01-A10 audit reports are present, and they agree on the high-level state:
the repository contains substantial kernel-checked infrastructure, but almost
all lower-bound routes that look close to an endpoint are conditional wrappers,
restricted side tracks, audit-only refutations, or typed contracts whose hard
mathematical payload is still absent. Phase 1+ can dispatch a small number of
infrastructure/governance tasks, but not a broad implementation wave and not a
new P-vs-NP endpoint attempt.

The operator should treat this as a **limited-dispatch gate**:

- Dispatch only tasks that reduce confusion, expose already-existing no-go or
  adapter surfaces, or implement narrowly scoped parser/interface hygiene.
- Hold tasks that package theorem-sized assumptions as fields and call that a
  barrier or lower-bound theorem.
- Cancel or rewrite tasks that claim mainline progress without reducing
  `SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource`.

## 2. Audit coverage table

| Audit | Present? | Executive verdict | Main area | Confidence | Main caveat |
| --- | --- | --- | --- | --- | --- |
| A01 | yes | PARTIAL_BUT_USEFUL | pnp3 Magnification partial-MCSP locality/provider pipeline | Medium-high | Strong conditional formula/real endpoints exist, but no closed locality provider, no `NP_strict` partial-MCSP proof in scope, and no `PpolyDAG` bridge. |
| A02 | yes | PARTIAL_BUT_USEFUL | pnp3 FinalResult / ResearchGapWitness wrappers | High | Final pipeline is complete only modulo an honest `ResearchGapWitness`; audit/refuted routes remain reachable for compatibility. |
| A03 | yes | PARTIAL_BUT_USEFUL | pnp3 AC0/asymptotic/bridge files | Medium-high | AC0/formula bridges are restricted side-track or conditional; semantic/support-bounds providers cannot be promoted to DAG sources. |
| A04 | yes | PARTIAL_BUT_USEFUL | pnp3 barrier interfaces | Medium | Barrier witness structures are useful, but `BarrierBypassPackage` is a Prop-field package and not a concrete bypass theorem. |
| A05 | yes | PARTIAL_BUT_USEFUL | pnp3 LowerBounds / anti-checker / DAG producer files | Medium | Several lower-bound-looking endpoints are enriched-solver or provider conditional; DAGStableRestrictionProducer needs dependency-closure audit before reuse. |
| A06 | yes | PARTIAL_BUT_USEFUL | pnp3 Models / Complexity / MCSP model layer | Medium-high | Partial-MCSP decision models exist, but concrete NP verifier/search relation and pnp4 search-MCSP alignment are missing. |
| A07 | yes | PARTIAL_BUT_USEFUL | pnp4 AlgorithmsToLowerBounds | Medium-high | AC0[p], local-PRG, coin, formula surfaces are restricted/contracts; no adapter turns them into `VerifiedNPDAGLowerBoundSource`. |
| A08 | yes | PARTIAL_BUT_USEFUL | pnp4 Frontier / ContractExpansion | High | Mainline interfaces are honest but staged; parser/runtime/codec fields and the actual weak search lower bound/magnification theorem are absent. |
| A09 | yes | PARTIAL_BUT_USEFUL | NoGoLog formal witnesses | Medium-high | Most NoGo entries have formal witnesses, but NOGO-000003 is `needs_review` and some JSONL anchors/wording need repair. |
| A10 | yes | PARTIAL_BUT_USEFUL | Partial/legacy markers and hidden-payload scan | Medium | No active axiom declarations found; risks are known support/default wrappers and one `True -- placeholder` invariant. |

## 3. Repo state summary

### pnp3 Magnification partials

The partial-MCSP magnification area has a real typed skeleton: partial solver
interfaces, locality-lift facades, Step-C/pipeline statements, conditional
formula/real separation wrappers, and many adapters among certificate/provider
packages. The useful kernel-checked content is mostly dataflow from explicit
premises to restricted formula/real conclusions. The hard pieces remain as
provider fields or premises: structured locality providers, semantic provider
packages, provenance-safe support bounds, and `NP_strict` membership for the
partial-MCSP language. The old support-bound route is explicitly unsafe without
provenance restrictions.

### pnp3 FinalResult pipeline

The final-result layer correctly separates a final target wrapper from the
source obligation: `ResearchGapWitness` / `dagSeparation` is still the payload.
The pipeline can turn a genuine `NP_not_subset_PpolyDAG`-strength witness into
final statements, but it does not construct that witness. Refuted and audit
routes are present for regression/governance and must not be mistaken for
candidate progress.

### AC0 / asymptotic / bridge files

The AC0/asymptotic bridge files contain useful conditional adapters and no-go
surfaces, including scenario-budget and support-cardinality limitations. They
support a restricted lower-bound side track, not a mainline P-vs-NP route,
unless a future task supplies a real `PpolyDAG`/`VerifiedNPDAGLowerBoundSource`
bridge.

### Barrier files

Barrier files define typed natural-proofs, relativization, and algebrization
witness shapes and audit wrappers. They do not contain concrete oracle-world or
algebraic-oracle constructions that prove a route bypasses the barriers. The
most dangerous pattern is treating an arbitrary `Prop`-field package as a
barrier theorem.

### LowerBounds

LowerBounds contains significant kernel-checked anti-checker, singleton-density,
asymptotic/DAG, and support-cardinality infrastructure. However, many theorem
surfaces are conditional on enriched solver data, provider/source classes, or
already-known risky support predicates. The current lower-bound files do not
supply a non-vacuous `NP_not_subset_PpolyDAG` source.

### Models / Complexity

The pnp3 model layer provides circuit, formula, DAG, straight-line, partial
truth-table, and partial-MCSP definitions plus complexity interfaces. It is
usable infrastructure. It does not yet include a concrete partial-MCSP verifier
construction, a search-MCSP relation aligned with pnp4, or a compact guide to
which circuit model should be used by which route.

### pnp4 AlgorithmsToLowerBounds

The pnp4 algorithms-to-lower-bounds area has rich typed surfaces for AC0[p],
coin/local-PRG, formula routes, and a bridge file that mentions
`VerifiedNPDAGLowerBoundSource`. The current artifacts are mostly contracts and
conditional implications. The CKLM-style formula envelope is currently too weak
for the advertised global formula growth condition, and restricted lower-bound
sources do not become DAG lower bounds automatically.

### pnp4 Frontier / ContractExpansion

The Frontier layer is the cleanest mainline scaffold. It exposes
`SearchMCSPWeakLowerBound`, `VerifiedNPDAGLowerBoundSource`, compression/search
problem contracts, and `SearchMCSPMagnificationContract`-style staging. It is
honest because the hard field remains explicit. ContractExpansion has useful
prefix-language/parser/runtime shapes but leaves parser implementation, codec
serialization, NP membership, and machine-cost bridge work mostly staged.

### NoGoLog

The NoGoLog is valuable and mostly formalized. NOGO-000001, 000002, and
000004-000009 have formal witnesses; NOGO-000003 remains `needs_review`. A09
found stale or imprecise JSONL anchors/wording, and K-style automation should
not pretend that a JSONL ledger plus manual certificates is automatic semantic
NoGo detection.

### Legacy / partial markers

A10 found no active Lean `axiom` declarations and no hidden new source theorem.
There are many `_Partial`, audit, `default*`, `noncomputable`, and placeholder
markers. Most are acceptable if they remain visibly staged, but they are a
misuse risk for future workers and should be guarded by naming, docs, tests,
and dispatch wording.

## 4. What is actually kernel-checked?

### A. Canonical useful artifacts

- Trust-root complexity interfaces and final target types in pnp3.
- Partial-MCSP language/model definitions and circuit-model infrastructure.
- Locality lift/adapters that map explicit provider assumptions to explicit
  local/general solver conclusions.
- pnp3 formula/real conditional endpoints from partial-MCSP pipeline hypotheses.
- pnp4 Frontier source interfaces: weak search-MCSP, verified DAG lower-bound
  sources, and conditional final bridge statements.
- Surface tests and axiom audits that import many public declarations.

### B. Conditional wrappers

- `ResearchGapWitness -> P_ne_NP`-style final wrappers.
- `VerifiedNPDAGLowerBoundSource -> NP_not_subset_PpolyDAG` and related pnp4
  bridges.
- Partial-MCSP formula/real endpoints under explicit locality/provider and
  `NP_strict` hypotheses.
- `SearchMCSPMagnificationContract` / compression-magnification wrappers whose
  central hard implication is a field.
- Barrier wrappers that consume typed bypass witnesses or package assumptions.

### C. Audit-only theorems

- Refuted route regression theorems under `pnp3/Magnification/AuditRoutes/`,
  `pnp3/RefutedPredicates/`, tests, and barrier audit modules.
- NoGo formal witnesses for fixed-parameter probes, log-width/adversarial
  truth-table routes, support-cardinality barriers, and provenance-filter V2
  attacks.
- Smoke tests checking that quarantined theorem statements remain buildable.

### D. Refuted/vacuous route witnesses

- Support-bound routes that allow truth-table or singleton hardwiring.
- Fixed-slice or support-cardinality predicates that are too broad.
- Formula/real final wrappers intentionally named or documented as refuted or
  audit-only.
- `via_ex_falso` / `RefutedRoute` style artifacts that prove only governance
  regressions, not mathematical progress.

### E. Adapter/infrastructure theorems

- Circuit/model coercions and simple correctness field projections.
- Locality provider/certificate conversion lemmas.
- ContractExpansion parser/runtime shell lemmas where obligations remain fields.
- pnp4 surface-test wrappers and `#print axioms` audit entries.

## 5. What is staged / placeholder / wrapper?

Major staged patterns across A01-A10:

- `ResearchGapWitness` wrappers: final statements are available only after the
  `dagSeparation : NP_not_subset_PpolyDAG` payload is honestly supplied.
- `VerifiedNPDAGLowerBoundSource` wrappers: pnp4 can package a DAG lower-bound
  source, but the source itself is not constructed by side-track lower bounds.
- `SearchMCSPMagnificationContract`: central magnification is a contract field,
  not a proved theorem from current MCSP artifacts.
- Prop-field budget records: parser/runtime/codec/lower-bound/barrier packages
  often contain `Prop` fields that state hard work rather than performing it.
- Partial/legacy routes: `_Partial` files are active infrastructure, but old
  support-bound/weak/fixed-slice paths remain dangerous without quarantine.
- Refuted support-bounds: support-cardinality and hardwiring NoGo results block
  naive support-bound reuse.
- `FinalPayloadProvider` / typeclass channels: final payloads must not be hidden
  behind instances or provider classes; final wrappers must keep assumptions
  explicit.
- Noncomputable default payloads: `Nonempty` plus `Classical.choice` default
  providers are wrapper risk and should not become global instances.
- `NP_TM`/membership abbreviations: several membership surfaces are aliases or
  staged specs rather than concrete verifier implementations.
- `PDT.WellFormed := True` and a few proof-local `True` placeholders: mostly not
  endpoint-critical, but they demonstrate why implementation claims need local
  self-attack.

## 6. What is mathematically missing?

### Gap 1: Honest `NP_not_subset_PpolyDAG`

- **Where it appears:** pnp3 final target, pnp4 `VerifiedNPDAGLowerBoundSource`,
  `BridgeToPpolyDAG`, and Frontier final bridges.
- **Why it is not just engineering:** No current audited theorem supplies an NP
  language and proves every polynomial-size DAG family fails to decide it. This
  is the core lower-bound problem.
- **What would be needed:** A non-vacuous NP-language lower bound against
  `PpolyDAG`, with no refuted support predicate, no hidden typeclass payload,
  and clean dependency closure.
- **Current Phase 1 task coverage:** None. Existing tasks mostly stage surfaces,
  barriers, parser work, or side-track lower bounds.

### Gap 2: Search-MCSP weak lower bound and magnification theorem

- **Where it appears:** pnp4 Frontier search/compression contracts,
  `SearchMCSPWeakLowerBound`, `SearchMCSPMagnificationContract`, and
  ContractExpansion.
- **Why it is not just engineering:** The missing theorem is not a parser or API
  fact; it is a lower-bound/magnification claim turning weak search hardness
  into a verified DAG lower-bound source.
- **What would be needed:** A concrete target, a proof of no bounded solver for
  that target, and a proved magnification bridge to `VerifiedNPDAGLowerBoundSource`.
- **Current Phase 1 task coverage:** X02 may help parser infrastructure only;
  no current task proves `target.noBoundedSolver` or magnification.

### Gap 3: Formula/AC0/restricted lower bounds to `PpolyDAG`

- **Where it appears:** pnp3 AC0 bridge files, pnp3 partial-MCSP formula/real
  endpoints, pnp4 AC0[p]/formula/local-PRG contracts.
- **Why it is not just engineering:** A formula or restricted AC0 lower bound is
  weaker/different than a DAG lower bound. Converting it requires a real bridge,
  not a rename.
- **What would be needed:** A theorem showing the restricted lower-bound source
  implies `VerifiedNPDAGLowerBoundSource` or directly yields
  `NP_not_subset_PpolyDAG`, with all model-size losses accounted for.
- **Current Phase 1 task coverage:** None. L01 may describe search-to-decision;
  A07/A08 show no present bridge.

### Gap 4: Non-vacuous locality/support/provenance route

- **Where it appears:** `LocalityProvider_Partial`, support-bound contracts,
  NoGoLog entries, fixed-parameter probes, provenance-filter modules.
- **Why it is not just engineering:** Naive support/provenance predicates are
  refuted by hardwiring or support-cardinality attacks. Avoiding those attacks
  requires a genuinely narrower mathematical invariant.
- **What would be needed:** A provenance/locality predicate proven to exclude
  truth-table/singleton hardwiring while still strong enough to drive the lower
  bound.
- **Current Phase 1 task coverage:** No. Recommended work is audit/quarantine,
  not proof of a new invariant.

### Gap 5: Concrete NP/verifier/search model alignment

- **Where it appears:** pnp3 partial-MCSP `NP_TM` abbreviations, X01/X02,
  ContractExpansion prefix language, and pnp4 tree-MCSP target.
- **Why it is not just engineering:** A concrete verifier can be engineering,
  but proving it matches the exact lower-bound/search target and preserves
  length/threshold conventions is a formal mathematical specification problem.
- **What would be needed:** Concrete parser/codec/verifier plus equivalence to
  the intended MCSP/search relation and polynomial runtime semantics.
- **Current Phase 1 task coverage:** X01/X02 partially address infrastructure;
  they do not address lower-bound source progress.

### Gap 6: Real barrier bypass certificates

- **Where it appears:** pnp3 barrier interfaces and planned B01-B03.
- **Why it is not just engineering:** Showing a route escapes natural proofs,
  relativization, or algebrization requires substantive route-specific witness
  worlds/properties, not just filling fields.
- **What would be needed:** Concrete RR constructivity/largeness/usefulness
  failure, two oracle worlds for relativization, and two algebraic-oracle worlds
  for algebrization, tied to the exact candidate route.
- **Current Phase 1 task coverage:** B01-B03 as written mostly build surfaces;
  they should be rewritten or downgraded unless they demand concrete witnesses.

## 7. What is engineering / formalization work?

| Task title | Exact files | Dependency | Expected value | Risk | Dispatch? |
| --- | --- | --- | --- | --- | --- |
| Route-status synthesis note for pnp3/pnp4 MCSP model alignment | New markdown under `seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/` or operator-chosen docs | A01, A06, A08 | Prevents duplicate X/MCSP work and clarifies partial vs search MCSP | Low | **now** |
| Quarantine/naming pass for support-bound wrappers | `pnp3/Magnification/LocalityProvider_Partial.lean`, tests only if names touched | A01, A02, A09, A10 | Reduces accidental reuse of refuted routes | Medium | **after repair/spec** |
| NoGoLog anchor/wording repair | `outputs/nogolog.jsonl` only | A09 | Aligns ledger with current theorem lines and scope | Low-medium governance risk | **after operator approval** |
| Dedicated smoke tests for NOGO-000008/000009 | New `pnp3/Tests/AuditRoutes_*_Smoke.lean`, maybe `lakefile.lean` | A09 | Uniform regression coverage | Medium | **later** |
| Public no-go surface for scenario-budget insufficiency | Existing pnp3 tests/docs, possibly `AC0AtlasBridge.lean` only if operator permits | A03 | Makes a known blocker visible | Low-medium | **now if markdown/test-only** |
| Dependency-closure audit for `DAGStableRestrictionProducer.lean` | New markdown audit report | A05 | Avoids hidden hard-payload imports by future candidates | Low repo risk; high audit time | **now/later** |
| ContractExpansion parser implementation | `pnp4/Pnp4/Frontier/ContractExpansion/TreeMCSPParserImpl.lean` only | A08; X02 spec repair | Removes staged parser shell for one target | Medium-high | **after X02 rewrite** |
| X01 verifier bridge anti-faking repair | X01 task spec and maybe new modules only after spec fixed | A06, A08 | Could create useful verifier interface if not merely NP wrapper | Medium | **after repair** |
| Barrier task rewrite into markdown/design certificates | B01-B03 task docs or new markdown reports | A04 | Prevents theorem-as-field false confidence | Low | **now as markdown rewrite, not Lean barrier theorem wave** |

## 8. Planned Phase 2-5 task review

| Task | Decision | Explanation |
| --- | --- | --- |
| L01 | **DOWNGRADE_TO_MARKDOWN** | The proposed deliverable is a typed surface with `correctness : Prop` and `witness_marker : Prop := True`. That is useful literature mapping, but as Lean it risks adding a theorem-shaped wrapper around an unproved multi-month reduction. Approve only as a literature/route-spec report unless rewritten to avoid implying proof. |
| L02 | **DOWNGRADE_TO_MARKDOWN** | The bounded-arithmetic metatheorems are explicitly multi-year; the current task mainly packages `proves : Prop -> Prop` and an unprovability field. Good as a bibliography/interface note, not a kernel-checked theorem claim. |
| B01 | **REWRITE_SCOPE** | Do not approve if it only packages RR barrier theorem assumptions as fields. It may proceed only if rewritten to produce concrete route-specific witness obligations or a markdown design explaining exactly what remains unproved. |
| B02 | **REWRITE_SCOPE** | Concrete oracle worlds are not present. A theorem `BGS_no_relativizing_proof (B : BGSRelativizationBarrier)` is just a wrapper if `B` contains the hard facts. Require actual oracle semantics/witnesses or downgrade to markdown. |
| B03 | **DOWNGRADE_TO_MARKDOWN** | The listed theorems are trivial markers. Algebrization semantics and worlds are missing. A markdown barrier map is useful; a Lean marker theorem is not. |
| K01 | **REWRITE_SCOPE** | Do not approve as automatic NoGo detection. It can be rewritten as an operator-assist library that checks explicit, manually supplied certificate fields and reports applicability, with NOGO-000003 excluded/needs-review. |
| K02 | **APPROVE_AFTER_REPAIR** | A pre-dispatch classifier is useful if it remains decision support and not auto-red-light production. It should depend on repaired A09 anchors and A11 gating language. |
| X01 | **HOLD_PENDING_DEPENDENCY** | A verifier bridge can be useful, but A06/A08 warn that NP membership aliases and staged verifier specs are easy to fake. Hold until anti-faking criteria, concrete TM choice, and length/runtime conventions are specified. |
| X02 | **HOLD_PENDING_DEPENDENCY** | Parser implementation is plausible infrastructure, but A08 identifies unresolved `M(n)`/length, codec, and runtime-field issues. Rewrite the scope around one concrete encoding and forbid claims of `PrefixExtensionLanguage_in_NP`. |

## 9. Phase 1+ dispatch list

At most five initial tasks should be opened. These are infrastructure/governance
only and should not be reported as source theorem progress.

### P1P-01 — MCSP route-alignment map

- **Title:** Align pnp3 partial-MCSP, pnp4 search-MCSP, and ContractExpansion targets.
- **Exact scope:** Markdown route map with definitions, non-equivalences, and
  required adapters.
- **Files allowed:** One new markdown file under
  `seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/` or a
  dedicated operator-selected route-status docs path.
- **Forbidden scope:** Lean edits, endpoint work, `ResearchGapWitness`,
  `VerifiedNPDAGLowerBoundSource`, `P_ne_NP`.
- **Expected deliverable:** A table mapping pnp3 partial decision/promise
  surfaces to pnp4 search/compression targets and listing missing theorems.
- **Estimated time:** 0.5-1 day.
- **Prerequisite audits:** A01, A06, A08.
- **Why not duplicate:** No A01-A10 report is a single cross-version route map.

### P1P-02 — NoGoLog governance repair

- **Title:** Repair stale NoGoLog anchors and needs-review wording.
- **Exact scope:** Update line anchors/wording only where A09 identified drift.
- **Files allowed:** `outputs/nogolog.jsonl`; optional governance changelog if
  operator requires.
- **Forbidden scope:** New entries, status promotion, theorem edits, endpoint work.
- **Expected deliverable:** JSONL-only PR with `./scripts/check.sh` pass.
- **Estimated time:** 1-2 hours.
- **Prerequisite audits:** A09.
- **Why not duplicate:** A09 was markdown-only and could not perform the repair.

### P1P-03 — Support-bound quarantine decision and labels

- **Title:** Make refuted/support-bound route status harder to misuse.
- **Exact scope:** Operator-chosen rename/doc/test pass for support-bound wrappers.
- **Files allowed:** `pnp3/Magnification/LocalityProvider_Partial.lean`, relevant
  pnp3 tests/audits only if public names are changed; or markdown-only decision
  record if renaming is too disruptive.
- **Forbidden scope:** New lower-bound theorem, new provider construction,
  weakening route-policy guards, trust-root edits.
- **Expected deliverable:** Explicit audit/refuted labeling and passing guards.
- **Estimated time:** 1-2 days.
- **Prerequisite audits:** A01, A02, A09, A10.
- **Why not duplicate:** Audits identify the risk but do not change visible labels.

### P1P-04 — DAGStableRestrictionProducer dependency-closure audit

- **Title:** Audit hidden payload risk before candidate reuse of DAG provider/source endpoints.
- **Exact scope:** Markdown-only dependency map of theorem/provider classes and
  imports in `pnp3/LowerBounds/DAGStableRestrictionProducer.lean`.
- **Files allowed:** One new audit report under the seed pack audit/follow-up area.
- **Forbidden scope:** Lean edits, endpoint construction, proof repair.
- **Expected deliverable:** Classification of which declarations are safe adapters,
  wrappers, or hard-payload assumptions.
- **Estimated time:** 2-4 days.
- **Prerequisite audits:** A05, A10.
- **Why not duplicate:** A05 explicitly says this file is too large/provider-heavy
  for casual reuse and needs a dedicated closure audit.

### P1P-05 — ContractExpansion concrete parser scope rewrite

- **Title:** Rewrite X02 into a one-encoding parser-only infrastructure task.
- **Exact scope:** Update task text or create a replacement prompt specifying one
  concrete encoding, exact `M(n)`/table length convention, and no NP/source claim.
- **Files allowed:** Seed-pack task markdown only in the repair PR; later Lean task
  may touch only `TreeMCSPParserImpl.lean` after approval.
- **Forbidden scope:** Implement parser in the repair task; `PrefixExtensionLanguage_in_NP`;
  weak lower-bound or magnification claims.
- **Expected deliverable:** Dispatchable X02-repair prompt.
- **Estimated time:** 0.5 day for rewrite; 1-2 weeks later for implementation.
- **Prerequisite audits:** A08, A10.
- **Why not duplicate:** The existing X02 prompt lacks the length/codec specificity
  A08 says is needed.

## 10. Tasks to cancel / hold

- **Cancel or downgrade L01/L02 as Lean theorem tasks** unless rewritten as honest
  literature/design reports.
- **Hold B01-B03** until they require concrete barrier witness semantics rather
  than theorem-as-field packaging; B03 should be markdown-only for now.
- **Hold K01** until the prompt stops claiming automatic NoGo detection and
  excludes `needs_review` entries from completeness claims.
- **Hold K02** until A09 governance repair and A11 gate language are incorporated.
- **Hold X01** until concrete verifier/runtime/anti-faking conventions are fixed.
- **Hold X02** until the `M(n)`/table length/codec convention is specified.
- **Cancel any X01 variant** that is just an `NP_TM` wrapper or accepts staged
  `Prop` placeholders as verifier correctness.
- **Cancel any B/K/X/L variant** that introduces `ResearchGapWitness`, `gap_from`,
  `SourceTheorem`, `VerifiedNPDAGLowerBoundSource`, or `P_ne_NP` as a wrapper
  without a new source theorem.

## 11. Governance repairs needed before next wave

- Add A11 as an explicit dispatch gate in README/COMMON before any Phase 1+ / B /
  K / X / L work is authorized.
- Fix README wording that says all 19 tasks are dispatchable now; A01-A10 show
  several need rewrite, downgrade, or hold.
- Fix branch naming mismatch: prompts may say `main`, but worker checkout may be
  task/work branch; future prompts should say expected base and branch action.
- Resolve the COMMON `E<NN>` Phase-A template mismatch with actual L/B/K/X/A task IDs.
- Add B/K/X gating language: B tasks need concrete witness semantics; K tasks are
  operator-assist, not automatic semantic NoGo detection; X tasks are
  infrastructure, not source theorem work.
- Rename or retitle tasks whose names imply theorem proof while deliverable is a
  `Prop`-field surface.
- Add explicit “no theorem-as-field progress” language to task prompts.
- Reference A09/NOGO status in support/provenance tasks, especially NOGO-000003
  `needs_review` and support-cardinality refutations.
- Require every task review to classify work as mainline, side track, or
  infrastructure under AGENTS/constitution policy.

## 12. Final operator decision

Dispatch now:
  - P1P-01 MCSP route-alignment map.
  - P1P-04 DAGStableRestrictionProducer dependency-closure audit.
  - Markdown/spec rewrites for L01, L02, B01-B03, K01, X01, X02; no Lean source
    implementation from those prompts yet.

Hold:
  - K02 until A09/A11 governance repairs land.
  - X01 until anti-faking/runtime/verifier conventions are concrete.
  - X02 until codec and `M(n)`/length conventions are concrete.
  - Any pnp4 AC0[p]/formula bridge to `VerifiedNPDAGLowerBoundSource` until a
    real `PpolyDAG` bridge theorem is specified.

Cancel:
  - Any task that packages `ResearchGapWitness`, `VerifiedNPDAGLowerBoundSource`,
    or barrier theorems as fields and reports source progress.
  - Any task that promotes refuted support-bound or fixed-slice routes.
  - Any task that claims P-vs-NP progress from restricted AC0/formula/local-PRG
    lower bounds without an explicit DAG bridge.

Next:
  - Operator repairs seed-pack governance wording.
  - Operator opens at most five limited Phase 1+ tasks from section 9.
  - After those land, re-evaluate X01/X02 and K02 with concrete scopes.

## Output template block

Task: A11  
Engineer handle: codex  
Branch: work (prompt requested `main`)  
Commit before: fe03a5751cf3282c15fc2e45645a5fb66386551a  
Commit after: `recorded in final response after commit`

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
  - P1P-01 MCSP route-alignment map
  - P1P-04 DAGStableRestrictionProducer dependency-closure audit
  - Markdown/spec rewrites only for L/B/K/X tasks

Held tasks:
  - K02
  - X01
  - X02
  - all AC0[p]/formula-to-DAG bridge implementation claims

Cancelled / rewrite required:
  - L01 Lean theorem-surface version (downgrade to markdown)
  - L02 Lean theorem-surface version (downgrade to markdown)
  - B01/B02/B03 as theorem-as-field barrier tasks
  - K01 automatic NoGo checker framing
  - any refuted support-bound promotion

Top 3 mathematical gaps:
  1. Honest `NP_not_subset_PpolyDAG` / `VerifiedNPDAGLowerBoundSource`.
  2. Search-MCSP weak lower bound plus magnification theorem.
  3. Non-vacuous bridge from restricted AC0/formula/locality lower bounds to DAG lower bounds.

Top 3 engineering tasks:
  1. MCSP route-alignment map.
  2. NoGoLog anchor/wording repair.
  3. Support-bound quarantine/labeling pass.

Governance repairs:
  - Add A11 gate.
  - Remove or qualify “all 19 dispatchable now”.
  - Fix COMMON `E<NN>` mismatch.
  - Add B/K/X gating and theorem-as-field warnings.
  - Clarify branch naming/base expectations.

Commands run:
  - `./scripts/check.sh` -> PASS; all checks passed (pre-existing Lean warnings emitted).
  - `ls seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A*.md` -> A01-A10 plus A11 present after report creation.
  - `rg -n "Executive verdict|Verdict:" seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A*.md` -> A01-A10 all show executive verdict sections / `PARTIAL_BUT_USEFUL`; A11 added this verdict.
  - Optional `outputs/nogolog.jsonl` parse -> 9 entries; NOGO-000003 is `needs_review`, others have formal witnesses.

Scope violations:
  none

Honest caveats:
  - This synthesis relies on A01-A10 report claims plus targeted task/NoGoLog inspection; it does not re-audit every Lean proof body.
  - Branch was `work`, not `main`, despite the worker prompt.
  - Section 9 proposes follow-up tasks; this A11 task itself made no Lean, JSONL, source, spec, known_guards, trust-root, or NoGoLog edits.
