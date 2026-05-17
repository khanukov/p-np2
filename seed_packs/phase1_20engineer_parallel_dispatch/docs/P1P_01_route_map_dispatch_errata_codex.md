# P1P-01 — Phase 0 route map and dispatch errata

Task: P1P-01  
Handle: codex  
Scope classification: Infrastructure / governance documentation. Markdown-only.  
Source decision: `PHASE0_COMPLETE_DISPATCH_LIMITED_PHASE1_PLUS` from A11.

## 1. Executive decision

Phase 0 audits are complete: A01 through A10 are present, and A11 synthesized them into the decision `PHASE0_COMPLETE_DISPATCH_LIMITED_PHASE1_PLUS`.

Broad 19-task implementation dispatch is **not authorised**. The previous README/COMMON dispatch language is stale where it suggests that all planned L/B/K/X implementation tasks can run concurrently.

Only limited Phase 1+ tasks are allowed, and they must remain within their explicitly approved scopes. They must not claim lower-bound-source progress, must not create Lean endpoints, and must not instantiate or imply a `ResearchGapWitness`, `VerifiedNPDAGLowerBoundSource`, or `P_ne_NP` result.

Current priority: **P1P-01 and P1P-02 only**.

## 2. Route map

This route map is operator-facing. It is intended to prevent accidental promotion of side tracks, audit artifacts, or infrastructure into claimed progress on the main P-vs-NP target.

### A. Mainline / canonical

| Object | Role | Dispatch meaning |
| --- | --- | --- |
| `ResearchGapWitness` | pnp3 target witness whose hard field is a DAG separation. | Mainline only if the work genuinely reduces or supplies `dagSeparation`; wrappers around it are not progress. |
| `NP_not_subset_PpolyDAG` | The real mathematical gap: an NP-language lower bound against polynomial-size DAG circuits. | Any claimed P-vs-NP progress must ultimately reduce to this, not to a restricted lower-bound class. |
| `VerifiedNPDAGLowerBoundSource` | pnp4 source object representing a verified NP lower bound against `PpolyDAG`. | Canonical pnp4 endpoint; consuming it is infrastructure, producing it non-vacuously would be mainline. |

Operator rule: only work that reduces `SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource` should be called mainline progress. All other route work must be labelled side track, infrastructure, or audit-only.

### B. Conditional wrappers

| Object | Role | Dispatch meaning |
| --- | --- | --- |
| `SearchMCSPMagnificationContract` | Conditional contract intended to turn weak search-MCSP lower bounds into a verified DAG source. | Useful only as a contract boundary until its hard magnification field is proven non-vacuously. |
| `TreeMCSPSearchMagnificationSource` | Tree-MCSP/search target source surface in the magnification frontier. | Conditional; parser or target plumbing does not prove the weak lower bound. |
| `PvsNPBridgeRequirement` | Bridge-requirement surface recording what must be supplied before final claims. | Governance/contract object; must not be treated as supplying the bridge. |

Operator rule: conditional wrappers may clarify obligations, but a wrapper with a field of the hard theorem is not evidence for that theorem.

### C. Restricted side tracks

| Side track | Allowed interpretation | Forbidden interpretation |
| --- | --- | --- |
| `AC0[p]` | Restricted lower-bound formalization or literature-facing infrastructure. | Do not call it unconditional P-vs-NP progress without an explicit `PpolyDAG` / `VerifiedNPDAGLowerBoundSource` bridge. |
| formula | Restricted formula-circuit lower-bound work. | Do not promote formula lower bounds to DAG lower bounds by naming or adapter alone. |
| local-PRG | Conditional/restricted pseudorandomness or locality surfaces. | Do not use local-PRG statements as a source of `VerifiedNPDAGLowerBoundSource` unless a real DAG theorem is present. |
| coin problems | Restricted coin-problem lower-bound or transfer surfaces. | Do not claim a coin-problem exclusion proves an NP-vs-DAG separation. |
| partial-MCSP | Partial-MCSP/formula/locality pipeline and Step-C style infrastructure. | Do not treat support-bound, default-provider, or partial-provider channels as a final lower-bound source. |

Operator rule: these tracks are useful, but they are side tracks unless paired with a genuine bridge to `PpolyDAG` or `VerifiedNPDAGLowerBoundSource`.

### D. Audit / NoGo

| Object | Role | Dispatch meaning |
| --- | --- | --- |
| `NOGO-000005` through `NOGO-000009` | Structured negative evidence and regression anchors for failed or risky route families. | Audit-only; use to prevent repeated mistakes, not as a lower-bound source. |
| `RefutedRoute` / vacuous routes | Quarantined route forms that demonstrate known-bad or vacuous implications. | Never import or reuse as mathematical payload outside audit/test/docs quarantine. |

Operator rule: NoGo and refuted/vacuous material protects the project from false progress. It must not be repackaged as a positive endpoint.

### E. Contract-expansion infrastructure

| Object | Role | Dispatch meaning |
| --- | --- | --- |
| `C_DAG` adapter | Adapter layer around DAG-circuit encodings and contract-expansion targets. | Infrastructure; useful for future proof plumbing, not itself a lower bound. |
| `PrefixExtensionLanguage` | Prefix-extension language surface. | Infrastructure for a future concrete target; not an NP-membership proof by itself. |
| `PrefixExtensionLanguageNP` | Staged NP-membership surface for prefix-extension work. | Must not be completed with placeholder `Prop` fields or no-faking gaps. |
| `PrefixExtensionLanguageRuntime` | Runtime/serialization support for the prefix-extension route. | Needs explicit parser conventions and runtime scope before implementation dispatch. |

Operator rule: contract-expansion work can unblock future formalization, especially around prefix parsing and NP membership, but it does not close the real mathematical gap.

## 3. Dispatch status table

Status values are taken from the A11 decisions and normalized to the allowed vocabulary for this errata.

| Task | Status | Operator-facing decision |
| --- | --- | --- |
| L01 | DOWNGRADE_TO_MARKDOWN | Rewrite as literature/interface alignment for Hirahara search-to-decision context; do not create Lean `Prop := True` skeletons or reduction records untied to current pnp4 interfaces. |
| L02 | DOWNGRADE_TO_MARKDOWN | Rewrite as bounded-arithmetic governance/barrier context; do not create theorem-oracle Lean surfaces. |
| B01 | REWRITE | Rewrite as a concrete route-specific barrier-certificate template or require checked RR conditions; do not package the natural-proofs theorem as an arbitrary field. |
| B02 | CANCEL | Cancel as written because placeholder/trivial oracle and separation/collapse markers would create misleading kernel-checked skeletons without BGS content. |
| B03 | CANCEL | Cancel as written because `∀ O, True`, generic algebraic-extension fields, and trivial theorem markers are placeholder/theorem-as-field work. |
| K01 | REWRITE | Rewrite as manual NoGo certificate support or operator-supplied classification; do not present it as automatic NoGo detection. |
| K02 | APPROVE_LATER | Approve only after governance repair and only as operator-support classification, not automatic gating. |
| X01 | HOLD | Hold until a no-faking design confirms the bridge cannot accept staged `Prop` placeholders and a toy verifier is feasible. |
| X02 | REWRITE | Rewrite after P1P-02 resolves parser conventions for `M(n)`, `tableLen`, serialization, malformed rejection, and runtime scope; do not approve implementation yet. |

## 4. Governance errata

Before the next dispatch, README/COMMON need the following exact governance changes:

1. Replace `E<NN>` with `<TASK_ID>` everywhere in identity, task-file, branch, failure-report, PR-title, PR-template, label, and output-format instructions.
2. Remove the stale “all 19 dispatchable now” / “All tasks are independent and run concurrently” wording.
3. Add A11 as the explicit gate before any Phase 1+, L, B, K, or X wave is opened.
4. Mark B02 and B03 cancelled as written.
5. Mark B01, K01, and X02 rewrite required before any implementation dispatch.
6. Mark X01 held pending no-faking / NP-interface design review.
7. Clarify that current P1P tasks are the only allowed dispatch class, and for the immediate operator window only P1P-01 and P1P-02 should run.
8. Clarify that no implementation may begin without explicit operator authorisation after the A11 gate.
9. Add labels for task class: mainline, restricted side track, infrastructure, audit-only.
10. Require every future lower-bound task to state whether it reduces `SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource`; otherwise it must be labelled side track or infrastructure.
11. Add explicit warning that `BridgeToPpolyDAG.lean` consumes a supplied `VerifiedNPDAGLowerBoundSource`; it does not produce one from AC0[p], formula, local-PRG, coin, or partial-MCSP lower bounds.
12. Add B/K/X gating text: B tasks require concrete witness criteria, K tasks are manual/operator-support unless proven otherwise, and X tasks require parser/runtime/no-faking design.
13. Add a NoGoLog caveat that formal witnesses are audit anchors, some line/status metadata may be stale, and NoGo entries are not lower-bound sources.

## 5. What can run now

Run now:

- P1P-01
- P1P-02

Hold everything else.

## 6. What moves toward P≠NP

P1P-01 does not prove anything. It is a governance and route-map document that reduces dispatch ambiguity.

P1P-02 may unblock future `PrefixExtensionLanguage ∈ NP` work by fixing parser and runtime conventions before implementation. Even then, NP-membership infrastructure would still not be a lower bound.

The real mathematical gap remains `NP_not_subset_PpolyDAG`. Equivalently, pnp4 still needs a non-vacuous `VerifiedNPDAGLowerBoundSource` or the SearchMCSP route still needs a genuine weak lower bound plus a magnification theorem producing that source.

No statement in this errata should be read as a `P≠NP` claim.

## 7. Recommended next operator patch

Yes: after P1P-01 lands, the operator should update README/COMMON in a dedicated governance patch before opening any broader dispatch.

Recommended patch shape:

1. Edit only README/COMMON first, not Lean, JSONL, spec, or NoGoLog.
2. Apply the governance errata from section 4 verbatim or with stricter wording.
3. Replace the stale broad-dispatch status with an A11-gated status.
4. Add the dispatch status table or a shorter equivalent directly into README.
5. Add a short “What can run now” block naming only P1P-01 and P1P-02 for the current window.
6. Require an operator-authored dispatch note before any L/B/K/X implementation task can start.

## Final structured output

Task: P1P-01  
Handle: codex  
Branch: work  
Commit before: 4f39e76d7bc0f4fed22dad883267f40f1e7a6d1b  
Commit after: to be recorded by the landing commit for this report  
Changed files:
- `seed_packs/phase1_20engineer_parallel_dispatch/docs/P1P_01_route_map_dispatch_errata_codex.md`

Outcome: REPORT_LANDED

Dispatch now:
- P1P-01
- P1P-02

Held:
- L01 and L02 as Lean implementation work; downgrade to markdown only.
- B01 until rewritten.
- K01 until rewritten.
- K02 until governance repair.
- X01 pending no-faking / NP-interface design review.
- X02 until P1P-02 parser convention design and rewrite.
- Everything else not explicitly operator-authorised.

Cancelled:
- B02 as written.
- B03 as written.

Governance errata:
- Replace `E<NN>` with `<TASK_ID>`.
- Remove broad “all 19 dispatchable now” wording.
- Add the A11 gate.
- Mark B02/B03 cancelled as written.
- Mark B01/K01/X02 rewrite required.
- Mark X01 held.
- Clarify P1P-only dispatch for the current window.
- Clarify no implementation without operator authorisation.

Commands run:
- `cat AGENTS.md`
- `sed -n '1,240p' RESEARCH_CONSTITUTION.md`
- `sed -n '1,260p' seed_packs/phase1_20engineer_parallel_dispatch/README.md`
- `sed -n '1,260p' seed_packs/phase1_20engineer_parallel_dispatch/COMMON_WORKER_INSTRUCTIONS.md`
- `sed -n '1,260p' seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A11_phase0_synthesis_codex.md`
- `for f in seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A{01,02,03,04,05,06,07,08,09,10}_*.md; do sed -n '1,220p' "$f"; done`
- `rg -n "^## (7|8|9|10)\\.|L01|B02|X01|P1P" seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A11_phase0_synthesis_codex.md seed_packs/phase1_20engineer_parallel_dispatch/README.md seed_packs/phase1_20engineer_parallel_dispatch/COMMON_WORKER_INSTRUCTIONS.md`
- `rg -n "E<NN>|19|dispatch-able|All tasks|authori|Branch|PR|TASK" seed_packs/phase1_20engineer_parallel_dispatch/COMMON_WORKER_INSTRUCTIONS.md seed_packs/phase1_20engineer_parallel_dispatch/README.md`
- `./scripts/check.sh`

Scope violations:
- none
