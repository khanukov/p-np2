# P1P-01 — Phase 0 route map and dispatch errata

Task: P1P-01  
Handle: codex  
Branch: main  
Scope classification: Infrastructure / governance errata proposal. Markdown-only.  
Source decision: A11 verdict `PHASE0_COMPLETE_DISPATCH_LIMITED_PHASE1_PLUS`.

## 1. Executive decision

- Phase 0 audits are complete: A01 through A10 exist, and A11 synthesizes their results.
- Broad 19-task implementation dispatch is **not authorised**.
- Only limited Phase 1+ tasks are allowed.
- Current priority: **P1P-01 and P1P-02 only**.
- This document is an errata proposal and route map. It does not edit `README.md`, `COMMON_WORKER_INSTRUCTIONS.md`, Lean sources, JSONL ledgers, specs, or NoGo logs.

## 2. Route map

This map is operator-facing: it classifies route objects by how they should be treated during dispatch. It is deliberately conservative and follows the Research Constitution target: the real project gap is an honest inhabitant of `NP_not_subset_PpolyDAG`, ultimately usable through `ResearchGapWitness.dagSeparation`.

### A. Mainline / canonical

These are the canonical target objects or direct mainline obligations. Work should be described as P-vs-NP mainline progress only if it honestly reduces one of these obligations or produces a verified bridge to them.

| Object | Route role | Dispatch interpretation |
| --- | --- | --- |
| `ResearchGapWitness` | Final witness package whose `dagSeparation` field supplies the frozen target. | Do not instantiate or advertise unless `NP_not_subset_PpolyDAG` is honestly inhabited. |
| `NP_not_subset_PpolyDAG` | Frozen mathematical gap for the repository target. | This is the real mathematical lower-bound gap. |
| `VerifiedNPDAGLowerBoundSource` | pnp4 source object with NP-language lower-bound strength against `PpolyDAG`. | Mainline source obligation. Supplying this is meaningful only when non-vacuous and not imported from restricted side tracks without a DAG bridge. |

### B. Conditional wrappers

These wrappers are useful only as contracts, adapters, or requirements around the mainline gap. They must not be reported as solved lower bounds by themselves.

| Object | Route role | Dispatch interpretation |
| --- | --- | --- |
| `SearchMCSPMagnificationContract` | Conditional search-MCSP magnification contract. | Can organize future mainline work, but still needs the missing weak lower bound and verified DAG source path. |
| `TreeMCSPSearchMagnificationSource` | Tree-MCSP/search magnification source interface. | Useful conditional interface; not a proof of the endpoint. |
| `PvsNPBridgeRequirement` | Requirement wrapper for bridge prerequisites. | Governance/contract object; it records requirements rather than proving them. |

### C. Restricted side tracks

These routes may be valuable formalization tracks, but they are side tracks for `P != NP` unless they include an explicit bridge to `PpolyDAG` or `VerifiedNPDAGLowerBoundSource`.

| Side track | Dispatch interpretation |
| --- | --- |
| `AC0[p]` | Restricted lower-bound formalization; not unconditional P-vs-NP progress without a DAG bridge. |
| formula | Formula lower-bound work is not enough for the frozen DAG target unless bridged explicitly. |
| local-PRG | Restricted/local consequence; do not promote to `PpolyDAG` separation without a real bridge. |
| coin problems | Useful restricted lower-bound context; not a mainline endpoint. |
| partial-MCSP | Conditional/restricted pipeline; must remain labelled side-track unless it reaches `VerifiedNPDAGLowerBoundSource`. |

### D. Audit / NoGo

These entries are audit artifacts. They are valuable for preventing repeated mistakes but must never be used as candidate payloads or endpoint progress.

| Object | Dispatch interpretation |
| --- | --- |
| `NOGO-000005` through `NOGO-000009` | NoGo audit knowledge; use for route hygiene and operator review, not final payload construction. |
| `RefutedRoute` / vacuous routes | Quarantined audit routes. They may document failure modes but are not mathematical progress. |

### E. Contract-expansion infrastructure

These are infrastructure objects for future parser/runtime/NP-interface work. They can unblock future engineering, but do not prove the lower bound.

| Object | Route role | Dispatch interpretation |
| --- | --- | --- |
| `C_DAG` adapter | Adapter layer for DAG-circuit conventions. | Infrastructure only unless tied to a verified lower-bound source. |
| `PrefixExtensionLanguage` | Prefix-extension language definition surface. | Potentially useful for contract expansion; not itself a lower bound. |
| `PrefixExtensionLanguageNP` | Intended NP-membership surface for prefix-extension language. | P1P-02 may help unblock this, but no implementation should proceed without operator authorization. |
| `PrefixExtensionLanguageRuntime` | Runtime/complexity convention surface. | Requires parser and runtime convention design before Lean implementation. |

## 3. Dispatch status table

Every planned non-audit task is blocked from broad dispatch. The statuses below follow the A11 decisions, normalized to the allowed operator status vocabulary for this errata.

| Task | Status | A11-grounded decision note |
| --- | --- | --- |
| L01 | `DOWNGRADE_TO_MARKDOWN` | Do not create Lean skeletons with `Prop := True` markers. Recast as literature/search-to-decision design context only. |
| L02 | `DOWNGRADE_TO_MARKDOWN` | Do not package bounded-arithmetic metatheorems as theorem-oracle fields. Recast as governance/barrier context only. |
| B01 | `REWRITE` | Rewrite as concrete Razborov-Rudich condition work or a markdown barrier-certificate template; theorem-as-field packaging is not approved. |
| B02 | `CANCEL` | Cancel as written because placeholder/trivial oracle predicates would create misleading skeletons without BGS content. |
| B03 | `CANCEL` | Cancel as written because trivial algebraic-extension markers and `∀ O, True`-style surfaces are placeholder work. |
| K01 | `REWRITE` | Rewrite as manual NoGo certificate support or operator-supplied classification schema; do not claim automatic NoGo detection. |
| K02 | `APPROVE_LATER` | Potentially useful only after governance repair, and only as manual/operator-support classification with no automatic gating claims. |
| X01 | `HOLD` | Hold until no-faking and NP-interface design review confirms the bridge cannot accept staged `Prop` placeholders. |
| X02 | `REWRITE` | Rewrite after parser conventions resolve `M(n)`, `tableLen`, serialization, malformed rejection, and runtime scope. |

## 4. Governance errata

Before the next dispatch wave, update `README.md` and `COMMON_WORKER_INSTRUCTIONS.md` to remove stale or misleading instructions. Exact changes needed:

1. Replace every generic `E<NN>` task identity placeholder with `<TASK_ID>` or another neutral token that covers A/L/B/K/X/P1P task IDs.
2. Remove or replace wording that says all 19 tasks are independent, concurrent, or dispatchable now, including “All 19 tasks dispatch-able NOW.”
3. Add an explicit A11 gate: no Phase 1+ / L / B / K / X implementation wave may start until A11 decisions are reflected in dispatch docs and operator authorization is explicit.
4. Mark `B02` and `B03` cancelled as written.
5. Mark `B01`, `K01`, and `X02` rewrite required before any implementation dispatch.
6. Mark `X01` held pending no-faking / NP-interface design review.
7. Clarify that the only current priority tasks are `P1P-01` and `P1P-02`.
8. Clarify that no implementation work is authorized without explicit operator authorization.
9. Add route classification labels to future tasks: mainline, restricted side track, infrastructure, or audit-only.
10. Require every future lower-bound task to state whether it reduces `SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource`; otherwise it must be reported as side-track or infrastructure.
11. Add a warning that restricted `AC0[p]`, formula, local-PRG, coin-problem, and partial-MCSP results do not become P-vs-NP progress without a real `PpolyDAG` / `VerifiedNPDAGLowerBoundSource` bridge.

## 5. What can run now

Run now:

- P1P-01
- P1P-02

Hold everything else.

## 6. What moves toward P≠NP

- `P1P-01` does not prove anything. It is governance/infrastructure documentation that prevents mistaken dispatch.
- `P1P-02` may unblock future `PrefixExtensionLanguage ∈ NP` work by resolving parser, encoding, and runtime conventions before implementation.
- The real mathematical gap remains `NP_not_subset_PpolyDAG`.
- No statement in this errata should be read as a P≠NP claim, a new endpoint, a `ResearchGapWitness`, a `gap_from` bridge, or a `SourceTheorem`.

## 7. Recommended next operator patch

Yes: after this errata lands, the operator should patch `README.md` and `COMMON_WORKER_INSTRUCTIONS.md` before any additional implementation dispatch. That patch should be small and governance-only, applying the errata in Section 4 exactly enough to remove stale broad-dispatch language and install the A11 gate.

Recommended order:

1. Land P1P-01 route map / dispatch errata.
2. Land P1P-02 prefix parser convention design.
3. Patch `README.md` and `COMMON_WORKER_INSTRUCTIONS.md` to make A11 gating normative.
4. Re-evaluate whether any markdown-only follow-up tasks should run.
5. Approve at most one later implementation task at a time, explicitly classified as mainline, side-track, infrastructure, or audit-only.

## Final structured output

Task: P1P-01  
Handle: codex  
Branch: main  
Commit before: to be filled by commit metadata for this errata PR  
Commit after: to be filled by commit metadata for this errata PR  
Changed files: `seed_packs/phase1_20engineer_parallel_dispatch/docs/P1P_01_route_map_dispatch_errata_codex.md`  
Outcome: REPORT_LANDED  
Dispatch now: P1P-01, P1P-02  
Held: L01, L02, B01, K01, K02, X01, X02, and everything else not explicitly listed under Dispatch now  
Cancelled: B02, B03 as written  
Governance errata: Replace `E<NN>` with `<TASK_ID>`; remove all-19-dispatch wording; add A11 gate; cancel B02/B03 as written; require rewrites for B01/K01/X02; hold X01; clarify P1P-only priority; clarify no implementation without operator authorization.  
Commands run: required check command is `./scripts/check.sh`  
Scope violations: none intended; this task adds only this markdown errata document.
