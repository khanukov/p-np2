# P1P-01 route map and dispatch errata

Task: P1P-01  
Handle: codex  
Branch observed: work  
Classification: Infrastructure / governance documentation  
Scope: Markdown-only errata proposal; no Lean, JSONL, spec, NoGoLog, README, or COMMON edits.

## 1. Executive decision

Phase 0 audits are complete: A01 through A10 are present, and A11 has issued the synthesis verdict `PHASE0_COMPLETE_DISPATCH_LIMITED_PHASE1_PLUS`.

The operator decision for future dispatch is therefore:

- **Broad 19-task implementation dispatch is not authorised.** The old dispatch wording that implies every planned task can run concurrently is stale and unsafe.
- **Only limited Phase 1+ tasks are allowed.** These must be documentation, governance, audit hygiene, or explicitly conditional infrastructure unless separately authorised by the operator.
- **Current priority is P1P-01 and P1P-02 only.** P1P-01 creates this route map / errata. P1P-02 designs the prefix parser convention before any X02 implementation.
- **Everything else is held, cancelled, downgraded, or rewritten according to A11.** No engineer should infer permission to implement Lean lower-bound routes from the old README or COMMON text.

## 2. Route map

This map is operator-facing. It classifies route artifacts by their governance role, not by desirability.

### A. Mainline / canonical

These are the only objects that should be described as directly relevant to the final project target.

| Artifact | Role | Dispatch consequence |
| --- | --- | --- |
| `ResearchGapWitness` | The frozen project witness package whose DAG-separation field would carry the real gap. | Do not fabricate or weaken it. Work counts as mainline only if it honestly reduces its source obligation. |
| `NP_not_subset_PpolyDAG` | The mathematical separation still missing. | This remains the real mathematical gap. No restricted lower-bound side track discharges it by itself. |
| `VerifiedNPDAGLowerBoundSource` | The pnp4 source-strength object representing an NP-language lower bound against `PpolyDAG`. | Mainline progress must reduce this obligation or the approved Search-MCSP weak lower-bound source feeding it. |

### B. Conditional wrappers

These are useful only as explicit contracts. They must not be presented as solved sources.

| Artifact | Role | Dispatch consequence |
| --- | --- | --- |
| `SearchMCSPMagnificationContract` | Conditional magnification wrapper around Search-MCSP-style assumptions. | Useful for contract organization, not a proof by itself. |
| `TreeMCSPSearchMagnificationSource` | Tree-MCSP source wrapper used in the pnp4 frontier. | Requires precise parser, runtime, and source assumptions before implementation work expands it. |
| `PvsNPBridgeRequirement` | Bridge-requirement packaging for turning verified source obligations into final consequences. | May document obligations; must not be treated as producing the missing DAG separation. |

### C. Restricted side tracks

These routes can be valuable formalization work, but they are not mainline unless paired with an explicit `PpolyDAG` / `VerifiedNPDAGLowerBoundSource` bridge.

| Side track | Status | Dispatch consequence |
| --- | --- | --- |
| `AC0[p]` | Restricted lower-bound track. | May be formalized only with side-track labeling and no final-target progress claim. |
| formula | Restricted lower-bound track. | Formula lower bounds do not imply the missing DAG separation without a real bridge. |
| local-PRG | Restricted lower-bound track. | Treat as conditional / side-track unless it explicitly reaches the DAG source obligation. |
| coin problems | Restricted lower-bound track. | Do not advertise as direct progress on the final target. |
| partial-MCSP | Restricted / conditional track with known support-bound and provenance hazards. | Reuse only under explicit hypotheses; do not promote support-bound wrappers or default providers. |

### D. Audit / NoGo

These artifacts are safety rails and failure records, not progress routes.

| Artifact family | Role | Dispatch consequence |
| --- | --- | --- |
| `NOGO-000005` through `NOGO-000009` | NoGo / audit records for blocked or hazardous routes. | Use as operator checks before redispatching related work. Do not bypass by renaming a route. |
| `RefutedRoute` / Vacuous routes | Quarantined proof-shape or route-shape artifacts. | Audit-only. Never count ex-falso, vacuous, or refuted-channel implications as mathematical progress. |

### E. Contract-expansion infrastructure

These are infrastructure areas that may support later work but must remain implementation-gated.

| Artifact | Role | Dispatch consequence |
| --- | --- | --- |
| `C_DAG` adapter | Adapter layer for DAG circuit conventions. | Infrastructure only unless tied to the verified DAG source obligation. |
| `PrefixExtensionLanguage` | Prefix-extension language concept needed by parser / NP-membership design. | Needs P1P-02 conventions before Lean implementation. |
| `PrefixExtensionLanguageNP` | Intended NP-membership surface for prefix-extension language. | Do not implement until parser and no-faking design are explicit. |
| `PrefixExtensionLanguageRuntime` | Runtime-claim surface for parser / language membership. | Runtime scope must be designed before any X02-style proof work. |

## 3. Dispatch status table

A11 decisions, normalized to the allowed status vocabulary for every planned non-audit task:

| Task | Status | Operator note |
| --- | --- | --- |
| L01 | DOWNGRADE_TO_MARKDOWN | Replace Lean skeleton ambitions with a literature / interface-alignment note until current pnp4 interfaces justify code. |
| L02 | DOWNGRADE_TO_MARKDOWN | Replace theorem-oracle or marker work with a markdown barrier / governance note. |
| B01 | REWRITE | Rewrite as a concrete barrier-certificate template or require checked Razborov--Rudich conditions; do not package a barrier theorem as arbitrary fields. |
| B02 | CANCEL | Cancel as written because placeholder collapse / separation oracles would create misleading skeletons without real BGS content. |
| B03 | CANCEL | Cancel as written because trivial universal markers and algebraization-as-`Prop` fields are placeholder work. |
| K01 | REWRITE | Rewrite as manual operator-supplied NoGo certificate support; do not claim automatic detection. |
| K02 | APPROVE_LATER | Consider only after README / COMMON governance repair, and only as operator-support classification rather than automatic gating. |
| X01 | HOLD | Hold pending no-faking design against staged `Prop` placeholders and feasibility review for a toy verifier. |
| X02 | REWRITE | Rewrite after P1P-02 resolves serialization, `M(n)`, `tableLen`, malformed rejection, and runtime scope. |

## 4. Governance errata

Before any next dispatch wave, README and COMMON need an operator-approved patch with the following exact corrections:

1. Replace every generic `E<NN>` worker identity, branch, task-file, failure-file, and PR-title placeholder with `<TASK_ID>` or a task-ID-aware convention.
2. Remove wording equivalent to “all 19 dispatchable now” and any dependency text saying no engineer is blocked on another.
3. Add A11 as an explicit gate: A01-A10 completion alone does not authorise implementation waves.
4. Mark B02 and B03 **cancelled as written**.
5. Mark B01, K01, and X02 **rewrite required**.
6. Mark X01 **held** pending no-faking / NP-interface design.
7. Clarify that only P1P tasks authorised by the operator may run now, with current priority narrowed to P1P-01 and P1P-02.
8. Clarify that no Lean implementation, lower-bound route expansion, public theorem surface, JSONL/spec edit, or NoGoLog edit may begin without explicit operator authorisation.
9. Add task-classification labels: mainline, restricted side track, infrastructure, and audit-only.
10. Require future lower-bound tasks to state whether they reduce `SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource`; otherwise classify them as side-track or infrastructure.
11. Add explicit warnings that restricted `AC0[p]`, formula, local-PRG, coin-problem, and partial-MCSP work must not be reported as direct final-target progress without a real DAG bridge.
12. Add B/K/X gating text: B tasks need concrete barrier-bypass conditions, K tasks are manual decision support unless proven otherwise, and X tasks need parser / runtime / no-faking design first.

## 5. What can run now

Run now:

- P1P-01
- P1P-02

Hold everything else.

## 6. What moves toward P≠NP

This errata is deliberately modest:

- P1P-01 does not prove anything. It is a governance and route-map document.
- P1P-02 may unblock future `PrefixExtensionLanguage ∈ NP` work by fixing parser and runtime conventions before implementation.
- The real mathematical gap remains `NP_not_subset_PpolyDAG`.

No statement in this document should be read as claiming an unconditional proof of P≠NP or as authorising implementation of a lower-bound source.

## 7. Recommended next operator patch

Yes: after this errata lands, the operator should approve a small README / COMMON governance patch before any further dispatch.

Recommended patch order:

1. Update COMMON first so every future worker sees `<TASK_ID>` rather than `E<NN>` and sees the A11 gate before opening a task file.
2. Update README second so the public dispatch table removes stale concurrent-dispatch wording and embeds the A11 status table.
3. Keep that patch governance-only unless the operator separately authorises implementation.
4. After README / COMMON are repaired, decide whether P1P-02 is sufficient to rewrite X02, and whether K02 can be scoped as manual operator-support classification.
