# P1P-01 route map and dispatch errata

Task: P1P-01  
Handle: codex  
Scope classification: Infrastructure / governance errata proposal. Markdown-only; no Lean/source/spec/JSONL edits.

## 1. Executive decision

A11 landed the Phase 0 synthesis verdict:

```text
PHASE0_COMPLETE_DISPATCH_LIMITED_PHASE1_PLUS
```

Operator-facing decision:

- Phase 0 audits are complete: A01 through A10 are present, and A11 synthesizes them.
- Broad 19-task implementation dispatch is **not authorised**.
- Only limited Phase 1+ tasks are allowed.
- Current priority is **P1P-01 and P1P-02 only**.
- Everything outside the explicitly listed current priority remains held, cancelled, or subject to rewrite before any implementation dispatch.

This document is an errata proposal for future operator patches. It intentionally does not edit `README.md`, `COMMON_WORKER_INSTRUCTIONS.md`, Lean source, JSONL logs, specs, or NoGoLog entries.

## 2. Route map

### A. Mainline / canonical

These are the only route objects that should be treated as canonical progress boundaries for the frozen target.

| Object | Route-map role | Dispatch interpretation |
| --- | --- | --- |
| `ResearchGapWitness` | pnp3 witness whose hard payload is the DAG separation field. | Mainline only when honestly inhabited without refuted/vacuous/provider channels. |
| `NP_not_subset_PpolyDAG` | The real mathematical separation still missing. | The central hard gap. Supplying this is genuine progress; wrapping it is not. |
| `VerifiedNPDAGLowerBoundSource` | pnp4 source object strong enough to feed the DAG lower-bound bridge. | Mainline source obligation; must not be instantiated from restricted side-track results without an explicit `PpolyDAG` theorem. |

### B. Conditional wrappers

These wrappers are useful only as conditional infrastructure. They do not by themselves supply the hard payload.

| Object | Route-map role | Dispatch interpretation |
| --- | --- | --- |
| `SearchMCSPMagnificationContract` | Contract surface intended to turn a search-MCSP weak lower bound into a verified DAG source. | Conditional mainline wrapper; valuable only when paired with a real source assumption and non-vacuous magnification proof. |
| `TreeMCSPSearchMagnificationSource` | Tree-MCSP concrete/search target surface. | Conditional wrapper; parser/runtime conventions must be fixed before implementation. |
| `PvsNPBridgeRequirement` | Bridge-requirement documentation/interface for what a route must satisfy. | Governance/contract aid, not a proof source. |

### C. Restricted side tracks

These tracks may be mathematically useful, but they are not to be reported as unconditional P-vs-NP mainline progress unless they include an explicit bridge to `PpolyDAG` / `VerifiedNPDAGLowerBoundSource`.

| Track | Route-map role | Dispatch interpretation |
| --- | --- | --- |
| `AC0[p]` | Restricted circuit lower-bound pipeline. | Side track unless connected to a real DAG-source bridge. |
| `formula` | Formula lower-bound / collapse surfaces. | Side track unless it proves the frozen DAG target. |
| `local-PRG` | Local pseudorandom-generator consequences. | Side track unless it yields the required DAG separation source. |
| `coin problems` | Coin-problem / AC0-style contract surfaces. | Side track; do not promote to final lower-bound progress. |
| `partial-MCSP` | Partial MCSP/formula/locality plumbing. | Useful infrastructure, but support-bound and locality routes are known high-risk for refuted/vacuous misuse. |

### D. Audit / NoGo

These artifacts are audit and safety infrastructure, not lower-bound sources.

| Object family | Route-map role | Dispatch interpretation |
| --- | --- | --- |
| `NOGO-000005` through `NOGO-000009` | Formal or documented negative route witnesses and guardrails. | Use to prevent repeated failed routes; do not treat as positive lower-bound progress. |
| `RefutedRoute` / vacuous routes | Quarantined or audit-only endpoints that can typecheck while carrying no mathematical payload. | Never use as dispatch justification for P-vs-NP progress. |

### E. Contract-expansion infrastructure

These are engineering surfaces that may unblock later precise contracts. They are not mathematical endpoints.

| Object | Route-map role | Dispatch interpretation |
| --- | --- | --- |
| `C_DAG` adapter | Adapter infrastructure for concrete DAG/circuit interfaces. | Infrastructure; safe only under explicit no-overclaim language. |
| `PrefixExtensionLanguage` | Prefix-extension language scaffold. | Infrastructure; useful for future parser/encoding work. |
| `PrefixExtensionLanguageNP` | Staged NP-membership surface for the prefix-extension language. | Hold any strong NP-membership claim until parser/runtime/no-faking obligations are settled. |
| `PrefixExtensionLanguageRuntime` | Runtime accounting scaffold. | Infrastructure; must be aligned with parser conventions before X02-style implementation. |

## 3. Dispatch status table

Status vocabulary used here is intentionally restricted to: `CANCEL`, `HOLD`, `REWRITE`, `DOWNGRADE_TO_MARKDOWN`, `APPROVE_LATER`, and `NOT_NOW`.

| Task | Status | A11-based operator meaning |
| --- | --- | --- |
| `L01` | `DOWNGRADE_TO_MARKDOWN` | Rewrite as literature/interface alignment for SearchMCSP, not a Lean surface with `Prop := True` markers or reduction records that only package assumptions. |
| `L02` | `DOWNGRADE_TO_MARKDOWN` | Keep as bounded-arithmetic/barrier governance context; do not add theorem-oracle Lean surfaces. |
| `B01` | `REWRITE` | Require concrete barrier-certificate criteria or a markdown template; do not package Razborov-Rudich as arbitrary theorem fields. |
| `B02` | `CANCEL` | Cancel as written because placeholder oracle/collapse/separation skeletons would be misleading. |
| `B03` | `CANCEL` | Cancel as written because trivial algebraization markers and theorem-as-field placeholders would be misleading. |
| `K01` | `REWRITE` | Rewrite as manual/operator-supplied NoGo certificate support, not automatic route detection. |
| `K02` | `APPROVE_LATER` | Potentially useful only after README/COMMON governance repair and only as manual/operator-support classification. |
| `X01` | `HOLD` | Hold pending no-faking and NP-interface design review; do not accept staged placeholder propositions as NP bridges. |
| `X02` | `REWRITE` | Parser implementation is useful only after P1P-02 fixes parser conventions and after the X01 dependency decision. |

## 4. Governance errata

Before the next dispatch wave, the operator should patch `README.md` and `COMMON_WORKER_INSTRUCTIONS.md` to make the A11 gate explicit. Required changes:

1. Replace `E<NN>` with `<TASK_ID>` everywhere the instruction is intended to cover A/L/B/K/X/P1P task IDs.
2. Remove or replace “all 19 dispatchable now” / “all tasks are independent and run concurrently” wording.
3. Add A11 as an explicit gate for any post-audit Phase 1+ / L / B / K / X implementation dispatch.
4. Mark `B02` and `B03` cancelled as written.
5. Mark `B01`, `K01`, and `X02` rewrite required.
6. Mark `X01` held pending no-faking / NP-interface design review.
7. Clarify that the only current priority tasks are P1P tasks explicitly authorised by the operator; for this dispatch window, that means P1P-01 and P1P-02 only.
8. Clarify that no implementation work may start without operator authorisation after the A11 gate.
9. Add task-classification labels: mainline, side track, infrastructure, and audit-only.
10. Require future lower-bound tasks to state whether they reduce `SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource`; if not, they must be labelled side track, infrastructure, or audit-only.
11. Add an explicit warning that consuming `VerifiedNPDAGLowerBoundSource` is not the same as producing it.
12. Add no-placeholder language for theorem-as-field, `Prop := True`, trivial oracle markers, vacuous providers, and refuted-route endpoints.

## 5. What can run now

Run now:

- P1P-01
- P1P-02

Hold everything else.

For avoidance of doubt, this route-map document narrows the immediate operator-facing priority to P1P-01 and P1P-02 even though A11 listed additional possible markdown-only P1P tasks. Those additional tasks require separate operator authorisation before dispatch.

## 6. What moves toward P≠NP

Honest assessment:

- P1P-01 does not prove anything. It is a governance and dispatch-clarity document.
- P1P-02 may unblock future `PrefixExtensionLanguage ∈ NP` work by fixing parser, serialization, table-length, and runtime conventions before X02-style implementation.
- The real mathematical gap remains `NP_not_subset_PpolyDAG`.
- Conditional wrappers, restricted lower-bound side tracks, NoGo witnesses, and parser/runtime infrastructure should not be described as a proof of P≠NP.

## 7. Recommended next operator patch

Yes: after this errata lands, the operator should update `README.md` and `COMMON_WORKER_INSTRUCTIONS.md` before authorising any further dispatch.

Recommended patch order:

1. Patch README/COMMON with the governance errata in Section 4.
2. Make the A11 gate and P1P-only current priority unambiguous.
3. Replace stale branch/PR/task-ID examples so engineers do not follow the `E<NN>` naming path.
4. Reissue or rewrite task prompts only after the updated dispatch docs clearly mark cancelled, held, downgraded, and rewrite-required work.

## Final structured output template for this task

```text
Task: P1P-01
Handle: codex
Branch: <actual branch at execution time>
Commit before: <commit before this markdown-only change>
Commit after: <commit containing this markdown-only change>
Changed files:
  - seed_packs/phase1_20engineer_parallel_dispatch/docs/P1P_01_route_map_dispatch_errata_codex.md
Outcome: REPORT_LANDED | STRUCTURED_FAILURE
Dispatch now:
  - P1P-01
  - P1P-02
Held:
  - everything else unless separately operator-authorised
Cancelled:
  - B02 as written
  - B03 as written
Governance errata:
  - replace E<NN> with <TASK_ID>
  - remove all-19-dispatchable wording
  - add A11 gate
  - mark B02/B03 cancelled as written
  - mark B01/K01/X02 rewrite required
  - mark X01 held
  - clarify P1P tasks only
  - clarify no implementation without operator authorisation
Commands run:
  - ./scripts/check.sh
Scope violations:
  - none expected
```
