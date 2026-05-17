# A11: Synthesis of wave 1 audits (A01–A10) — operator decision memo

**Engineer:** A11 | **Wave:** 1 — Synthesis (post-audit) | **Estimated:** 1 week | **Difficulty:** medium-high | **Type:** markdown-only

## Goal

Read all 10 wave-1 audit reports (A01–A10) and produce **one operator-decision memo** that synthesizes them into:

1. A repo-wide map of what is kernel-checked vs staged vs refuted vs legacy.
2. A consolidated **cross-cutting recommendations list** with priorities.
3. A clear **wave-2 decision matrix**: which (if any) of L/B/K/X tracks should be reactivated, in what order, with what scope rewrites, and why.
4. An honest verdict on whether engineering wave 1 has changed the operator's understanding of the math-level bottleneck (`ResearchGapWitness` source).

This is the **gating task** before any L/B/K/X dispatch. Until A11 lands and the operator decides, no wave-2 dispatch happens.

## Source material — required reading

All 10 wave-1 audit reports under `seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/`:

* `A01_pnp3_magnification_partial_codex.md` (466 lines, codex)
* `A02_pnp3_finalresult_auditor.md` (493 lines, auditor)
* `A03_pnp3_ac0_bridges_gpt55.md` (470 lines, gpt55)
* `A04_pnp3_barrier_gpt55.md` (598 lines, gpt55)
* `A05_pnp3_lowerbounds_codex.md` (372 lines, codex)
* `A06_pnp3_models_complexity_codex.md` (568 lines, codex)
* `A07_pnp4_algorithmstolowebounds_codex.md` (581 lines, codex)
* `A08_pnp4_frontier_codex.md` (568 lines, codex)
* `A09_nogolog_formal_witnesses_codex.md` (312 lines, codex)
* `A10_partial_legacy_markers_codex.md` (1,266 lines, codex)

Plus the original deferred-task files (`tasks/L01..L02`, `B01..B03`, `K01..K02`, `X01..X02`) and the reduction memo (`AUDIT_2026-05-17_PLAN_REDUCTION.md`) to understand what was deferred and why.

Plus trust-root files (read-only): `pnp3/Complexity/Interfaces.lean`, `pnp3/Magnification/UnconditionalResearchGap.lean`, `pnp3/Barrier/*`.

Total reading volume: ~5,700 lines of audit markdown + design memos. Plan for a real week of close reading; do not skim.

## Deliverable

```
seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A11_wave1_synthesis_<handle>.md
```

**One file, markdown only.** No Lean edits, no NoGoLog edits, no trust-root touches.

### Required sections

#### 1. Executive verdict (1 paragraph + 1 sentence)

One of: `WAVE_1_COMPLETE_NO_NEW_ROUTE` / `WAVE_1_COMPLETE_NEW_DIRECTION_FOUND` / `WAVE_1_REVEALS_ENGINEERING_GAPS_FIRST` / `WAVE_1_INCOMPLETE_NEEDS_RE_DISPATCH`.

Followed by one sentence stating whether the math-level bottleneck (non-vacuous `ResearchGapWitness` source) is closer, unchanged, or further away after wave 1.

#### 2. Cross-audit consensus map

For each architectural area (Magnification, FinalResult, AC0 bridges, LowerBounds, Models/Complexity, AlgorithmsToLowerBounds, Frontier/ContractExpansion, NoGoLog), summarize the consensus or disagreement across the audit reports that touch it. Use a table:

| Area | A01 | A02 | A03 | A04 | A05 | A06 | A07 | A08 | A09 | A10 | Consensus |

Mark cells with one of: `none` / `summary` / `kernel-checked` / `staged` / `refuted` / `legacy` / `hotspot`. The Consensus column is a 1-2 sentence synthesis.

#### 3. Refuted / vacuous / legacy quarantine inventory

Cross-cutting list of every refuted / vacuous / legacy route flagged in two or more audits. For each, list:
- declaration name(s)
- audit reports that flag it
- recommended action: `keep quarantined` / `rename` / `add guard test` / `delete after migration` / `operator decision`

This should at minimum address:
- `FormulaSupportRestrictionBoundsPartial` and `_of_old` migration bridges (A01, A03)
- `FormulaSemanticMultiSwitchingProvider` and singleton-route internal provider (A03)
- `Vacuous_P_ne_NP_via_*` and `VacuousFinalPayloadProvider` (A02)
- `MagnificationAssumptions` legacy support-bounds carrier (A02)
- Default/`hasDefault*` provider flags (A01, A03, A10)
- Stale NoGoLog anchors NOGO-000002/000004/000005 and the `needs_review` entry NOGO-000003 (A09)
- `LegacyStraight*` naming in pnp3/Complexity (A06)
- `FailedRoute_*` modules in pnp3/LowerBounds (A05)

#### 4. Math-level bottleneck status

For each of the following candidate paths to a non-vacuous `ResearchGapWitness`, classify as:
- `path closed` (audit shows no traction or formally refuted)
- `path open with known mathematical content` (e.g., real lower-bound theorem still needed)
- `path open with engineering content` (e.g., bridge or adapter still needed but math content exists)
- `path unclassified` (insufficient evidence in wave 1)

Candidate paths:
1. AC0/locality → formula/real separation → DAG (per A03 / A01)
2. Anti-checker → asymptotic locality/IsoStrongRoute → DAG (per A02)
3. Search-MCSP magnification → DAG (per A07 / A08)
4. Contract-expansion / prefix-extension language → NP_TM → DAG (per A08)
5. AC0[p] / coin lower bounds → restricted P/poly source → DAG (per A07)
6. Fixed-slice / fixedParams + uniformProvenance (per A02, A10)
7. Pich-Santhanam unprovability (per L02 deferral)
8. Hirahara search-to-decision MCSP (per L01 deferral)

State which (if any) path is most promising for further investigation given current repository state.

#### 5. Wave-2 decision matrix

For each of the 8 deferred tasks (L01, L02, B01, B02, B03, K01, K02, X02) plus X01 (still pending), make a recommendation:

| Task | Current status | Wave-1 evidence | Recommendation | Conditions |

Recommendations must be one of:
- `DISPATCH wave 2` (and state in what order and with what scope changes)
- `DISPATCH after spec rewrite` (state what rewrite)
- `DEFER beyond wave 2` (state the dependency that would unlock it)
- `CANCEL` (state why audit evidence kills the task)

X01 is a special case: it is the only narrow engineering bridge endorsed by D0 scoping. State whether the audits provide a reason to dispatch it now, dispatch it conditionally, or cancel/rewrite it.

#### 6. Cross-cutting operator-decision items

Consolidated list of every actionable, markdown-only or low-risk Lean cleanup task surfaced by the 10 audits. Prioritize: H (high, blocks wave-2 quality) / M (medium, improves hygiene) / L (low, nice to have).

At minimum address:
- NoGoLog anchor repair (A09)
- Provider/Default quarantine pass (A01, A03, A10)
- `_fromPipeline` vs old support-bounds visibility (A01, A03)
- pnp3↔pnp4 MCSP crosswalk (A06, A07)
- `RefutedRoute_*` naming review in FinalResultAuditRoutes (A02)
- Frontier/ContractExpansion source-theorem packaging (A08)
- `FailedRoute_*` module cleanup recommendations (A05)

#### 7. Honest caveats

Where the synthesis is uncertain, say so. In particular:
- Where audits disagree on whether a route is refuted or only weak.
- Where the audit coverage was partial (e.g., A01's 85% coverage of `LocalityProvider_Partial.lean`).
- Where math-level claims would require external literature verification not done in wave 1.

#### 8. Recommended wave-2 size

State a single number: how many tasks (0–N) the operator should dispatch in wave 2 based on this synthesis. With one sentence of justification.

If the answer is 0, state the conditions under which wave 2 should ever be reopened.

## Acceptance criteria

### Universal (per `COMMON_WORKER_INSTRUCTIONS.md`)

- Markdown report at exact path `seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A11_wave1_synthesis_<handle>.md`.
- No Lean edits (`git diff origin/main -- "*.lean"` must be empty).
- No NoGoLog edits, no spec edits, no trust-root touches.
- Honest caveats line in PR description.
- Self-attack: read your own synthesis adversarially; check that no claim about "consensus" is actually one audit projected onto the others; check that recommendations cite specific audit evidence.

### Task-specific

- [ ] All 10 audit reports cited at least once each by name + section/finding.
- [ ] Executive verdict is exactly one of the 4 stated options.
- [ ] Cross-audit consensus map covers all 8 architectural areas listed.
- [ ] Refuted/vacuous/legacy inventory covers all 8 minimum items.
- [ ] Math-level bottleneck section classifies all 8 candidate paths.
- [ ] Wave-2 decision matrix covers all 9 tasks (L01, L02, B01, B02, B03, K01, K02, X01, X02).
- [ ] Cross-cutting items list covers all 7 minimum items, prioritized H/M/L.
- [ ] Recommended wave-2 size is a single explicit number with justification.
- [ ] PR description uses the structured template from COMMON §12.

### Honest framing requirements

- ❌ Do not claim that wave 1 changes the public endpoint `P_ne_NP_final (gap : ResearchGapWitness)`. It does not.
- ❌ Do not promote any audit recommendation to "this proves a step toward P ≠ NP". They are all infrastructure recommendations.
- ❌ Do not pretend confidence about wave-2 timing — synthesis is a snapshot, not a roadmap commitment.
- ✅ Do say explicitly if the synthesis suggests **stop** ("audits confirm no shorter route; bottleneck is math-level; do not dispatch wave 2 until new math content appears").
- ✅ Do flag specific places where audit reports contradict each other, if any.

## Scope

### Allowed

- New markdown report at the exact path above.
- Reading all files in `audit_reports/`, all task files, the reduction memo, trust-root files.
- Reading `outputs/nogolog.jsonl` to cross-check A09's stale-anchor claims.
- Targeted `rg` searches for cited declaration names to verify they exist.

### Forbidden

- Universal forbidden scope from `COMMON_WORKER_INSTRUCTIONS.md` §3.
- ❌ Editing audit reports A01–A10 (they are frozen as wave-1 record).
- ❌ Editing `tasks/L01..L02`, `B01..B03`, `K01..K02`, `X01..X02` task files — wave-2 dispatch decisions go in the A11 memo, not in those files.
- ❌ Updating the dispatch README or COMMON_WORKER_INSTRUCTIONS — the operator does that based on A11.
- ❌ Producing wave-2 task specifications — A11 is a decision memo, not a dispatch.
- ❌ Editing `outputs/nogolog.jsonl` even to fix the stale anchors A09 flagged — those are separate cleanup tasks gated on operator decision.

## Output

PR title: `Phase 1 A11: wave 1 synthesis + wave 2 decision memo`

PR body uses the structured template; verdict line and recommended-wave-2-size line must be in the body for operator quick-read.

## Why this is gating

The 10 wave-1 audits produced ~5,700 lines of markdown. Operator review of each individually is feasible but operator decision on the next move requires cross-cutting synthesis — which audit, what is the new evidence, does any path change priority. A11 is the synthesis pass that turns the 10-report corpus into a single actionable operator-decision memo.

Without A11, dispatching L/B/K/X would be flying blind: the deferred-task memos (`AUDIT_2026-05-17_PLAN_REDUCTION.md`) predate the audits and cannot reflect their evidence.

After A11 lands and the operator decides, wave 2 (if any) gets a new dispatch spec; if the operator decides stop, A11 is the closeout document for the engineering phase.
