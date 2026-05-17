# Phase 1 — Reduced wave (6 tasks)

## Status

**OPEN** for dispatch. 5 markdown audits + 1 narrow Lean bridge. Tasks run independently.

This file was reduced from 19 tasks per `AUDIT_2026-05-17_PLAN_REDUCTION.md` (read first if you are an operator deciding on dispatch).

## Why a reduced wave

The earlier 19-task plan was an infrastructure program rather than a closeout program: it opened 5 programmatic surfaces (audits, literature, barriers, kill-machine, contract expansion) and pre-committed a wave 2 of 5–15 more tasks. The repository's own strategic documents (FP3b retrospective; D0 polynomial-time-formalism scoping) point in a much narrower direction: the active gap is mathematical (`ResearchGapWitness` source), not engineering, and the one infrastructure investment that is on the critical path is the `PolyTimeVerifierSpec → NP_TM` bridge.

Reduced wave keeps only:

- the audits with the highest operator-decision yield (live theorem surfaces, NoGoLog integrity, placeholder inventory);
- the one Lean bridge endorsed by the D0 memo.

Everything else is deferred. See `AUDIT_2026-05-17_PLAN_REDUCTION.md` for per-task rationale.

## Repository reality (recap)

`UnconditionalResearchGap.lean` already proves `P_ne_NP_final (gap : ResearchGapWitness) : P_ne_NP`. The remaining mathematical gap is producing a non-vacuous `ResearchGapWitness` — a real proof of `NP_not_subset_PpolyDAG`. This phase does not attempt that; it audits the surrounding surface and adds one resumability-enabling bridge.

| Area | Status |
|---|---|
| `pnp3/` axiom-clean (0 sorry / 0 admit / 0 axiom-decl) | ✓ |
| `pnp4/` fully clean (0 sorry / 0 admit / 0 axiom / 0 Fact / 0 opaque) | ✓ |
| Falsifiability audit closed (5 legacy routes proven vacuous) | ✓ |
| Trust roots intact (`Interfaces.lean`, `UnconditionalResearchGap.lean`, `Barrier/*`) | ✓ |
| Contract-expansion infra through R1-B2a runtime | ✓ |
| Non-vacuous `ResearchGapWitness` source | ✗ (math-level, not in scope this phase) |

## Engineer dispatch

You are one of 6 engineers. Take **ONE** task by ID. Don't take more than one.

### Common reading (everyone)

1. `RESEARCH_CONSTITUTION.md` — discipline rules; binding.
2. `seed_packs/phase1_20engineer_parallel_dispatch/COMMON_WORKER_INSTRUCTIONS.md` — universal rules.
3. `seed_packs/phase1_20engineer_parallel_dispatch/AUDIT_2026-05-17_PLAN_REDUCTION.md` — context for why this wave is reduced.
4. **Your specific task file** in `tasks/<ID>_*.md`.
5. (Audit tasks only) The files you're auditing — read carefully.

### Task list

#### Audit tasks (5 tasks, markdown-only)

| ID | Audit area | LOC scope | Time |
|---|---|---|---|
| [A02](tasks/A02_audit_pnp3_finalresult.md) | `pnp3/Magnification/FinalResult*.lean` (6 files) | ~4,091 | 1 wk |
| [A07](tasks/A07_audit_pnp4_algorithmstolowebounds.md) | `pnp4/Pnp4/AlgorithmsToLowerBounds/` (24 files) | ~6,700 | 1 wk |
| [A08](tasks/A08_audit_pnp4_frontier.md) | `pnp4/Pnp4/Frontier/*` incl. `ContractExpansion/` | ~1,200 | 1 wk |
| [A09](tasks/A09_audit_nogolog_formal_witnesses.md) | `outputs/nogolog.jsonl` formal_witness validation | — | 3 days |
| [A10](tasks/A10_audit_partial_legacy_markers.md) | Cross-cutting `_Partial`/`_Legacy`/`TODO`/`Classical.choose` inventory | — | 3 days |

Output: each audit lands one markdown report at `seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/<ID>_<area>_<handle>.md`.

No Lean edits, no shared-file collisions.

#### Lean task (1 task)

| ID | Title | Time | Difficulty |
|---|---|---|---|
| [X01](tasks/X01_polytimeverifierspec_bridge.md) | `PolyTimeVerifierSpec` + bridge to `NP_TM` (Option B.1 from D0) | 3 wks | medium |

X01 touches `lakefile.lean`, `pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean`, and `pnp4/Pnp4/Tests/AxiomsAudit.lean`. Within this wave X01 is the only Lean task, so no parallel-merge collision.

### Deferred tasks (not dispatchable this wave)

The following task files exist under `tasks/` for record but are marked DEFERRED. **Do not pick one of these.** See `AUDIT_2026-05-17_PLAN_REDUCTION.md` for per-task reasoning.

- `A01`, `A03`, `A04`, `A05`, `A06` — deferred lower-yield audits; maintainability not shortest-path.
- `L01`, `L02` — deferred. L01 has bibliographic ID error (`1804.05985` is not Hirahara FOCS 2018); needs rewrite.
- `B01`, `B02`, `B03` — deferred. B02/B03 are placeholder/`True`-typed wrapper surfaces; B01 lower priority than X01.
- `K01`, `K02` — deferred. Typed rubrics, not theorem engines.
- `X02` — deferred until X01 lands AND spec rewritten. Current spec uses `M := fun n => n` which is incompatible with the live `treeMCSPPrefixAmbientLength` convention in `PrefixExtensionLanguageRuntime.lean`.

### Dependency graph

```
A02, A07, A08, A09, A10 — all independent markdown audits.
X01 — independent of all audits; only Lean task this wave.
No engineer is blocked on another.
```

After wave 1 lands and operator synthesizes, wave 2 is an operator decision:
- **Stop** if audits confirm no hidden shorter route and X01 is the only worthwhile bridge; or
- **Dispatch rewritten X02** explicitly gated on X01.

## Acceptance criteria — universal

See `COMMON_WORKER_INSTRUCTIONS.md` §4. Summary:

1. ✅ Files at exact paths specified in the task.
2. ✅ For audit tasks: markdown report at expected path with all required sections.
3. ✅ For X01: `lake build PnP3 Pnp4` passes; `./scripts/check.sh` passes; `rg "\bsorry\b|\badmit\b" -g"*.lean" pnp3 pnp4` empty.
4. ✅ For X01: smoke test in `AlgorithmsToLowerBoundsSurfaceTests.lean` + `#print axioms` line in `AxiomsAudit.lean`.
5. ✅ PR description uses structured template from COMMON §12.
6. ✅ No edits to forbidden files (see COMMON §3.1).

Operator review target: **~20 minutes per audit PR**, **~45 minutes for X01 PR**.

## Forbidden scope — universal

See `COMMON_WORKER_INSTRUCTIONS.md` §3. Summary:

- No edits to `pnp3/Complexity/Interfaces.lean`, `pnp3/Complexity/PsubsetPpolyInternal/**`, `pnp3/Magnification/UnconditionalResearchGap.lean`, `pnp3/Barrier/**`, `pnp3/Magnification/AuditRoutes/**`.
- No edits to existing `pnp3/Magnification/*_Partial.lean`, `FinalResult*.lean`, `AC0*Bridge.lean` files.
- For X01: no `sorry` / `admit` / `axiom` / `opaque` / `Fact` / typeclass-payload.
- No `Classical.choose` in core definitions (acceptable in derived proofs if standard exponent extraction; document).
- No `SourceTheorem_*` / `gap_from_*` / `ResearchGapWitness` / `NP_not_subset_PpolyDAG` / `P_ne_NP` claims.
- No `ProvenanceFilter_v1` promotion.
- No new NoGoLog entries.

## What this phase does NOT do

- No P-vs-NP proof.
- No `ResearchGapWitness` construction.
- No new endpoint or final theorem.
- No claim that any audit or X01 advances the math-level bottleneck.

This wave is **operator situational awareness + one resumability bridge**. Nothing more.

## Re-dispatch / failure protocol

If you cannot complete your task within scope, write a structured failure report at:

`seed_packs/phase1_20engineer_parallel_dispatch/failures/<ID>_<your-handle>.md`

Four sections: What was attempted / Where it broke / Local vs global obstruction / What an integrator must know.

## Cross-references

- `RESEARCH_CONSTITUTION.md` — overarching discipline.
- `seed_packs/phase1_20engineer_parallel_dispatch/AUDIT_2026-05-17_PLAN_REDUCTION.md` — why this wave is reduced.
- `seed_packs/first_move_search_2026/reports/fp3b_epoch_strategic_retrospective_claudeopus.md` — FP3b context.
- `seed_packs/polynomial_time_formalism_scoping_D0/reports/D0_four_way_review_and_synthesis_claudeopus.md` — X01 rationale.
- `seed_packs/phase1_20engineer_parallel_dispatch/COMMON_WORKER_INSTRUCTIONS.md` — required reading.

## Status header

```
Wave: 1 (reduced)
Engineers: 6 (parallel)
  - Audits (markdown): 5 (A02, A07, A08, A09, A10)
  - Lean bridge: 1 (X01)
Wave 2 status: operator decision after wave 1 synthesis (no pre-commitment)
Estimated wall-clock: 3 weeks (X01-bound; audits land within 1 week)
Operator review load: ~5 × 20 min + 1 × 45 min ≈ 2.5 operator-hours
Outcome: operator-decision-useful snapshot of live theorem surface + one D0-aligned bridge
```
