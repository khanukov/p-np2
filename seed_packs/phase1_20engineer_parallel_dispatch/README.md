# Phase 1 — 20-engineer parallel dispatch

## Status

**OPEN** for parallel dispatch. All 20 tasks are independent and can run concurrently.

## Classification

**Infrastructure / kill-machine acceleration.**

This phase is **not** P-vs-NP mainline progress. It accelerates the kill-machine by:

1. Formalizing state-of-the-art magnification literature in pnp4 (E01-E13).
2. Making the three classical barriers (Razborov-Rudich, relativization, algebrization) into kernel-checked Lean theorems (E14-E16).
3. Building industrial-scale kill-machine tooling (E17-E18).
4. Optionally completing the contract_expansion implementation in parallel (E19-E20).

After Phase 1 lands, every future route attempt can be:
- evaluated against formal barrier theorems automatically
- compared with formal magnification thresholds
- checked for NoGo applicability across routes

## Engineer dispatch

You are one of 20 engineers. Take **ONE** task by ID. Don't take more than one.

### Common reading (everyone)

Before starting your task:

1. `RESEARCH_CONSTITUTION.md` — discipline rules; binding.
2. `seed_packs/phase1_20engineer_parallel_dispatch/COMMON_WORKER_INSTRUCTIONS.md` — universal rules for this phase.
3. **Your specific task file** in `tasks/E<NN>.md`.

### Task list

| ID | Title | Phase | Time est. | Difficulty |
| --- | --- | --- | --- | --- |
| [E01](tasks/E01_AM2025_distinguisher_definitions.md) | AM 2025 Distinguisher structure + weight + sparsity | A — Literature | 2 wks | medium |
| [E02](tasks/E02_AM2025_theorem1_surface.md) | AM 2025 Theorem 1 (n^7 distinguisher) typed surface | A — Literature | 2 wks | medium |
| [E03](tasks/E03_AM2025_kernel_K_interface.md) | AM 2025 Kernel K(Q,D,r) construction interface | A — Literature | 2 wks | medium |
| [E04](tasks/E04_CHOPRS_oracle_gate_model.md) | CHOPRS 2020 oracle-gate model | A — Literature | 2 wks | medium |
| [E05](tasks/E05_CHOPRS_locality_barrier_statement.md) | CHOPRS 2020 locality barrier statement | A — Literature | 2 wks | medium |
| [E06](tasks/E06_CHOPRS_magnification_locality_link.md) | CHOPRS magnification-vs-locality theorem statement | A — Literature | 2 wks | high |
| [E07](tasks/E07_OPS_gap_problems.md) | OPS 2021 Gap-MCSP / Gap-MKtP problem definitions | A — Literature | 2 wks | medium |
| [E08](tasks/E08_OPS_magnification_thresholds.md) | OPS 2021 magnification thresholds (s_1, s_2, β, ε, c) | A — Literature | 2 wks | medium |
| [E09](tasks/E09_CJW_sparse_NP_magnification.md) | CJW 2019 sparse-NP-language magnification statement | A — Literature | 2 wks | medium |
| [E10](tasks/E10_CHMY_one_tape_TM_bound.md) | CHMY 2021 one-tape TM lower bound for MCSP | A — Literature | 2 wks | medium |
| [E11](tasks/E11_CHMY_branching_program_bound.md) | CHMY 2021 branching program lower bound for MKtP | A — Literature | 2 wks | medium |
| [E12](tasks/E12_Hirahara_search_to_decision.md) | Hirahara search-to-decision MCSP reduction surface | A — Literature | 2 wks | high |
| [E13](tasks/E13_PichSanthanam_unprovability.md) | Pich-Santhanam bounded arithmetic unprovability surface | A — Literature | 3 wks | high |
| [E14](tasks/E14_RazborovRudich_barrier.md) | Razborov-Rudich natural proofs barrier — formal | B — Barriers | 3 wks | high |
| [E15](tasks/E15_relativization_barrier.md) | Relativization (BGS) barrier — concrete oracle | B — Barriers | 3 wks | high |
| [E16](tasks/E16_algebrization_barrier.md) | Algebrization (Aaronson-Wigderson) barrier — formal | B — Barriers | 3 wks | high |
| [E17](tasks/E17_cross_route_nogo_checker.md) | Cross-route NoGo applicability checker library | C — Kill-machine | 2 wks | medium |
| [E18](tasks/E18_pre_dispatch_barrier_classifier.md) | Pre-dispatch barrier-classification tool | C — Kill-machine | 2 wks | medium |
| [E19](tasks/E19_PolyTimeVerifierSpec_bridge.md) | PolyTimeVerifierSpec + bridge to NP_TM | D — Contract expansion | 3 wks | medium |
| [E20](tasks/E20_concrete_tree_MCSP_parser.md) | Concrete tree-MCSP parser + runtime proofs | D — Contract expansion | 4 wks | medium-high |

### Dependency graph

```
Phase A (E01-E13):  all independent.
Phase B (E14-E16):  all independent of each other and of Phase A.
Phase C (E17, E18): can start in parallel; E17 benefits from E14-E16 landing first
                    but does not block on them.
Phase D (E19, E20): E20 benefits from E19 landing first; both independent of A/B/C.
```

**No engineer is blocked on another engineer.** Each task is self-contained.

## Acceptance criteria — universal

For every task, the operator-review checklist is identical:

1. ✅ All files at exact paths specified in the task.
2. ✅ `lake build PnP3 Pnp4` passes from repo root.
3. ✅ `./scripts/check.sh` passes.
4. ✅ `rg -n "\bsorry\b|\badmit\b" -g"*.lean" pnp3 pnp4` returns no output (across the whole repo, not just your file).
5. ✅ All theorems/structures in the task's "expected signatures" section are defined with the exact names and shapes specified.
6. ✅ At least one smoke test in `pnp4/Pnp4/Tests/` references each new public theorem/structure (one-line `def check_<name> := ...`).
7. ✅ Three `#print axioms` lines in `pnp4/Pnp4/Tests/AxiomsAudit.lean` for the three most important new theorems.
8. ✅ The PR description contains the structured output template from §"Output format" of `COMMON_WORKER_INSTRUCTIONS.md`.
9. ✅ No edits to forbidden files (see COMMON).

Operator review target time: **< 15 minutes per landed task**.

## Forbidden scope — universal

See `COMMON_WORKER_INSTRUCTIONS.md`. Summary:

- No edits to `pnp3/Complexity/Interfaces.lean`, `pnp3/Magnification/UnconditionalResearchGap.lean`, `pnp3/Barrier/*` (trust roots).
- No `sorry` / `admit` / `axiom` / `opaque` / `Fact` / typeclass-payload in committed Lean.
- No `Classical.choose` in core literature definitions (acceptable in derived proofs if standard exponent extraction; document explicitly).
- No `SourceTheorem_*` / `gap_from_*` / `ResearchGapWitness` / FP-4 / final endpoint / P ≠ NP claim.
- No `ProvenanceFilter_v1` promotion.
- No new NoGoLog entries (operator-side action only).

## Output template — every PR

Every engineer's PR description must end with:

```text
Task: E<NN> <title>
Engineer handle: <your-handle>
Branch: main
Commit: <sha>
Files added/modified:
  - <list>
Acceptance criteria:
  [x] / [ ] for each universal item above
  [x] / [ ] for each task-specific item from the task file
Lean signatures landed:
  - <name> : <signature>
  - ...
Smoke tests added in pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean:
  - <name>
#print axioms entries added in pnp4/Pnp4/Tests/AxiomsAudit.lean:
  - <name>
Commands run:
  - lake build PnP3 Pnp4 → <status>
  - ./scripts/check.sh → <status>
  - rg sorry|admit -g*.lean pnp3 pnp4 → <status>
Scope violations: none / <list>
Honest caveats: <list any place where the deliverable falls short of literal task spec>
```

## Operator review process

Each completed task lands as one PR to `main`. Operator:

1. Reads the PR description and verifies the acceptance checklist.
2. Spot-checks the Lean signatures match the task file.
3. Runs `lake build PnP3 Pnp4` and `./scripts/check.sh` locally if CI is suspect.
4. Either merges or requests specific changes (no scope drift).
5. Closes any sibling/duplicate PRs with comment crediting unique strengths.

Target: 1-2 tasks merged per operator-day during active dispatch.

## What this phase does NOT do

* No P-vs-NP proof.
* No `ResearchGapWitness.dagSeparation` construction.
* No new endpoint or final theorem.
* No claim that magnification reaches a strong enough lower bound on its own.

Phase 1 is **strictly infrastructure**. Its value is enabling future research by making formal what is currently markdown-only.

## Re-dispatch / failure protocol

If you cannot complete your task within scope (e.g., the Lean implementation requires forbidden constructs, the literature reference is wrong, the deliverable is more ambitious than estimated):

1. Write a **structured failure report** at `seed_packs/phase1_20engineer_parallel_dispatch/failures/E<NN>_<your-handle>.md`.
2. The report has four sections:
   - **What was attempted.**
   - **Where it broke.** (Lean error verbatim, or precise prose obstruction.)
   - **Local vs global obstruction.** (Local = another engineer might succeed; Global = task as specified is impossible.)
   - **What an integrator must know.** (Recipe for redispatching or pivoting.)
3. PR the failure report only. Operator decides on redispatch or pivot.

## Cross-references

* `RESEARCH_CONSTITUTION.md` — overarching discipline.
* `seed_packs/first_move_search_2026/reports/fp3b_epoch_strategic_retrospective_claudeopus.md` — context for why this phase exists.
* `seed_packs/polynomial_time_formalism_scoping_D0/reports/D0_four_way_review_and_synthesis_claudeopus.md` — context for E19/E20.
* `seed_packs/phase1_20engineer_parallel_dispatch/COMMON_WORKER_INSTRUCTIONS.md` — your required reading.

## Status header

```
Phase: 1
Engineers: 20 (parallel)
Estimated wall-clock to complete: 4-8 weeks
Operator review load: ~20 PRs, ~15 min each = ~5 operator-hours total
Outcome: kill-machine + magnification infrastructure complete, ready for Phase 2
```
