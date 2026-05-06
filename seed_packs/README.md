# Seed packs — Research Governance v0.1, Autoresearch MVP-5

A **seed pack** is a self-contained research task description
suitable for a single parallel-search worker (manual or LLM).  It
specifies:

* the goal of the task (one sentence);
* the scope and forbidden-zone (what the worker MAY and MAY NOT
  touch);
* the success criteria, in the form of executable checks where
  possible;
* pointers to the relevant Constitution rules, registry entries,
  audit modules, and prior NoGoLog entries;
* the expected output shape (Lean artifacts, NoGoLog entries,
  `outputs/attempts.jsonl` rows, etc.).

Seed packs are **NOT** candidate packages.  A candidate package
lives under `pnp3/Candidates/<id>/` and is the result of a worker
*successfully* completing one or more seed packs.  A seed pack is
the *brief*, not the *artifact*.

## Directory layout

```
seed_packs/
  README.md                          ← this file
  <seed_pack_id>/
    README.md                        ← brief + scope + success criteria
    [extra files specific to the pack, e.g. Lean snippets]
```

Every seed pack id must be lowercase ASCII with underscores, and
must be referenced by the `seed_pack_id` field of any
`outputs/attempts.jsonl` entry that responds to the pack.

## Worker protocol

See `seed_packs/PILOT_WAVE_0_PROTOCOL.md` for the step-by-step
minimum-viable cycle every Pilot Wave 0 worker must follow.

## Active seed packs

### Research seeds (under `seed_packs/<id>/`)

| ID                                    | Track       | Status                                |
| ------------------------------------- | ----------- | ------------------------------------- |
| `fp3b1_log_width_hardwiring`          | Research-A  | skeleton-shipped; FP-3b.2 prefix-AND specialisation closed via `_lift` |
| `fp3b1_log_width_hardwiring_lift`     | Research-A  | shipped (prefix-AND only) — `NOGO-000003` → `NOGO-000004 status=formalized`; post-review scope-corrected by `NOGO-000005` |
| `fp3b2_arbitrary_logwidth_tt_payload` | Research-A  | shipped — `NOGO-000005` → `NOGO-000006 status=formalized`; full arbitrary all-essential `ttFormula` payload obstruction |
| `fp3b4_support_cardinality_barrier`   | Research-A  | OPEN (priority 1) — meta-barrier theorem generalising NOGO-000006 to any support-cardinality-only filter; 6 slots; target `NOGO-000007` |
| `fp3b3_provenance_filter_v2_design`   | Research-A  | OPEN (priority 2) — four parallel directions (V2-A formula-shape, V2-B cross-length coherence, V2-C bounded incremental info, V2-D rename/provenance signature); two-phase shipping (paper sketch → Lean) |
| `first_move_search_2026`              | Research-A  | OPEN (priority parallel) — structured literature scan for non-obvious "move-one" ideas from adjacent areas; markdown reports only, NOT Lean code; survivors become future seed packs |

### Infrastructure seeds (under `seed_packs/INFRA/<id>/`)

The `INFRA/` subtree mirrors the research-seed format but covers
**control-plane scaling** work toward the v0.3 100K-worker target.
See `seed_packs/INFRA/README.md` for the full listing and phase
status.

Active phases summary:

| Phase | Goal                                          | Status              |
| ----- | --------------------------------------------- | ------------------- |
| A     | Concurrency hardening                         | shipped             |
| B     | Coordinator HTTP service                      | shipped             |
| C     | Worker scratch + distributed build cache      | spec-only (deferred)|
| D     | Generator/Critic role-gate                    | shipped             |
| E     | Telemetry + wave gate                         | shipped             |
| F     | Sharded coordinator + 100K rollout            | spec-only (deferred)|

## Forbidden across all seed packs

Per the Research Constitution:

* **Trust root edits forbidden.**  No worker, regardless of seed
  pack, may edit `pnp3/Complexity/Interfaces.lean`,
  `pnp3/Complexity/PsubsetPpolyInternal/`,
  `pnp3/Magnification/UnconditionalResearchGap.lean`,
  `pnp3/Magnification/FormulaSupportBoundsPartial_fromPipeline_fixedParams`,
  or `ResearchGapWitness`.
* **No `Candidates/` promotion** without a green Verifier+Critic
  cycle.  Seed packs that produce audit-only artifacts under
  `pnp3/Magnification/AuditRoutes/` do NOT trigger
  `pnp3/Candidates/` directories.
* **No bridge / SourceTheorem / final endpoint** is added by a
  seed pack except via an explicit FP-4-style Candidates promotion.
* **No `axiom`, `opaque`, `Fact`, hidden typeclass payload, or
  `sorry`/`admit`** in any committed artifact (Rule 16, Rule 1).
* **JSONL logs are append-only** (Rule 9).  Corrections are new
  entries with `supersedes` pointing to the original.

## Worker output expectations

Each seed pack defines its own concrete acceptance criteria.  At
minimum every worker run produces exactly one
`outputs/attempts.jsonl` entry, regardless of whether the run
succeeds or fails:

```jsonl
{"id": "ATT-NNNNNN", "candidate_id": "<seed_pack_id-or-candidate_id>",
 "method_family": "<MethodFamily>", "seed_pack_id": "<seed_pack_id>",
 "verifier_status": "PASS|FAIL|PASS_SHAPE_ONLY",
 "critic_status": "not_run|pass|fail", ...}
```

If a worker run produces a Critic report, a `critic_report.md` file
following `spec/critic_protocol.md` MUST also be written and
referenced by the attempts.jsonl line.
