# Infrastructure seed packs

Mirror of the research seed-pack format (`seed_packs/<id>/`) for
**infrastructure** work that scales the autoresearch control plane
toward the v0.3 100K-worker target documented in
`/root/.claude/plans/calm-hopping-shannon.md` and the
`autoresearch_mvp` history block in `spec/version_manifest.toml`.

Each `seed_packs/INFRA/<id>/README.md` is a self-contained brief
for ONE engineer (human or LLM): goal, allowed scope, forbidden
scope, acceptance criteria, dependencies, how-to-test, how-to-ship.
Pick one brief and follow `seed_packs/PILOT_WAVE_0_PROTOCOL.md`'s
worker cycle, treating the brief as the seed pack and the chosen
implementation files as the "candidate" output.

Coordinator-mediated workers DO NOT pull infrastructure briefs from
the coordinator's `/v1/task`; the coordinator only assigns research
candidates.  Infrastructure briefs are picked manually by humans
or by an external task-manager (`autoresearch_mvp` 0.5+).

## Phase status (2026-05-03)

| Phase | Goal                                          | Status              |
| ----- | --------------------------------------------- | ------------------- |
| A     | Concurrency hardening                         | shipped (e87743b)   |
| B     | Coordinator HTTP service                      | shipped (3dfb1de)   |
| C     | Worker scratch + distributed build cache      | DEFERRED            |
| D     | Generator/Critic role-gate                    | shipped (7c221c3)   |
| E     | Telemetry + wave gate                         | shipped (56a95e6)   |
| F     | Sharded coordinator + 100K rollout            | DEFERRED            |

Phase C is **deferred** because it requires a real deployment
context (S3 / object store credentials, multi-host topology) that
isn't available in the current development environment.  Phase F
is deferred because it requires Phase C as a precondition.

## Active INFRA briefs

| ID                          | Phase | Status         |
| --------------------------- | ----- | -------------- |
| `C1_worker_scratch_isolation`     | C     | spec-only      |
| `C2_build_cache_server`           | C     | spec-only      |
| `C3_jwt_auth`                     | C     | spec-only      |
| `C4_per_worker_quota`              | C     | spec-only      |
| `C5_ci_matrix_fanout`             | C     | spec-only      |
| `E_followup_cost_budget`          | E+    | spec-only      |
| `E_followup_critic_dispatcher`    | E+    | spec-only      |
| `E_followup_interesting_stream`   | E+    | spec-only      |
| `F1_sharded_coordinator`          | F     | spec-only      |
| `F2_s3_build_cache`               | F     | spec-only      |
| `F3_kafka_interesting_stream`     | F     | spec-only      |
| `F4_public_catalog_mirror`        | F     | spec-only      |
| `F5_runbook`                      | F     | spec-only      |
| `F6_end_to_end_100k_smoke`        | F     | spec-only      |

A `spec-only` brief means: the brief exists with full goal +
acceptance criteria, but no Lean / Python work has started.  An
engineer who picks up a `spec-only` brief should:

1. Read the brief end-to-end.
2. Read its dependencies (other briefs that must merge first).
3. Branch `worker/INFRA-<id>/<short-name>`.
4. Implement to the brief's acceptance criteria.
5. Open a PR; mention the brief id and the "what did NOT change"
   list.

## Conflict-avoidance rules

* Briefs are scoped to non-overlapping files where possible.
  When two briefs touch the same file, the brief's `Dependencies`
  field declares ordering.
* No infra brief edits the trust root (Rule 0).
* No infra brief mutates existing JSONL log entries (Rule 9).
* Schema bumps coordinate via `spec/version_manifest.toml` and the
  affected file's `[meta].spec_version`.
* `autoresearch_mvp` version is bumped per brief per Phase
  release; the bumping engineer adds the history block.

## What an engineer must NEVER do

(Mirrors `seed_packs/PILOT_WAVE_0_PROTOCOL.md` §"What an engineer
must NEVER do" but for infra-track.)

* Edit the trust root.
* Promote `ProvenanceFilter_v1` or any informal guard to
  `accepted`.
* Mutate existing JSONL log entries.
* Make a `gen-*` worker submit a critic verdict, or vice versa
  (Rule 12).
* Introduce `class`/`instance`/`Fact`/`opaque`/typeclass-payload
  in candidate-local code (Rule 16).
* Disable any `scripts/check.sh` step "to make CI green".
* Force-push the canonical branch.
* Skip the Pilot Wave 0 worker checklist when shipping work that
  goes through the coordinator (research seed packs).
