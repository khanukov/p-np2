# v0.4.2 Track B0 — Baseline Verification Report

Read-only preflight, executed 2026-05-05 on
`claude/research-governance-phase0-lmZBP`.

## Repository state

* HEAD: `3b60d97fda2e7e226ef0d01ab22c67ed5f71c25a` (matches one of
  the v0.3 commit chain cited by the plan; the audit's
  `44f253c…1632316` observation appears to be from a different
  point in time and does not contradict the current branch state).
* Branch: `claude/research-governance-phase0-lmZBP` (correct).

## Pipeline status

* `./scripts/check.sh` — 17/17 + sub-steps 12.b/d/e/f/g GREEN.
* `python3 ./coordinator/test_coordinator.py` — all e2e cases
  passed (including `/v1/release then /v1/result -> 409`).
* `python3 ./coordinator/test_role_gate.py` — 4/4.
* `python3 ./coordinator/test_wave_gate.py` — 4 wave-gate +
  metrics cases passed.

## Findings that change v0.4.2 scope

### Already-shipped work (skip in v0.4.2)

1. **`POST /v1/release` endpoint** — already in
   `coordinator/server.py:154-155` with `_handle_release` at
   line 563.  `released` is already a valid assignment state
   (`coordinator/store.py:29, 43`).  Track B5 in the plan is
   redundant; the new B work is only the git-pinning part plus
   wiring the worker pre-check to call the existing
   `/v1/release`.

2. **FP-2 NoGo theorem** — already proved as
   `NoGo_FixedParamsRoute_with_OverbroadUniformProvenance` in
   `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean:155`,
   re-exporting
   `Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.false_of_fixedParams_and_uniformProvenance`
   (helper at
   `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean:532`).

3. **FP-2 NoGoLog entry** — already
   `outputs/nogolog.jsonl::NOGO-000001` with
   `status="formalized"`, citing the theorem above as
   `formal_witness`.  `NOGO-000002` (alternating-slice, refuted
   by NOGO-000003) and `NOGO-000003` (log-width hardwiring,
   `status="needs_review"`) are also already in place.

**Track A-FP2 is therefore unnecessary work and is dropped from
v0.4.2.**  Anything it would have produced already exists.

### Genuinely missing (still in v0.4.2 scope)

* All git-pinning fields: no occurrence of `git_commit`,
  `git_ref`, or `coordinator_git_*` anywhere in `coordinator/`,
  `scripts/`, or `spec/`.
* C-track infrastructure: `coordinator/cost_budget.py`,
  `coordinator/critic_dispatcher.py`,
  `coordinator/promotion_evaluator.py` — none exist.
  `FAIL_TIMEOUT`, `lease_id`, `generator_principal_id`,
  `principal_id` — none in source.

### Other notes

* The audit's claimed proof helper
  `false_of_fixedParams_and_uniformProvenance` exists exactly
  where expected.
* Existing FP-3 / FP-3b research artifacts in
  `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean` are
  more advanced than v0.4.2 anticipated; A-FP2's "fallback
  Prop-target" form would have been a regression.

## Revised v0.4.2 execution plan

* Track B0 — DONE (this report).
* Track B — git-pinning ONLY; B5 (release endpoint creation)
  collapses into "wire worker pre-check to existing
  `/v1/release`".
* Track A-FP2 — SKIPPED (already shipped pre-v0.4.2).
* Track A-CL0 — proceed as planned.
* Tracks C2 / C3 / C4 / C5 — proceed as planned.

Baseline is GREEN.  v0.4.2 may proceed.
