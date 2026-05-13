# INFRA-E follow-ups: deferred Phase E components

> **Phase:** E follow-up (post-MVP-0.5).
> **Status:** spec-only.
> **Depends on:** Phase E shipped (56a95e6).

Three components from the original Phase E plan that were
intentionally deferred from MVP-0.5 because they're either
stub-only without real workers or depend on unbuilt infrastructure.

## E1 — `coordinator/cost_budget.py`

**Goal.** Per-attempt CPU-minute budget with auto-FAIL_TIMEOUT.

**Brief.** When a worker requests `/v1/task` with a `role` and
`seed_pack`, the coordinator embeds a per-attempt CPU-minute
budget in the assignment.  The worker passes the budget to
`scripts/verify_candidate.sh --stage-timeout <budget * 60>`.  On
timeout, `verify_candidate.sh` writes a partial JSON with
`status="ABNORMAL_EXIT"` (Phase A's MVP-0.1.6 trap), and
`scripts/run_worker.sh` submits with `verifier_status="FAIL"`,
`verifier_failure_class="reproducibility_failure"` (the closest
allowed `FailureClass` enum value; if a more specific class is
needed it must be added to `spec/nogolog_schema.json`).

**Default budgets.** Read from `spec/cost_budget_thresholds.toml`:

```toml
[role.gen]
default_minutes = 30
hard_cap_minutes = 60

[role.crit]
default_minutes = 10
hard_cap_minutes = 20
```

**Acceptance.** new `coordinator/test_cost_budget.py` exercises
overrun → FAIL_TIMEOUT path.  `scripts/check.sh` Step 12.j.

## E2 — `coordinator/critic_dispatcher.py`

**Goal.** Auto-pull verifier-pass attempts lacking a critic
verdict, assign to crit-* workers.

**Brief.** Today, `crit-*` workers manually pass
`supersedes=ATT-NNNNNN` in their submission.  The dispatcher
inverts this: when `crit-*` calls `/v1/task` without a specific
`seed_pack`, the coordinator pulls one verifier-pass attempt
where `critic_status="not_run"` and the requesting worker did
NOT generate it (Rule 12 prevention even before role-gate).

**Endpoint shape:**

```
GET /v1/task?role=crit&worker_id=crit-bob
```

returns:

```json
{
  "assignment_id": "ASN-...",
  "candidate_id":  "...",
  "seed_pack_id":  "...",
  "role":          "crit",
  "worker_id":     "crit-bob",
  "supersedes":    "ATT-000123",
  "lease_seconds": 600,
  "deadline":      "..."
}
```

The `supersedes` field is new on the `TaskAssignment` shape; it
tells the Critic which gen attempt to critique.

**Acceptance.** `coordinator/test_critic_dispatcher.py` 6 cases
(no pending → 503, one pending → 200, gen-alice + crit-alice
get-task is refused, gen-alice + crit-bob get-task succeeds,
post-result merges supersedes correctly, dispatcher ignores
already-superseded gen attempts).

## E3 — `coordinator/interesting_stream.py`

**Goal.** Read-only stream of Critic-pass survivors for human
review.

**Brief.**

```
GET /v1/interesting?since=ATT-000050&limit=20
```

returns the last N AttemptLedgerEntries with `critic_status="pass"`
in the canonical ledger after `since`, in monotonic order.  Used
by the Phase F "nightly survivor promotion" pipeline + by humans
auditing recent passes.

**Acceptance.** `coordinator/test_interesting_stream.py` 4 cases
(empty stream, populated stream, since filter, limit cap).

These three follow-ups are independent of one another; pick any
one.  Each ships its own brief in
`seed_packs/INFRA/E_followup/<sub_id>/README.md` if more detail
is needed during implementation.
