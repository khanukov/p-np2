# Worker roles — Research Governance v0.1, MVP-0.4 (Phase D)

This spec defines the three worker roles in the Autoresearch
control plane and the **infrastructure-level** rules that enforce
Rule 12 (Generator/Critic separation) of the Research Constitution.

Until MVP-0.4, Rule 12 was enforced at the protocol level only:
the worker checklist in `seed_packs/PILOT_WAVE_0_PROTOCOL.md`
forbade the same worker from playing both roles, but nothing in
the coordinator stopped a misbehaving worker from doing so.
MVP-0.4 closes that gap.

## 1. Roles

| Role  | Prefix    | Purpose                                                  |
| ----- | --------- | -------------------------------------------------------- |
| `gen` | `gen-*`   | Generator — produces candidate `proof.lean`, `manifest.toml`, `sketch.md`, `barrier_certificate.md`, `self_attack.md`.  Submits one `AttemptLedgerEntry` per cycle with `critic_status="not_run"`. |
| `crit`| `crit-*`  | Critic — picks a verifier-pass attempt and produces `critic_report.md` per `spec/critic_protocol.md`.  Submits a NEW `AttemptLedgerEntry` with `critic_status ∈ {pass, fail}` and `supersedes` pointing at the gen attempt's `ATT-NNNNNN` id. |
| `rev` | `rev-*`   | Reviewer (human) — out-of-cycle audit / promotion decisions.  Phase D leaves Reviewers unrestricted by role-gate; their work is governed by the worker checklist + PR review process. |

The `worker_id` itself is a free-form string after the prefix:

```
gen-alice                       OK
gen-alice@worker.example         OK
gen-llm-claude-opus-4-7-x-12345  OK
crit-bob                         OK
gen-rule12-2026-05-03-001        OK
```

Regex (enforced by `coordinator/schema.py::WORKER_ID_RE`):

```
^(gen|crit|rev)-[a-z0-9_-]{1,64}$
```

## 2. Rule 12 enforcement matrix

The coordinator evaluates these rules on every `POST /v1/result`
via `coordinator/role_gate.py::enforce_role_for_submission`.  Each
rule that fails returns HTTP 403 with the rule citation in the
error body.

### 2.1 `role = gen`

| # | Rule                                                                  |
| - | --------------------------------------------------------------------- |
| G1 | `attempt.critic_status` MUST equal `"not_run"`.                       |
| G2 | `attempt.supersedes` MUST be absent or null.                          |

A Generator does NOT critique.  Its submission is the raw verifier
result of synthesising a candidate; the critic verdict is filed
separately by a Critic worker.

### 2.2 `role = crit`

| # | Rule                                                                  |
| - | --------------------------------------------------------------------- |
| C1 | `attempt.critic_status` MUST be in `{"pass", "fail"}`.                |
| C2 | `attempt.supersedes` MUST be `"ATT-NNNNNN"` of an existing gen attempt. |
| C3 | `worker_id` MUST differ from the `worker_id` recorded for `attempt.supersedes`. |
| C4 | If `attempt.critic_status = "fail"`, `attempt.critic_break_class` MUST be a non-null `FailureClass` enum value. |
| C5 | Standard MVP-0.1.1 cross-field rules apply: `critic_report_path` MUST point at a non-template, completed Critic report whose Verdict's `critic_status` matches `attempt.critic_status`. |

C3 is **the** infrastructure-level Rule-12 enforcement.  The
coordinator looks up the `worker_id` that originally submitted
`attempt.supersedes` (via the `assignments` table) and refuses if
it equals the current submission's `worker_id`.

### 2.3 `role = rev`

No role-gate restrictions.  Reviewers are humans; their actions are
governed by Constitution Rule 0 (no trust-root edits), Rule 9
(append-only ledgers), and the worker checklist.

## 3. Operational notes

### 3.1 Worker rebrand

A worker that previously ran as `gen-alice` and now runs as
`crit-alice` is **TWO distinct `worker_id` strings**.  The
role-gate compares them verbatim.  Therefore:

* `gen-alice` cannot generate AND submit a critic verdict against
  her own ATT — caught directly by C3.
* `crit-alice` (a separately-named worker that happens to share
  the suffix) used to be allowed to critique `gen-alice`'s ATT
  because the literal strings differ.  v0.4.2 Track C3 closes this
  prefix-only bypass by also comparing the **principal id** (the
  suffix after the role prefix); see §3.4.

Operators MUST NOT reuse a worker_id base name across roles.  The
recommended convention is to namespace worker_ids by deployment
identity (e.g. `gen-llm-claude-opus-001`, `crit-llm-claude-opus-002`),
NOT by human author.

### 3.4 Principal identity (v0.4.2 Track C3) — protocol-level integrity, NOT authentication

> **Important.**  Principal identity (extracted from `worker_id`
> suffix) is a *protocol-level integrity guard* for honest,
> coordinated workers.  It is NOT an authentication mechanism.
> Until the deferred Phase C-3 JWT auth track ships, any worker
> can self-declare any `worker_id` and bypass Rule 12 by
> impersonation.  The coordinator does not — and cannot —
> distinguish two distinct principals named `alice` from one
> principal pretending to be both.

Mechanism:

* `principal_id_from_worker_id("gen-alice") == "alice"`.
* On every gen-* `/v1/result` merge the coordinator stamps
  `attempt.generator_principal_id` from the gen worker's principal.
* On every crit-* submission, `role_gate._enforce_crit` rejects
  with 403 if `principal_id_from_worker_id(crit_worker_id)`
  matches the gen worker's principal — i.e. `gen-alice`'s ATT
  cannot be critiqued by `crit-alice`, even though the worker_id
  strings differ.
* The critic auto-dispatcher (Phase E,
  `coordinator/critic_dispatcher.py`) refuses to OFFER a gen
  attempt to a crit worker with a matching principal at task
  issuance time, so honest workers don't waste a lease on a
  doomed submission.

Threat-model boundary: a malicious worker that runs both
`gen-alice` and `crit-alice` can be observed by an external
auditor scanning `outputs/attempts.jsonl`, but the coordinator
itself cannot detect it.  Strong-cryptographic authentication is
deferred to JWT auth.

### 3.2 Generator rate vs Critic rate

Phase D does NOT impose a ratio between Generator and Critic
attempts.  In Pilot Wave 0 the operator runs Critic manually on a
selected subset of `gen` attempts.  Phase E
(`coordinator/critic_dispatcher.py`) will automatically pull
verifier-pass `gen` attempts that lack a critic verdict and assign
them to crit-* workers — at which point the Generator/Critic ratio
becomes a tunable.

### 3.3 Reviewer escalation

When a candidate accumulates `critic_status="pass"` from K
distinct Critic workers (Phase E threshold, `K ≥ 3`), it is
flagged for Reviewer escalation.  Reviewers (rev-*) inspect the
candidate manually and decide promotion vs further critique.

Reviewer outputs are NOT filed via `POST /v1/result`; they go
through PR review and may include `outputs/survivor_history.jsonl`
appends with `final_status="accepted"` or `"refuted"`.

## 4. Forbidden cross-role actions

Beyond what role-gate enforces, every worker MUST NOT:

* edit the trust root (Rule 0);
* edit existing JSONL log entries (Rule 9 — corrections via
  `supersedes` only);
* introduce `class`/`instance`/`Fact`/`opaque`/typeclass-payload
  in candidate-local code (Rule 16);
* promote any guard in `spec/known_guards.toml` to `accepted`
  (Reviewer-only, requires Foundational PR);
* skip the Pilot Wave 0 worker checklist
  (`seed_packs/PILOT_WAVE_0_PROTOCOL.md` §11);
* force-push to the canonical branch.

## 5. Test coverage

`coordinator/test_role_gate.py` exercises seven canonical
Rule-12 cases (four MVP-0.4 + three v0.4.2 Track C3):

1. gen submission carrying `critic_status="pass"` → 403.
2. crit submission carrying `critic_status="not_run"` → 403.
3. gen + crit by the SAME `worker_id` → 403 (Rule 12 reject).
4. gen by `gen-alice` + crit by `crit-bob` → 200 (allowed).
5. `/v1/task` crit dispatcher with empty ledger → 503
   `no_pending_critic`.
6. `/v1/task` crit dispatcher with pending verified gen → 200
   carrying `supersedes=ATT-NNNNNN`.
7. gen by `gen-grace` + crit by `crit-grace` → 403 (principal
   identity guard; v0.4.2 Track C3).

The test is wired into `scripts/check.sh` as Step 12.f and runs
on every CI push.

## 6. Forward compatibility

Phase E will add:

* `coordinator/critic_dispatcher.py::POST /v1/dispatch_critic` —
  pulls one verifier-pass gen attempt with `critic_status="not_run"`
  and assigns to a crit-* worker.  The dispatcher refuses to
  assign to a `worker_id` whose base name matches the gen worker
  (preventing accidental Rule-12 violation by automated
  dispatch).
* `coordinator/wave_gate.py` — gates Critic dispatch on the
  current Wave's worker cap.

Phase F will add:

* sharded coordinator → cross-shard `worker_id` reservation so a
  worker name booked for `gen` cannot be re-issued as `crit`.

The role-gate API in `coordinator/role_gate.py` is stable across
Phase D/E/F; only the dispatcher and gate enforcement layers
above it grow.
