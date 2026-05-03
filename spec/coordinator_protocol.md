# Coordinator HTTP protocol — Research Governance v0.1, MVP-0.2

This document is the wire contract for the Autoresearch coordinator
service.  Workers (Generator, Critic, Reviewer) communicate with the
coordinator over HTTP/JSON.  The coordinator is the **single writer**
to the canonical append-only ledgers under `outputs/`; workers never
write to those files directly.

The protocol is intentionally minimal in MVP-0.2 (Phase B): no
authentication, no quota, no metrics endpoint.  Phase C adds JWT
auth and per-worker quota; Phase D adds Generator/Critic infra-level
separation; Phase E adds metrics and wave gates; Phase F shards the
coordinator.  Each later phase preserves the contract below as a
strict subset.

## 0. Conventions

* Request/response bodies are JSON, UTF-8.
* All timestamps are ISO 8601 UTC with `Z` suffix.
* HTTP status codes are RFC 7231; the coordinator NEVER returns a
  redirect.
* Errors carry the shape `{"ok": false, "error": "<human message>"}`.
* All identifiers match a fixed regex; see §1.

## 1. Identifiers

| Field           | Pattern                                  | Source                  |
| --------------- | ---------------------------------------- | ----------------------- |
| `worker_id`     | `^(gen\|crit\|rev)-[a-z0-9_-]{1,64}$`    | worker startup config   |
| `assignment_id` | `^ASN-[0-9]{6}$`                         | coordinator             |
| `candidate_id`  | `^[a-z0-9][a-z0-9_-]{0,127}$`            | coordinator             |
| `attempt_id`    | `^ATT-[0-9]{6}$`                         | `attempts_append.py`    |
| `nogolog_id`    | `^NOGO-[0-9]{6}$`                        | `nogolog_append.py`     |
| `seed_pack_id`  | name of a directory under `seed_packs/`  | filesystem              |
| `content_hash`  | 64-char lowercase hex (sha256)           | `coordinator/dedup.py`  |

The `worker_id` prefix is the role marker:

* `gen-*` — Generator worker (produces candidate proof.lean +
  manifest).
* `crit-*` — Critic worker (produces critic_report.md per
  `spec/critic_protocol.md`).
* `rev-*` — Reviewer (human; rarely automated).

`GET /v1/task` enforces that `worker_id` starts with the requested
`role` prefix; mismatch yields 403.

## 2. Endpoints

### 2.1 `GET /v1/health`

Liveness probe.  Always returns 200 when the coordinator is running.

Response:

```json
{
  "status":                     "ok" | "draining" | "shutdown",
  "coordinator_version":        "0.2.0",
  "autoresearch_mvp_version":   "0.1.5",
  "current_wave":               0,
  "assigned_count":             <int>,
  "completed_count":            <int>,
  "abandoned_count":            <int>
}
```

`current_wave` is `0` in MVP-0.2 (Phase E populates it from
`coordinator/wave_gate.py`).  `assigned_count` is the live
in-progress lease count.

### 2.2 `GET /v1/manifest`

Returns the contents of `spec/version_manifest.toml` verbatim.  Used
by workers to discover the coordinated snapshot of spec versions.
Content-Type: `application/toml`.

### 2.3 `GET /v1/task?role=…&worker_id=…&seed_pack=…&lease_seconds=…`

Issues one task lease.  All four query parameters are
URL-encoded strings.  `seed_pack` is optional; if absent, the
coordinator round-robins over `seed_packs/<id>/`.  `lease_seconds`
is optional; clamped to `[30, 7200]` (default 1800).

200 response:

```json
{
  "assignment_id":  "ASN-000123",
  "candidate_id":   "fp3b1_log_width_hardwiring_a1b2c3d4e5f6",
  "seed_pack_id":   "fp3b1_log_width_hardwiring",
  "role":           "gen",
  "worker_id":      "gen-test-001",
  "lease_seconds":  1800,
  "deadline":       "2026-05-03T14:30:00Z"
}
```

Errors:

| Code | When                                                        |
| ---- | ----------------------------------------------------------- |
| 400  | Missing/malformed query parameter                           |
| 403  | `worker_id` prefix does not match `role`                    |
| 404  | `seed_pack` does not exist                                  |
| 503  | No seed packs available                                     |

### 2.4 `GET /v1/dedup?content_hash=…`

Look up whether a content-hash has already been attempted.  Useful
for workers that compute their hash before requesting a task.

200 response (unseen):

```json
{
  "content_hash":           "<hex>",
  "seen":                   false,
  "first_assignment_id":    null
}
```

409 response (seen):

```json
{
  "content_hash":           "<hex>",
  "seen":                   true,
  "first_assignment_id":    "ASN-000042"
}
```

`content_hash` is computed by `coordinator/dedup.py`:

* `gen-*`: `sha256("gen" || sep || seed_pack_id || sep || sketch.md ||
  sep || manifest.toml || sep || proof.lean)`.
* `crit-*`: `sha256("crit" || sep || attempt_id || sep ||
  template-stripped critic_report.md)`.

The `sep` byte is `0x1e` (record separator).

### 2.5 `POST /v1/result`

Submit one cycle's result.  Body shape:

```json
{
  "assignment_id":  "ASN-000123",
  "worker_id":      "gen-test-001",
  "attempt": {
      ...AttemptLedgerEntry per spec/nogolog_schema.json...
  },
  "nogolog_entry":  { ...NoGoLogEntry... } | null,
  "survivor_entry": { ...SurvivorHistoryEntry... } | null
}
```

The coordinator:

1. Verifies `assignment_id` exists and is in status `assigned`.
2. Verifies `worker_id` matches the lease holder.
3. Overwrites `attempt.candidate_id` with the assignment's
   `candidate_id` so a worker cannot fabricate.
4. Calls `scripts/attempts_append.py` to validate + append
   atomically (the Phase A flock primitive applies).
5. If `nogolog_entry` is present, calls
   `scripts/nogolog_append.py` similarly.
6. If `survivor_entry` is present, calls
   `scripts/survivor_append.py` similarly.
7. Marks the assignment `submitted` with the new `attempt_id`.

200 response:

```json
{
  "ok":            true,
  "assignment_id": "ASN-000123",
  "attempt_id":    "ATT-000456",
  "nogolog_id":    "NOGO-000007" | null,
  "survivor_msg":  "[survivor_append] OK..." | null
}
```

Errors:

| Code | When                                                        |
| ---- | ----------------------------------------------------------- |
| 400  | Body parse error / missing fields / attempt fails validation|
| 403  | Wrong `worker_id` for this assignment                       |
| 404  | Unknown `assignment_id`                                     |
| 409  | Assignment is not in status `assigned` (already submitted, expired, or released) |
| 500  | Attempt merged but auxiliary log (NoGo/survivor) rejected   |

### 2.6 `POST /v1/release`

Cancel an assignment without submitting.  Body shape:

```json
{
  "assignment_id":  "ASN-000123",
  "worker_id":      "gen-test-001"
}
```

200 response if the lease was successfully released; 409 otherwise
(already submitted, expired, or never existed).

## 3. Lease state machine

```
              create_assignment
                     │
                     ▼
                 assigned
                /    │    \
        POST     POST  deadline
        /result  /release passed
           │        │       │
           ▼        ▼       ▼
       submitted  released  expired
       (final)    (final)   (final)
```

Once a lease leaves `assigned`, no further transitions are allowed.
The coordinator MAY allocate a NEW lease for the same
(seed_pack_id, candidate_id) after the previous one expires; the
new lease gets a fresh `assignment_id`.

## 4. Single-writer ledger guarantee

The coordinator runs on ONE process per host.  All canonical-ledger
writes go through `scripts/attempts_append.py` /
`nogolog_append.py` / `survivor_append.py`, which hold an
`fcntl.flock(LOCK_EX)` on the matching `outputs/<name>.jsonl.lock`
sibling lockfile (Phase A contract; see `spec/concurrency_model.md`).

A direct write to `outputs/*.jsonl` from outside this protocol is a
contract violation.  No worker, neither Generator nor Critic, may
bypass `POST /v1/result`.

## 5. State persistence

The coordinator stores assignments and dedup entries in
`coordinator/state.db` (SQLite, WAL mode).  The DB file is gitignored;
it carries no canonical content.  Loss of the DB means abandoning
in-progress leases and re-deriving dedup state from
`outputs/attempts.jsonl`.

Future phases:

* Phase C: per-worker JWT auth on every endpoint.
* Phase D: server-side enforcement that the same `worker_id` cannot
  generate AND criticise the same `candidate_id`
  (`coordinator/role_gate.py`).
* Phase E: `GET /v1/metrics` (Prometheus exposition);
  `coordinator/wave_gate.py` populates `current_wave` from
  `spec/wave_gate_thresholds.toml` and refuses `/v1/task` beyond the
  current wave's worker cap.
* Phase F: sharded coordinator behind a consistent-hash load
  balancer; SQLite replaced by Postgres or equivalent.

## 6. Forbidden coordinator actions

The coordinator does NOT:

* Edit existing JSONL entries (Rule 9 — corrections are new entries
  with `supersedes`).
* Edit the trust root (Rule 0).
* Promote any guard in `spec/known_guards.toml` to `accepted`.
* Run Lean (no `lake build` from the coordinator process).
* Touch `pnp3/Candidates/<real-id>/` files.
* Issue assignments outside the `seed_packs/` registry.
* Generate `attempt_id` itself — that's the responsibility of
  `scripts/attempts_append.py`'s flocked critical section.

## 7. Worker checklist (interaction with this protocol)

Per `seed_packs/PILOT_WAVE_0_PROTOCOL.md` §11, every worker run MUST:

1. `GET /v1/task` to obtain an `assignment_id` (no manual seed-pack
   selection in coordinator-mediated mode).
2. Run the cycle locally.
3. `POST /v1/result` with the AttemptLedgerEntry payload.
4. NEVER write directly to `outputs/*.jsonl`.
5. NEVER fabricate a `candidate_id` — use the one returned by
   `/v1/task`; the coordinator overwrites it on submission anyway,
   but workers must not pretend to control it.
