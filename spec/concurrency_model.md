# Concurrency model — Research Governance v0.1, Autoresearch MVP-0.1.8

This document specifies the **concurrency contract** of the
autoresearch infrastructure: which scripts are safe to invoke from
N parallel workers on one machine, which require a per-worker
scratch directory, and which must be mediated by the (later-phase)
Coordinator service.

The contract is the substrate that lets Phase B (`coordinator/`)
and beyond assume consistent behaviour.  Without this document, an
engineer cannot tell whether a script is safe to run in parallel
without re-deriving it from source.

## 1. Categories

Every script under `scripts/` falls into one of four categories:

| # | Category                       | Parallel-safe?         | Per-worker scratch?       | Mediation required? |
| - | ------------------------------ | ---------------------- | ------------------------- | ------------------- |
| 1 | Read-only (validators)         | YES                    | not needed                | none                |
| 2 | Per-candidate writers          | YES (worker-scoped)    | YES (`VERIFY_TMP_DIR`)    | none                |
| 3 | Append-only ledger writers     | YES via fcntl.flock    | not needed                | shares lockfile     |
| 4 | Coordinator-mediated (Phase B) | YES                    | YES                       | YES (HTTP)          |

The MVP-0.1.8 hardening (this document's primary subject) brought
categories 2 and 3 to "YES" by:

* category 3: `attempts_append.py` / `nogolog_append.py` /
  `survivor_append.py` wrap their critical sections in
  `fcntl.flock(LOCK_EX)` on a sibling lockfile
  (`outputs/<log>.jsonl.lock`);
* category 2: `verify_candidate.sh` writes all per-stage logs into
  a per-worker `${VERIFY_TMP_DIR}` directory unique per (PID,
  RUN_UUID) and cleaned up on EXIT;
* `test_underscore_policy.sh` and `test_rule16_negative.sh` use
  UUID-suffixed staging dirs to avoid PID-reuse collisions in
  containerised environments.

## 2. Per-script disposition

| Script                                 | Cat | Notes                                                                |
| -------------------------------------- | --- | -------------------------------------------------------------------- |
| `validate_jsonl.py`                    | 1   | read-only against three JSONL files                                  |
| `validate_critic_report.py`            | 1   | read-only                                                            |
| `validate_version_manifest.py`         | 1   | read-only                                                            |
| `audit_bootstrap.sh`                   | 1   | read-only; writes only to `mktemp -d`                                |
| `attempts_append.py`                   | 3   | flock on `outputs/attempts.jsonl.lock` (MVP-0.1.8)                   |
| `nogolog_append.py`                    | 3   | flock on `outputs/nogolog.jsonl.lock` (MVP-0.1.8)                    |
| `survivor_append.py`                   | 3   | flock on `outputs/survivor_history.jsonl.lock` (MVP-0.1.8)           |
| `verify_candidate.sh`                  | 2   | per-worker `${VERIFY_TMP_DIR}` (MVP-0.1.8); EXIT trap cleans up      |
| `check_candidate_kernel.sh`            | 2   | per-candidate; uses `lake env lean` (see §4 build-cache)             |
| `check_barrier_certificate.sh`         | 2   | per-candidate read-only                                              |
| `check_source_theorem_size.sh`         | 2   | per-candidate read-only                                              |
| `check_candidate_rule16.sh`            | 2   | scans `pnp3/Candidates/`; safe under fresh dirs                      |
| `check_doc_honesty.sh`                 | 1   | read-only over pnp3/, pnp4/                                          |
| `check_typeclass_payload_quarantine.sh`| 1   | read-only                                                            |
| `check_refuted_route_quarantine.sh`    | 1   | read-only                                                            |
| `check_refuted_predicate_usage.sh`     | 1   | read-only                                                            |
| `check_target_lock.sh`                 | 1   | read-only                                                            |
| `run_smoke_probes.sh`                  | 2   | uses `${staging_path}` from per-probe config; PID-suffixed temp dirs |
| `test_attempts_validator.sh`           | 1   | read-only against synthetic temp jsonl                               |
| `test_underscore_policy.sh`            | 2   | UUID-suffixed staging (MVP-0.1.8)                                    |
| `test_rule16_negative.sh`              | 2   | UUID-suffixed staging (MVP-0.1.8)                                    |
| `test_concurrency_safety.sh`           | 2   | spawns N=16 ledger writers against a stub repo (MVP-0.1.8)           |

## 3. Locking primitives (Category 3 detail)

Every Category-3 writer follows the same template:

```python
import fcntl
LOG_PATH  = ROOT / "outputs" / "<name>.jsonl"
LOCK_PATH = ROOT / "outputs" / "<name>.jsonl.lock"

LOCK_PATH.touch(exist_ok=True)
with LOCK_PATH.open("a+", encoding="utf-8") as lockf:
    fcntl.flock(lockf.fileno(), fcntl.LOCK_EX)
    try:
        # 1. re-scan max id INSIDE the lock
        # 2. validate the entry
        # 3. append to LOG_PATH
    finally:
        fcntl.flock(lockf.fileno(), fcntl.LOCK_UN)
```

Invariants:

* **Read max-id INSIDE the lock.**  Reading the file before
  acquiring the lock would re-introduce the race that
  `_scan_max_id` was meant to close.
* **One lockfile per ledger file.**  Sharing a lockfile across
  ledgers (e.g. one global `outputs/.lock`) would serialise
  unrelated writes; conversely, multiple lockfiles per ledger
  would not serialise at all.
* **The lockfile is `.gitignore`d.**  It carries no canonical
  content; it exists only as a kernel handle for `flock`.
* **`LOCK_EX` is an advisory lock**, not mandatory.  Code paths
  that WRITE to the JSONL files MUST go through these scripts;
  a future direct-write script would silently bypass the lock.
  The discipline is enforced by code review and by
  `seed_packs/PILOT_WAVE_0_PROTOCOL.md` §11 (worker checklist
  forbids direct ledger edits).

## 4. Build-cache contract (deferred to Phase C)

`lake build PnP3 Pnp4` writes to `.lake/build/`, which is a
**single shared directory**.  Two workers running `lake build`
simultaneously can corrupt each other's artifacts.

**Phase A (this MVP) does NOT solve this.**  It is documented
here so engineers know:

* In Phase A, only ONE `verify_candidate.sh` invocation per host
  may run `lake build` at a time.  Schedule serially via
  `flock /tmp/lake.lock -c '...'` in worker drivers.
* In Phase B, the Coordinator assigns one candidate per worker
  but does NOT yet provide build-cache isolation.
* In Phase C (`scripts/worker_bootstrap.sh`), each worker gets
  its own `${WORKER_SCRATCH}/.lake/` directory bootstrapped from
  a content-addressed tarball (`coordinator/build_cache.py`).
  At that point `lake build` is parallel-safe across workers.

Until Phase C ships, scaling beyond ~10 simultaneous
`verify_candidate.sh` runs on one host is unsafe.

## 5. Coordinator-mediated calls (Phase B+ preview)

In Phase B, the following calls move from local-script to
HTTP-mediated:

* **Task assignment.**  `coordinator/server.py::GET /v1/task` is
  the only path by which a worker learns which seed pack /
  candidate id to attempt.  The Coordinator handles
  content-addressed dedup and lease management; no local script
  performs this.
* **Result submission.**  `coordinator/server.py::POST /v1/result`
  is the only path by which a worker registers an attempt's
  outcome.  The Coordinator runs `validate_attempt` server-side
  and atomically appends to the canonical `outputs/attempts.jsonl`.
  Worker-side direct writes are forbidden.
* **NoGoLog appends.**  Inside `POST /v1/result` when
  `critic_status="fail"`, the Coordinator additionally appends a
  NoGoLog entry.  Worker-side direct `nogolog_append.py` is
  permitted only for governance / audit work outside the
  worker-cycle path.

The Phase A flock contract continues to hold inside the
Coordinator: when the Coordinator writes the canonical ledger, it
uses the same `attempts_append.py` / `nogolog_append.py`
machinery, just from a single process instead of N parallel ones.
Phase A is therefore the substrate for Phase B, not a separate
design.

## 6. What an engineer doing async parallel work must know

If you are building infrastructure (Phase B–F):

* You may rely on Categories 1, 2, 3 above being parallel-safe on
  one machine within the limits documented here.
* You may NOT rely on `lake build` being parallel-safe across
  workers on the same host until Phase C; serialise via
  `flock /tmp/lake.lock`.
* If you add a new ledger file, it MUST follow the Category 3
  template (sibling lockfile, `_scan_max_id` inside the lock,
  `.gitignore` entry).
* If you add a new shared-state path (any file outside
  per-worker scratch), document it here under §2 with a category
  classification, and either add it to the Phase A flock pattern
  or to a Phase B Coordinator endpoint.

If you are running research-side work (a seed pack worker):

* You do NOT need to think about concurrency.  The protocol at
  `seed_packs/PILOT_WAVE_0_PROTOCOL.md` already constrains you to
  one cycle at a time per worker, and the scripts you invoke are
  Category-2-safe.
* When in doubt: read this document's §2 table and confirm the
  script you're invoking is Category 1, 2, or 3.
