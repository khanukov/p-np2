# INFRA-F: 100K-scale rollout

> **Phase:** F.
> **Status:** spec-only.
> **Depends on:** Phase A + B + D + E shipped; Phase C scratch +
> build cache shipped (INFRA-C1, INFRA-C2, INFRA-C3, INFRA-C5);
> Phase E follow-ups (cost_budget, critic_dispatcher,
> interesting_stream).
> **Mvp version target:** `autoresearch_mvp = 1.0.0`.

Phase F is the final integration: actually running 100K parallel
workers.  This phase is mostly glue + ops; the safety-critical
research-side rules are already enforced by Phase A–E.  Phase F's
risk profile is operational (deployment, monitoring, recovery)
rather than mathematical.

The five F-briefs below are independent.  Pick any one.

## INFRA-F1: sharded coordinator

**Goal.** N>1 coordinator instances behind a consistent-hash load
balancer.

**Brief.**
* Replace `coordinator/state.db` (SQLite) with Postgres or
  equivalent; each coordinator instance shares the same backend.
* Hash assignments by `worker_id` so a worker always reaches the
  same shard.
* Keep `attempts_append.py`-style flock on a per-shard basis
  (each shard has its own per-shard `outputs/<shard>/attempts.jsonl`
  + a nightly merge to canonical).
* Ledger reconciliation: nightly job aggregates per-shard JSONL
  into `outputs/attempts.jsonl` (still append-only, still
  fcntl.flock).

**Acceptance.** 4 coordinator shards behind nginx/HAProxy serve
1K workers each (4K total) with no cross-shard duplicate
ATT-NNNNNN.  Nightly merge produces a canonical ledger with
4 × 1K = 4K entries.

## INFRA-F2: S3-backed build cache

**Goal.** Replace `coordinator/build_cache.py`'s local-disk
storage with S3 / GCS / equivalent.

**Brief.**
* Workers fetch tarballs via signed URL (no shared credentials).
* Coordinator writes new tarballs via `boto3` or equivalent.
* Multi-region edge cache (CDN) for read latency.

## INFRA-F3: Kafka / Pub/Sub interesting stream

**Goal.** Replace `coordinator/interesting_stream.py`'s direct
ledger query with a Kafka topic / Pub/Sub channel.

**Brief.**
* Every successful `POST /v1/result` produces one Kafka message
  on topic `autoresearch.attempts`.
* A consumer (the survivor-promotion pipeline) reads the topic,
  filters `critic_status="pass"`, files Reviewer tickets.
* Ledger remains the canonical source of truth; Kafka is a
  notification stream, not a replacement.

## INFRA-F4: public catalog mirror

**Goal.** A read-only public mirror of
`outputs/attempts.jsonl` + `outputs/nogolog.jsonl` for academic
transparency.

**Brief.**
* Static-file serving via S3/CloudFront (or GitHub Pages of a
  separate read-only repo).
* Hourly sync from canonical ledgers.
* No PII (worker_ids are pseudonymous already).

## INFRA-F5: docs/runbook.md

**Goal.** Operational runbook for the live coordinator.

**Brief.**
* Sections:
    1. How to start the coordinator.
    2. How to provision workers.
    3. How to read metrics + dashboards.
    4. How to promote Wave-N → N+1 (operator decision +
       env-var restart).
    5. How to handle each common failure mode (Critic queue
       backed up, NoGoLog flood, ledger corruption recovery,
       false-pass alarm).
    6. Incident response: who to page, what to do first.
* Each section has a concrete "if this happens, run X".

## INFRA-F6: end-to-end 100K smoke

**Goal.** Synthetic 100K cycles in a staging cluster proving the
pipeline works at scale.

**Brief.**
* `scripts/end_to_end_100k_smoke.sh` (or `.py`) — spawns N=100K
  parallel synthetic workers in a single test, against a real
  sharded coordinator + S3 cache, completes in ≤24h wall-time.
* Asserts: no duplicate `attempt_id`, no Rule-12 violation, no
  ledger corruption, wave gate auto-promotes through 0→1→2→3→4.
* Drives Wave 4 (cap=100K) once promotion_requirements per
  `spec/wave_gate_thresholds.toml::waves.4.promotion_requirements`
  are met.

When all five F-briefs ship + e2e 100K smoke passes, the project
is in **MVP-1.0**: real autoresearch at full scale.  At that
point the Pilot Wave 0 protocol's "Autoresearch full-scale" gate
(currently NO-GO) flips to GO.

## Final note

100K-worker autoresearch is **infrastructure-complete** when
Phase F merges.  It is **research-complete** only when an actual
candidate Π survives the cycle and proves
`ResearchGapWitness.dagSeparation` via a closed-term
`P_ne_NP_unconditional`.  The infrastructure track and the
research track proceed in parallel; neither blocks the other,
but the infrastructure must be ready before mass autoresearch can
search the candidate space at scale.
