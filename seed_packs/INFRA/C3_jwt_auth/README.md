# INFRA-C3: per-worker JWT authentication

> **Phase:** C (deferred until deployment context is available).
> **Status:** spec-only.
> **Depends on:** Phase B (3dfb1de) shipped.
> **Mvp version target:** `autoresearch_mvp = 0.6.2`.

## 1. Goal

Every `POST /v1/result`, `POST /v1/release`, and (later) `POST
/v1/cache` request carries a Bearer JWT.  The coordinator
verifies the token's signature and audience claim; mismatch → 401.

In MVP-0.2 the coordinator runs auth-less on `127.0.0.1`.  Phase C
opens it to multi-host workers; auth is the gate for that.

## 2. Allowed scope

* New `coordinator/auth.py` — issuance + verification.  Stdlib
  `hmac` + `hashlib` (HS256) — no external library.
* New endpoint: `POST /v1/auth/token` (operator-only via shared
  secret) → returns a fresh JWT for a given `worker_id` + role.
* `coordinator/server.py` — Bearer verification middleware on
  POST endpoints.
* `spec/coordinator_protocol.md` — auth section appended.
* `seed_packs/PILOT_WAVE_0_PROTOCOL.md` — worker-side change
  documentation.

## 3. Forbidden scope

* Trust root.
* JSONL ledgers.
* External library dependencies (Phase F can introduce PyJWT or
  similar; MVP-0.6 stays stdlib).

## 4. Acceptance criteria

1. `coordinator/auth.py::issue_jwt(worker_id, role, ttl_seconds)`
   returns a Bearer token verifiable by
   `coordinator/auth.py::verify_jwt(token) → (worker_id, role)`.
2. `POST /v1/result` without a Bearer header → 401.
3. `POST /v1/result` with a token whose claim does NOT match the
   `worker_id` in the body → 403.
4. `POST /v1/result` with a token whose claim role does NOT match
   the assignment's role → 403.
5. Token TTL of 5min by default; expired token → 401.
6. New `coordinator/test_auth.py` with 8 cases (none, valid,
   wrong-worker, wrong-role, expired, tampered-signature,
   wrong-audience, missing-claim).
7. `scripts/check.sh` 17/17 green; new Step 12.i runs `test_auth.py`.

## 5. Operator workflow

* Operator generates a coordinator HMAC secret at startup (env
  var `AUTORESEARCH_JWT_SECRET`) — at least 32 random bytes.
* Operator issues per-worker tokens via:
    `curl -X POST -H "X-Operator-Secret: $S" \
      "http://coord/v1/auth/token?worker_id=gen-alice&role=gen"`
* Worker stores token, attaches `Authorization: Bearer <token>`
  on every POST.

## 6. Open questions

* Algorithm: HS256 (symmetric) is simplest for one-coordinator
  deployments.  Phase F (sharded) needs RS256 or ED25519 with key
  rotation.
* Refresh: deferred to Phase F; MVP requires worker re-issuance
  on expiry (~5min cycle is the worker's wave-cycle order anyway).
