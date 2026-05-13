# INFRA-C2: build cache server

> **Phase:** C (deferred until deployment context is available).
> **Status:** spec-only.
> **Depends on:** INFRA-C1 (worker scratch isolation).
> **Mvp version target:** `autoresearch_mvp = 0.6.1`.

## 1. Goal

Serve `.lake/build/` tarballs by `(commit_hash, mathlib_version)`
so workers across many hosts can bootstrap a build cache in <5min
without each rebuilding mathlib + PnP3 + Pnp4 from scratch.

## 2. Allowed scope

* New `coordinator/build_cache.py` — HTTP file server endpoint
  exposed at `GET /v1/cache/.lake-build_${commit}_${mathlib}.tar.zst`.
* New `scripts/build_cache_publish.sh` — packages the local
  `.lake/build/` into a tarball and uploads via `POST
  /v1/cache/<key>` (or local-disk write in MVP).
* Storage: local filesystem (`coordinator/cache/<key>.tar.zst`)
  in MVP-0.6; S3 in Phase F (separate brief INFRA-F2).
* Modifications to `scripts/worker_bootstrap.sh` to fetch from
  the cache when present.

## 3. Forbidden scope

* Trust root.
* JSONL ledgers.
* `lake update mathlib`.
* Public-internet egress in MVP (local-only).

## 4. Acceptance criteria

1. `scripts/build_cache_publish.sh` produces a tarball and either
   POSTs to coordinator (200 OK) or writes to a configured local
   path.
2. `coordinator/build_cache.py::GET /v1/cache/<key>` returns 200
   with the tarball bytes when known, 404 otherwise.
3. `scripts/worker_bootstrap.sh` queries the cache, downloads if
   present, falls back to `lake build` from sources if absent.
4. Smoke: warm cache → 5 workers bootstrap in parallel each <5min.
5. Cache size cap: a worker MAY refuse to fetch a tarball >1GB
   (configurable via env).
6. `scripts/check.sh` 17/17 green.

## 5. How to test locally

```bash
# Publish a cache tarball after a clean build.
lake build PnP3 Pnp4
scripts/build_cache_publish.sh

# Start coordinator + workers; second worker should hit cache.
python3 -m coordinator.server --bind 127.0.0.1 --port 8765 --quiet &
scripts/worker_bootstrap.sh /tmp/cache_test_1
scripts/worker_bootstrap.sh /tmp/cache_test_2  # should hit cache, <5min
```

## 6. Open questions

* What hash function pinpoints "this build artifact set"?  MVP:
  `sha256(lakefile.lean + lake-manifest.json + git HEAD)`.  Phase F
  may add `lean_version` + `mathlib_version` explicitly.
* How to revoke a stale cache?  MVP: rename + restart coordinator.
  Phase F: TTL + LRU eviction.
* Compression: zstd vs gzip?  zstd is ~2x faster + smaller; ship
  zstd if the local toolchain has it, else gzip.
