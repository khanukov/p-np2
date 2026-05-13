# INFRA-C1: worker scratch isolation

> **Phase:** C (deferred until deployment context is available).
> **Status:** spec-only.
> **Depends on:** Phase A + B + D + E shipped (e87743b → 56a95e6).
> **Mvp version target:** `autoresearch_mvp = 0.6.0`.

## 1. Goal

Each parallel worker gets a fully isolated scratch directory at
`${WORKER_SCRATCH}/worker_${WORKER_ID}_${UUID}/` containing its own
`.lake/`, its own `/tmp/`, its own staged candidate dir.  Workers
do NOT share filesystem state with other workers on the same host
beyond explicitly-shared read-only spec files.

## 2. Allowed scope

* New `scripts/worker_bootstrap.sh` — provisions a clean scratch
  in ≤5min from cold start.
* Modifications to `scripts/run_worker.sh` to use the bootstrapped
  scratch.
* New `spec/worker_scratch_contract.md` — what's in/out of scope
  for "scratch".
* `spec/version_manifest.toml` — `snapshot.worker_scratch_contract`
  + bump `autoresearch_mvp` to 0.6.0.

## 3. Forbidden scope

* `pnp3/Complexity/Interfaces.lean`, `pnp3/Magnification/UnconditionalResearchGap.lean`,
  `ResearchGapWitness`.
* Any existing JSONL ledger entries.
* `coordinator/server.py` core endpoints (the coordinator does not
  know about scratch dirs; that's worker-side).
* `lake update mathlib` (out of scope per v0.3 plan).

## 4. Acceptance criteria

1. `scripts/worker_bootstrap.sh /tmp/test_w1` provisions a clean
   scratch in ≤5min from cold start (cached `.lake/` tarball).
2. Two `scripts/run_worker.sh` invocations against ONE coordinator
   on ONE host with distinct `--worker-id` and `--scratch` paths
   complete without filesystem collision.
3. `lake build PnP3 Pnp4` inside the scratch produces identical
   `.olean` checksums vs the canonical repo.
4. New smoke `scripts/test_worker_scratch_isolation.sh` runs 4
   workers in parallel against the same coordinator and asserts
   no shared `.lake` write.
5. `scripts/check.sh` 17/17 green; new Step 12.h runs the smoke.
6. No regressions on Steps 12.b/d/e/f/g.

## 5. How to test locally

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake build PnP3 Pnp4         # warm canonical cache
./scripts/worker_bootstrap.sh /tmp/iso_test_1
./scripts/worker_bootstrap.sh /tmp/iso_test_2
# Each is independent.

# Spawn coordinator + 4 workers via the new smoke:
python3 -m coordinator.server --bind 127.0.0.1 --port 8765 --quiet &
COORD_PID=$!
./scripts/test_worker_scratch_isolation.sh
kill $COORD_PID
```

## 6. How to ship

* Commit message starts with `INFRA-C1:`.
* PR body mentions: this brief id, the new files, the "what did
  NOT change" list (no Lean code, no trust-root, no FixedParams
  Probe math, no candidates, no bridge, no SourceTheorem).
* Pipeline state: all green incl. new Step 12.h.

## 7. Open questions

* Is `cp .lake/` → scratch preferred over a tarball download?
  At single-machine scale `cp -al` (hardlink-copy) is fast.
  Decide in implementation.
* Where does the canonical `.lake/` live for bootstrapping? For
  Phase C single-machine, just the repo's own; for Phase F the
  build-cache server hosts tarballs.
