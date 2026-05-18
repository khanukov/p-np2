# `./scripts/check.sh` structured failure note — hInDag L0

Handle: gpt55
Command: `./scripts/check.sh`
Exit code: 1

Observation: the full Lean build and all governance checks through step 12.d
completed successfully, but step 12.e (`coordinator/test_coordinator.py`) failed
with an HTTP service concurrency reset while submitting `/v1/result` in the
coordinator e2e test:

```text
ConnectionResetError: [Errno 104] Connection reset by peer
```

This occurred after the Lean build had completed successfully and after the
new staging module was individually checked with:

```sh
lake env lean pnp3/Tests/HInDagTrivialityProbe.lean
```

No code failure in `pnp3/Tests/HInDagTrivialityProbe.lean` was observed.
