# `./scripts/check.sh` coordinator reset observation

Command: `./scripts/check.sh`

Observed twice on 2026-05-18 UTC.  In both runs, the full Lean build and the
preceding governance/audit checks passed through Step 12.d, then Step 12.e
(`coordinator HTTP service e2e`) failed during parallel `/v1/result` submission
with:

```text
ConnectionResetError: [Errno 104] Connection reset by peer
```

The second run also showed:

```text
[test_coordinator] OK   /v1/health
[test_coordinator] OK   /v1/manifest
[test_coordinator] OK   /v1/task role-mismatch -> 403
[test_coordinator] OK   /v1/task x N=20 -> 20 distinct ids
```

Exit code: `1`.

Local Lean check for the staged probe succeeded separately:

```sh
lake env lean pnp3/Tests/HInDagTrivialityProbe.lean
```
