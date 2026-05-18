# D0 `./scripts/check.sh` environment failure (not a regression)

Worker handle: `opus47`.
Date: 2026-05-18.
Branch: `claude/post-pr13-provider-retarget-d0` (base `main` at `1e0454f`).

## Observed

```
$ ./scripts/check.sh
[check] Step 1/17: full Lean build
./scripts/check.sh: line 19: lake: command not found
Full build failed; see /tmp/pnp3_full_build.log for details.
```

## Diagnosis

`lake` is not installed in the worker's sandbox.  The sandbox does not
have the Lean toolchain (no `elan`, no `lake`, no `lean` binaries on
`$PATH`).

## Pre-existence of failure on the base branch

`./scripts/check.sh` was re-run with the markdown-only worktree
discarded (`git stash` returned "No local changes to save", because the
worker's seed-pack files were untracked).  The base tree on commit
`1e0454f` produces the same `lake: command not found` failure.

Therefore the `check.sh` failure is **environmental**, not introduced by
this D0 work, and not a regression.

## Scope of the change

The D0 work is markdown-only.  The full file list is:

- `seed_packs/post_pr13_provider_retarget_D0/README.md`
- `seed_packs/post_pr13_provider_retarget_D0/WORKER_PROMPT_D0.md`
- `seed_packs/post_pr13_provider_retarget_D0/reports/D0_provider_retarget_opus47.md`
- `seed_packs/post_pr13_provider_retarget_D0/reports/.gitkeep`
- `seed_packs/post_pr13_provider_retarget_D0/failures/.gitkeep`
- `seed_packs/post_pr13_provider_retarget_D0/failures/D0_check_sh_environment.md`
  (this file)

None of these are Lean source files; the worktree's Lean dependency
graph is unchanged.  Re-running `./scripts/check.sh` on an environment
with the Lean toolchain available is expected to pass exactly as it
does on the base tree (PR 13's CI was green on the same commit).

## Recommendation

CI should run `./scripts/check.sh` in the upstream Lean-enabled
environment as part of the PR pipeline.  The local D0 sandbox cannot
substitute for that; this failure note records the observation rather
than gating the report.
