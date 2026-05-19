# `./scripts/check.sh` environment failure note

Handle: `opus47`.

```sh
$ ./scripts/check.sh
[check] Step 1/17: full Lean build
./scripts/check.sh: line 19: lake: command not found
Full build failed; see /tmp/pnp3_full_build.log for details.
```

## Diagnosis

`lake` is not installed in the worker sandbox.  Same environmental
failure observed in prior markdown-only audits.

## Non-regression confirmation

The audit is markdown-only (one report under `reports/`, plus README,
WORKER_PROMPT, and two `.gitkeep` files).  No Lean files are touched.
The failure reproduces on `main` HEAD without the audit's changes
(checked in prior sessions); the upstream Lean-enabled CI is expected
to pass this PR.
