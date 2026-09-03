# TMVerifier freeze decision

**Status:** frozen infrastructure snapshot.
**Frozen commit:** `42c598815c8e7d27a53f26102705f84455c6979d` (2026-09-02).

The complete tree below is content-addressed by `spec/tmverifier_freeze.json`:

```text
pnp3/Complexity/TMVerifier/
```

`scripts/check_tmverifier_freeze.sh` validates the manifest against Git objects
at the frozen commit, then verifies the working tree's exact paths, object types,
executable modes, SHA-256 contents, and lakefile inclusion without following
symlinks. It and an isolated manifest/lake/filesystem negative-control suite
are part of `scripts/check.sh` and run before any build.

The freeze-policy paths are listed in `.github/CODEOWNERS` to make ownership
explicit. By repository-owner decision, `main` does not currently enforce
branch protection or code-owner review, so these are repository-level checks,
not an unoverrideable GitHub merge block.
The base-controlled `TMVerifier Freeze Policy` workflow independently rejects
changes to the frozen tree or policy files unless the PR has both the
`tmverifier-unfreeze` label and an exact repository-owner comment
`/tmverifier-unfreeze <current-head-sha>`. It checks both sides of renames,
fails closed on incomplete GitHub file lists, and never executes PR code.

This is a source snapshot, not a frozen semantic dependency or toolchain
closure. In particular, `Complexity.PsubsetPpolyInternal.TuringEncoding`,
`Complexity.PsubsetPpolyInternal.Bitstring`, `Models.Model_PartialMCSP`,
`Magnification.CanonicalAsymptoticTrackData`,
`Magnification.CanonicalAsymptoticDecider`, and the Lean/Mathlib toolchain
remain separately governed. P1 must introduce versioned foundations outside
the frozen tree and must not silently alter these dependencies to change the
meaning of the snapshot.

## Why it is frozen

The one-tape verifier track is preserved as formal-methods and model-audit
infrastructure, but further gate-by-gate construction is paused while a new
versioned uniform complexity-class foundation is established. New model-repair
work must live outside the frozen tree.

This record is internal repository governance. Public-facing model claims are
updated separately once the replacement interface and migration theorems are
kernel-checked.

## Allowed changes

Ordinary PRs must not add, remove, rename, or modify files in the frozen tree.
A change requires a dedicated unfreeze/migration PR that:

1. states why the frozen artifact itself must change rather than a new versioned
   module outside it;
2. reruns the complete local and remote review gates;
3. updates this decision record, then regenerates the manifest from the newly
   pinned Git commit with:

   ```text
   python3 scripts/check_tmverifier_freeze.py --write-manifest
   ```

4. does not silently resume the old verifier roadmap.

For each new head SHA, the repository owner must first post the exact command
above and then apply or retrigger the `tmverifier-unfreeze` label. A later push
invalidates the old attestation. Without branch protection the resulting check
remains repository governance rather than an unoverrideable merge block.

The next active track is the versioned uniform `P` model and its circuit
simulation, not GN-E2-3b or later TMVerifier stages.
