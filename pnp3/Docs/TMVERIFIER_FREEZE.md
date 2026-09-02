# TMVerifier freeze decision

**Status:** frozen infrastructure snapshot.  
**Frozen commit:** `42c598815c8e7d27a53f26102705f84455c6979d` (2026-09-02).

The complete tree below is content-addressed by `spec/tmverifier_freeze.json`:

```text
pnp3/Complexity/TMVerifier/
```

`scripts/check_tmverifier_freeze.sh` verifies both the exact file set and the
SHA-256 digest of every file. It is part of `scripts/check.sh`.

## Why it is frozen

The one-tape verifier track is preserved as formal-methods and model-audit
infrastructure, but further gate-by-gate construction is paused while the
complexity-class foundation is replaced by a uniform machine interface without
an unrestricted `runTime : Nat → Nat` field. New model-repair work must live
outside the frozen tree.

This record is internal repository governance. Public-facing model claims are
updated separately once the replacement interface and migration theorems are
kernel-checked.

## Allowed changes

Ordinary PRs must not add, remove, rename, or modify files in the frozen tree.
A change requires a dedicated unfreeze/migration PR that:

1. states why the frozen artifact itself must change rather than a new versioned
   module outside it;
2. reruns the complete local and remote review gates;
3. updates this decision record and regenerates the manifest deliberately;
4. does not silently resume the old verifier roadmap.

The next active track is the versioned uniform `P` model and its circuit
simulation, not GN-E2-3b or later TMVerifier stages.
