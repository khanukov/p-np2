# TMVerifier freeze decision

**Status:** frozen infrastructure snapshot.
**Frozen commit:** `249435bfa4cb540822e47844107781042f18537f` (2026-09-19).
**Previously frozen at:** `42c598815c8e7d27a53f26102705f84455c6979d` (2026-09-02);
see the migration record below for the one reviewed unfreeze since then.

The complete tree below is content-addressed by `spec/tmverifier_freeze.json`:

```text
pnp3/Complexity/TMVerifier/
```

`scripts/check_tmverifier_freeze.sh` validates the manifest against Git objects
at the frozen commit, then verifies the working tree's exact paths, object types,
executable modes, and SHA-256 contents without following symlinks. It and an
isolated manifest/filesystem negative-control suite are part of
`scripts/check.sh` and run before any build. `lakefile.lean` is blanket-protected
by the trusted PR policy rather than partially parsed as Lean syntax.

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

For each new head SHA, the repository owner must first post the exact
attestation comment `/tmverifier-unfreeze <current-head-sha>` as a PR issue
comment whose entire body is that single line, with `<current-head-sha>`
spelled out as the **full 40-character SHA** of the PR's current head. That
comment — not the `--write-manifest` command in the code block above — is what
the `TMVerifier Freeze Policy` workflow matches, and it must be posted by the
repository owner account. The owner must then apply or retrigger the
`tmverifier-unfreeze` label. A later push changes the head SHA and invalidates
the old attestation, so a fresh comment naming the new 40-character head is
required. Without branch protection the resulting check remains repository
governance rather than an unoverrideable merge block.

The next active track is the versioned uniform `P` model and its circuit
simulation, not GN-E2-3b or later TMVerifier stages.

## Migration record

### 2026-09-19 — S11 one-gate acceptance closure (single reviewed unfreeze)

Re-pinned from `42c59881` to `249435bf`. This is the only unfreeze since the
tree was frozen on 2026-09-02.

**What entered the frozen tree.** Two new modules,
`TuringToolkit/GateOneAcceptsClosure.lean` and
`TuringToolkit/GateOneAcceptsClosureExamples.lean`, plus a docstring-only
correction in `TuringToolkit/GateOneValidation.lean`. They add two
hypothesis-free endpoints over every `r : G1Request`:

```lean
g1CS_accepts_eq_isSome (r : G1Request) :
    TM.accepts (M := G1M) (encodeG1 r).length (g1Point (encodeG1 r)) =
      r.spec.isSome

g1CS_accepts_iff_wellFormed (r : G1Request) :
    TM.accepts (M := G1M) (encodeG1 r).length (g1Point (encodeG1 r)) = true ↔
      r.WellFormed
```

No `g1Transition` row, no `g1Clock`, no `*Steps` definition, no head position,
no `GateN` declaration and no encoder is changed or restated; the snapshot's
transducer convention is unchanged, so a defined `false` accepts exactly as a
defined `true` does and the value stays on the output cell. Acceptance is
exact-step, not halting, and every statement is scoped to the image of
`encodeG1`, so this is not a language-membership theorem.

**Why the frozen artifact itself had to change (requirement 1 above).** The
statement quantifies over the concrete fixed `G1M`/`encodeG1`/`g1Clock` triple
defined inside the snapshot and is proved from roughly twenty in-tree lemmas of
the same `Internal.PsubsetPpoly.TM` namespace — the validation-prefix reject
route, the pass-A/pass-B out-of-range boundaries, and the existing driver clock
bounds. It is a closure statement *about the frozen machine*, not new
model-repair work and not a new versioned foundation, so the escape hatch this
record offers — put new work in a versioned module outside the tree — does not
apply: any such module would name the same frozen internals, would be a
satellite of the snapshot rather than an independent foundation, and would
split the `GateOne*` chain that the surface tests and `AxiomsAudit` walk as one
unit. Relocation would also not avoid this gate, because `lakefile.lean` is
itself blanket-protected and the module must be registered there. The
`GateOneValidation.lean` docstring fix — it called `encodeG1 r` the "canonical
encoding of a noncanonical request", which is self-contradictory — has no
out-of-tree form at all.

**Review status.** The theorem content was reviewed at its exact head by two
independent read-only adversarial reviews (Claude and Codex), both APPROVE,
against the two endpoint signatures above with no side hypotheses permitted.
The reviewed tree is reproduced byte-for-byte in `249435bf`; only
`pnp3/Tests/AxiomsAudit.lean` and `lakefile.lean` were re-merged, additively,
against newer `main`.

**Gates (requirement 2) — local done, remote still owed.** Requirement 2 above
asks for the complete local *and* remote review gates. Only the local half is
discharged by this record, and only the local half is claimed here.

*Local, observed.* The complete `./scripts/check.sh` was run at the re-freeze
commit `0d699f6e` and printed `[check] All checks passed.`; it was then re-run
in full, with the same result, on the tree of the docs-only governance commit
that adds this paragraph. That run covers the frozen-tree manifest and
filesystem preflight and its isolated negative-control suite, both Lean
libraries, the placeholder and hygiene scans, the route-policy and doc-honesty
gates, and the axiom-surface dumps. The supplementary local gates were
additionally run on their own at the same tree — the four freeze-specific ones,
`python3 scripts/check_tmverifier_freeze.py`,
`scripts/check_tmverifier_freeze.sh`, `scripts/test_tmverifier_freeze.sh` and
`node scripts/test_tmverifier_freeze_policy.js`, together with
`scripts/check_doc_honesty.sh`, which is the public-document claim gate rather
than a freeze gate — all reporting OK, with the freeze checker matching the
frozen tree against `249435bf`.

*Remote, not yet done and explicitly not claimed.* When this paragraph was
written the branch had not been pushed and no PR existed, so there is **no**
remote CI result and no remote review for it; nothing here should be read as
asserting green CI. Before merge the remote half must be completed against the
*final* head: green `ci.yml` and `lean.yml`, the exact-head repository-owner
attestation comment and `tmverifier-unfreeze` label described above, and the
required PR review. The local run recorded here does not substitute for any of
them, and the two independent read-only adversarial reviews recorded in the
previous paragraph are reviews of the theorem content, not a rerun of the
gates.

**Scope.** This is a narrow migration of one already-reviewed theorem slice,
not a resumption of the paused roadmap. GN-E2-3b and later gate-by-gate
construction remain paused, the next active track remains the versioned uniform
`P` model and its circuit simulation, and nothing here reduces
`VerifiedNPDAGLowerBoundSource` or `SearchMCSPWeakLowerBound` or discharges a
`CanonicalAsymptoticVerifierComponents` obligation. The tree is re-frozen
immediately at `249435bf`; the manifest was regenerated with the documented
`--write-manifest` command and the next ordinary PR that touches the tree fails
exactly as before.

**Operational note on the pin — merge commit only.** The checker resolves
`FROZEN_COMMIT` with `git ls-tree`, so the pinned commit must be reachable in
the checkout being verified. `249435bf` is an ancestor of this branch, and it
remains an ancestor of `main` only if the migration PR lands with its history
preserved. **This PR must therefore be merged with a merge commit** (an exact
fast-forward, which also preserves the commit objects, is equally acceptable).

**"Squash and merge" and "Rebase and merge" are both prohibited for this
migration.** Both rewrite commit SHAs — squash collapses the branch into one
new commit, rebase replays the commits as new objects — so either one discards
`249435bf` from `main`'s ancestry, and re-pinning to `0d699f6e` beforehand
would not help because that commit's ancestry is discarded the same way. After
such a merge the pinned object survives only incidentally, for as long as the
unmerged source branch happens to be kept on the remote; a fresh clone or a
single-branch checkout can no longer resolve it, so
`scripts/check_tmverifier_freeze.py` raises, and `scripts/check.sh` then fails
on `main` for every subsequent PR. Recovery is itself gated — the repin touches
protected paths and needs a new `tmverifier-unfreeze` label plus a fresh
exact-head owner attestation — so `main` stays broken until that second PR
lands. A post-hoc repin is a recovery procedure for an accident, **not** an
acceptable planned merge sequence: do not squash or rebase on the assumption
that the pin can be cleaned up afterwards. If the merge-commit option is
unavailable in the GitHub UI, enable it for this PR or perform an
owner-controlled history-preserving merge; do not fall back to squash.

**The migration branch itself must never be rebased or force-pushed.** The
prohibition above covers the merge buttons; the same rule applies to the branch
for as long as the PR is open. If `main` advances and the PR has to be updated,
use GitHub's **"Update branch" → "Update with merge commit"**, never "Update
with rebase", and likewise never a local `git rebase` followed by a force-push.
Branch rebasing replays the pinned commit
`249435bfa4cb540822e47844107781042f18537f` itself as a new object, so
`FROZEN_COMMIT` in `scripts/check_tmverifier_freeze.py` becomes unresolvable on
the PR branch and the PR's own freeze check fails before merge is even reached
— strictly worse than a rewriting merge, because the pin is then lost on the
branch as well as on `main`, and recovery is the same gated repin described
above. Any such rewrite also changes the head SHA and invalidates the
repository-owner attestation, which must then be reposted for the new
40-character head.

**Post-merge verification (required).** Immediately after the merge, on an
updated `main` or a fresh clone, run both:

```text
git merge-base --is-ancestor 249435bfa4cb540822e47844107781042f18537f origin/main
python3 scripts/check_tmverifier_freeze.py
```

The first must exit `0`, and the second must report that the frozen tree
matches `249435bf`. If the ancestry check fails, the pin was stripped by a
rewriting merge: treat `main` as broken, announce it, and land the recovery
repin under this same unfreeze gate before any other PR touches the tree.
