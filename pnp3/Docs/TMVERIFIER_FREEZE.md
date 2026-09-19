# TMVerifier freeze decision

**Status:** frozen infrastructure snapshot.
**Frozen tree (authoritative):** `7ef6ac6e119f0f078f9c896f17415fa560a6edf3` —
the Git tree object of the subtree below, and the content source the checker
verifies against.
**Reviewed commit (provenance):** `249435bfa4cb540822e47844107781042f18537f`
(2026-09-19) — the commit at which those bytes were reviewed and re-pinned.
**Previously frozen at:** `42c598815c8e7d27a53f26102705f84455c6979d` (2026-09-02);
see the migration record below for the one reviewed unfreeze since then.

The complete tree below is content-addressed by `spec/tmverifier_freeze.json`:

```text
pnp3/Complexity/TMVerifier/
```

`scripts/check_tmverifier_freeze.sh` validates the manifest against the Git
objects in the frozen tree, then verifies the working tree's exact paths, object
types, executable modes, and SHA-256 contents without following symlinks. Git
tree objects are content-addressed, so that enumeration is reachable from any
history carrying the bytes — squash merges, rebases, force-pushes, and shallow
or single-branch clones do not take it away. Where the reviewed commit is still
present the checker additionally verifies that its subtree resolves to the
frozen tree and fails closed if it does not; where a rewritten history no longer
has that commit, content verification is unaffected. It and an isolated
manifest/filesystem/rewritten-history negative-control suite are part of
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
3. updates this decision record with the new authoritative tree and its
   reviewed commit, then regenerates the manifest from the newly pinned Git
   tree with:

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

The same complete `./scripts/check.sh` was run again, with the same result, on
the tree of the follow-up commit that moves the authoritative pin from the
reviewed commit to the frozen tree object `7ef6ac6e` (schema version 3). That
commit changes no frozen byte — the manifest's 115 `files` entries are
byte-identical across it — so no Lean module was rebuilt and no reviewed
theorem content was re-reviewed. The five supplementary gates above were rerun
at that tree, as were `python3 scripts/validate_version_manifest.py` and the
suite's new rewritten-history and provenance controls; the freeze checker now
reports the tree match plus the state of the reviewed provenance commit.

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
immediately at tree `7ef6ac6e`, reviewed at `249435bf`; the manifest was
regenerated with the documented `--write-manifest` command and the next ordinary
PR that touches the tree fails exactly as before.

**Operational note on the pin — content is rewrite-proof, provenance is not.**
The checker enumerates the frozen content from `FROZEN_TREE`, the Git tree
object `7ef6ac6e119f0f078f9c896f17415fa560a6edf3`. Tree objects are
content-addressed, so every history that carries these bytes carries this
object: squash merges, rebases, branch rewrites, force-pushes, and shallow or
single-branch clones all leave the content check working, and it works in a
clone that never fetched this branch at all. `FROZEN_COMMIT` is retained beside
it as reviewed provenance; when the checkout still contains that commit the
checker verifies that its subtree resolves to the frozen tree, and available
provenance that disagrees — a wrong subtree, a missing subtree, an object that
is not a commit — is a hard failure. Only genuine absence is skipped.

A tree pin proves content identity, not commit ancestry. Nothing about a
matching tree establishes that `249435bf`, the commit at which the theorem
content was reviewed, is an ancestor of `main`. That is a separate invariant,
and it is the one the merge rule below still protects.

**Merge with a merge commit — required, for provenance.** This PR must be
merged with a merge commit (an exact fast-forward, which also preserves the
commit objects, is equally acceptable). "Squash and merge" and "Rebase and
merge" both rewrite commit SHAs — squash collapses the branch into one new
commit, rebase replays the commits as new objects — so either one discards
`249435bf` from `main`'s ancestry. Under the tree pin that is no longer a
correctness problem for any check: the frozen content stays verifiable,
`scripts/check_tmverifier_freeze.py` keeps passing, and `scripts/check.sh` stays
green on `main` and in fresh or shallow clones. What a rewriting merge destroys
is the recorded link from the frozen bytes back to the commit two independent
reviews approved. Retaining that link is a requirement of this record, so the
history-preserving merge stays mandatory for this migration; it is simply no
longer the thing that keeps the repository's checks working.

**Correction to an earlier revision of this record.** Before the tree pin, this
section claimed that after a rewriting merge `scripts/check.sh` would fail on
`main` for every subsequent PR and that `main` would stay broken until a gated
recovery repin landed. That overstated the consequence even then —
`delete_branch_on_merge` is off and every workflow checks out with
`fetch-depth: 0`, so the pinned object stayed resolvable through the retained
branch ref, and the breakage was latent rather than immediate — and since the
tree pin it is not the failure mode at all. The cost of a rewriting merge is the
loss of reviewed-commit provenance, recorded and repaired as governance, not a
red build.

**The migration branch itself must not be rebased or force-pushed.** The same
reasoning applies to the branch for as long as the PR is open. If `main`
advances and the PR has to be updated, use GitHub's **"Update branch" → "Update
with merge commit"**, not "Update with rebase" and not a local `git rebase`
followed by a force-push. Branch rebasing replays the reviewed commit
`249435bfa4cb540822e47844107781042f18537f` itself as a new object and so drops
the reviewed provenance on the branch as well as from `main`. It no longer
breaks the PR's own freeze check — the frozen tree object travels with the bytes
— but it does change the head SHA and invalidate the repository-owner
attestation, which must then be reposted for the new 40-character head.

**Post-merge verification (required).** Immediately after the merge, on an
updated `main` or a fresh clone, run both:

```text
git merge-base --is-ancestor 249435bfa4cb540822e47844107781042f18537f origin/main
python3 scripts/check_tmverifier_freeze.py
```

The second is the content gate: it must report that the frozen tree matches
`7ef6ac6e119f0f078f9c896f17415fa560a6edf3`, and it is expected to pass under any
merge style. The first is the provenance audit and must exit `0`. If it does
not, the merge was a rewriting one and the reviewed-commit link was dropped:
the frozen content is still verified and `main` is not broken, so the response
is not an emergency but a deliberate repin onto a commit in `main`'s ancestry,
landed under this same unfreeze gate, plus a note in this record saying which
merge dropped the link.
