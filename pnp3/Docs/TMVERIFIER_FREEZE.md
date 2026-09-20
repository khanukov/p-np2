# TMVerifier freeze decision

**Status:** frozen infrastructure snapshot, with **one unfreeze in flight**.
The two pinned constants below are unchanged and this revision does **not**
repin anything. A GN-E2-3b stage-(a) commit has added new bytes to the frozen
subtree ahead of its repin, exactly in the order requirement 3 below mandates,
so `scripts/check_tmverifier_freeze.py` and the freeze preflight of
`scripts/check.sh` are **expected to fail** on this tree until stage (b) lands.
See the pending migration record at the end of this file for what is done and
what is still owed.
**Frozen tree (authoritative):** `7ef6ac6e119f0f078f9c896f17415fa560a6edf3` —
the Git tree object of the subtree below, and the content source the checker
verifies against. It is the tree of the *last completed* migration, not of the
working tree while an unfreeze is in flight.
**Reviewed commit (provenance):** `249435bfa4cb540822e47844107781042f18537f`
(2026-09-19) — the commit at which those bytes were reviewed and re-pinned.
**Previously frozen at:** `42c598815c8e7d27a53f26102705f84455c6979d` (2026-09-02);
see the migration record below for the one completed reviewed unfreeze since
then, and for the pending one.

The complete tree below is content-addressed by `spec/tmverifier_freeze.json`:

```text
pnp3/Complexity/TMVerifier/
```

`scripts/check_tmverifier_freeze.sh` validates the manifest against the Git
objects in the frozen tree, then verifies the working tree's exact paths, object
types, executable modes, and SHA-256 contents without following symlinks.
Executable mode is read as Git reads it — from the owner execute bit alone — so
a group- or other-execute bit that Git does not record is not reported as a
change. Git tree objects are content-addressed, so that enumeration is reachable
from any Git object store holding these bytes — squash merges, rebases,
force-pushes, and shallow or single-branch clones do not take it away. It is
also taken from the root of the tree object rather than through the current
directory's Git prefix, so a checkout nested inside another repository — a
vendored export, a fixture directory — is enumerated whole instead of failing on
a false mismatch. What travels is the object store, not the bytes alone: an
exported working tree — `git archive`, a release tarball, any `.git`-less copy —
carries byte-identical content and nothing to enumerate, and is refused rather
than verified. Where the reviewed commit is still present the checker
additionally verifies that its subtree resolves to the frozen tree and fails
closed if it does not; where a rewritten history no longer has that commit,
content verification is unaffected. An object Git cannot read is never counted
as an absent one: corruption, an unreadable object store, a failed promisor
fetch and every other Git failure are hard failures carrying Git's own
diagnostic. That distinction is drawn from Git's stderr, so the probe
runs with every `GIT_TRACE*` variable stripped from its environment — tracing
switched on to debug something else is not a Git diagnostic and must not turn a
genuinely absent object into a reported fault. It and an isolated
negative-control suite — manifest, filesystem, rewritten-history, provenance,
object-state, nested-prefix, authoring-atomicity, tracing and self-hosted
provenance-free controls — are part of `scripts/check.sh` and run before any
build. The suite proves it passes in a checkout that has lost the reviewed
commit by running itself inside one. `lakefile.lean` is blanket-protected by the
trusted PR policy rather than partially parsed as Lean syntax.

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
3. re-pins the freeze in two stages, in this order. `--write-manifest` refuses
   to write unless the reviewed provenance commit already resolves in this
   repository and records exactly the pinned tree, so the new bytes must be
   committed before the new pin can be authored:

   a. commit the new frozen bytes together with whatever registration they
      need to build — a new module has to be declared in `lakefile.lean`, and
      any new public surface has to reach the surface tests and the axiom
      audit, in the same commit, or the tree the pin names does not compile.
      What stage (a) must not carry is the pin itself. That commit becomes the
      new reviewed provenance commit, and its subtree is the new authoritative
      tree; read both off it:

      ```text
      git rev-parse HEAD
      git rev-parse HEAD:pnp3/Complexity/TMVerifier
      ```

   b. in a second commit, set `FROZEN_COMMIT` and `FROZEN_TREE` in
      `scripts/check_tmverifier_freeze.py` to those two values — plus
      `SCHEMA_VERSION` there and the `[snapshot.tmverifier_freeze]` row in
      `spec/version_manifest.toml` if the manifest shape changes — update the
      header of this decision record with the same pair, and regenerate the
      manifest, which re-verifies the pin before it writes anything:

      ```text
      python3 scripts/check_tmverifier_freeze.py --write-manifest
      ```

   Stage (b) must be its own commit: it names stage (a)'s SHA, which does not
   exist until (a) is committed and would change again if (a) were amended.
   Neither half of the repin can be skipped, and `--write-manifest` enforces
   that rather than trusting it — it refuses, leaving the manifest untouched,
   both when the pinned `FROZEN_COMMIT` is not in this repository (stage (a)
   not landed, or a mistyped SHA) and when it is present but does not record
   the pinned `FROZEN_TREE` (the tree repinned, the commit left stale). When it
   does write, it serializes the whole manifest first and installs it by
   renaming a completed temporary file over the target, so an interrupted
   regeneration leaves the previous manifest intact rather than truncated.

   This unfreeze has the same two-stage shape, though it predates part of the
   machinery described here: `249435bf` is stage (a) — the new frozen bytes
   together with their `lakefile.lean` registration, surface tests and
   axiom-audit entries, seven files in all — and `0d699f6e` is stage (b), which
   set `FROZEN_COMMIT` and regenerated the manifest. Stage (b) set neither of
   the other two constants: `FROZEN_TREE` did not exist until `4abbe04b` moved
   the authoritative pin onto the tree object, and `SCHEMA_VERSION` stayed at 2
   because the manifest's shape did not change until then either.

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

**One authorized exception to that sentence, 2026-09-20.** The repository owner
authorized a single dedicated unfreeze for GN-E2-3b, under this record's
two-stage rule and with no other stage resumed. Its stage (a) is recorded as
pending below. The sentence above still governs everything else: E2-4 and later
TMVerifier stages remain paused, and no further slice may be taken without a
fresh authorization.

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

Two further independent read-only adversarial reviews of that follow-up commit
required changes, and a third run of the same seven gates — the complete
`./scripts/check.sh`, the four freeze-specific gates, `check_doc_honesty.sh` and
`validate_version_manifest.py` — was made on the tree of the review-fix commit
that answers them. That commit again changes no frozen byte and no Lean source:
the frozen tree is still `7ef6ac6e119f0f078f9c896f17415fa560a6edf3` and the
manifest is byte-identical. What it changes is how the two pinned objects are
probed (a Git failure of any kind is now a hard failure rather than an answer of
"absent"), the strictness of `--write-manifest`, the negative-control suite that
holds both properties down, and the wording corrected in this record.

Two more independent read-only adversarial reviews of *that* commit required
changes in turn, and a fourth run of the same seven gates was made on the tree
of the second review-fix commit that answers them, together with the check
those reviews showed was missing: the checker and the negative-control suite
were both run in a real `git clone --depth 1 --single-branch` of this branch,
where `249435bf` is genuinely absent from the object store and the frozen tree
object is present. Both pass there, and the suite now asserts that shape itself
on every run by building a provenance-free repository and running itself inside
it. That commit, too, changes no frozen byte and no Lean source. What it changes
is the object probe's environment (`GIT_TRACE*` is stripped, so tracing cannot
be mistaken for a diagnostic), manifest authoring (a completed temporary file is
renamed over the target instead of the target being truncated in place), the
controls that hold both down, and the wording corrected in this record.

A further independent read-only audit of this branch's head reported two
low-severity defects in how the checker enumerates, and a third review-fix
commit answers them. Neither was a freeze bypass — both failed closed — but both
failed on the wrong question. `git ls-tree` was reading the frozen tree through
Git's current-directory prefix, so a checkout nested inside another repository
enumerated nothing and was told its manifest disagreed with a tree object the
checker could read perfectly well; `--full-tree` now takes the listing from the
root of the named tree object, leaving the tree-relative paths and their
re-prefixing exactly as they were. And the working-tree side derived `100755`
from any execute bit where Git derives it from the owner bit alone, so a group-
or other-execute bit Git does not record was reported as a mode change; it now
reads `stat.S_IXUSR`, which is Git's own rule. That commit changes no frozen
byte, no Lean source, and no pin: the frozen tree is still
`7ef6ac6e119f0f078f9c896f17415fa560a6edf3`, the manifest's 115 `files` entries
are byte-identical, and `SCHEMA_VERSION` and the `[snapshot.tmverifier_freeze]`
row are untouched. The negative-control suite gains four controls: a vendored
export two directories deep inside an unrelated repository that carries the
frozen tree object, and group-only, other-only and owner-only execute bits on
one frozen file. Three of them — the export and the two tolerated bits — fail
before these fixes and pass after; the owner-only case is the fail-closed
direction and is a violation on both sides of the change, which is what pins the
fix to Git's rule rather than to dropping the mode column.

*The gates run for that third review-fix commit, and only those.* Six of the
seven gates listed above were run on its tree and all passed: the four
freeze-specific ones (`python3 scripts/check_tmverifier_freeze.py`,
`scripts/check_tmverifier_freeze.sh`, `scripts/test_tmverifier_freeze.sh` and
`node scripts/test_tmverifier_freeze_policy.js`), plus
`scripts/check_doc_honesty.sh` and `python3
scripts/validate_version_manifest.py`; `python3 -m py_compile` on both changed
scripts and `git diff --check` were run alongside them. The seventh — the
complete `./scripts/check.sh` — was **not** rerun for it, and no Lean or `lake`
build was performed. It changes no Lean source and no frozen byte, so no module
would be rebuilt, but that is a reason to expect the unrun gate to pass and not
a record that it did. No remote result is claimed for it either.

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
content-addressed, so every Git object store that carries these bytes carries
this object: squash merges, rebases, branch rewrites, force-pushes, and shallow
or single-branch clones all leave the content check working, and it works in a
clone that never fetched this branch at all. What survives the rewrite is the
object, not merely the content — a `git archive` export, a release tarball or
any other `.git`-less copy has the bytes and no object store, and fails closed
with that as the stated reason. `FROZEN_COMMIT` is retained beside it as
reviewed provenance; when the checkout still contains that commit the checker
verifies that its subtree resolves to the frozen tree, and available provenance
that disagrees — a wrong subtree, a missing subtree, an object that is not a
commit — is a hard failure. So is any Git failure that leaves the question
unanswered: absence is concluded only from Git's own silent `missing` reply, so
a corrupt object, an unreadable object store or a failed promisor fetch is
reported as the fault it is and is never recorded as a rewritten history.
Reading stderr as a signal also means the probe must not inherit Git's own
tracing, so `GIT_TRACE*` is dropped from its environment — from its environment
only, leaving tracing usable for everything it is normally turned on for.
Manifest authoring is stricter than verification: `--write-manifest` refuses to
write anything at all unless the reviewed provenance resolves and matches, so a
pin cannot be recorded without being proved, while an ordinary check of a
rewritten or shallow history still verifies content against `FROZEN_TREE`. A
permitted write is atomic: the manifest is enumerated and serialized in full,
written to a fresh file in the same directory, flushed, and renamed over the
target, so an interrupted regeneration destroys nothing and leaves nothing
behind.

One diagnostic limitation is worth knowing before debugging a red check. When
the working tree has drifted *and* this object store does not carry the frozen
tree — a `--depth 1` clone of an already-drifted tip is the realistic case — the
checker reports the unavailable tree object instead of listing the changed
paths. It still fails closed, and the three workflows that run it all check out
with `fetch-depth: 0`, so CI always gets the path-level report.

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
`scripts/check_tmverifier_freeze.py` keeps passing, and the freeze preflight of
`scripts/check.sh` — the checker, the negative-control suite and the policy
tests it runs before any build — stays green on `main` and in fresh or shallow
clones. That is asserted rather than assumed: the suite builds a provenance-free
repository and runs itself inside it on every invocation, and the same thing was
reproduced by hand in a real `--depth 1 --single-branch` clone of this branch.
What a rewriting merge destroys is the recorded link from the frozen bytes back
to the commit two independent reviews approved. Retaining that link is a
requirement of this record, so the history-preserving merge stays mandatory for
this migration; it is simply no longer the thing that keeps the repository's
checks working.

**Correction to an earlier revision of this record.** Before the tree pin, this
section claimed that after a rewriting merge `scripts/check.sh` would fail on
`main` for every subsequent PR and that `main` would stay broken until a gated
recovery repin landed. That overstated the consequence even then. The three
workflows that run the freeze checker — `.github/workflows/ci.yml`,
`.github/workflows/lean.yml` and `.github/workflows/nightly-unconditional.yml` —
all check out with `fetch-depth: 0`, so for as long as the merged source branch
remained on the remote the pinned object stayed resolvable through that retained
ref, and the breakage was latent rather than immediate. (Whether merged branches
are auto-deleted is a GitHub repository setting that no checkout records; the
earlier revision asserted `delete_branch_on_merge` was off as though it were a
verified in-repository fact, and this record should not. The fourth workflow,
`.github/workflows/tmverifier-freeze.yml`, sets no `fetch-depth`, but it only
checks out the default-branch policy script and never runs the freeze checker,
so it is outside this claim.) Since the tree pin it is not the failure mode at
all. The cost of a rewriting merge is the loss of reviewed-commit provenance,
recorded and repaired as governance, not a red build.

**A second correction, to what that claim says about `scripts/check.sh`.** The
claim is about the whole freeze preflight and not only about the checker, and
from `a1227ba3` until the commit that adds this paragraph it was false of the
negative-control suite. The suite regenerated the manifest at the repository
root unconditionally, and the strict `--write-manifest` guard that `a1227ba3`
introduced refuses to regenerate wherever `249435bf` is absent — so a `--depth
1` clone of this branch, and a squash-rewritten `main`, had a green freeze
checker and a red `scripts/check.sh` preflight. (Before `a1227ba3` the same
clone was green, because authoring was not yet strict; the defect arrived with
the guard, not with the tree pin.) The strictness is right and is kept. What
was wrong was a control that demanded authoring in exactly the checkouts where
authoring is deliberately forbidden; it now asserts whichever half of the
authoring contract the checkout admits — regeneration must reproduce the
reviewed manifest where the provenance commit resolves, and must be refused
with its target untouched where it does not — and the self-hosted
provenance-free control above exists so that this cannot silently become false
again.

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

### 2026-09-20 — GN-E2-3b body driver (PENDING: stage (a) only, not repinned)

**This record is not a repin.** `FROZEN_COMMIT`, `FROZEN_TREE`,
`SCHEMA_VERSION`, `spec/tmverifier_freeze.json` and
`spec/version_manifest.toml` are untouched by the stage-(a) commit, and the
header of this file still names tree `7ef6ac6e` reviewed at `249435bf`. That is
the required order: requirement 3(a) says the new bytes must be committed
first, because `--write-manifest` refuses to author a pin whose provenance
commit does not yet exist. Until stage (b) lands, the frozen tree on this branch
legitimately disagrees with the pin, and the freeze checker fails closed saying
so.

**Why the frozen artifact itself had to change (requirement 1).** The slice is
the arbitrary proof-level induction over GN-E2-3a's own
`gnCS_bodyRound_iteration_exact` and `gnCS_bodyFinishRound_recordDone_exact`,
composed with GN-E2-2's `gnCS_encodeGN_bofSeed_exact`. Every one of those names,
and `GNM`, `gnCS`, `gnTransition`, `gnClock`, `encodeGN`, `gnBodyRoundConfig`
and `gnCopyShuttle`, is defined inside the snapshot. A module outside the tree
would name the same frozen internals, would be a satellite of the snapshot
rather than an independent versioned foundation, and would split the `GateN*`
chain that the surface tests and `AxiomsAudit` walk as one unit. Relocation
would also not avoid this gate, because `lakefile.lean` is blanket-protected and
a new module must be registered there.

**What entered the frozen tree.** One new module,
`TuringToolkit/GateNBodyDriver.lean`. Nothing else in the frozen subtree is
added, removed, renamed or modified — no existing `GateN*` or `GateOne*` file is
touched. The module adds no `GNState` constructor, no `gnTransition` row, no
machine, no clock, no encoder, no step-count hack, no request-dependent runtime
state and no runtime geometry or advice. Its two endpoints are:

```lean
gnCS_bodyDriver_recordDone_exact (n : Nat) (fixed done : List G1Frame)
    (current : G1Frame) (body tail seed : List G1Frame)
    (previous : GNInstallAux) … :
    TM.runConfig (M := GNM) (gnBodyRoundConfig …)
        (gnBodyDriverSteps (current :: body).length …) =
      gnCopyShuttle.cfg n (4 * (fixed ++ (done ++ current :: body)).length + 4) …
        (frameListTape …) .recordDone

gnCS_encodeGN_firstRecordDone_exact {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    TM.runConfig (M := GNM) (GNM.initialConfig (gnPoint (encodeGN r)))
        (gnFirstRecordDoneSteps r g) = gnFirstRecordDoneConfig r g hg
```

Both are genuine `TM.runConfig` execution with an exact accumulated schedule, a
literal `.recordDone` state, an exact head and a complete physical tape
equality; neither is weakened to a wrapper predicate. The second starts at the
real initial configuration and tracks the actually selected first gate through
`hg`. Nothing claims continuation from `recordDone`, a values or tail writer, a
launch, delegation, commit, next-gate loop, total installer clock, verdict,
acceptance, or that the pure evaluator `evalGNProgram` is executed by the
machine. Details, including the semantics-versus-execution distinction, are in
the GN-E2-3b section of `TMVerifier_Session_Plan.md`.

**Registration carried in the same commit (requirement 3(a)).**
`lakefile.lean` registers both the new source module and the new
`Tests/TMGateNBodyDriverSurfaceTests.lean`; that surface test `#check`s all
twenty-one new public declarations (seven definitions and fourteen theorems)
and restates every one of the fourteen theorems as a full-proposition
`check_*` wrapper; `pnp3/Tests/AxiomsAudit.lean` imports both
and adds twenty-eight direct `#print axioms` roots (the fourteen theorems and
the fourteen wrappers). Observed axiom sets are subsets of
`{propext, Classical.choice, Quot.sound}`; no `sorryAx`, `Lean.ofReduceBool`,
`Lean.trustCompiler` or `nativeDecide` appears.

**Gates — what was actually run, and only that.** The complete
`./scripts/check.sh` was **not** run and is **not** claimed: its first action is
the freeze preflight, which correctly rejects a changed frozen tree before the
repin, so at stage (a) it cannot pass by construction. What was run, on the
stage-(a) tree: targeted `lake build` of
`Complexity.TMVerifier.TuringToolkit.GateNBodyDriver`,
`Tests.TMGateNBodyDriverSurfaceTests` and `Tests.AxiomsAudit`, serialized, all
succeeding; the hygiene scans for `axiom`, `sorry`/`admit`, `native_decide`,
`Lean.ofReduceBool`, `Lean.trustCompiler` and `unsafe` over active pnp3/pnp4
Lean; `git diff --check`; `scripts/check_doc_honesty.sh`;
`python3 scripts/validate_version_manifest.py`; and the non-freeze governance
gates of `scripts/check.sh` that do not depend on the freeze preflight. The
freeze checker was run exactly once, to record the expected rejection, and was
not weakened or bypassed in any way.

**Still owed before merge.** All of it: stage (b) itself (set `FROZEN_COMMIT`
and `FROZEN_TREE` to the stage-(a) commit and its
`git rev-parse HEAD:pnp3/Complexity/TMVerifier` subtree, update this file's
header, regenerate the manifest with the documented `--write-manifest`
command), then the complete local gate set including `./scripts/check.sh` and
the four freeze-specific gates on the repinned tree, then the remote half
against the *final* head: green `ci.yml` and `lean.yml`, the required PR review,
the repository owner's exact full-SHA attestation comment, the
`tmverifier-unfreeze` label, and a history-preserving merge. None of that has
happened. There is no PR, no independent review of this slice, and no CI result
of any kind, and nothing in this record should be read as asserting one.
