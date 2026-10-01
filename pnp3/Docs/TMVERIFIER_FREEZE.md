# TMVerifier freeze decision

**GN-E2-5d first-request launch and successful interception (2026-10-01,
Infrastructure only):** from exact base
`5aa3f945025de7cb06fe83e4330a13685e15e8d9`, the finite `requestReady` reverse
scanner now executes the installed request back to its opening `bof` and
enters the fixed G1 start. `gnCS_encodeGN_firstLaunch_exact` assumes only the
selected first-gate equation `hg`. `gnCS_encodeGN_firstOutputDone_exact` and
`gnCS_encodeGN_firstReturned_exact` additionally require the actual request's
`spec = some res`; neither result nor proof selects runtime behavior.
The exact full-tape real-input fixtures launch at **1333**, reach output-done
at **1562**, and intercept at **1563/head107**, with scratch cell111=true and
GN reserved cell11=false. The independent 33/34-step kernel launch probe and
five-step reserved-1101 rejection with stable padding pass. Canonical first
`notGate 0` on `[true]` still launches but has undefined specification.

All requested targeted Lane B builds, the focused audit and the aggregate
`Tests.AxiomsAudit` passed. This does not include the exclusive full gate.

The dependency-closed change is **789 changed Lean lines (777 added,
12 deleted), eight modules plus lakefile.lean**, below both frozen caps.
Only the control owner and the obsolete writer row/prose change in the
frozen subtree. The 17 new public propositions have full-proposition wrappers;
focused and aggregate audits each directly root all 34 owner/wrapper names
and the revised writer pair. Existing `Classical.choice` dependencies are
reported, not removed or used for runtime extraction.

Returned-bit commit, cursor/spent advance, repeated gates, verdict, GN
acceptance, first-arrival minimality, composed runtime adequacy,
`ContentVerifierBridge`, and Lane B N1/N3 remain open. No pnp4 bridge or
P-vs-NP source obligation is reduced. The user excludes the globally exclusive
full gate, push and PR creation from this local task. Prior release reviews
and full gates below are historical and do not certify GN-E2-5d.
See the [frozen targets, premises and implementation evidence](GN_E2_5D_FIRST_REQUEST_LAUNCH.md).

Stage (a), `f07c4439c3f04a5455b624403be8efcfb16be29e`, commits the validated implementation with the old
pin intentionally failing on exactly two frozen files. Its direct child is the
stage-(b) content-address repin to subtree `bf871e090bf1ca564293502e4ff09c1c5f8ca9a0` (120 objects), with no
Lean or frozen-byte change. The repinned checker, freeze negative controls and
local policy tests pass. Both GN-E2-5c stages and the exact base remain ancestors.
The local work is complete; no push, PR or full exclusive gate was performed.

**Historical GN-E2-5c values induction and first-request tail (2026-10-01,
Infrastructure only):** on base `b71eb6ca3ff4101d6d1596dfb4fc06ce63f845c7`,
`GateNValuesInduction` executes every actual input value through the live
classifier using the landed one-value theorem, then executes the existing
output-false tail writer to the exact `gnFirstRequestReadyConfig` endpoint.
The initial theorem assumes only the selected first-gate equation. Its clock
is `gnValuesEntrySteps + (k*(8*d+38) + (4*d+20))`, with `k = r.inputs.length`
and `d = gnValuesTailDistance r g`. The full nonempty request now fits within
**529 added Lean lines, six Lean files including lakefile.lean (five modules)**.
The 136-step two-value and 1300-step encoded nonempty fixtures pass, as do the
targeted Lane B builds and all 22 direct new audit roots. The exact frozen
premises, surfaces, evidence and limits are in the
[GN-E2-5c record](GN_E2_5C_VALUES_INDUCTION.md).

Stage (a), `d1694e4b8c3e4838fb38d682f4c10d5ffacc6eb8`, committed the validated frozen
bytes and registrations/surfaces/audits. Stage (b),
`4ffd71f356e13babde80397186ee176e5455ccc5`, repinned the checker and manifest to
stage (a)'s subtree `b2762b378800f81e6adaaa3ecbe6b277ddd59482` (120 objects), with no
frozen-byte change. The freeze checker, negative controls and local policy
unit tests passed. Both stages preserve the exact base in ancestry. The docs-only
child `6c21021a1ca9685bd7fa563c7cc005bc87fd08b8` and its docs-only follow-up
`e984d32d16fe172307127fa8c58ceaf2009e6173` corrected the GN-E2-5b/5c records
without changing Lean, pins or frozen bytes. The integration head
`85a8c61b6c926b4a54594a84504c28ac4e11f269` subsequently
passed the globally exclusive 17-step full gate; exact-head Codex and Fable 5.1
reviews both reported **APPROVE**. PR #1808 carries the `Infrastructure` and
`tmverifier-unfreeze` labels, the owner's full-SHA attestation, and successful
CodeQL and freeze-policy runs. The final raw CI rollup and a fresh agentic review
of this release-record correction remain merge gates. Exact evidence and scope
limits are recorded in the GN-E2-5c record linked above.
Request launch, delegation, returned-bit commit, repeated gates, verdict,
acceptance, first arrival and new-clock/runtime adequacy remain open, together
with Lane B's N1/N3 carry-forward items. No P-vs-NP source obligation is reduced.

**Current authoritative frozen tree:** `bf871e090bf1ca564293502e4ff09c1c5f8ca9a0`.
**Current provenance commit (`FROZEN_COMMIT`):** `f07c4439c3f04a5455b624403be8efcfb16be29e`.
**Stage-(a) whole repository tree:** `754cc5ce57827bacf71e92515fb00ecd808fda06`.
This provenance identifies the authorized implementation snapshot, not an
independent review or remote attestation. The checker’s “reviewed provenance”
output verifies the commit/tree identity only. The freeze pins source bytes,
not the full semantic/toolchain dependency closure.

The following GN-E2-5b and earlier records describe their dated snapshots;
their then-open values-list/tail work is discharged only by GN-E2-5c above.
Their reviews and gates do not transfer to this new slice.

**Historical GN-E2-5b one-value Infrastructure slice (2026-10-01):** on merged base
`b83de46cc67ecfbf52093807b66b9cd7acf04010`, the live classifier and installer
copy one value in `8*d+37` rows through the data exit; the stationary dispatch
returns to `valuesEntry` after `8*d+38`. The real initial capstone returns at
head 8 with one copied `data` frame and the request tail pending (1184 rows in
the literal example). The implementation at reviewed head
`df7699642bf22673cfee7f3ebe6c37e36128360a` measured **903 changed Lean lines
across seven Lean files including `lakefile.lean`**, with no transition-row
changes. Its targeted Lane B builds, 44 focused audit roots, freeze checker
and negative controls passed as recorded in the
[implementation and review record](GN_E2_5B_VALUES_COPY.md).
Stage (a), `b16d816e011560e86ea81ffa1a08da20e18cd2d2`, committed the frozen
bytes; stage (b), `df7699642bf22673cfee7f3ebe6c37e36128360a`, repinned tree
`e4fa8f333a055e8bbce4c258af7f84719426416a` with 119 manifest objects and
changed no frozen byte. Fable 5.1 and Codex both approved that exact stage-(b)
head; Fable listed seven documentation notes. Neither review covers this later
correction.
The documentation-only follow-up preserved both stages, frozen bytes and pins.
At integration release head `e65231fc1be4c12d9338b39dd67e8d8e9a6b8571`,
the targeted Lane B build passed, exact-head remote CI completed `scripts/check.sh`,
and exact-head Codex and Fable 5.1 reviews approved. PR #1806 carries the `Infrastructure` and
`tmverifier-unfreeze` labels, the owner's full-SHA attestation, and a successful
freeze-policy run. Qodo's later documentation finding is corrected by this dated
release record; fresh checks and reviews of that correction remain required before
merge. At that GN-E2-5b snapshot full-list execution and nonempty request
completion remained open; GN-E2-5c now discharges those execution targets.
**Lane B owns the deferred N1/N3 follow-up**, explicitly still open in the
[carry-forward register](GN_E2_5B_VALUES_COPY.md#carry-forward-ownership).
Historical GN-E2-5a records below retain their dated scope.

**Historical GN-E2-5b frozen tree:** `e4fa8f333a055e8bbce4c258af7f84719426416a`.
**Historical GN-E2-5b provenance commit:** `b16d816e011560e86ea81ffa1a08da20e18cd2d2`.
**Historical GN-E2-5b stage-(a) whole repository tree:** `7ef7a45e0c53bbd1d24c615a9a523d7615810b25`.
That GN-E2-5b provenance names its stage-(a) snapshot; the stage-(b) reviews and the later
integration-head reviews apply only to their named heads as recorded above. The
owner's PR #1806 attestation names `e65231fc1be4c12d9338b39dd67e8d8e9a6b8571`.
The inherited GN-E2-5a preamble below is
historical; its old pins and review outcomes do not apply to GN-E2-5b.

**Historical owner-docstring correction (2026-09-29, Infrastructure only):** Qodo's
finding at PR #1804 exact head
`1b5aa3e219d30d2292c8cd13bbc8e68acbbb1d90`, as supplied by the owner,
is addressed by the two-stage migration recorded in `TMVERIFIER_FREEZE.md`.
Stage (a) is `1e7fe40592001142378ff3620c888045d8c10594`; stage (b)
repins tree `145252565dc2538c6c01c19fc2f6814abc1c3a8d` and updates these
records. The size at that correction was **1499 changed Lean lines
(1468 added, 31 deleted) across 8 files**, including `lakefile.lean`, against merge base
`2f8a3d5e6f90fe41a2cd7bc240d3c9fad407b68e`. The 1497-line counts below
are historical measurements before this correction. The owner-label deferral
was closed; GN-E2-5b implementation was paused at that date. No review of
either owner-docstring correction head was claimed in that record. The sole
repository category remains
`Infrastructure`; the existing `tmverifier-unfreeze` labeling intent remains.
No remote label or attestation is issued by this local correction.

**Historical integration update (2026-09-29, Infrastructure):** the third integration merge
has parents `03b8184402fb7bf092d3bcd72ca7c936fab9862b` and
`2f8a3d5e6f90fe41a2cd7bc240d3c9fad407b68e`, in that order. It preserves G3m
and GN-E2-5a, including the stage-(a) and stage-(b) ancestry, with no frozen
subtree, pin or manifest changes. The comparison base at that integration was the second
parent; the changed-Lean count remains **1497 lines across 8 files**, including
`lakefile.lean`. References below to two integration merges or `9445a93e` as
current are the prior snapshot's bookkeeping. Historical reviews and checks
remain attached only to their recorded heads; this integration establishes no
full-check or review gate result and did not begin GN-E2-5b at that date.

**Historical GN-E2-5a status (2026-09-29):** this block records that slice's
snapshot and review inventory; its pending-gate and branch statements belong
to that date. The Qodo owner-docstring correction used a separate two-stage
migration: stage (a), `1e7fe40592001142378ff3620c888045d8c10594`,
changed only `which E2-4b owns` to `which GN-E2-5b owns`; stage (b)
repinned the checker and manifest to that commit and subtree `145252565dc2538c6c01c19fc2f6814abc1c3a8d`.
The GN-E2-5a pair `11dc8e82` → `311abc6b` remains in ancestry.
The new correction heads have no independent review claimed.
Two independent
exact-head reviews ran at the stage-(b) head `311abc6b` and split: Codex
returned **APPROVE** with no blocking finding and one P3 documentation note,
and Claude returned **BLOCK** on four documentation findings. Neither reported
a Lean, execution, surface, size-gate-arithmetic or freeze-content defect; both
are recorded with their verdicts, evidence and limits in the GN-E2-5a record
below. **History through `bceb38db98cf7d43fda523384969d3f320ed4ced`
(review inventory recorded 2026-09-29):** the later first-parent heads are the
docs-only correction `3195ffc1`, this branch's integration merges of `main` —
`4abaac92`, which brought in `main` at `71179c6d`, and `d01e2c3e`, which brought
in `main` at `9445a93e` — and the docs-only corrections `40ea2346`, `51db7753`
and `bceb38db`, in that order. `3195ffc1` fixes the stage-(b) findings; the
reviews at `d01e2c3e` split, and `40ea2346` fixes their documentation findings.
At `40ea2346`, Codex reported two **P2** documentation findings with no
APPROVE/BLOCK label; the second run ended at its turn limit with no verdict.
`51db7753` fixes those P2 findings. Codex reviewed `51db7753` as **FINDINGS**,
one P3 and no P0–P2; `bceb38db` fixes that P3 layout-versus-byte-identity wording.
At `bceb38db`, Codex initially returned **PASS**, while Opus returned
**FINDINGS** on P2-A/P2-B provenance defects. The subsequent Codex adjudication
upheld both and the nonblocking six-of-eight scan wording nit, acknowledging
that its earlier documentation PASS was too broad. None reported a blocking
theorem or freeze-content defect. The reports, disagreement, evidence and limits
are recorded below. No review is claimed for `3195ffc1` or `4abaac92`.
**None of these reports reviews or approves a later correction SHA**; no
attestation or label is claimed for any head on this branch. One complete
`./scripts/check.sh` is on record for this branch's content — logged between
`4abaac92` and `d01e2c3e`, carrying this slice's own freeze pin and ending "All
checks passed" — but its checkout and exclusivity are not established and it is
no head's gate result; the record below states exactly what it does and does not
establish. The complete final-head gate, a fresh
exact-head review of the corrected head, remote CI, owner attestation, PR
review and merge are still owed and are not claimed here.
The GN-E2-4a migration, whose pins GN-E2-5a's stage (b) replaced, has since been
merged into `main` by PR #1801 as the merge commit `71179c6d`; what it
discharged and what it still owes are listed in its own record, not here, in
`main`'s copy of that record, which the first of those two integration merges
brought into this file. The reviews recorded there are named with their reviewed
head and verdict: at the stage-(b) head `e2c3ee33`, two were reported as
**APPROVE** and one as **REQUEST_CHANGES** on documentation; at the docs head
`4e182c03`, both the Codex and Claude reruns returned **BLOCK** on contradictory
review claims; and at the reviewed head `6718b422`, PR #1801 records an
exact-head Codex **APPROVE**, an exact-head Fable 5.1 **APPROVE**, a complete
`./scripts/check.sh` in which all checks passed, the owner's full-SHA
attestation comment and the `tmverifier-unfreeze` label. None of that is a gate
result for GN-E2-5a, and none of it transfers to the current pin.
The earlier GN-E2-3b migration, whose pins were replaced by `e2c3ee33`, landed
both of its stages on its own branch and was then merged by PR #1777 on
2026-09-23 as the merge commit `48151689`, which preserved history, so its
provenance commit `7b53a08f` is an ancestor of this branch. Local Git records
neither the remote gate results for that merge nor the required PR review, so
neither is claimed; what it discharged and what local history cannot show are
split out in its record, not here.
**GN-E2-5a historical frozen tree:** `145252565dc2538c6c01c19fc2f6814abc1c3a8d` —
the Git tree object of that snapshot, verified by the checker before the
GN-E2-5b repin recorded above.
**GN-E2-5a historical provenance commit:**
`1e7fe40592001142378ff3620c888045d8c10594` (2026-09-29) — the owner-docstring correction
stage-(a) commit whose subtree the then-current pin named. The checker called
this value "reviewed provenance" for its role as a pin; this historical
inventory claimed no independent review of that final migration head.
**Previously frozen at:** tree `4213b315075f67468451a6736afc04486df0350c`,
provenance commit `11dc8e8200368db075821d74ed9acd60665bc398` (2026-09-28),
before that at tree `c544405f94cb68755cad3dc5c6a0639517a2967b`,
provenance commit `b35bdca2cb24af709144998af5c4402d42a18aa5` (2026-09-27),
before that at tree `b49456d6e08bbce69fd94af2d2a97beef438d210`, provenance
commit `7b53a08fc13517fcf8b2c73b45f6515102a13863` (2026-09-20), before
that at tree `7ef6ac6e119f0f078f9c896f17415fa560a6edf3`, provenance commit
`249435bfa4cb540822e47844107781042f18537f` (2026-09-19), and before that at
commit `42c598815c8e7d27a53f26102705f84455c6979d` (2026-09-02); see the
migration record below for those five historical unfreezes, the sixth,
GN-E2-5b, and the seventh, GN-E2-5c, whose pin is recorded in the current header.

**Those SHAs are provenance commits, not reviewed heads.** Each one is the
`FROZEN_COMMIT` its pin named — the commit whose subtree the pin identified — and
none of them is a head at which a review outcome is recorded. `b35bdca2` in
particular is the GN-E2-4a **stage-(a)** commit, the commit that introduced the
frozen bytes of tree `c544405f`, and the GN-E2-4a record below says in as many
words that no independent adversarial review was claimed for its stage (a).
Review outcomes belong only to the heads reviewers actually read: for GN-E2-4a
those are the superseded stage-(b) head `23335cc3` (**REQUEST_CHANGES**), the
retained stage-(b) head `e2c3ee33` (two **APPROVE**, plus an earlier
**REQUEST_CHANGES** pass) and the docs head `4e182c03` (two **BLOCK**), each
recorded below with its verdict and its evidence limits — and, written after this
branch's copy of that record and merged in here from `main`, the pre-merge head
`6718b422` (an exact-head Codex **APPROVE** and an exact-head Fable 5.1
**APPROVE**); that slice's final head `a312622f`, and `main`'s merge commit
`71179c6d` itself, carry no gate result of their own. No outcome is carried
from one of those heads to another commit on the strength of a shared frozen
subtree. The commits resolving to tree `c544405f` are not only those heads: at
least ten do — `b35bdca2`, `23335cc3`, `e2c3ee33`, `4e182c03`, `13f36c1d`,
`6718b422`, `a312622f`, `71179c6d`, `f2237a68` and `9445a93e` — and of those
only `23335cc3`, `e2c3ee33`, `4e182c03` and `6718b422` have review
outcomes recorded below. `23335cc3` is the case that makes the rule bite: it
carries exactly those bytes **and** a **REQUEST_CHANGES**, and that verdict
travels no further along the shared subtree than the approving ones do. The
same rule governed the original GN-E2-5a pin — `11dc8e82` is
the GN-E2-5a
stage-(a) provenance commit and carries no review of its own, and the `4213b315`
subtree it shares with the stage-(b) head extends no review to it.

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

## Authorized GN-E2-5d local migration

The owner explicitly authorizes this narrow Infrastructure slice and the two
ordered commits in the GN-E2-5d record. The machine owner may add finite launch
control and activate requestReady; the writer may replace only the obsolete
row conjunct/prose; lakefile registrations are authorized. Downstream proofs,
fixtures, full-proposition surfaces and direct audits live outside the frozen
tree. All other frozen files remain byte-identical to the exact base.
A scoped `backward.eqns.nonrecursive false` on the enlarged transition table
avoids equation-generation timeouts without changing its semantics or any
existing proof. The private base cache is copied, not shared for writes.

Stage (a) intentionally retains the old checker/manifest: its freeze failure
must identify exactly the owner and writer. Stage (b) alone repins the
committed stage-(a) subtree, with no frozen-byte changes. The owner's current
task explicitly requires targeted Lane B builds and prohibits the globally
exclusive full gate; this is a local implementation record, not a remote
release approval. The general future release/attestation policy below remains
in place. No push, PR, remote attestation or remote review is performed here.

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

   The S11 unfreeze has the same two-stage shape, though it predates part of the
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
two-stage rule and with no other stage resumed. Both of its stages are recorded
below, together with the split between what that migration has already
discharged and what its remote half still owes. The sentence above still governs
everything else, and no further slice may be taken without a fresh
authorization.

**A second authorized exception, 2026-09-27.** The repository owner gave that
fresh authorization for one GN-E2-4a slice — continuation of the frozen
evaluator/runtime chain past the landed `recordDone` endpoint, toward the
values/tail writer — under this record's two-stage rule and with no other stage
resumed. Both of its stages are recorded below, together with what it still
owes. At that date E2-4b and later TMVerifier stages remained paused;
each later slice required its own authorization, as recorded next.

**A third authorized exception, 2026-09-28.** The repository owner authorized
the GN-E2-5a first-request values/tail writer slice under the same two-stage
rule. It is deliberately rescoped to the zero-input first-gate path to stay
inside the ordinary 1,500 changed-Lean-LOC cap, which is **not waived**; that
measurement is stated exactly in the GN-E2-5a record below, where it is green
at 1497 lines across 8 modules against the current merge base `9445a93e`, and
was the same 1497 at each of the two superseded bases while each of them was the
current one — `13f36c1d`, this branch's own base commit, which PR #1801 made the
merge base by merging GN-E2-4a into `main` out from underneath this branch, and
`71179c6d`, PR #1801's merge commit, which this branch's first integration merge
of `main` made the merge base in turn. Later
value-copy rounds, launch, next-gate looping, verdict and
acceptance remained paused under that authorization. The stage above called `E2-4b` was
never taken under that name: GN-E2-5a landed its carried-`data` exit route,
and the per-value copy it deferred was assigned to **GN-E2-5b**, which still
needed fresh authorization at that date. Read every other `E2-4b` in this file as
`GN-E2-5b`, whether it stands before this paragraph or after it; the GN-E2-4a
record's deferral of the carried-`data` exit route is among those standing
after, and the GN-E2-5a record's notes on the retirement are the rest.

**Authorized one-value continuation, 2026-10-01.** The owner authorized the
bounded GN-E2-5b slice recorded below: one physical value copy, return to the
live classifier, residual handoffs and the real-input one-value endpoint.
At that GN-E2-5b boundary, full-list induction and nonempty request completion
were deferred; GN-E2-5c now executes them. Later construction remains open.
The [carry-forward register](GN_E2_5B_VALUES_COPY.md#carry-forward-ownership)
assigns the N1/N3 items, still open after GN-E2-5c, to Lane B;
the present documentation remediation implements neither item.

## Migration record

### 2026-09-19 — S11 one-gate acceptance closure (single reviewed unfreeze)

Re-pinned from `42c59881` to `249435bf`. This was the only unfreeze since the
tree was frozen on 2026-09-02 until the GN-E2-3b migration recorded below;
every mention of tree `7ef6ac6e` and commit `249435bf` in this section
describes the pin as it stood at this migration, and the current pin is the one
in the header.

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

**Scope at the time of the S11 migration.** This was a narrow migration of one
already-reviewed theorem slice, not a resumption of the paused roadmap.
GN-E2-3b and later gate-by-gate construction then remained paused; the later
GN-E2-3b migration is recorded separately below. The next active track remained
the versioned uniform `P` model and its circuit simulation, and nothing here
reduces `VerifiedNPDAGLowerBoundSource` or `SearchMCSPWeakLowerBound` or discharges a
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

### 2026-09-20 — GN-E2-3b body driver (stage (a) 2026-09-20, stage (b) repin 2026-09-22)

Re-pinned from tree `7ef6ac6e` (reviewed at `249435bf`) to tree `b49456d6`,
the `pnp3/Complexity/TMVerifier` subtree of the stage-(a) commit
`7b53a08fc13517fcf8b2c73b45f6515102a13863`. This is the second unfreeze since
the tree was frozen on 2026-09-02, and it landed as the two separate commits
requirement 3 prescribes, in that order.

**Stage (a), commit `7b53a08f`.** The new frozen bytes together with their
registration, and nothing of the pin: `FROZEN_COMMIT`, `FROZEN_TREE`,
`SCHEMA_VERSION`, `spec/tmverifier_freeze.json` and
`spec/version_manifest.toml` are untouched by it, and the header of this file
at that commit still named tree `7ef6ac6e` reviewed at `249435bf`. That is the
required order: requirement 3(a) says the new bytes must be committed first,
because `--write-manifest` refuses to author a pin whose provenance commit does
not yet exist. Between the two commits the frozen tree on this branch
legitimately disagreed with the pin, and the freeze checker failed closed
reporting exactly one added path,
`pnp3/Complexity/TMVerifier/TuringToolkit/GateNBodyDriver.lean`.

**Stage (b), the separate commit that adds this paragraph.** It sets
`FROZEN_COMMIT` to `7b53a08fc13517fcf8b2c73b45f6515102a13863` and
`FROZEN_TREE` to `b49456d6e08bbce69fd94af2d2a97beef438d210` in
`scripts/check_tmverifier_freeze.py`, updates the header of this record with
the same pair, and regenerates `spec/tmverifier_freeze.json` with the
documented `python3 scripts/check_tmverifier_freeze.py --write-manifest`,
which re-verified that `7b53a08f` resolves here and records exactly `b49456d6`
before writing. The manifest goes from 115 to 116 `files` entries; the only
entry-level change is the one new blob, and every other entry is
byte-identical. `SCHEMA_VERSION` stays at 3 and the
`[snapshot.tmverifier_freeze]` row of `spec/version_manifest.toml` is
untouched, because the manifest's shape did not change. Stage (b) changes no
frozen byte and no Lean source. Beyond the pin it touches only prose that named
the old pin: this record, the preamble and GN-E2-3b slice sentence of
`TMVerifier_Session_Plan.md`, the two freeze sentences of `STATUS.md`, and one
docstring of `scripts/test_tmverifier_freeze.py` that counted the frozen
entries. It amends neither stage (a) nor anything before it.

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

**Gates at stage (a) — what was actually run, and only that.** The complete
`./scripts/check.sh` was **not** run at stage (a) and is **not** claimed for it:
its first action is the freeze preflight, which correctly rejects a changed
frozen tree before the repin, so at stage (a) it cannot pass by construction.
What was run, on the stage-(a) tree: targeted `lake build` of
`Complexity.TMVerifier.TuringToolkit.GateNBodyDriver`,
`Tests.TMGateNBodyDriverSurfaceTests` and `Tests.AxiomsAudit`, serialized, all
succeeding; the hygiene scans for `axiom`, `sorry`/`admit`, `native_decide`,
`Lean.ofReduceBool`, `Lean.trustCompiler` and `unsafe` over active pnp3/pnp4
Lean; `git diff --check`; `scripts/check_doc_honesty.sh`;
`python3 scripts/validate_version_manifest.py`; and the non-freeze governance
gates of `scripts/check.sh` that do not depend on the freeze preflight. The
freeze checker was run exactly once, to record the expected rejection, and was
not weakened or bypassed in any way.

**Gates at stage (b) — what was actually run, and only that.** On the tree of
the stage-(b) commit: the four freeze-specific gates —
`python3 scripts/check_tmverifier_freeze.py` (116 Git objects match tree
`b49456d6`, reviewed provenance `7b53a08f` verified),
`scripts/check_tmverifier_freeze.sh`, `scripts/test_tmverifier_freeze.sh` (the
complete negative-control suite, including the self-hosted provenance-free
control) and `node scripts/test_tmverifier_freeze_policy.js` — plus
`python3 scripts/validate_version_manifest.py`, `scripts/check_doc_honesty.sh`,
`python3 -m py_compile` on both changed scripts, `git diff --check`, the
hygiene scans for `axiom`, `sorry`/`admit`, `native_decide`,
`Lean.ofReduceBool`, `Lean.trustCompiler` and `unsafe` over active pnp3/pnp4
Lean, and a targeted `lake build` of
`Complexity.TMVerifier.TuringToolkit.GateNBodyDriver`,
`Tests.TMGateNBodyDriverSurfaceTests` and `Tests.AxiomsAudit`, all passing.
The complete `./scripts/check.sh` was **not** rerun at stage (b) and is not
claimed for it either; no Lean source differs from the stage-(a) tree.

**Discharged at branch head `50f3eadd` — completed, and only this.** The
complete `./scripts/check.sh` was run locally on the tree of head
`50f3eadd48a88e7ce6cde31791cb50a1d9b3b753` and passed. That head's
`pnp3/Complexity/TMVerifier` subtree is the pinned tree
`b49456d6e08bbce69fd94af2d2a97beef438d210`, so the run covered exactly the
frozen bytes pinned here. Two independent read-only adversarial reviews of the
slice — Codex and Claude Fable 5.1 — were completed at that same exact head.
The slice was open at that point as PR #1777, which carries the
`Infrastructure` and `tmverifier-unfreeze` labels and the owner's exact full-SHA
attestation comment `/tmverifier-unfreeze
50f3eadd48a88e7ce6cde31791cb50a1d9b3b753`. An automated Qodo review of that PR
raised one documentation finding — that this record denied evidence the PR
already carried — and the docs-only commit that rewrites these two paragraphs
is its fix.

**Still owed before merge.** The remote gate results against the *final* head:
`ci.yml` and `lean.yml` observed green, and the `TMVerifier Freeze Policy`
rollup observed passing on that head. When this paragraph was written those
runs had not been observed to completion, so **no** green CI is claimed here
and nothing in this record should be read as asserting one; an earlier
`TMVerifier Freeze Policy` run against a pre-attestation head failed as
designed. Also owed: the required PR review, a history-preserving merge, and
the post-merge verification below. The docs-only fix commit named above changes
the head SHA, so the attestation must be reposted for the new 40-character
head, the label retriggered, and the remote gates rerun there; the complete
`./scripts/check.sh` was **not** rerun for that commit and is not claimed for
it — it changes no frozen byte and no Lean source, which is a reason to expect
the unrun gate to pass and not a record that it did.

**Merge with a merge commit — required, for provenance.** As for the S11
migration above: this branch must be merged with a merge commit or an exact
fast-forward, never squashed or rebased, and the branch itself must not be
rebased or force-pushed while its PR is open. A rewriting merge would not break
any check — the frozen tree object `b49456d6` travels with the bytes — but it
would drop `7b53a08f`, the commit this pin names as provenance, from `main`'s
ancestry. Bringing `main` into this branch must likewise be a merge commit, so
that stage (a) and stage (b) remain two distinct, auditable commits.

**Post-merge verification (required).** Immediately after the merge, on an
updated `main` or a fresh clone, run both:

```text
git merge-base --is-ancestor 7b53a08fc13517fcf8b2c73b45f6515102a13863 origin/main
python3 scripts/check_tmverifier_freeze.py
```

The second is the content gate: it must report that the frozen tree matches
`b49456d6e08bbce69fd94af2d2a97beef438d210`, and it is expected to pass under
any merge style. The first is the provenance audit and must exit `0`. If it
does not, the merge was a rewriting one and the provenance link was dropped:
the frozen content is still verified and `main` is not broken, so the response
is not an emergency but a deliberate repin onto a commit in `main`'s ancestry,
landed under this same unfreeze gate, plus a note in this record saying which
merge dropped the link.

**Merged 2026-09-23 — what local history does and does not show.** The two
paragraphs above were written before the merge and record what had not been
observed then; they are historical. PR #1777 was in fact merged as the merge
commit `48151689ac127d0616ba40e6864d10b21f3d9d49`, whose second parent is the
docs-only fix commit `635ac15e` named above, so the merge was a
history-preserving one and not a squash or a rebase. The provenance audit
prescribed just above therefore exits `0` on this branch: both
`7b53a08fc13517fcf8b2c73b45f6515102a13863` and the reviewed head `50f3eadd` are
ancestors of it. Local Git does not record the remote gate results against the
final head or the required PR review, so no green remote gate and no completed
PR review is claimed for GN-E2-3b here; only the merge and the surviving
provenance link are.

### 2026-09-27 — GN-E2-4a values rewind (stage (a) and stage (b) repin, both 2026-09-27)

**Progress classification: Infrastructure only.** This migration and its prose
recovery reduce neither `VerifiedNPDAGLowerBoundSource` nor
`SearchMCSPWeakLowerBound`, produce neither
`ComplexityInterfaces.NP_not_subset_PpolyDAG` nor `ResearchGapWitness`, and
discharge no `CanonicalAsymptoticVerifierComponents` obligation.

Re-pinned from tree `b49456d6` (reviewed at `7b53a08f`) to tree `c544405f`,
the `pnp3/Complexity/TMVerifier` subtree of the stage-(a) commit
`b35bdca2cb24af709144998af5c4402d42a18aa5`. This is the third unfreeze since
the tree was frozen on 2026-09-02, and the second authorized exception recorded
above. It landed as the two separate commits requirement 3 prescribes, in that
order.

**Stage (a), commit `b35bdca2`.** The new frozen bytes together with their
registration, and nothing of the pin: at that commit `FROZEN_COMMIT`,
`FROZEN_TREE`, `SCHEMA_VERSION`, `spec/tmverifier_freeze.json` and the
`[snapshot.tmverifier_freeze]` row of `spec/version_manifest.toml` are
byte-identical to their GN-E2-3b values, and the header of this file there
still names tree `b49456d6` reviewed at `7b53a08f`. That is the required order:
requirement 3(a) says the new bytes must be committed first, because
`--write-manifest` refuses to author a pin whose provenance commit does not yet
exist.

**The expected fail-closed state between the two commits, stated exactly.** At
stage (a) the frozen tree on this branch legitimately disagreed with the pin.
On that tree `python3 scripts/check_tmverifier_freeze.py` reported `TMVerifier
freeze violation.` with exactly one `Added` path,
`pnp3/Complexity/TMVerifier/TuringToolkit/GateNValuesRewind.lean`, and exactly
one `Changed` path,
`pnp3/Complexity/TMVerifier/TuringToolkit/GateNFixedDelegateRelocation.lean`;
nothing was `Removed`. The freeze preflight of `scripts/check.sh` therefore
rejected that tree before any build, which is why the complete
`scripts/check.sh` was **not** run and is **not** claimed for stage (a) — it
could not pass there by construction. The checker was neither weakened nor
bypassed, and stage (a) authored no pin: `--write-manifest` was not invoked at
that stage.

**Stage (b), the separate commit that adds this paragraph.** It sets
`FROZEN_COMMIT` to `b35bdca2cb24af709144998af5c4402d42a18aa5` and `FROZEN_TREE`
to `c544405f94cb68755cad3dc5c6a0639517a2967b` in
`scripts/check_tmverifier_freeze.py`, updates the header of this record with
the same pair, and regenerates `spec/tmverifier_freeze.json` with the
documented `python3 scripts/check_tmverifier_freeze.py --write-manifest`, which
re-verified that `b35bdca2` resolves here and records exactly `c544405f` before
writing. The manifest goes from 116 to 117 `files` entries; the only
entry-level changes are the one new blob
`TuringToolkit/GateNValuesRewind.lean` (`git_oid` `0e895d76`, mode `100644`)
and the one modified blob `TuringToolkit/GateNFixedDelegateRelocation.lean`
(`git_oid` `2c63db41` → `93ba7edb`, mode `100644`), and the other 115 entries
are byte-identical. `SCHEMA_VERSION` stays at 3 and the
`[snapshot.tmverifier_freeze]` row of `spec/version_manifest.toml` is
untouched, because the manifest's shape did not change. Stage (b) changes no
frozen byte and no Lean source: the working `pnp3/Complexity/TMVerifier`
subtree is still exactly `c544405f`, the tree stage (a) committed. Beyond the
pin it touches only prose: this record, the preamble and GN-E2-4a slice
paragraph of `TMVerifier_Session_Plan.md`, and two freeze paragraphs of
`STATUS.md`. All of that prose either named the old pin or described the
now-closed one-stage state, with one exception — stage (b) also corrects the
audit-root count in the stage-(a) gates paragraph below, from a wrong `4881` to
the verified `4910`. It amends neither stage (a) nor anything before it: the
stage-(a) commit object is untouched, so the provenance SHA this pin names
still resolves.

**Why the frozen artifact itself had to change (requirement 1).** The slice
activates the `recordDone` row of `gnTransition` and adds two `GNState`
constructors. `GNState`, `gnTransition`, `gnCS`, `GNM`, `gnClock`, `encodeGN`,
`gnRecordsStart`, `gnRecordSize`, `gnFirstRecordDoneSteps` and
`gnFirstRecordDoneConfig` are all defined inside the snapshot, and a transition
row and an inductive constructor have no out-of-tree form at all: a module
outside the frozen tree cannot add a constructor to `GNState` or change a row
of `gnTransition`. Relocation would also not avoid this gate, because
`lakefile.lean` is blanket-protected and a new module must be registered there.

**What entered the frozen tree.** One new module,
`TuringToolkit/GateNValuesRewind.lean`, and one modified module,
`TuringToolkit/GateNFixedDelegateRelocation.lean`. No other file in the frozen
subtree is added, removed, renamed or modified. The modification to the control
module is exactly: two `GNState` constructors, `rewind (buffer :
GNInstallBuffer)` and `valuesEntry`; the three-constructor finite mode type
`GNRewindMode` with its frame-level `gnRewindAdvance` and bit-level
`gnRewindComplete` tables and the one-buffer `gnRewindControl` row set; the
`.recordDone` row, which was `(0, .recordDone, scan, .stay)` and is now
`(0, .rewind .r3, scan, .left)`; the two new rows `.rewind buffer` and
`.valuesEntry`; and the module docstring. No machine, clock, encoder, phase
count, start state, accept state, existing row, existing definition or existing
theorem is otherwise changed. In particular `gnInstallExitDispatch`,
`GNInstallExitContinue` and `GNInstallExitInvalid` are byte-identical, so the
installer shuttle's exit semantics — including its rejection of a carried
`data` frame — are exactly as reviewed.

No previously exported theorem changes meaning. `recordDone` never had a public
stability theorem (`GateNBodyRound.lean` says so in as many words), so no
exported statement asserted the row this slice replaces; every `GateN*` and
`GateOne*` theorem downstream of the control module is unchanged in statement
and re-proved unchanged.

**What the new module proves.** Its two capstones are:

```lean
gnCS_valuesRewind_exact (n : Nat) (pre post : List G1Frame)
    (hpre : ∀ f ∈ pre, f ≠ G1Frame.bof)
    (hroom : 4 * pre.length + 4 < GNM.tapeLength n) :
    TM.runConfig (M := GNM) (gnValuesRewindConfig n pre post hroom)
        (gnValuesRewindSteps pre.length) =
      gnValuesEntryConfigOf n pre post hroom

gnCS_encodeGN_valuesEntry_exact {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    TM.runConfig (M := GNM) (GNM.initialConfig (gnPoint (encodeGN r)))
        (gnValuesEntrySteps r g) = gnValuesEntryConfig r g hg
```

Both are genuine `TM.runConfig` execution with an exact schedule, a literal
state, an exact head and a complete physical tape; neither is weakened to a
wrapper predicate. The second starts at the real initial configuration and
tracks the actually selected first gate through `hg`.

**What it does not claim.** The pass is read-only: its endpoint tape is the
*same term* as the GN-E2-3b `recordDone` endpoint tape, and
`gnValuesEntryConfig_structure` states that equality as a conjunct. No value is
copied, no `[output false, finish]` tail is written, no request word is
completed, and there is no launch, delegation, commit, next-gate loop, total
installer clock, verdict, acceptance, language-level statement, or claim that
the pure evaluator `evalGNProgram` is executed by this machine. Extending
`gnInstallExitDispatch` so that the shuttle can carry a `data` frame is
explicitly deferred to E2-4b.

**Registration carried in the same commit (requirement 3(a)).**
`lakefile.lean` registers both the new source module and the new
`Tests/TMGateNValuesRewindSurfaceTests.lean`; that surface test `#check`s all
new public declarations on both sides of the slice — the two new `GNState`
constructors, `GNRewindMode` and its three constructors, `gnRewindAdvance`,
`gnRewindComplete`, `gnRewindControl`, the new module's thirteen definitions
and its seventeen theorems — and restates every one of the seventeen theorems
as a full-proposition `check_*` wrapper; `pnp3/Tests/AxiomsAudit.lean` imports
both and adds thirty-four direct `#print axioms` roots (the seventeen theorems
and the seventeen wrappers).

**Gates at stage (a) — what was actually run, and only that.** The complete
`./scripts/check.sh` was **not** run and is **not** claimed, for the reason
given above: its first action is the freeze preflight, which correctly rejected
the stage-(a) tree. What was run, on that tree, all succeeding: targeted
`lake build` of
`Complexity.TMVerifier.TuringToolkit.GateNFixedDelegateRelocation`,
`…GateNValuesRewind` and `…GateNRelocationExamples` (that last one imports
`GateNRelocation`, not the changed control module, so it is an extra targeted
build and not part of the cone), plus the complete
reverse-dependency cone of the changed control module — the six other frozen
`TuringToolkit/GateN*` modules that import it transitively
(`GateNBodyDriver`, `GateNBodyRound`, `GateNBoundaryShuttle`,
`GateNFirstInstallBridge`, `GateNFrameShuttle`, `GateNScratchBootstrap`), the
eight `Tests.TMGateN*SurfaceTests` in that cone including the new
`Tests.TMGateNValuesRewindSurfaceTests`, and `Tests.AxiomsAudit`. That is every
module in the cone; nothing downstream of the changed control is left
unchecked. All 4910 `#print axioms` roots in the audit report a subset of
`{propext, Classical.choice, Quot.sound}`; of the thirty-four new roots, two
(`gnRewindAdvance_laws` and its wrapper) report no axioms at all, and no
`sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler` or `nativeDecide` appears
anywhere in the audit output. That root count is a stage-(b) correction: the
stage-(a) commit message and the first draft of this paragraph both said 4881,
which was wrong. The audit carries 4876 roots at the pre-slice parent
`20850b93` and the slice adds exactly thirty-four, so the count on the
stage-(a) tree is 4910, and re-reading the audit output on that unchanged Lean
tree reports 4910 root lines. Only the figure was wrong; the property asserted
of every root is unchanged and was re-verified, root by root, when the number
was corrected. The stage-(a) commit message keeps the wrong figure because
amending it would destroy the SHA this pin names as provenance.
Also run, all OK: the hygiene scans for `axiom`, `sorry`/`admit`,
`native_decide`, `Lean.ofReduceBool`, `Lean.trustCompiler` and `unsafe` over
active pnp3/pnp4 Lean (no hits); `git diff --check` (clean);
`scripts/check_doc_honesty.sh`; `scripts/check_typeclass_payload_quarantine.sh`;
`scripts/check_refuted_route_quarantine.sh`;
`scripts/check_refuted_predicate_usage.sh`; `scripts/check_target_lock.sh`;
`scripts/test_underscore_policy.sh`;
`node scripts/test_tmverifier_freeze_policy.js`; and
`python3 scripts/validate_version_manifest.py`. The freeze checker itself was
run to record the expected rejection quoted above, and was not weakened or
bypassed in any way. Two further gates were red on the stage-(a) tree for the
same structural reason and are therefore **not** claimed for it:
`scripts/check_tmverifier_freeze.sh`, which is that same preflight, and
`scripts/test_tmverifier_freeze.py`, whose baseline case runs the checker
against the live tree and asserts that it passes. Both go green again with
stage (b), and the paragraph below records them there. No remote gate result
and no independent adversarial review was claimed for stage (a).

**Gates at stage (b) — what was actually run, and only that.** On the tree of
the stage-(b) commit: the four freeze-specific gates —
`python3 scripts/check_tmverifier_freeze.py` (117 Git objects match tree
`c544405f`, reviewed provenance `b35bdca2` verified),
`scripts/check_tmverifier_freeze.sh`, `scripts/test_tmverifier_freeze.sh` (the
complete negative-control suite, including the self-hosted provenance-free
control) and `node scripts/test_tmverifier_freeze_policy.js` — plus
`python3 scripts/validate_version_manifest.py`, `scripts/check_doc_honesty.sh`,
`scripts/check_typeclass_payload_quarantine.sh`,
`scripts/check_refuted_route_quarantine.sh`,
`scripts/check_refuted_predicate_usage.sh`, `scripts/check_target_lock.sh`,
`scripts/test_underscore_policy.sh`, `python3 -m py_compile` on the changed
script, `git diff --check`, and the hygiene scans for `axiom`,
`sorry`/`admit`, `native_decide`, `Lean.ofReduceBool`, `Lean.trustCompiler`
and `unsafe` over active pnp3/pnp4 Lean — all passing. No Lean source and no
frozen byte differs from the stage-(a) tree. These author checks reused the
stage-(a) build artifacts; **no fresh compilation is claimed for those checks**.
The later independent Claude review's recompilation at `e2c3ee33` (**APPROVE**)
is recorded separately below. The author ran `lake build --no-build` over
`…GateNFixedDelegateRelocation`, `…GateNValuesRewind`,
`Tests.TMGateNValuesRewindSurfaceTests` and `Tests.AxiomsAudit`; it exited `0`,
i.e. Lake considered stage (a)'s artifacts current for that tree and would
recompile nothing. That is a staleness check against a warm build directory,
not an independent rebuild from source, and it is the sole basis for the
corrected audit-root count above. The complete `./scripts/check.sh` was
**not** run at stage (b) either and is **not** claimed for it: the whole-gate
run was reserved for the final head after the exact-head reviews, and the
record at the end of this file reports it run there.

**Reviews — which head, which verdict.** The known independent read-only review
outcomes are recorded below. The local evidence paths name external reports,
not committed artifacts or portable attestations; local Git establishes content
identity and ancestry, not that an external review ran. Earlier reported
outcomes are preserved with their limits, separately from the reports inspected
during this recovery.

*At the superseded stage-(b) head
`23335cc37831acea23688642b4621b9ac0892cd6`* — a first stage-(b) commit,
replaced by `e2c3ee33`, which is its sibling under the same stage-(a) parent, so
`23335cc3` is **not** an ancestor of this branch. One Codex review (model
`gpt-6-astra`) returned **REQUEST_CHANGES** on a single P2 documentation
blocker: the freeze note under "What Is Still Open" in `STATUS.md` still pinned
the snapshot to the GN-E2-3b tree `b49456d6`/`7b53a08f` and still said this
slice's repin deliberately had not landed, so the freeze gate was red "on this
tree" — both false at that head. It found no blocking Lean, execution, clock,
state-arithmetic, surface/audit-root or freeze-content defect. That finding was
fixed by replacing the stage-(b) commit: `e2c3ee33` rewrites that freeze note.
The retained draft at
`/tmp/gn-e24-codex-review-xxmnimdd/report-draft.md` names that head and the
**REQUEST_CHANGES** verdict; it still has an audit-result placeholder and is
not a finalized kernel-audit report. The earlier recovery account also records
a Claude attempt at `23335cc3` that reached its turn limit with **no verdict**.

*At the retained stage-(b) head
`e2c3ee3330ac536131714df1d707044b0927e2fb`*, whose
`pnp3/Complexity/TMVerifier` subtree is exactly the pinned tree `c544405f`.
**Two reviews were reported as APPROVE with no blocking finding:** a Codex
review (model `gpt-6-astra`) in a separate
read-only-sandbox worktree, and a Claude Fable 5.1 review, which additionally
recompiled the changed control module and the new module from the committed
source and compared the results against a sibling worktree at the same commit.
The Claude report is available locally at
`/root/.claude/plans/read-only-adversarial-exact-head-lean-fr-zesty-newt.md`;
its compilation log is `/tmp/gn-e24-audit-compile.log`. The Codex approval is
preserved as previously reported; its report is not among the
`/tmp/gn-e24-4e182c03-*` evidence inspected for this recovery.
**A third, an earlier Codex pass in the lane worktree, returned
REQUEST_CHANGES** on two P2 documentation findings and nothing else: that this
record's "no independent review at any head" sentence was falsified by the
`23335cc3` review above, which had to be recorded with its reviewed SHA and its
REQUEST_CHANGES disposition and distinguished from approval of the current head;
and that `TMVerifier_Session_Plan.md` still called PR #1777 open with its
history-preserving merge owed. It too found no blocking Lean or freeze-content
defect, and it confirmed the `23335cc3` blocker fixed. The PR #1777 finding was
fixed by `4e182c03`; the provenance finding is what the commit carrying this
paragraph finishes. That earlier Codex **REQUEST_CHANGES** outcome and a
Claude attempt at `e2c3ee33` with **no verdict** are likewise preserved from the
earlier recovery account; their reports are not in the `4e182c03` evidence set.

*At the docs head `4e182c03187c3a1071485821505c3f6cf4a29c19`*, whose commit
changed only this file and `TMVerifier_Session_Plan.md`, **two completed reruns
returned BLOCK**:

- **Codex (`gpt-6-astra`): BLOCK**, recorded in
  `/tmp/gn-e24-4e182c03-codex-rerun.txt`. Its blocking finding was inconsistent
  review provenance: this file's header and the Session Plan claimed approvals
  at `e2c3ee33`, while this record and `STATUS.md` still denied any review at
  any head. It requested reviewer, head, verdict and available evidence for the
  claimed reviews. It found no blocking Lean execution defect. It inspected
  cached axiom output, explicitly without a fresh kernel check, and ran the
  freeze checker and `git diff --check`; it ran no build or full gate.
- **Claude: BLOCK**, recorded in
  `/tmp/gn-e24-4e182c03-claude-rerun.txt`. B1 identified this file's contradiction
  and missing review paragraph; B2 identified the stale `STATUS.md` review
  claim. It found the Lean surface, pins and numeric claims correct and ran the
  freeze checker. It did not reproduce compilation or axiom output or verify
  that the two earlier approvals occurred. Its five nonblocking notes are
  disposed of below or in the Session Plan.

Both reports independently counted thirteen public definitions, seventeen
public theorems, thirty-four new audit roots, 4876 roots at base and 4910 at
`4e182c03`; both measured 1041 changed Lean lines across five `.lean` files
(four modules plus `lakefile.lean`), within the ≤ 1500-line / ≤ 10-module gate.
The initial Codex attempt in `/tmp/gn-e24-4e182c03-codex.txt` failed because
`gpt-5.4` was unsupported and returned **no verdict**. The separate attempt
logged in `/tmp/gn-e24-4e182c03-opus5-fallback.txt` reached its turn limit and
returned **no verdict**. Neither failed attempt cancels either completed
rerun. This correction addresses both **BLOCK** reports at `4e182c03`.

**No review of the current head is claimed.** That fix commit changes the head
SHA again, as the GN-E2-3b docs-only commits `50f3eadd` and `635ac15e` did after
its stage (b), so a fresh exact-head review of the new head is owed and is
listed below with the rest. The fix changes no frozen byte, no Lean source, no
pinned constant and no manifest entry. Content identity does not extend an
earlier approval to the corrected head. The fix does edit
`pnp3/Docs/TMVERIFIER_FREEZE.md`, which
`.github/scripts/tmverifier-freeze-policy.js` protects by name, so the freeze
policy gate applies at the new head and the owner's attestation must name that
head's 40-character SHA, followed by applying or retriggering the
`tmverifier-unfreeze` label. No attestation for an earlier head discharges that
requirement.

**Nonblocking notes from those reviews, and their disposition.** Three concern
docstring wording inside the frozen tree, so fixing any of them would change
frozen bytes and would need its own stage (a) plus stage (b) unfreeze pair and a
new pin. Any in-tree wording changes are therefore **deferred** to a future
authorized unfreeze; this recovery records the accurate reading outside the
frozen tree and does not authorize that later work.

1. `gnValuesEntryConfig`'s docstring says "Only the head differs from
   `gnFirstRecordDoneConfig`". The *state* differs too — `recordDone` becomes
   `valuesEntry` — and only the tape is the same term. The Codex reports at
   `23335cc3` (**REQUEST_CHANGES**) and `4e182c03` (**BLOCK**) note this; the
   definition and `gnValuesEntryConfig_structure` correctly expose both changes.
2. `gnValuesEntryConfig_structure`'s docstring says its fifth conjunct
   "identifies head `4` as p0 of the first frame after the leading `bof`".
   That conjunct is a pure `gnLocatePrefix r` list identity and does not by
   itself pin the head; head `4` is pinned outright by the second conjunct.
   Raised by Claude at `e2c3ee33` (**APPROVE**) and `4e182c03` (**BLOCK**);
   the theorem is exactly as stated and as proved.
   `TMVerifier_Session_Plan.md` carries the accurate reading of this note and of
   the previous one.
3. `gnRewindAdvance_laws`'s docstring says "every representative frame a
   stage-zero GN word can carry to the left of a finished record continues the
   pass". Claude at `e2c3ee33` (**APPROVE**) noted that the enumeration omits
   `output true`, `blank` and `spent`, which cannot occur in that position.
   The stage-zero qualification is accurate; the theorem proves its stated
   enumeration, while `gnRewind_validPath` covers every constructor under its
   no-`bof` hypothesis. No theorem correction is required.

The remaining notes from Claude at `4e182c03` (**BLOCK**) are resolved in
prose: ragged wraps are repaired, `STATUS.md` no longer calls GN-E2-3b the
"single authorized" slice in a list that also includes GN-E2-4a, and the Session
Plan distinguishes the eight `gnRewindControl` arms from the nine fixed rows
pinned by `gnTransition_rewind_rows`. That plan also records why the thirteen
definitions are covered transitively by the thirty-four audit roots, rather
than directly as in S11. The zero-input literal remains a nonvacuity witness
for execution, not a witness of a nonempty values run, as Codex at `4e182c03`
(**BLOCK**) noted and the Session Plan already explains.

Two further notes are historical facts about the two landed commits and cannot
be repaired without destroying the heads the reviews above name. Claude at
`e2c3ee33` (**APPROVE**) observed that the stage-(b) commit message carries
only its subject line, where the GN-E2-3b stage (b) carried classification,
gates run and owed items in its body; this record carries that content instead.
The stage-(a) message's wrong 4881-root count is recorded and corrected further
up for the same reason.

**Recovery validation (2026-09-28).** On the docs-only working tree based on
`4e182c03`, the three commands comprising the freeze preflight passed:
`./scripts/check_tmverifier_freeze.sh`, `./scripts/test_tmverifier_freeze.sh`
and `node scripts/test_tmverifier_freeze_policy.js`. The checker matched all
117 objects to `c544405f94cb68755cad3dc5c6a0639517a2967b` and verified
`b35bdca2` provenance. Targeted `./scripts/check_doc_honesty.sh`,
`python3 -B scripts/validate_version_manifest.py` and `git diff --check` also
passed. The diff against base `20850b93` still has 1041 changed Lean lines in
five `.lean` files (four modules plus `lakefile.lean`); this recovery changes
only `STATUS.md`, this record and `TMVerifier_Session_Plan.md`. No frozen byte,
pin, manifest or Lean source changed. This validation is not an independent
review, a theorem rebuild, fresh kernel-axiom output, or the complete
`./scripts/check.sh`; none of those is claimed for the correction.

**Exact-head reviews, full gate and attestation (2026-09-28).** The docs-only
correction above was merged with `origin/main` (`789350ee`) into
`6718b422a0f8555feed46930a7eada69be007f6a`, and that merge commit is the head
at which this slice was reviewed. PR #1801 records, against that exact full
SHA, an independent Codex read-only review returning **APPROVE**, an
independent Fable 5.1 read-only review returning **APPROVE**, and a complete
`./scripts/check.sh` run in which all checks passed. The repository owner's
attestation comment `/tmverifier-unfreeze
6718b422a0f8555feed46930a7eada69be007f6a` was posted on that PR against the
same full SHA, and the `tmverifier-unfreeze` label is applied to it. Those
discharge the fresh review of the final head, the whole-gate run and the
attestation-and-label pair that the paragraphs above listed as owed. The
`e2c3ee33` and `4e182c03` verdicts recorded earlier remain the history of how
that head was reached, not a competing final verdict. This record-correction
commit advances the head past
`6718b422a0f8555feed46930a7eada69be007f6a`: it changes only `STATUS.md`, this
record and `TMVerifier_Session_Plan.md`, and no review, `./scripts/check.sh`
run, attestation or label is claimed for the resulting head.

**Still owed before merge.** The remote half: `ci.yml` and `lean.yml` observed
green on the latest head, and the `TMVerifier Freeze Policy` rollup observed
passing there. No remote CI result is claimed for this slice in this record.
The required PR review is unresolved — PR #1801 carries no approving review,
and its only GitHub review is an automated `qodo-code-review` pass submitted as
**COMMENTED**, whose single governance finding is the staleness this
correction repairs. That comment-review is not an approval, and the separate
"PR Summary by Qodo" comment is a generated description, not a review at all;
neither is counted among the independent reviews recorded above. Finally, the
history-preserving merge below is still owed. If the merge candidate head moves
past `6718b422a0f8555feed46930a7eada69be007f6a` — as this correction moves it —
the owner's attestation and the label must be reissued against the final head
before merge.

**Merge with a merge commit — required, for provenance.** As for the two
migrations above, this branch must be merged with a merge commit or an exact
fast-forward, never squashed or rebased, and must not be rebased or
force-pushed while its PR is open, so that its stage (a) and stage (b) remain
two distinct, auditable commits. A rewriting merge would not break any check —
the frozen tree object `c544405f` travels with the bytes — but it would drop
`b35bdca2`, the commit this pin names as provenance, from `main`'s ancestry.
Bringing `main` into this branch must likewise be a merge commit.

**Post-merge verification (required).** Immediately after the merge, on an
updated `main` or a fresh clone, run both:

```text
git merge-base --is-ancestor b35bdca2cb24af709144998af5c4402d42a18aa5 origin/main
python3 scripts/check_tmverifier_freeze.py
```

The second is the content gate: it must report that the frozen tree matches
`c544405f94cb68755cad3dc5c6a0639517a2967b`, and it is expected to pass under
any merge style. The first is the provenance audit and must exit `0`. If it
does not, the merge was a rewriting one and the provenance link was dropped:
the frozen content is still verified and `main` is not broken, so the response
is not an emergency but a deliberate repin onto a commit in `main`'s ancestry,
landed under this same unfreeze gate, plus a note in this record saying which
merge dropped the link.

**GN-E2-4a has since merged, and the paragraphs above are now `main`'s copy of
its record.** On 2026-09-28 PR #1801 merged the slice into `main` as the merge
commit `71179c6d42a895504e16391a93421c980b3fd98f`, whose two parents are the
previous `main` `789350ee` and the slice's final head
`a312622f81bff9316b78875653b48177f56cf06e` — a merge commit, not a squash or a
rebase, so history was preserved and the provenance audit required above passes:
`git merge-base --is-ancestor b35bdca2cb24af709144998af5c4402d42a18aa5
origin/main` exits `0`. This branch's own copy of that record stood as it was at
`13f36c1d`; the first integration merge, `4abaac92`, brought `main`'s later copy
in, so the "Exact-head reviews, full gate and attestation" and "Still owed"
paragraphs above are that copy verbatim, and they — not this branch — are the
authority for what the slice discharged before the merge: an exact-head Codex
**APPROVE**, an exact-head Fable 5.1 **APPROVE**, a complete local
`./scripts/check.sh`, the owner's full-SHA attestation and the
`tmverifier-unfreeze` label, all recorded against the pre-merge head
`6718b422`, with no gate result claimed there for the docs-only final head
`a312622f`. Read the "Still owed before merge" paragraph above as written before
this merge: the history-preserving merge it lists as owed is the `71179c6d`
merge reported here, while the remote half and the resolution of the required PR
review — which that paragraph records as unresolved, PR #1801's only GitHub
review having been an automated `qodo-code-review` pass submitted as
**COMMENTED**, not an approval — are not recorded in local Git and are not
claimed here either way. This branch claims none of it, and none of it transfers
to GN-E2-5a. What the merge
does change for GN-E2-5a is the merge base: it moved to `13f36c1d` then, and
this branch's two integration merges of `main` have since moved it on to
`71179c6d` and then to the current `9445a93e`, where the §6.1 size gate measures
this slice alone, as the GN-E2-5a record below records.

### 2026-09-28 — GN-E2-5a zero-value first-request writer

**Progress classification: Infrastructure only.** This migration reduces
neither `VerifiedNPDAGLowerBoundSource` nor `SearchMCSPWeakLowerBound` and does
not provide `ContentVerifierBridge`.

The migration re-pins tree `c544405f` to tree
`4213b315075f67468451a6736afc04486df0350c`, the
`pnp3/Complexity/TMVerifier` subtree of stage-(a) commit
`11dc8e8200368db075821d74ed9acd60665bc398`. Stage (a) adds
`GateNValuesWriter.lean`, extends the finite GN control and data-exit routing,
updates the rewind/body proofs, and carries the module registration, complete
surface wrappers and direct axiom roots in the same commit. It does not alter
the old pins. The targeted implementation, surface, rewind-surface and axiom
audit builds all completed successfully before that commit.

The concrete capstone is genuine `TM.runConfig` execution from
`GNM.initialConfig (gnPoint (encodeGN r))` to a physical `requestReady`
configuration for a first gate under exactly `hg : r.program.gates[0]? = some
g` and `r.inputs = []`. It writes the fixed `[output false, finish]` tail and
pins the complete tape, head and exact schedule. The finite data-copy rows are
present but dormant in this rescoped theorem; removing the zero-input premise
is GN-E2-5b, not a result of this migration. There is no launch, delegation,
next-gate loop, verdict, acceptance, language theorem, advice-freedom result or
P-vs-NP claim.

Stage (b) is the separate commit containing this paragraph. It sets
`FROZEN_COMMIT` to `11dc8e8200368db075821d74ed9acd60665bc398` and
`FROZEN_TREE` to `4213b315075f67468451a6736afc04486df0350c`, leaves schema
version 3 unchanged, and regenerates `spec/tmverifier_freeze.json` with
`python3 scripts/check_tmverifier_freeze.py --write-manifest`. No frozen byte or
Lean source changes in stage (b).

**Size gate — one measurement, green, never waived.** §6.1 of
`pnp4/Pnp4/Frontier/ContractExpansion/VERIFIER_RETARGET_PLAN.md` takes the gate
against `git merge-base main HEAD`. That merge base was
`13f36c1dbde4ade4ce6cb5e7798a64e1085c8a83` — this slice's own base, which became
the merge base when PR #1801 merged GN-E2-4a into `main` — then
`71179c6d42a895504e16391a93421c980b3fd98f`, once this branch's first integration
merge `4abaac92` brought that `main` in and made it an ancestor, and is now
`9445a93e763b4ab6377426bca9078ea73a726fbb`, because this branch's second
integration merge `d01e2c3e` brought in the `main` that PR #1802 created with
the Part A G3l origin-alignment handoff. The
measurement is the same at all three, and coincides with the slice-local one:
**1497 changed Lean lines (1467 added, 30 deleted) across 8 `.lean` modules**,
inside both the `≤ 1500`-line and `≤ 10`-module bounds. The gate is **green**.
Neither merge of `main` enlarged it: `main`'s own G3j and G3k modules became
shared history and dropped out of the diff at the first, its G3l module and that
module's surface test did the same at the second, and what is left is exactly the
eight modules this slice touches. Against the superseded bases the same working
tree now measures 2880 changed Lean lines across 10 `.lean` files at `71179c6d`
and 5808 across 14 at `13f36c1d`, because those diffs also carry `main`'s G3j,
G3k and G3l modules, their surface tests and their `lakefile.lean` and
`AxiomsAudit.lean` registrations, none of which is this slice's content; neither
is the prescribed measurement any longer and neither is reported as one. 1497 is
the number the rescope was
designed to hit, and the Codex review at `311abc6b` independently reproduced it
against `13f36c1d` before either merge.

Before that merge the same gate was **red at 2496 Lean lines (2485 added, 11
deleted) across the same 8 modules**, measured against the then-current merge
base `20850b93`, because GN-E2-4a's 1041 changed lines were still unmerged and
sat between that base and stage (a), so the measurement covered two authorized
slices at once. It was recorded red rather than waived, with the note that
GN-E2-4a landing was what would clear it; that is exactly what happened, and the
excess was never this slice's content. Note also that the same plan's standing
remedy when `main` moves under an open slice — "rebase, don't merge", stated in
§5 rather than §6.1, with §6 to be re-run after every rebase — remains
unavailable to this branch: rebasing would rewrite `11dc8e82`, which is the
provenance commit the pin names, so the conflict between that instruction and
the no-rebase requirement below is real and is left for the merge decision, not
resolved here. It no longer bears on the size gate, which is green at the
current merge base. `main` advanced to `71179c6d`, and then to `9445a93e`, while
this slice was open, and this branch took the only route left open to it both
times: a merge commit, which is what
the "Merge with a merge commit" requirement above already demands for bringing
`main` into this branch. Both merges are documentation and integration only — no
frozen byte, pinned constant, manifest entry or Lean source of this slice
changes in either — and neither carries a gate result of its own.

**The second integration merge, `d01e2c3e`.** Its two
parents are this branch's docs head `4abaac92` and `main` at
`9445a93e763b4ab6377426bca9078ea73a726fbb`, in that order, so the stage-(a) →
stage-(b) ancestry is untouched: `11dc8e82` and `311abc6b` remain distinct
commits on the first-parent path, and `git merge-base --is-ancestor 11dc8e82
HEAD` and `… 311abc6b HEAD` both exit `0`. What `main` brings in is PR #1802's
Part A G3l origin-alignment handoff — one new
`Complexity.Uniform.V1` module, its surface test, and their `lakefile.lean`,
`pnp3/Tests/AxiomsAudit.lean`, `STATUS.md`, `TODO.md`,
`pnp3/Docs/UniformP_V1.md` and pnp4 `README` entries — all of it outside the
frozen tree and disjoint from every GN surface. The three files both sides touch
were resolved additively and both sides' surfaces are retained: `lakefile.lean`
keeps G3l's `Complexity.Uniform.V1.FixedPairOriginAlignment…Countdown` and
`Tests.UniformV1FixedPairOriginAlignment…CountdownSurfaceTests` registrations
alongside GN-E2-5a's `…TuringToolkit.GateNValuesWriter` and
`Tests.TMGateNValuesWriterSurfaceTests`; `pnp3/Tests/AxiomsAudit.lean` keeps
both import pairs and both root blocks, G3l's 58 `#print axioms` roots and
GN-E2-5a's 28, for 5122 roots where `71179c6d` had 5036, `4abaac92` 5064 and
`9445a93e` 5094 — the sum, so neither side's roots were dropped or duplicated;
and `STATUS.md` keeps G3l's slice entry and GN-E2-5a's freeze and slice prose. The frozen subtree of the merge result is bit-for-bit the pinned
tree `4213b315075f67468451a6736afc04486df0350c`, so `FROZEN_COMMIT`,
`FROZEN_TREE`, `SCHEMA_VERSION`, `spec/tmverifier_freeze.json` and the
`[snapshot.tmverifier_freeze]` row are all untouched by it and the freeze
checker's provenance cross-check still resolves `11dc8e82` to that tree. Beyond
the mechanical merge it changes only prose that named the superseded merge base
or spoke of a single integration merge: this record, `STATUS.md` and
`TMVerifier_Session_Plan.md`.

**Reviews at the stage-(b) head `311abc6b` — which reviewer, which verdict.**
Two independent read-only exact-head reviews ran against this head, both with
`13f36c1d` as the comparison base, and they split. Neither reported a blocking
Lean, execution, geometry, surface, axiom-root or freeze-content defect, and
neither disputed the size arithmetic above.

- **Codex: APPROVE**, recorded in
  `/root/pnp2-agent-reports/gn-e25-311-exact-codex.md`. It inspected all twelve
  changed files with the execution, encoding, scanner, writer and
  earlier-capstone dependencies; confirmed the capstone is genuine
  `TM.runConfig` from the real initial configuration under exactly `hg` and
  `r.inputs = []` with room proved internally; confirmed the added control is
  finite and request-independent, the dormant data-copy rows and the narrowed
  invalid-exit predicate pinned, and nonempty-input execution scoped out; and
  confirmed fourteen public writer theorems with full-proposition wrappers and
  direct axiom roots for both originals and wrappers. It ran read-only freeze
  verification (118 objects and provenance matched), `git diff --check`, and
  static surface/root, registration, size and forbidden-token checks. It
  explicitly did **not** run Lean compilation, evaluated `#print axioms`, the
  full `./scripts/check.sh`, negative controls or any remote check, and states
  that its approval discharges none of the outstanding merge gates. Its single
  **P3** note is N2 below.
- **Claude (`claude-opus-5`): BLOCK**, recorded in
  `/root/pnp2-agent-reports/gn-e25-311-exact-claude.json`, with the full report
  at `/root/.claude/plans/read-only-exact-head-documentation-and-quirky-flame.md`.
  It recorded the Lean as sound and blocked entirely on documentation
  consistency, naming the same defect class that blocked the predecessor slice
  at the same lifecycle point. Its four blocking findings were **B1** the stale
  `STATUS.md` pin, migration count and missing GN-E2-5a entry, plus GN-E2-4a
  prose there left in a present tense stage (a) had already falsified; **B2**
  the stale `TMVerifier_Session_Plan.md` header pin and "three unfreezes"
  count, in the very file stage (a) appended the GN-E2-5a section to; **B3**
  two owners for the per-value copy round, and a supersession note that
  undercounted the sentences it superseded; and **B4** the `≤ 1500` claim above
  stated with neither base nor number. It re-derived the literal probe by hand
  from `G1Frame.bits`/`encodeGNFrames` — 21 frames, head 80, 4+68+4+8 = 84
  steps onto 700 for 784, cells 72/76 as bit 0 of the written `output false`
  and `finish` frames — and confirmed the freeze pins, tree, manifest, the
  two-stage split, `311abc6b^ = 11dc8e82`, and schema 3. It ran **no** build,
  kernel check or `#print axioms`, so every `rfl` and `decide` is accepted as
  stated; it also did not run `check.sh`, did not verify this record's
  "targeted builds completed" claim, and verified nothing remote.

The docs-only commit `3195ffc1` is the fix for B1–B4. It changes no frozen
byte, no Lean source, no pinned constant and no manifest entry, so it does not
disturb either review's content findings — and, by the same token, neither
verdict transfers to the head it created. A fresh exact-head review is owed.

**Nonblocking notes, and their disposition.** **N2** — raised by Codex as its
P3 and by Claude as a note — is fixed: `TMVerifier_Session_Plan.md` said "four
changed destination bits" where the literal theorem makes four before/after
assertions about **two** physical cells, 72 and 76, and now says two. **N1** —
the narrowed `GNInstallExitInvalid` has no full-proposition surface
restatement of its own; `check_gnTransition_dataExit` restates the narrowing
only at the `carried (.data b)` case and `TMGateNBodyRoundSurfaceTests.lean`
pins the bare name — is **not** addressed here, because closing it means adding
a Lean wrapper and that was a documentation-only commit. It was carried forward
to the then-planned GN-E2-5b and remains open after the bounded one-value slice;
**Lane B's deferred GN values/tail follow-up** owns it in the
[carry-forward register](GN_E2_5B_VALUES_COPY.md#carry-forward-ownership).
The owner-label inconsistency was deferred at that docs-only head:
`GateNValuesRewind.lean:531` still assigned the values copy to `E2-4b`, while
`GateNValuesWriter.lean:38-39` assigned it to GN-E2-5b. That deferral is now
closed by the separately authorized owner-docstring stage (a) and stage (b)
recorded below. Only the owner label changes; N1 and the other frozen wording
notes remain outside this correction's scope.

**Reviews at the second integration-merge head `d01e2c3e` — which reviewer,
which verdict.** Two further independent read-only exact-head reviews ran
against `d01e2c3e635e24b6722d6b3ce31382ab54b1f909`, both comparing it with
`main` at `9445a93e`. Neither reported a blocking Lean, execution, theorem
surface, premise, scope, freeze-content, manifest, registration or size defect,
and they split on documentation.

- **Codex: no blocking theorem or freeze-content defect; merge readiness not
  established.** Recorded in `/root/pnp2-agent-reports/gn-e25-d01-codex.md`. It
  re-verified the 118-object freeze match against tree `4213b315`, the
  `11dc8e82` → `311abc6b` two-stage split, the 1497-line/8-module size
  measurement, and the fourteen public writer theorems with their
  full-proposition wrappers and 28 audit roots, and it reproduced the literal
  probe independently — 700 + 84 = 784, head 80, cells 72 and 76 turning from
  false to true. It ran direct read-only Lean elaboration of the four changed
  implementation files and both changed surface files against existing cached
  imports and evaluated the 28 slice audit roots, but states that whole-file
  `AxiomsAudit.lean` elaboration could not proceed for want of a cached object
  for the separately merged G3l surface module, so it claims **no** complete
  audit build; it ran no full `./scripts/check.sh` and nothing remote. Its two
  nonblocking notes are N1 above and N3 below.
- **Claude (`claude-opus-5`): BLOCK on documentation consistency.** Recorded in
  `/root/pnp2-agent-reports/gn-e25-d01-opus5.md`, with the full report at
  `/root/.claude/plans/read-only-independent-documentation-theo-floofy-spring.md`.
  It reported the Lean, theorem surface, premises, scope, freeze content,
  manifest, checker, provenance, registrations, classification and size gates
  clean — 118/118 manifest hashes and git object ids matched disk, a fresh
  `--write-manifest` was byte-identical, the 5036 → 5122 root arithmetic and the
  literal probe were re-derived by hand — and blocked entirely on prose this
  change set had itself added. Its two blocking findings were **D-1**, the stale
  present-tense merge base `13f36c1d` in this record's GN-E2-4a merge paragraph,
  and **D-2**, a `STATUS.md` sentence pointing at an `E2-4b` that stood nowhere
  in the prose it named. **D-3** to **D-7** were non-blocking accuracy findings:
  the "rebase, don't merge" remedy attributed to §6.1 rather than §5 of the
  retarget plan; the merge-base provenance of `13f36c1d` and `71179c6d` phrased
  as commit authorship; a "read every *earlier* `E2-4b`" directive that missed
  the live later one; the shared-tree list that omitted `23335cc3`, the one
  co-tree commit carrying a **REQUEST_CHANGES**; and two "E2-4b" deferrals
  attributed to this record where it makes one. It ran **no** build, kernel
  check or `#print axioms`, so every `rfl` and `decide` is accepted as written;
  it also ran no `check.sh` and verified nothing remote.

The docs-only commit `40ea2346` is the fix for D-1 through D-7 and
for N4 below. It changes no frozen byte, no Lean source, no pinned constant and
no manifest entry, so it disturbs neither review's content findings — and, by
the same token, neither outcome transfers to the head it created, and neither
discharges any gate owed below. The subsequent `40ea2346` review is recorded
below; reviews apply only to their named SHA.

**Two further nonblocking notes, and their disposition.** **N3** — raised by
Codex at `d01e2c3e` — is that `gnCS_encodeGN_firstRequestReady_exact` states
arrival at `gnFirstRequestReadySteps r g` and not exclusion of `requestReady` at
every earlier time, so general first-arrival minimality is not part of the
public contract; direct execution confirms first arrival at 784 for the literal
probe, which is a witness and not a general theorem. It is **not** addressed
here, because closing it means adding a Lean theorem and this is a
documentation-only commit. It was carried forward to the then-planned
GN-E2-5b, alongside N1, and remains open after the bounded one-value slice.
**Lane B's deferred GN values/tail follow-up** owns N3 in the
[carry-forward register](GN_E2_5B_VALUES_COPY.md#carry-forward-ownership).
**N4** — raised by Claude at `d01e2c3e` — is fixed: `TMVerifier_Session_Plan.md`
reported the 1497 measurement at the two superseded bases without the
base-relativity caveat that this record and `STATUS.md` both carry, and now
carries it in both places it states that measurement.

**Review at the docs head `40ea2346` — which reviewer, which finding.** One
exact-head Codex review ran against
`40ea2346311c7fc13cd051333aad7895856f443a`, comparing it with `main` at
`9445a93e`, and is recorded in `/root/reports/gn-e25-40ea-codex.txt`. It
returned no APPROVE/BLOCK label and reported **no blocking theorem or
freeze-content defect** in the stated zero-input contract. It re-verified the
118-object freeze match, the `11dc8e82` → `311abc6b` two-stage split with both
commits still ancestors, subtree `4213b315` and schema 3; re-derived the size
measurement as 1497 changed Lean lines, 1467 additions plus 30 deletions across
8 files; re-confirmed the genuine `TM.runConfig` execution under exactly `hg`
and `r.inputs = []`, the exact endpoint and clock, and the fourteen public
writer theorems with their full-proposition wrappers and 28 audit roots, all
evaluating to `propext`, `Classical.choice` and `Quot.sound` only; and
independently reproduced the literal probe at 700 + 84 = 784 with head 80 and
cells 72 and 76 turning true. It confirmed D-1 through D-7 present and the
superseded-base caveat repaired, and it raised no new nonblocking note: N1, N3
and the frozen in-tree `E2-4b` label were deferred at that head (the label is
now corrected by the migration below). It ran
read-only elaboration of the four changed implementation files and both changed
surface files **against existing cached imports only** — **not** a clean
dependency build, whole-file `AxiomsAudit`, a full repository build,
`./scripts/check.sh`, negative controls, remote CI, approval or attestation —
and it edited, committed and pushed nothing. Its two findings were both **P2**
documentation defects, fixed by `51db7753`:
that this file's header denied any review at the later heads while the
`d01e2c3e` pair above was recorded, so the header had to separate those
historical reviews from the absence of a review of the corrected head; and that
the "no full check at any head" claim here, in `STATUS.md` and in
`TMVerifier_Session_Plan.md` denied evidence that exists — the log covered in
the full-check record below — instead of recording it with its limits. A second
review run at this head, `claude-opus-5`, ended at its 30-turn limit and produced **no
verdict and no report**; its result record is
`/root/reports/gn-e25-40ea-opus.json`. Neither outcome transfers to `51db7753`
or any later SHA, and neither discharges any gate owed below.

**Review at the docs head `51db7753`.** Codex reviewed
`51db77532dfe471cb03a26477cf92e98448143fd` against `9445a93e`, recorded in
`/root/reports/gn-e25-51db-codex.txt`: **FINDINGS**, one **P3**, no P0–P2
finding and no blocking theorem or freeze-content defect. It marked the
`40ea2346` P2 findings resolved. Its P3 was that audit-command positions and
counts establish layout agreement, not exact source bytes; an in-memory
comment-only counterexample preserved that layout while changing the hash.
`bceb38db98cf7d43fda523384969d3f320ed4ced` resolves P3 by saying the fingerprint
matches the audit-command layout at `4abaac92` and establishes neither exact
file bytes nor checkout identity. This FINDINGS verdict is not an approval.
The review reported source/signature and surface/root/registration inspection,
118-object read-only freeze verification, independent hashes and in-memory
manifest regeneration, ancestry checks, the 1497-line/8-file size measurement,
and an added-line forbidden-token scan across all eight changed `.lean` files.
It elaborated the four changed implementation files and both changed surface
files against cached imports, evaluated the 28 audit roots (only `propext`,
`Classical.choice`, `Quot.sound`) and reproduced the literal execution probe.
It ran no full `./scripts/check.sh`, full build or clean dependency rebuild,
whole-file `AxiomsAudit` elaboration, freeze negative controls, doc-honesty
script, remote gates, attestation or approval. These are reviewer checks at
`51db7753`, not author checks or results for a later SHA.

**Reviews and adjudication at `bceb38db` (2026-09-29).** Both exact-head
reports reviewed `bceb38db98cf7d43fda523384969d3f320ed4ced` against `9445a93e`:

- **Codex: PASS**, in `/root/reports/gn-e25-bceb38db-codex.txt`. It confirmed
  the P3 correction and initially found no new documentation contradiction.
  It reported Git/whitespace/size/ancestry and source/surface/axiom checks,
  read-only freeze verification, independent hashes and in-memory manifest
  regeneration, an all-eight added-line scan, historical log comparisons,
  cached-import elaboration of the four implementation and two surface files,
  and evaluation of the 28 audit roots and literal execution probe. It excluded
  the full check/build, clean rebuild, whole-file audit, negative controls,
  doc-honesty script, remote gates, attestation and PR approval.
- **Opus (`claude-opus-5`, explicit fallback): FINDINGS**, in
  `/root/reports/gn-e25-bceb38db-opus.txt`. It agreed that P3 was fixed and
  found no theorem or freeze-content defect, but raised **P2-A**, ambiguous
  attribution of the inherited author-check suite, and **P2-B**, stale head
  and review history omitting the `51db7753` review. It inspected Git history,
  diffs, source/surfaces, size arithmetic and historical audit-command layout.
  It ran no Lean elaboration/axiom evaluation, freeze checker or independent
  hashes/manifest regeneration, whole-slice token scan, whitespace check,
  doc-honesty, negative controls, full check, remote gates or attestation.
- **Codex adjudication: UPHOLD P2-A and P2-B**, in
  `/root/reports/gn-e25-bceb38db-debate-codex.txt`, also upholding the
  nonblocking six-versus-eight wording nit without enlarging the historical
  scan. It explicitly called its earlier unconditional documentation PASS too
  broad. It qualified Opus's reasoning: editing a paragraph does not necessarily
  move its historical referent; the driver log does evidence some `bceb38db`
  author checks; and absence of a claimed review is not absence of an existing
  review. The upheld defects are ambiguous attribution and an incomplete,
  unanchored status record. The adjudication used only read-only Git, file
  inspection and in-memory arithmetic, with no build, Lean, checker, linter,
  negative-control or remote run.

None of these reports reviews or approves any later correction SHA, supplies
final-head gate credit or establishes merge readiness.

**One full `./scripts/check.sh` is on record for GN-E2-5a, and it is no head's
gate result.** Stage (a) ran only the
targeted implementation, surface, rewind-surface and axiom-audit builds named
above; stage (b) ran the freeze checker; the docs-only commits `3195ffc1`,
`40ea2346` and `51db7753` each ran `git diff --check`, the
freeze checker, the freeze shell tests, the freeze-policy script test and the
doc-honesty linter, re-measured the §6.1 size gate, and ran no Lean build at
all.

**Checks recorded for the docs change committed as
`51db77532dfe471cb03a26477cf92e98448143fd`.** `HEAD` in these recorded commands
denotes the checkout in that historical run, not a reader's later checkout.
`git diff --check` clean;
`scripts/check_tmverifier_freeze.py` **OK** at 118 Git objects matching tree
`4213b315075f` with reviewed provenance `11dc8e820036` verified;
`scripts/test_tmverifier_freeze.sh` and
`node scripts/test_tmverifier_freeze_policy.js` both **OK**;
`scripts/check_doc_honesty.sh` **OK** across its four scans; the §6.1
re-measurement, still 1497 changed Lean lines across 8 modules against
`9445a93e`; a Git-native provenance check — `HEAD:pnp3/Complexity/TMVerifier`,
`11dc8e82`'s subtree and `311abc6b`'s all equal the pinned tree
`4213b315075f67468451a6736afc04486df0350c`, `311abc6b^` is `11dc8e82`,
`git merge-base --is-ancestor` exits `0` for both stage commits against `HEAD`,
and `spec/tmverifier_freeze.json`, both checker scripts and their pinned
`FROZEN_COMMIT`, `FROZEN_TREE` and schema-3 constants are undirtied; and a
reported forbidden-token scan over six of the slice's eight changed `.lean`
files with no hit for `axiom`, `sorry`, `admit`, `native_decide`, `Classical.choose`,
`Classical.arbitrary`, `Nat.find` or a placeholder marker. The historical account
does not identify the six paths; the reviewers' separate all-eight scans do not
enlarge this author scan's recorded coverage. It ran **no** Lean
build, no `AxiomsAudit` elaboration, no `./scripts/check.sh` and nothing remote,
and it changes no Lean byte, so no targeted build was owed for it.

**Author checks for the docs change committed as
`bceb38db98cf7d43fda523384969d3f320ed4ced`.**
`/root/reports/gn-e25-51db-p3fix-driver.log` records successful
`git diff --check` (including staged and committed diff checks),
`bash scripts/check_doc_honesty.sh`, and the read-only
`python3 scripts/check_tmverifier_freeze.py` (118 objects, tree `4213b315075f`,
provenance `11dc8e820036`), together with the committed diff and final SHA.
It records no full check or build. The `51db7753` freeze shell/policy tests
and the reviewer checks above are not attributed to this author run.

**Historical full-check evidence.** Between
`4abaac92` and `d01e2c3e` one complete `./scripts/check.sh` was
nevertheless run and logged, at
`/root/pnp2-agent-reports/gn-e25-4aba-full-check.log`. **What the log shows.**
Its preflight is this slice's own pin — 118 Git objects matching tree
`4213b315075f`, reviewed provenance `11dc8e820036` verified — followed by the
freeze shell tests and the freeze-policy script test and then all seventeen
numbered steps in order; no `error:` line occurs in its 16,539 lines, and line
16,539 is `[check] All checks passed.` **What it does not show.** It records no
commit, branch or working directory, so the log does not by itself pin its
checkout. Its only timestamps are four candidate-verifier progress stamps
inside step 13, `2026-09-28T17:51:20Z` through `2026-09-28T17:52:07Z`; they
fall between `4abaac92` (committed 17:47:48Z) and
`d01e2c3e` (18:35:56Z), and its `pnp3/Tests/AxiomsAudit.lean` diagnostics occupy
exactly 5066 distinct command positions with maximum line 6234 — matching the
layout at `4abaac92`, where 5064 `#print axioms` plus two `#check` commands fill
6234 lines, rather than at `d01e2c3e`, where the file is 6318 lines with 5122
`#print axioms`. Consistently, GN-E2-5a's writer and its surface module appear
throughout the log, while the G3l origin-alignment countdown module that
`d01e2c3e` merged in from `main` at `9445a93e` never appears in it. This fingerprint
matches the audit-command layout at `4abaac92`; it establishes neither exact
file bytes nor checkout identity, and **exclusivity is not established** —
nothing in the log shows what else was running or that the tree was otherwise
clean. The run is therefore evidence about this branch's content at `4abaac92`
and about nothing later: `d01e2c3e` brought in `main`'s G3l Lean modules, which
that run never compiled, and `40ea2346`, `51db7753` and `bceb38db` subsequently
moved the head again in the history through `bceb38db`.
**The exclusive full check at the final head is still owed**, and nothing above
is claimed as it. The passing local full `./scripts/check.sh`
named in the GN-E2-4a record belongs to that slice at `6718b422` and says
nothing about this slice's head.

Still owed before merge: a fresh exact-head review of the corrected head
(the `311abc6b`, `d01e2c3e`, `40ea2346`, `51db7753` and `bceb38db` reviews
and the `bceb38db` adjudication apply only to their named SHA), the
exclusive full
`./scripts/check.sh`, all final-head remote checks, the repository owner's
exact `/tmverifier-unfreeze <full-sha>` attestation, the `tmverifier-unfreeze`
label, agentic review, and a history-preserving merge. The §6.1 size gate is no
longer among the owed items: it is green at the current merge base, as recorded
above. Every push requires a fresh attestation. The branch
must not be squash-merged or rebased because stage (a) is the provenance commit
named by the pin.

### 2026-09-29 — PR #1804 Qodo exact-head owner-label correction

**Classification: Infrastructure only.** The owner supplied the legitimate
Qodo finding against exact head `1b5aa3e219d30d2292c8cd13bbc8e68acbbb1d90`:
`GateNValuesRewind.lean:531` assigned the values copy to the retired `E2-4b`
name instead of `GN-E2-5b`. This records that finding, not an independently
retrieved review, an overall Qodo verdict, or review of either correction head.

Stage (a), `1e7fe40592001142378ff3620c888045d8c10594`, has that exact
reviewed head as its parent and changes only `which E2-4b owns` to
`which GN-E2-5b owns`. Checker pins and manifest are byte-identical to the
parent. The old freeze checker detected precisely this expected one-file drift
before the repin. No theorem signature or executable semantics changed.
Stage (b), the separate commit carrying this record, changes no frozen bytes:
it repoints `FROZEN_COMMIT` to stage (a), `FROZEN_TREE` to
`145252565dc2538c6c01c19fc2f6814abc1c3a8d`, and regenerates schema-3
`spec/tmverifier_freeze.json` with
`python3 scripts/check_tmverifier_freeze.py --write-manifest`.  For this
owner-docstring repin, the regenerated manifest changes only the rewind blob
entry and the two provenance fields.  Earlier, the original GN-E2-5a repin
`11dc8e82` → `311abc6b` added the `GateNValuesWriter.lean` entry, changed the
`GateNBodyRound.lean`, `GateNFixedDelegateRelocation.lean`, and
`GateNValuesRewind.lean` entries, and updated those same provenance fields.
This is the fifth migration since `42c59881`; prior migrations remain historical.
The older `11dc8e82` → `311abc6b` pair and all ancestry through `1b5aa3e`
are preserved. No superseded GN-E2-4b1 donor worktree or commit was touched.

Local validation for this correction:

- `pnp2-lake lane-b build Complexity.TMVerifier.TuringToolkit.GateNValuesRewind
  Complexity.TMVerifier.TuringToolkit.GateNValuesWriter
  Tests.TMGateNValuesRewindSurfaceTests Tests.TMGateNValuesWriterSurfaceTests`
  passed on the stage-(a) source bytes (existing linter warnings only; log
  `/tmp/gn-e25-qodo-lane-b.log`). Stage (b) changes no Lean source.
- `bash scripts/check_tmverifier_freeze.sh` passed: 118 objects, the new tree,
  and stage-(a) provenance verified. `bash scripts/test_tmverifier_freeze.sh`
  and `node scripts/test_tmverifier_freeze_policy.js` passed their local tests.
- `bash scripts/check_doc_honesty.sh` and `git diff --check` passed.
- `python3 /tmp/gn-e25-provenance.py` verified the exact one-line replacement,
  stage-(a) unchanged pins, stage-(b) unchanged frozen bytes, the manifest's
  exact commit/subtree, and ancestry with `git merge-base --is-ancestor` for
  `11dc8e82`, `311abc6b`, `1b5aa3e` and stage (a), plus `311abc6b^ = 11dc8e82`.
  Its `git diff --numstat` against the current merge base with `main`,
  `2f8a3d5e6f90fe41a2cd7bc240d3c9fad407b68e`, measured 1468 additions and
  31 deletions: **1499 Lean lines across 8 files**, within §6.1's 1500/10 cap.
- Forbidden-token scan over all eight changed Lean files covered `axiom`,
  `sorry`, `admit`, `native_decide`, `Classical.choose`, `Classical.arbitrary`,
  `Nat.find` and TODO/FIXME/PLACEHOLDER markers. The raw scan found two existing
  line comments in `AxiomsAudit.lean` (one TODO and one use of the word axiom);
  excluding line comments produced no hits. Neither comment changes here.

No global `./scripts/check.sh` was run: the owner explicitly excluded it because
CI/builds are active and full checks require exclusivity. The full final-head
gate, fresh exact-head review, remote CI, owner attestation and PR review remain
owed; local policy tests do not establish the remote policy gate. The category
is only `Infrastructure`, and `tmverifier-unfreeze` remains the intended unfreeze
label, not a second category or a newly applied label. No push, PR operation,
history rewrite or GN-E2-5b implementation is part of this correction.

### 2026-10-01 — GN-E2-5b exact one-value copy

This is the explicitly authorized local Infrastructure continuation from merged
GN-E2-5a `b83de46cc67ecfbf52093807b66b9cd7acf04010`, scoped to one value,
its return to the live classifier, and its residual-list/tail handoffs.
The frozen target, theorem premises, literal fixtures, targeted build command,
44 direct audit roots, and completion limits are in
[GN_E2_5B_VALUES_COPY.md](GN_E2_5B_VALUES_COPY.md).

The migration preserves the required order and existing ancestry:

| Item | Exact value |
| --- | --- |
| Stage (a), committed frozen bytes and registration | `b16d816e011560e86ea81ffa1a08da20e18cd2d2` |
| Stage (b), checker/manifest repin | `df7699642bf22673cfee7f3ebe6c37e36128360a` |
| Stage-(a) whole repository tree | `7ef7a45e0c53bbd1d24c615a9a523d7615810b25` |
| New authoritative TMVerifier subtree | `e4fa8f333a055e8bbce4c258af7f84719426416a` |
| Previous provenance | `1e7fe40592001142378ff3620c888045d8c10594` |
| Previous authoritative subtree | `145252565dc2538c6c01c19fc2f6814abc1c3a8d` |

Stage (a) carries no pin change. Stage (b), named above, changed the checker's
two pin constants and regenerated the manifest
from that committed Git tree. Schema 3 and `spec/version_manifest.toml` are
unchanged. There are 119 manifest objects, up from 118: one added blob,
`TuringToolkit/GateNValuesCopy.lean`, and one changed blob,
`TuringToolkit/GateNValuesWriter.lean` (public classifier visibility and scope
prose). No object is removed, and no mode or type changes. No transition-owner
byte, machine, encoder, clock, state constructor or row is changed.

The Lane B targeted build passed, including old writer/rewind surfaces; the
focused audit emitted all 44 roots with only `propext`, `Classical.choice` and
`Quot.sound`. The freeze checker and its negative-control suite both passed;
logs are `/root/reports/gn-e25b-targeted.log`,
`/root/reports/gn-e25b-freeze-check.log` and
`/root/reports/gn-e25b-freeze-tests.log`. The suite covered manifest/schema,
filesystem, rewritten history, provenance, object-state, missing object store,
nested prefix, authoring, tracing, root authoring and its provenance-free
self-hosted run. None is a full repository gate or an independent review.

The implementation delta at stage (b) is 903 changed Lean lines (898 added, 5 deleted), seven Lean
files including `lakefile.lean`, against the exact base above. No donor commit
was merged/cherry-picked. Only donor proof geometry was adapted; its conflicting
entry and exit rows and `8*d+30` clock were not restored. The proved exit costs
`8*d+37`; returning to `valuesEntry` costs one additional dispatch row. The
1184-row real initial fixture and the independent 46-row kernel reduction both
leave the scratch request tail pending. Full-list execution, nonempty request
completion, launch, delegation, commit, repeated gates, total installer clock,
verdict and acceptance remain deferred. No full gate, remote check,
attestation, push or PR is claimed for either migration stage.

Fable 5.1 and Codex subsequently both returned **APPROVE** at the exact
stage-(b) head above. The parsed Fable `result` and Codex text, their evidence
limits and all documentation-note dispositions are recorded in
[the review remediation record](GN_E2_5B_VALUES_COPY.md#exact-head-review-and-documentation-remediation-2026-10-01).
N1/N3 remain open with a named Lane B owner there. The later documentation-only
correction preserves both stage commits and changes no frozen byte, checker
pin or manifest entry; it adds no theorem or stronger contract. Its surface
comment qualifies the frozen literal docstring's narrated pre-state without
editing that source. No Lean/lake/check build or full gate is run during this
correction, and the two earlier approvals do not review its new head.


### 2026-10-01 — GN-E2-5c values-list induction and completed first request

Infrastructure only. The exact pre-implementation targets, premises and
validation are in [GN_E2_5C_VALUES_INDUCTION.md](GN_E2_5C_VALUES_INDUCTION.md).
The initial endpoint now covers every actual input list and assumes only the
selected first-gate equation. The additive clock uses `8*d+38` per copied
value and the landed `4*d+20` tail phase. No machine row changes; launch,
delegation, returned-bit commit, repeated gates, verdict, acceptance and runtime
adequacy remain open, along with N1/N3. Neither P-vs-NP source is reduced.

Stage (a), `d1694e4b8c3e4838fb38d682f4c10d5ffacc6eb8`, is a direct child of
`b71eb6ca3ff4101d6d1596dfb4fc06ce63f845c7`; its repository tree is
`2e9f958a192376763a84e2bc9beb0633820972e9` and TMVerifier subtree is `b2762b378800f81e6adaaa3ecbe6b277ddd59482`.
Stage (b), `4ffd71f356e13babde80397186ee176e5455ccc5`, records the repin as
its direct child. Neither stage is amended or rebased. The superseded donor
commits are unused and remain outside ancestry.

The manifest remains schema 3, growing from 119 to 120 objects. Only the new
`GateNValuesInduction.lean` blob is added and the existing writer blob changes;
there are no removals or mode/type changes. Its new blob is
`63f54e173803d0b7c78fce71aaca936408b91da7`, SHA-256
`f11ae088effa48232092e1234fac21fac2ba3416975976a5cbc1bb79e79e0c5c`.
The former frozen tree/provenance pair is retained in the GN-E2-5b historical
record above. `spec/version_manifest.toml` is unchanged.

The targeted Lane B build passed, including the focused audit and affected
older surfaces. All 22 new direct roots emitted only the standard axiom union
`propext`, `Classical.choice`, `Quot.sound`. The 529-line/six-Lean-file delta
includes registrations and both audits. The checker verified 120 matching Git
objects and stage-(a) provenance; `test_tmverifier_freeze.py` passed its manifest,
filesystem, history, provenance, object-state, authoring and self-hosted
controls. The local freeze-policy unit tests passed. Logs are under
`/root/reports/gn-e25c-*.log`, named explicitly in the slice record.

This paragraph records the stage-(b) evidence snapshot only: at stage (b), no
full repository gate, independent exact-head review, remote gate or attestation,
push, or PR was claimed. The later integration-head full gate, reviews, PR,
owner attestation and remote evidence are recorded in the release header above
and in the linked GN-E2-5c slice record. Local policy tests alone are not a
remote policy approval, and no release approval is inferred from historical
reviews.

### 2026-10-01 — GN-E2-5d first request launch and returned interception

Infrastructure only. The exact targets, premises, clocks, scope limits and
validation are in
[GN_E2_5D_FIRST_REQUEST_LAUNCH.md](GN_E2_5D_FIRST_REQUEST_LAUNCH.md).
The slice executes the selected first request from the real encoded GN input to
the fixed delegated G1 start under the selected-first-gate premise. With the
additional defined-specification equation it executes through output-done and
the returned-state interception. Result commit, cursor/spent advance, repeated
gates, verdict, GN acceptance, first-arrival minimality, composed runtime
adequacy, `ContentVerifierBridge`, and Lane B N1/N3 remain open. Neither P-vs-NP
source obligation is reduced.

The ordered migration preserves ancestry and has the following exact values:

| Item | Exact value |
| --- | --- |
| Stage (a), committed frozen bytes and registration | `f07c4439c3f04a5455b624403be8efcfb16be29e` |
| Stage (b), checker/manifest repin | `2644c72452a5b327355a0a87ca8292e74a1f81ac` |
| Stage-(a) whole repository tree | `754cc5ce57827bacf71e92515fb00ecd808fda06` |
| New authoritative TMVerifier subtree | `bf871e090bf1ca564293502e4ff09c1c5f8ca9a0` |
| Previous provenance | `d1694e4b8c3e4838fb38d682f4c10d5ffacc6eb8` |
| Previous authoritative subtree | `b2762b378800f81e6adaaa3ecbe6b277ddd59482` |

Stage (a) carries no pin change and changes exactly the authorized owner and
writer blobs; the other 118 frozen objects remain byte-identical. Stage (b)
changes no Lean or frozen byte, updates the two pin constants, and regenerates
the schema-3 120-object manifest from the committed stage-(a) tree. Both prior
GN-E2-5c migration stages and the exact base remain ancestors; no donor commit
is merged or cherry-picked.

Two writer docstrings retained in the frozen snapshot call `requestReady`
"dormant". They are dated descriptions of the GN-E2-5c writer endpoint, not a
claim about the composed GN-E2-5d machine: the authorized owner row now leaves
`requestReady`, and the new launch theorems execute that row. Correcting those
historical source comments would require another frozen-byte migration, so this
record qualifies them without altering the reviewed stage-(a) bytes.

The Lane B targeted build, both audits, freeze checker, negative controls and
local policy tests passed as recorded in the linked slice record. At stage (b),
the globally exclusive full gate, exact-head reviews, push, PR, owner
attestation and remote checks were not yet claimed; later release evidence must
be recorded on its actual descendant head.
