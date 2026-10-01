# GN-E2-5b exact one-value execution

Progress classification: **Infrastructure only**. Base: merged GN-E2-5a
`b83de46cc67ecfbf52093807b66b9cd7acf04010`.
This record first appeared with the implementation in stage (a). The target
and hypotheses below describe that bounded implementation contract; this is
not evidence of a separately committed pre-implementation specification.

The implementation authorization covered this one-value frozen-TMVerifier
slice, with targeted
`pnp2-lake lane-b` builds only, no full repository gate, no push and no PR.
Stage (a) committed the frozen bytes, registration, surfaces and audit roots;
stage (b) separately repinned the content-addressed manifest and checker.
The exact-head reviews and subsequent documentation-only remediation are
recorded below. At the implementation stages recorded here, no remote gate or
attestation was claimed. No P-vs-NP progress is claimed at any stage.

## Implemented bounded target

On the existing GNM, start in `valuesEntry` on `data b`, classify its four
physical cells, take four backward rows into the existing installer, execute
its source-restoring shuttle to the first blank, then dispatch its carried
`data b` exit back to `valuesEntry` on the following source frame. The complete
tape equality replaces the destination blank by `data b`, preserves the
source and all other cells, and retains the following blank. The request's
`output false`/`finish` tail is still pending at this endpoint.

Clock endpoints are distinguished explicitly: `8*d+37 = 8+(8*d+29)` reaches
the installer exit. The existing stationary exit dispatch costs one further
row, so the return to `valuesEntry` costs `8*d+38`. The donor's `8*d+30`
clock and its direct valuesEntry-to-installer and data-exit-to-installer rows
are incompatible with this machine and were not restored.

The generic theorem has an arbitrary frame prefix, source bit, middle and
suffix; hypotheses are (1) every middle frame is neither blank nor temporary
`output true`, and (2) `4*(pre.length+middle.length+2) < GNM.tapeLength n`.
A nonempty-list step identifies the remaining values and appends the
copied bit to the installed prefix. If another data value follows, the live
classifier enters its installer in eight rows; if the list is exhausted,
the next `output false` enters the existing tail seek in four rows.
Neither handoff claims execution of the remaining list or completion of its
tail.

The real-input theorem starts at `GNM.initialConfig (gnPoint (encodeGN r))`.
Its only premises are the actual first-gate equation
`r.program.gates[0]? = some g` and nonempty input equation `r.inputs = b::bs`.
It ends in a full `TM.runConfig` equality to a configuration with state
`valuesEntry`, head 8, and tape consisting of the original GN word, the
installed first record image, `data b`, and a blank. Room/admissibility and
all representation equalities are proved internally.
The literal fixtures below pin the numeric clocks and endpoint tapes.

## Open obligations and evidence boundary

Obligations discharged by this implementation: physical data classification/back
execution, data exit return,
generic source-restoring composition, nonempty-list and exhausted-list
handoffs, real-input geometry/room/composition, literal fixture, surfaces and
direct axiom roots. Their proofs supply the execution facts used below.
Still outside this slice: induction over all values, tail execution after a
nonempty run, a completed nonempty request, launch/delegation/commit, repeated
gates, total installer clock, verdict, acceptance, and any language lower bound.

Read-only donor evidence: `/root/pnp2-lane-b-gn-e24b1`, commits
`706a2ff8453ac172947b990b0ed56754e68c4b5b`,
`f4be6fd3678a7e6d5301266f1d0c660d9fe25e17`, and
`161f31329822fc8c1414169cf203aac840e319da`.
Only proof geometry may be adapted. No merge/cherry-pick or donor machine row
is authorized. Current GN-E2-5a semantics control every execution statement.

## Checked implementation

`GateNValuesCopy.lean` composes the live classifier, four backward rows,
existing `gnCS_copyShuttle_nextBlank`, and the carried-data dispatch. It adds
no transition or control constructor. `GateNValuesWriter.lean` promotes
`gnCS_values_classify` from private to public so that the exact landed
classification proof can be reused and directly audited, and clarifies the
limited continuation now owned by this slice. Its existing surface module
docstring identifies where the promoted classifier is pinned.

The public endpoints are `gnCS_valueCopy_exit_exact` (`8*d+37`),
`gnCS_valueCopy_return_exact` (`8*d+38`), `gnCS_values_cons_exact`, and
`gnCS_encodeGN_firstValueCopied_exact`. The cons theorem consumes exactly one
list element and restates the residual boundary with the copied bit appended
at the destination. The two handoff theorems execute the live next classifier;
neither substitutes an assumed execution witness. The real-input structure
lemma's request-prefix identity is a pure ledger of installed and pending
values, not execution of the remaining list.

Fixtures cover both bits (46 rows), a second pending value (54+8 rows), an
exhausted singleton entering tail seek (46+4 rows), and reserved `1101`
rejecting in four rows. The 46-row `literal_tiny_executable` independently
reduces the actual transition function with `decide +kernel` and checks state,
head and a destination cell changing false to true. The real initial fixture
has 84 input bits, distance 24, and a checked 1184-row endpoint whose 28-frame
tape includes the new `data true` at bit 104 and a retained blank at bit 108.
The tail `output false`/`finish` remains unwritten in the scratch region.
`literal_cap_firstValueCopied` asserts the 1184-row run equality and its
head/state/schedule/distance facts. Its endpoint configuration defines the
tape; the frozen docstring's phrase "was blank" is narration, not a separate
pre-state conjunct in that theorem. The unfrozen surface wrapper documents
this distinction without strengthening the proposition. The small
`literal_tiny_executable` theorem separately states both values of cell 9.

These are explicit-step executions on finite, boundary-clamped tapes.
Generic list tapes specify allocated cells; an arbitrary suffix need not fit
in full. No scoped bound by `GNM.runTime` for the new endpoint, general
first-arrival theorem, clock-adequacy theorem or acceptance theorem is exported.

All 21 new public theorem declarations and the promoted classifier have named
full-proposition wrappers (22 total), with 44 direct owner/wrapper axiom roots
in both the focused `Tests.TMGateNValuesCopyAxioms` and the aggregate audit.
The focused audit permits dependency-closed validation without the aggregate
repository build. The implementation measurement at reviewed stage (b)
`df7699642bf22673cfee7f3ebe6c37e36128360a` against the exact base is **903 changed
Lean lines: 898 added, 5 deleted, across seven Lean files including
`lakefile.lean`**. Three modules are new (owner, surface, focused audit).
The machine owner `GateNFixedDelegateRelocation.lean` is byte-identical to the
base. The 878-line/six-file draft measurement preceded proof elaboration fixes
and the existing writer-surface docstring clarification.

## Completion and targeted validation

All implementation obligations within the bounded one-value target above are
closed. The real initial theorem assumes only `hg` and `hvals`; there is no
assumed execution, advice, runtime witness, or destination-value premise. At
this GN-E2-5b endpoint, the remaining values and scratch request tail were
still pending on return. GN-E2-5c subsequently closed that full-list/tail
execution boundary; every later obligation listed above remains open,
including the separately tracked N1/N3 items below. See
`GN_E2_5C_VALUES_INDUCTION.md`.

The stage-(a) implementation snapshot passed on 2026-10-01:

```text
pnp2-lake lane-b build \
  Complexity.TMVerifier.TuringToolkit.GateNValuesCopy \
  Tests.TMGateNValuesCopyAxioms \
  Tests.TMGateNValuesWriterSurfaceTests \
  Tests.TMGateNValuesRewindSurfaceTests
```

The surface module is a dependency of the focused audit. Log:
`/root/reports/gn-e25b-targeted.log` (exit 0, `Build completed successfully`).
All 44 expected direct audit roots appeared. Their axiom union is exactly
`propext`, `Classical.choice`, and `Quot.sound`; no additional axiom appears.
The literal executable uses kernel reduction; it does not assert axiom freedom.
The log contains linter warnings, including unused names of proof binders in
full-proposition wrappers, and no compilation error. Source scans found no
new proof escape or choose/find construction. `git diff --check` passed.

The aggregate audit was registered and updated; the focused audit's 44 roots
are reproduced there exactly. The aggregate repository build and full
`./scripts/check.sh` were **not run by this lane**, as explicitly instructed.
At implementation time no independent review was claimed; the later reviews
of stage (b) are recorded below. No remote gate, owner attestation, push or PR
is claimed here.
The long initial wait for another job's exclusive build lock was respected;
all Lean compilation in this lane used `pnp2-lake lane-b` and isolated caches.

Stage (a), `b16d816e011560e86ea81ffa1a08da20e18cd2d2`, commits this validated frozen snapshot,
registration and audits without changing either freeze pin. Its whole repository
tree is `7ef7a45e0c53bbd1d24c615a9a523d7615810b25` and its TMVerifier subtree is
`e4fa8f333a055e8bbce4c258af7f84719426416a`. It is a direct child of the exact base.
Stage (b), `df7699642bf22673cfee7f3ebe6c37e36128360a`, contains the completion
record and checker/manifest repin. It changes no frozen byte and preserves stage (a) as
its parent; neither stage is amended or rebased.

The previous pin was provenance `1e7fe40592001142378ff3620c888045d8c10594`,
frozen subtree `145252565dc2538c6c01c19fc2f6814abc1c3a8d`. The generated
manifest retains schema 3 and grows from 118 to 119 objects: only the copy
module is added and the writer module changes; no mode/type or removal delta.
`spec/version_manifest.toml` is unchanged. The new copy blob is
`1fb4efd1fe2a66c6d461f687abd5ba3660b78da1` (SHA-256
`f20950b4f3795575e21ec91afb06ea64f64bc8b83998272e02f047875ca798e6`).

Both focused freeze checks passed on the repinned bytes:

```text
python3 scripts/check_tmverifier_freeze.py
python3 scripts/test_tmverifier_freeze.py
```

Logs: `/root/reports/gn-e25b-freeze-check.log` (119 matching objects and
verified provenance), `/root/reports/gn-e25b-freeze-tests.log` (all manifest,
filesystem, history, provenance, object-state, authoring, tracing and
self-hosted controls passed). These local checks are not a full repository
gate or independent review. No donor commit has been merged or cherry-picked;
all three donor SHAs remain outside ancestry. The final local commit IDs and
clean-worktree result are recorded in
`/root/reports/gn-e25b-writer-codex-final.txt` after stage (b) is committed.

## Carry-forward ownership

The earlier GN-E2-5a reviews assigned N1 and N3 to a broader planned GN-E2-5b.
The bounded one-value implementation did not close either item. GN-E2-5c later
closed the values-list/tail execution boundary but explicitly did not close N1
or N3. **Lane B continues to own both after GN-E2-5c**; any implementation
requires a separately authorized scope and validation. This register assigns
follow-up responsibility and records open work, without scheduling another
frozen change.

| Item | Status and remaining obligation | Owner |
| --- | --- | --- |
| N1 | Open after GN-E2-5c: add a full-proposition surface restatement of the narrowed `GNInstallExitInvalid` predicate, with matching audit coverage. The existing bare name pin and `carried (.data b)` case wrapper do not supply that general restatement. | Lane B |
| N3 | Open after GN-E2-5c: prove general first-arrival minimality for GN-E2-5a's `gnCS_encodeGN_firstRequestReady_exact`, excluding `requestReady` at every earlier time. The exact endpoint theorem and literal execution evidence do not establish that general claim. | Lane B |

Neither item is a premise of the one-value endpoint theorem or a result of
this documentation correction. No completion or waiver of either is claimed.
GN-E2-5c now supplies full-list induction and completion of a nonempty first
request. A scoped `GNM.runTime` bound for that new complete clock remains
outside the proved contract.

## Exact-head review and documentation remediation (2026-10-01)

Both supplied reports review `df7699642bf22673cfee7f3ebe6c37e36128360a`
against `b83de46cc67ecfbf52093807b66b9cd7acf04010`:

- Fable 5.1: **APPROVE**, with seven nonblocking documentation notes, in the
  parsed `result` field of `/root/reports/gn-e25b-df76-exact-fable51.json`.
- Codex: **APPROVE**, no blocking finding, in
  `/root/reports/gn-e25b-df76-exact-codex.txt`.

They checked execution, surfaces, audit roots and the two-stage freeze, and
reported independent re-elaboration against cached dependencies. Those reviewer
runs are distinct from the author's targeted builds above and are not a clean
rebuild or full gate. The reviews apply only to their named head.

This later documentation-only correction gives historical pause/pin/status
sentences dated context, updates the status date, assigns N1/N3 above, removes
the pre-implementation claim, clarifies the literal theorem's narrated
pre-state in this record and its surface comment, and dates/describes all
three lakefile registrations. Lean declarations, proofs, registrations and
audit roots are unchanged; only comments change in the two edited Lean files.
Including those comments, the delta against the same merged base is **913
changed Lean lines (908 added, 5 deleted), still across seven Lean files**.
The earlier 903-line measurement belongs to reviewed stage (b).
The frozen TMVerifier sources, checker and manifest remain byte-identical to
stage (b); the original two commits remain in order and are not rewritten.
The freeze pins source bytes, not the entire semantic/toolchain dependency
closure. This remediation does not extend the bounded mathematical result.

The documentation correction was followed by a history-preserving integration
merge. At release head `e65231fc1be4c12d9338b39dd67e8d8e9a6b8571`, the targeted
Lane B build passed, exact-head remote CI completed `scripts/check.sh`, and
exact-head Codex and Fable 5.1 reviews approved. PR #1806 carries the `Infrastructure` and
`tmverifier-unfreeze` labels, the owner's exact-SHA attestation, and a successful
freeze-policy run. The first two policy attempts raced the attestation and failed
as expected; the subsequent exact-head policy run passed. Qodo's later finding
that the repository did not record those release events is addressed by this
dated correction. Fresh exact-head reviews, local gates, remote checks and
agentic-review coverage of the correction remain required before the
history-preserving merge. The bounded theorem result and all open obligations
are unchanged.
