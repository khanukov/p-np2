# GN-E2-5b exact one-value execution

Progress classification: **Infrastructure only**. Base: merged GN-E2-5a
`b83de46cc67ecfbf52093807b66b9cd7acf04010`.
This file freezes the target and open hypotheses before implementation.

The user authorizes this one-value frozen-TMVerifier slice, with targeted
`pnp2-lake lane-b` builds only, no full repository gate, no push and no PR.
Stage (a) commits the frozen bytes, registration, surfaces and audit roots;
stage (b) separately repins the content-addressed manifest and checker.
No independent review, remote gate, attestation or P-vs-NP progress is claimed.

## Frozen target

On the existing GNM, start in `valuesEntry` on `data b`, classify its four
physical cells, take four backward rows into the existing installer, execute
its source-restoring shuttle to the first blank, then dispatch its carried
`data b` exit back to `valuesEntry` on the following source frame. The complete
tape equality must replace the destination blank by `data b`, preserve the
source and all other cells, and retain the following blank. The request's
`output false`/`finish` tail is still pending at this endpoint.

Clock endpoints are distinguished explicitly: `8*d+37 = 8+(8*d+29)` reaches
the installer exit. The existing stationary exit dispatch costs one further
row, so the return to `valuesEntry` costs `8*d+38`. The donor's `8*d+30`
clock and its direct valuesEntry-to-installer and data-exit-to-installer rows
are incompatible with this machine and will not be restored.

The generic theorem has an arbitrary frame prefix, source bit, middle and
suffix; hypotheses are (1) every middle frame is neither blank nor temporary
`output true`, and (2) `4*(pre.length+middle.length+2) < GNM.tapeLength n`.
A nonempty-list handoff must identify the remaining values and append the
copied bit to the installed prefix. If another data value follows, the live
classifier must enter its installer in eight rows; if the list is exhausted,
the next `output false` must enter the existing tail seek in four rows.
Neither handoff claims execution of the remaining list or completion of its
tail.

The real-input theorem starts at `GNM.initialConfig (gnPoint (encodeGN r))`.
Its only premises are the actual first-gate equation
`r.program.gates[0]? = some g` and nonempty input equation `r.inputs = b::bs`.
It must end in a full `TM.runConfig` equality to a configuration with state
`valuesEntry`, head 8, and tape consisting of the original GN word, the
installed first record image, `data b`, and a blank. Room/admissibility and
all representation equalities must be proved, not assumed.
A small literal fixture will pin the numeric clock and changed tape if feasible.

## Open obligations and evidence boundary

Initially open: physical data classification/back execution, data exit return,
generic source-restoring composition, nonempty-list and exhausted-list
handoffs, real-input geometry/room/composition, literal fixture, surfaces and
direct axiom roots. These are proof obligations, not assumed execution facts.
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

All 21 new public theorem declarations and the promoted classifier have named
full-proposition wrappers (22 total), with 44 direct owner/wrapper axiom roots
in both the focused `Tests.TMGateNValuesCopyAxioms` and the aggregate audit.
The focused audit permits dependency-closed validation without the aggregate
repository build. The final measurement against the exact base is **903 changed
Lean lines: 898 added, 5 deleted, across seven Lean files including
`lakefile.lean`**. Three modules are new (owner, surface, focused audit).
The machine owner `GateNFixedDelegateRelocation.lean` is byte-identical to the
base. The 878-line/six-file draft measurement preceded proof elaboration fixes
and the existing writer-surface docstring clarification.

## Completion and targeted validation

All initially open obligations within the frozen one-value target above are
closed. The real initial theorem assumes only `hg` and `hvals`; there is no
assumed execution, advice, runtime witness, or destination-value premise. The
remaining values and scratch request tail are still pending on return.
Full-list execution and every later obligation listed above remain open.

This exact Lean snapshot passed on 2026-10-01:

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
No independent review, remote gate, owner attestation, push or PR is claimed.
The long initial wait for another job's exclusive build lock was respected;
all Lean compilation in this lane used `pnp2-lake lane-b` and isolated caches.

Stage (a) commits this validated frozen snapshot, registration and audits
without changing either freeze pin. Stage (b) will record stage (a)'s exact
commit and trees, repin the checker, regenerate the manifest from Git, and run
the focused freeze checker and its negative controls. No donor commit has
been merged or cherry-picked; all three donor SHAs remain outside ancestry.
