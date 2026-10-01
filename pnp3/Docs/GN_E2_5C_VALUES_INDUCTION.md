# GN-E2-5c values induction and first-request tail

Classification: **Infrastructure only**. Authorized base:
`b71eb6ca3ff4101d6d1596dfb4fc06ce63f845c7` (merged GN-E2-5b). This target/premise freeze was written before editing Lean sources
on 2026-10-01. It is a working-tree pre-implementation record, not a separately
committed specification. The immutable implementation snapshot will be stage
(a); stage (b) will regenerate the content-addressed freeze without changing
those frozen bytes. The cap is 1500 changed Lean lines and 10 modules,
including registrations, surfaces and audits in the measurement.

## Frozen target and every premise

Names below are in `Pnp3.Internal.PsubsetPpoly.TM`. For generic statements,
`n : Nat`, `pre middle : List G1Frame`, and `values : List Bool` are arbitrary.
Write `p = pre.length`, `k = values.length`, `m = middle.length`, and
`L = GNM.tapeLength n`; these are proof/documentation abbreviations, never
machine state. The generic list premises are exactly:

```lean
(hmiddle : ∀ f ∈ middle, GNInstallAdmissible f)
(hroom : 4 * (pre.length + 2 * values.length + middle.length + 3) <
  GNM.tapeLength n)
```

1. `gnCS_values_list_exact`: genuine `TM.runConfig (M := GNM)` from
   `gnPendingValuesConfig n pre values middle _ .valuesEntry` after
   `gnValuesListSteps values middle = k * (8 * (k + m) + 38)` to
   `gnPendingValuesConfig n (pre ++ values.map G1Frame.data) []
   (middle ++ values.map G1Frame.data) _ .valuesEntry`.
   The proof must induct on the actual list using landed
   `gnCS_values_cons_exact`, including the live eight classifier/back rows
   and stationary data-exit dispatch on every iteration. No run equality is
   a premise. The empty base costs zero. `gnValuesListSteps_cons` must state
   the exact additive recurrence: first step `8*(bs.length+1+m)+38`, then
   the recursive clock on `bs` and `middle ++ [G1Frame.data b]`.
2. `gnCS_values_outputFalse_tail_exact` in the existing writer module:
   arbitrary `n`, `pre`, `middle`; only admissibility and
   `4*(p+m+3) < L`. Start at `gnCopyShuttle.cfg n (4*p) _` with tape
   `(pre ++ output false :: middle ++ [blank, blank]).flatMap G1Frame.bits`
   interpreted by `frameListTape`, state `valuesEntry`. After `4*m+20` rows,
   reach head `4*(p+m+3)`, state `requestReady`, and full tape
   `(pre ++ output false :: middle ++ [output false, finish, blank]).flatMap
   G1Frame.bits`. This exposes the already-proved private
   `gnCS_values_terminal`, including four output-false classifier rows,
   `4*(m+1)` seek rows, four back rows and eight writes. It does not assume
   that execution or alter a transition.
3. `gnCS_values_list_requestReady_exact`: same generic list premises as (1),
   same starting configuration, clock
   `gnValuesListSteps values middle + (4*(m+k)+20)`, ending in
   `gnValuesListReadyConfig n pre values middle hroom`: head
   `4*(p+2*k+m+3)`, state `requestReady`, full tape
   `(pre ++ values.map data ++ output false :: middle ++ values.map data ++
   [output false, finish, blank]).flatMap G1Frame.bits` via `frameListTape`.
   This must compose (1) with (2), not just enter the tail seek.
4. `gnCS_valuesEntry_requestReady_exact`: `{r : GNProgram}`,
   `{g : SLGate r.inputs.length}`, with **only**
   `hg : r.program.gates[0]? = some g`. From `gnValuesEntryConfig r g hg`
   execute `r.inputs.length*(8*gnValuesTailDistance r g+38) +
   gnValuesTailSteps r g` rows to the existing
   `gnFirstRequestReadyConfig r g hg`. Values are exactly `r.inputs`,
   covering arbitrary nonempty lists and the empty case. Derive all room,
   admissibility, tape and request-prefix equalities internally from `hg`
   and the landed encoding lemmas.
5. `gnCS_encodeGN_valuesRequestReady_exact`: the same parameters and sole
   premise `hg` as (4), starting at
   `GNM.initialConfig (gnPoint (encodeGN r))`, clock
   `gnValuesRequestReadySteps r g = gnValuesEntrySteps r g +
   (r.inputs.length*(8*gnValuesTailDistance r g+38) + gnValuesTailSteps r g)`,
   and the same existing exact request-ready configuration. In particular,
   the scratch word is the actual `encodeG1Frames (gnFirstRequest r g)`.
   No evaluation result or proof-to-runtime selection is supplied.

Supporting arithmetic and structure statements have only their typed data
parameters (or `hg` when they concern the actual selected first request).
Literal full-tape fixtures will cover multiple values and the real nonempty
`capProgram`; a small independent kernel execution will pin changed cells.
The existing malformed-ingress rejection will be retained and directly
pinned. Every new public theorem will receive a named full-proposition
surface and direct owner/surface `#print axioms` roots in both a focused audit
and the aggregate audit. Private proof helpers have no public-surface promise.

## Dependency and scope boundary

Only the landed GN-E2-5b one-value execution, GN-E2-5a tail writer and earlier
real-input values-entry execution are used. The machine owner, encoder and
runtime allocation remain unchanged. No superseded donor commit is used.
No advice, choose/find, runtime witness, execution hypothesis, or
proof-to-runtime selection is permitted. No new proof escape is permitted.

If the full real-input composition cannot be proved within the cap or lacks
a precise landed dependency, stop at the strongest executed list/tail
endpoint above and record the precise blocker, without claiming completion.

Still open after the intended endpoint: request launch/rewind, delegation,
returned-bit commit, next-gate/cursor loop, total installer/runtime bounds,
verdict, acceptance and all language lower bounds. The first-arrival N3
obligation and general invalid-exit surface N1 remain Lane B carry-forward
work unless explicitly discharged and audited here. An exact additive
execution clock is not a first-arrival or public-runtime adequacy theorem.
The landed writer overwrites its two destination frames; generic theorems
here specify both as blank, and do not claim arbitrary corruption rejection.

## Implementation and validation record

All five frozen targets are implemented with exactly the premises above;
there is no dependency blocker or truncated endpoint. The implementation is
**529 added, 0 deleted Lean lines across six Lean files including lakefile.lean**
against the exact base. Five modules are affected; three are new (owner,
surface, focused audit). The owner is `GateNValuesInduction.lean`; the only
existing frozen-source addition is the 23-line public interface to the
already-landed terminal execution in `GateNValuesWriter.lean`.
`GateNFixedDelegateRelocation.lean` and `spec/version_manifest.toml` are
byte-identical to the base. No machine row or finite control changes.

The list induction uses the actual `values` parameter at every cons step and
calls `gnCS_values_cons_exact`. Both source position and destination frontier
advance by one frame, so `d = k + m` remains constant. The generic room bound
uniformly includes the final head after the tail write and implies every
one-copy room premise. The real specialization derives `k+m =
gnValuesTailDistance r g` and the entire initial/final tape equalities from
the encoded input and selected first gate. The initial theorem's only premise
is `hg`; no nonemptiness, room, execution, destination-value, canonicality,
evaluation or well-formedness premise is added. It covers the empty list too.
This is an encoded-input execution theorem; no new theorem for arbitrary
unencoded bytes accepted by a decoder is claimed.

The complete two-value fixture runs `[true, false]` in `108 + 28 = 136` rows,
ending at head 28 with both copied values, output false, finish and a blank.
Its full-tape equality is proved by composition. A separate `decide +kernel`
fixture reduces the actual 136 transitions and checks state, head, a cell
changing false to true, and cells in each written tail frame. It is not
claimed axiom-free. The real nonempty capProgram fixture runs `954 + 230 +
116 = 1300` rows, ending at head 116 on the blank following the full installed
G1 request; its literal tape has 30 frames. Its decoding conjunct is the pure
identity identifying the actual encoded program, not an executed decoder.
The reserved-1101 fixture retains four-row rejection and stable reject padding.
The unchanged row table retains the other existing fail-closed ingress cases.
These runs use finite, boundary-clamped tapes; tape equality covers all
allocated cells. The arbitrary generic prefix need not itself encode a program.

All 11 public theorems (including the new writer interface) have named
full-proposition wrappers. Seven new definitions have name pins. The focused
and aggregate audits contain the same 22 direct owner/wrapper roots. The
focused build emitted all 22; their axiom union is exactly `propext`,
`Classical.choice`, and `Quot.sound`. Classical library axioms in the proof
closure do not supply values or a runtime selection mechanism.

The implementation passed on 2026-10-01:

```text
pnp2-lake lane-b build \
  Complexity.TMVerifier.TuringToolkit.GateNValuesInduction \
  Tests.TMGateNValuesInductionAxioms \
  Tests.TMGateNValuesCopyAxioms \
  Tests.TMGateNValuesWriterSurfaceTests \
  Tests.TMGateNValuesRewindSurfaceTests
```

Log: `/root/reports/gn-e25c-targeted.log`, exit 0, `Build completed
successfully`. The surface module is a dependency of the new focused audit.
Warnings include unused admissibility binder names in full-proposition
wrappers and existing dependency lints; there are no compilation errors.
Compilation used the Lane B wrapper and an isolated copy of the landed
GN-E2-5b cache, not a clean dependency rebuild. An initial cache setup attempt
raced an unfinished copy and failed before compilation; the copy was completed
before later builds. Subsequent proof-elaboration failures were corrected;
the successful log above is the final implementation validation.
Source/audit checks are recorded in `/root/reports/gn-e25c-source-audit.log`.
`git diff --check` passed. No new axiom declaration, proof escape, choose/find,
advice, or proof-to-runtime selection is present.

The pre-implementation target text is preserved separately at
`/root/reports/gn-e25c-target-freeze.md`, SHA-256
`dbc5f23df25aa2fc29bfae0d22fcc705a6a32fc3bc9adc442575928f7a8601f1`.
That external copy was saved after implementation started; it preserves the
unchanged target text written before Lean editing, and is not evidence of a
separate pre-implementation commit. The exact five target propositions and
premises above were not weakened during proof elaboration.

Stage (a) commits the validated frozen bytes, registrations, surfaces, audit
roots and this record, while retaining the GN-E2-5b checker/manifest pins.
Stage (b) must next repin the checker to stage (a), author its manifest from
that committed Git tree and run the focused freeze checks, changing no frozen
source byte. Neither stage is to be amended or rebased. At this stage-(a)
snapshot those freeze checks are pending; the old pin deliberately does not
validate the new frozen bytes.

No full repository `./scripts/check.sh`, aggregate audit build, independent
review, remote gate, owner attestation, push or PR is claimed by this lane.
This Infrastructure execution result reduces neither lower-bound source
obligation. N1 and N3 remain open and owned by Lane B. First arrival for the
new endpoint and a bound of its full new clock by `GNM.runTime` are also open,
as are every launch/delegation/commit/loop/verdict/acceptance/runtime obligation
listed above. Final commit IDs and clean-worktree checks will be written to
`/root/reports/gn-e25c-writer-final.txt` after both stages.
