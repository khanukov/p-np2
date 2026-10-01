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

Historical narration in `GateNValuesWriter.lean`, `GateNValuesRewind.lean`,
the GN-E2-5b registration comment in `lakefile.lean`, and the original
GN-E2-5b record describes what remained open at those earlier endpoints. It
does not override this module's subsequently proved list/tail execution. The
GN-E2-5b record now links here explicitly. Those frozen/source comments are
left byte-identical rather than starting an additional freeze migration solely
for retrospective prose.

The broader design discussion also suggested N1, clock-coincidence lemmas, and
a `gnValuesRequestReadySteps ≤ GNM.runTime` theorem. They were not part of the
five frozen targets and are intentionally re-scoped to later Lane B work; N1
and the complete-clock runtime bound remain listed below rather than being
implied by this slice.

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

Stage (a), `d1694e4b8c3e4838fb38d682f4c10d5ffacc6eb8`, committed the validated frozen
bytes, registrations, surfaces, audit roots and this record. It is a direct
child of the exact base; its whole repository tree is `2e9f958a192376763a84e2bc9beb0633820972e9`
and its TMVerifier subtree is `b2762b378800f81e6adaaa3ecbe6b277ddd59482`. Stage (a) retained
GN-E2-5b's checker/manifest pins. Stage (b),
`4ffd71f356e13babde80397186ee176e5455ccc5`, repinned only after those bytes
were committed, authored the manifest from that Git tree, and changed no frozen
source byte. The two commits remain in order without amendment or rebase.
At stage (b), its own commit ID was recorded only in the external final report;
the release checklist below now names it explicitly.

The previous tree was `e4fa8f333a055e8bbce4c258af7f84719426416a`, provenance
`b16d816e011560e86ea81ffa1a08da20e18cd2d2`. Schema 3 is retained and the
manifest grows from 119 to 120 objects: one new induction blob and one changed
writer blob, no removal or mode/type change. The induction blob is
`63f54e173803d0b7c78fce71aaca936408b91da7`, SHA-256
`f11ae088effa48232092e1234fac21fac2ba3416975976a5cbc1bb79e79e0c5c`.
`spec/version_manifest.toml` and the finite machine owner remain unchanged.

Stage (b)'s focused freeze validation passed:

```text
python3 scripts/check_tmverifier_freeze.py --write-manifest
python3 scripts/check_tmverifier_freeze.py
python3 scripts/test_tmverifier_freeze.py
node scripts/test_tmverifier_freeze_policy.js
```

Logs respectively: `/root/reports/gn-e25c-freeze-manifest.log`,
`/root/reports/gn-e25c-freeze-check.log`,
`/root/reports/gn-e25c-freeze-tests.log`, and
`/root/reports/gn-e25c-freeze-policy-tests.log`. All exit 0. The checker reports
120 matching objects and verified provenance. The Python negative controls
cover manifest trust/schema, filesystem changes, rewritten history, provenance,
object state, authoring, tracing and self-hosted verification. Policy unit tests
cover blanket paths, rename, attestation and API completeness; they do not
constitute remote policy approval. The checker's phrase “reviewed provenance”
identifies the commit/tree pair, not an independent review of this slice.
The freeze pins source bytes rather than the semantic/toolchain closure.

Documentation and review history (2026-10-01): Codex and Fable 5.1 both
reported **APPROVE** for the exact stage-(b) head
`4ffd71f356e13babde80397186ee176e5455ccc5`, in
`/root/reports/gn-e25c-4ffd-exact-codex.txt` and
`/root/reports/gn-e25c-4ffd-exact-fable51.txt`. Neither review re-elaborated Lean.
The direct docs-only child `6c21021a1ca9685bd7fa563c7cc005bc87fd08b8` addressed
prior review notes in the GN-E2-5b and GN-E2-5c records; it changed no Lean,
checker/manifest pin or frozen byte. Those two reviews cover stage (b), not
that docs-only child. The later Fable 5.1 report
`/root/reports/gn-e25c-6c21021-final-fable51.json` reviews exactly that child
and reports **APPROVE** with nonblocking notes. This subsequent documentation
correction addresses only its N-1 through N-3; no cited review covers this
correction's eventual commit SHA.

No full repository `./scripts/check.sh`, aggregate audit build, remote gate,
owner attestation, push or PR is claimed by this lane.
Before release, the final branch head still owes all of the following:

- one globally exclusive full `./scripts/check.sh` run;
- fresh exact-head Codex theorem review and Fable 5.1 documentation/surface
  audit after any remediation commit;
- an Infrastructure PR and `/agentic_review` coverage of its exact final SHA;
- raw-green CI, CodeQL and freeze-policy rollups with no queued or in-progress
  duplicate run;
- the `tmverifier-unfreeze` label and repository-owner comment whose complete
  body is `/tmverifier-unfreeze <exact final full SHA>`; and
- an ancestry-preserving merge (not squash), followed by verification that
  stage (a) `d1694e4b8c3e4838fb38d682f4c10d5ffacc6eb8` and stage (b)
  `4ffd71f356e13babde80397186ee176e5455ccc5` remain ancestors of `main`.

This Infrastructure execution result reduces neither lower-bound source
obligation. N1 and N3 remain open and owned by Lane B. First arrival for the
new endpoint and a bound of its full new clock by `GNM.runTime` are also open,
as are every launch/delegation/commit/loop/verdict/acceptance/runtime obligation
listed above. The implementation-stage commit IDs and clean-worktree checks in
`/root/reports/gn-e25c-writer-final.txt` describe stage (b), before the docs-only child.
