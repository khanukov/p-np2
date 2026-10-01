# GN-E2-5d: frozen target and premise record

Frozen before Lean edits, 2026-10-01. Classification: **Infrastructure**.
Exact base: `5aa3f945025de7cb06fe83e4330a13685e15e8d9`.
Authorization: this isolated implementation, two ordered commits, no push/PR,
no full exclusive gate. No superseded GN-E2-4b1 donor commits.

## Data, premises, endpoints

For `r : GNProgram`, `g : SLGate r.inputs.length`, the real path assumes only
`hg : r.program.gates[0]? = some g`. Fix `q := gnFirstRequest r g`, with
`q.vals = r.inputs`, `N := (encodeGN r).length`, `W := (encodeG1 q).length`,
`A := (GNM.initialConfig (gnPoint (encodeGN r))).tape`, and the dependent room
proof **`gnFirstRequest_room hg`**, footprint `N + (W+5) ≤ GNM.tapeLength N`.
No substituted values, execution premise, installer record, assumed safety or
delegation, runtime witness, advice, or proof-to-runtime extraction is allowed.
`res : Bool` and `hs : q.spec = some res` index successful correctness only.
Canonicality, source execution/safety and delegation must be derived from the
existing `gnFirstRequest_canonical`, `g1CS_gate_done_trace_safe`, and
`gn_g1_gate_done_delegates` chain.

Freeze these public proposition targets (all receive named full-proposition
`check_<name>` wrappers and direct owner/wrapper roots in both audits):

- `gnTransition_launch_rows`, `gnTransition_launch_decision`: finite reverse
  buffer rows; entry preserves bit and moves left; decoded `bof` stays at fixed
  `gnEmbed G1M.start`, other decoded frames continue left, malformed windows
  and unused forward buffer states reject. No request/result controls a row.
- `gnCS_launch_onList_exact`: arbitrary `n pre body post`, essential premises
  `∀ f ∈ body, f ≠ .bof` and
  `4*(pre.length+body.length+1) < GNM.tapeLength n`; exact run from
  `requestReady` at `4*(pre.length+body.length+1)` on
  `(pre ++ .bof :: body ++ post).flatMap G1Frame.bits`, in `4*body.length+5`
  steps, to fixed delegated start at `4*pre.length`, entire tape unchanged.
- `gnFirstRequestReady_geometry`: real ready state/head/full concatenated tape
  and room, under `hg`. The appended blank is tape-equivalent, not a launch.
- `gnFirstLaunchSteps_provenance`: `gnFirstRequestLaunchSteps = W+1`,
  `gnFirstLaunchSteps = T+(W+1)`, with
  `T = gnValuesEntrySteps r g + (r.inputs.length*(8*gnValuesTailDistance r g+38)
  + (4*gnValuesTailDistance r g+20))`.
- `gnCS_requestReady_launch_exact`: real `gnFirstRequestReadyConfig r g hg`
  reaches **`gnFirstInstalledConfig r g hg`** after `W+1`, under only `hg`.
- `gnCS_encodeGN_firstLaunch_exact`: real encoded initial reaches that same
  complete configuration at `S := T+(W+1)`, under only `hg`.
- If feasible within the cap, `gnCS_encodeGN_firstOutputDone_exact` at `S+D`
  and `gnCS_encodeGN_firstReturned_exact` at `S+(D+1)`, under only `hg,res,hs`,
  where `D := g1GateDoneSteps q = g1GateResultSteps q+(1+g1OutputKernelSteps q)`.
  Done is exactly `gnShiftConfig GNM N gnEmbed A (g1OutputDoneConfig q res)
  (gnFirstRequest_room hg) (g1OutputDoneConfig_head_lt_gnLocalSpan q res)`;
  intercepted is `gnReturnConfig res` of that same dependent value.
- `gnFirstReturned_structure`: derived from the real initial run, state
  `gnReturnedQ res`, head `N+g1OutputExitHead q`, full output tape
  `frameListTape ((encodeGNFrames r ++ g1OutputFrames q res).flatMap
  G1Frame.bits)` (and its exact overlay equality).
- `gnCS_requestReady_reserved1101_reject_five` and
  `gnCS_requestReady_reserved1101_reject_stable`: actual requestReady run at
  `base+4`, room and physical `1101` window at `base`, rejects in exactly five
  steps at `base` with tape unchanged, then remains rejected for any padding.

## Concrete targets

`GNFirstRequestLaunchProbes` uses the actual `GNEncodingExamples.capProgram`:
`N=84,W=32,T=1300,W+1=33,S=1333`, launched head 84, `gnEmbed G1M.start`.
`literal_cap_firstLaunch` is full configuration equality from real encoded
initial. Successful composition, if achieved: `D=229`, output-done at 1562,
intercepted at 1563/head107/`gnReturnedQ true`, full tape with scratch frames
`[.bof,.tag,.argSep,.argSep,.separator,.data true,.output true,.finish,.blank]`;
cell111=true, GN reserved cell11=false. `literal_cap_firstReturned` pins this
real initial run; `literal_cap_launch_executable` independently kernel-checks
33 steps from `capValuesReady` and one further delegated read.
`literal_first_not_is_undefined` pins the canonical but unspecified first
`notGate 0` example on `[true]`. Extra public fixture theorems also get wrappers
and both direct audit roots.

## Mutation and size freeze

At most **1500 changed Lean LOC (additions + deletions, including tests,
audits, comments, registrations), at most 10 modules**, measured against the
exact base. Intended nine Lean files: owner, writer, one downstream proof
module `TMVerifierExtensions/GateNFirstRequestLaunch`, one examples module,
existing writer surface, new surface, focused audit, aggregate audit, lakefile.
Only frozen edits: finite launch control/requestReady row in
`GateNFixedDelegateRelocation`; obsolete requestReady conjunct and affected
prose in `GateNValuesWriter`. Register modules in lakefile. Preserve all other
frozen bytes, specifically induction/copy/rewind/install bridge, GateOne*,
encodings and generic scanner kernels.

## Scope and validation

An internal `bof` stops early; generic no-internal-bof is essential. Reserved
1101 rejection covers that inspected window, not every corruption. `hg` alone
proves launch, not return: first not/and/or references have no prior results.
Canonicality does not imply defined semantics. First returned true differs
from capProgram's whole-program false. Exact clocks are not first arrival.
Commit, cursor/spent advance, repeated gates, verdict, GN acceptance, composed
runtime adequacy, ContentVerifierBridge and Lane B N1/N3 remain open. There is
no pnp4 bridge or P-vs-NP mainline claim, and no equivalence is inferred from a
one-directional implication.

Stage (a) commits dependency-closed validated bytes/tests/audits/docs with old
pin intentionally failing. Stage (b), a separate child without frozen-byte
changes, pins stage (a)'s exact SHA/subtree and regenerates schema-3 manifest.
Preserve ancestry, no squash/amend. Run changed/new and relevant dependency
targets only through `pnp2-lake lane-b`; record cache provenance, targeted
outputs, freeze failure then success, negative controls and policy tests.
The globally exclusive full gate is explicitly excluded by this task.
If composition cannot fit/prove, retain the complete genuine launch slice and
record its precise blocker; never replace execution by configuration wrappers.

## Implemented evidence (after the target freeze)

The successful composition fits: no fallback endpoint or additional premise
was needed. The owner adds `GNState.launch` and `gnLaunchControl`; the proof
module supplies `gnLaunchScanner` by proving all six reverse-kernel fields.
The generic scan composes `revScanFrames` with `revAnchorStep` at the actual
prefix length, never assuming the scratch base is zero. The ready geometry
removes only a trailing all-false frame. The return theorems compose the real
initial prefix with the already-proved safe evaluator/delegation/interception.
`gnFirstReturned_structure` derives state, head, full concatenated output tape
and the exact dependent overlay from that real run.

All 12 generic public propositions named above and all five public fixtures
are implemented. The extra fixture `literal_reserved_launch_reject k` pins a
literal full-tape rejection run at `5+k`; `literal_cap_firstReturned` includes
both 1562-step output-done and 1563-step intercepted configuration equalities.
The independent kernel probe reads false from the opening bof's first cell
at step 34, enters `gnEmbed ⟨0, g1State .vBof .p1 false⟩`, and stands at head85.
This reflects the unchanged bof code `0001`.

Lean size against the exact base: **777 additions + 12 deletions = 789 changed
lines**, **nine Lean files = eight modules plus lakefile**, including all
registrations, comments, full-proposition wrappers and audits. The new proof
module is 344 lines and the examples module 112. No other frozen file changes.
The only elaboration adjustment is the owner transition's scoped
`backward.eqns.nonrecursive false`: the expanded control exhausted lazy
fine-grained equation generation, while the unchanged base compiled. One
unfolding equation compiles the same rows and preserves existing proof bytes.

Focused audit: **36 direct roots** = 17 new owner/wrapper pairs plus the
revised writer pair; all are also direct roots in `Tests.AxiomsAudit`.
The exact printed dependencies are standard `propext`, `Classical.choice`,
`Quot.sound` (the arithmetic provenance pair uses only `propext`). There are
no new axioms, unchecked proof placeholders, native evaluation, runtime advice,
choose/find selection or assumed execution/delegation fields.

Build provenance: isolated private `.lake` copied with `cp -a --reflink=auto`
from `/root/p-np2/.lake`, whose source checkout is the exact base SHA above.
Lake invalidates changed-source artifacts and rebuilds the affected dependency
closure locally; all Lean invocations use `pnp2-lake lane-b` (two threads,
CPUs 2-3). The successful focused log is
`/root/reports/gn-e25d-logs/build-launch-5.log`. The complete targeted validation
log is `/root/reports/gn-e25d-logs/targeted-final.log`; this is not the exclusive
repository gate. No full gate is run, as explicitly instructed.

Before stage (a), `check_tmverifier_freeze.py` exits 1 naming exactly the two
authorized changed frozen blobs. The negative-control suite's baseline also
fails for that same intentional mismatch, so its successful run belongs after
the stage-(b) repin. Local policy tests already pass. Pin constants, schema and
manifest remain unchanged in stage (a); stage (b) records its exact committed
subtree and rechecks content, negative controls and policy. See the final
commit/evidence record below and `/root/reports/gn-e25d-implementation-result.txt`.

Final stage-(a) targeted validation completed successfully, exit 0, including
both changed owners, all four new modules, the revised writer surface,
`Tests.TMGateNValuesInductionAxioms`, `Tests.TMGateNValuesCopyAxioms`,
`Tests.TMGateNValuesRewindSurfaceTests`,
`Tests.TMGateNFixedDelegateRelocationSurfaceTests`,
`Tests.TMGateNFirstInstallBridgeSurfaceTests`,
`Tests.TMGateOneFiveTagTraceSafetySurfaceTests`, and `Tests.AxiomsAudit`.
The log ends `Build completed successfully.` The old 1300-row real ready
fixture and 136-row two-value kernel fixture were rebuilt unchanged.
All 36 direct focused roots also passed in the aggregate audit. Explicit scope
and surface checks passed, as did `git diff --check`. The frozen subtree has
120 files: 118 unchanged and only the two authorized blob changes.
