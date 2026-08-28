# Plan: closing the TM verifier for canonical asymptotic GapPartialMCSP

**Repository:** `/home/user/p-np2/pnp3`
**Baseline branch:** `claude/audit-hnpbridge-interface-FnO1v` (already
carries the decoder + components bridge)

## 1. Context

The reduction layer in
`pnp3/Magnification/CanonicalAsymptoticDecider.lean` already collapses
the canonical asymptotic NP track to a single typed target: build
`CanonicalAsymptoticVerifierComponents`.  Downstream,
`canonicalAsymptoticData_of_components → AsymptoticFormulaTrackData`
is fully proved with no `sorry` / axioms.

Closing the TM verifier is **multi-thousand-LOC engineering**.  One
Lean session ≈ one leaf blocker, so we decompose into **7
sequential sessions**, each with a standalone theorem and a "0 sorry
/ standard classical axioms only" obligation.

The toolkit already carries the heavyweight theorems:
- `BinaryCounter.incrementProgram_correct` —
  `BinaryCounter.lean:1315`
- `CombineAtOffset.combineAtOffsetCS_run_full` —
  `CombineAtOffset.lean:1037`
- `GateWrappers.circuitEvaluatorCS_run_correct_wf` —
  `GateWrappers.lean:5034`
- `GateWrappers.seqList_timeBound_le_uniform` —
  `GateWrappers.lean:577`

## 2. Architectural decision: Variant B (NP-style)

Replace `CanonicalAsymptoticVerifierComponents.accepts_eq` with the
standard NP formulation:

```lean
accepts_eq : ∀ n (x : Bitstring n),
  decideAsymptotic n x = true ↔
    ∃ w : Bitstring (certificateLength n k),
      Internal.PsubsetPpoly.TM.accepts (M := M) (n := n + certificateLength n k)
        (concatBitstring x w) = true
```

**Rationale:**
- Removes the internal "Phase A scan + Phase B identify" (~600 LOC)
  for enumerate-all-candidates.
- The TM just **verifies** a guessed candidate encoded in `w` — the
  standard OPS19 / CJW20 pattern.
- Non-canonical lengths are handled trivially: the verifier rejects
  every `(x ++ w)` whenever `n ≠ 2·2^m`, without a special search.
- Saves ~30% of LOC across sessions 3–6.

After the structure change, the current `witness` (lines 296–312)
will directly use the existential rewrite instead of `trivialCert`.

## 3. Per-session plan

### Session 1 — `seqList_run_full`
**File:** `pnp3/Complexity/TMVerifier/TuringToolkit/ConstStatePhasedProgram.lean`
**LOC:** ~350
**Building blocks:** `runConfig_seq_succ_*` (lines 414–544),
`seqList` (line 573)
**Deliverable:** a generic `seqList_run_full` with motive parameter
`Configuration → S → Prop`, modelled on `runConfig_seq_succ_P2_*`
(lines 488–544).
**Acceptance:** theorem typechecks; axiom audit ∈
`{propext, Classical.choice, Quot.sound}`.

**W-A infrastructure delivered (2026-08-22):**
`TuringToolkit/ConstStatePhasedProgramSeqRun.lean` now completes the named
two-program configuration-flow theorem `seq_run_full`, ordinary `RunSpec.seq`
closure, and the specialized terminal closure `RunSpec.seqList_singleton`, not
the full list induction promised by this session.  `RunSpec` records the
non-automatic prefix conditions (not reaching the accept phase early and
right-move head safety), arrival at the accept phase at `timeBound`, and a
caller-chosen semantic postcondition.  Phase arrival alone is not TM
acceptance, because it does not assert equality with the accepting local state.
`seq_run_full` starts from
`embedSeqConfig P1 P2 c1`, derives the handoff head bound from the single
`P1.tapeLength ≤ P2.tapeLength` premise, starts P2 at
`liftP1ToP2 P1 P2 (P1.run ...)`, and returns the final configuration as
`embedSeqP2Config P1 P2 (P2.run ...)` together with both postconditions.
`RunSpec.seq` packages that flow as a `RunSpec (seq P1 P2)` whose postcondition
identifies the exact embedded final configuration and preserves both component
postconditions.  Its full P2 `RunSpec` premise is intentionally stronger than
configuration flow alone requires: P2's early-phase avoidance and final phase
arrival are required to prove closure and support later right-nested
induction.  It cannot serve as the singleton base by taking `P2 := idleCS`:
for nonzero `P.timeBound`, `P.tapeLength ≤ idleCS.tapeLength` is false.
`RunSpec.seqList_singleton` instead performs the final handoff directly in the
`seq P idleCS` composite, reaches the composite accept phase, and preserves the
embedded P final tape and head without projecting either into a shorter idle
tape.  The two-piece concrete theorem's second write postcondition is relative
to the P1-to-P2 boundary lift `c2Init`, not directly to the original P1
configuration.  `gateConstCS_seqList_singleton_runSpec` supplies a concrete
compiling singleton `seqList [gateConstCS b d]` surface.
`gateConstCS_seq_run_full` instantiates the theorem on two ordered constant
gate pieces and derives the second gate's destination bound from the first
gate's bound and `d1 ≤ d2`.  These two concrete constant-gate examples live in
`TuringToolkit/ConstStatePhasedProgramSeqRunExamples.lean`; the generic
`RunSpec` interface and composition theorems remain in
`TuringToolkit/ConstStatePhasedProgramSeqRun.lean`.

This W-A increment was **Infrastructure**, not a restricted lower bound and
not P-vs-NP mainline progress.  At that stage, ordinary `RunSpec.seq` plus the
terminal singleton closure formed the induction kernel, while the recursive
theorem assembling it over `seqList` remained open.  It did not close any
verifier-language correctness or runtime obligation.

**W-B non-dependent list layer delivered (2026-08-22):**
`TuringToolkit/ConstStatePhasedProgramSeqListRun.lean` now supplies the light
`seqList` recursion layer, importing only the preceding `SeqRun` module.  The
bridge `liftP1ToSeq_eq_embedSeqConfig_lift` proves that lifting directly into a
composite tail agrees with lifting into its head and embedding, under the
explicit adjacent comparison `Pᵢ.tapeLength n ≤ Pᵢ₊₁.tapeLength n`.
This adjacent hypothesis is essential: embedding through a shorter successor
can erase cells.  The current public API covers adjacent-monotone lists; a
shorter handoff would require a separate no-information-loss premise rather
than an unrestricted-list claim.

`RunSpec.seqList_singleton_exact` identifies the actual terminal boundary-step
configuration.  `RunSpec.seqList_cons` is the semantic recursion interface: it
preserves the exact final composite configuration together with the head
program's standalone postcondition and the already-assembled tail
postcondition.  The separate non-dependent control-flow theorem
`RunSpec.seqList_of_forall` handles every nonempty list using ordinary
`List.Forall` and `List.Chain' (ReadyStep ready)` and deliberately concludes
with postcondition `True`.  It guarantees whole-list `prefixSafe` and arrival
at the declared accept phase.  It does **not** collect heterogeneously typed
intermediate configurations, and it does not assert TM acceptance: phase
arrival remains distinct from equality with the accepting local state.

`TuringToolkit/ConstStatePhasedProgramSeqListRunExamples.lean` proves an actual
two-constant-gate `seqList` `RunSpec` with exact final configuration and both
gate-write facts; this exercises the bridge and exact singleton.  A three-gate
probe applies the cons theorem twice under only `d₁ ≤ d₂` and `d₂ ≤ d₃`,
pinning the recursive scope without claiming arbitrary unordered gates.
The arbitrary control-flow driver is now concretely inhabited for every
nonempty homogeneous list `P :: List.replicate copies P`, where
`P = gateConstCS b d`: its explicit readiness predicate and every
`List.Forall`/`List.Chain' ReadyStep` obligation are proved from the constant
gate run facts.  This remains a phase-only result.  An arbitrary-length
semantic accumulator (including the proposed `zeroExtTape`-style tape
description) remains open.
The modules, public signatures, and headline axiom dependencies are registered
in `lakefile.lean`, `Tests/TMSeqRunSurfaceTests.lean`, and
`Tests/AxiomsAudit.lean`.

This remains **Infrastructure**, not a restricted lower bound and not P-vs-NP
mainline progress.  It closes the non-dependent, adjacent-monotone list
control-flow layer, but it does not prove verifier-language correctness,
acceptance, or a polynomial runtime bound for the eventual verifier.

**W-C actual-input conditional-accept capstone delivered (2026-08-23):**
`TuringToolkit/ConstStatePhasedProgramInitialConfig.lean` proves the
unconditional full-configuration identity
`initialConfig_seq_eq_embedSeqConfig_initialConfig`.  The equality covers the
dependent phase/local state, head, and every cell of the composite tape; it
has no hypotheses and no input cast.

`TuringToolkit/ConstStatePhasedProgramConditionalAcceptExamples.lean` defines
`gateConstThenAcceptIfCS b d := seq (gateConstCS b d) (acceptIfCellCS d)`.
The operands both have standalone clock `2*d+3`, so ordinary `RunSpec.seq`
applies with equal tape lengths and no padding.  From the composite machine's
actual `initialConfig`, the dependency-closed `RunSpec` proves that the exact
final local state is `(b,b)`, the head returns to its initial position, and
the complete final tape is the initial tape with cell `d` set to `b`.  Hence
`TM.accepts ... = b` for every input length, input, bit, and offset, covering
both the accepting and rejecting executions.

This W-C increment is **Infrastructure**, not a restricted lower bound and
not P-vs-NP mainline progress.  It constructs no content verifier and proves
no runtime bound for one.  Generic padding and the discipline needed to rule
out advice through arbitrary functional clocks remain explicitly open; this
increment adds neither a padding constructor nor a free clock argument.

**T1a fixed-control true uniform seek delivered (2026-08-23):**
`TuringToolkit/TrueUniformSeekEncoding.lean` defines the canonical four-bit
frame ABI and proves the encoder/decoder round trip.
`TuringToolkit/TrueUniformSeek.lean` defines one closed finite-control
`ConstStatePhasedProgram` with the public exact clock
`128 * (N + 1)^2 + 128`.  `TuringToolkit/TrueUniformSeekValidation.lean`
proves genuine `TM.runConfig` traces for the four-bit forward macrostep,
canonical grammar validation, and the exact rewind to the left anchor.  The
exact finite-time theorem `t1CS_validate_rewind_encoded_exact` reaches the
`startMutation` handoff while preserving the initial tape.  T1b-A subsequently
makes that handoff active, so the former T1a full-clock idle-handoff theorem is
intentionally superseded rather than retained with a false conclusion.

This increment is **Infrastructure**, not a restricted lower bound and not
P-vs-NP mainline progress.

**T1b-A fixed destructive-seek opening delivered (2026-08-23):**
`TuringToolkit/TrueUniformSeek.lean` extends the same zero-parameter finite
control with a single Boolean latch and machine-created `spent`/`cursor`
markers.  The ABI, public quadratic clock, and absence of runtime `Nat`, width,
offset, or index fields are unchanged.  Small transition-table lemmas feed the
generic `ConstStatePhasedStepBridge`; mutation proofs do not unfold the full
control table inside `TM.stepConfig`.

`TuringToolkit/TrueUniformSeekMutation.lean` proves genuine atomic execution
for leaving `startMutation`, probing data/OOB, installing and restoring cursor
frames, marking one unary index frame as `spent`, and finding the next index or
success anchor.  The capstones prove exact first-cursor installation from both
the mutation boundary and the real initial configuration, and prove that an
empty data region reaches the OOB boundary in exactly `4 * index + 12` steps
from the mutation boundary.  Concrete index-zero, nonzero-index, and
empty-data runs instantiate the public theorems.  T1c-1 subsequently makes
the OOB boundary active, so the former full-public-clock empty-data theorem is
intentionally superseded rather than retained with a false conclusion; the
exact finite-prefix form is what remains.

This T1b-A increment remains **Infrastructure**.  It does not prove the
iterated `j → j+1` mutation invariant, successful runtime-index lookup,
restoration of all temporary markers, output writing, malformed-input closure,
or acceptance.  Those are explicit T1b-B/T1c obligations.  The modules and
their public headline results are covered by concrete examples, a compile-time
surface test, and the axiom audit.

**T1b-B one-iteration loop delivered (2026-08-23):**
`TuringToolkit/TrueUniformSeekMutationLoop.lean` defines the exact canonical
loop configuration `t1MutationConfig r j`: `index^(k-j)`, `spent^j`, one cursor
at data slot `j`, and — under the executed bound `j ≤ k` — head immediately
before that cursor.  The constructor
carries an explicit Boolean latch; the execution capstones identify it with
`r.data[j]` through their `getElem?` hypotheses.
The genuine theorem `t1CS_loop_iteration_exact` executes one full on-tape unary
decrement and cursor move in exactly `16*j+37` steps, producing the complete
canonical `j+1` configuration.  `t1CS_loop_oob_exact` proves the exact companion
path when no next data cell exists: after `16*j+32` steps the data field is
cursor-free and restored, while the consumed index markers remain explicitly
`spent`, and control is at the OOB boundary.

This slice is **Infrastructure**.  It does not yet iterate the one-step theorem
over all unary index units or prove the final `getElem?` success/OOB split.
It also proves no consumed-index-field repair, output write, malformed-input
closure, or acceptance; the loop driver is T1b-C below, while the remaining
repair/output/acceptance work is owned by T1c.

**T1b-C loop driver delivered (2026-08-23):**
`TuringToolkit/TrueUniformSeekMutationDriver.lean` sums the variable loop cost
as `t1LoopSteps m = 8*m^2 + 29*m` and proves by genuine `TM.runConfig`
induction that the installed cursor reaches every canonical `Σ(m)` allowed by
the unary index and data bounds.  The success tail crosses the fully spent
index field and reaches `successStart`; the OOB branches cover both empty and
nonempty data.  Exact case theorems start from the real initial
configuration and are keyed by `r.data[r.index]? = some v` or `none`.
`t1CS_decideTotal_le_clock` proves every case fits the fixed public quadratic
clock.  The four public `T1M.run` theorems that padded the decision prefix with
idle success/OOB boundary behavior were removed by T1c-1 below, which activated
both boundaries; the exact finite-prefix `runConfig` picture is what remains.

This remains **Infrastructure**: `successStart` and `oobStart` are semantic
boundaries, not accept/reject states.  No temporary-marker repair, output write,
malformed-input closure, or acceptance equivalence is claimed; those are T1c
obligations.

**T1c-1 terminal control activated (2026-08-23):**
The same zero-parameter `t1CS` now contains fixed output traversal, cursor/data
restoration setup, right-to-left `spent → index` repair, and final dispatch to
the literal `t1AcceptState` or `t1RejectState` with scratch/latch cleared.  The
ABI, one-phase architecture, and public quadratic clock are unchanged.
`TrueUniformSeekTerminalControl.lean` proves genuine mode-level execution
macros for entering both arms, writing a data/output frame, scanning/rewriting
repair frames, and dispatching into the stable accept/reject sinks.

Activating `successStart` and `oobStart` necessarily removes the former
full-clock theorems that padded at those idle boundaries; all exact finite-prefix
validation, seek-loop, and real-initialConfig decision theorems remain.  This
slice is **Infrastructure** and does not yet compose the terminal macros over a
whole canonical tape, prove complete restoration, pad through the final sinks,
or establish `TM.accepts`/output correctness.  Those are T1c-2/T1c-3.

**T1c-2 terminal execution delivered (2026-08-23):**
`TuringToolkit/TrueUniformSeekTerminal.lean` composes the terminal macros over
whole canonical tapes.  On success it restores the cursor to the selected data
bit, writes that bit into the output frame, repairs every `spent` marker to an
`index`, and reaches the literal accept state at head `0`.  The final tape is
obtained by overwriting only `t1OutputPosition r` with the selected bit
(possibly a no-op).  On both nonempty
and empty OOB paths it repairs every consumed marker, preserves data and
`output false`, and reaches the literal reject state at head `0`; the final tape
is bit-for-bit the initial tape.  Exact terminal clocks and pointwise tape
conservation theorems are surfaced and axiom-audited.

This is still **Infrastructure**.  Composition from the real initial
configuration through the terminal pass, final public-clock padding, and the
`TM.accepts`/output semantic equivalence are deliberately deferred to T1c-3.

**T1c-3 canonical semantics delivered (2026-08-24):**
`TuringToolkit/TrueUniformSeekSemantics.lean` composes the exact decision and
terminal prefixes from the real `initialConfig`, proves the total cost fits the
unchanged fixed quadratic clock, and pads only in literal accept/reject sinks.
For every canonical request `r`, the full machine satisfies
`t1CS_accepts_eq_isSome`: `TM.accepts` is exactly
`(r.data[r.index]?).isSome`.  Thus an in-range selected `false` bit is still a
structurally successful accepting read whose output cell is `false`; OOB rejects.
On success the full run changes only `t1OutputPosition r` and writes the
selected bit there; on rejection the final tape is bit-for-bit the input tape;
the final head is `0` in all cases.

This closes the canonical fixed-machine runtime-addressing semantics as
**Infrastructure**.  Theorems remain scoped to `encodeT1 r`; arbitrary raw
trailing input retains the documented `T1Physical`/blank-suffix caveat.  No
universal gate interpreter or content verifier is claimed by this result.

**Generic four-bit frame scanner delivered (2026-08-24):**
`FrameScannerCodec.lean` and `FrameScannerKernel.lean` factor out an executable
four-cell macrostep and exact multi-frame `TM.runConfig` induction, reproducing
T1's execution shape in a kernel generic over the frame alphabet, finite
control, mode table and carried context.  The one-frame macrostep preserves an
arbitrary physical tape; the multi-frame induction preserves its canonical
list-backed tape with arbitrary frame prefix/suffix and exposes exact
state/head/tape projections.  Transition obligations are concrete tuple facts
consumed by the existing generic step bridge, not a correctness field that
repackages a semantic theorem.  `FrameScannerProbe.lean` supplies a genuinely
non-T1 codec/program execution, while `FrameScannerT1.lean` instantiates the
kernel at the existing T1 machine and pins named regression theorems.

This is **Infrastructure** for the fixed unary gate interpreter.  It proves no
gate semantics, multi-gate evaluation, verifier correctness or lower bound.

**T2a unary one-gate interpreter foundation delivered (2026-08-27):**
Six modules under `TuringToolkit/` build the dependency-closed foundation of
the fixed one-gate interpreter on top of the generic frame-scanner kernel.

* `GateOneEncoding.lean` — a **fresh** four-bit unary ABI, independent of the
  width-parameterised `SLGate.encode`.  `blank` stays `0000`; `argSep` is
  `1011`; `spent`/`cursor` are the two machine-internal markers the planned
  destructive read needs; `1101`–`1111` are reserved and rejected.  The
  canonical word is
  `bof · tag^g · argSep · index^arg1 · argSep · index^arg2 · separator ·
  data(vals) · output(false) · finish`, with the unary tag
  `input 1, const 2, not 3, and 4, or 5` and an explicit arity convention
  (`arg2 = 0` for arity-1 tags, `arg1 ≤ 1` for `const`).  `decodeG1Tape?_iff`
  characterises the pure parser exactly: a bit list decodes to `r` iff it is
  literally `encodeG1 r` with `r` canonical, so wrong tag counts, wrong
  arity/unused fields, missing delimiters, reserved codes and malformed
  canonical words are rejected.  `encodeG1_injective`, the pure `g1FrameCodec`,
  exact length/output-cell theorems, and literal ABI pins are provided.
* `GateOneSemantics.lean` — the pure `G1Request.spec : Option Bool`, operand
  selection by partial list indexing (`vals[i]?`), with branch simplification,
  out-of-range/non-canonical `none`, and concrete successful-`false` examples.
  `G1Request.WellFormed` adds operand bounds to the unused-field convention;
  `spec_isSome_iff` proves that this, not canonicity alone, is the semantic domain.
* `GateOneControl.lean` — one zero-parameter `ConstStatePhasedProgram`
  `g1CS` with the closed clock `g1Clock N = 512 * (N + 1) ^ 2 + 512`.  The
  finite state carries a mode, a frame position, a three-cell frame buffer and
  a three-Boolean context; no `Nat`, index, width, offset, data length or
  request-dependent value occurs in it.  Everything below `g1Transition` is a
  standalone tuple lemma.

  The forward modes **remember the unary tag count**, and through it the tag
  kind: `vTag0 … vTag5` count the tag run (`vTag0` rejects `argSep`, `vTag5`
  rejects a sixth `tag`), and the `argSep` leaving `vTagk` selects that tag's
  operand convention — `vArg1Unary` for `input`/`not`, `vConst0`/`vConst1`
  for `const` (a second constant `index` rejects), `vArg1Binary` for
  `and`/`or`; an arity-1 tag then lands in `vArg2Zero`, which rejects any
  operand-2 `index`, and an arity-2 tag in `vArg2Any`, which loops.  This is
  exactly `G1Request.Canonical`, and it is *proved* to be:

  - `g1Automaton_accepts_iff_decode` — for every frame word `fs`, the forward
    control run of `fs ++ [.blank]` reaches `rewindStart` **iff**
    `decodeG1FrameList? fs` succeeds.  Machine language = pure parser
    language, on explicit canonical frame words closed by one trailing blank
    frame.  (Nothing is claimed about arbitrary padded physical tapes.)
  - `g1CanonicalEncoderAutomatonTrace_iff` — its encoder specialisation:
    `advanceList .vBof (encodeG1Frames r ++ [.blank]) = .rewindStart ↔
    r.Canonical`.
  - `g1AdvanceList_encode_reject` and the named witnesses
    `g1_reject_tagRun_zero`, `g1_reject_tagRun_six`,
    `g1_reject_const_arg1_ge_two`, `g1_reject_unusedField_{input,not,const}`
    — every noncanonical class ends in the literal `reject` sink.
* `GateOneScanner.lean` — `g1CS` as a genuine instance of the generic
  `FrameScanner` kernel.  The T1 scanner proof stack is not duplicated: the
  five obligations are the tuple lemmas above, and the multi-frame scan is the
  generic `scanFrames` instantiated at G1.  `g1FrameScanner_advanceList` and
  `g1FrameScanner_validPath` identify the kernel's frame language with the
  control's, and `g1FrameScanner_frameLanguage_iff_decode` transfers the pure
  parser correspondence to the kernel's `advanceList` fold.
* `GateOneValidation.lean` — the executable capstone.  From the real
  `G1M.initialConfig (g1Point (encodeG1 r))` of a **canonical** `r`, exactly
  `g1ReadBHandoffSteps r = 2 * (encodeG1 r).length + 9` genuine
  `TM.runConfig` steps perform read-only canonical grammar validation and
  rewind, ending at head `0` in the local `readBStart` handoff with frame
  position `p0`, all three frame-buffer cells `false`, context `g1Ctx0`, and
  the tape bit-for-bit the initial tape.  Exact validation
  (`g1CS_validate_encoded_exact`) and exact reverse scan
  (`g1CS_rewind_tail`) are separate public components.

  The `r.Canonical` hypothesis is matched by a proved converse:
  `g1CS_validate_noncanonical_reject_exact` runs the *same* fixed
  `(encodeG1 r).length + 4`-step validation prefix from the same real initial
  configuration on a noncanonical request and lands in the literal
  `g1RejectState` with the tape exactly unchanged, and
  `g1CS_noncanonical_ne_readB` records that the validation-prefix endpoint is
  not a pass-B handoff.  The head is deliberately not pinned in the rejection
  statement: it stops on the offending frame.
* `GateOneExamples.lean` — named examples: round trip, every listed rejection,
  the pure semantics, the capstone at every gate tag, and concrete
  *machine-level* rejections of every noncanonical class — the two wrong
  tag-count classes at frame-word level (`automaton_reject_zero_tags`,
  `automaton_reject_six_tags`; wrong tag counts are not expressible as
  `encodeG1Frames r`, since `G1Tag.units` is always `1 … 5`), and
  `const` with `arg1 = 2` plus `input`/`not`/`const` with `arg2 > 0` as exact
  TM runs (`machine_reject_*`, `machine_no_handoff_*`).

This slice is **Infrastructure**.  It is not a universal gate interpreter, not
a multi-gate evaluator, not a content verifier and not a lower bound.  The
following are **explicitly deferred** and are not claimed anywhere:

* **operand execution** — the pass-B/pass-A destructive index reads that
  resolve `arg1`/`arg2` against the data region (the *non-destructive*
  `arg2 = 0` pass-B read is delivered by T2b-2 below; the destructive walk is
  still deferred);
* **combine, write and repair** — computing the gate value, writing it into
  the `output` cell, and the `spent ↦ index` restoration pass;
* **full run and acceptance** — `TM.run`, `TM.accepts`, and any full-clock
  theorem.  `readBStart` was idle in the T2a slice and is activated by T2b-1
  below, so only the exact prefix statement above is proved;
  `g1ReadBHandoffSteps ≤ g1Clock` records solely that the proved prefix fits
  the public clock;
* **the `SLGate` bridge** — the pure `G1Request.ofGate` / `spec_ofGate`
  relation to `SLGate.compute`;
* **the multi-gate evaluator** — `SLProgram.eval`-style iteration;
* **the verifier** — no `CanonicalAsymptoticVerifierComponents` obligation is
  reduced, and no runtime-polynomial verifier claim is made.

Every execution theorem is scoped to `encodeG1 r`; no execution claim is made
for physically padded tapes.  The rejection theorems are likewise scoped: they
are about the canonical encoding of a *noncanonical request*, not about an
arbitrary padded or malformed physical tape.  The head, state and tape scope is
explicit: the canonical capstone pins head, state *and* tape, while the
rejection statement pins state and tape but deliberately not the head.

**T2b-1 pass-B control table and routing delivered (2026-08-25):**

`readBStart` is no longer an idle row of the table.  It is now a genuine
*forward frame-reading mode* of the same fixed zero-parameter `g1CS`, in the
same single phase, under the **unchanged** clock
`g1Clock N = 512 * (N + 1) ^ 2 + 512`.  No `Nat`, index, width, offset, data
length or request value was added to `G1State`: the new state is twenty extra
`G1Mode` constructors plus the existing three-Boolean `G1Ctx`, whose `vB` field
is the one place a resolved Boolean is stored.

The continuity constraint is respected literally.  At the T2a handoff the
context is `g1Ctx0` and no gate tag is retained anywhere, so the control
**physically rescans** `bof · tag^units · argSep` from the start of the word and
re-derives the routing from the tape.  The tag appears in the T2b-1 statements
only as a fact about `r`, never as a hypothesis about the machine's state and
never as a parameter.

* `GateOneControl.lean` — the table.  Twenty new `G1Mode` constructors, the
  five handoff states (`readAStart`, `combineStart`, `readAResetStart`,
  `bRoundStart`, `bOOB`), the `vB` writer `G1Ctx.withVB`, and transition tuple
  lemmas for the two stationary dispatch rows (`g1Transition_constLit`,
  `g1Transition_store`), the four idle handoffs and the stable `bOOB` sink.
* `GateOneRouting.lean` — the frame level.  `g1RouteMode` is the mode the
  `argSep` closing the rescanned tag run selects; `g1_tagRescan_advance` and
  `g1_tagRescan_validPath` fold and validate the rescan for each of the five
  tags.  Five route prefixes of the canonical word are defined —
  `g1TagRouteFrames` (`bof · tag^units · argSep`), `g1FieldRouteFrames`
  (`… · index^arg1 · argSep`, which is also the `const` literal route), the
  two probe extensions `g1ReadBRouteFrames`/`g1ReadBOOBFrames`, and (added by
  T2b-2 below, **removed** by T2b-3a-1) `g1RoundRouteFrames`, the route up to
  the deferred
  positive-index boundary — each with a split lemma saying the prefix followed
  by the rest of the word is literally `encodeG1Frames r ++ [.blank]`.  No
  producer annotation, no scratch region, no marker.

This layer is **table- and frame-level only**, and it is **Infrastructure**.
Nothing in it is a `TM.runConfig` statement: the exact executions from the real
`G1M.initialConfig (g1Point (encodeG1 r))` — the per-tag route capstones, the
`const` literal store, the zero-index operand-2 read and its out-of-range
boundary — are the T2b-2 layer below and are claimed nowhere here.  Also
claimed nowhere in T2b-1:

* **the destructive index walk** — for `arg2 > 0` this table/routing layer
  sends the operand walk to the `bRoundStart` bridge
  (`g1_bScan_index_bridge`) and runs no machine step beyond that boundary.  The
  T2b-2 slice below activates the bridge and executes exactly **one**
  `index ↦ spent` round; general runtime-index addressing is claimed nowhere.
  (**Superseded by T2b-3a-1, 2026-08-28**: that row is re-pointed to `bInsSeek`
  and `g1_bScan_index_bridge` is renamed `g1_bScan_index_install`.)
* **pass A, combine, write, repair, acceptance** — `readAStart`,
  `combineStart` and `readAResetStart` are idle rows; there is still no
  `TM.run`, `TM.accepts`, output-write, `spec`-correctness or full-clock
  theorem.  (**Superseded by Repair-2a, 2026-08-28**, for `readAResetStart`
  only: it is now the one-step bridge into the repair sweep.  `readAStart` and
  `combineStart` are still idle rows, and pass A, combine, the output write,
  `TM.accepts` and a full clock are still absent.)

Structural note: `G1ForwardMode` now holds of the pass-B modes, and the old
`g1Advance_range` ("forward, `rewindStart` or `reject`") was generalised to
"forward, `rewindStart` or `G1Stuck`", where a stuck mode completes every frame
into `reject` and is not `rewindStart`.  The four dispatch modes, the five
handoffs and the `reject` sink are stuck; `rewind` and `accept` also satisfy the
predicate but are unreachable from `g1Advance`.  Thus the T2a
validation-grammar proofs are unaffected: they are the same theorems with the
same statements and the same step arithmetic.

**T2b-2 pass-B execution delivered (2026-08-27):**

The T2b-1 table and its frame-level routing become genuine `TM.runConfig`
statements.  The six arrival capstones of `GateOneReadB.lean` start from the
**real** initial configuration `G1M.initialConfig (g1Point (encodeG1 r))` of
the same one fixed zero-parameter machine, compose the exact T2a validation/rewind
prefix `g1ReadBHandoffSteps r = 2 * (encodeG1 r).length + 9`, and then run the
`readBStart` handoff for a further exact, literal number of steps.  No
transition table is unfolded: the single composition lemma `g1CS_readB_scan`
glues the T2a prefix to the *generic* `FrameScanner.scanFrames`, and the two
stationary dispatch rows come from the standalone tuple lemmas
`g1Transition_constLit`/`g1Transition_store`.  No T1 theorem is transported and
no machine, state field, clock or `G1Ctx` field is added or changed.

The reusable local adapters quantify over arbitrary aligned tapes.  The stable
handoff theorems also allow arbitrary post-boundary `+ k`/`+ m` budgets; those
padding budgets are not claimed to fit the public clock.  Only the named
initial-configuration arrival prefixes have the clock bounds listed below.

**Implication direction.**  Each capstone is an *equation* read left to right:
running the fixed machine from its real initial configuration for exactly this
many steps **produces** this configuration.  Nothing is assumed about where the
machine already is, and no theorem concludes something about the machine from a
hypothesis about the machine.

**Hypotheses, and why none of them is advice.**  Every capstone assumes
`r.Canonical` (matched by T2a's proved converse
`g1CS_validate_noncanonical_reject_exact`), a tag fact about the encoded request
`r`, and — where a Boolean is resolved — a *pure selector equation on that same
`r`*: `r.spec = some b` for `const` (which by `g1_const_fields_of_spec`
determines the encoded `index^arg1` run the machine physically decodes), and
`r.vals[r.arg2]? = some b` / `= none` with `r.arg2 = 0` for the operand-2 read.
The tag is *not* carried across the T2a rewind: at the handoff the context is
`g1Ctx0` and the route is re-derived by physically re-reading
`bof · tag^units · argSep` off the tape.  No value, cell index, cursor or target
is supplied to the machine, and `encodeG1` gains no annotation.

Six historical exact endpoints (five remain live after T2b-3a-1), each pinning
head, state **and** tape (`n` abbreviates
`(encodeG1 r).length`, `u` abbreviates `r.tag.units`):

| hypotheses on `r` | steps | endpoint state | head |
|---|---|---|---|
| `Canonical`, `tag ∈ {input, not}` | `g1ReadARouteSteps r = 2n+9 + 4*(u+2)` | `readAStart`, `g1Ctx0` | `4*(u+2)` |
| `Canonical`, `tag = const`, `spec = some b` | `g1ConstRouteSteps r = 2n+9 + 4*(u+arg1+3) + 1` | `combineStart`, `vB = b` | `4*(u+arg1+3)` |
| `Canonical`, `tag ∈ {and, or}` | `g1FieldRouteSteps r = 2n+9 + 4*(u+arg1+3)` | `bScan`, `g1Ctx0` | `4*(u+arg1+3)` |
| `Canonical`, `tag ∈ {and, or}`, `arg2 = 0`, `vals[arg2]? = some b` | `g1ReadBSteps r = 2n+9 + 4*(u+arg1+5) + 1` | `readAResetStart`, `vB = b` | `4*(u+arg1+5)` |
| `Canonical`, `tag ∈ {and, or}`, `arg2 = 0`, `vals[arg2]? = none` | `g1ReadBOOBSteps r = 2n+9 + 4*(u+arg1+5)` | `bOOB`, `g1Ctx0` (stable) | `4*(u+arg1+5)` |
| `Canonical`, `tag ∈ {and, or}`, `arg2 = k+1` | `g1RoundRouteSteps r = 2n+9 + 4*(u+arg1+4)` | `bRoundStart` bridge, `g1Ctx0` | `4*(u+arg1+4)` |

**The sixth row was removed by T2b-3a-1 (2026-08-28)** together with
`g1RoundRouteSteps`: the re-pointed table no longer reaches `bRoundStart`.  Its
replacement is `g1CS_readB_install_scan_exact` at
`g1InstallScanSteps r = 2n+9 + 4*(u+arg1+arg2+4)`, endpoint `bProbe2`, head
`4*(u+arg1+arg2+4)`.

For `and`/`or`, `Canonical` is automatic; it is retained to compose uniformly
with the T2a initial prefix.

In **every** row the tape is bit-for-bit the initial tape: the whole pass-B
rescan is read-only, so no `spent`/`cursor` marker is written and no data cursor
has to be restored.  The `input`/`not` head is the first cell of the operand-1
field and the binary field head is the first cell of the operand-2 field — in
both cases the cell of the `argSep`/`separator` closing that field when the
field is empty — so the deferred passes continue from a physically addressed
cell.

**Scope: generic vs. concrete.**  All six endpoints are *generic* in the
request: `r` ranges over all canonical requests with the stated tag, with
arbitrary `arg1`, `arg2` and arbitrary data region.  `GateOneReadBExamples.lean`
instantiates them at concrete requests (heads `12`/`20` for `input`/`not`, both
`const` literals, `true`/`false` operand-2 reads, the empty-data boundary, the
frame-level bridge boundary) with literal step counts, purely as an audit surface.  Every
step count is bounded by the **unchanged** clock
`g1Clock N = 512 * (N + 1) ^ 2 + 512` through `g1_readB_steps_le_clock`; the
clock is neither widened nor restated, and these are budget facts about the
proved prefixes only, **not** a full-clock theorem.

**Both stopping points are boundaries, not verdicts.**  `bOOB` records that the
operand index selects nothing: it is stable for every further budget
(`g1CS_readB_zero_oob_stable`), it stores nothing in `vB`, and it is a different
state from both the success handoff (`g1CS_readB_zero_oob_ne_success`) and the
reject sink (`g1CS_readB_oob_ne_reject`); no acceptance or rejection semantics
is attached to it.  At the T2b-2 slice, `bRoundStart` was the proved bridge
boundary and no theorem ran it further; the first-round slice below activates
the bridge and executes exactly one round.

**Explicitly deferred, and claimed nowhere:** the **destructive positive-index
walk** (the physically executed operand-2 read is exactly the zero-index one;
for `arg2 > 0` the proved endpoint *is* the `bRoundStart` boundary, so no
general runtime-index addressing beyond the single round below is claimed);
**pass A, combine, output write
and repair** (`readAStart`, `combineStart` and `readAResetStart` are idle rows,
proved idle for every budget by `g1CS_runConfig_readA_idle`,
`g1CS_runConfig_combine_idle`, `g1CS_runConfig_readAReset_idle`, and nothing
consumes the `G1Ctx.vB` value they carry — **superseded by Repair-2a,
2026-08-28**: `g1CS_runConfig_readAReset_idle` is *gone*, replaced by the
executed bridge `g1CS_step_readAReset_bridge`, and the repair sweep behind it is
delivered; the other two rows are still idle and nothing still consumes `vB`);
**acceptance/rejection semantics,
full run and full clock** (no `TM.run`, no `TM.accepts`, no `spec`-correctness
and no full-clock theorem — none could honestly exist while four handoffs are
idle); **padded tapes** (the six initial-config capstones are scoped to the
exact tape `encodeG1 r`; local adapters state arbitrary tapes explicitly, but
no capstone covers a padded tape); and the **`SLGate` bridge, multi-gate evaluator
and verifier obligation**, unchanged from T2a.

Modules: `GateOneReadB.lean` (execution) and `GateOneReadBExamples.lean` (named
examples), both registered in `lakefile.lean`; `GateOneRouting.lean` gains only
the frame-level deferred route `g1RoundRouteFrames` with its split, fold and
valid-path lemmas (all **removed** by T2b-3a-1), and `GateOneControl.lean` only
a docstring correction.
Pinned by `Tests/TMGateOneReadBSurfaceTests.lean` (`#check` plus exact `check_*`
contract wrappers) and audited by `Tests/AxiomsAudit.lean`; the observed cone of
every new declaration is `[propext, Classical.choice, Quot.sound]` or a subset,
with no trusted-compiler reduction axiom.  No existing theorem was weakened,
restated or removed.

This slice is **Infrastructure**, not P-vs-NP mainline progress: it is a
finite-control tape-reading capability, not a gate evaluator, not a content
verifier and not a lower bound.

**Generic reverse frame kernel and four-cell frame write delivered
(2026-08-27):**

The prerequisite named in the T2b read-B design audit — "extract a generic
reverse four-bit scanner with a finite context update, plus generic
`writeFrame`, frame-replacement and rewrite-cycle lemmas" — is delivered in its
reverse-scan and single-frame-write parts.  Four modules under `TuringToolkit/`
add the mutation-side half of the frame kernel; no existing control table,
theorem statement or step count was changed.

* `FrameScannerReverse.lean` — the generic **reverse** kernel.  A
  `ReverseFrameScanner S F Mode Aux` is parameterised by a fixed
  `ConstStatePhasedProgram S`, its phase, a fixed-width `FrameCodec F`, a
  reverse frame table `revAdvance`/`revComplete`, a reverse-mode predicate, a
  `Stop` predicate, and the five aligned state constructors
  `rst3/rst2/rst1/rst0`/`stopState`.  Its proof obligations are **one codec law
  and five concrete transition tuple equalities** — there is no semantic
  correctness field and no "desired run" field, and every execution theorem is
  derived through `ConstStatePhasedStepBridge`, so no instance can hand the
  kernel a finished theorem.  Proved: `revFrameMacrostep` (one frame right to
  left in exactly four `TM.stepConfig`s, head `base + 3 ↦ base - 1`, tape and
  carried context untouched), `revAnchorStep` (the stopping frame: the fourth
  step *stays*, head lands on `base` in `stopState`), `revScanFrames` (exact
  `List` induction over an arbitrary `pre ++ anchor :: scanned ++ suffix`
  layout: exactly `4 * scanned.length` steps, right-to-left fold order, head
  `4 * (pre.length + scanned.length) + 3 ↦ 4 * pre.length + 3`), its
  `_tape`/`_state`/`_head` projections, `revValidPath_const` (homogeneous
  runs), and `revScanToAnchor` (the generic rewind).  The `Phased` namespace
  holds the shared aligned-configuration constructor and the three step
  adapters.
* `FrameScannerWrite.lean` — the generic **four-cell write/replacement** layer.
  `writeFrame4` with its pointwise `writeFrame4_apply`;
  `writeFrame4_frameListTape`, the frame-replacement law on an *arbitrary*
  surrounding frame list, proved for an arbitrary codec with no case split on a
  frame type; `FrameWriter.writeMacrostep`, the exact four-step machine macro
  for a control that writes a supplied 4-bit code while walking across the
  frame (exact head, exit state, carried context and pointwise tape); and
  `FrameWriter.writeFrameOnList`, their composition — four genuine TM steps
  replace one frame of an arbitrary frame list.
* `FrameScannerReverseProbe.lean` — the genericity probe, with **no T1
  import**.  A frame alphabet whose five codewords are `1011`, `1100`, `1101`,
  `1110`, `1111` — every one of them outside the eleven codes `T1Frame` uses —
  two *distinct* reverse modes so the mode argument of `revAdvance` is
  genuinely used, a control state whose carried context is a Boolean *triple*,
  and its own program and clock.  It ends in two concrete executable runs that
  hold for **every** input length `n` with no side hypothesis:
  `revProbeCS_scan_word` (twenty genuine TM steps rewind
  `anchor · cell true · mark · cell false · spent` and stop on the anchor,
  having switched reverse mode at `mark`) and `revProbeCS_write_cell` (four
  genuine TM steps replace one frame, with the exact resulting tape).
* `FrameScannerReverseInstances.lean` — the concrete instances.
  `t1RevScanner` and `g1RevScanner` instantiate the kernel at the *existing*
  T1 and G1 rewinds, discharging every obligation from the existing standalone
  `t1Transition_rewind_*` / `g1Transition_rewind_*` tuple lemmas;
  `t1RevScanner_rewind_tail` and `g1RevScanner_rewind_tail` are the named
  regressions, matching `t1CS_rewind_tail` and `g1CS_rewind_tail` in statement
  shape (the T1 one additionally generalises the latch, which the original
  fixes to `false`).  No control table was touched by *that* slice: in
  particular `bRoundStart` was still idle there, and the G1 clock, grammar and
  step arithmetic are the same literals as before (they are still the same
  literals after T2b-2, which adds rows but changes no clock and no grammar).

`Tests/TMFrameScannerReverseSurfaceTests.lean` pins the public surface and
`Tests/AxiomsAudit.lean` audits the generic capstones, both probe runs and both
regressions; all of them depend only on `propext`, `Classical.choice` and
`Quot.sound`.

This slice is **Infrastructure**.  It proves no gate semantics, no addressing,
no acceptance and no verifier claim, and it does not by itself execute any new
`G1` pass.  The following are **explicitly deferred** and claimed nowhere:

* **the leftward frame writer** — the mirror image of `FrameWriter` that walks
  `p3 … p0` while writing, as T1's `writeCursor`/`outWriteOut` do;
* **the generic 13-step rewrite-cycle composition** matching T1's
  `spent ↦ index` cycle — it needs the leftward writer plus a
  seek-until-marker driver on top of this layer, and is the immediately
  following slice.  Only the exact generic reverse scan and the exact generic
  single-frame write are capstones here;
* **the G1 pass-B destructive index walk** — the kernel is a prerequisite for
  it, not a proof of it.  At that historical slice `bRoundStart` was still
  idle; T2b-2 below later activates it for exactly one round, while the full
  runtime-determined destructive walk remains deferred;
* **non-canonical or physically padded inputs** — local reverse/write
  macrosteps support arbitrary tapes under explicit safety and codeword
  premises; list-scan and frame-replacement capstones use explicit list-backed
  layouts.  No theorem packages either form as a canonical or padded-input
  end-to-end execution.

The first two of those deferrals are discharged by the next slice, below; the
G1 pass-B destructive index walk and the padded-tape question are not.

**Generic leftward writer, seek driver and thirteen-step rewrite cycle
delivered (2026-08-25):**

The mutation half of the frame kernel is completed.  Five modules under
`TuringToolkit/`; no existing control table, theorem statement or step count was
changed, and `bRoundStart` is still idle.

* `FrameScannerWriteLeft.lean` — the generic **leftward** four-cell writer.
  `writeFrame4_descending` identifies the descending write order with
  `writeFrame4`, so the leftward writer inherits the frame-replacement law of
  the rightward one.  A `ReverseFrameWriter S F Aux` carries one codec law and
  four concrete transition tuples; unlike `FrameWriter` its installed frame may
  depend on the carried context (`target : Aux → F`).  `writeMacrostepLeft` is
  the exact four-step macro (head `base + 3 ↦ base - 1`, exact exit state and
  context, tape exactly `writeFrame4`) and `writeFrameOnListLeft` the executable
  replacement on an arbitrary `pre ++ old :: suffix`.
* `FrameScannerSeek.lean` — the generic **seek-until-marker** driver on top of
  `ReverseFrameScanner`.  `revSkipRun` crosses an arbitrary run of skippable
  frames (`4 * skipped.length` steps, mode/tape/context unchanged) and
  `revSeekToMarker` continues into the marker that stops the pass
  (`4 * skipped.length + 4` steps, head on the marker's first cell,
  `stopState (revAdvance mode marker)`), with `revSeekToMarker_head` its head
  projection.  The desired run is *not* a field: the premises are two mode
  facts of the scanner's own table, one frame predicate on the skipped run, one
  table fact about the marker, and head safety.
* `FrameRewriteCycle.lean` — the exact **thirteen-step rewrite cycle**,
  `4 + 4 + 4 + 1`: `revAnchorStep` reads the marker right to left and stops on
  its first cell; `FrameWriter.writeMacrostep` — obtained from the cycle by
  `toWriter`, entered at the *scanner's own* `stopState`, which is what glues
  the halves — installs the replacement codeword; `backWalk` returns the head;
  one explicit hop transition re-enters the reverse scan.  `rewriteCycle` is
  the arbitrary-tape form (head `base + 3 ↦ base - 1`, tape exactly
  `writeFrame4`), `rewriteCycleOnList` the frame-list form
  (`pre ++ marker :: suffix ↦ pre ++ target :: suffix`), and `seekAndRewrite`
  the composition with the seek driver (`4 * skipped.length + 13` steps).  The
  thirteen is derived, not assumed: the structure has no step-count field, no
  desired-run field and no semantic-correctness field.
* `FrameRewriteCycleProbe.lean` — the genericity probe, with **no T1 import**,
  on the non-T1 `RevFrame` alphabet and a new seven-mode control whose carried
  context is a Boolean *pair*.  Four concrete runs, unconditional in `n`:
  `cycProbeCS_rewrite_cycle` (thirteen genuine steps, `spent ↦ cell true`,
  head `11 ↦ 7`, exact resulting tape), `cycProbeCS_seek_rewrite`
  (`8 + 13 = 21` steps, head `19 ↦ 7`), `cycProbeCS_write_left` (the leftward
  writer, head `15 ↦ 11`) and `cycProbeCS_seek_marker` (the seek alone).
* `FrameRewriteCycleInstances.lean` — the concrete instances.
  `t1RepairScanner`/`t1RepairCycle` instantiate the kernel at T1's *existing*
  `repairSeek`/`repairWrite`/`repairBack`/`repairHop` rows, and
  `t1RepairCycle_repair_cycle` re-derives `t1CS_repair_cycle` — same statement,
  `spent ↦ index` in thirteen steps — from the generic composition, with
  `t1RepairCycle_repair_cycle_onList` its frame-list form.  `t1OutWriter`
  instantiates the leftward writer at T1's output write and
  `t1OutWriter_outWriteOut_frame` matches `t1CS_outWriteOut_frame`.  For G1,
  `g1RevScanner_seek_bof` instantiates the seek driver at the *existing* rewind
  modes in the `pre = []` case (`4 * tail.length + 4` steps to head `0` in the
  `readBStart` handoff).

The only change to an existing module is one new standalone tuple lemma,
`t1Transition_repairSeek_p0_bad`, in `TrueUniformSeek.lean`: the fourth outcome
of T1's `repairSeek` frame decision (a frame the pass cannot cross), which the
generic kernel's five-row interface requires and which the existing three
lemmas did not cover.  The table itself is untouched.

**G1 was not executed by that slice.**  `g1CS` had no write, walk-back or hop
rows, so no G1 rewrite cycle existed.  What was provided instead was the exact
core obligation: `G1RewriteCycleObligation` fixed a `FrameRewriteCycle` whose
scanner program was `g1CS`, codec was `g1FrameCodec`, and direction was
`index ↦ spent`, but did not yet fix the scanner-state embedding; the next G1
slice therefore had to prove alignment with the pass-B state before execution.
`machine_eq` recorded that such a cycle's machine was literally `G1M`, and
`rewrite_cycle` derived the thirteen-step run from it by the generic theorem
verbatim.  Those statements were conditional on data that did not exist then;
the T2b-2 slice below adds the rows, strengthens the obligation to pin the exact
aligned-state constructors, and **constructs** it.

`Tests/TMFrameRewriteCycleSurfaceTests.lean` pins the public surface and
`Tests/AxiomsAudit.lean` audits the generic capstones, the four probe runs, the
T1 regressions and both G1 statements; all depend only on `propext`,
`Classical.choice` and `Quot.sound`.

This slice is **Infrastructure**.  Still deferred and claimed nowhere: any
runtime-index addressing, the iteration of the cycle along a runtime-determined
run inside `G1`, the G1 destructive index walk itself, gate semantics,
acceptance, and non-canonical or physically padded tapes.

**T2b-2: one destructive G1 operand-2 index round delivered (2026-08-27):**

The G1 obligation left open by the previous slice is discharged for **one
round**.  Six existing modules gained content and one is new; the `G1Ctx`
triple, the
public clock `g1Clock` and the whole T2a validation grammar are unchanged.

* `GateOneControl.lean` — `G1Mode` gains four constructors, `bWalk`, `bMark`,
  `bBack` and `bHop`, and `g1Transition` gains fourteen rows: the
  `bRoundStart` **bridge** (`.left`, writing back the scanned cell), the four
  reverse-read rows of `bWalk` (`p3 … p0`, the last one *staying* into `bMark`
  when the completed frame is an `index` and stepping left otherwise), the four
  `bMark` rows that write the fixed cells `1 1 0 0` — the codeword of `spent` —
  regardless of what they overwrite, the four tape-preserving `bBack` rows and
  the `bHop` row.  The idle `bRoundStart` row and its lemma
  `g1Transition_bRoundStart_idle` are **gone**: `bRoundStart` moves.  All four
  new modes are non-forward (`G1ForwardMode`) and `G1Stuck`, so `g1Advance` and
  every T2a/T2b-1 grammar and execution theorem is re-derived unchanged against
  the new table, with the same statements and the same step literals.
* `FrameRewriteCycleInstances.lean` — `g1IndexScanner` instantiates the generic
  reverse kernel at `bWalk`/`bMark` and `g1IndexCycle` the generic thirteen-step
  rewrite cycle at `marker = index`, `target = spent`; every obligation is a
  standalone tuple lemma of `GateOneControl`.  `g1CS_index_round` and
  `g1CS_index_round_onList` are the resulting exact thirteen-step runs of `G1M`
  (head `base + 3 ↦ base − 1`, tape `pre ++ index :: suffix ↦
  pre ++ spent :: suffix`, `G1Ctx` preserved).  `G1RewriteCycleObligation` is
  strengthened to pin `seekMode`, `stopMode`, `Reverse`, `Stop`, `revAdvance`,
  all four `rst*` constructors, `stopState`, all eight write/back/hop states and
  the four written cells, and `g1RewriteCycleObligation` **constructs** it by
  `rfl`: the previously uninhabited conditional gap is closed.
* `GateOneReadB.lean` — `g1CS_runConfig_round_idle` is replaced by
  `g1CS_step_round_bridge`: one genuine step, head `h ↦ h − 1`, state
  `bWalk .p3`, tape and context untouched.
* `GateOneIndexRound.lean` (new) — the composition.  `g1CS_round_from_bridge`
  is bridge-plus-round on an arbitrary frame list (`14 = 1 + 13` steps, exact
  tape replacement, head `4p + 4 ↦ 4p − 1`); `g1CS_readB_round_boundary`
  reaches the bridge from the **real** initial configuration for a canonical
  `and`/`or` request with `arg2 = k + 1`; `g1CS_index_first_round` composes the
  two, so `g1IndexRoundSteps r = g1FieldRouteSteps r + 18` genuine steps turn
  the initial tape into the canonical word with the **first** operand-2 `index`
  replaced by `spent`.  `g1IndexRoundSteps_le_clock` keeps it inside the
  unchanged clock, and `g1RoundExample = ⟨.and, 0, 1, [true]⟩` is a concrete
  request where all numbers are literals: after exactly `151` steps the head is
  `27`, the state is `g1WalkState g1Ctx0`, and the tape is the thirteen-frame
  word `bof · tag⁴ · argSep · argSep · spent · separator · data true ·
  output false · finish · blank`.
  (**Superseded by T2b-3a-1, 2026-08-28**: `g1CS_readB_round_boundary`,
  `g1CS_index_first_round`, `g1IndexRoundSteps*`, `g1RoundExample*` and the
  `151`-step projections are **removed**, because the re-pointed forward table
  never reaches `bRoundStart`.  `g1CS_round_from_bridge` survives only as an
  arbitrary-configuration regression, with the literal probe
  `g1CS_round_probe`.)

`Tests/TMGateOneControlSurfaceTests.lean`,
`Tests/TMGateOneReadBSurfaceTests.lean`,
`Tests/TMFrameRewriteCycleSurfaceTests.lean` and `Tests/AxiomsAudit.lean` pin
and audit every new surface; all depend only on `propext`, `Classical.choice`
and `Quot.sound`.

This slice is **Infrastructure**.  It executes **one** round and claims nothing
beyond it.  Explicitly deferred and claimed nowhere: iterating the round along a
runtime-determined operand-2 field, any runtime-index addressing, termination of
the reverse walk, the `arg2 > 0` operand *value* (no read-B success theorem for
that branch), restoring the data region, pass A, combine, output write,
`TM.accepts`, a full-clock theorem, and non-canonical or physically padded
tapes.  After the round the control sits in `bWalk` on the last cell of the
frame preceding the rewritten one, and no theorem runs it further.

**T2b-3a-1: the G1 installation-scan opening, delivered (2026-08-28):**

**Progress classification: Infrastructure.**

The T2b-2 positive-index route is **superseded**.  Repeating the thirteen-step
cycle does not address an operand-2 value: `bWalk` stops on *any* `index`, so
once the operand-2 field empties it crosses the opening `argSep` and consumes
operand-1 units.  The agreed replacement is the paired-marker (cursor) design —
one `spent` per consumed index unit in the operand-2 field, one `cursor` in the
data region.  **This slice delivers only the opening of that design**: the
re-pointed row, the two modes it needs, and the read-only **installation scan**
executed from a real initial configuration.  `G1Ctx`, the `G1State` field list,
`g1Clock` and the whole T2a validation grammar are unchanged, and no new `Nat`,
index, width, offset, length or request field appears anywhere in the machine,
the control or the context.

* `GateOneControl.lean` — `G1Mode` gains exactly **two** constructors,
  `bInsSeek` (the installation scan) and `bProbe2` (its endpoint).  `g1Advance`
  gains **three** rows and **one existing row is re-pointed**:

  ```text
  bScan    + index     ↦ bInsSeek     (re-pointed, was bRoundStart)
  bInsSeek + index     ↦ bInsSeek
  bInsSeek + spent     ↦ bInsSeek
  bInsSeek + separator ↦ bProbe2
  ```

  Both modes are ordinary forward frame-reading modes, so `g1Transition` gains
  **no rows at all** and there are **no new tuple lemmas**: their steps are the
  existing `g1Transition_forward_*` lemmas.  `g1Advance_range`,
  `g1Advance_ne_sink` and every T2a/T2b-1 grammar and execution theorem
  re-derives unchanged, with the same statements and the same step literals.
  The `bScan + data` row stays **absent**: a data frame before the separator is
  still malformed and still rejects.

  **`bProbe2` is an explicit local boundary.**  (**Superseded by T2b-3a-2,
  2026-08-28**: it now has three rows and `g1_bProbe2_stuck` is removed; the
  boundary is `bSeek`.)  It has no outgoing `g1Advance`
  row, so it completes every frame into `reject` and is `G1Stuck`
  (`g1_bProbe2_stuck`); no theorem of this development runs the machine out of
  it.  The **fourteen remaining cursor-walk modes** — `bSeek`, `bDec`, `bFwd`,
  `bTurn`, `bRestoreFalse`/`bRestoreTrue`, `bLatchFalse`/`bLatchTrue`, `bIns`,
  `bExh`, `bRet`, `bTurnFin`, `bFinFalse`/`bFinTrue` — together with their
  `g1Advance` rows, their `g1Transition` rows and tuple lemmas, the kernel
  instances, and every execution of the latch, the cursor install or a walk
  round, are **PR2**.  None of them exists in the tree after this slice.
* `GateOneRouting.lean` — `g1_bScan_index_install` replaces
  `g1_bScan_index_bridge`; `g1_bRoundStart_unreachable` proves by `decide` that
  **no** mode/frame pair completes into `bRoundStart`, and `g1_bProbe2_stuck`
  then pinned the new boundary.  `g1InstallRouteFrames`
  (`= g1FieldRouteFrames r · index^arg2 · separator`) is the fifth route prefix,
  with `g1InstallRouteRest`, its length, its split, its fold (`= .bProbe2`) and
  its valid path.  The bridge route `g1RoundRouteFrames` and its
  split/fold/valid-path lemmas are **removed**: the re-point makes
  `g1RoundRoute_advance` false outright.
* `GateOneInstallScan.lean` (new) — a deliberately narrow module importing
  `GateOneReadB` and nothing else.  It reuses the **existing** forward frame
  scanner `g1FrameScanner`; it instantiates no reverse scanner and no frame
  writer.  `G1InstallSkip` is the class of frames the scan crosses,
  `g1Advance_bInsSeek_of_skip` the table fact, and `g1ValidPath_fix` /
  `g1AdvanceList_fix` the heterogeneous-run forms `GateOneRouting` has only for
  `List.replicate`.  `g1CS_walk_install_scan` is the `4 * (k + 1)`-step macro on
  a caller-supplied `pre ++ skipped ++ separator :: suffix` layout, and
  `g1CS_readB_install_scan_exact` is the re-pointed real-initial-configuration
  route: `g1InstallScanSteps r = g1ReadBHandoffSteps r + 4*(units+arg1+arg2+4)`
  steps land at `bProbe2` on the **first cell after the separator**, context
  still `g1Ctx0`, tape **bit-for-bit the initial tape**.  `_head`, `_tape`,
  `_state` are its projections and `g1InstallScanSteps_le_clock` keeps it inside
  the unchanged clock.
* `GateOneInstallScanExamples.lean` (new) — one literal probe on
  `g1WalkExample = ⟨and, 0, 2, [false, true, true]⟩`: **fifteen** encoded frames
  and `60` input cells; the explicit list-backed layout `g1WalkInitFrames`
  appends one `blank`, so it has **sixteen** frames and `64` bits.  Exactly
  `169 = 2*60 + 9 + 4*10` genuine steps from the real initial configuration
  reach `bProbe2` at head `40`, with the tape equal to that same literal
  sixteen-frame word.
* `GateOneReadB.lean` — the obsolete positive live-route declarations
  `g1RoundRouteSteps`, `g1RoundRouteSteps_le_clock`,
  `g1CS_readB_round_deferred_exact` and `g1CS_readB_round_deferred_state` are
  **removed**; the endpoint table drops from six rows to five.  Everything else
  is retained verbatim, including the zero-phase, OOB-non-reject, unary/const
  tape, stable-`bOOB` and exact-arrival hardening.  `g1CS_step_round_bridge`
  stays, now documented as a caller-supplied regression step.
* `GateOneIndexRound.lean` — reduced to the arbitrary-configuration regression.
  `g1CS_round_from_bridge` (fourteen steps) and its provider chain
  (`g1CS_step_round_bridge`, `g1CS_index_round_onList`,
  `g1RewriteCycleObligation`) are kept, and a literal frame-list probe
  `g1CS_round_probe` (`g1RoundProbeFramesIn/Out`, head `32 → 27`) is added.
  `g1IndexRoundSteps`, `g1IndexRoundSteps_eq`, `g1IndexRoundSteps_le_clock`,
  `g1CS_readB_round_boundary`, `g1CS_index_first_round`, `g1RoundRouteRest`,
  `g1RoundExample*` and the four concrete `151`-step projections are
  **removed** — every one of them asserted a live route the re-pointed table no
  longer has.
* `GateOneReadBExamples.lean` — `readB_bridge_at_index` becomes
  `readB_install_at_index` (`bScan + index ↦ bInsSeek`), and the `arg2 = 1`
  field-route docstring now names the installation scan as its successor.

**The endpoint is reachability, not addressing.**  `g1CS_readB_install_scan_exact`
says the machine gets to the first frame after the separator: a `.data` frame
when the region is nonempty and `.output false` otherwise.  It latches no bit, installs
no cursor, writes no cell and says nothing about which data frame the operand
finally selects.  `bProbe2` has no successful frame row in this slice; an
attempted full-frame read rejects, and no theorem executes that read.
(**Superseded by T2b-3a-2, 2026-08-28** for the last sentence only: the probe is
now active.  The reachability endpoint itself is unchanged.)

Pinned by `Tests/TMGateOneControlSurfaceTests.lean` (the two entry states plus
exact wrappers for the re-pointed row and the complete four-row installation
table), `Tests/TMGateOneRoutingSurfaceTests.lean` (the installation route, with
exact wrappers for its split, fold, valid path, length, and for
`g1_bRoundStart_unreachable` and the then-current `g1_bProbe2_stuck`) and
`Tests/TMGateOneReadBSurfaceTests.lean` (exact
wrappers for the installation exact/head/tape/state endpoints, the literal
`169`-step run with its head, tape and clock, and the retained
arbitrary-configuration round regression).  `Tests/AxiomsAudit.lean` prints the
axioms of every load-bearing new theorem directly; the stale `#1662` roots are
removed in the same change.

This slice is **Infrastructure**.  Explicitly deferred and claimed nowhere, all
of it **PR2** (**T2b-3a-2 below delivers four of these modes; ten remain**):
the fourteen remaining cursor-walk modes and every row and tuple
lemma they need, the
cursor-walk tape invariant `Σ(j)`, the **installation driver** (latch plus
cursor install executed from a real initial configuration), the reverse/write
atomic macro family and its kernel instances, any iteration of the round or loop
clock, addressing, the positive-index operand *value* read, the aggregated
out-of-range branches, repair, pass A, combine, output write, `TM.accepts`,
gate-semantics correctness, a full-clock theorem, and non-canonical or
physically padded tapes.

*Superseded statements in the T2b-1 and T2b-2 entries above:* the sentences
saying the `arg2 > 0` branch hands off to `bRoundStart`, that
`g1RoundRouteFrames`/`g1RoundRouteSteps` is a route prefix of a real run, and
that `g1CS_index_first_round` reaches the first round from `initialConfig`, all
describe the table before this slice.  The current handoff is `bInsSeek`, the
current route prefix is `g1InstallRouteFrames`, and the current
real-initial-config statement for that branch is
`g1CS_readB_install_scan_exact`.  The T2b-2 endpoint table's sixth row
(`bRoundStart` bridge) no longer exists.

**T2b-3a-2: the G1 probe, latch and cursor install, delivered (2026-08-28):**

**Progress classification: Infrastructure.**

The immediate successor of the T2b-3a-1 endpoint `bProbe2`, and nothing else.
`G1Ctx`, the `G1State` field list, `g1Clock` and the whole T2a validation
grammar are unchanged, and no new `Nat`, index, width, offset, length or request
field appears anywhere in the machine, the control or the context.

**The route from the real initial configuration is unchanged.**  It still
reaches exactly `bProbe2`: `g1InstallScanSteps`,
`g1CS_readB_install_scan_exact`, its `_head`/`_tape`/`_state` projections, the
clock bound and the literal `169`-step probe of `GateOneInstallScanExamples` are
byte-for-byte as merged.  **Every** new run below starts from a
**caller-supplied** configuration, tape length and safety bound.  There is no
installation driver: nothing composes the `169`-step capstone with the atoms.

* `GateOneControl.lean` — `G1Mode` gains exactly **four** constructors:
  `bLatchFalse`, `bLatchTrue` (the latch dispatches), `bIns` (the leftward
  cursor writer) and `bSeek` (the reverse-seek entry shape).  `g1Advance` gains
  **three** rows, all out of the now-active probe:

  ```text
  bProbe2 + data false   ↦ bLatchFalse
  bProbe2 + data true    ↦ bLatchTrue
  bProbe2 + output false ↦ bOOB
  ```

  `g1Transition` gains **three** blocks and **five** standalone tuple lemmas —
  `g1Transition_bLatch` and `g1Transition_bIns_p3/p2/p1/p0` — each `rfl` after
  at most one split, none mentioning the request.  `g1LatchMode`, `g1InsState`
  and `g1SeekState` are the new selector and entry states.  `g1Advance_range`,
  `g1Advance_ne_sink` and every T2a/T2b-1 grammar and execution theorem
  re-derives unchanged.  The `bScan + data` row stays **absent**.
* **`bSeek` is the explicit local endpoint.**  The install stops at `.p3`, head
  on the last cell of the frame preceding the cursor.  `bSeek` has no successful
  frame row, so an attempted complete-frame read enters `reject`; it is
  `G1Stuck` (`GateOneRouting.g1_bSeek_stuck`) and no theorem executes that read.
  (**Superseded by PR2b1 below:** `bSeek` now has three live reverse outcomes,
  `g1_bSeek_stuck` is removed, and the boundary is `bExh`.  **PR2b2, 2026-08-28**
  removes that boundary too: `bExh + argSep ↦ bRet` and no mode of the walk is a
  reject boundary any more.)
* `GateOneRouting.lean` — `g1_bProbe2_stuck` is **removed** (it is false now)
  and replaced by `g1_bProbe2_rows`, which pins the three active probe rows, and
  by the then-current `g1_bSeek_stuck`, which pinned the new endpoint.  No route prefix reaches
  past `bProbe2`.
* `GateOneProbeInstall.lean` (new) — imports `FrameScannerWriteLeft` and the
  merged `GateOneInstallScan`, and **reuses** `G1InstallSkip`,
  `g1Advance_bInsSeek_of_skip`, `g1ValidPath_fix`, `g1AdvanceList_fix`,
  `g1CS_walk_install_scan` and the real-initial-config capstones without
  restating them.  It adds one table fact (`g1Advance_bProbe2_data`), one
  `ReverseFrameWriter` instance (`g1CursorWriter`, leftward `_ ↦ cursor`) and
  three exact `TM.runConfig` macros on an **arbitrary** frame list:
  `g1CS_walk_probe_latch` (five steps: four to read `data v`, one to store `v`
  in `G1Ctx.vB`; head `4k ↦ 4k + 3`, tape unchanged),
  `g1CS_walk_probe_oob` (four steps on `output false` into the stable `bOOB`)
  and `g1CS_walk_install_cursor` (four leftward steps, frame `pre.length`
  replaced by `cursor`, head `4k + 3 ↦ 4k - 1`, control in `bSeek`).  The probe
  reuses the existing forward `g1FrameScanner`; only the leftward writer needs a
  new kernel instance, and **no** generic kernel file is touched.
* `GateOneProbeInstallExamples.lean` (new) — four literal probes reusing
  `G1InstallScanExamples.g1WalkExample = ⟨and, 0, 2, [false, true, true]⟩`
  (**fifteen** encoded frames, `60` input cells; the layout `g1WalkInitFrames`
  appends one `blank`, so **sixteen** frames and `64` bits) and its literal
  frame word: `probe_latch_false` (head `40 → 43`, `vB := false`),
  `probe_latch_true` (`44 → 47`, `vB := true`), `probe_oob` (`52 → 56`) and
  `install_cursor` (`43 → 39`, ordinal `10` becomes `cursor`).  One new layout,
  `g1WalkFramesCursor0`.  Each takes `n` and one safety bound from the caller;
  nothing chains them, and nothing chains them to the `169`-step capstone.

Pinned by `Tests/TMGateOneProbeInstallSurfaceTests.lean` (theorem-style exact
wrappers for all three macros and all four literal probes),
`Tests/TMGateOneControlSurfaceTests.lean` (the entry states, the latch selector,
the five tuple lemmas, and exact wrappers for the probe table, for `bSeek`/the
three new modes being stuck, for the still-absent `bScan + data` row, and for
the latch tuple) and `Tests/TMGateOneRoutingSurfaceTests.lean` /
`Tests/TMGateOneReadBSurfaceTests.lean` (`g1_bProbe2_rows` and
the then-current `g1_bSeek_stuck` replacing `g1_bProbe2_stuck`).
`Tests/AxiomsAudit.lean` prints
the axioms of every load-bearing new theorem directly.

Explicitly deferred and claimed nowhere (at the time of that slice; PR2b1 below
delivers six of these ten modes): the ten remaining cursor-walk modes and all
their rows and tuple lemmas, the reverse-seek rows and exact stop endpoints, the
`index ↦ spent` round, the turns, the restore writers, the exhaustion
path, the cursor-walk tape invariant, the **installation driver** (latch plus
cursor install executed from a real initial configuration), any iteration or
loop clock, addressing, the positive-index operand *value* read, the aggregated
out-of-range branches, repair, pass A, combine, output write, `TM.accepts`,
gate-semantics correctness, a full-clock theorem, and non-canonical or
physically padded tapes.

*Superseded statements in the T2b-3a-1 entry above:* the sentences saying that
`bProbe2` "has no outgoing `g1Advance` row", that it "completes every frame into
`reject` and is `G1Stuck` (`g1_bProbe2_stuck`)", that an "attempted full-frame
read rejects", and that the **fourteen** remaining cursor-walk modes are all
PR2, describe the table before this slice.  `bProbe2` now has three rows,
`g1_bProbe2_stuck` is removed, and the remaining deferred modes are **ten**.
The endpoint whose reject-boundary reading still holds is `bSeek`.
(**Superseded by PR2b1, 2026-08-28** for that last sentence only: `bSeek` is now
a live reverse-reading mode with three outcomes, `g1_bSeek_stuck` is removed,
and the boundary is `bExh`.  **PR2b2, 2026-08-28**: `bExh` is live too, so the
walk has no reject boundary left; all sixteen of its modes have rows.)

**PR2b1: one normal round of the G1 cursor walk, delivered (2026-08-28):**

**Progress classification: Infrastructure.**

The successor of the merged reverse-seek entry `bSeek`, and one **normal round**
only.  `G1Ctx`, the `G1State` field list, `g1Clock` and the whole T2a validation
grammar are unchanged, and no new `Nat`, index, width, offset, length or request
field appears anywhere in the machine, the control or the context.

**The route from the real initial configuration is unchanged.**  It still
reaches exactly `bProbe2`: `g1InstallScanSteps`,
`g1CS_readB_install_scan_exact`, its projections, the clock bound and the
literal `169`-step probe of `GateOneInstallScanExamples` are byte-for-byte as
merged, as are `g1CursorWriter`, `g1CS_walk_probe_latch`, `g1CS_walk_probe_oob`,
`g1CS_walk_install_cursor` and their four literal probes.  **Every** new run
below starts from a **caller-supplied** configuration, tape length and safety
bound.  There is no installation driver: nothing composes the `169`-step
capstone with the atoms, and nothing composes two atoms into a round.

* `GateOneControl.lean` — `G1Mode` gains exactly **six** constructors: `bDec`
  (the `index ↦ spent` writer), `bFwd` (the forward scan back to the cursor),
  `bTurn` (the four-step turn), `bRestoreFalse`/`bRestoreTrue` (the two
  cursor-restore writers) and `bExh` (the exhaustion handoff).  `g1Advance`
  gains **four** rows, all out of `bFwd`:

  ```text
  bFwd + spent      ↦ bFwd      bFwd + separator ↦ bFwd
  bFwd + data _     ↦ bFwd      bFwd + cursor    ↦ bTurn
  ```

  `bSeek` becomes a **non-forward, right-to-left** mode: it has no `g1Advance`
  row and is decided at frame position `.p0` inside `g1Transition`, with the
  three exact outcomes `index ↦ bDec` (stay), opening `argSep ↦ bExh` (stay)
  and everything else ↦ `bSeek` (one frame further left).  The literal
  `argSep` stop row enters the exact exhaustion endpoint `bExh`; no trace
  invariant is claimed by this slice.
  `g1Transition` gains **five** blocks and **eighteen** new standalone tuple
  lemmas — `g1Transition_bSeek_p3/p2/p1`, `_p0_index`, `_p0_argSep`, `_p0_other`,
  `g1Transition_bDec_p0…p3`, `g1Transition_bTurn_p0…p3` and
  `g1Transition_bRestore_p0…p3` — each `rfl` after at most one split, none
  mentioning the request.  `g1DecState`, `g1FwdState`, `g1ExhState`,
  `g1RestoreMode` and `g1ExhState_ne_dec` are the new entry states, selector and
  separation fact.  `g1Advance_range`, `g1Advance_ne_sink` and every T2a/T2b
  grammar and execution theorem re-derives unchanged; the `bScan + data` row
  stays **absent**.
* **`bExh` is the explicit local boundary.**  (**Superseded by PR2b2 below,
  2026-08-28**, for the boundary claim only: `bExh` now has the single row
  `bExh + argSep ↦ bRet`, `g1_bExh_stuck` is removed and `g1_bRet_rows`
  replaces it.  The *endpoint* statement is unchanged.)  The seek's `argSep`
  outcome stops
  at `.bExh .p0`, head on the **first cell of the `argSep` that opens the
  operand-2 field**, tape and `G1Ctx` untouched.  `bExh` was, at the time of
  that slice, a forward mode with
  **no successful frame row**, so an attempted complete-frame read entered
  `reject`; it was `G1Stuck` (`GateOneRouting.g1_bExh_stuck`) and no theorem
  executed past it.  The **terminal exhaustion** path — the modes `bRet`,
  `bTurnFin`, `bFinFalse`, `bFinTrue`, their rows and tuple lemmas, the
  `bExh + argSep ↦ bRet` handoff, the run back to the cursor, the terminal turn
  and the two terminal restore writers that hand off to `readAResetStart` with
  no cursor left on the tape — was **PR2b2**, and is delivered below.
* `GateOneRouting.lean` — `g1_bSeek_stuck` is removed because it no longer
  describes an execution boundary.  The frame-table proposition
  `G1Stuck .bSeek` remains true: non-forward `bSeek` has no `g1Advance` row,
  while its execution now uses dedicated reverse `g1Transition` rows.  The old
  boundary root is replaced by `g1_bFwd_rows`, which pins the walk's
  right-running scan, and by
  `g1_bExh_stuck`, which pinned the then-new boundary (**removed again by PR2b2
  below, 2026-08-28**, in favour of `g1_bRet_rows`).  No route prefix reaches
  either.
* `FrameScannerReverse.lean` — the shared phased layer gains the two generic
  tape-preserving leftward primitives `Phased.holdLeft` (one hold-and-move-left
  step) and `Phased.holdWalk4` (the four-step turn from `k + 4` back to `k`).
  They are used concretely by `g1CS_walk_turn`.
* `GateOneWalkKernel.lean` (new) — imports `FrameScannerSeek` and the merged
  `GateOneProbeInstall`, and **reuses** `G1InstallSkip`,
  `g1Advance_bInsSeek_of_skip`, `g1ValidPath_fix`, `g1AdvanceList_fix`,
  `g1CS_walk_install_scan`, `g1CursorWriter` and the probe/latch/install macros
  without restating them.  It adds `G1WalkSkip` with
  `g1Advance_bFwd_of_skip`, the reverse-seek table
  (`g1WalkRevAdvance`/`g1WalkRevComplete`/`G1WalkMode`/`G1WalkStop`), three
  kernel instances — `g1WalkScanner` (`ReverseFrameScanner`), `g1DecWriter` and
  `g1RestoreWriter b` (`FrameWriter`) — and **seven** exact `TM.runConfig`
  macros on an **arbitrary** frame list: `g1CS_walk_seek_to_index`
  (`4k + 4` steps, head `4(p+k)+3 ↦ 4p`, into `bDec`), `g1CS_walk_seek_exhaust`
  (the same shape into the boundary `bExh`), `g1CS_walk_mark`
  (`index ↦ spent`, head `4p ↦ 4p + 4`, into `bFwd`), `g1CS_walk_seek_mark`
  (`4k + 8` steps, the two composed), `g1CS_walk_fwd_to_cursor`
  (`4(k+1)` read-only steps to just past the cursor, into `bTurn`),
  `g1CS_walk_turn` (four hold-left steps, arbitrary tape, into
  `g1RestoreMode ctx.vB`) and `g1CS_walk_restore` (`cursor ↦ data b`, back into
  `bProbe2`).
* `GateOneWalkExamples.lean` (new) — five literal probes reusing
  `G1InstallScanExamples.g1WalkExample = ⟨and, 0, 2, [false, true, true]⟩`
  (**fifteen** encoded frames, `60` input cells; the list-backed layouts append
  one `blank`, so **sixteen** frames and `64` bits) and three new intermediate
  layouts `g1WalkFramesRound1`/`Marked1`/`Restored1`: `walk_seek_mark`
  (`43 → 32` in `20` steps), `walk_seek_exhaust` (`43 → 24` in `20` steps on the
  marked layout, into `bExh`), `walk_fwd_to_cursor` (`32 → 48` in `16`),
  `walk_turn` (`48 → 44`) and `walk_restore` (`44 → 48`).  Each takes `n` and
  one safety bound from the caller; nothing chains them.

Pinned by `Tests/TMGateOneWalkSurfaceTests.lean` (theorem-style exact wrappers
for all seven macros, for `Phased.holdWalk4` and for three representative
literal probes), `Tests/TMGateOneControlSurfaceTests.lean` (the three new entry
states, the restore selector, the eighteen tuple lemmas, and exact wrappers for
the probe/`bFwd` table with `G1Stuck .bExh`, for the eight non-forward walk
modes being stuck, and for the seek's three outcomes) and
`Tests/TMGateOneRoutingSurfaceTests.lean` / `Tests/TMGateOneReadBSurfaceTests.lean`
(`g1_bFwd_rows` and `g1_bExh_stuck` replacing `g1_bSeek_stuck`).
`Tests/AxiomsAudit.lean` prints the axioms of every new tuple lemma, macro and
probe directly.  (**PR2b2, 2026-08-28**: the `G1Stuck .bExh` conjunct is gone
from `check_g1Advance_probe`, `check_g1_bFwd_rows_and_bExh` is now
`check_g1_bFwd_and_bRet_rows`, and the eight-mode stuck wrapper is now an
eleven-mode one.)

Explicitly deferred and claimed nowhere: the four remaining cursor-walk modes
and all their rows and tuple lemmas, the terminal exhaustion path (**both
delivered by PR2b2 below, 2026-08-28**), the
cursor-walk tape invariant, the **installation driver** (latch plus cursor
install executed from a real initial configuration), any iteration or loop
clock, addressing, the positive-index operand *value* read, the aggregated
out-of-range branches, repair, pass A, combine, output write, `TM.accepts`,
gate-semantics correctness, a full-clock theorem, and non-canonical or
physically padded tapes.

**PR2b2: the terminal exhaustion path of the G1 cursor walk, delivered
(2026-08-28):**

**Progress classification: Infrastructure.**

The successor of the merged `bExh` handoff, and the **terminal path only**.
`G1Ctx`, the `G1State` field list, `g1Clock` and the whole T2a validation
grammar are unchanged, and no new `Nat`, index, width, offset, length or request
field appears anywhere in the machine, the control or the context.  Every
merged normal-round atom keeps its statement byte-for-byte: only prose that
described `bExh` as a dead boundary changed.

**The route from the real initial configuration is unchanged.**  It still
reaches exactly `bProbe2`: `g1InstallScanSteps`,
`g1CS_readB_install_scan_exact`, its projections, the clock bound and the
literal `169`-step probe of `GateOneInstallScanExamples` are byte-for-byte as
merged.  **Every** new run below starts from a **caller-supplied**
configuration, tape length and safety bound.

* `GateOneControl.lean` — `G1Mode` gains exactly **four** constructors: `bRet`
  (the exhaustion scan), `bTurnFin` (the terminal turn) and
  `bFinFalse`/`bFinTrue` (the two terminal restore writers).  `g1Advance` gains
  **five** rows:

  ```text
  bExh + argSep     ↦ bRet      bRet + spent     ↦ bRet
  bRet + separator  ↦ bRet      bRet + data _    ↦ bRet
  bRet + cursor     ↦ bTurnFin
  ```

  `bRet` is an ordinary forward frame-reading mode, so it has no `g1Transition`
  rows of its own; `bExh` becomes a forward mode with a live row instead of a
  stuck boundary.  `g1Transition` gains **three** blocks and **eight** new
  standalone tuple lemmas — `g1Transition_bTurnFin_p0…p3` and
  `g1Transition_bFin_p0…p3` — each `rfl` after at most one split, none
  mentioning the request.  `g1FinMode` is the new terminal-writer selector and
  `g1FinMode_ne_restore` the fact that the terminal writer is never the round
  writer.  The walk now has **sixteen** modes: five forward
  (`bInsSeek`, `bProbe2`, `bFwd`, `bExh`, `bRet`) and eleven non-forward, with
  **thirty-one** transition tuples in total.  `g1Advance_range`,
  `g1Advance_ne_sink` and every T2a/T2b grammar and execution theorem
  re-derives unchanged; the `bScan + data` row stays **absent**.
* `GateOneRouting.lean` — `g1_bExh_stuck` is **removed**: it is now false, since
  `bExh + argSep` succeeds.  `g1_bRet_rows` replaces it and pins all five new
  rows exactly.  No route prefix reaches either mode.
* `GateOneWalkKernel.lean` — **reuses** `G1WalkSkip`, `g1FrameScanner`,
  `g1ValidPath_fix`, `g1AdvanceList_fix` and `Phased.holdWalk4` without
  restating them, and adds `g1Advance_bRet_of_skip` (the exhaustion scan crosses
  exactly the frames the round's forward scan does), the fourth kernel instance
  `g1FinWriter b` (`FrameWriter`: `cursor ↦ data b`, out into
  `readAResetStart`) and **three** exact `TM.runConfig` macros on an
  **arbitrary** frame list: `g1CS_walk_exh_to_cursor`
  (`4 * (k + 2)` read-only steps, head `4p ↦ 4(p + k + 2)`, into `bTurnFin`),
  `g1CS_walk_turn_fin` (four hold-left steps, arbitrary tape, into
  `g1FinMode ctx.vB`) and `g1CS_walk_fin_restore`
  (`cursor ↦ data b`, head `4p ↦ 4p + 4`, into `readAResetStart`).
* `GateOneWalkExamples.lean` — two new layouts at `j = 2 = arg2` on the reused
  request `⟨and, 0, 2, [false, true, true]⟩` (**fifteen** encoded frames, `60`
  input cells; the list-backed layouts append one `blank`, so **sixteen** frames
  and `64` bits): `g1WalkFramesTerminal`, operand-2 entirely `spent` with the
  cursor on ordinal `12`, and `g1WalkFramesFinal`, after the terminal restore.
  `g1WalkFramesTerminal_length` pins their shape and
  `g1WalkFramesFinal_no_cursor` pins that the final tape has **no `cursor`
  frame at all**.  Three literal probes: `walk_exh_to_cursor` (`24 → 52` in `28`
  steps), `walk_turn_fin` (`52 → 48`) and `walk_fin_restore` (`48 → 52`, into
  `readAResetStart`).  Each takes `n` and one safety bound from the caller;
  nothing chains them.

Pinned by `Tests/TMGateOneWalkSurfaceTests.lean` (theorem-style exact wrappers
for the three new macros, for `g1FinWriter`, for the two new layouts including
the cursor-free witness, and for all three literal probes),
`Tests/TMGateOneControlSurfaceTests.lean` (`g1FinMode`, `g1FinMode_ne_restore`,
the eight new tuple lemmas, the exact terminal table
`check_g1Advance_exhaustion`, and the terminal turn/restore wrappers
`check_g1Transition_bTurnFin`/`check_g1Transition_bFin`) and
`Tests/TMGateOneRoutingSurfaceTests.lean` / `Tests/TMGateOneReadBSurfaceTests.lean`
(`g1_bRet_rows` replacing `g1_bExh_stuck`).  `Tests/AxiomsAudit.lean` prints the
axioms of every new tuple lemma, macro and probe directly.

Explicitly deferred and claimed nowhere: the cursor-walk tape invariant, the
**installation driver**, any iteration or loop clock, any theorem that a real
run reaches `bExh` — or reaches it after the right number of rounds —
addressing, the positive-index operand *value* read, the aggregated
out-of-range branches, repair, pass A, combine, output write, `TM.accepts`,
gate-semantics correctness, a full-clock theorem, and non-canonical or
physically padded tapes.  `readAStart`, `combineStart`, `readAResetStart` and
`bOOB` are still idle handoffs: the terminal restore *arrives* at
`readAResetStart` and nothing happens there.  (**Superseded by Repair-2a,
2026-08-28**, for `readAResetStart` only: it is now the live one-step bridge
into `bRepairSeek`, so the terminal restore's arrival *does* continue into the
repair sweep.  The other three handoffs are unchanged.)

**PR3a: the G1 cursor-walk tape invariant and its real installation, delivered
(2026-08-28):**

**Progress classification: Infrastructure.**

The merged atoms of PR2b1/PR2b2 hold on **arbitrary** frame lists.  This slice
pins the **one canonical frame list** the walk runs on and reaches it from the
**real initial configuration** — and stops there.  **No round is executed.**
`G1Ctx`, the `G1State` field list, `G1Mode`, `g1Advance`, `g1Transition` and
`g1Clock` are all unchanged, no new `Nat`, index, width, offset, length or
request **field** appears in the machine, the control or the context, and
**every merged module is byte-identical**: this slice is additive.  The new
`Nat`-valued names below (`g1WalkCursor`, `g1WalkInstallSteps`,
`g1WalkEmptyOOBSteps`) are pure functions used to *state* the theorems; the
machine never computes with them.

* `GateOneWalkInvariant.lean` (new) — the vocabulary.  With `u = tag.units`,
  `a1 = arg1`, `a2 = arg2`, `m = vals.length`:

  ```text
  g1WalkFrames r j = g1FieldRouteFrames r
      · index^(a2-j) · spent^j · separator
      · data(vals.take j) · cursor · data(vals.drop (j+1))
      · output false · finish · blank
  g1WalkCursor r j = u + a1 + a2 + j + 4
  g1WalkConfig r j _ _ v _  -- Σ(j): that tape, head 4 * g1WalkCursor r j - 1,
                            -- control bSeek .p3, ctx g1Ctx0.withVB v,
                            -- and vals[j]? = some v
  ```

  under the invariant's numeric conditions `j ≤ a2`, `j < m` and the hidden-bit
  relation `vals[j]? = some v`, all **explicit arguments** of `g1WalkConfig`, so
  the configuration cannot be formed outside the invariant's range or with a
  latch inconsistent with the hidden frame.  Every structural side condition
  the merged round macros take as a *hypothesis* is **proved here as a theorem
  about the layout**, from the numeric guards and never assumed — PR3b is what
  feeds them to the macros: `g1WalkFrames_length_eq_validation` (the invariant
  word is exactly as long as `encodeG1Frames r ++ [.blank]`),
  `g1WalkFrames_count_index`/`_count_spent`/`_count_cursor` (`a2 - j` unspent,
  `j` spent, cursor **unique**), `g1WalkOperand2_spent_suffix` (`spent^j` is the
  right suffix of the operand-2 field, so the reverse seek's stopping `index` is
  the one immediately left of the spent run), `g1WalkSkipRun_mem` and
  `g1WalkSkipRun_no_index` (the run both scans of a round cross is
  `spent^j · separator · data^j` and contains **no** `index` frame — the reason
  the forward scan `bFwd`, which has no `index` row, never stalls) and
  `g1WalkCursor_safe` (every cell a round touches is inside the tape on the
  invariant domain `j ≤ a2`, `j < m`).  `g1WalkFramesMarked` and
  `g1WalkFramesRestored` name the two other layouts of a round; both carry exact
  length/count facts, while their execution theorems remain PR3b.  The
  module imports `GateOneWalkKernel` for exactly one name, `G1WalkSkip`, in
  whose terms the two skip-run facts are stated; **no macro of that module is
  used**, and the two executed capstones compose only the merged
  `GateOneInstallScan` and `GateOneProbeInstall` atoms, with the transition
  table never unfolded.
* `GateOneWalkInvariant.lean`, executed part — **two** capstones, both from
  `G1M.initialConfig` and both **terminating at their endpoint**:
  * `g1CS_walk_install_exact` — for a canonical `and`/`or` request with
    `arg2 = k + 1` and `vals[0]? = some v`, exactly
    `g1WalkInstallSteps r = g1InstallScanSteps r + 9` genuine steps validate the
    word, rewind, rescan the tag, cross both operand fields and the `separator`,
    probe the first data frame, latch its bit into `G1Ctx.vB` and install the
    cursor over it — landing exactly on `Σ(r, 0, v)`.  Exactly **one** frame is
    written, `data vals[0] ↦ cursor`.  `_head`, `_vB`, `_tape` and `_state`
    project it.
  * `g1CS_walk_install_oob_exact` — the **empty-data** branch: with `vals = []`
    the same read-only scan's probe meets the `output false` destination and
    `g1WalkEmptyOOBSteps r = g1InstallScanSteps r + 4` steps end in the stable
    `bOOB` boundary with the tape **bit-for-bit the initial tape**.  `_stable`,
    `_tape`, `_head` and `_state` project it, and `g1CS_walk_oob_ne_invariant`
    separates that boundary from the reverse-seek entry of `Σ(0)`.

  `g1WalkInstallSteps_le_clock` and `g1WalkEmptyOOBSteps_le_clock` keep both
  counts inside the **unchanged** public clock; `g1Clock` is not widened.
* `GateOneWalkInvariantExamples.lean` (new) — all-literal probes on two literal
  requests.  `⟨and, 0, 2, [false, true, true]⟩` (the merged
  `G1InstallScanExamples.g1WalkExample`, **fifteen** encoded frames and `60`
  input cells; the list-backed layouts append one `blank`, so **sixteen**
  frames): `Σ(0)` is literally the merged post-install layout
  `G1ProbeInstallExamples.g1WalkFramesCursor0`, re-named `g1WalkFramesRound0`,
  with the cursor at ordinal `10`, `index²` and no `spent`; the installation is
  `169 + 5 + 4 = 178` steps to head `39`, inside the clock.
  `⟨and, 0, 2, []⟩`: the empty-data installation out-of-range branch in exactly
  `149` steps to head `44`, tape unchanged, inside the clock.

Pinned by `Tests/TMGateOneWalkInvariantSurfaceTests.lean` (theorem-style exact
wrappers for the structural facts, the lengths and counts of all three layouts,
the head bound, `Σ(j)`'s projections and hidden-bit relation, both capstones
with all their projections, both clock bounds and both literal probes).
`Tests/AxiomsAudit.lean` prints the
axioms of every new statement directly; each depends only on `propext`,
`Classical.choice` and `Quot.sound`.

Explicitly deferred to PR3b and claimed nowhere **by PR3a** (the first two items
were then **delivered by PR3b, 2026-08-28**, and the walk items after them by
**PR3c, 2026-08-28**, both in sections below; the repair sweep and everything
listed after it are still open): the **one-round iteration**
`Σ(j) → Σ(j+1)`, the **normal-round and out-of-range preservation** theorems on
`Σ(j)`, the induction over `j`, any loop, driver or cumulative clock, the
successful terminal at `j = arg2` (the `bExh`/`bRet`/`bTurnFin`/`bFin` path into
`readAResetStart`), the aggregation of the two out-of-range branches,
addressing, and the **positive-index operand-value theorem** — nothing here
claims the machine resolves `r.vals[r.arg2]?` for `arg2 > 0`.  Also absent: the
`spent ↦ index` repair sweep, pass A, combine, the output write, `TM.accepts`,
gate-semantics correctness, a full-clock theorem, and non-canonical or
physically padded tapes.  The deferral lists of the merged `GateOneInstallScan`,
`GateOneProbeInstall` and `GateOneWalkKernel` docstrings are scoped to *those*
modules ("nothing *here*", "every theorem below") and stay true verbatim; the
invariant and the installation driver they defer now live in the new module
above.

**PR3b: exactly one round of the G1 cursor walk, delivered (2026-08-28):**

**Progress classification: Infrastructure.**

PR3a reaches `Σ(0)` and stops there.  This slice executes **one round** on the
invariant, in both of its outcomes, and stops there: **there is still no
induction over `j`, no driver, no loop and no cumulative clock**.  `G1Ctx`, the
`G1State` field list, `G1Mode`, `g1Advance`, `g1Transition` and `g1Clock` are
all unchanged, **no new runtime field** of any kind appears in the machine, the
control or the context, and every merged module outside the two extended below
is byte-identical.  The PR3a install/OOB declarations themselves are unchanged;
this slice is purely additive.

* `GateOneWalkInvariant.lean` (extended) — the layout algebra a round needs, all
  of it *proved* from the PR3a structural facts and never assumed: eight private
  re-association splits (`g1WalkSplit_mark`, `_marked_mark`, `_marked_fwd`,
  `_marked_cursor`, `_restored_cursor`, `_restored_probe`, `_restored_oob`,
  `_succ`) putting `g1WalkFrames`/`g1WalkFramesMarked`/`g1WalkFramesRestored`
  into exactly the shape one merged macro consumes, and five private length
  lemmas (`g1MarkPre_length`, `g1SkipRun_length`, `g1FwdPre_length`,
  `g1CursorPre_length`, `g1ProbePre_length`) pinning the frame ordinal each
  macro's `pre` ends at, so every head position is the invariant's own.  Two
  private list helpers are added, `g1Drop_cons` and `g1Getn`; `g1Getn` is what
  turns the invariant's hidden-bit argument `vals[j]? = some v` into the
  `getElem` form the restore split consumes, so **the bit written back is the
  bit the cursor was hiding**, by proof rather than by stipulation.  One further
  private `rfl`, `g1Ctx0_withVB_withVB`, records that re-latching overwrites the
  previous bit rather than accumulating state.  The shared
  prefix of a round (`g1CS_walk_prefix_exact`, private) composes
  `g1CS_walk_seek_mark` (`8j + 12`), `g1CS_walk_fwd_to_cursor` (`8j + 8`),
  `g1CS_walk_turn` (`4`) and `g1CS_walk_restore` (`4`) into `16j + 28` steps
  from `Σ(j)` to `bProbe2` on `g1WalkFramesRestored r j`; the skip-run
  hypotheses of both scans are discharged by `g1WalkSkipRun_mem` and the tape
  bound by `g1WalkCursor_safe`.  The transition table is never unfolded.
* `GateOneWalkInvariant.lean`, executed part — **three** new public theorems,
  all from a **caller-supplied** `Σ(j)`:
  * `g1CS_walk_iteration_exact` — for `j < arg2` and `j + 1 < vals.length`,
    exactly `16 * j + 37` genuine steps run `Σ(r, j, v)` to `Σ(r, j+1, v')`.
    The hypotheses are exactly `hv : vals[j]? = some v` and
    `hv' : vals[j+1]? = some v'`, and **both are passed into `g1WalkConfig`**,
    at the start *and* at the endpoint: the hidden-bit relation is explicit on
    both sides, so the round re-establishes the invariant rather than weakening
    it.  Because both sides are the canonical layout at their own `j`, the
    statement pins the whole tape: one on-tape decrement
    `index^(a2-j) · spent^j ↦ index^(a2-j-1) · spent^(j+1)`, the **unique**
    cursor moves one data slot right, slot `j` is restored to `data vals[j]`,
    and the anchor, tag run, operand-1 field, `argSep`s, `separator`, untouched
    data slots, `output`, `finish` and blank frames are all unchanged.  Six
    merged macros are composed — the prefix's four plus
    `g1CS_walk_probe_latch` (`5`) and `g1CS_walk_install_cursor` (`4`).
  * `g1CS_walk_oob_exact` — for `j < arg2` but `j + 1 = vals.length` (cursor on
    the *last* data frame, an operand-2 unit still unspent), exactly
    `16 * j + 32` steps reach the `bOOB` boundary on `g1WalkFramesRestored r j`.
    That tape is stated exactly: the data region is **fully restored to `vals`
    and cursor-free** (`g1WalkFramesRestored_count_cursor`) while operand 2 is
    **partially spent and unrepaired** — `j + 1` units consumed and
    `arg2 - j - 1` left (`_count_spent`, `_count_index`).  It is an
    intermediate tape, and reaching `bOOB` is **not a rejection theorem**: no
    output write, verdict or `TM.accepts` result is claimed anywhere.
  * `g1CS_walk_oob_stable` — that boundary absorbs every further step.

  No clock bound is claimed for either round count: `16 * j + 37` and
  `16 * j + 32` are stated but never summed or compared against `g1Clock`,
  because the comparison only becomes meaningful once the loop exists.
* `GateOneWalkInvariantExamples.lean` (extended) — the PR3b probes, reusing the
  merged literals rather than copying them.  On `⟨and, 0, 2, [false, true,
  true]⟩`: `Σ(1)`, `Σ(2)` and the round's restored word **are literally**
  `G1WalkExamples.g1WalkFramesRound1`, `g1WalkFramesTerminal` and
  `g1WalkFramesRestored1` (`walkFrames_one`, `walkFrames_two`,
  `walkFramesRestored_one`), with cursors at ordinals `11` and `12`, sixteen
  frames, a unique cursor and `index¹ · spent¹` at `j = 1`; the two single
  rounds are `Σ(0) → Σ(1)` in `37` steps and `Σ(1) → Σ(2)` in `53`, heads
  `39 → 43 → 47`.  On `⟨and, 0, 2, [false, true]⟩` — whose data region is one
  frame shorter, so it needs its own two fifteen-frame literals — the
  out-of-range round is exactly `48` steps, head `43 → 52`, ending on a layout
  with `cursor` count `0`, `spent` count `2` and `index` count `0`.  Neither
  round probe is chained to `walk_install` or to the other.

Pinned by `Tests/TMGateOneWalkInvariantSurfaceTests.lean` (theorem-style exact
wrappers for all three round theorems and for every new example fact, plus the
existing PR3a wrappers, unchanged).  `Tests/AxiomsAudit.lean` prints the axioms
of every new statement **directly**; each depends only on `propext`,
`Classical.choice` and `Quot.sound`.  No new module is registered: both extended
modules and the surface test are already roots of `lakefile.lean`.

Deferred to PR3c **by PR3b** and all **delivered by PR3c, 2026-08-28**, in the
section below: the **induction over `j`**, the driver that reaches `Σ(j)` for
`j > 0` from `G1M.initialConfig`, the cumulative loop clock and the clock bounds
on the cumulative success/OOB totals, the **successful terminal** at `j = arg2` (the
`bExh`/`bRet`/`bTurnFin`/`bFin` path into `readAResetStart`), the aggregation of
the round's out-of-range branch with the empty-data one, and the
**positive-index operand-value theorem**.  Still absent and claimed nowhere:
the `spent ↦ index` repair sweep, pass A, combine, the output write,
`TM.accepts`, gate-semantics correctness, a full-clock theorem, and
non-canonical or physically padded tapes.

**PR3c: the G1 cursor-walk driver, terminal and positive-index read-B,
delivered (2026-08-28):**

**Progress classification: Infrastructure.**

PR3b executes one round on `Σ(j)` from a caller-supplied configuration.  This
slice **iterates** that round from the real initial configuration, closes the
walk at `j = arg2` and turns the result into the first **arbitrary
positive-index operand-2 read** of the G1 machine.  `G1Ctx`, the `G1State` field
list, `G1Mode`, `g1Advance`, `g1Transition` and `g1Clock` are all unchanged,
**no new runtime field** and **no new `Nat`** appear anywhere, every merged
module outside the four docstrings touched below is byte-identical, and the
transition table is never unfolded: every step is a composition of the PR3a/PR3b
capstones.  With `u = tag.units`, `a1 = arg1`, `a = arg2`, `m = vals.length`:

* `GateOneWalkDriver.lean` (new) — the loop clock and the induction.
  `g1BLoopSteps k = 8k² + 29k` is the cumulative cost of the first `k` rounds,
  with the recurrence `g1BLoopSteps_succ` (`= g1BLoopSteps k + (16k + 37)`,
  exactly the cost of `g1CS_walk_iteration_exact` at `j = k`) and the closed
  form `g1BLoopSteps_eq_sum` (`= ∑_{j<k} (16j + 37)`).
  `g1CS_walk_loop_exact` is the induction: for every `k ≤ a` with `k < m` and
  `hv : r.vals[k]? = some v`, exactly `g1WalkInstallSteps r + g1BLoopSteps k`
  genuine steps run `G1M.initialConfig` to `Σ(r, k, v)` — **formed with that
  same `hv`**, so the hidden-bit relation is carried, not dropped: the
  statement is about the invariant configuration whose latch is tied to the
  data region, and every intermediate round re-establishes it.  The base case
  *is* `g1CS_walk_install_exact`; the successor composes one exact `16k + 37`
  round and generates the *prior* round's hidden-bit proof
  `r.vals[k]? = some r.vals[k]` from `k < m`.  Both numeric side conditions of
  `Σ` travel with the induction; no semantic hypothesis is introduced.
* `GateOneWalkDriver.lean`, the layout family — `g1BSpentFrames r s`, the one
  **repair-pending** shape both endpoints land on: operand 2 split as
  `index^(a-s) · spent^s`, data region exactly `vals`, **no cursor**.
  The semantic domain is `s ≤ a`; outside it the unrestricted definition is
  only a syntactic Nat-subtraction identity.
  `g1WalkFramesRestored r j = g1BSpentFrames r (j+1)`
  (`g1BSpentFrames_eq_restored`), `g1BSpentFrames r 0 = encodeG1Frames r ++
  [.blank]` when `vals = []` (`_empty`), plus `_length`,
  `_length_eq_validation` and `_count_cursor`/`_count_spent`/`_count_index`.
  `g1ExhPre` with `_length` and `_argSep` names the prefix the exhaustion seek
  stops in front of.
* `GateOneWalkDriver.lean`, the successful terminal — `g1CS_walk_terminal_exact`
  at `k = a < m`.  `Σ(a)` has `index⁰`, so the reverse seek exhausts on the
  `argSep` that opens the operand-2 field instead of marking:
  `(8a + 8) + (8a + 12) + 4 + 4 = 16a + 28` steps compose
  `g1CS_walk_seek_exhaust`, `g1CS_walk_exh_to_cursor`, `g1CS_walk_turn_fin` and
  `g1CS_walk_fin_restore` and land in `readAResetStart`, head
  `4 * (g1WalkCursor r a + 1)`, tape `g1BSpentFrames r a`, `vB = vals[a]`.  The
  cursor is gone and the data region is exactly `vals`; the operand-2 field is
  `spent^a` — **unrepaired**.
* `GateOneWalkDriver.lean`, the public read — `g1CS_readB_positive_exact`.  For
  a canonical `and`/`or` request with `0 < a` and `r.vals[a]? = some b`, exactly
  `g1BReadSteps r = g1WalkInstallSteps r + 8a² + 45a + 28 = g1InstallScanSteps r
  + 8a² + 45a + 37` genuine steps take `G1M.initialConfig` to that pass-A reset
  handoff with `G1Ctx.vB = b`; head, control state, context and the whole tape
  are pinned, with `_head/_state/_vB/_tape` projections.  The returned bit is
  the **actual** `r.vals[r.arg2]`, resolved physically out of the unannotated
  data region: no value, target, cursor or index annotation is supplied to the
  machine, and every summand of the count is a concrete polynomial in the
  request's own fields — no pad and no advice.
* `GateOneWalkDriver.lean`, the aggregated out-of-range branch —
  `g1CS_readB_positive_oob_exact`.  For `0 < a` and `m ≤ a`, one exact
  configuration equality with the single count `g1BOOBSteps r =
  g1InstallScanSteps r + 8m² + 29m + 4`: `m = 0` is the read-only empty-data
  installation branch (`+4`, `_oob_nil`), `m > 0` composes the installation,
  `g1BLoopSteps (m-1)` and the `16(m-1) + 32` out-of-range round (`_oob_cons`).
  Head `4 * (u + a1 + a + m + 5)`, stable `bOOB`, tape `g1BSpentFrames r m`,
  context `g1BOOBCtx r` — `g1Ctx0` when `vals = []`, `g1Ctx0.withVB vals[m-1]`
  otherwise.  `_oob_stable` shows the boundary absorbs every further step, and
  `_head/_state/_tape` project it.  Reaching `bOOB` is a **boundary, not a
  verdict**: no output write, rejection or `TM.accepts` claim is attached.
* `GateOneWalkDriver.lean`, the clock — `g1BReadSteps_le_clock` and
  `g1BOOBSteps_le_clock` keep both totals inside the **unchanged** `g1Clock`,
  and are proved *before* either public capstone is stated.  `m ≤ a` and
  `a < m` are exhaustive and the two endpoints are distinguished by
  `g1CS_readB_positive_oob_ne_success`, so exactly one public capstone applies
  to every data region of a canonical binary request with `0 < a`.
* `GateOneWalkDriverExamples.lean` (new) — four all-literal probes, reusing the
  merged literals.  `⟨and, 0, 1, [false, true]⟩`: `vals[1] = true` in `239`
  steps (`149 + 90`) to head `44`, ending on a fourteen-frame word with no
  cursor, one `spent` and no `index`; literal clock `1438720`.
  `⟨and, 0, 2, [false, true, true]⟩`: `vals[2] = true` in `328` steps
  (`178 + (37 + 53) + 60`) to head `52`, ending on
  `G1WalkExamples.g1WalkFramesFinal` — the literal word that module's terminal
  restore probe already produced, re-identified here as `g1BSpentFrames r arg2`.
  `⟨and, 0, 2, []⟩`: aggregated OOB at `m = 0` in `149` steps to head `44`,
  tape the initial word.  `⟨and, 0, 2, [false, true]⟩`: aggregated OOB at
  `m = 2` in `255` steps (`170 + 37 + 48`) to head `52` on
  `G1WalkInvariantExamples.g1OOBFramesRestored1`.

Pinned by `Tests/TMGateOneWalkDriverSurfaceTests.lean` (new: theorem-style exact
wrappers for the loop clock, the induction with its hidden-bit endpoint, the
layout family with all its counts, the terminal, both totals, both clock bounds,
the public read with all four projections, both out-of-range branches with the
aggregated capstone, its stability, its projections and the boundary
distinction, plus all four literal probes).  `Tests/AxiomsAudit.lean` prints the
axioms of every new statement **directly**; each depends only on `propext`,
`Classical.choice` and `Quot.sound`.  Two new modules and one new surface test
are registered in `lakefile.lean`.  The `GateOneReadB`, `GateOneWalkKernel`,
`GateOneWalkInvariant` and `TMGateOneWalkInvariantSurfaceTests` docstrings are
re-scoped to point here — in particular the PR3a/T2b-1 sentence saying nothing
in this development resolves the selected data frame for `arg2 > 0` is
superseded by `g1CS_readB_positive_exact`.

Explicitly deferred and claimed nowhere by PR3c: the `spent ↦ index` **repair
sweep** — both endpoints leave the operand-2 field consumed, so neither final
tape is the canonical word and no theorem claims otherwise — **pass A** (the
operand-1 read the `readAResetStart` handoff opens), the **combine** step, the
**output write**, `TM.accepts`, a full-clock theorem, gate-semantics
correctness, the acceptance gate, multi-gate composition, the
specification-level bridge, and non-canonical or physically padded tapes.
Reaching `bOOB` remains a boundary, not a rejection theorem.

**Repair-1: the G1 operand-2 repair control and its generic kernel, delivered
(2026-08-28):**

**Progress classification: Infrastructure.**

PR3c leaves both operand-2 endpoints on a **repair-pending** tape: the field is
`index^(a-s) · spent^s`, so the word is not the canonical one.  This slice adds
the finite control that can undo that, and the generic `spent ↦ index` machine
kernel behind it, on **caller-supplied** frame lists only.  `G1Ctx`, the
`G1State` field list, `g1Advance`, `g1Clock`, `G1M` and every merged execution
theorem are unchanged; **no new runtime field**, **no new `Nat`**, and the
transition table is never unfolded inside an execution proof.

* `GateOneControl.lean` — five new modes `bRepairSeek`/`bRepairWrite`/
  `bRepairBack`/`bRepairHop`/`bRepairDone`, the exact analogue of T1's
  `repairSeek`/`repairWrite`/`repairBack`/`repairHop`/`repairDone`, with their
  three named entry states (`g1RepairSeekState`, `g1RepairWriteState`,
  `g1RepairDoneState`), the reverse frame table
  `g1RepairBackAdvance`/`g1RepairBackComplete` and its crossable-frame predicate
  `G1RepairSkip`, their `g1Transition` rows and their eleven standalone
  tuple lemmas.  `bRepairSeek` reads right to left with **four** outcomes,
  exactly T1's — a
  `spent` unit stops it at `bRepairWrite`, the `bof` anchor at `bRepairDone`,
  a crossable interior frame (`G1RepairSkip`: the tag run, both `argSep`s,
  `index`, the `separator`, the data region, `output` and `finish`) continues it
  one frame further left, and a window the scan may not cross — a `blank`, a
  leftover `cursor`, or one of the three reserved codes, which decode to nothing
  — enters the **pre-existing** `reject` sink without moving
  (`g1Transition_bRepairSeek_p0_bad`).  `bRepairWrite` writes the
  four literal cells of `index`, `bRepairBack` walks them back and `bRepairHop`
  hops, the same `4 + 4 + 4 + 1 = 13` shape as the destructive round run in
  reverse; `bRepairDone` hands off to the **existing, still idle** `readAStart`.
  `G1ForwardMode` gains the five extra non-forward rows; `G1Stuck` and
  `g1Advance_range` are unchanged definitions whose `decide` proofs now range
  over them too, and the docstring counts are updated to match.
* **The sweep cannot cross corrupted tape.**  This is the point of the fourth
  outcome: without it a repair run would skip an undecodable window or a
  structurally impossible `blank`/`cursor` and keep rewriting `spent` units
  behind it, contradicting the decoder's rejected-code contract and the T1
  repair sweep this control mirrors.  `G1RepairSkip` is therefore pinned in both
  directions, and the rejection is executable, not merely tabular:
  `g1CS_repair_frame_reject` runs it as four genuine `G1M` steps into the sink
  and `g1CS_repair_frame_reject_idle` shows the sink then holds for the whole
  remaining budget.  The three reserved codes decode to **no frame at all**, so
  they are pinned at the transition/table level (`g1RepairBackComplete_reserved`
  and the literal `bRepairSeek` rows in the control surface tests) rather than
  through a frame-level run that could not exist.
* **`readAResetStart` is still idle.**  Nothing routes into the sweep in this
  slice: `g1_repair_unreachable_forward` proves no `g1Advance` row produces a
  repair mode, `g1_repair_modes_stuck` proves all five are stuck at the frame
  table, and no `g1Transition` row outside the five enters one.  The sweep is
  therefore only ever entered from a configuration the caller writes down.  Its
  rejection row leaves the sweep into the pre-existing `reject` sink: no sixth
  mode, no new state field.  (**Superseded by Repair-2a, 2026-08-28**: the
  `readAResetStart` row is now the live bridge into `bRepairSeek`.  The two
  unreachability theorems are unchanged and still true — they are about the
  *frame table* `g1Advance` — and the bridge is the only `g1Transition` row
  outside the five that enters one.)
* `GateOneRepairKernel.lean` (new) — `g1RepairScanner` (`ReverseFrameScanner`,
  stopping on `spent` at the write handoff, on `bof` at the terminal
  handoff and on any frame it may not cross in the `reject` sink, with the
  three-way stop state `g1RepairStopState`) and `g1RepairCycle`
  (`FrameRewriteCycle`, `marker = spent`,
  `target = index`) as genuine instances of the generic kernels, all of whose
  obligations are the control's standalone tuple lemmas.  On top of them, the
  exact `TM.runConfig` macros on an **arbitrary** frame list: the thirteen-step
  cycle `g1CS_repair_cycle_onList` (head `4p + 3 ↦ 4p - 1`),
  `g1CS_repair_seek_and_repair` (`4k + 13`), `g1CS_repair_frame_skip` (`4`),
  `g1CS_repair_frame_reject` (`4`, into the sink) with its stable form
  `g1CS_repair_frame_reject_idle`,
  `g1CS_repair_scan_skip` (`4` per frame), the iteration
  `g1CS_repair_spent_run` (`13 * s`), the executed terminal dispatch
  `g1CS_step_repairDone` and the anchor finish `g1CS_repair_finish` (`5`).
  `g1RepairPassSteps a s m = 4m + 13s + 4a + 5` — literally T1's
  `t1RepairSteps` — is the closed cost of the capstone
  `g1CS_repair_pass_exact`: from the scan's entry shape on the last cell of the
  rightmost frame it must visit, exactly that many genuine steps rewrite every
  designated `spent` frame to `index`, leave `left`, `mid` and `tail`
  bit-for-bit alone, leave the whole carried `G1Ctx` untouched, and stop at
  head `0` in `readAStart` through `bRepairDone`.  Its `hleft`/`hmid`
  hypotheses are `G1RepairSkip` constraints on the caller's frame list, so the
  capstone says nothing at all about a list containing a malformed frame; the
  arbitrary `tail` sits to the right of the entry point and is never read.
* **No literal probes in this slice.**  `g1CS_repair_pass_exact` is the
  concrete capstone: it is an exact `TM.runConfig` equation, on the caller's
  `n`, frame list and `G1Ctx`, with a closed step count.  The all-literal
  sixteen-frame probes of the sweep — one cycle, seek+repair, a multi-unit run
  and a whole pass — were deferred **in full** to **Repair-1b** together with
  their module, so *this* slice ships no `GateOneRepairKernelExamples`, no probe
  wrappers and no probe axiom roots.  **Repair-1b is delivered below
  (2026-08-28)** and supplies exactly those four runs.

Pinned by `Tests/TMGateOneRepairKernelSurfaceTests.lean` (new: theorem-style
exact wrappers for both kernel instances, the reverse table with all four
outcomes and its three stop states, all nine macros,
the closed cost, the capstone, the two unreachability facts and the idle
endpoint) and by the extended
`Tests/TMGateOneControlSurfaceTests.lean` (the eleven new tuple lemmas, the
reverse table pinned in both directions, the two forbidden codewords and the
three reserved codes pinned literally, plus the
row pinning that `readAStart` and `readAResetStart` are both still idle —
**superseded by Repair-2a, 2026-08-28**, which replaces the `readAResetStart`
conjunct by `check_g1Transition_readAResetStart_bridge`).
`Tests/AxiomsAudit.lean` prints the axioms of every new statement **directly**;
each depends only on `propext`, `Classical.choice` and `Quot.sound`.  One new
module and one new surface test are registered in `lakefile.lean`.  The
`GateOneWalkKernel` and `GateOneWalkInvariant` docstrings are re-scoped to point
here.

Deferred by Repair-1 to **Repair-1b** and **now delivered there** (see the
Repair-1b entry immediately below): the all-literal probe module for this
kernel and every statement in it.  Explicitly deferred to **Repair-2** and
claimed nowhere by Repair-1 — and **all delivered by Repair-2a, 2026-08-28**,
in the section below: the
request-specific **repair driver** (the layout split that identifies `left`,
`spent^s`, `mid` and `tail` inside a real request), any composition of the
operand-2 read with a repair, the `readAResetStart` bridge that would route into
`bRepairSeek`, the common zero/positive pass-A theorem, clocks for a combined
read-plus-repair.  Still deferred and claimed nowhere: any pass-A execution, and
any output write, acceptance or `TM.accepts` claim.  `readAStart` remains idle, so the sweep's endpoint is a
stationary handoff and nothing continues from it; `bOOB` is untouched and is
still a boundary, not a rejection theorem.  The sweep's own rejection outcome is
likewise a **control-level** fact — the machine enters the stable `reject` state
and stops rewriting — and not a verdict: no statement of this slice relates it
to `TM.accepts`, to a decision procedure, or to any claim that malformed tapes
are detected end to end.

**Repair-1b: the literal G1 repair probes, delivered (2026-08-28):**

**Progress classification: Infrastructure.**

The probe module Repair-1 deferred.  Nothing in the control, the kernel or the
machine changes: no new mode, **no new runtime field**, no new `Nat`, no new
`g1Advance` row, and no macro of `GateOneRepairKernel` is restated.  This slice
only *instantiates* those macros at one literal word.

* `GateOneRepairKernelExamples.lean` (new) — the sixteen-frame word for
  `G1InstallScanExamples.g1WalkExample = ⟨and, 0, 2, [false, true, true]⟩` with
  **both** operand-2 units consumed (`probeSpentFrames`), the half-repaired word
  (`probeHalfFrames`) and the repaired word (`probeIndexFrames`).
  `probeInputLen = 60` is the encoded-input length parameter; `probe_word_cells`
  separately pins 64 occupied cells strictly inside `G1M.tapeLength
  probeInputLen`.  Nonvacuity is literal:
  `probeIndex_eq_encoded` says the repaired word is exactly
  `encodeG1Frames g1WalkExample ++ [blank]`, `probe_words_distinct` says the
  three words are pairwise different, `probe_counts` says the consumed units go
  `2 ↦ 1 ↦ 0` while the `index` count goes `0 ↦ 2` at length `16`, and
  `probe_cell32` says physical cell `32` genuinely flips `true ↦ false`, so the
  runs below cannot be no-ops.  `probe_safe` is the single head-safety bound
  every probe reuses.
* **Four exact `G1M` runs**, each from a caller-supplied `g1AlignedConfig` in
  the reverse-read entry shape `bRepairSeek .p3` with the caller's latch
  `g1Ctx0.withVB true`: `cycle_probe` (`13` steps, head `35 ↦ 31`, one unit
  repaired) with `cycle_probe_ctx`; `seek_repair_probe`
  (`37 = 4 * 6 + 13` steps, head `59 ↦ 31`) with `seek_repair_probe_tape`
  landing on the half-repaired word; `run_probe` (`26 = 13 * 2` steps, head
  `35 ↦ 27`) with `run_probe_tape`; and the whole pass `pass_probe`
  (`79` steps, head `59 ↦ 0`, control `readAStart`) with `pass_probe_head`,
  `pass_probe_tape` — bit-for-bit `encodeG1Frames g1WalkExample ++ [blank]` —
  `pass_probe_ctx` (`vB` still latched) and `pass_probe_idle` (the endpoint
  holds for the whole remaining budget).  `probe_passSteps` and
  `probe_passSteps_split` pin `g1RepairPassSteps 6 2 6 = 4 * 6 + 13 * 2 +
  4 * 6 + 5 = 79`, and six split lemmas put the word into the exact shapes the
  macros consume.
* **The narrowed skip predicate is exercised, not bypassed.**  Repair-1
  narrowed `G1RepairSkip` so that `blank`, `bof`, `cursor` and `spent` are not
  crossable; these probes are stated against that narrowing.  `probeLeft` (the
  tag run and both `argSep`s) and `probeMid` (the `separator`, the data region,
  `output` and `finish`) are the only lists handed to the kernel's `hleft`/
  `hmid`, and they remain valid: `probeLeft_skip`/`probeMid_skip` discharge the
  hypotheses, and the new regression `probe_scan_lists_clean` pins **both
  directions** — the four non-crossable frames really are non-crossable, and
  neither scanned list, nor the fifteen-frame scanned region `probeScanned` as a
  whole, contains a `blank` or a leftover `cursor`.  Were a
  malformed frame to appear in either list, those hypotheses would fail and the
  pass theorems would lose their premises.
* **The trailing `blank` is documented and proved to sit outside the scan.**
  It is the sixteenth frame, the one the machine's own tape supplies past the
  `60` input cells; it is *not* `G1RepairSkip`, so it could not be crossed.
  `probeTail_beyond_entry` proves it does not have to be: it does not occur in
  the scanned region `probeScanned` (fifteen frames), and each of its four
  physical cells `60 … 63` lies strictly to the right of the sweep's entry cell
  `59 = 4 * 15 - 1`.  It is therefore passed as the capstone's **unconstrained**
  `tail`, never read, and reproduced bit-for-bit at the endpoint.
* **The probes stay caller-supplied.**  Every probe starts from an explicit
  `g1AlignedConfig`; none mentions `G1M.initialConfig`.  Repair-1's
  unreachability results say no `g1Advance` frame-table row enters the sweep;
  Repair-2a below adds the sole live `readAResetStart` bridge.  `readAStart`
  remains idle, exactly as `pass_probe_idle` records.

Pinned by `Tests/TMGateOneRepairKernelExamplesSurfaceTests.lean` (new:
theorem-style exact wrappers for **every** public statement of the probe module,
including the two narrowing regressions).  `Tests/AxiomsAudit.lean` prints the
axioms of every new statement **directly**; none depends on anything beyond
`propext`, `Classical.choice` and `Quot.sound`, and the purely definitional
ones depend on no axiom at all.  One new module and
one new surface test are registered in `lakefile.lean`; the Repair-1 deferral
pointers in `lakefile.lean`, `Tests/AxiomsAudit.lean` and
`Tests/TMGateOneRepairKernelSurfaceTests.lean` are re-scoped to point here.

Explicitly deferred to **Repair-2** and claimed nowhere by Repair-1b: the
request-specific **repair driver** and its layout split, any composition of the
operand-2 read with a repair, any run from `G1M.initialConfig`, any clock or
budget statement for a combined read-plus-repair, any pass-A execution, the
combine step, the output write, and any `TM.accepts`, verdict, gate-semantics,
acceptance-gate, multi-gate or specification-bridge claim.  (**Repair-2a,
2026-08-28**, delivers the first four of those; pass A, combine, the output
write and every verdict claim remain deferred.)  No literal
**rejection** probe is claimed here either: the executable rejection lives in
Repair-1 (`g1CS_repair_frame_reject`, `g1CS_repair_frame_reject_idle`) on the
caller's tape, and this slice adds no literal instance of it — the probe word
has no malformed frame inside its scanned region, which is precisely what
`probe_scan_lists_clean` and `probeTail_beyond_entry` record.

**Repair-2a: the G1 repair driver and the common pass-A handoff, delivered
(2026-08-28):**

**Progress classification: Infrastructure.**

Repair-1/1b prove the `spent ↦ index` sweep on **caller-supplied** frame lists
only.  This slice activates it on the machine's own route and instantiates it at
the **real** operand-2 layout, so both successful operand-2 reads end on a tape
that is bit-for-bit the initial tape again.  `G1Ctx`, the `G1State` field list,
`g1Advance`, `g1Clock`, `G1M` and every merged execution theorem are otherwise
unchanged: **no new mode**, **no new runtime field**, **no new `Nat`**, no
runtime argument and no advice input.

* **The one new live activation.**  `GateOneControl`'s `readAResetStart` row
  stops being idle and becomes the sweep's one-step bridge: it writes back the
  cell it scans — so **not one tape cell changes** — steps one cell *left* onto
  the last cell of the frame the reverse scan starts on, and enters
  `bRepairSeek .p3` with an empty frame buffer and the whole `G1Ctx` (in
  particular the latched `vB`) preserved.  `g1Transition_readAResetStart_idle`
  is **replaced** by `g1Transition_readAResetStart_bridge`, and
  `GateOneReadB`'s `g1CS_runConfig_readAReset_idle` — now false — is **replaced**
  by the executed boundary `g1CS_step_readAReset_bridge`.  This is the *only*
  row that changes.  `g1_repair_unreachable_forward` and `g1_repair_modes_stuck`
  are unchanged and still true: no *frame-table* row produces a repair mode, so
  the bridge is the single live entry.  `readAStart` and `combineStart` stay
  idle, `bOOB` stays a stable boundary, `G1ForwardMode`, `G1Stuck` and the
  validation grammar are untouched, and the malformed-word rejection surface of
  `GateOneValidation` is unaffected — a malformed word never reaches
  `readAResetStart`.
* **Repair-1's reject-aware behaviour is preserved verbatim.**  The scan still
  has four outcomes, `G1RepairSkip` is still the narrowed predicate, and the
  driver *discharges* its hypotheses rather than weakening them.
* `GateOneRepairDriver.lean` (new) — the layout split
  `g1BSpentFrames_repair_split`:
  `g1BSpentFrames r s = [bof] ++ g1RepairLeft r s ++ spent^s ++ g1RepairMid r
  ++ g1RepairTail r`, with `g1RepairLeft r s = tag^u · argSep · index^a1 ·
  argSep · index^(a-s)` (length `u + a1 + (a-s) + 2`),
  `g1RepairMid r = separator · data^(a+1)` (length `a + 2`) and the rest in
  `g1RepairTail r`.  `g1BSpentFrames_zero` pins that `s = 0` is *literally*
  `encodeG1Frames r ++ [blank]` (generalising `g1BSpentFrames_empty`, which
  needed an empty data region), and `g1RepairLeft_append`/
  `g1RepairFrames_repaired` pin that repairing the `s` units restores exactly
  the canonical word — the endpoint tape is the machine's **initial word**, not
  merely a word of the same length.
* **Both scanned runs are clean, and the tail is not scanned.**
  `g1RepairLeft_skip`/`g1RepairMid_skip` discharge the kernel's `hleft`/`hmid`
  against the narrowed `G1RepairSkip`; `g1Repair_not_skip` plus
  `g1RepairLeft_clean`/`g1RepairMid_clean` record the contrapositive — neither
  run contains a `blank` or a leftover `cursor`.  `g1RepairTail` **does**
  contain a `blank` (the frame the machine's own tape supplies past the input),
  and `g1RepairTail_unread` shows why that is harmless: the scanned region is
  exactly `g1WalkCursor r a + 1` frames, the sweep enters on its last cell, and
  every tail cell lies strictly to the right.  The tail is therefore the
  kernel's **unconstrained** argument, never read, reproduced bit-for-bit.
* **The sweep at the real layout.**  `g1CS_repair_sweep_exact`: from the post-B
  `readAResetStart` boundary **at its exact head** `4 * (g1WalkCursor r a + 1)`
  on `g1BSpentFrames r s`, for `s ≤ a` and `a < m`, exactly
  `g1RepairSteps r s = 4u + 4a1 + 8a + 9s + 22` genuine steps repair **all** `s`
  consumed units, finish on head `0` in `readAStart`, leave the tape exactly
  `encodeG1Frames r ++ [blank]` and leave the carried `G1Ctx` **unchanged**.
  `g1RepairSteps_eq` gives the provenance: `1 + g1RepairPassSteps (u + a1 +
  (a-s) + 2) s (a + 2)` — the bridge, `4` per skipped frame, `13` per consumed
  unit, the anchor read and the dispatch.  No pad, no free budget parameter.
* **The common pass-A handoff.**  `g1ReadAConfig r b` is head `0`, control
  `readAStart`, tape `(G1M.initialConfig (g1Point (encodeG1 r))).tape` and
  `G1Ctx.vB = b`, with the four projections `g1ReadAConfig_head/_state/_vB/
  _tape`.  `g1CS_readB_positive_repaired_exact` composes
  `g1CS_readB_positive_exact` (at `s = a`) with the sweep in
  `g1BPassASteps r = g1BReadSteps r + g1RepairSteps r a = g1InstallScanSteps r +
  8a² + 62a + 4u + 4a1 + 59` steps; `g1CS_readB_zero_repaired_exact` composes
  `g1CS_readB_zero_exact` (at `s = 0`, where nothing was consumed so the sweep
  writes **nothing** — `13 * 0` write steps) in
  `g1ZPassASteps r = g1ReadBSteps r + g1RepairSteps r 0 = g1ReadBHandoffSteps r
  + 8u + 8a1 + 43` steps.  Both land on the **same** `g1ReadAConfig r b`, with
  head/state/`vB`/tape projections each way and `*_tape_initial` pinning the
  tape as literally the initial tape; `g1CS_readB_repaired_common` states the
  meeting point once, conditioned on the *request* (`arg2 = 0` or not), never on
  a machine parameter.  The bit `b` is the **actual** `r.vals[r.arg2]`, resolved
  physically out of the unannotated data region.
* **Both totals fit the unchanged clock.**  `g1BPassASteps_le_clock`,
  `g1ZPassASteps_le_clock` and `g1CS_readB_repaired_common_le_clock` hold with
  **no hypothesis on the request**; `g1Clock` is not widened anywhere.
* **The out-of-range boundary is untouched.**
  `g1CS_readB_positive_oob_unrepaired` records only that it is stable for every
  extra budget, that its tape still carries `m` consumed units, and that
  `g1ReadAState ≠ g1OOBState` (`g1ReadAState_ne_oob`).  No repair, no rejection
  and no verdict is claimed for it.

Pinned by `Tests/TMGateOneRepairDriverSurfaceTests.lean` (new: theorem-style
exact wrappers for **every** public statement of the driver, including both
narrowing regressions and the unread tail), by the re-scoped
`Tests/TMGateOneControlSurfaceTests.lean` (`check_g1Transition_bRepairDone`
loses its `readAResetStart`-idle conjunct; the new
`check_g1Transition_readAResetStart_bridge` pins the bridge row and that
`readAStart`/`combineStart` are still idle) and by the re-scoped
`Tests/TMGateOneReadBSurfaceTests.lean` (`check_g1CS_step_readAReset_bridge`
replaces the removed idle pin).  `Tests/AxiomsAudit.lean` prints the axioms of
every new statement **directly**; each depends only on `propext`,
`Classical.choice` and `Quot.sound`.  One new module and one new surface test
are registered in `lakefile.lean`.  The `GateOneReadB`, `GateOneWalkDriver`,
`GateOneRepairKernel` and `GateOneRepairKernelExamples` docstrings are re-scoped
to point here.

Explicitly deferred to **Repair-2b** and claimed nowhere by Repair-2a: the
**all-literal** repaired runs from `G1M.initialConfig` — concrete requests,
concrete step counts, concrete endpoint words — and every probe module, probe
wrapper and probe axiom root for them.  Every statement of this slice is
quantified over the caller's request.  Explicitly deferred further and claimed
nowhere: **pass A** (`readAStart` is still idle and operand 1 is not read), the
**combine** step, the **output write**, `TM.accepts`, a full-clock theorem,
gate-semantics correctness, the acceptance gate, multi-gate composition, the
specification-level bridge, and non-canonical or physically padded tapes.

**T2a correction (2026-08-24).**  The first T2a head shipped a permissive
forward table (`vTag` looping on every `tag`, `vArg1`/`vArg2` looping on every
`index`) whose language was strictly larger than `G1Request.Canonical`, while
the comments, theorem names and this document described it as "the canonical
grammar".  Two independent reviews agreed the brief's §3 requires machine
enforcement, not a label.  The control was redesigned as described above; the
success surfaces `g1ValidationPath`, `g1ValidationAdvance`,
`g1CS_validate_encoded_exact`, `g1CS_validate_rewind_readB_exact`,
`g1CS_readB_head/state/tape` and `g1CanonicalEncoderAutomatonTrace` now take
`r.Canonical`, and the correspondence and rejection surfaces listed above were
added.  Step arithmetic is unchanged: no motion or step count of the control
was altered, so `2 * (encodeG1 r).length + 9`, the clock bound and every
head/tape projection are the same literals as before.

**T1a review hardening (2026-08-23):** the generic forward-frame scanner
`t1CS_scan_frames` and non-anchor reverse scanner `t1CS_rewind_tail` are public
T1b reuse surfaces, with exact import-side type probes and axiom audits.  Their
shared public signature exposes only the concrete-machine abbreviation `T1M`
in addition to the existing frame/tape/path vocabulary.  The public
`t1CS_frame_macrostep` now takes the positive `T1ForwardMode` premise.  The
clock theorem remains available by name but is not a simp rule: the generic
clock projections stop at `t1CS.timeBound N`, and the named theorem supplies
the explicit program-specific expansion to `t1Clock N` when needed.

The pure parser is now canonical: `decodeT1Tape? bits = some r` implies
`bits = encodeT1 r`.  Separately, `t1CanonicalEncoderAutomatonTrace` connects
the encoder's frames plus the explicit blank frame to the forward control
trace ending at rewind.  This is not a theorem equating the parser and the TM,
nor a malformed/trailing-input rejection theorem.  `T1Physical` is retained
only as vocabulary for that future scope and is not claimed to be discharged
by the current canonical execution results.  This review increment remains
**Infrastructure**, not P-vs-NP mainline progress.

**Generic step bridge delivered (2026-08-23):**
`TuringToolkit/ConstStatePhasedStepBridge.lean` proves, once and generically,
that an opaque `ConstStatePhasedProgram.transition` tuple equality determines
the complete compiled `TM.stepConfig`: dependent control state, moved head and
pointwise tape update.  Its five corollaries (`left`, `left_clamped`, `right`,
`right_clamped`, `stay` — the two `left` and the two `right` premises are
pairwise complementary, so every move at every head position is covered) let
large fixed control tables supply one small transition lemma without unfolding
every branch inside each machine proof.  Separate one-phase probes exercise all
five corollaries on concrete programs.  This is **Infrastructure**, not
verifier correctness, runtime closure, or P-vs-NP mainline progress; it
unblocks the T1b destructive seek proof layer after direct unfolding exceeded
the heartbeat budget.

**T1b-A1 fixed-control activation delivered (2026-08-23, after the generic
step bridge it consumes):**
`TuringToolkit/TrueUniformSeek.lean` extends the same zero-parameter finite
control with one Boolean latch and the machine-only modes needed to create
`spent` and `cursor` markers.  The ABI and quadratic clock are unchanged, and
no runtime `Nat`, width, offset, or index enters the state or program term.
Small transition-table lemmas feed the generic `ConstStatePhasedStepBridge`;
the latch-aware validation module supplies reusable aligned right/left/stay
step adapters and, at the time, proved the success/OOB handoff states stable —
superseded by T1c-1 above, which activates both.

As of that slice the control table was a **T1a/T1b-A fragment, not a complete
T1 control**: the T1c transitions — index-field restoration, the output write,
and acceptance — were absent from the table, not merely unproved; no transition
entered `accept`, and no transition left `successStart` or `oobStart`.  T1c-1
above supersedes that: the table is now complete, both boundaries are active,
and `repairDone` enters `accept`/`reject`.

The existing exact validation/rewind execution theorem still reaches the now
active `startMutation` boundary at its finite prefix time with the complete tape
unchanged.  This A1 slice is **Infrastructure** and does not yet execute cursor
installation, a unary decrement, the `j → j+1` loop, restoration, output, or
acceptance; those genuine execution theorems are isolated in T1b-A2/T1c.

**T1b-A1 review-surface hardening:** headline semantic probes in
`Tests/TMTrueUniformSeekSurfaceTests.lean` are `theorem check_*` restatements:
the forward macrostep and scan quantify the latch, and the cursor-position
probe pins the exact marker equation.  The remaining T1b-A1 `#check` entries
pin declaration existence only; their theorem bodies are covered by the
corresponding `Tests/AxiomsAudit.lean` roots.  `t1CS_frame_macrostep` and
`t1CS_scan_frames` take the latch as an explicit argument rather than an
`optParam`, so callers cannot silently select only the `latch = false` instance.
`t1MutationFrames_getElem?_cursor` puts `t1CursorFrameIndex`'s arithmetic under
the kernel.  `t1CursorBase` remains a pure bounded-layout definition; any
machine execution that reads or writes at that physical address is deferred to
the T1b-A2 slice.
The control-table bodies, the frame ABI, the clock and every pre-existing proof
are untouched: the only new content is that cursor-position theorem, and the
only signature change is the two now-explicit latch arguments.

The earlier A1 review decision to keep `t1PhysicalBitsAt_flatMap` private is
superseded now that the dependent A2 mutation execution has concrete consumers.
The helper is intentionally public as the list-backed frame-locality bridge
used by those proofs; it does not state arbitrary-tape acceptance or a machine
runtime bound.

### Session 2 — `writeVecOfNatProgram`
**File:** new
`pnp3/Complexity/TMVerifier/TuringToolkit/RowInputWriter.lean`
**LOC:** ~300
**Building blocks:** `incrementProgram_correct`,
`CopyAtOffset.copyAtOffsetProgram_run_full`
**Deliverable:** `writeVecOfNatProgram` + the `_run_full` theorem:
after `timeBound N` steps, the tape region `[Δrow .. Δrow+m)` equals
`vecOfNat n i`.
**Acceptance:** theorem closed; module registered in
`lakefile.lean`.

### Session 3 — `mcspCheckAllRows_correct`
**File:**
`pnp3/Complexity/TMVerifier/TuringToolkit/RowConsistencyCheck.lean`
(extension)
**LOC:** ~450
**Building blocks:** Session 1 (`seqList_run_full`),
`circuitEvaluatorCS_run_correct_wf`, Session 2
(`writeVecOfNat`), `rowConsistencyCheckCSAt_row` (line 69)
**Deliverable:** `tape[Δflag]` after the run =
`List.any (List.ofFn …) inconsistent_at_row_i`.
**Acceptance:** theorem + axiom audit.

### Session 4 — Witness decoder
**File:** new
`pnp3/Complexity/TMVerifier/TuringToolkit/WitnessDecoder.lean`
**LOC:** ~250
**Building blocks:** `Encoding.lean` table layout,
`CopyAtOffset.copyAtOffsetProgram_run_full`
**Deliverable:**
`decodeCandidateSpec : Bitstring (certLen) → Option (CandidateSpec n)` +
`decodeCandidateSpec_writeToTape_run_full` (writes the gate table
into the tape region) +
`decodeCandidateSpec_surjective_on_valid_candidates`.
**Acceptance:** both theorems closed.

### Session 5 — Length probe
**File:** new
`pnp3/Complexity/TMVerifier/TuringToolkit/LengthProbe.lean`
**LOC:** ~250
**Building blocks:** `incrementProgram_correct` (doubling),
`UnaryAtOffset` for compare
**Deliverable:** `canonicalLengthCheckProgram` reads `m` from the
standard `w` slot and checks `n = 2·2^m` via walk + compare; returns
`(m, true)` or `false`.
**Acceptance:** `canonicalLengthCheckProgram_run_full` closed.

### Session 6 — Top-level composition
**File:** new
`pnp3/Complexity/TMVerifier/TuringToolkit/CanonicalVerifierTM.lean`
**LOC:** ~500
**Building blocks:** sessions 1–5,
`decideAsymptotic_at_inputLen`, `decideAsymptotic_of_not_canonical`
**Deliverable:** `verifierProgram` + `verifierProgram_accepts_iff`:
```
TM.accepts (concatBitstring x w) = true ↔ candidateValid w ∧ decideAsymptotic n x = true
```
The non-canonical branch rejects via
`decideAsymptotic_of_not_canonical`.
**Acceptance:** theorem + full build.

### Session 7 — Runtime bound + Components term
**Files:**
- new `pnp3/Magnification/CanonicalAsymptoticVerifierInstance.lean`;
- edit `pnp3/Magnification/CanonicalAsymptoticDecider.lean` (struct +
  witness body, Variant B switch);
- edit
  `pnp3/Complexity/TMVerifier/GapMCSPVerifier.lean`
  (documentation);
- edit `pnp3/Tests/CanonicalIntegrationTests.lean` (adapt examples to
  the new structure).

**LOC:** ~450
**Building blocks:** `seqList_timeBound_le_uniform`,
`mcspCheckAllRows_timeBound_le` (line 213), session 6
**Deliverable:**
1. `verifierProgram_runTime_poly` with explicit `c`, `k`.
2. `canonicalAsymptoticVerifierComponents : CanonicalAsymptoticVerifierComponents`
   (Variant B).
3. `witness` body rewritten through the existential rewrite.

**Acceptance:** `def canonicalAsymptoticVerifierComponents`
typechecks; `#print axioms` ⊆
`{propext, Classical.choice, Quot.sound}`; all `canonical_*` theorems
in `CanonicalIntegrationTests.lean` are now unconditional (after
applying `witness` to the new term).

## 4. Critical files (reusable pieces)

- `pnp3/Complexity/TMVerifier/TuringToolkit/BinaryCounter.lean:1315`
  — `incrementProgram_correct`
- `pnp3/Complexity/TMVerifier/TuringToolkit/CombineAtOffset.lean:1037`
  — `combineAtOffsetCS_run_full`
- `pnp3/Complexity/TMVerifier/TuringToolkit/GateWrappers.lean:5034`
  — `circuitEvaluatorCS_run_correct_wf`
- `pnp3/Complexity/TMVerifier/TuringToolkit/GateWrappers.lean:577`
  — `seqList_timeBound_le_uniform`
- `pnp3/Complexity/TMVerifier/TuringToolkit/ConstStatePhasedProgram.lean:414-544`
  — `runConfig_seq_succ_*` (for session 1)
- `pnp3/Complexity/TMVerifier/TuringToolkit/RowConsistencyCheck.lean:69,175,213`
  — row primitives
- `pnp3/Magnification/CanonicalAsymptoticDecider.lean:192,206,223,244,271,296`
  — decider + bridge
- `pnp3/Models/Model_PartialMCSP.lean:883`
  — `GapPartialMCSP_Asymptotic_TMWitness`

## 5. Per-session verification checklist

At the end of each session:

1. **Build PnP3:**
   ```
   export PATH="$HOME/.elan/bin:$PATH" && cd /home/user/p-np2 && lake build PnP3
   ```
   Must pass with no errors and no `sorry` warnings.

2. **Axiom audit** for new top-level theorems: add `#print axioms T`
   to `scripts/audit_canonical_axioms.lean` and confirm the output is
   ⊆ `{propext, Classical.choice, Quot.sound}`.

3. **scripts/check.sh:**
   ```
   bash /home/user/p-np2/scripts/check.sh
   ```
   Exit 0.

4. **Integration regression:**
   `pnp3/Tests/CanonicalIntegrationTests.lean` must compile.  Session
   7 requires adapting the examples.

5. **Zero sorry / zero axiom policy:**
   `grep -c "sorry\|admit" pnp3/**/*.lean` stays 0; no new `axiom`
   declarations.

6. **Commit + push:** one session = one commit with an explicit
   message `Session N: <leaf theorem name>`, push to
   `claude/audit-hnpbridge-interface-FnO1v`.

## 6. Cross-session risk register

- **Session 1:** `seqList_run_full` needs a flexible motive parameter
  `Configuration → S → Prop`; otherwise we have to re-prove at every
  call site.  Mitigation: model on `runConfig_seq_succ_P2_*` (lines
  488–544) with an explicit state predicate.
- **Session 3:** `OR_{i<2^m}` may cause a
  `Decidable.decide`-vs-`Bool` mismatch with
  `circuitEvaluatorCS_run_correct_wf`.  Mitigation: formulate `OR`
  via `List.any` from the start.
- **Session 7:** changing `accepts_eq` is a breaking API change.  A
  grep shows only `Tests/CanonicalIntegrationTests.lean` (lines
  124–152) and `GapMCSPVerifier.lean` (lines 91–101) — both must be
  updated atomically in the same session.

## 7. Final state after session 7

- `Pnp3.Magnification.canonicalAsymptoticVerifierComponents` — a
  concrete term.
- `Pnp3.Magnification.CanonicalAsymptoticVerifierComponents.witness canonicalAsymptoticVerifierComponents`
  — a concrete `GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec`.
- All `canonical_*_of_TM` theorems in `CanonicalIntegrationTests.lean`
  are instantiated on this witness and become unconditional.
- The canonical asymptotic track is closed unconditionally.  The only
  remainder is the research-level `ResearchGapWitness.dagSeparation`
  (a separate problem, not part of the TM verifier).

**Total estimated work:** 7 sessions × ~350 LOC ≈ 2500 LOC of new
engineering plus ~50 LOC of edits to the bridge structure.
