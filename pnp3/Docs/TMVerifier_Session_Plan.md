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
  T2b-2 below) `g1RoundRouteFrames`, the route up to the deferred
  positive-index boundary — each with a split lemma saying the prefix followed
  by the rest of the word is literally `encodeG1Frames r ++ [.blank]`.  No
  producer annotation, no scratch region, no marker.

This layer is **table- and frame-level only**, and it is **Infrastructure**.
Nothing in it is a `TM.runConfig` statement: the exact executions from the real
`G1M.initialConfig (g1Point (encodeG1 r))` — the per-tag route capstones, the
`const` literal store, the zero-index operand-2 read and its out-of-range
boundary — are the T2b-2 layer below and are claimed nowhere here.  Also
claimed nowhere in T2b-1:

* **the destructive index walk** — for `arg2 > 0` the table sends the operand
  walk to `bRoundStart` (`g1_bScan_index_deferred`), which is idle and stuck
  (`g1_bRoundStart_stuck`), and no execution theorem passes it.  Nothing here
  claims general runtime-index addressing;
* **pass A, combine, write, repair, acceptance** — `readAStart`,
  `combineStart` and `readAResetStart` are idle rows; there is still no
  `TM.run`, `TM.accepts`, output-write, `spec`-correctness or full-clock
  theorem.

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

Six exact endpoints, each pinning head, state **and** tape (`n` abbreviates
`(encodeG1 r).length`, `u` abbreviates `r.tag.units`):

| hypotheses on `r` | steps | endpoint state | head |
|---|---|---|---|
| `Canonical`, `tag ∈ {input, not}` | `g1ReadARouteSteps r = 2n+9 + 4*(u+2)` | `readAStart`, `g1Ctx0` | `4*(u+2)` |
| `Canonical`, `tag = const`, `spec = some b` | `g1ConstRouteSteps r = 2n+9 + 4*(u+arg1+3) + 1` | `combineStart`, `vB = b` | `4*(u+arg1+3)` |
| `Canonical`, `tag ∈ {and, or}` | `g1FieldRouteSteps r = 2n+9 + 4*(u+arg1+3)` | `bScan`, `g1Ctx0` | `4*(u+arg1+3)` |
| `Canonical`, `tag ∈ {and, or}`, `arg2 = 0`, `vals[arg2]? = some b` | `g1ReadBSteps r = 2n+9 + 4*(u+arg1+5) + 1` | `readAResetStart`, `vB = b` | `4*(u+arg1+5)` |
| `Canonical`, `tag ∈ {and, or}`, `arg2 = 0`, `vals[arg2]? = none` | `g1ReadBOOBSteps r = 2n+9 + 4*(u+arg1+5)` | `bOOB`, `g1Ctx0` (stable) | `4*(u+arg1+5)` |
| `Canonical`, `tag ∈ {and, or}`, `arg2 = k+1` | `g1RoundRouteSteps r = 2n+9 + 4*(u+arg1+4)` | `bRoundStart`, `g1Ctx0` (idle) | `4*(u+arg1+4)` |

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
deferred boundary) with literal step counts, purely as an audit surface.  Every
step count is bounded by the **unchanged** clock
`g1Clock N = 512 * (N + 1) ^ 2 + 512` through `g1_readB_steps_le_clock`; the
clock is neither widened nor restated, and these are budget facts about the
proved prefixes only, **not** a full-clock theorem.

**Both stopping points are boundaries, not verdicts.**  `bOOB` records that the
operand index selects nothing: it is stable for every further budget
(`g1CS_readB_zero_oob_stable`), it stores nothing in `vB`, and it is a different
state from both the success handoff (`g1CS_readB_zero_oob_ne_success`) and the
reject sink (`g1CS_readB_oob_ne_reject`); no acceptance or rejection semantics
is attached to it.  `bRoundStart` is the deferred entry point of the destructive
index walk: for `arg2 > 0` the machine provably reaches it and provably never
leaves it (`g1CS_readB_round_deferred_stable`, for every further budget).

**Explicitly deferred, and claimed nowhere:** the **destructive positive-index
walk** (the physically executed operand-2 read is exactly the zero-index one;
for `arg2 > 0` the proved endpoint *is* the `bRoundStart` boundary, so no
general runtime-index addressing is claimed); **pass A, combine, output write
and repair** (`readAStart`, `combineStart` and `readAResetStart` are idle rows,
proved idle for every budget by `g1CS_runConfig_readA_idle`,
`g1CS_runConfig_combine_idle`, `g1CS_runConfig_readAReset_idle`, and nothing
consumes the `G1Ctx.vB` value they carry); **acceptance/rejection semantics,
full run and full clock** (no `TM.run`, no `TM.accepts`, no `spec`-correctness
and no full-clock theorem — none could honestly exist while five handoffs are
idle); **padded tapes** (as in T1 and T2a every execution statement is scoped to
the exact tape `encodeG1 r`); and the **`SLGate` bridge, multi-gate evaluator
and verifier obligation**, unchanged from T2a.

Modules: `GateOneReadB.lean` (execution) and `GateOneReadBExamples.lean` (named
examples), both registered in `lakefile.lean`; `GateOneRouting.lean` gains only
the frame-level deferred route `g1RoundRouteFrames` with its split, fold and
valid-path lemmas, and `GateOneControl.lean` only a docstring correction.
Pinned by `Tests/TMGateOneReadBSurfaceTests.lean` (`#check` plus exact `check_*`
contract wrappers) and audited by `Tests/AxiomsAudit.lean`; the observed cone of
every new declaration is `[propext, Classical.choice, Quot.sound]` or a subset,
with no trusted-compiler reduction axiom.  No existing theorem was weakened,
restated or removed.

This slice is **Infrastructure**, not P-vs-NP mainline progress: it is a
finite-control tape-reading capability, not a gate evaluator, not a content
verifier and not a lower bound.

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
