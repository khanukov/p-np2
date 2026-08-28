import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram
import Complexity.TMVerifier.TuringToolkit.GateOneEncoding
import Mathlib.Tactic.DeriveFintype

/-!
# G1: the one fixed zero-parameter finite control

**Progress classification: Infrastructure.**  One `ConstStatePhasedProgram`,
the frame-level language of its forward table, and the standalone tuple lemmas
of its transition table.  No execution trace, no addressing, no acceptance, no
gate semantics.

There is exactly one program declaration, `g1CS`, and it takes no arguments.
`G1State` is a mode, a frame position, a three-cell frame buffer and a
three-Boolean context: **no `Nat`, index, width, offset, data length or other
request-dependent value occurs in it**.  The clock
`g1Clock N = 512 * (N + 1) ^ 2 + 512` mentions only the physical input length.

## The forward table decides the canonical grammar

The sixteen forward modes remember the tag count and, through it, the tag
kind, so the tag-dependent arity/unused-field convention of
`G1Request.Canonical` is enforced by the finite control itself and not merely
by the pure parser:

* `vTag0 … vTag5` count the unary tag run.  `vTag0` rejects an `argSep`
  (empty tag run) and `vTag5` rejects a further `tag` (six units), so exactly
  the legal run lengths `1 … 5` survive.
* the `argSep` leaving `vTagk` selects the operand regime of that tag:
  `vTag1` (`input`) and `vTag3` (`not`) enter `vArg1Unary`, `vTag2` (`const`)
  enters `vConst0`, and `vTag4`/`vTag5` (`and`/`or`) enter `vArg1Binary`.
* `vArg1Unary` and `vArg1Binary` loop on `index`; `vConst0` accepts at most one
  `index` (`vConst1` rejects a second), which is exactly the `arg1 ≤ 1`
  convention of `const`.
* an arity-1 tag lands in `vArg2Zero`, which accepts only the `separator` and
  rejects any `index`, which is exactly the `arg2 = 0` convention; an arity-2
  tag lands in `vArg2Any`, which loops on `index`.

`g1Automaton_accepts_iff_decode` proves the resulting frame-level language is
**exactly** the language of the pure parser, and
`g1CanonicalEncoderAutomatonTrace_iff` specialises it to the encoder: the
forward run of `encodeG1Frames r` plus the explicit trailing blank frame
reaches `rewindStart` if and only if `r.Canonical`.  In particular every
noncanonical encoded request ends in `reject`; arbitrary-frame behavior is
stated only through the explicit table/path theorems below.

`Canonical` enforces frame grammar and unused-field conventions only.  Operand
bounds belong to `G1Request.WellFormed` and are deferred to pass B.

Both statements are scoped to explicit *frame words* closed by one trailing
blank frame.  Nothing is claimed about arbitrary padded physical tapes.

## Motion

The control performs read-only canonical grammar validation of the whole word
plus one trailing blank frame, then rewinds right-to-left to head zero and
enters `readBStart`.  The forward modes (`vBof … vBlank`) read frames left to
right through the shared `g1Advance` table and are therefore an instance of the
generic frame-scanner kernel (`GateOneScanner`); `rewindStart`/`rewind` read
right to left and have their own tuple lemmas.

`readBStart` is **no longer idle**: the T2b-1 slice activates it as a genuine
forward frame-reading mode.  From head zero it re-reads the anchor and
*physically rescans* the unary tag run (`rTag0 … rTag5`) — the tag is not
retained anywhere across the rewind, and it is not a parameter of anything —
and the `argSep` that closes the run selects the operand regime a second time:

* `rTag1` (`input`) and `rTag3` (`not`) hand off directly to `readAStart`, with
  the head exactly on the first cell of the operand-1 field — the `argSep`
  closing that field when it is empty;
* `rTag2` (`const`) enters `rConst0`, which decodes the canonical unary literal
  (`argSep` at once ↦ `constFalse`, one `index` then `argSep` ↦ `constTrue`)
  and stores it in the fixed Boolean field `G1Ctx.vB` on the way to
  `combineStart`;
* `rTag4`/`rTag5` (`and`/`or`) enter `rArg1Binary`, which skips the operand-1
  field and stops on the `argSep` that opens the **operand-2 field**, entering
  `bScan`.

`bScan` walks the operand-2 region (only `spent` frames are skipped) to the
`separator`; a `data` frame before that separator is malformed and rejects.
At the separator it enters `bProbe`, which reads the selected data frame:
`data b` stores `b` in `vB` through `bStoreFalse`/`bStoreTrue` and hands off to
`readAResetStart`, while the `output` destination frame means the index ran off
the end of the data region and hands off to the stable `bOOB` boundary.

## The positive-index branch: the installation scan

`bScan` reaching an *unspent* `index` frame means the operand-2 index is
non-zero.  This slice **re-points** that single row: `bScan + index` now enters
`bInsSeek`, the read-only **installation scan**, which crosses the rest of the
operand-2 field (`index` and `spent` alike), crosses the `separator` and stops
at `bProbe2` on the first cell after the separator, the start of the data
region.  Four `g1Advance` rows
and two new modes, and that is all:

```text
bScan    + index     ↦ bInsSeek     (the re-pointed row)
bInsSeek + index     ↦ bInsSeek
bInsSeek + spent     ↦ bInsSeek
bInsSeek + separator ↦ bProbe2
```

Both modes are ordinary *forward* frame-reading modes, so they need no
`g1Transition` rows of their own: their steps are the four
`g1Transition_forward_*` lemmas below.  The executed form of the route is
`GateOneInstallScan.g1CS_readB_install_scan_exact`.

**`bProbe2` is an explicit local boundary of this slice.**  It has **no**
outgoing `g1Advance` row here, so it completes every frame into `reject` and is
therefore `G1Stuck` (`GateOneRouting.g1_bProbe2_stuck`).  No theorem of this
development runs the machine out of it: the installation scan's endpoint is the
last thing proved on this branch.  Reading the selected data bit there, latching
it into `G1Ctx.vB` and installing the data cursor need the **fourteen remaining
cursor-walk modes** — the reverse seek and its two outcomes, the
`index ↦ spent` writer, the forward scan and the two turns, the four restore
writers, the two latch dispatches and the leftward cursor writer — together with
their `g1Advance`/`g1Transition` rows and tuple lemmas.  All of that, and every
execution of the latch, the cursor install or a walk round, is **PR2**; none of
it is present or claimed here.

## The rewrite-cycle bridge, retained only as a regression

`bRoundStart`/`bWalk`/`bMark`/`bBack`/`bHop` are the earlier one-step bridge and
its thirteen-step `index ↦ spent` round (`4 + 4 + 4 + 1 = 13`, so bridge plus
round is fourteen).  After the re-point they are **unreachable from the forward
table**: no mode/frame pair completes into `bRoundStart`
(`GateOneRouting.g1_bRoundStart_unreachable`).  Their rows and tuple lemmas
survive only so that the generic rewrite-cycle composition of
`FrameRewriteCycleInstances` and `GateOneIndexRound` keeps a regression on a
**caller-supplied** configuration.  Nothing composes them from
`G1M.initialConfig`, and nothing claims that repeating that cycle addresses an
operand-2 value: `bWalk` stops on *any* `index`, so once the operand-2 field
empties it would cross the opening `argSep` and consume operand-1 units.  That
is the failure the PR2 walk is designed to rule out.

**What is deferred.**  `readAStart`, `combineStart` and `readAResetStart` are
idle handoffs in this slice.  `bOOB` is a stable read boundary, distinct from
the reject state, rather than a rejection verdict.  There is **no full-clock or
acceptance theorem** — the public clock is unchanged and only the proved
prefixes are bounded.  `accept`/`reject` are the two stable sinks; only their
tuple equations are proved.

**Proof discipline.**  Everything below `g1Transition` is a small standalone
tuple lemma proved by `rfl` after at most one mode split.  Downstream
`TM.stepConfig` facts come from the generic `ConstStatePhasedStepBridge`
corollaries (directly or through the kernel); `g1Transition` is never unfolded
inside an execution proof, and no semantic content is carried by a structure
field.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

/-- The modes of the G1 control.

`vBof … vBlank` validate the canonical grammar left to right; `vTag0 … vTag5`
carry the unary tag count (and hence the tag kind), and `vArg1Unary`,
`vConst0`/`vConst1`, `vArg1Binary`, `vArg2Zero`, `vArg2Any` carry the
tag-dependent operand convention.  `rewindStart`/`rewind` return the head to
zero.

`readBStart` opens the pass-B rescan: `rTag0 … rTag5` recount the unary tag
physically, `rConst0`/`rConst1` decode the unary `const` literal,
`rArg1Binary` skips the operand-1 field of a binary gate, and `bScan`/`bProbe`
walk the operand-2 region and read the selected data frame.

`constFalse`/`constTrue` and `bStoreFalse`/`bStoreTrue` are the four one-step
dispatch modes that write the decoded Boolean into `G1Ctx.vB`.

`bRoundStart` is the one-step bridge into the destructive round and
`bWalk`/`bMark`/`bBack`/`bHop` are its reverse read, its fixed-code write, its
back-walk and its hop; the forward table no longer enters `bRoundStart`.

`bInsSeek` is the read-only installation scan of the positive-index branch and
`bProbe2` its endpoint, the explicit local boundary of this slice.

`readAStart`, `combineStart`, `readAResetStart` and
`bOOB` are the four remaining local handoffs, idle in this slice;
`accept`/`reject` are the sinks. -/
inductive G1Mode
  | vBof
  | vTag0 | vTag1 | vTag2 | vTag3 | vTag4 | vTag5
  | vArg1Unary | vConst0 | vConst1 | vArg1Binary
  | vArg2Zero | vArg2Any
  | vData | vFinish | vBlank
  | rewindStart | rewind
  | readBStart
  | rTag0 | rTag1 | rTag2 | rTag3 | rTag4 | rTag5
  | rConst0 | rConst1 | rArg1Binary
  | bScan | bProbe
  | constFalse | constTrue | bStoreFalse | bStoreTrue
  | bRoundStart | bWalk | bMark | bBack | bHop
  -- the installation scan and its endpoint
  | bInsSeek | bProbe2
  | readAStart | combineStart | readAResetStart | bOOB
  | accept | reject
  deriving Fintype, DecidableEq, Repr

inductive G1FramePosition | p0 | p1 | p2 | p3
  deriving Fintype, DecidableEq, Repr

/-- The carried context of the G1 control.  `pass` and `crossed` remain inert in
this slice.  `vB` is written by the dispatch rows and holds either the decoded
`const` literal or the operand-2 value read from the data region.  All fields
are part of the fixed finite state; adding state later would change the machine. -/
structure G1Ctx where
  pass : Bool
  crossed : Bool
  vB : Bool
  deriving Fintype, DecidableEq, Repr

def g1Ctx0 : G1Ctx := ⟨false, false, false⟩

/-- **The one place a resolved Boolean is stored.**  `vB` is the fixed Boolean
field of the finite context that holds the decoded `const` literal or the
value read out of the data region; nothing else in the state changes. -/
def G1Ctx.withVB (ctx : G1Ctx) (b : Bool) : G1Ctx := { ctx with vB := b }

@[simp] theorem G1Ctx.withVB_vB (ctx : G1Ctx) (b : Bool) :
    (ctx.withVB b).vB = b := rfl

@[simp] theorem G1Ctx.withVB_pass (ctx : G1Ctx) (b : Bool) :
    (ctx.withVB b).pass = ctx.pass := rfl

@[simp] theorem G1Ctx.withVB_crossed (ctx : G1Ctx) (b : Bool) :
    (ctx.withVB b).crossed = ctx.crossed := rfl

theorem g1Ctx0_withVB (b : Bool) : g1Ctx0.withVB b = ⟨false, false, b⟩ := rfl

set_option synthInstance.maxSize 1024 in
/-- The complete G1 control state.  No `Nat`, width, offset, index or length
field occurs. -/
structure G1State where
  mode : G1Mode
  position : G1FramePosition
  b0 : Bool
  b1 : Bool
  b2 : Bool
  ctx : G1Ctx
  deriving Fintype, DecidableEq, Repr

def g1State (mode : G1Mode) (position : G1FramePosition)
    (b0 := false) (b1 := false) (b2 := false) (ctx : G1Ctx := g1Ctx0) :
    G1State :=
  ⟨mode, position, b0, b1, b2, ctx⟩

def g1AcceptState : G1State := g1State .accept .p0
def g1RejectState : G1State := g1State .reject .p0

/-- The local pass-B handoff state, with all scratch and context bits at their
documented values. -/
def g1ReadBState (ctx : G1Ctx) : G1State :=
  g1State .readBStart .p0 false false false ctx

/-- The pass-A handoff of an arity-1 gate: the head sits on the first cell of
the operand-1 field (the closing `argSep` when that field is empty). -/
def g1ReadAState (ctx : G1Ctx) : G1State :=
  g1State .readAStart .p0 false false false ctx

/-- The `const` handoff: the decoded literal is already in `ctx.vB`. -/
def g1CombineState (ctx : G1Ctx) : G1State :=
  g1State .combineStart .p0 false false false ctx

/-- The post-operand-2 handoff of a binary gate: `ctx.vB` holds the resolved
operand-2 value and the data cursor has to be reset before pass A. -/
def g1ReadAResetState (ctx : G1Ctx) : G1State :=
  g1State .readAResetStart .p0 false false false ctx

/-- **Caller-supplied regression state for the old destructive index round.**
The current forward table never reaches this state; it remains only so the
generic rewrite-cycle regression can be stated on an arbitrary configuration. -/
def g1RoundState (ctx : G1Ctx) : G1State :=
  g1State .bRoundStart .p0 false false false ctx

/-- **The reverse-aligned entry of the index round.**  Head on the last cell of
the frame about to be read right to left, frame buffer empty. -/
def g1WalkState (ctx : G1Ctx) : G1State :=
  g1State .bWalk .p3 false false false ctx

/-- **The write handoff of the index round.**  Head on the first cell of the
`index` frame the reverse read stopped on. -/
def g1MarkState (ctx : G1Ctx) : G1State :=
  g1State .bMark .p0 false false false ctx

/-- The stable out-of-range boundary of the operand read. -/
def g1OOBState (ctx : G1Ctx) : G1State :=
  g1State .bOOB .p0 false false false ctx

/-! ### The two named states of the installation scan.  Neither carries a `Nat`,
an index, an offset or a length: the scan's whole memory is the frame position,
the three-cell frame buffer and the pre-existing `G1Ctx`. -/

/-- Installation scan: head on the first cell of the frame after the first
operand-2 `index`. -/
def g1InsSeekState (ctx : G1Ctx) : G1State :=
  g1State .bInsSeek .p0 false false false ctx

/-- **The endpoint of the installation scan**, and the explicit local boundary
of this slice: head on the first cell after the separator.  That frame is data
when the region is nonempty and `output false` otherwise.  Reading it
successfully is PR2. -/
def g1Probe2State (ctx : G1Ctx) : G1State :=
  g1State .bProbe2 .p0 false false false ctx

/-- The reject sink and pass-B handoff differ.  Used by the
`GateOneValidation` rejection surface. -/
theorem g1RejectState_ne_readB (ctx : G1Ctx) :
    g1RejectState ≠ g1ReadBState ctx := by
  intro h
  have hmode : G1Mode.reject = G1Mode.readBStart := congrArg G1State.mode h
  exact G1Mode.noConfusion hmode

/-- The stable out-of-range boundary is not the success handoff. -/
theorem g1OOBState_ne_readAReset (ctx ctx' : G1Ctx) :
    g1OOBState ctx ≠ g1ReadAResetState ctx' := by
  intro h
  have hmode : G1Mode.bOOB = G1Mode.readAResetStart := congrArg G1State.mode h
  exact G1Mode.noConfusion hmode

/-- **The left-to-right frame table.**

This is the complete canonical grammar of `GateOneEncoding`: the anchor, a
unary tag run of a legal length `1 … 5`, the two `argSep`-terminated unary
index fields *under the operand convention selected by the tag count*, the
separator, the data region, the `output false` destination, the terminator,
and the trailing blank frame that marks end of input.  Every other
mode/frame pair rejects.  `g1Automaton_accepts_iff_decode` below proves this
table decides exactly the language of `decodeG1FrameList?`. -/
def g1Advance : G1Mode → G1Frame → G1Mode
  | .vBof, .bof => .vTag0
  -- the unary tag run, counted; `vTag0 + argSep` and `vTag5 + tag` reject
  | .vTag0, .tag => .vTag1
  | .vTag1, .tag => .vTag2
  | .vTag2, .tag => .vTag3
  | .vTag3, .tag => .vTag4
  | .vTag4, .tag => .vTag5
  -- leaving the tag run selects the operand convention of that tag
  | .vTag1, .argSep => .vArg1Unary   -- input
  | .vTag2, .argSep => .vConst0      -- const
  | .vTag3, .argSep => .vArg1Unary   -- not
  | .vTag4, .argSep => .vArg1Binary  -- and
  | .vTag5, .argSep => .vArg1Binary  -- or
  -- operand field 1
  | .vArg1Unary, .index => .vArg1Unary
  | .vArg1Unary, .argSep => .vArg2Zero
  | .vConst0, .index => .vConst1
  | .vConst0, .argSep => .vArg2Zero
  | .vConst1, .argSep => .vArg2Zero  -- a second `index` here rejects
  | .vArg1Binary, .index => .vArg1Binary
  | .vArg1Binary, .argSep => .vArg2Any
  -- operand field 2
  | .vArg2Zero, .separator => .vData -- an `index` here rejects
  | .vArg2Any, .index => .vArg2Any
  | .vArg2Any, .separator => .vData
  -- data region, destination, terminator, end of input
  | .vData, .data _ => .vData
  | .vData, .output false => .vFinish
  | .vFinish, .finish => .vBlank
  | .vBlank, .blank => .rewindStart
  -- the pass-B rescan: re-read the anchor and physically recount the tag run
  | .readBStart, .bof => .rTag0
  | .rTag0, .tag => .rTag1
  | .rTag1, .tag => .rTag2
  | .rTag2, .tag => .rTag3
  | .rTag3, .tag => .rTag4
  | .rTag4, .tag => .rTag5
  -- routing, decided a second time from the physically rescanned tag
  | .rTag1, .argSep => .readAStart   -- input: no operand 2, pass A next
  | .rTag2, .argSep => .rConst0      -- const: decode the unary literal
  | .rTag3, .argSep => .readAStart   -- not: no operand 2, pass A next
  | .rTag4, .argSep => .rArg1Binary  -- and
  | .rTag5, .argSep => .rArg1Binary  -- or
  -- the canonical unary `const` literal: `argSep` at once is `0`, one `index`
  -- then `argSep` is `1`; a second `index` is not canonical and rejects
  | .rConst0, .index => .rConst1
  | .rConst0, .argSep => .constFalse
  | .rConst1, .argSep => .constTrue
  -- a binary gate skips the operand-1 field and stops at the operand-2 field
  | .rArg1Binary, .index => .rArg1Binary
  | .rArg1Binary, .argSep => .bScan
  -- the operand-2 walk: spent index units are skipped; the separator opens
  -- the probe.  A data frame before the separator is malformed and rejects.
  | .bScan, .spent => .bScan
  | .bScan, .separator => .bProbe
  | .bScan, .index => .bInsSeek      -- a non-zero index: enter installation scan
  -- the probe reads the selected data frame, or runs off the data region
  | .bProbe, .data false => .bStoreFalse
  | .bProbe, .data true => .bStoreTrue
  | .bProbe, .output false => .bOOB
  -- the installation scan: cross the rest of the operand-2 field and the
  -- `separator`, stopping at `bProbe2` on the *first* data frame.  `bProbe2`
  -- has no row of its own in this slice: it is the explicit local boundary,
  -- and its successors are PR2.
  | .bInsSeek, .index => .bInsSeek
  | .bInsSeek, .spent => .bInsSeek
  | .bInsSeek, .separator => .bProbe2
  | _, _ => .reject

/-- The bit-level form of `g1Advance`, as the control table computes it. -/
def g1Complete (mode : G1Mode) (b0 b1 b2 b3 : Bool) : G1Mode :=
  match decodeG1Frame? [b0, b1, b2, b3] with
  | some frame => g1Advance mode frame
  | none => .reject

/-- The modes that read one frame left to right through `g1Advance`.  The
validation scan (`vBof … vBlank`), the pass-B rescan (`readBStart`,
`rTag0 … rTag5`, `rConst0`/`rConst1`, `rArg1Binary`, `bScan`, `bProbe`) and the
installation scan (`bInsSeek`, `bProbe2`) are forward modes; the rewind, the
four dispatch modes, the five modes of the destructive round, the four remaining
handoffs and the two sinks are not.

`bProbe2` is forward *and* `G1Stuck` in this slice: the shared forward control
can read its four cells, but the table gives it no successful frame row, so a
completed frame enters `reject`.  No theorem executes that read.  This is what
makes it an explicit boundary and
not a claim; PR2 supplies its rows. -/
def G1ForwardMode : G1Mode → Prop
  | .rewindStart | .rewind
  | .constFalse | .constTrue | .bStoreFalse | .bStoreTrue
  | .bRoundStart | .bWalk | .bMark | .bBack | .bHop
  | .readAStart | .combineStart | .readAResetStart | .bOOB
  | .accept | .reject => False
  | _ => True

instance : DecidablePred G1ForwardMode := fun mode => by
  cases mode <;> first | exact isTrue trivial | exact isFalse id

theorem G1ForwardMode.not_reject : ¬ G1ForwardMode .reject := id

theorem G1ForwardMode.not_rewindStart : ¬ G1ForwardMode .rewindStart := id

theorem G1ForwardMode.readBStart : G1ForwardMode .readBStart := trivial

/-- **Stuck modes.**  A mode from which the forward table can read nothing: it
completes every frame into `reject`, and it is not the end-of-input mode.  In
particular the four dispatch modes, the five modes of the destructive round,
the installation scan's endpoint `bProbe2`,
the four remaining handoffs and the `reject` sink are
stuck; `rewind` and `accept` also satisfy this table-level predicate but are
unreachable as results of `g1Advance`;
the point of the predicate is that a stuck mode can never fold to
`rewindStart`, which is what keeps the validation grammar proofs of this module
independent of the pass-B rows added above. -/
def G1Stuck (mode : G1Mode) : Prop :=
  (∀ f : G1Frame, g1Advance mode f = .reject) ∧ mode ≠ .rewindStart

instance (mode : G1Mode) : Decidable (G1Stuck mode) :=
  inferInstanceAs
    (Decidable ((∀ f : G1Frame, g1Advance mode f = .reject) ∧
      mode ≠ .rewindStart))

/-! ## The frame-level language of the forward table

`g1AdvanceList` is the fold of `g1Advance` over a frame word; `GateOneScanner`
proves it is literally the generic scanner kernel's `advanceList`, so the
grammar results proved here transfer verbatim to the executable scan.  Nothing
in this section mentions a Turing machine. -/

/-- Fold the forward frame table over a frame word. -/
def g1AdvanceList : G1Mode → List G1Frame → G1Mode
  | mode, [] => mode
  | mode, frame :: rest => g1AdvanceList (g1Advance mode frame) rest

@[simp] theorem g1AdvanceList_nil (mode : G1Mode) : g1AdvanceList mode [] = mode :=
  rfl

@[simp] theorem g1AdvanceList_cons (mode : G1Mode) (frame : G1Frame)
    (rest : List G1Frame) :
    g1AdvanceList mode (frame :: rest) =
      g1AdvanceList (g1Advance mode frame) rest := rfl

theorem g1AdvanceList_append (mode : G1Mode) (fs gs : List G1Frame) :
    g1AdvanceList mode (fs ++ gs) =
      g1AdvanceList (g1AdvanceList mode fs) gs := by
  induction fs generalizing mode with
  | nil => rfl
  | cons frame rest ih => simpa using ih (g1Advance mode frame)

/-- `reject` is a sink of the frame table. -/
theorem g1Advance_reject (frame : G1Frame) :
    g1Advance .reject frame = .reject := by revert frame; decide

/-- Nothing follows the end-of-input frame. -/
theorem g1Advance_rewindStart (frame : G1Frame) :
    g1Advance .rewindStart frame = .reject := by revert frame; decide

@[simp] theorem g1AdvanceList_reject (fs : List G1Frame) :
    g1AdvanceList .reject fs = .reject := by
  induction fs with
  | nil => rfl
  | cons frame rest ih => rw [g1AdvanceList_cons, g1Advance_reject]; exact ih

/-- A stuck mode can never fold to the end-of-input mode. -/
theorem g1AdvanceList_ne_rewindStart_of_stuck {mode : G1Mode} (h : G1Stuck mode)
    (fs : List G1Frame) : g1AdvanceList mode fs ≠ .rewindStart := by
  cases fs with
  | nil => exact h.2
  | cons frame rest =>
      rw [g1AdvanceList_cons, h.1 frame, g1AdvanceList_reject]
      decide

/-- **The forward table only ever produces a forward mode, `rewindStart`, or a
stuck mode.**  In particular `rewind` and `accept` are unreachable from any
scan.  Every non-forward target (the four dispatch modes, the round's five
modes, the four idle handoffs and the `reject` sink) is stuck; the forward
boundary `bProbe2` is separately stuck because it has no successful frame row. -/
theorem g1Advance_range (mode : G1Mode) (frame : G1Frame) :
    G1ForwardMode (g1Advance mode frame) ∨
      g1Advance mode frame = .rewindStart ∨
      G1Stuck (g1Advance mode frame) := by
  revert mode frame; decide

/-- Neither sink-like control mode is ever produced by one frame-table step. -/
theorem g1Advance_ne_sink (mode : G1Mode) (frame : G1Frame) :
    g1Advance mode frame ≠ .accept ∧ g1Advance mode frame ≠ .rewind := by
  revert mode frame
  decide

/-- Once the end-of-input frame has been consumed, an accepting word is over. -/
theorem g1AdvanceList_rewindStart_eq_nil {fs : List G1Frame}
    (h : g1AdvanceList .rewindStart fs = .rewindStart) : fs = [] := by
  cases fs with
  | nil => rfl
  | cons frame rest =>
      rw [g1AdvanceList_cons, g1Advance_rewindStart, g1AdvanceList_reject] at h
      exact absurd h (by decide)

/-- A rejected first frame kills the whole word. -/
theorem g1AdvanceList_cons_ne_of_reject {mode : G1Mode} {frame : G1Frame}
    (rest : List G1Frame) (hf : g1Advance mode frame = .reject) :
    g1AdvanceList mode (frame :: rest) ≠ .rewindStart := by
  rw [g1AdvanceList_cons, hf, g1AdvanceList_reject]
  decide

/-! ### Path predicates

`G1ValidPath` and `G1RejectPath` are the local forms of "the forward control
reads this whole word" and "the forward control reads a prefix of this word and
then rejects".  Both are what the executable scan of `GateOneValidation`
consumes: the first drives the generic kernel's frame scan, the second drives
the exact noncanonical rejection trace.  Neither mentions a Turing machine. -/

/-- A frame word is a valid path from `mode` when every frame is read in a
forward mode and never completes into `reject`. -/
def G1ValidPath : G1Mode → List G1Frame → Prop
  | _, [] => True
  | mode, frame :: rest =>
      G1ForwardMode mode ∧ g1Advance mode frame ≠ .reject ∧
        G1ValidPath (g1Advance mode frame) rest

/-- A frame word is a *rejecting* path from `mode` when the forward control
reads frames in forward modes until some frame completes into `reject`. -/
def G1RejectPath : G1Mode → List G1Frame → Prop
  | _, [] => False
  | mode, frame :: rest =>
      G1ForwardMode mode ∧
        (g1Advance mode frame = .reject ∨
          G1RejectPath (g1Advance mode frame) rest)

theorem G1RejectPath.forward {mode : G1Mode} {fs : List G1Frame}
    (h : G1RejectPath mode fs) : G1ForwardMode mode := by
  cases fs with
  | nil => exact h.elim
  | cons frame rest => exact h.1

/-- A rejecting path really does fold to the `reject` sink. -/
theorem g1AdvanceList_eq_reject_of_rejectPath {mode : G1Mode}
    {fs : List G1Frame} (h : G1RejectPath mode fs) :
    g1AdvanceList mode fs = .reject := by
  induction fs generalizing mode with
  | nil => exact h.elim
  | cons frame rest ih =>
      rcases h with ⟨-, hr | hr⟩
      · rw [g1AdvanceList_cons, hr, g1AdvanceList_reject]
      · rw [g1AdvanceList_cons]; exact ih hr

/-! ### Three generic decomposition lemmas

Each says: from a mode whose only non-rejecting frames are the listed ones, an
accepting word *must* start with the corresponding shape. -/

/-- One forced frame. -/
theorem g1_step_split {mode next : G1Mode} {frame : G1Frame}
    (hmode : mode ≠ .rewindStart) (hstep : g1Advance mode frame = next)
    (hother : ∀ f : G1Frame, f ≠ frame → g1Advance mode f = .reject)
    {fs : List G1Frame} (h : g1AdvanceList mode fs = .rewindStart) :
    ∃ tail, fs = frame :: tail ∧ g1AdvanceList next tail = .rewindStart := by
  cases fs with
  | nil => exact absurd h hmode
  | cons f rest =>
      rw [g1AdvanceList_cons] at h
      by_cases hf : f = frame
      · subst hf; rw [hstep] at h; exact ⟨rest, rfl, h⟩
      · rw [hother f hf, g1AdvanceList_reject] at h; exact absurd h (by decide)

/-- Two forced alternatives. -/
theorem g1_two_split {mode nextA nextB : G1Mode} {frameA frameB : G1Frame}
    (hmode : mode ≠ .rewindStart) (hA : g1Advance mode frameA = nextA)
    (hB : g1Advance mode frameB = nextB)
    (hother : ∀ f : G1Frame, f ≠ frameA → f ≠ frameB →
      g1Advance mode f = .reject)
    {fs : List G1Frame} (h : g1AdvanceList mode fs = .rewindStart) :
    (∃ tail, fs = frameA :: tail ∧ g1AdvanceList nextA tail = .rewindStart) ∨
      (∃ tail, fs = frameB :: tail ∧
        g1AdvanceList nextB tail = .rewindStart) := by
  cases fs with
  | nil => exact absurd h hmode
  | cons f rest =>
      rw [g1AdvanceList_cons] at h
      by_cases hfa : f = frameA
      · subst hfa; rw [hA] at h; exact Or.inl ⟨rest, rfl, h⟩
      · by_cases hfb : f = frameB
        · subst hfb; rw [hB] at h; exact Or.inr ⟨rest, rfl, h⟩
        · rw [hother f hfa hfb, g1AdvanceList_reject] at h
          exact absurd h (by decide)

/-- A unary run of one frame terminated by another. -/
theorem g1_run_split {mode next : G1Mode} {unit stop : G1Frame}
    (hmode : mode ≠ .rewindStart) (hloop : g1Advance mode unit = mode)
    (hstop : g1Advance mode stop = next)
    (hother : ∀ f : G1Frame, f ≠ unit → f ≠ stop → g1Advance mode f = .reject)
    {fs : List G1Frame} (h : g1AdvanceList mode fs = .rewindStart) :
    ∃ (k : Nat) (tail : List G1Frame),
      fs = List.replicate k unit ++ stop :: tail ∧
        g1AdvanceList next tail = .rewindStart := by
  induction fs with
  | nil => exact absurd h hmode
  | cons f rest ih =>
      rw [g1AdvanceList_cons] at h
      by_cases hu : f = unit
      · subst hu
        rw [hloop] at h
        obtain ⟨k, tail, hrest, htail⟩ := ih h
        exact ⟨k + 1, tail, by rw [List.replicate_succ, List.cons_append, hrest],
          htail⟩
      · by_cases hs : f = stop
        · subst hs; rw [hstop] at h; exact ⟨0, rest, rfl, h⟩
        · rw [hother f hu hs, g1AdvanceList_reject] at h
          exact absurd h (by decide)

/-! ### Completeness: an accepting word is a canonical encoding

The tail lemmas run from the inside out; `g1_structure_of_accepts` assembles
them, splitting five ways on the tag count. -/

theorem g1_tail_vBlank {fs : List G1Frame}
    (h : g1AdvanceList .vBlank fs = .rewindStart) : fs = [.blank] := by
  obtain ⟨tail, rfl, ht⟩ :=
    g1_step_split (mode := .vBlank) (next := .rewindStart) (frame := .blank)
      (by decide) rfl (by decide) h
  rw [g1AdvanceList_rewindStart_eq_nil ht]

theorem g1_tail_vFinish {fs : List G1Frame}
    (h : g1AdvanceList .vFinish fs = .rewindStart) : fs = [.finish, .blank] := by
  obtain ⟨tail, rfl, ht⟩ :=
    g1_step_split (mode := .vFinish) (next := .vBlank) (frame := .finish)
      (by decide) rfl (by decide) h
  rw [g1_tail_vBlank ht]

theorem g1_tail_vData {fs : List G1Frame}
    (h : g1AdvanceList .vData fs = .rewindStart) :
    ∃ vals : List Bool,
      fs = vals.map .data ++ [.output false, .finish, .blank] := by
  induction fs with
  | nil => exact absurd h (by decide)
  | cons frame rest ih =>
      cases frame with
      | data b =>
          obtain ⟨vals, hrest⟩ :=
            ih (by rw [g1AdvanceList_cons] at h; cases b <;> exact h)
          exact ⟨b :: vals, by rw [List.map_cons, List.cons_append, hrest]⟩
      | output b =>
          cases b with
          | false =>
              rw [g1AdvanceList_cons] at h
              exact ⟨[], by rw [g1_tail_vFinish h]; rfl⟩
          | true => exact absurd h (g1AdvanceList_cons_ne_of_reject rest rfl)
      | blank | bof | tag | index | separator | cursor | finish | argSep
      | spent => exact absurd h (g1AdvanceList_cons_ne_of_reject rest rfl)

theorem g1_tail_vArg2Zero {fs : List G1Frame}
    (h : g1AdvanceList .vArg2Zero fs = .rewindStart) :
    ∃ vals : List Bool,
      fs = .separator :: (vals.map .data ++ [.output false, .finish, .blank]) := by
  obtain ⟨tail, rfl, ht⟩ :=
    g1_step_split (mode := .vArg2Zero) (next := .vData) (frame := .separator)
      (by decide) rfl (by decide) h
  obtain ⟨vals, hvals⟩ := g1_tail_vData ht
  exact ⟨vals, by rw [hvals]⟩

theorem g1_tail_vArg2Any {fs : List G1Frame}
    (h : g1AdvanceList .vArg2Any fs = .rewindStart) :
    ∃ (a2 : Nat) (vals : List Bool),
      fs = List.replicate a2 .index ++ .separator ::
        (vals.map .data ++ [.output false, .finish, .blank]) := by
  obtain ⟨a2, tail, rfl, ht⟩ :=
    g1_run_split (mode := .vArg2Any) (next := .vData) (unit := .index)
      (stop := .separator) (by decide) rfl rfl (by decide) h
  obtain ⟨vals, hvals⟩ := g1_tail_vData ht
  exact ⟨a2, vals, by rw [hvals]⟩

theorem g1_tail_vArg1Unary {fs : List G1Frame}
    (h : g1AdvanceList .vArg1Unary fs = .rewindStart) :
    ∃ (a1 : Nat) (vals : List Bool),
      fs = List.replicate a1 .index ++ .argSep :: .separator ::
        (vals.map .data ++ [.output false, .finish, .blank]) := by
  obtain ⟨a1, tail, rfl, ht⟩ :=
    g1_run_split (mode := .vArg1Unary) (next := .vArg2Zero) (unit := .index)
      (stop := .argSep) (by decide) rfl rfl (by decide) h
  obtain ⟨vals, hvals⟩ := g1_tail_vArg2Zero ht
  exact ⟨a1, vals, by rw [hvals]⟩

theorem g1_tail_vArg1Binary {fs : List G1Frame}
    (h : g1AdvanceList .vArg1Binary fs = .rewindStart) :
    ∃ (a1 a2 : Nat) (vals : List Bool),
      fs = List.replicate a1 .index ++ .argSep ::
        (List.replicate a2 .index ++ .separator ::
          (vals.map .data ++ [.output false, .finish, .blank])) := by
  obtain ⟨a1, tail, rfl, ht⟩ :=
    g1_run_split (mode := .vArg1Binary) (next := .vArg2Any) (unit := .index)
      (stop := .argSep) (by decide) rfl rfl (by decide) h
  obtain ⟨a2, vals, hvals⟩ := g1_tail_vArg2Any ht
  exact ⟨a1, a2, vals, by rw [hvals]⟩

/-- The `const` operand field carries at most one `index`: the unary constant
bit.  A second `index` rejects, so an accepting word has `a1 ≤ 1`. -/
theorem g1_tail_vConst0 {fs : List G1Frame}
    (h : g1AdvanceList .vConst0 fs = .rewindStart) :
    ∃ (a1 : Nat) (vals : List Bool), a1 ≤ 1 ∧
      fs = List.replicate a1 .index ++ .argSep :: .separator ::
        (vals.map .data ++ [.output false, .finish, .blank]) := by
  rcases g1_two_split (mode := .vConst0) (nextA := .vConst1) (nextB := .vArg2Zero)
      (frameA := .index) (frameB := .argSep) (by decide) rfl rfl (by decide) h with
    ⟨tail, rfl, ht⟩ | ⟨tail, rfl, ht⟩
  · obtain ⟨tail2, rfl, ht2⟩ :=
      g1_step_split (mode := .vConst1) (next := .vArg2Zero) (frame := .argSep)
        (by decide) rfl (by decide) ht
    obtain ⟨vals, hvals⟩ := g1_tail_vArg2Zero ht2
    exact ⟨1, vals, Nat.le_refl 1, by rw [hvals]; rfl⟩
  · obtain ⟨vals, hvals⟩ := g1_tail_vArg2Zero ht
    exact ⟨0, vals, Nat.zero_le 1, by rw [hvals]; rfl⟩

/-- **Machine-side completeness.**  Every frame word the forward table accepts
is literally the canonical encoding of a canonical request, followed by the
explicit end-of-input frame. -/
theorem g1_structure_of_accepts {fs : List G1Frame}
    (h : g1AdvanceList .vBof fs = .rewindStart) :
    ∃ r : G1Request, r.Canonical ∧ fs = encodeG1Frames r ++ [.blank] := by
  obtain ⟨fs, rfl, h⟩ :=
    g1_step_split (mode := .vBof) (next := .vTag0) (frame := .bof)
      (by decide) rfl (by decide) h
  obtain ⟨fs, rfl, h⟩ :=
    g1_step_split (mode := .vTag0) (next := .vTag1) (frame := .tag)
      (by decide) rfl (by decide) h
  rcases g1_two_split (mode := .vTag1) (nextA := .vTag2) (nextB := .vArg1Unary)
      (frameA := .tag) (frameB := .argSep) (by decide) rfl rfl (by decide) h with
    ⟨fs, rfl, h⟩ | ⟨fs, rfl, h⟩
  · rcases g1_two_split (mode := .vTag2) (nextA := .vTag3) (nextB := .vConst0)
        (frameA := .tag) (frameB := .argSep) (by decide) rfl rfl (by decide) h with
      ⟨fs, rfl, h⟩ | ⟨fs, rfl, h⟩
    · rcases g1_two_split (mode := .vTag3) (nextA := .vTag4)
          (nextB := .vArg1Unary) (frameA := .tag) (frameB := .argSep)
          (by decide) rfl rfl (by decide) h with
        ⟨fs, rfl, h⟩ | ⟨fs, rfl, h⟩
      · rcases g1_two_split (mode := .vTag4) (nextA := .vTag5)
            (nextB := .vArg1Binary) (frameA := .tag) (frameB := .argSep)
            (by decide) rfl rfl (by decide) h with
          ⟨fs, rfl, h⟩ | ⟨fs, rfl, h⟩
        · -- five tag units: `or`
          obtain ⟨fs, rfl, h⟩ :=
            g1_step_split (mode := .vTag5) (next := .vArg1Binary)
              (frame := .argSep) (by decide) rfl (by decide) h
          obtain ⟨a1, a2, vals, rfl⟩ := g1_tail_vArg1Binary h
          exact ⟨⟨.or, a1, a2, vals⟩,
            by simp [G1Request.Canonical, G1Request.canonicalB, G1Tag.arity],
            by simp [encodeG1Frames, G1Tag.units, List.append_assoc]⟩
        · -- four tag units: `and`
          obtain ⟨a1, a2, vals, rfl⟩ := g1_tail_vArg1Binary h
          exact ⟨⟨.and, a1, a2, vals⟩,
            by simp [G1Request.Canonical, G1Request.canonicalB, G1Tag.arity],
            by simp [encodeG1Frames, G1Tag.units, List.append_assoc]⟩
      · -- three tag units: `not`
        obtain ⟨a1, vals, rfl⟩ := g1_tail_vArg1Unary h
        exact ⟨⟨.not, a1, 0, vals⟩,
          by simp [G1Request.Canonical, G1Request.canonicalB, G1Tag.arity],
          by simp [encodeG1Frames, G1Tag.units, List.append_assoc]⟩
    · -- two tag units: `const`
      obtain ⟨a1, vals, hle, rfl⟩ := g1_tail_vConst0 h
      exact ⟨⟨.const, a1, 0, vals⟩,
        by simp [G1Request.Canonical, G1Request.canonicalB, G1Tag.arity, hle],
        by simp [encodeG1Frames, G1Tag.units, List.append_assoc]⟩
  · -- one tag unit: `input`
    obtain ⟨a1, vals, rfl⟩ := g1_tail_vArg1Unary h
    exact ⟨⟨.input, a1, 0, vals⟩,
      by simp [G1Request.Canonical, G1Request.canonicalB, G1Tag.arity],
      by simp [encodeG1Frames, G1Tag.units, List.append_assoc]⟩

/-! ### Soundness: the canonical encoder is accepted, and only then -/

private theorem g1_advance_vData_tail (vals : List Bool) :
    g1AdvanceList .vData
        (vals.map .data ++ [.output false, .finish, .blank]) = .rewindStart := by
  induction vals with
  | nil => rfl
  | cons b bs ih => rw [List.map_cons, List.cons_append, g1AdvanceList_cons]
                    cases b <;> exact ih

private theorem g1_advance_vArg2Zero_tail (vals : List Bool) :
    g1AdvanceList .vArg2Zero
        (.separator :: (vals.map .data ++ [.output false, .finish, .blank])) =
      .rewindStart :=
  g1_advance_vData_tail vals

private theorem g1_advance_vArg2Any_tail (a2 : Nat) (vals : List Bool) :
    g1AdvanceList .vArg2Any
        (List.replicate a2 .index ++ .separator ::
          (vals.map .data ++ [.output false, .finish, .blank])) = .rewindStart := by
  induction a2 with
  | zero => exact g1_advance_vData_tail vals
  | succ k ih => rw [List.replicate_succ, List.cons_append, g1AdvanceList_cons]
                 exact ih

/-- An arity-1 tag with a non-empty operand-2 field is rejected by the control
at `vArg2Zero`, on the very first `index` frame. -/
theorem g1_rejectPath_vArg2Zero (a2 : Nat) (ha2 : a2 ≠ 0)
    (rest : List G1Frame) :
    G1RejectPath .vArg2Zero (List.replicate a2 .index ++ rest) := by
  obtain ⟨k, rfl⟩ : ∃ k, a2 = k + 1 := ⟨a2 - 1, by omega⟩
  rw [List.replicate_succ, List.cons_append]
  exact ⟨trivial, Or.inl rfl⟩

private theorem g1_advance_vArg1Unary_tail (a1 : Nat) (vals : List Bool) :
    g1AdvanceList .vArg1Unary
        (List.replicate a1 .index ++ .argSep :: .separator ::
          (vals.map .data ++ [.output false, .finish, .blank])) = .rewindStart := by
  induction a1 with
  | zero => exact g1_advance_vArg2Zero_tail vals
  | succ k ih => rw [List.replicate_succ, List.cons_append, g1AdvanceList_cons]
                 exact ih

theorem g1_rejectPath_vArg1Unary (a1 a2 : Nat) (ha2 : a2 ≠ 0)
    (rest : List G1Frame) :
    G1RejectPath .vArg1Unary
      (List.replicate a1 .index ++ .argSep ::
        (List.replicate a2 .index ++ rest)) := by
  induction a1 with
  | zero => exact ⟨trivial, Or.inr (g1_rejectPath_vArg2Zero a2 ha2 rest)⟩
  | succ k ih =>
      rw [List.replicate_succ, List.cons_append]
      exact ⟨trivial, Or.inr ih⟩

private theorem g1_advance_vArg1Binary_tail (a1 a2 : Nat) (vals : List Bool) :
    g1AdvanceList .vArg1Binary
        (List.replicate a1 .index ++ .argSep ::
          (List.replicate a2 .index ++ .separator ::
            (vals.map .data ++ [.output false, .finish, .blank]))) =
      .rewindStart := by
  induction a1 with
  | zero => exact g1_advance_vArg2Any_tail a2 vals
  | succ k ih => rw [List.replicate_succ, List.cons_append, g1AdvanceList_cons]
                 exact ih

private theorem g1_advance_vConst0_tail (a1 : Nat) (ha1 : a1 ≤ 1)
    (vals : List Bool) :
    g1AdvanceList .vConst0
        (List.replicate a1 .index ++ .argSep :: .separator ::
          (vals.map .data ++ [.output false, .finish, .blank])) = .rewindStart := by
  match a1, ha1 with
  | 0, _ => exact g1_advance_vArg2Zero_tail vals
  | 1, _ =>
      rw [List.replicate_one, List.cons_append, g1AdvanceList_cons]
      exact g1_advance_vArg2Zero_tail vals

/-- A `const` field of two or more `index` units is rejected by the control at
`vConst1`, on the second `index` frame. -/
theorem g1_rejectPath_vConst0_arg1 (a1 : Nat) (ha1 : 2 ≤ a1)
    (rest : List G1Frame) :
    G1RejectPath .vConst0 (List.replicate a1 .index ++ rest) := by
  obtain ⟨k, rfl⟩ : ∃ k, a1 = k + 2 := ⟨a1 - 2, by omega⟩
  have hrep : List.replicate (k + 2) G1Frame.index =
      .index :: .index :: List.replicate k .index := by
    simp [List.replicate_succ]
  rw [hrep, List.cons_append, List.cons_append]
  exact ⟨trivial, Or.inr ⟨trivial, Or.inl rfl⟩⟩

theorem g1_rejectPath_vConst0_arg2 (a1 a2 : Nat) (ha1 : a1 ≤ 1)
    (ha2 : a2 ≠ 0) (rest : List G1Frame) :
    G1RejectPath .vConst0
      (List.replicate a1 .index ++ .argSep ::
        (List.replicate a2 .index ++ rest)) := by
  match a1, ha1 with
  | 0, _ => exact ⟨trivial, Or.inr (g1_rejectPath_vArg2Zero a2 ha2 rest)⟩
  | 1, _ =>
      rw [List.replicate_one, List.cons_append]
      exact ⟨trivial, Or.inr ⟨trivial,
        Or.inr (g1_rejectPath_vArg2Zero a2 ha2 rest)⟩⟩

/-- The canonical frame word plus the explicit end-of-input frame, in the
cons-normal form the frame table consumes. -/
theorem encodeG1Frames_blank_shape (r : G1Request) :
    encodeG1Frames r ++ [.blank] =
      .bof :: (List.replicate r.tag.units .tag ++ .argSep ::
        (List.replicate r.arg1 .index ++ .argSep ::
          (List.replicate r.arg2 .index ++ .separator ::
            (r.vals.map .data ++ [.output false, .finish, .blank])))) := by
  simp [encodeG1Frames, List.append_assoc]

/-- **Encoder soundness.**  A canonical request's frame word plus the explicit
end-of-input frame is accepted by the forward table. -/
theorem g1AdvanceList_encode (r : G1Request) (hc : r.Canonical) :
    g1AdvanceList .vBof (encodeG1Frames r ++ [.blank]) = .rewindStart := by
  rw [G1Request.canonical_iff] at hc
  obtain ⟨hArity, hConst⟩ := hc
  rw [encodeG1Frames_blank_shape, g1AdvanceList_cons]
  rcases r with ⟨tag, a1, a2, vals⟩
  cases tag with
  | input =>
      have ha2 : a2 = 0 := hArity rfl
      subst ha2
      simpa [G1Tag.units] using g1_advance_vArg1Unary_tail a1 vals
  | const =>
      have ha2 : a2 = 0 := hArity rfl
      have ha1 : a1 ≤ 1 := hConst rfl
      subst ha2
      simpa [G1Tag.units] using g1_advance_vConst0_tail a1 ha1 vals
  | not =>
      have ha2 : a2 = 0 := hArity rfl
      subst ha2
      simpa [G1Tag.units] using g1_advance_vArg1Unary_tail a1 vals
  | and => simpa [G1Tag.units] using g1_advance_vArg1Binary_tail a1 a2 vals
  | or => simpa [G1Tag.units] using g1_advance_vArg1Binary_tail a1 a2 vals

/-- **Encoder rejection, as a path.**  A *noncanonical* request's frame word
drives the forward control into the `reject` sink, at the first frame that
violates the tag-dependent operand convention. -/
theorem g1RejectPath_encode (r : G1Request) (hc : ¬ r.Canonical) :
    G1RejectPath .vBof (encodeG1Frames r ++ [.blank]) := by
  rw [encodeG1Frames_blank_shape]
  rcases r with ⟨tag, a1, a2, vals⟩
  cases tag with
  | input =>
      have ha2 : a2 ≠ 0 := by
        intro h; subst h
        exact hc (by simp [G1Request.Canonical, G1Request.canonicalB, G1Tag.arity])
      refine ⟨trivial, Or.inr ?_⟩
      show G1RejectPath _ (List.replicate (G1Tag.units .input) .tag ++ _)
      simp only [G1Tag.units, List.replicate_one, List.cons_append,
        List.nil_append]
      refine ⟨trivial, Or.inr ⟨trivial, Or.inr ?_⟩⟩
      exact g1_rejectPath_vArg1Unary a1 a2 ha2
        (.separator :: (vals.map .data ++ [.output false, .finish, .blank]))
  | not =>
      have ha2 : a2 ≠ 0 := by
        intro h; subst h
        exact hc (by simp [G1Request.Canonical, G1Request.canonicalB, G1Tag.arity])
      refine ⟨trivial, Or.inr ?_⟩
      show G1RejectPath _ (List.replicate (G1Tag.units .not) .tag ++ _)
      simp only [G1Tag.units, List.replicate_succ, List.replicate_zero,
        List.cons_append, List.nil_append]
      refine ⟨trivial, Or.inr ⟨trivial, Or.inr ⟨trivial, Or.inr
        ⟨trivial, Or.inr ?_⟩⟩⟩⟩
      exact g1_rejectPath_vArg1Unary a1 a2 ha2
        (.separator :: (vals.map .data ++ [.output false, .finish, .blank]))
  | const =>
      refine ⟨trivial, Or.inr ?_⟩
      show G1RejectPath _ (List.replicate (G1Tag.units .const) .tag ++ _)
      simp only [G1Tag.units, List.replicate_succ, List.replicate_zero,
        List.cons_append, List.nil_append]
      refine ⟨trivial, Or.inr ⟨trivial, Or.inr ⟨trivial, Or.inr ?_⟩⟩⟩
      by_cases ha1 : a1 ≤ 1
      · have ha2 : a2 ≠ 0 := by
          intro h; subst h
          exact hc (by
            simp [G1Request.Canonical, G1Request.canonicalB, G1Tag.arity, ha1])
        exact g1_rejectPath_vConst0_arg2 a1 a2 ha1 ha2
          (.separator :: (vals.map .data ++ [.output false, .finish, .blank]))
      · exact g1_rejectPath_vConst0_arg1 a1 (by omega)
          (.argSep :: (List.replicate a2 .index ++ .separator ::
            (vals.map .data ++ [.output false, .finish, .blank])))
  | and =>
      exact absurd
        (show G1Request.Canonical ⟨.and, a1, a2, vals⟩ by
          simp [G1Request.Canonical, G1Request.canonicalB, G1Tag.arity]) hc
  | or =>
      exact absurd
        (show G1Request.Canonical ⟨.or, a1, a2, vals⟩ by
          simp [G1Request.Canonical, G1Request.canonicalB, G1Tag.arity]) hc

/-- **Encoder rejection.**  A *noncanonical* request's frame word is rejected
by the forward table: the run ends in the literal `reject` sink. -/
theorem g1AdvanceList_encode_reject (r : G1Request) (hc : ¬ r.Canonical) :
    g1AdvanceList .vBof (encodeG1Frames r ++ [.blank]) = .reject :=
  g1AdvanceList_eq_reject_of_rejectPath (g1RejectPath_encode r hc)

/-- **Parser/machine agreement, at frame level.**  A frame word closed by the
explicit end-of-input frame is accepted by the fixed forward control exactly
when the pure parser decodes it.  This is the theorem that makes "the control
validates *the* canonical grammar" a proved statement rather than a
description. -/
theorem g1Automaton_accepts_iff_decode (fs : List G1Frame) :
    g1AdvanceList .vBof (fs ++ [.blank]) = .rewindStart ↔
      ∃ r : G1Request, decodeG1FrameList? fs = some r := by
  constructor
  · intro h
    obtain ⟨r, hc, heq⟩ := g1_structure_of_accepts h
    have hfs : fs = encodeG1Frames r := List.append_cancel_right heq
    exact ⟨r, by rw [hfs]; exact decodeG1FrameList?_encoded r hc⟩
  · rintro ⟨r, hr⟩
    obtain ⟨hfs, hc⟩ := decodeG1FrameList?_eq_some hr
    subst hfs
    exact g1AdvanceList_encode r hc

/-- **Encoder equivalence.**  The forward run of a request's canonical frame
word reaches `rewindStart` if and only if the request is canonical. -/
theorem g1CanonicalEncoderAutomatonTrace_iff (r : G1Request) :
    g1AdvanceList .vBof (encodeG1Frames r ++ [.blank]) = .rewindStart ↔
      r.Canonical := by
  constructor
  · intro h
    by_contra hc
    rw [g1AdvanceList_encode_reject r hc] at h
    exact absurd h (by decide)
  · exact g1AdvanceList_encode r

/-- Closed accepted-word witness for the control grammar. -/
theorem g1_example_control_and_accepts :
    g1AdvanceList .vBof
        (encodeG1Frames ⟨.and, 2, 3, [true, false]⟩ ++ [.blank]) =
      .rewindStart :=
  (g1CanonicalEncoderAutomatonTrace_iff _).2 rfl

/-- Closed noncanonical-word witness for the reject sink. -/
theorem g1_example_control_const_rejects :
    g1AdvanceList .vBof (encodeG1Frames ⟨.const, 3, 1, []⟩ ++ [.blank]) =
      .reject :=
  g1AdvanceList_encode_reject _ (by decide)

/-! ### Named frame-level rejection witnesses

Concrete words the control rejects and the parser refuses.  These are the
grammar clauses that the previous, permissive table could not see. -/

/-- **Zero tag units.**  The empty tag run is rejected at `vTag0`. -/
theorem g1_reject_tagRun_zero (rest : List G1Frame) :
    g1AdvanceList .vBof (.bof :: .argSep :: rest) = .reject := by
  rw [g1AdvanceList_cons, g1AdvanceList_cons]
  exact g1AdvanceList_reject _

/-- **Six tag units.**  A sixth `tag` is rejected at `vTag5`. -/
theorem g1_reject_tagRun_six (rest : List G1Frame) :
    g1AdvanceList .vBof
        (.bof :: .tag :: .tag :: .tag :: .tag :: .tag :: .tag :: rest) =
      .reject := by
  simp only [g1AdvanceList_cons]
  exact g1AdvanceList_reject _

/-- **`const` with `arg1 ≥ 2`.**  A second constant `index` unit is rejected at
`vConst1`. -/
theorem g1_reject_const_arg1_ge_two (a1 : Nat) (ha1 : 2 ≤ a1)
    (rest : List G1Frame) :
    g1AdvanceList .vBof
        (.bof :: .tag :: .tag :: .argSep :: (List.replicate a1 .index ++ rest)) =
      .reject :=
  g1AdvanceList_eq_reject_of_rejectPath
    ⟨trivial, Or.inr ⟨trivial, Or.inr ⟨trivial, Or.inr ⟨trivial, Or.inr
      (g1_rejectPath_vConst0_arg1 a1 ha1 rest)⟩⟩⟩⟩

/-- **An arity-1 tag with a non-empty operand-2 field.**  The first stray
`index` is rejected at `vArg2Zero`.  The tag run `.tag ^ units` selects the
regime; `input` (1) and `not` (3) both land in `vArg1Unary`. -/
theorem g1_reject_unusedField_input (a1 a2 : Nat) (ha2 : a2 ≠ 0)
    (rest : List G1Frame) :
    g1AdvanceList .vBof
        (.bof :: .tag :: .argSep ::
          (List.replicate a1 .index ++ .argSep ::
            (List.replicate a2 .index ++ rest))) = .reject :=
  g1AdvanceList_eq_reject_of_rejectPath
    ⟨trivial, Or.inr ⟨trivial, Or.inr ⟨trivial, Or.inr
      (g1_rejectPath_vArg1Unary a1 a2 ha2 rest)⟩⟩⟩

theorem g1_reject_unusedField_not (a1 a2 : Nat) (ha2 : a2 ≠ 0)
    (rest : List G1Frame) :
    g1AdvanceList .vBof
        (.bof :: .tag :: .tag :: .tag :: .argSep ::
          (List.replicate a1 .index ++ .argSep ::
            (List.replicate a2 .index ++ rest))) = .reject :=
  g1AdvanceList_eq_reject_of_rejectPath
    ⟨trivial, Or.inr ⟨trivial, Or.inr ⟨trivial, Or.inr ⟨trivial, Or.inr
      ⟨trivial, Or.inr (g1_rejectPath_vArg1Unary a1 a2 ha2 rest)⟩⟩⟩⟩⟩

theorem g1_reject_unusedField_const (a1 a2 : Nat) (ha1 : a1 ≤ 1) (ha2 : a2 ≠ 0)
    (rest : List G1Frame) :
    g1AdvanceList .vBof
        (.bof :: .tag :: .tag :: .argSep ::
          (List.replicate a1 .index ++ .argSep ::
            (List.replicate a2 .index ++ rest))) = .reject :=
  g1AdvanceList_eq_reject_of_rejectPath
    ⟨trivial, Or.inr ⟨trivial, Or.inr ⟨trivial, Or.inr ⟨trivial, Or.inr
      (g1_rejectPath_vConst0_arg2 a1 a2 ha1 ha2 rest)⟩⟩⟩⟩

/-! ### Path validity

Every accepting word is automatically a `G1ValidPath`, so the executable scan
never needs a separate structural induction. -/

theorem g1ValidPath_of_accepts {mode : G1Mode} (hmode : G1ForwardMode mode)
    {fs : List G1Frame} (h : g1AdvanceList mode fs = .rewindStart) :
    G1ValidPath mode fs := by
  induction fs generalizing mode with
  | nil => trivial
  | cons frame rest ih =>
      refine ⟨hmode, ?_, ?_⟩
      · intro hr
        rw [g1AdvanceList_cons, hr, g1AdvanceList_reject] at h
        exact absurd h (by decide)
      · rw [g1AdvanceList_cons] at h
        rcases g1Advance_range mode frame with hf | hf | hf
        · exact ih hf h
        · rw [hf] at h ⊢
          rw [g1AdvanceList_rewindStart_eq_nil h]
          trivial
        · exact absurd h (g1AdvanceList_ne_rewindStart_of_stuck hf rest)

/-! ## The one fixed zero-parameter program -/

/-- **The complete transition table.** -/
def g1Transition (_phase : Fin 1) (s : G1State) (scan : Bool) :
    Fin 1 × G1State × Bool × Move :=
  match s.mode with
  | .accept => (0, g1AcceptState, scan, .stay)
  | .reject => (0, g1RejectState, scan, .stay)
  -- the four remaining local handoffs: idle in this slice, each its own stable
  -- state
  | .readAStart => (0, g1ReadAState s.ctx, scan, .stay)
  | .combineStart => (0, g1CombineState s.ctx, scan, .stay)
  | .readAResetStart => (0, g1ReadAResetState s.ctx, scan, .stay)
  | .bOOB => (0, g1OOBState s.ctx, scan, .stay)
  -- the destructive index round: bridge, reverse read, fixed-code write,
  -- back-walk, hop.  Nothing here inspects the request: the four written cells
  -- are the literal codeword of `spent`, and every other row writes back the
  -- cell it scanned.
  | .bRoundStart => (0, g1WalkState s.ctx, scan, .left)
  | .bWalk =>
      match s.position with
      | .p3 => (0, g1State .bWalk .p2 false false scan s.ctx, scan, .left)
      | .p2 => (0, g1State .bWalk .p1 false scan s.b2 s.ctx, scan, .left)
      | .p1 => (0, g1State .bWalk .p0 scan s.b1 s.b2 s.ctx, scan, .left)
      | .p0 =>
          if decodeG1Frame? [scan, s.b0, s.b1, s.b2] = some .index then
            (0, g1MarkState s.ctx, scan, .stay)
          else (0, g1WalkState s.ctx, scan, .left)
  | .bMark =>
      match s.position with
      | .p0 => (0, g1State .bMark .p1 false false false s.ctx, true, .right)
      | .p1 => (0, g1State .bMark .p2 false false false s.ctx, true, .right)
      | .p2 => (0, g1State .bMark .p3 false false false s.ctx, false, .right)
      | .p3 => (0, g1State .bBack .p0 false false false s.ctx, false, .right)
  | .bBack =>
      match s.position with
      | .p0 => (0, g1State .bBack .p1 false false false s.ctx, scan, .left)
      | .p1 => (0, g1State .bBack .p2 false false false s.ctx, scan, .left)
      | .p2 => (0, g1State .bBack .p3 false false false s.ctx, scan, .left)
      | .p3 => (0, g1State .bHop .p0 false false false s.ctx, scan, .left)
  | .bHop => (0, g1WalkState s.ctx, scan, .left)
  -- the four dispatch modes: store the decoded Boolean in `vB`, do not move
  | .constFalse => (0, g1CombineState (s.ctx.withVB false), scan, .stay)
  | .constTrue => (0, g1CombineState (s.ctx.withVB true), scan, .stay)
  | .bStoreFalse => (0, g1ReadAResetState (s.ctx.withVB false), scan, .stay)
  | .bStoreTrue => (0, g1ReadAResetState (s.ctx.withVB true), scan, .stay)
  | .rewindStart => (0, g1State .rewind .p3 false false false s.ctx, scan, .left)
  | .rewind =>
      match s.position with
      | .p3 => (0, g1State .rewind .p2 false false scan s.ctx, scan, .left)
      | .p2 => (0, g1State .rewind .p1 false scan s.b2 s.ctx, scan, .left)
      | .p1 => (0, g1State .rewind .p0 scan s.b1 s.b2 s.ctx, scan, .left)
      | .p0 =>
          if decodeG1Frame? [scan, s.b0, s.b1, s.b2] = some .bof then
            (0, g1ReadBState s.ctx, scan, .stay)
          else (0, g1State .rewind .p3 false false false s.ctx, scan, .left)
  | mode =>
      match s.position with
      | .p0 => (0, g1State mode .p1 scan false false s.ctx, scan, .right)
      | .p1 => (0, g1State mode .p2 s.b0 scan false s.ctx, scan, .right)
      | .p2 => (0, g1State mode .p3 s.b0 s.b1 scan s.ctx, scan, .right)
      | .p3 =>
          let next := g1Complete mode s.b0 s.b1 s.b2 scan
          if next = .reject then (0, g1RejectState, scan, .stay)
          else (0, g1State next .p0 false false false s.ctx, scan, .right)

/-- **The closed program clock.**  Only the physical input length occurs. -/
def g1Clock (N : Nat) : Nat := 512 * (N + 1) ^ 2 + 512

/-- **The only G1 program declaration.**  One phase, no parameters, closed
finite control, closed clock. -/
def g1CS : ConstStatePhasedProgram G1State where
  numPhases := 1
  startPhase := 0
  startState := g1State .vBof .p0
  acceptPhase := 0
  acceptState := g1AcceptState
  transition := g1Transition
  timeBound := g1Clock

@[simp] theorem g1CS_numPhases : g1CS.numPhases = 1 := rfl

/-- The public clock in arithmetic normal form.  Deliberately not a `simp`
lemma: the generic clock projections stop at `g1CS.timeBound N`. -/
theorem g1CS_runTime (N : Nat) :
    g1CS.toPhased.toTM.runTime N = 512 * (N + 1) ^ 2 + 512 := rfl

/-! ## Standalone transition-table lemmas

Each lemma is a plain tuple equation about `g1Transition`, proved by `rfl`
after at most one mode split.  The phase is universally quantified so that a
caller can instantiate it at whatever `Fin`-encoded phase its configuration
carries. -/

/-! ### Sinks, handoffs and dispatch

`readBStart` no longer appears here: it is a genuine forward frame-reading
mode and its steps come from the four `g1Transition_forward_*` lemmas below.
`bRoundStart` no longer appears here either: it is the genuine one-step bridge
of the destructive round and its tuple is `g1Transition_bRoundStart_bridge`
below.  The four remaining handoffs are idle **in this slice**; the deferred
pass-A and combine slices replace those four equations. -/

@[simp] theorem g1Transition_accept_sink (phase : Fin 1) (scan : Bool) :
    g1Transition phase g1AcceptState scan = (0, g1AcceptState, scan, .stay) :=
  rfl

@[simp] theorem g1Transition_reject_sink (phase : Fin 1) (scan : Bool) :
    g1Transition phase g1RejectState scan = (0, g1RejectState, scan, .stay) :=
  rfl

theorem g1Transition_readAStart_idle (phase : Fin 1)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State .readAStart position b0 b1 b2 ctx) scan =
      (0, g1ReadAState ctx, scan, .stay) := rfl

theorem g1Transition_combineStart_idle (phase : Fin 1)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State .combineStart position b0 b1 b2 ctx) scan =
      (0, g1CombineState ctx, scan, .stay) := rfl

theorem g1Transition_readAResetStart_idle (phase : Fin 1)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State .readAResetStart position b0 b1 b2 ctx) scan =
      (0, g1ReadAResetState ctx, scan, .stay) := rfl

/-- **The out-of-range boundary is stable.**  It never moves, never writes and
never leaves itself. -/
theorem g1Transition_bOOB_stable (phase : Fin 1)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State .bOOB position b0 b1 b2 ctx) scan =
      (0, g1OOBState ctx, scan, .stay) := rfl

/-- **The `const` literal dispatch.**  One stationary step writes the decoded
unary literal into the fixed Boolean field `vB` and hands off to the combine
boundary.  `g1ConstMode` is the mode the forward table lands in. -/
def g1ConstMode : Bool → G1Mode
  | false => .constFalse
  | true => .constTrue

theorem g1Transition_constLit (phase : Fin 1) (b : Bool)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State (g1ConstMode b) position b0 b1 b2 ctx) scan =
      (0, g1CombineState (ctx.withVB b), scan, .stay) := by
  cases b <;> rfl

/-- **The operand-2 store dispatch.**  One stationary step writes the value
just read out of the data region into `vB` and hands off to the pass-A reset
boundary. -/
def g1StoreMode : Bool → G1Mode
  | false => .bStoreFalse
  | true => .bStoreTrue

theorem g1Transition_store (phase : Fin 1) (b : Bool)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State (g1StoreMode b) position b0 b1 b2 ctx) scan =
      (0, g1ReadAResetState (ctx.withVB b), scan, .stay) := by
  cases b <;> rfl

/-! ### Forward frame reading -/

theorem g1Transition_forward_p0 {mode : G1Mode} (hmode : G1ForwardMode mode)
    (phase : Fin 1) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State mode .p0 b0 b1 b2 ctx) scan =
      (0, g1State mode .p1 scan false false ctx, scan, .right) := by
  cases mode <;> first | rfl | exact (show False from hmode).elim

theorem g1Transition_forward_p1 {mode : G1Mode} (hmode : G1ForwardMode mode)
    (phase : Fin 1) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State mode .p1 b0 b1 b2 ctx) scan =
      (0, g1State mode .p2 b0 scan false ctx, scan, .right) := by
  cases mode <;> first | rfl | exact (show False from hmode).elim

theorem g1Transition_forward_p2 {mode : G1Mode} (hmode : G1ForwardMode mode)
    (phase : Fin 1) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State mode .p2 b0 b1 b2 ctx) scan =
      (0, g1State mode .p3 b0 b1 scan ctx, scan, .right) := by
  cases mode <;> first | rfl | exact (show False from hmode).elim

private theorem g1Transition_forward_p3_raw {mode : G1Mode}
    (hmode : G1ForwardMode mode) (phase : Fin 1) (b0 b1 b2 scan : Bool)
    (ctx : G1Ctx) :
    g1Transition phase (g1State mode .p3 b0 b1 b2 ctx) scan =
      (if g1Complete mode b0 b1 b2 scan = .reject then
          (0, g1RejectState, scan, .stay)
        else
          (0, g1State (g1Complete mode b0 b1 b2 scan) .p0 false false false
            ctx, scan, .right)) := by
  cases mode <;> first | rfl | exact (show False from hmode).elim

theorem g1Transition_forward_p3_advance {mode : G1Mode}
    (hmode : G1ForwardMode mode) (phase : Fin 1) (b0 b1 b2 scan : Bool)
    (ctx : G1Ctx) (hne : g1Complete mode b0 b1 b2 scan ≠ .reject) :
    g1Transition phase (g1State mode .p3 b0 b1 b2 ctx) scan =
      (0, g1State (g1Complete mode b0 b1 b2 scan) .p0 false false false ctx,
        scan, .right) := by
  rw [g1Transition_forward_p3_raw hmode, if_neg hne]

/-- Completing an invalid frame: stable reject, tape and head unchanged. -/
theorem g1Transition_forward_p3_reject {mode : G1Mode}
    (hmode : G1ForwardMode mode) (phase : Fin 1) (b0 b1 b2 scan : Bool)
    (ctx : G1Ctx) (heq : g1Complete mode b0 b1 b2 scan = .reject) :
    g1Transition phase (g1State mode .p3 b0 b1 b2 ctx) scan =
      (0, g1RejectState, scan, .stay) := by
  rw [g1Transition_forward_p3_raw hmode, if_pos heq]

/-! ### Rewinding -/

theorem g1Transition_rewindStart (phase : Fin 1)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State .rewindStart position b0 b1 b2 ctx) scan =
      (0, g1State .rewind .p3 false false false ctx, scan, .left) := rfl

theorem g1Transition_rewind_p3 (phase : Fin 1) (b0 b1 b2 scan : Bool)
    (ctx : G1Ctx) :
    g1Transition phase (g1State .rewind .p3 b0 b1 b2 ctx) scan =
      (0, g1State .rewind .p2 false false scan ctx, scan, .left) := rfl

theorem g1Transition_rewind_p2 (phase : Fin 1) (b0 b1 b2 scan : Bool)
    (ctx : G1Ctx) :
    g1Transition phase (g1State .rewind .p2 b0 b1 b2 ctx) scan =
      (0, g1State .rewind .p1 false scan b2 ctx, scan, .left) := rfl

theorem g1Transition_rewind_p1 (phase : Fin 1) (b0 b1 b2 scan : Bool)
    (ctx : G1Ctx) :
    g1Transition phase (g1State .rewind .p1 b0 b1 b2 ctx) scan =
      (0, g1State .rewind .p0 scan b1 b2 ctx, scan, .left) := rfl

private theorem g1Transition_rewind_p0_raw (phase : Fin 1)
    (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State .rewind .p0 b0 b1 b2 ctx) scan =
      (if decodeG1Frame? [scan, b0, b1, b2] = some .bof then
          (0, g1ReadBState ctx, scan, .stay)
        else (0, g1State .rewind .p3 false false false ctx, scan, .left)) :=
  rfl

/-- Reverse-reading the anchor enters the pass-B handoff without moving. -/
theorem g1Transition_rewind_p0_bof (phase : Fin 1) (b0 b1 b2 scan : Bool)
    (ctx : G1Ctx) (heq : decodeG1Frame? [scan, b0, b1, b2] = some .bof) :
    g1Transition phase (g1State .rewind .p0 b0 b1 b2 ctx) scan =
      (0, g1ReadBState ctx, scan, .stay) := by
  rw [g1Transition_rewind_p0_raw, if_pos heq]

/-- Reverse-reading any other frame continues the rewind. -/
theorem g1Transition_rewind_p0_other (phase : Fin 1) (b0 b1 b2 scan : Bool)
    (ctx : G1Ctx) (hne : decodeG1Frame? [scan, b0, b1, b2] ≠ some .bof) :
    g1Transition phase (g1State .rewind .p0 b0 b1 b2 ctx) scan =
      (0, g1State .rewind .p3 false false false ctx, scan, .left) := by
  rw [g1Transition_rewind_p0_raw, if_neg hne]

/-! ### The destructive index round, retained as a regression

Fourteen tuples: the bridge, four reverse-read steps (the last one splitting on
whether the completed frame is the `index` marker), four fixed-code writes, four
back-walk steps and the hop.  Every one of them is `rfl` after at most one
position split, and none of them mentions the request.  The forward table no
longer produces `bRoundStart`, so these rows are exercised only from
caller-supplied configurations. -/

/-- **The bridge.**  From a configuration whose head is on the first cell of the
frame after an `index`, one step to the left re-aligns the control on the last
cell of that `index` in the reverse-read entry shape.  The scanned cell is
written back, so the tape does not change. -/
theorem g1Transition_bRoundStart_bridge (phase : Fin 1)
    (position : G1FramePosition) (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State .bRoundStart position b0 b1 b2 ctx) scan =
      (0, g1WalkState ctx, scan, .left) := rfl

theorem g1Transition_bWalk_p3 (phase : Fin 1) (b0 b1 b2 scan : Bool)
    (ctx : G1Ctx) :
    g1Transition phase (g1State .bWalk .p3 b0 b1 b2 ctx) scan =
      (0, g1State .bWalk .p2 false false scan ctx, scan, .left) := rfl

theorem g1Transition_bWalk_p2 (phase : Fin 1) (b0 b1 b2 scan : Bool)
    (ctx : G1Ctx) :
    g1Transition phase (g1State .bWalk .p2 b0 b1 b2 ctx) scan =
      (0, g1State .bWalk .p1 false scan b2 ctx, scan, .left) := rfl

theorem g1Transition_bWalk_p1 (phase : Fin 1) (b0 b1 b2 scan : Bool)
    (ctx : G1Ctx) :
    g1Transition phase (g1State .bWalk .p1 b0 b1 b2 ctx) scan =
      (0, g1State .bWalk .p0 scan b1 b2 ctx, scan, .left) := rfl

private theorem g1Transition_bWalk_p0_raw (phase : Fin 1)
    (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State .bWalk .p0 b0 b1 b2 ctx) scan =
      (if decodeG1Frame? [scan, b0, b1, b2] = some .index then
          (0, g1MarkState ctx, scan, .stay)
        else (0, g1WalkState ctx, scan, .left)) :=
  rfl

/-- **The marker stops the reverse read.**  On an `index` frame the fourth step
*stays*, so the head is left on that frame's first cell, and the control enters
the write handoff. -/
theorem g1Transition_bWalk_p0_index (phase : Fin 1) (b0 b1 b2 scan : Bool)
    (ctx : G1Ctx) (heq : decodeG1Frame? [scan, b0, b1, b2] = some .index) :
    g1Transition phase (g1State .bWalk .p0 b0 b1 b2 ctx) scan =
      (0, g1MarkState ctx, scan, .stay) := by
  rw [g1Transition_bWalk_p0_raw, if_pos heq]

/-- **Any other frame continues the reverse read** one frame further left. -/
theorem g1Transition_bWalk_p0_other (phase : Fin 1) (b0 b1 b2 scan : Bool)
    (ctx : G1Ctx) (hne : decodeG1Frame? [scan, b0, b1, b2] ≠ some .index) :
    g1Transition phase (g1State .bWalk .p0 b0 b1 b2 ctx) scan =
      (0, g1WalkState ctx, scan, .left) := by
  rw [g1Transition_bWalk_p0_raw, if_neg hne]

/-! The four write rows.  Each writes a **fixed** cell of `G1Frame.spent.bits =
[true, true, false, false]` and moves right, whatever it scans: the code is in
the finite control, not on the tape. -/

theorem g1Transition_bMark_p0 (phase : Fin 1) (b0 b1 b2 scan : Bool)
    (ctx : G1Ctx) :
    g1Transition phase (g1State .bMark .p0 b0 b1 b2 ctx) scan =
      (0, g1State .bMark .p1 false false false ctx, true, .right) := rfl

theorem g1Transition_bMark_p1 (phase : Fin 1) (b0 b1 b2 scan : Bool)
    (ctx : G1Ctx) :
    g1Transition phase (g1State .bMark .p1 b0 b1 b2 ctx) scan =
      (0, g1State .bMark .p2 false false false ctx, true, .right) := rfl

theorem g1Transition_bMark_p2 (phase : Fin 1) (b0 b1 b2 scan : Bool)
    (ctx : G1Ctx) :
    g1Transition phase (g1State .bMark .p2 b0 b1 b2 ctx) scan =
      (0, g1State .bMark .p3 false false false ctx, false, .right) := rfl

theorem g1Transition_bMark_p3 (phase : Fin 1) (b0 b1 b2 scan : Bool)
    (ctx : G1Ctx) :
    g1Transition phase (g1State .bMark .p3 b0 b1 b2 ctx) scan =
      (0, g1State .bBack .p0 false false false ctx, false, .right) := rfl

/-! The four back-walk rows and the hop.  All five write back the scanned cell,
so they are tape-preserving. -/

theorem g1Transition_bBack_p0 (phase : Fin 1) (b0 b1 b2 scan : Bool)
    (ctx : G1Ctx) :
    g1Transition phase (g1State .bBack .p0 b0 b1 b2 ctx) scan =
      (0, g1State .bBack .p1 false false false ctx, scan, .left) := rfl

theorem g1Transition_bBack_p1 (phase : Fin 1) (b0 b1 b2 scan : Bool)
    (ctx : G1Ctx) :
    g1Transition phase (g1State .bBack .p1 b0 b1 b2 ctx) scan =
      (0, g1State .bBack .p2 false false false ctx, scan, .left) := rfl

theorem g1Transition_bBack_p2 (phase : Fin 1) (b0 b1 b2 scan : Bool)
    (ctx : G1Ctx) :
    g1Transition phase (g1State .bBack .p2 b0 b1 b2 ctx) scan =
      (0, g1State .bBack .p3 false false false ctx, scan, .left) := rfl

theorem g1Transition_bBack_p3 (phase : Fin 1) (b0 b1 b2 scan : Bool)
    (ctx : G1Ctx) :
    g1Transition phase (g1State .bBack .p3 b0 b1 b2 ctx) scan =
      (0, g1State .bHop .p0 false false false ctx, scan, .left) := rfl

/-- **The hop.**  One further left step re-enters the reverse read on the last
cell of the frame preceding the rewritten one. -/
theorem g1Transition_bHop (phase : Fin 1) (position : G1FramePosition)
    (b0 b1 b2 scan : Bool) (ctx : G1Ctx) :
    g1Transition phase (g1State .bHop position b0 b1 b2 ctx) scan =
      (0, g1WalkState ctx, scan, .left) := rfl

end Pnp3.Internal.PsubsetPpoly.TM
