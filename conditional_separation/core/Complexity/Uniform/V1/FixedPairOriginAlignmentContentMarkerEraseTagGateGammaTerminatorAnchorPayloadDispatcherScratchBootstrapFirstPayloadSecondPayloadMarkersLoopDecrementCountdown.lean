import Complexity.Uniform.V1.SequentialComposition
import
  Complexity.Uniform.V1.FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
/-!
# The pair origin alignment, the trailing content-marker erasure, the content tag gate, the gamma
terminator, the gamma anchor, the payload dispatcher, the scratch bootstrap, the first payload digit,
the second payload digit, the loop markers, the payload loop, the decrement and the countdown as one
machine (Part A G3l)

**No new table row.**  `machine` is `FixedPairOriginAlignment.machine.seq` the whole landed G3k
composite: the alignment phase's fixed 26-state, 78-row block-to-origin shift on `[0, 26)` and G3k's
151 states on `[26, 177)`, one closed 177-state, 531-row table whose every row is a row of one of
those thirteen tables with its target routed.  Write `N = a + m` and `d = borrow x w zeros`.
`pnp3/Docs/UniformP_V1.md` carries the long-form notes.
Classification (AGENTS.md): **Infrastructure**.

**Twelve executed handoffs.**  H6 — the origin-alignment phase into the marker-erase scan — is the
newly executed one, and in forward execution order it is the first of this chain with more than one
live routed row: **three**, the alignment states `10`, `11` and `12` on `none`, which
`accept_rows_unique` proves are the only rows targeting the phase's accept once the accept's own
absorbing three are excluded.  (H11, further right and executed by G3g, already routes six.)  `seq`
retargets all three to the right block's start `tailStart` at index `26`, each keeping its own written
symbol — `none`, `some false`, `some true`, the three restoration writes — and its **left** move, in
that same transition and at no cost.  The alignment phase's working state names are `private`, and no
landed theorem identifies the control one step before the clock, so **which** of the three fires on a
given input is not claimed here; the surface test exhibits each of the three by kernel reduction at a
fixture.  The endpoint head is `0`, which is what `seq_handoff` transports: it uses the post-move
head, and `run_exact` pins that to `0`.  That routed `.left` move is a genuine step onto the origin,
**not** a clamp: the landed `boundary_clamps` puts the phase's sole left clamp two steps earlier, at
source time `clock - 3`, where the head is already `0` and `moveHead_left_zero` (in `Machine.lean`)
applies; `check_h6_literal_probe` exhibits the switch carrying the head from cell `1` to `0`.  On the
reject side every row of the alignment table targeting its reject is one of **21** — the five `none`
rows of states `4, 5, 6, 16, 18` and the sixteen Boolean rows of states
`0, 13, 14, 15, 19, 20, 21, 23` — `reject_rows_unique` proves that list exhaustive over all `26`
states and all three symbols once both verdicts' own absorbing rows are excluded, and
`reject_rows_routed` sends each to the composed reject `176` with the symbol written and the move
unchanged.  None is *taken* out of this `startConfig`: `alignment_first_arrival` proves the left block
never enters its reject there at any time, so the composed reject is reachable only through the right
block.  The left copies of the two alignment verdicts are dead: no composed row targets either, and
the start is neither (`table_and_resource_pins`).  H7 (`27 → 30`), H8 (`42 → 45`), H9 (`45 → 48`),
H10 (`51 → 54`) and H11 (six rows inside `[54, 82)`, all into `82`) to H17 (`163 → 166`) are inherited
from G3k, its indices shifted by twenty-six and located by `(inTail q).val = 26 + q.val` with the
universal right-block row equation.

**The feasibility of this one step, as measured before it was built.**  The alignment phase has
exactly two absorbing states, `qAccept` and `qReject` — its raw states `24` and `25`, three rows each
— so the landed `seq` routes both and no `mergeAccept` is needed, as for H7 to H10 and unlike H11.
Its strict first arrival *was* already exported in the shape `UniformTM.seq_handoff` consumes: the
landed `strict_first_terminal` gives both halves against the phase's `qAccept` and `qReject`, which
its own landed `resource_pins` identifies with `machine.accept` and `machine.reject`, and it takes
**no hypothesis at all**, so `alignment_first_arrival` only repackages it at
`switchTime a m = clock a m` and adds the never-rejects consequence, from the landed
`accepting_absorption`.  `run_exact` alone would **not** suffice: it is one endpoint identity, and an
absorbing phase satisfies it at every later time too, while `seq_handoff` starts the right machine
inside the accepting transition and so needs the absence of any earlier acceptance.  The endpoint is
compatible with the right block's start by construction: the marker-erase `startConfig` is built
field-for-field out of the alignment `finalConfig`, which `run_exact` shows *is* the alignment run at
`switchTime a m` for every input, and `marker_erase_start_at_first_arrival` records that
hypothesis-free as whole-`Config` equality.  So the switch hands over exactly the head and tape the
right block's own `startConfig` carries — the `alignedTape`, on the origin cell `0`, the trailing
marker at `N` still present, erased `N + 3` steps later by the inherited H7 row.

**The switch time is the first in this chain to depend on the split lengths `a` and `m` separately.**
The landed switch times are of three kinds, none of them a function of the split: length-only in
`N = a + m` (H7's `N + 3`, H8's `3 * N + 7`), width-only in the decoded `zeros` (H9's `zeros + 1`,
H10's `successTime zeros = 2 * zeros + 5`) and input-dependent (H11's `C`, with no length formula).
The alignment clock is quadratic in `a` and reads the two lengths apart, so `switchTime` here takes
**two** arguments and so does `alignmentChainClock`.  `clock_pins` records that break explicitly and
exhibits three different values at one `N`.  The composed clock is therefore quadratic in `a`, and
whether the cubic budget still dominates it is *not* proved.

**The composed run.**  `handoff_exact` takes **no hypothesis** — no tag, no width, no room, no
positive budget, no budget-dominates-clock premise: the run out of `startConfig` stays strictly inside
the left block `[0, 26)` at every time strictly before `switchTime a m`, is in neither composed verdict
at any time up to and including it (at the switch time itself the control is `tailStart`, so that bound
is `≤`), is the alignment phase's own run routed at every such time as whole-`Config` equality, at
exactly `switchTime a m` **is** G3k's landed `startConfig B x w` re-embedded, and every later step is
a G3k step.  `handoff_endpoint_pins` reads that switch configuration back as G3k's own and as the
marker-erase phase's own `startConfig` projections, and records the origin head `0`, the
`alignedTape`, the marker `some true` still on cell `N`, and blanks above it.
`inherited_marker_erase_switch` locates the inherited H7 at `switchTime a m + (N + 3)`, at index `30`,
on exactly the head and tape G1's own `startConfig` carries.  The four deeper inherited locators — H8
at `45`, H9 at `48`, H10 at `54`, H11 at `82` — are **not** re-wrapped here: `handoff_exact`'s last
conjunct is a universal suffix equality, so G3k's own `tagged_inherited_switch`,
`tagged_inherited_terminator_switch`, `tagged_inherited_anchor_switch` and
`tagged_inherited_dispatcher_switch` transport into this machine by composing that one equation with
`UniformTM.seqEmbedRight_state/_head/_tape` and `(inTail q).val = 26 + q.val`, exactly as
`inherited_marker_erase_switch` does for H7; no fact is lost and none is claimed that is not proved.
The drained theorem lands the composed accept `175` at exactly
`alignmentChainClock C a m zeros d v = switchTime a m + eraseChainClock C N zeros d v` under G3k's
eight hypotheses unchanged.  Two rejecting branches are inherited, both forward direction only.  On a
matching tag whose physical suffix holds **no** gamma terminator the whole prefix hands over and
`malformed_reject_handoff` lands the composed reject `176` from
`switchTime a m + (N + 3 + (3 * N + 7 + (N - 7)))` on.  On a **mismatched** tag
`mismatched_tag_reject_handoff` lands it from `switchTime a m + (N + 3 + (3 * N + 7))` on, the gamma
blocks never running; that branch is deliberately **not** timed exactly, for the reason G3j and G3k
record — on a nonempty content the gate's own first rejection is at `3 * N + j` for its mismatch cell
`j`, which this chain does not derive from `tagMatches (Fin.append x w) = false`, the value of
`FixedContentTagGate.finalConfig`'s head being the only public trace of the `badIndex` that defines it
— and the composed run may already be in the composed reject before the time stated.

Deferred, and deliberately not claimed.  `startConfig` still **embeds** every earlier phase: the five
handoffs before H6 remain proof-level identifications (the alignment `startConfig` retags the actual
origin-shift-bootstrap `finalConfig`, which `handoff_pins` records hypothesis-free), no raw-input
`initialConfig` is executed, and no clock here counts a step of any phase *before* origin alignment —
this clock does count the alignment phase's own `(10 * a + 7) * (N + 1) + 3 * a` steps, which no
landed clock in this chain did.  No **first arrival** of the composed accept: the arrivals proved are
the alignment phase's and, as a hypothesis, the dispatcher's, each inside its own block.  The
**fence** (all thirteen tables are uncapped, and `hfence` is a proof premise the tables do not
enforce, so an oversized register still times out); every **converse**, so neither composed reject
implies anything about the input; a **footprint** theorem, the alignment phase's own bounding its head
only through its own clock and saying nothing about the right block; and the pnp4 bridge, not built
here, the standalone phases' pnp4 semantics being unchanged.  The composed `accept` is the countdown's
phase-local `qDone`: reaching it out of a retagged actual prior endpoint is neither halting on a raw
input nor language acceptance; no `accepts`, `AcceptsAt`, `DecidesWithin`, `UniformP` or
`ContentVerifierBridge` is stated.  `run` permits more steps than `B`, which fixes the tape extent and
is not a timeout guard.  The table is fixed and complete but not claimed state-minimal. -/
namespace
  Pnp3.Complexity.Uniform.V1.FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown

open PairEncoding
open FixedContentGammaTerminator (gammaZeros?)
open FixedContentGammaAnchor (successTime markedTape)
open FixedGammaPayloadDispatcherFirstArrival (StrictFirstTerminalAt)
open FixedGammaTargetPayloadExhaustion (totalClock)
open FixedGammaTargetDecrementCountdown (composedClock)
open FixedGammaTargetRegisterDecrement (borrow decBit)
open FixedGammaTargetUnaryCountdown (loopTape)
open FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
  (bootChainClock)
open FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
  (eraseChainClock)

/-- The right block: the machine of the landed G3k composite, named once so that the statements below
stay readable.  An `abbrev`, hence reducible, so every pin below is a pin on that machine itself;
`table_and_resource_pins` spells the identification out. -/
abbrev tailMachine : UniformTM :=
  FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine

/-- The right block's own start configuration: G3k's landed `startConfig`, named once.  Also an
`abbrev`; `marker_erase_start_at_first_arrival` identifies it with what this switch hands over. -/
abbrev tailStartConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config tailMachine.stateCount (pairLength a m) B :=
  FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.startConfig
    B x w

/-- The composed machine: the origin-alignment phase, then G3k's whole composite, as one closed
table.  No row is new; the left rows are routed. -/
def machine : UniformTM := FixedPairOriginAlignment.machine.seq tailMachine

/-- An alignment state in the composed control, at its own index. -/
def inAlign (q : Fin FixedPairOriginAlignment.alignmentStateCount) : Fin machine.stateCount :=
  FixedPairOriginAlignment.machine.seqLeft tailMachine q

/-- A G3k state in the composed control, shifted past the twenty-six alignment states. -/
def inTail (q : Fin tailMachine.stateCount) : Fin machine.stateCount :=
  FixedPairOriginAlignment.machine.seqRight tailMachine q

/-- The routed target of an alignment row: `qAccept` becomes G3k's start, `qReject` the composed
reject, every working state itself. -/
def route (q : Fin FixedPairOriginAlignment.alignmentStateCount) : Fin machine.stateCount :=
  FixedPairOriginAlignment.machine.seqRoute tailMachine q

/-- G3k's start in the composed control, index `26`: the common target of the three live routed
rows. -/
def tailStart : Fin machine.stateCount := inTail tailMachine.start

/-- The alignment phase's own `startConfig` — the retagged *actual* origin-shift-bootstrap endpoint —
routed into the composed control.  Still a phase-local retag, not `initialConfig` on a raw pair
input. -/
def startConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config machine.stateCount (pairLength a m) B :=
  FixedPairOriginAlignment.machine.seqEmbedRouted tailMachine
    (FixedPairOriginAlignment.startConfig B x w)

/-- The alignment phase's strict first arrival, for every input: its own landed `clock a m`.  **Not**
a function of `a + m`: the landed `clock_exact` reads it as
`2 + a * (10 * (a + m + 1) + 3) + (7 * (a + m) + 5)` — `a` walks of the whole `(a + m + 1)`-cell block
at ten steps per source cell, then one linear closing sweep — that is,
`10 * a * a + 10 * a * m + 20 * a + 7 * m + 7`, quadratic in `a` and with a cross term in `a * m`. -/
def switchTime (a m : Nat) : Nat := (10 * a + 7) * (a + m + 1) + 3 * a

/-- Exact cost of the origin alignment followed by the whole of G3k: the alignment phase's
length-pair-dependent first arrival, plus the marker-erase scan's length-only `N + 3`, plus the tag
gate's length-only `3 * N + 7`, plus the terminator's width-only `zeros + 1`, plus the anchor's
width-only `2 * zeros + 5`, plus the dispatcher's input-dependent `C`, plus G3e's `bootChainClock`.
All six handoffs cost nothing. -/
def alignmentChainClock (C a m zeros d v : Nat) : Nat :=
  switchTime a m + eraseChainClock C (a + m) zeros d v

/-! ### Table, resource, handoff and clock pins -/

set_option maxRecDepth 40000 in
/-- The composed table, pinned: the composition itself spelled out, both blocks' state counts, the
composed state and row counts, the alignment start and verdicts with their indices, G3k's three
distinguished states with theirs, the composed distinguished states with theirs, the block injections
with their offsets and disjointness, `tailStart` at `26`, the three routing cases, every left row as
the routed alignment row, every right row as the G3k row, the public step against the composed raw
table, the **three** live routed rows — the alignment states `10`, `11` and `12` on `none`, writing
`none`, `some false` and `some true` and moving **left** — the two dead verdict copies' three rows
each, and that no **left-block** row targets either dead copy.  The two injective, disjoint block maps
have domain sizes `26` and `151`, summing to the composed state count `177`, so they cover every
state.  Thus the two block equations account for every composed row, and block disjointness excludes
right-block targets from the dead left copies as well.  The right-block equation transports every G3k
row.  Deciding rows of a table this deep unfolds the whole thirteen-block composition, so the kernel
needs a raised recursion budget here. -/
theorem table_and_resource_pins :
    machine = FixedPairOriginAlignment.machine.seq
        FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine ∧
      tailMachine =
        FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine ∧
      machine.stateCount = 177 ∧ Fintype.card (Fin machine.stateCount × Option Bool) = 531 ∧
      FixedPairOriginAlignment.machine.stateCount = 26 ∧ tailMachine.stateCount = 151 ∧
      FixedPairOriginAlignment.machine.start.val = 0 ∧
      FixedPairOriginAlignment.machine.accept.val = 24 ∧
      FixedPairOriginAlignment.machine.reject.val = 25 ∧
      tailMachine.start.val = 0 ∧ tailMachine.accept.val = 149 ∧ tailMachine.reject.val = 150 ∧
      machine.start = route FixedPairOriginAlignment.machine.start ∧
      machine.start = inAlign FixedPairOriginAlignment.machine.start ∧
      machine.accept = inTail tailMachine.accept ∧ machine.reject = inTail tailMachine.reject ∧
      machine.start.val = 0 ∧ machine.accept.val = 175 ∧ machine.reject.val = 176 ∧
      (∀ q, (inAlign q).val = q.val) ∧ (∀ q, (inAlign q).val < 26) ∧
      (∀ q, (inTail q).val = 26 + q.val) ∧ (∀ q, 26 ≤ (inTail q).val) ∧
      Function.Injective inAlign ∧ Function.Injective inTail ∧
      (∀ p q, inAlign p ≠ inTail q) ∧
      tailStart = inTail tailMachine.start ∧ tailStart.val = 26 ∧
      route FixedPairOriginAlignment.machine.accept = tailStart ∧
      route FixedPairOriginAlignment.machine.reject = machine.reject ∧
      (∀ q, q ≠ FixedPairOriginAlignment.machine.accept →
        q ≠ FixedPairOriginAlignment.machine.reject → route q = inAlign q) ∧
      (∀ q s, machine.step (inAlign q) s =
        (route (FixedPairOriginAlignment.machine.step q s).1,
          (FixedPairOriginAlignment.machine.step q s).2.1,
          (FixedPairOriginAlignment.machine.step q s).2.2)) ∧
      (∀ q s, machine.step (inTail q) s =
        (inTail (tailMachine.step q s).1, (tailMachine.step q s).2.1,
          (tailMachine.step q s).2.2)) ∧
      (∀ q s, machine.step q s = machine.rawStep q s) ∧
      machine.step (inAlign ⟨10, by decide⟩) none = (tailStart, none, .left) ∧
      machine.step (inAlign ⟨11, by decide⟩) none = (tailStart, some false, .left) ∧
      machine.step (inAlign ⟨12, by decide⟩) none = (tailStart, some true, .left) ∧
      (∀ s, machine.step (inAlign FixedPairOriginAlignment.machine.accept) s =
        (tailStart, s, .stay)) ∧
      (∀ s, machine.step (inAlign FixedPairOriginAlignment.machine.reject) s =
        (machine.reject, s, .stay)) ∧
      (∀ q s, (machine.step (inAlign q) s).1 ≠
          inAlign FixedPairOriginAlignment.machine.accept ∧
        (machine.step (inAlign q) s).1 ≠
          inAlign FixedPairOriginAlignment.machine.reject) := by
  obtain ⟨-, -, -, -, -, -, hli, hri, hne, hra, hrr, hrw⟩ :=
    FixedPairOriginAlignment.machine.seq_pins tailMachine
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, by decide, rfl, ?_,
    rfl, rfl, by decide, by decide, by decide, fun _ => rfl, fun q => q.isLt, fun _ => rfl,
    fun _ => Nat.le_add_right _ _, hli, hri, hne, rfl, by decide, hra, hrr, hrw,
    fun q s => FixedPairOriginAlignment.machine.seq_step_left tailMachine q s,
    fun q s => FixedPairOriginAlignment.machine.seq_step_right tailMachine q s,
    fun q s => FixedPairOriginAlignment.machine.seq_step_eq_rawStep tailMachine q s,
    by decide, by decide, by decide, ?_, ?_, by decide⟩
  · exact hrw FixedPairOriginAlignment.machine.start (by decide) (by decide)
  · intro s; cases s with
    | none => decide
    | some b => cases b <;> decide
  · intro s; cases s with
    | none => decide
    | some b => cases b <;> decide

/-- **The alignment table has exactly three rows targeting its accept.**  Over all twenty-six states
and all three symbols, with the accept's own absorbing three excluded, a target of
`FixedPairOriginAlignment.machine.accept` forces one of the three classification states `10`, `11`,
`12` on `none`.  So H6 has exactly three live routed rows — plural, the first such in forward
execution order (H11, further right, already routes six), and they write three different symbols,
`table_and_resource_pins` exhibiting all three.  Which one fires on a given input is **not**
stated: those three states are `private` in the landed phase and no landed theorem identifies the
control at `clock - 1`.  This quantifies over the alignment rows alone and says nothing about the
composed table as a whole: the inherited right block keeps its own rows, and the only rows this
excludes are the dead left accept copy's own three — the reject copy's are *not* excluded here —
which `seq` routes to `tailStart` and no composed row ever enters. -/
theorem accept_rows_unique (q : Fin FixedPairOriginAlignment.alignmentStateCount) (s : Option Bool)
    (hq : q ≠ FixedPairOriginAlignment.machine.accept)
    (h : (FixedPairOriginAlignment.machine.rawStep q s).1 =
      FixedPairOriginAlignment.machine.accept) :
    (q.val = 10 ∨ q.val = 11 ∨ q.val = 12) ∧ s = none := by
  revert h
  revert hq
  revert s
  revert q
  decide

/-- **Every row of the alignment table targeting its reject is one of twenty-one.**  Over all
twenty-six states and all three symbols, with both verdicts' own absorbing rows excluded, a target of
`FixedPairOriginAlignment.machine.reject` forces either `none` on one of `4, 5, 6, 16, 18` — the five
probes that find the tape exhausted — or a Boolean on one of `0, 13, 14, 15, 19, 20, 21, 23` — the
sixteen rows that find a cell occupied where the shift invariant requires it blank.  That single
direction is what is stated — the list is exhaustive.  Its converse, that each of the twenty-one does
target the reject, is **not** stated here; `check_reject_row_literals` exhibits three of them.  It is
a statement about the fixed table, not about reachability: `alignment_first_arrival` proves no row of
it is ever taken out of this slice's `startConfig`, and it characterises no malformed configuration in
general. -/
theorem reject_rows_unique (q : Fin FixedPairOriginAlignment.alignmentStateCount) (s : Option Bool)
    (ha : q ≠ FixedPairOriginAlignment.machine.accept)
    (hq : q ≠ FixedPairOriginAlignment.machine.reject)
    (h : (FixedPairOriginAlignment.machine.rawStep q s).1 =
      FixedPairOriginAlignment.machine.reject) :
    (s = none ∧ (q.val = 4 ∨ q.val = 5 ∨ q.val = 6 ∨ q.val = 16 ∨ q.val = 18)) ∨
      (s ≠ none ∧ (q.val = 0 ∨ q.val = 13 ∨ q.val = 14 ∨ q.val = 15 ∨ q.val = 19 ∨
        q.val = 20 ∨ q.val = 21 ∨ q.val = 23)) := by
  revert h
  revert hq
  revert ha
  revert s
  revert q
  decide

/-- **Every row targeting the alignment reject is routed to the composed reject `176`.**  `seq` sends
each of the twenty-one to the composed reject, with the symbol written and the move unchanged.  The
two verdicts' own rows are excluded: both of their left copies are dead. -/
theorem reject_rows_routed (q : Fin FixedPairOriginAlignment.alignmentStateCount) (s : Option Bool)
    (ha : q ≠ FixedPairOriginAlignment.machine.accept)
    (hq : q ≠ FixedPairOriginAlignment.machine.reject)
    (h : (FixedPairOriginAlignment.machine.rawStep q s).1 =
      FixedPairOriginAlignment.machine.reject) :
    machine.step (inAlign q) s =
      (machine.reject, (FixedPairOriginAlignment.machine.rawStep q s).2.1,
        (FixedPairOriginAlignment.machine.rawStep q s).2.2) := by
  have hstep : FixedPairOriginAlignment.machine.step q s =
      FixedPairOriginAlignment.machine.rawStep q s :=
    FixedPairOriginAlignment.machine.step_of_ne ha hq s
  have hleft : machine.step (inAlign q) s =
      (route (FixedPairOriginAlignment.machine.step q s).1,
        (FixedPairOriginAlignment.machine.step q s).2.1,
        (FixedPairOriginAlignment.machine.step q s).2.2) :=
    FixedPairOriginAlignment.machine.seq_step_left tailMachine q s
  rw [hleft, hstep, h]
  rfl

/-- **The start is the retagged actual origin-shift-bootstrap endpoint, not a raw input, and this
needs no hypothesis.**  The bootstrap phase's run at its own clock is its `finalConfig`, on the cell
`pairLength a m + min B 1` over the once-shifted tape whose content-plus-marker block starts at cell
`a`; the alignment `startConfig` is that configuration retagged; and this slice's `startConfig` is
*that* one routed into the composed control — the same head and tape, the composed start `0` as
control.  This is handoff **H5**, recorded as an identification and not executed by this table.  No
`initialConfig` and no raw pair input appears, neither retag costs a step, and no table row of any
phase before the alignment is pinned. -/
theorem handoff_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let g := FixedPairOriginShiftBootstrap.machine.run (FixedPairOriginShiftBootstrap.clock a m)
      (FixedPairOriginShiftBootstrap.startConfig B x w)
    let p := FixedPairOriginAlignment.startConfig B x w
    let c := startConfig B x w
    g = FixedPairOriginShiftBootstrap.finalConfig B x w ∧
      g.state = FixedPairOriginShiftBootstrap.qAccept ∧
      p = FixedPairOriginAlignment.retag g ∧
      p.state = FixedPairOriginAlignment.machine.start ∧ p.head = g.head ∧ p.tape = g.tape ∧
      c = FixedPairOriginAlignment.machine.seqEmbedRouted tailMachine p ∧
      c.state = machine.start ∧ c.state = inAlign FixedPairOriginAlignment.machine.start ∧
      c.head = g.head ∧ c.tape = g.tape ∧ c.head.val = pairLength a m + Nat.min B 1 ∧
      c.tape = FixedPairOriginShiftBootstrap.shiftedTape B x w := by
  obtain ⟨hfin, hst, -, hhead, htape⟩ := FixedPairOriginAlignment.handoff_exact (B := B) x w
  obtain ⟨-, -, hhv, htv⟩ := FixedPairOriginShiftBootstrap.final_fields (B := B) x w
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hrw⟩ :=
    FixedPairOriginAlignment.machine.seq_pins tailMachine
  refine ⟨hfin, hst, ?_, rfl, hhead, htape, rfl, rfl,
    hrw FixedPairOriginAlignment.machine.start (by decide) (by decide), hhead, htape, ?_, ?_⟩
  · rw [hfin]; rfl
  · rw [show (startConfig B x w).head = _ from hhead]; exact hhv
  · rw [show (startConfig B x w).tape = _ from htape]; exact htv

/-- The chained clock, pinned: G3k's sum prefixed by the alignment phase's first arrival, that arrival
identified with the phase's own landed `clock` and given in both landed closed forms, the marker-erase
scan's length-only arrival, the tag gate's length-only arrival and its own deadline, the two
width-only arrivals G3i and G3h contribute, and on `2 ≤ zeros` the full expansion.  `C` has no closed
form in `N`.  **`switchTime` is not a function of `a + m`**: the three pairs with `a + m = 2` give
`21`, `54` and `87`, so no reformulation of this chain's clock on `N` alone is possible, and the
composed clock is quadratic in `a`. -/
theorem clock_pins (C a m zeros d v : Nat) :
    alignmentChainClock C a m zeros d v = switchTime a m + eraseChainClock C (a + m) zeros d v ∧
      switchTime a m = (10 * a + 7) * (a + m + 1) + 3 * a ∧
      switchTime a m = FixedPairOriginAlignment.clock a m ∧
      switchTime a m = 10 * a * a + 10 * a * m + 20 * a + 7 * m + 7 ∧
      switchTime 0 0 = 7 ∧ switchTime 0 2 = 21 ∧ switchTime 1 1 = 54 ∧ switchTime 2 0 = 87 ∧
      (∀ z : Nat,
        FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
          z = z + 3) ∧
      (∀ a' m' : Nat, FixedContentTagGate.deadline a' m' = 3 * (a' + m') + 7) ∧
      (∀ z : Nat, successTime z = 2 * z + 5) ∧
      alignmentChainClock C a m zeros d v =
        switchTime a m + (a + m + 3 + (3 * (a + m) + 7 + (zeros + 1 + (2 * zeros + 5 +
          (C + bootChainClock (a + m) zeros d v))))) ∧
      (2 ≤ zeros → alignmentChainClock C a m zeros d v =
        switchTime a m + (a + m + 3 + (3 * (a + m) + 7 + (zeros + 1 + (2 * zeros + 5 +
          (C + (2 * (a + m) - 11 - zeros + (2 * (a + m) + zeros - 6 + (2 * (a + m) - 7 +
            (zeros + 7 + (totalClock (a + m) zeros +
              composedClock (a + m) zeros d v))))))))))) := by
  refine ⟨rfl, rfl, rfl, (FixedPairOriginAlignment.clock_exact a m).2.1, rfl, rfl, rfl, rfl,
    fun _ => rfl, fun _ _ => rfl, fun _ => rfl, rfl, fun hz => ?_⟩
  show switchTime a m + eraseChainClock C (a + m) zeros d v = _
  rw [(FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.clock_pins
    C (a + m) zeros d v).2.2.2.2.2.2.2.2 hz]

/-! ### The alignment phase's arrival, in the shape the composition consumes -/

/-- **The alignment phase's strict first arrival, for every input and with no hypothesis.**  It is in
neither verdict at every time before `switchTime a m`, at that time its run **is** its `finalConfig`
and its control its accept, that time **equals** its own landed `clock a m`, and it is never in its
reject at any time at all.  The first three conjuncts repackage the landed `strict_first_terminal` and
`run_exact`, which state the two verdicts as the phase's own `qAccept` and `qReject` — its landed
`resource_pins` identifies those with `machine.accept` and `machine.reject`; the last adds the landed
`accepting_absorption`, which keeps the accepting endpoint unchanged from the clock on.  Empty inputs
and a zero budget are included: `clock 0 0 = 7`, so the strictness range is never empty. -/
theorem alignment_first_arrival {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    (∀ t, t < switchTime a m →
        (FixedPairOriginAlignment.machine.run t
            (FixedPairOriginAlignment.startConfig B x w)).state ≠
          FixedPairOriginAlignment.machine.accept ∧
        (FixedPairOriginAlignment.machine.run t
            (FixedPairOriginAlignment.startConfig B x w)).state ≠
          FixedPairOriginAlignment.machine.reject) ∧
      FixedPairOriginAlignment.machine.run (switchTime a m)
          (FixedPairOriginAlignment.startConfig B x w) =
        FixedPairOriginAlignment.finalConfig B x w ∧
      (FixedPairOriginAlignment.machine.run (switchTime a m)
          (FixedPairOriginAlignment.startConfig B x w)).state =
        FixedPairOriginAlignment.machine.accept ∧
      switchTime a m = FixedPairOriginAlignment.clock a m ∧
      (∀ t, (FixedPairOriginAlignment.machine.run t
          (FixedPairOriginAlignment.startConfig B x w)).state ≠
        FixedPairOriginAlignment.machine.reject) := by
  obtain ⟨hno, hacc⟩ := FixedPairOriginAlignment.strict_first_terminal (B := B) x w
  have hrun : FixedPairOriginAlignment.machine.run (switchTime a m)
      (FixedPairOriginAlignment.startConfig B x w) =
      FixedPairOriginAlignment.finalConfig B x w :=
    FixedPairOriginAlignment.run_exact B x w
  refine ⟨hno, hrun, hacc, rfl, fun t => ?_⟩
  by_cases ht : t < switchTime a m
  · exact (hno t ht).2
  · have hle : FixedPairOriginAlignment.clock a m ≤ t := by
      have : ¬ t < FixedPairOriginAlignment.clock a m := ht
      omega
    rw [show t = FixedPairOriginAlignment.clock a m +
        (t - FixedPairOriginAlignment.clock a m) by omega,
      (FixedPairOriginAlignment.accepting_absorption x w
        (t - FixedPairOriginAlignment.clock a m)).1]
    exact FixedPairOriginAlignment.machine.accept_ne_reject

/-- G3k's `startConfig` is the alignment run at `switchTime a m`, field for field — and this holds for
**every** input, because the phase's `run_exact` is unconditional.  This is the semantic dependency H6
has to respect; it executes nothing.  The last conjunct is the whole-`Config` equality
`UniformTM.seq_handoff` consumes: the right block's start configuration *is* G3k's start on the head
and tape the alignment phase leaves, not merely a tape agreement or an equal numeric head. -/
theorem marker_erase_start_at_first_arrival {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let g := FixedPairOriginAlignment.machine.run (switchTime a m)
      (FixedPairOriginAlignment.startConfig B x w)
    g = FixedPairOriginAlignment.finalConfig B x w ∧
      (FixedPairContentMarkerErase.startConfig B x w).state =
        FixedPairContentMarkerErase.machine.start ∧
      (FixedPairContentMarkerErase.startConfig B x w).head = g.head ∧
      (FixedPairContentMarkerErase.startConfig B x w).tape = g.tape ∧
      tailStartConfig B x w = ⟨tailMachine.start, g.head, g.tape⟩ := by
  dsimp
  rw [show FixedPairOriginAlignment.machine.run (switchTime a m)
      (FixedPairOriginAlignment.startConfig B x w) =
      FixedPairOriginAlignment.finalConfig B x w from
    FixedPairOriginAlignment.run_exact B x w]
  exact ⟨rfl, rfl, rfl, rfl, Config.ext_parts rfl rfl rfl⟩

/-! ### The executed handoff -/

/-- **H6 fires when the alignment phase restores the cell it probed and steps left onto the origin,
and it costs nothing.**  With **no hypothesis** — no tag, no width, no room, no positive budget — the
run out of `startConfig` stays strictly inside the left block `[0, 26)` at every time strictly before
`switchTime a m`, is in neither composed verdict at any time up to and including it (at the switch
time itself the control is `tailStart`, so that bound is `≤`), is the alignment phase's own run routed
at every such time — same head and whole tape — at exactly `switchTime a m` **is** G3k's landed
`startConfig B x w` re-embedded, and runs G3k on from there. -/
theorem handoff_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let cA := FixedPairOriginAlignment.startConfig B x w
    let c := startConfig B x w
    (∀ t, t < switchTime a m → (machine.run t c).state.val < 26) ∧
      (∀ t, t ≤ switchTime a m →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ t, t ≤ switchTime a m → machine.run t c =
        FixedPairOriginAlignment.machine.seqEmbedRouted tailMachine
          (FixedPairOriginAlignment.machine.run t cA)) ∧
      machine.run (switchTime a m) c =
        FixedPairOriginAlignment.machine.seqEmbedRight tailMachine (tailStartConfig B x w) ∧
      (∀ s, machine.run (switchTime a m + s) c =
        FixedPairOriginAlignment.machine.seqEmbedRight tailMachine
          (tailMachine.run s (tailStartConfig B x w))) := by
  intro cA c
  obtain ⟨hno, -, hacc, -, -⟩ := alignment_first_arrival (B := B) x w
  obtain ⟨-, -, -, -, hcfg⟩ := marker_erase_start_at_first_arrival (B := B) x w
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hrw⟩ :=
    FixedPairOriginAlignment.machine.seq_pins tailMachine
  have hwork : ∀ t, t < switchTime a m →
      (FixedPairOriginAlignment.machine.run t cA).state ≠
        FixedPairOriginAlignment.machine.accept := fun t ht => (hno t ht).1
  have hleft := FixedPairOriginAlignment.machine.seq_run_left tailMachine cA hwork
  have hsuffix : ∀ s, machine.run (switchTime a m + s) c =
      FixedPairOriginAlignment.machine.seqEmbedRight tailMachine
        (tailMachine.run s (tailStartConfig B x w)) := by
    intro s
    rw [hcfg]
    exact FixedPairOriginAlignment.machine.seq_handoff tailMachine cA hwork hacc s
  have hC : machine.run (switchTime a m) c =
      FixedPairOriginAlignment.machine.seqEmbedRight tailMachine (tailStartConfig B x w) :=
    hsuffix 0
  have hCs : (machine.run (switchTime a m) c).state = tailStart := by rw [hC]; rfl
  have hCa : (machine.run (switchTime a m) c).state ≠ machine.accept := by rw [hCs]; decide
  have hCr : (machine.run (switchTime a m) c).state ≠ machine.reject := by rw [hCs]; decide
  refine ⟨fun t ht => ?_, UniformTM.no_terminal_of_le machine c hCa hCr, hleft, hC, hsuffix⟩
  have hrt : machine.run t c = FixedPairOriginAlignment.machine.seqEmbedRouted tailMachine
    (FixedPairOriginAlignment.machine.run t cA) := hleft t (Nat.le_of_lt ht)
  rw [hrt]
  show (FixedPairOriginAlignment.machine.seqRoute tailMachine
    (FixedPairOriginAlignment.machine.run t cA).state).val < 26
  rw [hrw _ (hno t ht).1 (hno t ht).2]
  exact (FixedPairOriginAlignment.machine.run t cA).state.isLt

-- The composed index of G3k's start, and of G3k's own tail start, reduced once here so that the five
-- inherited-switch theorems below can shift G3k's indices by twenty-six without each paying for the
-- reduction.
private theorem tail_start_val : tailStart.val = 26 := by decide

private theorem erase_tail_start_val :
    FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.tailStart.val
      = 4 := by decide

private theorem erase_switch_time (N : Nat) :
    FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.switchTime
      N = N + 3 := rfl

/-- Every configuration from the switch on is the right block's own, transported by the one embedding
that shifts the control by twenty-six and preserves the head and the **whole** allocated tape.  The
four projections, stated once, so that the inherited locators below do not each repeat them. -/
private theorem shift_fields {a m B : Nat} (x : Bitstring a) (w : Bitstring m) (s : Nat) :
    let e := machine.run (switchTime a m + s) (startConfig B x w)
    let p := tailMachine.run s (tailStartConfig B x w)
    e.state = inTail p.state ∧ e.state.val = 26 + p.state.val ∧ e.head = p.head ∧
      e.tape = p.tape := by
  have hrun := (handoff_exact (B := B) x w).2.2.2.2 s
  exact ⟨by rw [hrun]; rfl, by rw [hrun]; rfl, by rw [hrun]; rfl, by rw [hrun]; rfl⟩

/-- **What the switch hands over is exactly what the marker-erase scan reads.**  At the alignment
phase's first arrival `switchTime a m`: the composed control is G3k's start `26`, the composed head and
whole tape are *the same* projections G3k's own `startConfig` carries and, field for field, the ones
the marker-erase phase's own `startConfig` carries; the head is the origin cell `0`; the tape is the
`alignedTape`, so the content sits at `[0, a)`, the word at `[a, N)`; the trailing content marker is
**still there**, `some true` on cell `N` — the inherited H7 row erases it `N + 3` steps later — and
every allocated cell above `N` is blank. -/
theorem handoff_endpoint_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let e := machine.run (switchTime a m) (startConfig B x w)
    let p := tailStartConfig B x w
    e.state = tailStart ∧ e.state.val = 26 ∧ e.head = p.head ∧ e.tape = p.tape ∧
      e.head = (FixedPairContentMarkerErase.startConfig B x w).head ∧
      e.tape = (FixedPairContentMarkerErase.startConfig B x w).tape ∧
      e.head.val = 0 ∧ e.tape = FixedPairOriginAlignment.alignedTape B x w ∧
      e.tape ⟨a + m, by unfold tapeLength pairLength; omega⟩ = some true ∧
      (∀ i : Fin (tapeLength (pairLength a m) B), a + m + 1 ≤ i.val → e.tape i = none) := by
  obtain ⟨-, -, -, hC, -⟩ := handoff_exact (B := B) x w
  obtain ⟨-, -, -, -, -, htp, -, -, hmark, hblank⟩ :=
    FixedPairOriginAlignment.final_fields_and_layout (B := B) x w
  rw [FixedPairOriginAlignment.run_exact] at htp hmark hblank
  have hhead : (machine.run (switchTime a m) (startConfig B x w)).head =
      (tailStartConfig B x w).head := congrArg Config.head hC
  have htape : (machine.run (switchTime a m) (startConfig B x w)).tape =
      (tailStartConfig B x w).tape := congrArg Config.tape hC
  have hstate : (machine.run (switchTime a m) (startConfig B x w)).state = tailStart :=
    congrArg Config.state hC
  refine ⟨hstate, by rw [hstate]; exact tail_start_val, hhead, htape, hhead, htape, ?_, ?_, ?_,
    fun i hi => ?_⟩
  · rw [hhead]; rfl
  · rw [htape]; exact htp
  · rw [htape]; exact hmark
  · rw [htape]; exact hblank i hi

/-! ### The inherited switches and the composed run -/

/-- **The inherited H7 fires inside this machine at `switchTime a m + (N + 3)`.**  The alignment
phase's own steps counted first, the composed control is G1's content-tag-gate start at index `30` —
G3k's `4` shifted by the twenty-six alignment states — on exactly the head and tape G1's landed
`startConfig` carries: the boundary cell `N` over the `contentTape`, every allocated cell from `N` on
blank, so the trailing marker really is erased, by the inherited routed row itself. -/
theorem inherited_marker_erase_switch {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let e := machine.run (switchTime a m + (a + m + 3)) (startConfig B x w)
    let p := FixedContentTagGate.startConfig B x w
    e.state.val = 30 ∧ e.head = p.head ∧ e.tape = p.tape ∧
      e.head.val = a + m ∧ e.tape = FixedPairContentMarkerErase.contentTape B x w ∧
      (∀ i : Fin (tapeLength (pairLength a m) B), a + m ≤ i.val → e.tape i = none) := by
  obtain ⟨-, hsv, hhd, htp⟩ := shift_fields x w (a + m + 3)
  obtain ⟨hs, -, -, hhead, htape, hhv, htv, hblank⟩ :=
    FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.handoff_endpoint_pins
      (B := B) x w
  rw [erase_switch_time] at hs hhead htape hhv htv hblank
  refine ⟨?_, hhd.trans hhead, htp.trans htape, by rw [hhd]; exact hhv, htp.trans htv,
    fun i hi => by rw [htp]; exact hblank i hi⟩
  rw [hsv, show (tailMachine.run (a + m + 3) (tailStartConfig B x w)).state.val = 4 from
    by rw [hs]; exact erase_tail_start_val]

/-- **The concrete exact run: the origin alignment, H6, the marker erasure, H7, the content tag gate,
H8, the gamma terminator, H9, the gamma anchor, H10, the payload dispatcher, H11, the scratch
bootstrap, H12, the first and second payload digits, H13 and H14, the markers, H15, the loop, H16, the
decrement, H17 and the countdown, one machine.**  Under G3k's **eight** hypotheses unchanged, after
exactly `alignmentChainClock C a m zeros d v` steps the composed machine is in its accept, the
countdown's `qDone`, on the separator blank `N + 2 + zeros` with tape `loopTape B x w zeros 0 v`,
persisting.  `v` is universally quantified and unsupplied — nothing here decodes it — and persistence
is exact execution at that time plus absorption, not first arrival of the composed accept.  Neither
`C ≤ deadline N` nor a successful-`q` premise is added: `StrictFirstTerminalAt` is the whole
dispatcher hypothesis. -/
theorem origin_alignment_marker_erase_tag_gate_terminator_anchor_dispatcher_scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained
    {a m B C zeros v F : Nat} {q : Fin FixedGammaPayloadDispatcher.stateCount} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = some zeros)
    (h : StrictFirstTerminalAt B x w C q)
    (hzeros : 2 ≤ zeros) (hfence : v ≤ F) (hroom : zeros + 2 + F ≤ a + B)
    (hv : ∀ j, j ≤ zeros → v.testBit (zeros - j) = decBit x w zeros (borrow x w zeros) j)
    (hhigh : ∀ b, zeros < b → v.testBit b = false) :
    let d := borrow x w zeros
    let D := alignmentChainClock C a m zeros d v
    let e := machine.run D (startConfig B x w)
    e.state = machine.accept ∧ e.head.val = a + m + 2 + zeros ∧
      e.tape = loopTape B x w zeros 0 v ∧
      (∀ t, D ≤ t → machine.run t (startConfig B x w) = e) := by
  obtain ⟨-, -, -, -, hsuffix⟩ := handoff_exact (B := B) x w
  obtain ⟨he1, he2, he3, -⟩ :=
    FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.marker_erase_tag_gate_terminator_anchor_dispatcher_scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained
      x w htag hg h hzeros hfence hroom hv hhigh
  have hE : machine.run (alignmentChainClock C a m zeros (borrow x w zeros) v)
      (startConfig B x w) =
      FixedPairOriginAlignment.machine.seqEmbedRight tailMachine
        (tailMachine.run (eraseChainClock C (a + m) zeros (borrow x w zeros) v)
          (tailStartConfig B x w)) :=
    hsuffix (eraseChainClock C (a + m) zeros (borrow x w zeros) v)
  have hstate : (machine.run (alignmentChainClock C a m zeros (borrow x w zeros) v)
      (startConfig B x w)).state = machine.accept := by
    rw [hE, UniformTM.seqEmbedRight_state, he1]
    rfl
  refine ⟨hstate, ?_, ?_, fun t ht => ?_⟩
  · rw [hE, UniformTM.seqEmbedRight_head, he2]
  · rw [hE, UniformTM.seqEmbedRight_tape]
    exact he3
  · rw [show t = alignmentChainClock C a m zeros (borrow x w zeros) v +
      (t - alignmentChainClock C a m zeros (borrow x w zeros) v) by omega, UniformTM.run_add]
    exact machine.run_accept _ hstate _

/-- **The routed reject on a matching tag with no gamma terminator.**  The alignment phase hands over
at `switchTime a m`, the marker erasure `N + 3` after that and the gate `3 * N + 7` after that, the
composed run is in neither verdict before
`switchTime a m + (N + 3 + (3 * N + 7 + (N - 7)))`, and from that time on it is in the composed reject
— index `176`, not the alignment `qReject` at `25`, nor the marker-erase one at `29`, nor G1's at `44`,
nor G2's at `47` — on the blank boundary cell `N`, over the `contentTape`: the anchor never runs.
**Not** a converse; it characterises no parsed target. -/
theorem malformed_reject_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = none) :
    let c := startConfig B x w
    (∀ t, t < switchTime a m +
          (a + m + 3 + (3 * (a + m) + 7 + FixedContentGammaTerminator.deadline a m)) →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ s, switchTime a m +
            (a + m + 3 + (3 * (a + m) + 7 + FixedContentGammaTerminator.deadline a m)) ≤ s →
        (machine.run s c).state = machine.reject ∧ (machine.run s c).head.val = a + m ∧
          (machine.run s c).tape = FixedPairContentMarkerErase.contentTape B x w) := by
  intro c
  obtain ⟨-, hnoPre, -, -, hsuffix⟩ := handoff_exact (B := B) x w
  obtain ⟨hno, hpost⟩ :=
    FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.malformed_reject_handoff
      (B := B) x w htag hg
  rw [erase_switch_time] at hno hpost
  have hshift : ∀ s, (machine.run (switchTime a m + s) c).state =
      inTail (tailMachine.run s (tailStartConfig B x w)).state := by
    intro s; rw [hsuffix s]; rfl
  refine ⟨fun t ht => ?_, fun s hs => ?_⟩
  · by_cases hle : t ≤ switchTime a m
    · exact hnoPre t hle
    · have hgt : switchTime a m ≤ t := Nat.le_of_lt (Nat.lt_of_not_le hle)
      have hlt : t - switchTime a m <
          a + m + 3 + (3 * (a + m) + 7 + FixedContentGammaTerminator.deadline a m) := by omega
      obtain ⟨ha, hr⟩ := hno (t - switchTime a m) hlt
      have hst := hshift (t - switchTime a m)
      rw [show switchTime a m + (t - switchTime a m) = t by omega] at hst
      refine ⟨fun hcon => ha ?_, fun hcon => hr ?_⟩
      · exact (Function.Injective.eq_iff
          ((FixedPairOriginAlignment.machine.seq_pins
            tailMachine).2.2.2.2.2.2.2.1)).mp (hst.symm.trans hcon)
      · exact (Function.Injective.eq_iff
          ((FixedPairOriginAlignment.machine.seq_pins
            tailMachine).2.2.2.2.2.2.2.1)).mp (hst.symm.trans hcon)
  · obtain ⟨hrj, hhd, htp⟩ := hpost (s - switchTime a m) (by omega)
    have hrun := hsuffix (s - switchTime a m)
    rw [show switchTime a m + (s - switchTime a m) = s by omega] at hrun
    refine ⟨?_, ?_, ?_⟩
    · rw [hrun, UniformTM.seqEmbedRight_state, hrj]; rfl
    · rw [hrun, UniformTM.seqEmbedRight_head]; exact hhd
    · rw [hrun, UniformTM.seqEmbedRight_tape]; exact htp

/-- **The routed reject on a mismatched tag.**  From `switchTime a m + (N + 3 + (3 * N + 7))` on — the
alignment phase's arrival, the marker-erase scan's and the gate's length-only deadline — the composed
run is in the composed reject `176`, on the gate's own `finalConfig` head, its mismatch cell clamped to
`N`, over the `contentTape`; the gamma blocks never run.  Forward direction only, and **not** timed
exactly: this time is the gate's deadline, not its first rejection, so the composed run may already be
in the composed reject strictly earlier, and nothing here says when.  On a nonempty content the gate
first rejects at `3 * N + j` for its mismatch cell `j`, which this slice does not derive from
`tagMatches (Fin.append x w) = false`; `FixedContentTagGate.finalConfig`'s head is the only public
trace of the `badIndex` that defines it.  **Not** a converse either. -/
theorem mismatched_tag_reject_handoff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = false) :
    ∀ s, switchTime a m + (a + m + 3 + (3 * (a + m) + 7)) ≤ s →
      (machine.run s (startConfig B x w)).state = machine.reject ∧
        (machine.run s (startConfig B x w)).head =
          (FixedContentTagGate.finalConfig B x w).head ∧
        (machine.run s (startConfig B x w)).tape =
          FixedPairContentMarkerErase.contentTape B x w := by
  intro s hs
  obtain ⟨-, -, -, -, hsuffix⟩ := handoff_exact (B := B) x w
  have htail :=
    FixedPairContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.mismatched_tag_reject_handoff
      (B := B) x w htag
  rw [erase_switch_time] at htail
  obtain ⟨hrj, hhd, htp⟩ := htail (s - switchTime a m) (by omega)
  have hrun := hsuffix (s - switchTime a m)
  rw [show switchTime a m + (s - switchTime a m) = s by omega] at hrun
  refine ⟨?_, ?_, ?_⟩
  · rw [hrun, UniformTM.seqEmbedRight_state, hrj]; rfl
  · rw [hrun, UniformTM.seqEmbedRight_head]; exact hhd
  · rw [hrun, UniformTM.seqEmbedRight_tape]; exact htp

end
  Pnp3.Complexity.Uniform.V1.FixedPairOriginAlignmentContentMarkerEraseTagGateGammaTerminatorAnchorPayloadDispatcherScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown
