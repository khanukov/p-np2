import Complexity.Uniform.V1.FixedGammaTargetFirstPayload

/-!
# Second gamma payload digit (Part A G2p-c1 foundation, G2p-c2 positive width)

One fixed 14-state, 42-row machine for the *second* gamma payload digit, landed
in two slices (the G2p-c *second-payload* specialization; it is unrelated to the
generic payload-round construction, which is a separate line of work).  `G2p-c1`
fixed the machine, the phase-local input ABI, the exact room arithmetic, the
local execution kernel, and the two decoded widths at which the machine performs
no net payload or register write.  `G2p-c2` — this file's positive-width section
— runs the eight remaining states and proves that on `2 ≤ zeros` the second
payload digit really is copied to the target cell `N + 3`.

Write `N = a + m`.  The target register grows from scratch cell `N + 1`, most
significant digit first: G2p-a wrote the leading `true` of `n + 1` there and
G2p-b added the first gamma payload digit at `N + 2`.  The payload cells of a
width-`zeros` header are `[9 + zeros, 9 + 2 * zeros)`, digit `k` at
`9 + zeros + k`, so a *second* payload digit exists exactly when `2 ≤ zeros`.
The machine decides that locally:

* it blanks the tag cell `7` as the single anchor and steps onto cell `8`;
* cell `8` is the terminator (`some true`) exactly when `zeros = 0`, and cell
  `9` is the terminator exactly when `zeros = 1`.  In both cases the machine
  turns around, restores the anchor, and halts in `qDone` at head `7` with the
  incoming tape unchanged.  Inside the private traces the head stays in
  `[7, 9]`, so no cell past `9` is read, but that read bound is *internal*:
  this module exports no footprint theorem and no head range for these two
  widths, so what a downstream user gets there is the tape equality (see
  "Scope");
* otherwise `2 ≤ zeros`: the run walks to the terminator `8 + zeros` and steps
  *over* the first payload cell `9 + zeros` in `qStepOne`.  The **logical
  source address** is `10 + zeros`, which `second_source_cell` identifies as the
  second payload cell of the block, and the value copied is always the *content*
  symbol at that address.  How the run selects it depends on where the blank
  boundary `N` falls, and since `9 + zeros ≤ N` always holds in scope there are
  exactly three shapes.  With `10 + zeros < N` the source is physical: `qRead`
  really reads that cell and its bit picks the carry state.  With
  `10 + zeros = N` the source address *is* the boundary blank: `qRead` is still
  entered and scans that blank, which picks the virtual zero.  With
  `9 + zeros = N` the *first* payload cell is already the boundary blank, so
  `qStepOne` reads it and hands straight to the register with carry `0`, and
  `qRead` is never entered at all.  The head does pass address `10 + zeros` on
  that third shape too, but there that address is `N + 1`, the control is in
  `qReg0`, and the tape holds the register `true` — crossed, deliberately not
  taken as a source.  The two virtual shapes are exactly the `N ≤ 10 + zeros`
  premise of `second_virtual_exact`, and both copy `false`, which is what
  `Option.getD` records for a `none` content symbol.  The carry state carries
  the selected bit across the content to the blank boundary `N`, then the
  matching register state crosses `N + 1` and `N + 2` — neither is ever taken as
  source — and writes the bit at the first blank after them, the target cell
  `N + 3`.  The run then walks back to the blanked anchor at `7`, restores it,
  and halts in `qDone` at head `7`.

The two sweeps have *different* delimiters.  The rightward sweep is delimited in
phases, and the run maintains none of its delimiters: the input terminator at
`8 + zeros` ends the `qSeekTerm` scan at every width; on a positive width the
layout blank at `N` then ends the walk across the content — in the carry state
when the source is physical, in `qRead` or `qStepOne` on the two boundary shapes
— and the first blank after the register, which is the target cell `N + 3`, ends
the register walk, so that last delimiter is consumed by the write rather than
maintained.  Only the leftward `qScanLeft` sweep is delimited by a cell the run
itself maintains, namely the blanked anchor at cell `7`, which is the unique
blank below `N` while the run is in flight.  The head moves right from `7` to
its turning point and then left back to `7`, so it never meets a boundary clamp.
On the positive branch that is a *theorem* (`positive_width_head_range`,
`positive_width_no_boundary_clamp`); for the two smaller widths it is
established only inside the private traces.  Both are head facts and not a
footprint: they bound the cells the head visits, not the cells whose content may
differ from the incoming tape.

`exactClock N zeros` is the first terminal time of a *decoded* width `zeros`:
`3` for width zero, `5` for width one, and `2 * N - 7` for `2 ≤ zeros`.  All
three are proved in both directions — `zero_width_exact` / `width_one_exact` /
`second_payload_exact` give the endpoint from that time on, and
`zero_width_strict` / `width_one_strict` / `second_payload_strict` exclude both
terminals before it.  `exactClock` says nothing about a malformed gamma, which
has no decoded width at all; that run is clocked separately by
`malformedExactClock = 1`, and `1` is its first terminal time as a theorem
(`malformed_exact` plus `malformed_strict`).  `-` is truncated `Nat`
subtraction, so `2 * N - 7` degenerates to `0` for `N ≤ 3`; the positive-width
premises exclude that, since `2 ≤ zeros` forces `N ≥ 9 + zeros ≥ 11`.  The
length-only public deadline is `2 * N`, and `exactClock_le_deadline` needs
`3 ≤ N` (it is sharp: width one costs `5`, so `N = 2` would not fit).  In scope
`N ≥ 9 + zeros ≥ 9`, so the premise is free.  A failed gamma scan inherits the
G2p-b rejection and rejects in one step at head `N` with `contentTape`.

## Phase-local input ABI

`startConfig` is a **phase-local handoff**, not a composed raw-input execution.
It definitionally retags the *actual* endpoint of
`FixedGammaTargetFirstPayload.machine.run (FixedGammaTargetFirstPayload.deadline
(a + m)) (FixedGammaTargetFirstPayload.startConfig B x w)`: only the control
field is replaced, and `handoff_exact` pins head and tape to that endpoint.  The
provider is therefore real rather than synthetic, but it is *not* one fixed
`UniformTM` running from the raw pair input, and neither `deadline N = 2 * N`
nor `exactClock N zeros` accounts for the steps embedded in `startConfig`.
Nothing here may be read as a `UniformP` execution, a runtime result, or a clock
for the composed pipeline; clock composition is out of scope.

## Room

Room is exact and is *not* implied by the header.  Width zero needs none.  Width
one needs `a + m + 2 < tapeLength (pairLength a m) B` — the G2p-b premise, which
is what makes the incoming tape known.  A width `2 ≤ zeros` needs
`a + m + 3 < tapeLength (pairLength a m) B`, equivalently `2 ≤ a + B`
(`room_iff`), which fails for example at `a = B = 0` and at `a + B = 1`; that is
exactly the cell the run writes and the last cell its head reaches.  No theorem
covers a width without its room premise; in particular nothing here says that
`qReject` at this deadline implies a malformed gamma, nothing says that `qDone`
or a written digit at `N + 3` implies `2 ≤ zeros`, and no converse of any
endpoint theorem is stated or available.

## Scope

`qDone` is an internal endpoint, not language acceptance.  Deferred to later
slices: the all-times footprint/budget package — this module exports no
`footprint` and no `budget_independence` theorem for any branch, so the exported
endpoints are tape equalities, which pin the *net* effect of a run and not the
cells it visited, and the head statements it does export (on the positive branch
only) bound the head rather than the difference set; the pnp4 semantic bridge,
every parser and `contentHeader?` claim, the remaining `zeros - 2` digits, the
decrement to `n`, and `ContentVerifierBridge`.  This is a *specialization*: the
same rows do not iterate, because ending a general payload scan needs both a
counter and an advancing source marker, neither of which this control has.  It
is uniform-machine infrastructure, not P-vs-NP mainline progress.
-/

namespace Pnp3.Complexity.Uniform.V1.FixedGammaTargetSecondPayload

open PairEncoding

abbrev stateCount : Nat := 14

def qStart : Fin stateCount := ⟨0, by decide⟩
def qInspectEight : Fin stateCount := ⟨1, by decide⟩
def qInspectNine : Fin stateCount := ⟨2, by decide⟩
def qSeekTerm : Fin stateCount := ⟨3, by decide⟩
def qStepOne : Fin stateCount := ⟨4, by decide⟩
def qRead : Fin stateCount := ⟨5, by decide⟩
def qCarry0 : Fin stateCount := ⟨6, by decide⟩
def qCarry1 : Fin stateCount := ⟨7, by decide⟩
def qReg0 : Fin stateCount := ⟨8, by decide⟩
def qReg1 : Fin stateCount := ⟨9, by decide⟩
def qBackReg : Fin stateCount := ⟨10, by decide⟩
def qScanLeft : Fin stateCount := ⟨11, by decide⟩
def qDone : Fin stateCount := ⟨12, by decide⟩
def qReject : Fin stateCount := ⟨13, by decide⟩

/-- The complete fixed 14-state, 42-row table.  No width, digit index, bit,
target address, proof term, or clock enters the control.  The eight
positive-route states `qSeekTerm`, `qStepOne`, `qRead`, `qCarry0`, `qCarry1`,
`qReg0`, `qReg1`, and `qBackReg` are the control of the `2 ≤ zeros` route; the
carried bit lives in the *pairs* `qCarry0`/`qCarry1` and `qReg0`/`qReg1` rather
than in any data field, so no single run walks all eight — the bit picks one
state of each pair, and a run whose first payload cell is already the boundary
blank skips `qRead` and the carry pair entirely. -/
def raw (q : Fin stateCount) (s : Option Bool) : Fin stateCount × Option Bool × Move :=
  match q.1 with
  | 0 => match s with
    | some false => (qInspectEight, none, .right)
    | s => (qReject, s, .stay)
  | 1 => match s with
    | some false => (qInspectNine, some false, .right)
    | some true => (qScanLeft, some true, .left)
    | none => (qReject, none, .stay)
  | 2 => match s with
    | some false => (qSeekTerm, some false, .right)
    | some true => (qScanLeft, some true, .left)
    | none => (qReject, none, .stay)
  | 3 => match s with
    | some false => (qSeekTerm, some false, .right)
    | some true => (qStepOne, some true, .right)
    | none => (qReject, none, .stay)
  | 4 => match s with
    | some b => (qRead, some b, .right)
    | none => (qReg0, none, .right)
  | 5 => match s with
    | some false => (qCarry0, some false, .right)
    | some true => (qCarry1, some true, .right)
    | none => (qReg0, none, .right)
  | 6 => match s with
    | some b => (qCarry0, some b, .right)
    | none => (qReg0, none, .right)
  | 7 => match s with
    | some b => (qCarry1, some b, .right)
    | none => (qReg1, none, .right)
  | 8 => match s with
    | some b => (qReg0, some b, .right)
    | none => (qBackReg, some false, .left)
  | 9 => match s with
    | some b => (qReg1, some b, .right)
    | none => (qBackReg, some true, .left)
  | 10 => match s with
    | some b => (qBackReg, some b, .left)
    | none => (qScanLeft, none, .left)
  | 11 => match s with
    | some b => (qScanLeft, some b, .left)
    | none => (qDone, some false, .stay)
  | 12 => (qDone, s, .stay)
  | _ => (qReject, s, .stay)

def machine : UniformTM where
  stateCount := stateCount
  start := qStart
  accept := qDone
  reject := qReject
  accept_ne_reject := by decide
  rawStep := raw

/-- Phase-local handoff ABI: only the control of the actual G2p-b configuration
is replaced; head and tape are copied verbatim. -/
def retagFirstPayload {N B : Nat}
    (c : Config FixedGammaTargetFirstPayload.stateCount N B) :
    Config stateCount N B := ⟨qStart, c.head, c.tape⟩

/-- The start configuration of this phase is the retagged *actual* G2p-b endpoint
configuration.  This is a phase-local handoff, not a composed raw-input
`UniformTM` execution. -/
def startConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config stateCount (pairLength a m) B :=
  retagFirstPayload (FixedGammaTargetFirstPayload.machine.run
    (FixedGammaTargetFirstPayload.deadline (a + m))
    (FixedGammaTargetFirstPayload.startConfig B x w))

/-- First terminal time for a *decoded* gamma width `zeros` over `N` content
cells; a malformed gamma has no decoded width and is clocked separately by
`malformedExactClock`.  All three values are proved exact first arrivals.
Truncated `Nat` subtraction makes `2 * N - 7` degenerate to `0` for `N ≤ 3`,
which the positive-width premises exclude: there `N ≥ 9 + zeros ≥ 11`. -/
def exactClock (N zeros : Nat) : Nat := if 2 ≤ zeros then 2 * N - 7 else 2 * zeros + 3

/-- First terminal time of a *malformed* gamma, which has no decoded width and
is therefore outside `exactClock` entirely.  It is length-independent:
`malformed_exact` gives the `qReject` endpoint from this time on, and
`malformed_strict` excludes both terminals before it. -/
def malformedExactClock : Nat := 1

theorem exactClock_pins :
    (∀ N, exactClock N 0 = 3) ∧ (∀ N, exactClock N 1 = 5) ∧
      (∀ N zeros, 2 ≤ zeros → exactClock N zeros = 2 * N - 7) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ h => if_pos h⟩

/-- Public length-only deadline for **this phase only**; it does not account for
the steps embedded in `startConfig`. -/
def deadline (N : Nat) : Nat := 2 * N

/-- The incoming G2p-b endpoint tape (leading register `true` at `N + 1`, first
payload digit `b0` at `N + 2`) with the second payload digit `c` added at the
target cell `N + 3`. -/
def secondPayloadTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) (b0 c : Bool) :
    Fin (tapeLength (pairLength a m) B) → Option Bool := fun i =>
  if i.val = a + m + 3 then some c
  else FixedGammaTargetFirstPayload.firstPayloadTape B x w b0 i

/-- Every row, pinned literally, with the resource counts. -/
theorem table_and_resource_pins :
    machine.step qStart none = (qReject, none, .stay) ∧
    machine.step qStart (some false) = (qInspectEight, none, .right) ∧
    machine.step qStart (some true) = (qReject, some true, .stay) ∧
    machine.step qInspectEight none = (qReject, none, .stay) ∧
    machine.step qInspectEight (some false) = (qInspectNine, some false, .right) ∧
    machine.step qInspectEight (some true) = (qScanLeft, some true, .left) ∧
    machine.step qInspectNine none = (qReject, none, .stay) ∧
    machine.step qInspectNine (some false) = (qSeekTerm, some false, .right) ∧
    machine.step qInspectNine (some true) = (qScanLeft, some true, .left) ∧
    machine.step qSeekTerm none = (qReject, none, .stay) ∧
    machine.step qSeekTerm (some false) = (qSeekTerm, some false, .right) ∧
    machine.step qSeekTerm (some true) = (qStepOne, some true, .right) ∧
    machine.step qStepOne none = (qReg0, none, .right) ∧
    machine.step qStepOne (some false) = (qRead, some false, .right) ∧
    machine.step qStepOne (some true) = (qRead, some true, .right) ∧
    machine.step qRead none = (qReg0, none, .right) ∧
    machine.step qRead (some false) = (qCarry0, some false, .right) ∧
    machine.step qRead (some true) = (qCarry1, some true, .right) ∧
    machine.step qCarry0 none = (qReg0, none, .right) ∧
    machine.step qCarry0 (some false) = (qCarry0, some false, .right) ∧
    machine.step qCarry0 (some true) = (qCarry0, some true, .right) ∧
    machine.step qCarry1 none = (qReg1, none, .right) ∧
    machine.step qCarry1 (some false) = (qCarry1, some false, .right) ∧
    machine.step qCarry1 (some true) = (qCarry1, some true, .right) ∧
    machine.step qReg0 none = (qBackReg, some false, .left) ∧
    machine.step qReg0 (some false) = (qReg0, some false, .right) ∧
    machine.step qReg0 (some true) = (qReg0, some true, .right) ∧
    machine.step qReg1 none = (qBackReg, some true, .left) ∧
    machine.step qReg1 (some false) = (qReg1, some false, .right) ∧
    machine.step qReg1 (some true) = (qReg1, some true, .right) ∧
    machine.step qBackReg none = (qScanLeft, none, .left) ∧
    machine.step qBackReg (some false) = (qBackReg, some false, .left) ∧
    machine.step qBackReg (some true) = (qBackReg, some true, .left) ∧
    machine.step qScanLeft none = (qDone, some false, .stay) ∧
    machine.step qScanLeft (some false) = (qScanLeft, some false, .left) ∧
    machine.step qScanLeft (some true) = (qScanLeft, some true, .left) ∧
    machine.step qDone none = (qDone, none, .stay) ∧
    machine.step qDone (some false) = (qDone, some false, .stay) ∧
    machine.step qDone (some true) = (qDone, some true, .stay) ∧
    machine.step qReject none = (qReject, none, .stay) ∧
    machine.step qReject (some false) = (qReject, some false, .stay) ∧
    machine.step qReject (some true) = (qReject, some true, .stay) ∧
    machine.stateCount = 14 ∧ machine.start = qStart ∧
    machine.accept = qDone ∧ machine.reject = qReject ∧
    qStart.val = 0 ∧ qInspectEight.val = 1 ∧ qInspectNine.val = 2 ∧ qSeekTerm.val = 3 ∧
    qStepOne.val = 4 ∧ qRead.val = 5 ∧ qCarry0.val = 6 ∧ qCarry1.val = 7 ∧
    qReg0.val = 8 ∧ qReg1.val = 9 ∧ qBackReg.val = 10 ∧ qScanLeft.val = 11 ∧
    qDone.val = 12 ∧ qReject.val = 13 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 42 := by
  repeat' apply And.intro
  all_goals rfl

theorem per_step_budget_independent : ∀ q s, machine.step q s = machine.rawStep q s := by
  intro q s
  fin_cases q <;> cases s with
  | none => rfl
  | some b => cases b <;> rfl

theorem endpoints_absorb {N B : Nat} (c : Config stateCount N B) :
    (c.state = qDone → ∀ n, machine.run n c = c) ∧
    (c.state = qReject → ∀ n, machine.run n c = c) :=
  ⟨fun h n => machine.run_accept c h n, fun h n => machine.run_reject c h n⟩

/-- The phase-local handoff, pinned: the start configuration *is* the retagged
G2p-b endpoint, with the same head and the same tape. -/
theorem handoff_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let p := FixedGammaTargetFirstPayload.machine.run
      (FixedGammaTargetFirstPayload.deadline (a + m))
      (FixedGammaTargetFirstPayload.startConfig B x w)
    let c := startConfig B x w
    c = retagFirstPayload p ∧ c.state = machine.start ∧ c.head = p.head ∧
      c.tape = p.tape :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The target cell `a + m + 3` is allocated exactly when `2 ≤ a + B`; it is not
allocated at `a = B = 0`, nor at `a + B = 1`.  Room is never inferred from a
decoded header. -/
theorem room_iff (a m B : Nat) :
    a + m + 3 < tapeLength (pairLength a m) B ↔ 2 ≤ a + B := by
  unfold tapeLength pairLength
  omega

/-- The logical source address of this phase is the **second** payload cell of a
width-`zeros` gamma block.  The payload occupies `[9 + zeros, 9 + 2 * zeros)`,
digit `k` at `9 + zeros + k`, so digit `1` is cell `10 + zeros`.  The statement
below is the forward direction only: *given* `2 ≤ zeros`, that cell lies inside
the block.  No converse is stated here, and neither is the dispatch — the fixed
control reaches the same `2 ≤ zeros` case by testing cells `8` and `9` for the
terminator, which is a fact about the table rather than about this arithmetic.
This is address arithmetic only.  Whether that address is *physically* present
is a separate question — it is when `10 + zeros < a + m` — and so is which state
the control occupies when the head passes it; neither is claimed here. -/
theorem second_source_cell {zeros : Nat} (hz : 2 ≤ zeros) :
    10 + zeros = 9 + zeros + 1 ∧ 9 + zeros < 10 + zeros ∧ 10 + zeros < 9 + 2 * zeros := by
  omega

/-- The endpoint tape: every content cell restored, the boundary blank at `N`,
the register `true` at `N + 1`, the G2p-b digit `b0` at `N + 2`, the second
payload digit `c` at `N + 3`, and blanks afterwards. -/
theorem secondPayloadTape_layout {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (b0 c : Bool) (hroom : a + m + 3 < tapeLength (pairLength a m) B) :
    (∀ j : Fin (a + m), secondPayloadTape B x w b0 c
      ⟨j.val, by unfold tapeLength pairLength; omega⟩ = some (Fin.append x w j)) ∧
    secondPayloadTape B x w b0 c ⟨a + m, by unfold tapeLength pairLength; omega⟩ = none ∧
    secondPayloadTape B x w b0 c ⟨a + m + 1, by unfold tapeLength pairLength; omega⟩ =
      some true ∧
    secondPayloadTape B x w b0 c
      ⟨a + m + 2, by unfold tapeLength pairLength at hroom ⊢; omega⟩ = some b0 ∧
    secondPayloadTape B x w b0 c ⟨a + m + 3, hroom⟩ = some c ∧
    ∀ i : Fin (tapeLength (pairLength a m) B), a + m + 3 < i.val →
      secondPayloadTape B x w b0 c i = none := by
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    FixedGammaTargetFirstPayload.firstPayloadTape_layout (B := B) x w b0 (by omega)
  refine ⟨fun j => ?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩ <;> unfold secondPayloadTape
  · rw [if_neg (show ¬ j.val = a + m + 3 by omega)]
    exact h1 j
  · rw [if_neg (show ¬ a + m = a + m + 3 by omega)]
    exact h2
  · rw [if_neg (show ¬ a + m + 1 = a + m + 3 by omega)]
    exact h3
  · rw [if_neg (show ¬ a + m + 2 = a + m + 3 by omega)]
    exact h4
  · rw [if_pos rfl]
  · rw [if_neg (show ¬ i.val = a + m + 3 by omega)]
    exact h5 i (by omega)

/-- The premise `3 ≤ N` is sharp: width one costs `5` steps, which does not fit
`2 * N` at `N = 2`.  In scope `N ≥ 9 + zeros`, so the premise is free. -/
theorem exactClock_le_deadline {N zeros : Nat} (hN : 3 ≤ N) :
    exactClock N zeros ≤ deadline N := by
  unfold exactClock deadline
  split_ifs <;> omega

/-! ### Address-level execution kernel -/

private def content {a m : Nat} (x : Bitstring a) (w : Bitstring m) : Nat → Option Bool :=
  FixedContentTagGate.physicalSymbol (Fin.append x w)

private def scratch {a m : Nat} (x : Bitstring a) (w : Bitstring m) (k : Nat) :
    Option Bool :=
  if k = a + m + 1 then some true else content x w k

/-- The incoming G2p-b endpoint tape on a positive width, read by address. -/
private def base {a m : Nat} (x : Bitstring a) (w : Bitstring m) (b0 : Bool) (k : Nat) :
    Option Bool :=
  if k = a + m + 2 then some b0 else scratch x w k

/-- Control, numeric head, and every tape cell read through its address. -/
private def At {n B : Nat} (c : Config stateCount n B) (q : Fin stateCount) (k : Nat)
    (T : Nat → Option Bool) : Prop :=
  c.state = q ∧ c.head.val = k ∧ ∀ i, c.tape i = T i.val

private def shift (k : Nat) : Move → Nat
  | .left => k - 1
  | .stay => k
  | .right => k + 1

private theorem step_at {n B : Nat} {c : Config stateCount n B} {q q' : Fin stateCount}
    {k k' : Nat} {T T' : Nat → Option Bool} {r s' : Option Bool} {mv : Move}
    (hc : At c q k T) (hread : T k = r) (hrow : machine.step q r = (q', s', mv))
    (hk : shift k mv = k') (hfit : mv = .right → k + 1 < tapeLength n B)
    (hwrite : T' k = s') (hkeep : ∀ i, i ≠ k → T' i = T i) :
    At (machine.stepConfig c) q' k' T' := by
  obtain ⟨hq, hh, ht⟩ := hc
  have haction : machine.step c.state (c.tape c.head) = (q', s', mv) := by
    rw [hq, ht, hh, hread, hrow]
  refine ⟨?_, ?_, fun i => ?_⟩
  · change (machine.step c.state (c.tape c.head)).1 = q'
    rw [haction]
  · change (moveHead c.head (machine.step c.state (c.tape c.head)).2.2).val = k'
    rw [haction, ← hk]
    cases mv with
    | left =>
        change c.head.val - 1 = k - 1
        rw [hh]
    | stay => exact hh
    | right =>
        have hlt : c.head.val + 1 < tapeLength n B := by
          rw [hh]
          exact hfit rfl
        unfold moveHead
        rw [dif_pos hlt]
        change c.head.val + 1 = k + 1
        rw [hh]
  · change (if i = c.head then (machine.step c.state (c.tape c.head)).2.1
      else c.tape i) = T' i.val
    rw [haction]
    by_cases hi : i.val = k
    · rw [if_pos (Fin.ext (hi.trans hh.symm)), hi, hwrite]
    · rw [if_neg (fun h => hi (by rw [h, hh])), hkeep i.val hi, ht]

private theorem stepAt_right {n B t : Nat} {c : Config stateCount n B}
    {q q' : Fin stateCount} {k k' : Nat} {T T' : Nat → Option Bool} {r s' : Option Bool}
    (hc : At (machine.run t c) q k T) (hread : T k = r)
    (hrow : machine.step q r = (q', s', .right)) (hk : k + 1 = k')
    (hfit : k + 1 < tapeLength n B) (hwrite : T' k = s')
    (hkeep : ∀ i, i ≠ k → T' i = T i) : At (machine.run (t + 1) c) q' k' T' :=
  step_at hc hread hrow hk (fun _ => hfit) hwrite hkeep

private theorem stepAt_left {n B t : Nat} {c : Config stateCount n B}
    {q q' : Fin stateCount} {k k' : Nat} {T T' : Nat → Option Bool} {r s' : Option Bool}
    (hc : At (machine.run t c) q k T) (hread : T k = r)
    (hrow : machine.step q r = (q', s', .left)) (hk : k - 1 = k')
    (hwrite : T' k = s') (hkeep : ∀ i, i ≠ k → T' i = T i) :
    At (machine.run (t + 1) c) q' k' T' :=
  step_at hc hread hrow hk (fun h => nomatch h) hwrite hkeep

private theorem stepAt_stay {n B t : Nat} {c : Config stateCount n B}
    {q q' : Fin stateCount} {k k' : Nat} {T T' : Nat → Option Bool} {r s' : Option Bool}
    (hc : At (machine.run t c) q k T) (hread : T k = r)
    (hrow : machine.step q r = (q', s', .stay)) (hk : k = k')
    (hwrite : T' k = s') (hkeep : ∀ i, i ≠ k → T' i = T i) :
    At (machine.run (t + 1) c) q' k' T' :=
  step_at hc hread hrow hk (fun h => nomatch h) hwrite hkeep

private theorem row_scanLeft (b : Bool) :
    machine.step qScanLeft (some b) = (qScanLeft, some b, .left) := by
  cases b <;> rfl

/-! ### Budget-free schedules of the two no-payload-write widths -/

private def zeroState (s : Nat) : Fin stateCount :=
  if s = 0 then qStart else if s = 1 then qInspectEight
  else if s = 2 then qScanLeft else qDone

private def zeroHead (s : Nat) : Nat := if s = 1 then 8 else 7

private def zeroTape {a m : Nat} (x : Bitstring a) (w : Bitstring m) (s k : Nat) :
    Option Bool :=
  if k = 7 ∧ 1 ≤ s ∧ s ≤ 2 then none else scratch x w k

private def oneState (s : Nat) : Fin stateCount :=
  if s = 0 then qStart else if s = 1 then qInspectEight else if s = 2 then qInspectNine
  else if s ≤ 4 then qScanLeft else qDone

private def oneHead (s : Nat) : Nat := if s ≤ 2 then 7 + s else if s = 3 then 8 else 7

private def oneTape {a m : Nat} (x : Bitstring a) (w : Bitstring m) (b0 : Bool) (s k : Nat) :
    Option Bool :=
  if k = 7 ∧ 1 ≤ s ∧ s ≤ 4 then none else base x w b0 k

/-! ### Content and tape lemmas -/

private theorem content_ge {a m : Nat} (x : Bitstring a) (w : Bitstring m) {k : Nat}
    (hk : a + m ≤ k) : content x w k = none := by
  unfold content FixedContentTagGate.physicalSymbol
  rw [dif_neg (show ¬ k < a + m by omega)]

private theorem zeroTape_content {a m : Nat} {x : Bitstring a} {w : Bitstring m} {s k : Nat}
    (h : (k ≠ 7 ∨ s = 0 ∨ 2 < s) ∧ k ≠ a + m + 1) :
    zeroTape x w s k = content x w k := by
  unfold zeroTape scratch
  split_ifs <;> first | rfl | omega

private theorem oneTape_content {a m : Nat} {x : Bitstring a} {w : Bitstring m}
    {b0 : Bool} {s k : Nat}
    (h : (k ≠ 7 ∨ s = 0 ∨ 4 < s) ∧ k ≠ a + m + 1 ∧ k ≠ a + m + 2) :
    oneTape x w b0 s k = content x w k := by
  unfold oneTape base scratch
  split_ifs <;> first | rfl | omega

/-- Tag cells `6`, `7` and the gamma block, as used by every successful run. -/
private theorem gamma_cells {a m zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    9 + zeros ≤ a + m ∧ content x w 7 = some false ∧
      content x w (8 + zeros) = some true ∧
      ∀ i, 7 ≤ i → i < 8 + zeros → content x w i = some false := by
  obtain ⟨hlt, hterm, hzero⟩ :=
    (FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 zeros hg
  have hall := ((FixedContentTagGate.tag_contract (Fin.append x w)).2.2.2.2.2.2.2.2.1).1 htag
  have h7 := hall ⟨7, by decide⟩
  refine ⟨by omega, h7, hterm, fun i h1 h2 => ?_⟩
  rcases Nat.lt_or_ge i 8 with h | h
  · rw [show i = 7 by omega]
    exact h7
  · have hi := hzero (i - 8) (by omega)
    rwa [show 8 + (i - 8) = i by omega] at hi

/-! ### Traces -/

private theorem start_at_pos {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 0 < zeros) (hroom : a + m + 2 < tapeLength (pairLength a m) B) :
    At (startConfig B x w) qStart 7 (base x w ((content x w (9 + zeros)).getD false)) := by
  obtain ⟨-, hh, ht⟩ :=
    FixedGammaTargetFirstPayload.first_payload_at_deadline (B := B) x w htag hg hz hroom
  refine ⟨rfl, hh, fun i => ?_⟩
  rw [show (startConfig B x w).tape = _ from ht]
  unfold base scratch content FixedGammaTargetFirstPayload.firstPayloadTape
    FixedGammaTerminatorScratchBootstrap.scratchTape
    FixedPairContentMarkerErase.contentTape FixedContentTagGate.physicalSymbol
  split_ifs <;> rfl

private theorem start_at_zero {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 0) :
    At (startConfig B x w) qStart 7 (scratch x w) := by
  obtain ⟨-, hh, ht⟩ :=
    FixedGammaTargetFirstPayload.zero_width_at_deadline (B := B) x w htag hg
  refine ⟨rfl, hh, fun i => ?_⟩
  rw [show (startConfig B x w).tape = _ from ht]
  unfold scratch content FixedGammaTerminatorScratchBootstrap.scratchTape
    FixedPairContentMarkerErase.contentTape FixedContentTagGate.physicalSymbol
  split_ifs <;> rfl

private theorem malformed_at {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none) (s : Nat) :
    At (machine.run s (startConfig B x w)) (if s = 0 then qStart else qReject) (a + m)
      (content x w) := by
  induction s with
  | zero =>
      obtain ⟨-, hh, ht⟩ :=
        FixedGammaTargetFirstPayload.malformed_at_deadline (B := B) x w htag hg
      exact ⟨rfl, hh, fun i => congrFun ht i⟩
  | succ s ih =>
      rw [if_neg (show ¬ s + 1 = 0 by omega)]
      by_cases hs : s = 0
      · rw [if_pos hs] at ih
        exact stepAt_stay ih (content_ge x w le_rfl) rfl rfl (content_ge x w le_rfl)
          (fun _ _ => rfl)
      · rw [if_neg hs] at ih
        exact stepAt_stay ih rfl (machine.step_reject _) rfl rfl (fun _ _ => rfl)

set_option linter.unusedSimpArgs false in
private theorem zero_at {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 0) (s : Nat) :
    At (machine.run s (startConfig B x w)) (zeroState s) (zeroHead s) (zeroTape x w s) := by
  obtain ⟨hN, h7, h8, -⟩ := gamma_cells x w htag hg
  induction s with
  | zero =>
      obtain ⟨hq, hh, ht⟩ := start_at_zero (B := B) x w htag hg
      exact ⟨hq, hh, fun i => (ht i).trans
        (by unfold zeroTape; split_ifs <;> first | rfl | omega)⟩
  | succ s ih =>
      rcases (show s = 0 ∨ s = 1 ∨ s = 2 ∨ 3 ≤ s by omega) with rfl | rfl | rfl | h <;>
        simp (disch := omega) only [zeroState, zeroHead, if_pos, if_neg, if_true] at ih ⊢
      · -- Blank the anchor at cell `7`.
        refine stepAt_right ih ((zeroTape_content (by omega)).trans h7) rfl rfl
          (by unfold tapeLength pairLength; omega) ?_ (fun i hi => ?_) <;>
          (unfold zeroTape; split_ifs <;> first | rfl | omega)
      · -- Cell `8` is the terminator: turn around.
        exact stepAt_left ih ((zeroTape_content (by omega)).trans h8) rfl rfl
          ((zeroTape_content (by omega)).trans h8)
          (fun i hi => by unfold zeroTape; split_ifs <;> first | rfl | omega)
      · -- Restore the anchor and halt.
        refine stepAt_stay ih (r := none)
          (by unfold zeroTape; split_ifs <;> first | rfl | omega) rfl rfl ?_ (fun i hi => ?_)
        · rw [show zeroTape x w 3 7 = content x w 7 from zeroTape_content (by omega)]
          exact h7
        · unfold zeroTape; split_ifs <;> first | rfl | omega
      · rw [show zeroTape x w (s + 1) = zeroTape x w s by
          funext k; unfold zeroTape; split_ifs <;> first | rfl | omega]
        exact stepAt_stay ih rfl (machine.step_accept _) rfl rfl (fun _ _ => rfl)

private theorem one_at {a m B : Nat} (x : Bitstring a) (w : Bitstring m) {b0 : Bool}
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 1)
    (hroom : a + m + 2 < tapeLength (pairLength a m) B)
    (hb0 : (content x w (9 + 1)).getD false = b0) (s : Nat) :
    At (machine.run s (startConfig B x w)) (oneState s) (oneHead s) (oneTape x w b0 s) := by
  obtain ⟨hN, h7, h9, hfalse⟩ := gamma_cells x w htag hg
  have h8 : content x w 8 = some false := hfalse 8 (by omega) (by omega)
  induction s with
  | zero =>
      obtain ⟨hq, hh, ht⟩ := start_at_pos (B := B) x w htag hg (by omega) hroom
      rw [hb0] at ht
      exact ⟨hq, hh, fun i => (ht i).trans
        (by unfold oneTape; split_ifs <;> first | rfl | omega)⟩
  | succ s ih =>
      rcases (show s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ 5 ≤ s by omega)
        with rfl | rfl | rfl | rfl | rfl | h <;>
        simp (disch := omega) only [oneState, oneHead, if_pos, if_neg, if_true] at ih ⊢
      · -- Blank the anchor at cell `7`.
        refine stepAt_right ih ((oneTape_content (by omega)).trans h7) rfl rfl
          (by unfold tapeLength pairLength; omega) ?_ (fun i hi => ?_) <;>
          (unfold oneTape; split_ifs <;> first | rfl | omega)
      · -- Cell `8` is a gamma zero.
        have hr : oneTape x w b0 1 8 = some false := (oneTape_content (by omega)).trans h8
        exact stepAt_right ih hr rfl rfl (by unfold tapeLength pairLength; omega) hr
          (fun i hi => by unfold oneTape; split_ifs <;> first | rfl | omega)
      · -- Cell `9` is the terminator: turn around.
        have hr : oneTape x w b0 2 9 = some true := (oneTape_content (by omega)).trans h9
        exact stepAt_left ih hr rfl rfl hr
          (fun i hi => by unfold oneTape; split_ifs <;> first | rfl | omega)
      · have hr : oneTape x w b0 3 8 = some false := (oneTape_content (by omega)).trans h8
        exact stepAt_left ih hr (row_scanLeft false) rfl hr
          (fun i hi => by unfold oneTape; split_ifs <;> first | rfl | omega)
      · -- Restore the anchor and halt.
        refine stepAt_stay ih (r := none)
          (by unfold oneTape; split_ifs <;> first | rfl | omega) rfl rfl ?_ (fun i hi => ?_)
        · rw [show oneTape x w b0 5 7 = content x w 7 from oneTape_content (by omega)]
          exact h7
        · unfold oneTape; split_ifs <;> first | rfl | omega
      · rw [show oneTape x w b0 (s + 1) = oneTape x w b0 s by
          funext k; unfold oneTape; split_ifs <;> first | rfl | omega]
        exact stepAt_stay ih rfl (machine.step_accept _) rfl rfl (fun _ _ => rfl)

/-! ### Positive width: rows, schedule, and tape

The rows below are the eight positive-route states of the fixed table.  The
carried bit never enters the control as data: it is carried by the *pair* of
states `qCarry0`/`qCarry1` and delivered by the pair `qReg0`/`qReg1`, so the
schedule indexes those pairs by the bit. -/

private def carryState (c : Bool) : Fin stateCount := if c then qCarry1 else qCarry0
private def regState (c : Bool) : Fin stateCount := if c then qReg1 else qReg0

private theorem carryState_ne (c : Bool) :
    carryState c ≠ qDone ∧ carryState c ≠ qReject := by
  cases c <;> exact ⟨by decide, by decide⟩

private theorem regState_ne (c : Bool) :
    regState c ≠ qDone ∧ regState c ≠ qReject := by
  cases c <;> exact ⟨by decide, by decide⟩

/-- The first payload cell is stepped over, never read as a source. -/
private theorem row_stepOne (b : Bool) :
    machine.step qStepOne (some b) = (qRead, some b, .right) := by
  cases b <;> rfl

/-- A blank first payload cell means the whole payload is virtual: hand straight
to the register with carry `0`. -/
private theorem row_stepOneBlank :
    machine.step qStepOne none = (regState false, none, .right) := rfl

/-- The source row: the second payload cell selects the carry state. -/
private theorem row_read (b : Bool) :
    machine.step qRead (some b) = (carryState b, some b, .right) := by
  cases b <;> rfl

/-- A blank source cell is the virtual zero. -/
private theorem row_readBlank :
    machine.step qRead none = (regState false, none, .right) := rfl

private theorem row_carry (c b : Bool) :
    machine.step (carryState c) (some b) = (carryState c, some b, .right) := by
  cases c <;> cases b <;> rfl

private theorem row_carryEnd (c : Bool) :
    machine.step (carryState c) none = (regState c, none, .right) := by
  cases c <;> rfl

private theorem row_reg (c b : Bool) :
    machine.step (regState c) (some b) = (regState c, some b, .right) := by
  cases c <;> cases b <;> rfl

/-- The only payload write of the run: the carried bit at the first blank cell
after the register, which is the target cell `N + 3`. -/
private theorem row_regWrite (c : Bool) :
    machine.step (regState c) none = (qBackReg, some c, .left) := by
  cases c <;> rfl

private theorem row_backReg (b : Bool) :
    machine.step qBackReg (some b) = (qBackReg, some b, .left) := by
  cases b <;> rfl

/-- Control schedule of a positive-width run carrying the second payload digit
`c`.  `qRead` is reached at time `zeros + 3` exactly when the first payload cell
`9 + zeros` is physical; otherwise `qStepOne` hands straight to the register. -/
private def posState (N zeros : Nat) (c : Bool) (s : Nat) : Fin stateCount :=
  if s = 0 then qStart
  else if s = 1 then qInspectEight
  else if s = 2 then qInspectNine
  else if s ≤ zeros + 1 then qSeekTerm
  else if s = zeros + 2 then qStepOne
  else if s ≤ N - 7 then (if s = zeros + 3 then qRead else carryState c)
  else if s ≤ N - 4 then regState c
  else if s ≤ N - 1 then qBackReg
  else if s ≤ 2 * N - 8 then qScanLeft
  else qDone

/-- The head walks right from the anchor `7` to the target cell `N + 3` without
pausing, then straight back to the anchor. -/
private def posHead (N s : Nat) : Nat :=
  if s ≤ N - 4 then 7 + s else if s ≤ 2 * N - 8 then 2 * N - 1 - s else 7

/-- Tape of a positive-width run: the blanked anchor at `7` over its window, and
the second payload digit at `N + 3` from the write on.  Every other cell keeps
its incoming G2p-b value. -/
private def posTape {a m : Nat} (x : Bitstring a) (w : Bitstring m) (b0 c : Bool) (s k : Nat) :
    Option Bool :=
  if k = 7 ∧ 1 ≤ s ∧ s ≤ 2 * (a + m) - 8 then none
  else if k = a + m + 3 ∧ a + m - 3 ≤ s then some c
  else base x w b0 k

private theorem content_lt {a m : Nat} (x : Bitstring a) (w : Bitstring m) {k : Nat}
    (hk : k < a + m) : ∃ b, content x w k = some b :=
  ⟨Fin.append x w ⟨k, hk⟩, by
    unfold content FixedContentTagGate.physicalSymbol
    rw [dif_pos hk]⟩

/-- The bit carried by a positive-width run: the physical second payload bit, or
the virtual zero when the source cell `10 + zeros` is not a content cell. -/
private theorem carried_cases {a m zeros : Nat} (x : Bitstring a) (w : Bitstring m) :
    content x w (10 + zeros) = some ((content x w (10 + zeros)).getD false) ∨
      (a + m ≤ 10 + zeros ∧ (content x w (10 + zeros)).getD false = false) := by
  unfold content FixedContentTagGate.physicalSymbol
  split
  · exact Or.inl rfl
  · exact Or.inr ⟨by omega, rfl⟩

private theorem posTape_succ {a m : Nat} {x : Bitstring a} {w : Bitstring m} {b0 c : Bool}
    {s : Nat} (h : s ≠ 0 ∧ s ≠ a + m - 4 ∧ s ≠ 2 * (a + m) - 8) :
    posTape x w b0 c (s + 1) = posTape x w b0 c s := by
  funext k
  unfold posTape
  split_ifs <;> first | rfl | omega

private theorem posTape_content {a m : Nat} {x : Bitstring a} {w : Bitstring m} {b0 c : Bool}
    {s k : Nat}
    (h : (k ≠ 7 ∨ s = 0 ∨ 2 * (a + m) - 8 < s) ∧ (k ≠ a + m + 3 ∨ s + 3 < a + m) ∧
      k ≠ a + m + 1 ∧ k ≠ a + m + 2) :
    posTape x w b0 c s k = content x w k := by
  unfold posTape base scratch
  split_ifs <;> first | rfl | omega

/-- The leading scratch `true` at `N + 1` is stepped over, never used as source. -/
private theorem posTape_scratch {a m : Nat} {x : Bitstring a} {w : Bitstring m} {b0 c : Bool}
    {s : Nat} (hN : 9 ≤ a + m) : posTape x w b0 c s (a + m + 1) = some true := by
  unfold posTape base scratch
  split_ifs <;> first | rfl | omega

/-- The G2p-b digit at `N + 2` is stepped over, never used as source. -/
private theorem posTape_digit {a m : Nat} {x : Bitstring a} {w : Bitstring m} {b0 c : Bool}
    {s : Nat} (hN : 9 ≤ a + m) : posTape x w b0 c s (a + m + 2) = some b0 := by
  unfold posTape base scratch
  split_ifs <;> first | rfl | omega

/-- The address-level incoming tape and the G2p-b endpoint tape are the same
function, read through the address and through the index. -/
private theorem base_eq_firstPayloadTape {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (b0 : Bool) (i : Fin (tapeLength (pairLength a m) B)) :
    base x w b0 i.val = FixedGammaTargetFirstPayload.firstPayloadTape B x w b0 i := by
  unfold base scratch content FixedGammaTargetFirstPayload.firstPayloadTape
    FixedGammaTerminatorScratchBootstrap.scratchTape
    FixedPairContentMarkerErase.contentTape FixedContentTagGate.physicalSymbol
  split_ifs <;> rfl

/-! ### Positive-width trace -/

/-- Content facts behind a positive-width run whose source cell `10 + zeros`
carries `c`. -/
private def SecondCells {a m : Nat} (x : Bitstring a) (w : Bitstring m) (zeros : Nat)
    (c : Bool) : Prop :=
  9 + zeros ≤ a + m ∧ content x w 7 = some false ∧ content x w (8 + zeros) = some true ∧
    (∀ i, 7 ≤ i → i < 8 + zeros → content x w i = some false) ∧
    (content x w (10 + zeros) = some c ∨ (a + m ≤ 10 + zeros ∧ c = false))

private def PosAt {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) (zeros : Nat)
    (b0 c : Bool) (s : Nat) : Prop :=
  At (machine.run s (startConfig B x w)) (posState (a + m) zeros c s) (posHead (a + m) s)
    (posTape x w b0 c s)

/-- A virtual source cell forces the carried bit to be `false`. -/
private theorem carried_virtual {a m zeros : Nat} {x : Bitstring a} {w : Bitstring m}
    {c : Bool} (hsrc : content x w (10 + zeros) = some c ∨ (a + m ≤ 10 + zeros ∧ c = false))
    (hv : a + m ≤ 10 + zeros) : c = false := by
  rcases hsrc with hsrc | ⟨-, hcf⟩
  · rw [content_ge x w hv] at hsrc
    cases hsrc
  · exact hcf

/-- Blank the anchor at cell `7`, walk past the gamma zeros at `8` and `9` — the
two cells that decide the width — and seek the terminator at `8 + zeros`. -/
private theorem pos_step_seek {a m B zeros s : Nat} {x : Bitstring a} {w : Bitstring m}
    {b0 c : Bool} (hcells : SecondCells x w zeros c) (hz : 2 ≤ zeros)
    (hroom : a + m + 3 < tapeLength (pairLength a m) B) (hs : s ≤ zeros + 1)
    (ih : PosAt B x w zeros b0 c s) : PosAt B x w zeros b0 c (s + 1) := by
  obtain ⟨hN, h7, hterm, hfalse, -⟩ := hcells
  unfold PosAt at ih ⊢
  rcases (show s = 0 ∨ s = 1 ∨ s = 2 ∨ (3 ≤ s ∧ s ≤ zeros) ∨ s = zeros + 1 by omega)
    with h | h | h | h | h
  · -- Blank the anchor at cell `7`.
    subst h
    simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
    refine stepAt_right ih ((posTape_content (by omega)).trans h7) rfl (by omega) (by omega) ?_
      (fun i hi => ?_) <;> (unfold posTape; split_ifs <;> first | rfl | omega)
  · -- Cell `8` is a gamma zero, so the width is not zero.
    subst h
    simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
    rw [posTape_succ (by omega)]
    have hr : posTape x w b0 c 1 8 = some false :=
      (posTape_content (by omega)).trans (hfalse 8 (by omega) (by omega))
    exact stepAt_right ih hr rfl (by omega) (by omega) hr (fun _ _ => rfl)
  · -- Cell `9` is a gamma zero, so `2 ≤ zeros` and a second payload digit exists.
    subst h
    simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
    rw [posTape_succ (by omega)]
    have hr : posTape x w b0 c 2 9 = some false :=
      (posTape_content (by omega)).trans (hfalse 9 (by omega) (by omega))
    exact stepAt_right ih hr rfl (by omega) (by omega) hr (fun _ _ => rfl)
  · -- Walk right over the remaining gamma zeros.
    obtain ⟨h1, h2⟩ := h
    simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
    rw [posTape_succ (by omega)]
    have hr : posTape x w b0 c s (7 + s) = some false :=
      (posTape_content (by omega)).trans (hfalse _ (by omega) (by omega))
    exact stepAt_right ih hr rfl (by omega) (by omega) hr (fun _ _ => rfl)
  · -- The terminator at `8 + zeros`: step onto the first payload cell.
    subst h
    simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
    rw [posTape_succ (by omega)]
    have hr : posTape x w b0 c (zeros + 1) (7 + (zeros + 1)) = some true := by
      rw [posTape_content (by omega), show 7 + (zeros + 1) = 8 + zeros by omega]
      exact hterm
    exact stepAt_right ih hr rfl (by omega) (by omega) hr (fun _ _ => rfl)

/-- Step over the first payload cell `9 + zeros`, select the second payload
digit at the logical source address `10 + zeros`, and carry it right to the
blank boundary `N`.  Only a *physical* source is selected by reading it: a blank
at `10 + zeros` is still scanned in `qRead`, a blank at `9 + zeros` is scanned in
`qStepOne` and `qRead` is skipped entirely, and either way the register is
entered with carry `0`. -/
private theorem pos_step_carry {a m B zeros s : Nat} {x : Bitstring a} {w : Bitstring m}
    {b0 c : Bool} (hcells : SecondCells x w zeros c) (hz : 2 ≤ zeros)
    (hroom : a + m + 3 < tapeLength (pairLength a m) B)
    (hs : zeros + 2 ≤ s ∧ s ≤ a + m - 7) (ih : PosAt B x w zeros b0 c s) :
    PosAt B x w zeros b0 c (s + 1) := by
  obtain ⟨hN, -, -, -, hsrc⟩ := hcells
  obtain ⟨hs1, hs2⟩ := hs
  unfold PosAt at ih ⊢
  rcases (show s = zeros + 2 ∨ s = zeros + 3 ∨ (zeros + 4 ≤ s ∧ s ≤ a + m - 8) ∨
      (zeros + 4 ≤ s ∧ s = a + m - 7) by omega) with h | h | h | h
  · -- The first payload cell.
    subst h
    rcases Nat.lt_or_ge (9 + zeros) (a + m) with hp | hp
    · -- Physical: step over it towards the source cell.
      obtain ⟨b, hb⟩ := content_lt x w hp
      simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
      rw [posTape_succ (by omega)]
      have hr : posTape x w b0 c (zeros + 2) (7 + (zeros + 2)) = some b := by
        rw [posTape_content (by omega), show 7 + (zeros + 2) = 9 + zeros by omega]
        exact hb
      exact stepAt_right ih hr (row_stepOne b) (by omega) (by omega) hr (fun _ _ => rfl)
    · -- Blank: the whole payload is virtual, so the carried bit is `false`.
      obtain rfl : c = false := carried_virtual hsrc (by omega)
      simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
      rw [posTape_succ (by omega)]
      have hr : posTape x w b0 false (zeros + 2) (7 + (zeros + 2)) = none :=
        (posTape_content (by omega)).trans (content_ge x w (by omega))
      exact stepAt_right ih hr row_stepOneBlank (by omega) (by omega) hr (fun _ _ => rfl)
  · -- The source cell `10 + zeros`.
    subst h
    rcases Nat.lt_or_ge (10 + zeros) (a + m) with hp | hp
    · -- Physical: its bit selects the carry state.
      have hb : content x w (10 + zeros) = some c := by
        rcases hsrc with hsrc | ⟨hv, -⟩
        · exact hsrc
        · omega
      simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
      rw [posTape_succ (by omega)]
      have hr : posTape x w b0 c (zeros + 3) (7 + (zeros + 3)) = some c := by
        rw [posTape_content (by omega), show 7 + (zeros + 3) = 10 + zeros by omega]
        exact hb
      exact stepAt_right ih hr (row_read c) (by omega) (by omega) hr (fun _ _ => rfl)
    · -- Blank: the virtual zero.
      obtain rfl : c = false := carried_virtual hsrc (by omega)
      simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
      rw [posTape_succ (by omega)]
      have hr : posTape x w b0 false (zeros + 3) (7 + (zeros + 3)) = none :=
        (posTape_content (by omega)).trans (content_ge x w (by omega))
      exact stepAt_right ih hr row_readBlank (by omega) (by omega) hr (fun _ _ => rfl)
  · -- Carry the bit over the content cells.
    obtain ⟨h1, h2⟩ := h
    obtain ⟨b, hb⟩ := content_lt x w (k := 7 + s) (by omega)
    simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
    rw [posTape_succ (by omega)]
    have hr : posTape x w b0 c s (7 + s) = some b := (posTape_content (by omega)).trans hb
    exact stepAt_right ih hr (row_carry c b) (by omega) (by omega) hr (fun _ _ => rfl)
  · -- The blank boundary `N`: enter the register.
    obtain ⟨h1, h2⟩ := h
    simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
    rw [posTape_succ (by omega)]
    have hr : posTape x w b0 c s (7 + s) = none :=
      (posTape_content (by omega)).trans (content_ge x w (by omega))
    exact stepAt_right ih hr (row_carryEnd c) (by omega) (by omega) hr (fun _ _ => rfl)

/-- Step over the register cells `N + 1` and `N + 2` and write the carried bit at
the first blank cell after them, the target cell `N + 3`. -/
private theorem pos_step_write {a m B zeros s : Nat} {x : Bitstring a} {w : Bitstring m}
    {b0 c : Bool} (hcells : SecondCells x w zeros c) (hz : 2 ≤ zeros)
    (hroom : a + m + 3 < tapeLength (pairLength a m) B)
    (hs : a + m - 6 ≤ s ∧ s ≤ a + m - 4) (ih : PosAt B x w zeros b0 c s) :
    PosAt B x w zeros b0 c (s + 1) := by
  obtain ⟨hN, -, -, -, -⟩ := hcells
  obtain ⟨hs1, hs2⟩ := hs
  unfold PosAt at ih ⊢
  rcases (show s = a + m - 6 ∨ s = a + m - 5 ∨ s = a + m - 4 by omega) with h | h | h
  · -- Step over the leading scratch `true`.
    simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
    rw [posTape_succ (by omega)]
    have hr : posTape x w b0 c s (7 + s) = some true := by
      rw [show 7 + s = a + m + 1 by omega]
      exact posTape_scratch (by omega)
    exact stepAt_right ih hr (row_reg c true) (by omega) (by omega) hr (fun _ _ => rfl)
  · -- Step over the G2p-b digit.
    simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
    rw [posTape_succ (by omega)]
    have hr : posTape x w b0 c s (7 + s) = some b0 := by
      rw [show 7 + s = a + m + 2 by omega]
      exact posTape_digit (by omega)
    exact stepAt_right ih hr (row_reg c b0) (by omega) (by omega) hr (fun _ _ => rfl)
  · -- Write the carried bit at the target cell `N + 3`.
    simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
    have hr : posTape x w b0 c s (7 + s) = none := by
      rw [posTape_content (by omega), show 7 + s = a + m + 3 by omega]
      exact content_ge x w (by omega)
    refine stepAt_left ih hr (row_regWrite c) (by omega) ?_ (fun i hi => ?_) <;>
      (unfold posTape; split_ifs <;> first | rfl | omega)

/-- Walk back over the register, cross the boundary, sweep left to the blanked
anchor at cell `7`, restore it, and halt.  This is the only phase with no room
premise: every move of it is a `.left` or a `.stay`, so it discharges no fit
obligation. -/
private theorem pos_step_return {a m B zeros s : Nat} {x : Bitstring a} {w : Bitstring m}
    {b0 c : Bool} (hcells : SecondCells x w zeros c) (hz : 2 ≤ zeros) (hs : a + m - 3 ≤ s)
    (ih : PosAt B x w zeros b0 c s) : PosAt B x w zeros b0 c (s + 1) := by
  obtain ⟨hN, h7, -, -, -⟩ := hcells
  unfold PosAt at ih ⊢
  rcases (show s = a + m - 3 ∨ s = a + m - 2 ∨ s = a + m - 1 ∨
      (a + m ≤ s ∧ s ≤ 2 * (a + m) - 9) ∨ s = 2 * (a + m) - 8 ∨
      2 * (a + m) - 8 < s by omega) with h | h | h | h | h | h
  · -- Back over the G2p-b digit.
    simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
    rw [posTape_succ (by omega)]
    have hr : posTape x w b0 c s (2 * (a + m) - 1 - s) = some b0 := by
      rw [show 2 * (a + m) - 1 - s = a + m + 2 by omega]
      exact posTape_digit (by omega)
    exact stepAt_left ih hr (row_backReg b0) (by omega) hr (fun _ _ => rfl)
  · -- Back over the leading scratch `true`.
    simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
    rw [posTape_succ (by omega)]
    have hr : posTape x w b0 c s (2 * (a + m) - 1 - s) = some true := by
      rw [show 2 * (a + m) - 1 - s = a + m + 1 by omega]
      exact posTape_scratch (by omega)
    exact stepAt_left ih hr (row_backReg true) (by omega) hr (fun _ _ => rfl)
  · -- Cross the blank boundary `N` into the leftward sweep.
    simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
    rw [posTape_succ (by omega)]
    have hr : posTape x w b0 c s (2 * (a + m) - 1 - s) = none := by
      rw [posTape_content (by omega), show 2 * (a + m) - 1 - s = a + m by omega]
      exact content_ge x w (by omega)
    exact stepAt_left ih hr rfl (by omega) hr (fun _ _ => rfl)
  · -- Sweep left over the content cells.
    obtain ⟨h1, h2⟩ := h
    obtain ⟨b, hb⟩ := content_lt x w (k := 2 * (a + m) - 1 - s) (by omega)
    simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
    rw [posTape_succ (by omega)]
    have hr : posTape x w b0 c s (2 * (a + m) - 1 - s) = some b :=
      (posTape_content (by omega)).trans hb
    exact stepAt_left ih hr (row_scanLeft b) (by omega) hr (fun _ _ => rfl)
  · -- The blanked anchor is the unique blank below `N`: restore it and halt.
    simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
    have hr : posTape x w b0 c s (2 * (a + m) - 1 - s) = none := by
      unfold posTape
      split_ifs <;> first | rfl | omega
    refine stepAt_stay ih hr rfl (by omega) ?_ (fun i hi => ?_)
    · rw [show 2 * (a + m) - 1 - s = 7 by omega, posTape_content (by omega)]
      exact h7
    · unfold posTape
      split_ifs <;> first | rfl | omega
  · -- `qDone` is absorbing.
    simp (disch := omega) only [posState, posHead, if_pos, if_neg] at ih ⊢
    rw [posTape_succ (by omega)]
    exact stepAt_stay ih rfl (machine.step_accept _) rfl rfl (fun _ _ => rfl)

private theorem pos_at {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m) {b0 c : Bool}
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 2 ≤ zeros) (hb0 : (content x w (9 + zeros)).getD false = b0)
    (hc : content x w (10 + zeros) = some c ∨ (a + m ≤ 10 + zeros ∧ c = false))
    (hroom : a + m + 3 < tapeLength (pairLength a m) B) (s : Nat) :
    PosAt B x w zeros b0 c s := by
  obtain ⟨hN, h7, hterm, hfalse⟩ := gamma_cells x w htag hg
  have hcells : SecondCells x w zeros c := ⟨hN, h7, hterm, hfalse, hc⟩
  induction s with
  | zero =>
      obtain ⟨hq, hh, ht⟩ := start_at_pos (B := B) x w htag hg (by omega) (by omega)
      rw [hb0] at ht
      refine ⟨hq.trans ?_, hh.trans ?_, fun i => (ht i).trans ?_⟩
      · unfold posState
        split_ifs <;> first | rfl | omega
      · unfold posHead
        split_ifs <;> omega
      · unfold posTape
        split_ifs <;> first | rfl | omega
  | succ s ih =>
      rcases (show s ≤ zeros + 1 ∨ (zeros + 2 ≤ s ∧ s ≤ a + m - 7) ∨
          (a + m - 6 ≤ s ∧ s ≤ a + m - 4) ∨ a + m - 3 ≤ s by omega) with h | h | h | h
      · exact pos_step_seek hcells hz hroom h ih
      · exact pos_step_carry hcells hz hroom h ih
      · exact pos_step_write hcells hz hroom h ih
      · exact pos_step_return hcells hz h ih

/-! ### Public execution theorems -/

/-- A failed gamma scan inherits the G2p-b rejection: after one step the machine
is in `qReject` at head `a + m` with `contentTape`.  No room premise is needed.
`malformed_strict` supplies the matching first-arrival direction, so `1` is the
*first* terminal time here, not merely a time by which the run has rejected.
There is deliberately **no converse**: this does not say that `qReject` at this
deadline implies a malformed gamma. -/
theorem malformed_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none)
    (s : Nat) (hs : 1 ≤ s) :
    let d := machine.run s (startConfig B x w)
    d.state = qReject ∧ d.head.val = a + m ∧
      d.tape = FixedPairContentMarkerErase.contentTape B x w := by
  obtain ⟨hq, hh, ht⟩ := malformed_at (B := B) x w htag hg s
  rw [if_neg (show ¬ s = 0 by omega)] at hq
  exact ⟨hq, hh, funext ht⟩

theorem malformed_at_deadline {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none) :
    let d := machine.run (deadline (a + m)) (startConfig B x w)
    d.state = qReject ∧ d.head.val = a + m ∧
      d.tape = FixedPairContentMarkerErase.contentTape B x w :=
  malformed_exact x w htag hg _ (by
    have := (FixedContentTagGate.tag_contract (Fin.append x w)).2.2.2.2.2.2.2.2.2 htag
    unfold deadline
    omega)

/-- `malformedExactClock = 1` is a *first* arrival: before step one — that is, at
the handed-over start configuration itself — the control is in neither terminal
state, so together with `malformed_exact` the first terminal time of a malformed
gamma really is `1`.  The premise admits `s = 0` only, and what excludes the two
terminals there is the handoff's own control tag (`machine.start = qStart`, see
`handoff_exact`); the malformed premises are carried so that the statement is
scoped to the same branch as `malformed_exact`. -/
theorem malformed_strict {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none)
    (s : Nat) (hs : s < malformedExactClock) :
    let d := machine.run s (startConfig B x w)
    d.state ≠ qDone ∧ d.state ≠ qReject := by
  obtain rfl : s = 0 := by
    rw [show malformedExactClock = 1 from rfl] at hs
    omega
  obtain ⟨hq, -, -⟩ := malformed_at (B := B) x w htag hg 0
  show (machine.run 0 (startConfig B x w)).state ≠ qDone ∧
    (machine.run 0 (startConfig B x w)).state ≠ qReject
  rw [hq]
  exact ⟨by decide, by decide⟩

/-- Width zero halts at head `7` after exactly three steps on the very bootstrap
scratch tape it was handed, with no room premise: the anchor at cell `7` is
blanked in flight and restored, so the tape equality below *is* the statement
that the run leaves no net payload or register write behind.  The private trace
also keeps the head inside `[7, 8]`, so no cell past `8` is read, but that read
bound is internal — this module exports no footprint theorem, and the head-range
theorems it does export cover the positive-width branch only. -/
theorem zero_width_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 0)
    (s : Nat) (hs : 3 ≤ s) :
    let d := machine.run s (startConfig B x w)
    d.state = qDone ∧ d.head.val = 7 ∧
      d.tape = FixedGammaTerminatorScratchBootstrap.scratchTape B x w := by
  obtain ⟨hq, hh, ht⟩ := zero_at (B := B) x w htag hg s
  refine ⟨hq.trans ?_, hh.trans ?_, funext fun i => (ht i).trans ?_⟩
  · unfold zeroState
    split_ifs <;> first | rfl | omega
  · unfold zeroHead
    split_ifs <;> omega
  · unfold zeroTape scratch content FixedGammaTerminatorScratchBootstrap.scratchTape
      FixedPairContentMarkerErase.contentTape FixedContentTagGate.physicalSymbol
    split_ifs <;> first | rfl | omega

theorem zero_width_at_deadline {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 0) :
    let d := machine.run (deadline (a + m)) (startConfig B x w)
    d.state = qDone ∧ d.head.val = 7 ∧
      d.tape = FixedGammaTerminatorScratchBootstrap.scratchTape B x w := by
  have hN := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 0 hg).1
  exact zero_width_exact x w htag hg _ (by unfold deadline; omega)

/-- `exactClock N 0 = 3` is a *first* arrival: before step three the control is
in neither terminal state. -/
theorem zero_width_strict {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 0)
    (s : Nat) (hs : s < exactClock (a + m) 0) :
    let d := machine.run s (startConfig B x w)
    d.state ≠ qDone ∧ d.state ≠ qReject := by
  rw [show exactClock (a + m) 0 = 3 from rfl] at hs
  obtain ⟨hq, -, -⟩ := zero_at (B := B) x w htag hg s
  show (machine.run s (startConfig B x w)).state ≠ qDone ∧
    (machine.run s (startConfig B x w)).state ≠ qReject
  rw [hq]
  rcases (show s = 0 ∨ s = 1 ∨ s = 2 by omega) with rfl | rfl | rfl <;>
    exact ⟨by decide, by decide⟩

/-- Width one has no second payload digit: after exactly five steps the machine
halts at head `7` on the very G2p-b tape it was handed — the anchor at cell `7`
is blanked in flight and restored, so there is no net tape change and hence no
net payload or register write — and every *allocated* cell after `a + m + 2` is
blank,
including the target cell `a + m + 3` whenever that cell is allocated.  Only the
G2p-b room premise `a + m + 2 < tapeLength (pairLength a m) B` is used; it does
not itself allocate `a + m + 3` (that needs `2 ≤ a + B`, see `room_iff`), so the
suffix claim is vacuous exactly when the target cell does not exist. -/
theorem width_one_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 1)
    (hroom : a + m + 2 < tapeLength (pairLength a m) B) (s : Nat) (hs : 5 ≤ s) :
    let d := machine.run s (startConfig B x w)
    d.state = qDone ∧ d.head.val = 7 ∧
      d.tape = FixedGammaTargetFirstPayload.firstPayloadTape B x w
        ((FixedContentTagGate.physicalSymbol (Fin.append x w) 10).getD false) ∧
      ∀ i : Fin (tapeLength (pairLength a m) B), a + m + 2 < i.val → d.tape i = none := by
  obtain ⟨hq, hh, ht⟩ := one_at (B := B) x w htag hg hroom rfl s
  have htape : (machine.run s (startConfig B x w)).tape =
      FixedGammaTargetFirstPayload.firstPayloadTape B x w
        ((FixedContentTagGate.physicalSymbol (Fin.append x w) 10).getD false) := by
    refine funext fun i => (ht i).trans ?_
    unfold oneTape base scratch content FixedGammaTargetFirstPayload.firstPayloadTape
      FixedGammaTerminatorScratchBootstrap.scratchTape
      FixedPairContentMarkerErase.contentTape FixedContentTagGate.physicalSymbol
    split_ifs <;> first | rfl | omega
  obtain ⟨-, -, -, -, hblank⟩ :=
    FixedGammaTargetFirstPayload.firstPayloadTape_layout (B := B) x w
      ((FixedContentTagGate.physicalSymbol (Fin.append x w) 10).getD false) hroom
  refine ⟨hq.trans ?_, hh.trans ?_, htape, fun i hi => ?_⟩
  · unfold oneState
    split_ifs <;> first | rfl | omega
  · unfold oneHead
    split_ifs <;> omega
  · rw [htape]
    exact hblank i hi

theorem width_one_at_deadline {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 1)
    (hroom : a + m + 2 < tapeLength (pairLength a m) B) :
    let d := machine.run (deadline (a + m)) (startConfig B x w)
    d.state = qDone ∧ d.head.val = 7 ∧
      d.tape = FixedGammaTargetFirstPayload.firstPayloadTape B x w
        ((FixedContentTagGate.physicalSymbol (Fin.append x w) 10).getD false) ∧
      ∀ i : Fin (tapeLength (pairLength a m) B), a + m + 2 < i.val → d.tape i = none := by
  have hN := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 1 hg).1
  exact width_one_exact x w htag hg hroom _ (by unfold deadline; omega)

/-- `exactClock N 1 = 5` is a *first* arrival: before step five the control is in
neither terminal state. -/
theorem width_one_strict {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 1)
    (hroom : a + m + 2 < tapeLength (pairLength a m) B)
    (s : Nat) (hs : s < exactClock (a + m) 1) :
    let d := machine.run s (startConfig B x w)
    d.state ≠ qDone ∧ d.state ≠ qReject := by
  rw [show exactClock (a + m) 1 = 5 from rfl] at hs
  obtain ⟨hq, -, -⟩ := one_at (B := B) x w htag hg hroom rfl s
  show (machine.run s (startConfig B x w)).state ≠ qDone ∧
    (machine.run s (startConfig B x w)).state ≠ qReject
  rw [hq]
  rcases (show s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 by omega)
    with rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by decide, by decide⟩

/-! ### Positive width: the second payload digit is copied -/

/-- **The execution theorem of this slice.**  On a matching tag, a decoded width
`2 ≤ zeros`, and an allocated target cell `a + m + 3`, the run halts in `qDone`
at head `7` from step `exactClock (a + m) zeros = 2 * (a + m) - 7` on, with the
second payload digit written at the target cell `a + m + 3` and every other cell
exactly as the G2p-b endpoint left it.

The copied value is the *content* symbol at the logical source address
`10 + zeros`, the second payload cell of the block (`second_source_cell`), which
is what `Option.getD` records.  This conclusion is extensional — it fixes the
endpoint tape, not the schedule — and the schedule has three shapes.  With
`10 + zeros < a + m` the source is physical and the fixed control really does
read it: the run steps over the first payload cell `9 + zeros` in `qStepOne` and
reads `10 + zeros` in `qRead` (`second_physical_exact`).  With
`10 + zeros = a + m` the source address *is* the blank boundary; `qRead` is
entered and scans that blank, taking the virtual zero.  With `9 + zeros = a + m`
the *first* payload cell is already the blank boundary, so `qStepOne` reads it
and hands straight to the register: `qRead` is never entered on that shape, and
although the head does pass address `10 + zeros`, that address is then
`a + m + 1`, the control is in `qReg0`, and the tape holds the register `true`
there rather than any source.  Both virtual shapes copy `false`
(`second_virtual_exact`, premise `a + m ≤ 10 + zeros`).  Neither the register
`true` at `a + m + 1` nor the G2p-b digit at `a + m + 2` is ever taken as the
source: both are stepped over in the register state that the selection already
fixed.

`second_payload_strict` supplies the matching first-arrival direction, so
`2 * (a + m) - 7` is the *first* terminal time and not merely a time by which the
run has halted.  `qDone` is an internal endpoint, not language acceptance, and
there is deliberately no converse: nothing here says that `qDone` at this time
implies `2 ≤ zeros`. -/
theorem second_payload_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 2 ≤ zeros) (hroom : a + m + 3 < tapeLength (pairLength a m) B)
    (s : Nat) (hs : exactClock (a + m) zeros ≤ s) :
    let d := machine.run s (startConfig B x w)
    d.state = qDone ∧ d.head.val = 7 ∧
      d.tape = secondPayloadTape B x w
        ((FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros)).getD false)
        ((FixedContentTagGate.physicalSymbol (Fin.append x w) (10 + zeros)).getD false) := by
  obtain ⟨hN, -⟩ := gamma_cells x w htag hg
  rw [show exactClock (a + m) zeros = 2 * (a + m) - 7 from if_pos hz] at hs
  obtain ⟨hq, hh, ht⟩ := pos_at x w htag hg hz rfl (carried_cases x w) hroom s
  refine ⟨hq.trans ?_, hh.trans ?_, funext fun i => (ht i).trans ?_⟩
  · unfold posState
    split_ifs <;> first | rfl | omega
  · unfold posHead
    split_ifs <;> omega
  · unfold posTape secondPayloadTape
    rw [if_neg (show ¬ (i.val = 7 ∧ 1 ≤ s ∧ s ≤ 2 * (a + m) - 8) by omega)]
    by_cases hi : i.val = a + m + 3
    · rw [if_pos (show i.val = a + m + 3 ∧ a + m - 3 ≤ s from ⟨hi, by omega⟩), if_pos hi]
      rfl
    · rw [if_neg (show ¬ (i.val = a + m + 3 ∧ a + m - 3 ≤ s) by omega), if_neg hi]
      exact base_eq_firstPayloadTape x w _ i

/-- `exactClock N zeros = 2 * N - 7` is a *first* arrival on a decoded width
`2 ≤ zeros`: before that step the control is in neither terminal state. -/
theorem second_payload_strict {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 2 ≤ zeros) (hroom : a + m + 3 < tapeLength (pairLength a m) B)
    (s : Nat) (hs : s < exactClock (a + m) zeros) :
    let d := machine.run s (startConfig B x w)
    d.state ≠ qDone ∧ d.state ≠ qReject := by
  obtain ⟨hN, -⟩ := gamma_cells x w htag hg
  rw [show exactClock (a + m) zeros = 2 * (a + m) - 7 from if_pos hz] at hs
  obtain ⟨hq, -, -⟩ := pos_at x w htag hg hz rfl (carried_cases x w) hroom s
  show (machine.run s (startConfig B x w)).state ≠ qDone ∧
    (machine.run s (startConfig B x w)).state ≠ qReject
  rw [hq]
  unfold posState
  split_ifs <;>
    first
      | exact ⟨by decide, by decide⟩
      | exact carryState_ne _
      | exact regState_ne _
      | omega

/-- The same endpoint at the length-only deadline `deadline N = 2 * N` of this
phase, which is not a clock for the composed pipeline: it omits every step
embedded in `startConfig`. -/
theorem second_payload_at_deadline {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 2 ≤ zeros) (hroom : a + m + 3 < tapeLength (pairLength a m) B) :
    let d := machine.run (deadline (a + m)) (startConfig B x w)
    d.state = qDone ∧ d.head.val = 7 ∧
      d.tape = secondPayloadTape B x w
        ((FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros)).getD false)
        ((FixedContentTagGate.physicalSymbol (Fin.append x w) (10 + zeros)).getD false) := by
  obtain ⟨hN, -⟩ := gamma_cells x w htag hg
  exact second_payload_exact x w htag hg hz hroom _ (exactClock_le_deadline (by omega))

/-- A *physical* second payload digit `b` — the logical source address
`10 + zeros` is a content cell — is copied verbatim to the target cell
`a + m + 3`.  The premise forces `10 + zeros < a + m`, so this is the physical
one of the three shapes: the control enters `qRead` at the source address, as it
also does when that address is the boundary blank, but here what it reads there
is the content symbol `b`, and that is the value copied. -/
theorem second_physical_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (b : Bool) (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 2 ≤ zeros)
    (hread : FixedContentTagGate.physicalSymbol (Fin.append x w) (10 + zeros) = some b)
    (hroom : a + m + 3 < tapeLength (pairLength a m) B)
    (s : Nat) (hs : exactClock (a + m) zeros ≤ s) :
    let d := machine.run s (startConfig B x w)
    d.state = qDone ∧ d.head.val = 7 ∧
      d.tape = secondPayloadTape B x w
        ((FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros)).getD false) b := by
  have h := second_payload_exact x w htag hg hz hroom s hs
  rw [hread] at h
  exact h

/-- When the logical source address `10 + zeros` is not a content cell the
*virtual* zero is copied: the target cell `a + m + 3` gets `false`.  The premise
admits two operationally different shapes.  If `10 + zeros = a + m`, that address
is the blank boundary itself and `qRead` scans it.  If `9 + zeros = a + m`, the
*first* payload cell is the boundary, `qStepOne` reads *that* blank and bypasses
`qRead` altogether; the address `10 + zeros` is then `a + m + 1`, the register
cell, which the run crosses in `qReg0` — so the `false` here comes from the
bypass, not from reading the register `true` that actually sits at that address.
Neither the register `true` at `a + m + 1` nor the G2p-b digit at `a + m + 2` is
taken as the source. -/
theorem second_virtual_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 2 ≤ zeros) (hvirtual : a + m ≤ 10 + zeros)
    (hroom : a + m + 3 < tapeLength (pairLength a m) B)
    (s : Nat) (hs : exactClock (a + m) zeros ≤ s) :
    let d := machine.run s (startConfig B x w)
    d.state = qDone ∧ d.head.val = 7 ∧
      d.tape = secondPayloadTape B x w
        ((FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros)).getD false)
        false := by
  have h := second_payload_exact x w htag hg hz hroom s hs
  rw [show FixedContentTagGate.physicalSymbol (Fin.append x w) (10 + zeros) = none from
    content_ge x w hvirtual] at h
  exact h

/-- Head range of the positive-width run at *every* time: it never leaves
`[7, a + m + 3]`.  This is the local non-clamp fact this branch needs, and it is
not the deferred all-times footprint package: it bounds the head, not the cells
whose content may differ from the incoming tape. -/
theorem positive_width_head_range {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 2 ≤ zeros) (hroom : a + m + 3 < tapeLength (pairLength a m) B) (s : Nat) :
    let d := machine.run s (startConfig B x w)
    7 ≤ d.head.val ∧ d.head.val ≤ a + m + 3 := by
  obtain ⟨hN, -⟩ := gamma_cells x w htag hg
  obtain ⟨-, hh, -⟩ := pos_at x w htag hg hz rfl (carried_cases x w) hroom s
  show 7 ≤ (machine.run s (startConfig B x w)).head.val ∧
    (machine.run s (startConfig B x w)).head.val ≤ a + m + 3
  rw [hh]
  unfold posHead
  split_ifs <;> omega

/-- No transition of the positive-width run clamps at either end of the tape:
every `.right` move has room and no `.left` move starts at cell `0`.  The head
*enters* the last allocated cell of the run, `a + m + 3`, on the preceding
`.right` move out of `a + m + 2`; the transition taken *at* `a + m + 3` is the
write, and it moves `.left`, so no `.right` move is ever attempted from there. -/
theorem positive_width_no_boundary_clamp {a m B zeros : Nat} (x : Bitstring a)
    (w : Bitstring m) (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 2 ≤ zeros) (hroom : a + m + 3 < tapeLength (pairLength a m) B) (s : Nat) :
    let d := machine.run s (startConfig B x w)
    let move := (machine.step d.state (d.tape d.head)).2.2
    (move = .right → d.head.val + 1 < tapeLength (pairLength a m) B) ∧
    (move = .left → 0 < d.head.val) := by
  obtain ⟨hN, -⟩ := gamma_cells x w htag hg
  obtain ⟨hq, hh, ht⟩ := pos_at x w htag hg hz rfl (carried_cases x w) hroom s
  have hb : 7 ≤ posHead (a + m) s ∧ posHead (a + m) s ≤ a + m + 3 ∧
      (posHead (a + m) s = a + m + 3 → s = a + m - 4) := by
    unfold posHead
    split_ifs <;> omega
  dsimp only
  rw [hq, ht, hh]
  refine ⟨fun hright => ?_, fun _ => by omega⟩
  by_cases hk : posHead (a + m) s = a + m + 3
  · have hs := hb.2.2 hk
    have hstate : posState (a + m) zeros
        ((content x w (10 + zeros)).getD false) s =
        regState ((content x w (10 + zeros)).getD false) := by
      simp (disch := omega) only [posState, if_pos, if_neg]
    have hcell : posTape x w ((content x w (9 + zeros)).getD false)
        ((content x w (10 + zeros)).getD false) s (a + m + 3) = none := by
      rw [posTape_content (by omega)]
      exact content_ge x w (by omega)
    rw [hk, hstate, hcell, row_regWrite] at hright
    cases hright
  · omega

end Pnp3.Complexity.Uniform.V1.FixedGammaTargetSecondPayload
