import Complexity.Uniform.V1.FixedGammaTargetFirstPayload

/-!
# Second gamma payload digit, foundation slice (Part A G2p-c1)

This is the **foundation / no-payload-write width slice** of the G2p-c
*second-payload* specialization (label `G2p-c1`; it is unrelated to the generic
payload-round construction, which is a separate line of work).
It fixes the machine, the phase-local input ABI, the exact room arithmetic, the
local execution kernel, and the two decoded widths at which the machine provably
performs no net payload or register write and leaves the tape unchanged end to end
(the anchor *is* blanked in flight and restored, so what is proved is the absence
of a net tape change, not a run that never writes).  The positive-width trace
that actually copies a second digit is deferred; see "Scope" below.

Write `N = a + m`.  The target register grows from scratch cell `N + 1`, most
significant digit first: G2p-a wrote the leading `true` of `n + 1` there and
G2p-b added the first gamma payload digit at `N + 2`.  The payload cells of a
width-`zeros` header are `[9 + zeros, 9 + 2 * zeros)`, so a *second* payload
digit exists exactly when `2 ≤ zeros`.  The machine decides that locally:

* it blanks the tag cell `7` as the single anchor and steps onto cell `8`;
* cell `8` is the terminator (`some true`) exactly when `zeros = 0`, and cell
  `9` is the terminator exactly when `zeros = 1`.  In both cases the machine
  turns around, restores the anchor, and halts in `qDone` at head `7` with the
  incoming tape unchanged.  Inside the private traces the head stays in
  `[7, 9]`, so no cell past `9` is read, but that read bound is *internal*:
  this module exports no footprint theorem, so what a downstream user gets is
  the tape equality, not a head range (see "Scope");
* otherwise `2 ≤ zeros` and it continues right past cell `9`.  That branch is
  deferred to the next slice.

The two sweeps have *different* delimiters.  The rightward sweep is delimited by
the input terminator at `8 + zeros` and, on a positive width, by the layout blank
at `N`; the run maintains neither of those.  Only the leftward `qScanLeft` sweep
is delimited by a cell the run itself maintains, namely the blanked anchor at
cell `7`, which is the unique blank below `N` while the run is in flight.  The
head moves right from `7` to its turning point and then left back to `7`, so it
never meets a boundary clamp — but that is established *internally*, by the
private width-zero and width-one traces (every `.right` step discharges an
explicit fit obligation and no `.left` step starts at `0`).  Those private
traces are also the only place where the head range, and with it the read and
write footprint, is pinned at all: neither the clamp-freedom nor any read bound
is exported as a theorem here; see "Scope".

`exactClock N zeros` is the first terminal time of a *decoded* width `zeros`:
`3` for width zero, `5` for width one, and `2 * N - 7` for `2 ≤ zeros`.  It says
nothing about a malformed gamma, which has no decoded width at all; that run is
clocked separately by `malformedExactClock = 1`, and `1` is its first terminal
time as a theorem: `malformed_exact` gives the `qReject` endpoint from that time
on, and `malformed_strict` excludes both terminals before it.  This slice
*proves* the first two decoded values the same way — `zero_width_exact` /
`width_one_exact` give the endpoint from that time on and `zero_width_strict` /
`width_one_strict` exclude both terminals before it.  The `2 * N - 7` branch is
the design constant consumed by the deferred positive-width trace and is **not**
proved here; `-` is truncated `Nat` subtraction, so the expression degenerates to
`0` for `N ≤ 3`, which the `3 ≤ N` premise below does not exclude.  It is
meaningful only in the intended scope of that deferred branch, where
`2 ≤ zeros` forces `N ≥ 9 + zeros ≥ 11`.  The
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
`UniformTM` running from the raw pair input, and `deadline N = 2 * N` is the cost
of this phase only — it omits every step embedded in `startConfig`.  Nothing here
may be read as a `UniformP` execution, a runtime result, or a clock for the
composed pipeline; clock composition is out of scope.

## Room

Room is exact and is *not* implied by the header.  Width zero needs none.  Width
one needs `a + m + 2 < tapeLength (pairLength a m) B` — the G2p-b premise, which
is what makes the incoming tape known.  A width `2 ≤ zeros` needs
`a + m + 3 < tapeLength (pairLength a m) B`, equivalently `2 ≤ a + B`
(`room_iff`), which fails for example at `a = B = 0` and at `a + B = 1`.  No
theorem covers a width without its room premise; in particular nothing here says
that `qReject` at this deadline implies a malformed gamma, and no converse of
`malformed_exact` is stated or available.

## Scope

`qDone` is an internal endpoint, not language acceptance.  Deferred to later
slices: the positive-width (`2 ≤ zeros`) second-digit trace and its endpoint
tape; the all-times clamp/footprint/budget package, which is deferred for *every*
branch of this slice, the two proved widths included — unlike G2p-a and G2p-b,
this module exports no `no_boundary_clamp`, no `footprint`, and no
`budget_independence` theorem at all, so every head-range statement made in the
prose above (`no cell past 9`, `no cell past 8`, `no boundary clamp`) holds only
inside the private traces and is unavailable downstream as a theorem; the
exported endpoints are tape equalities, which pin the *net* effect of the run
and not the cells it visited; the pnp4 semantic bridge, every parser and
`contentHeader?` claim, the remaining `zeros - 2` digits, the decrement to `n`,
and `ContentVerifierBridge`.  This is a *specialization*: the same rows do not
iterate, because ending a general payload scan needs both a counter and an
advancing source marker, neither of which this control has.  It is
uniform-machine infrastructure, not P-vs-NP mainline progress.
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
`qReg0`, `qReg1`, and `qBackReg` are landed and pinned deliberately — they are
the fixed control the deferred `2 ≤ zeros` trace will run — but no public
execution theorem of this slice reaches them; exercising them is the next
slice's job. -/
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
`malformedExactClock`.  This slice proves the
`zeros = 0` and `zeros = 1` values; `2 * N - 7` is the unproved design constant
for the deferred positive-width trace, where truncated `Nat` subtraction makes it
`0` for `N ≤ 3` and the intended scope is `N ≥ 9 + zeros ≥ 11`. -/
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
bound is internal — this module exports no footprint theorem. -/
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

end Pnp3.Complexity.Uniform.V1.FixedGammaTargetSecondPayload
