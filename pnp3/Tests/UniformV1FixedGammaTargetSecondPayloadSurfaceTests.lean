import Complexity.Uniform.V1.FixedGammaTargetSecondPayload

/-!
Surface pins for the Part A second gamma payload digit: the G2p-c1 foundation
(the fixed 14-state/42-row table, the phase-local handoff ABI, exact room, the
phase-local clocks, and the two decoded widths at which the machine provably
makes no net payload or register write and leaves the tape unchanged end to end
— the anchor *is* blanked in flight and restored, so what is pinned there is the
absence of a net tape change) and the G2p-c2 positive-width (`2 ≤ zeros`)
execution, which copies the *content* symbol at the logical source address
`10 + zeros` to the target cell `a + m + 3` and halts at the exact first
terminal time `2 * (a + m) - 7`.  That endpoint is extensional, and the schedule
behind it has *three* shapes.  With `10 + zeros < a + m` the source is physical:
`qRead` reads it and carries its bit.  With `10 + zeros = a + m` the source
address is the blank boundary: `qRead` is still entered, scans that blank, and
hands to `qReg0`.  With `9 + zeros = a + m` the *first* payload cell is already
that blank, so `qStepOne` scans it and `qRead` is bypassed entirely.  The two
positive-width probes below pin the two *extreme* shapes — the physical one and
the `qRead`-bypassing one; the middle, boundary-source shape is pinned by no
probe here.

All three decoded clocks are pinned in both directions — `check_*_exact` for the
endpoint from the clock on and `check_*_strict` for the exclusion of both
terminals before it — and so is the malformed branch.  The eight positive-route
states (`qSeekTerm`, `qStepOne`, `qRead`, `qCarry0`, `qCarry1`, `qReg0`,
`qReg1`, `qBackReg`) are the control that the positive-width wrappers below
exercise.

What is *not* here: the all-times footprint/budget package stays deferred for
every branch, so no wrapper below pins a read/write footprint or a
`budget_independence` claim, and none is available to pin.  The two head
wrappers that do exist (`check_positive_width_head_range`,
`check_positive_width_no_boundary_clamp`) cover the positive branch only and
bound the head, not the set of cells whose content may differ from the incoming
tape; for widths zero and one the module's head-range prose still lives inside
its private traces.  What the endpoint wrappers restate are tape equalities,
which pin the *net* effect of a run.  Every pnp4/parser claim, the remaining
digits, and the decrement to `n` are out of scope, and no wrapper states a
converse of any endpoint.
-/

namespace Pnp3.Tests.UniformV1FixedGammaTargetSecondPayloadSurfaceTests

open Complexity.Uniform.V1
open Complexity.Uniform.V1.PairEncoding
open Complexity.Uniform.V1.FixedGammaTargetSecondPayload

/-! ### Name pins for every public declaration of the slice -/

def check_stateCount : Nat := stateCount
def check_states : List (Fin stateCount) :=
  [qStart, qInspectEight, qInspectNine, qSeekTerm, qStepOne, qRead, qCarry0, qCarry1,
    qReg0, qReg1, qBackReg, qScanLeft, qDone, qReject]
def check_raw :
    Fin stateCount → Option Bool → Fin stateCount × Option Bool × Move := raw
def check_machine : UniformTM := machine
def check_retagFirstPayload {N B : Nat} :
    Config FixedGammaTargetFirstPayload.stateCount N B → Config stateCount N B :=
  retagFirstPayload
def check_startConfig {a m : Nat} :
    (B : Nat) → Bitstring a → Bitstring m → Config stateCount (pairLength a m) B :=
  startConfig
def check_exactClock (N zeros : Nat) : Nat := exactClock N zeros
def check_malformedExactClock : Nat := malformedExactClock
def check_deadline (N : Nat) : Nat := deadline N
def check_secondPayloadTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m)
    (b0 c : Bool) : Fin (tapeLength (pairLength a m) B) → Option Bool :=
  secondPayloadTape B x w b0 c

-- Name pins only.  Each of these four theorems also has a full-signature
-- `check_*` wrapper below; the `#check` lines alone would not catch a signature
-- change.
#check @table_and_resource_pins
#check @per_step_budget_independent
#check @endpoints_absorb
#check @exactClock_le_deadline

/-! ### Exact wrappers for the promised signatures -/

theorem check_deadline_eq (N : Nat) : deadline N = 2 * N := rfl

/-- The malformed branch has no decoded width, so it is clocked outside
`exactClock`; its value is pinned here. -/
theorem check_malformedExactClock_eq : malformedExactClock = 1 := rfl

theorem check_exactClock_pins :
    (∀ N, exactClock N 0 = 3) ∧ (∀ N, exactClock N 1 = 5) ∧
      (∀ N zeros, 2 ≤ zeros → exactClock N zeros = 2 * N - 7) :=
  exactClock_pins

/-- The `3 ≤ N` premise is part of the promised signature; it is sharp at width
one, where the phase costs `5` steps. -/
theorem check_exactClock_le_deadline {N zeros : Nat} (hN : 3 ≤ N) :
    exactClock N zeros ≤ deadline N :=
  exactClock_le_deadline hN

theorem check_table_and_resource_pins :
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
    Fintype.card (Fin machine.stateCount × Option Bool) = 42 :=
  table_and_resource_pins

theorem check_per_step_budget_independent :
    ∀ q s, machine.step q s = machine.rawStep q s :=
  per_step_budget_independent

theorem check_endpoints_absorb {N B : Nat} (c : Config stateCount N B) :
    (c.state = qDone → ∀ n, machine.run n c = c) ∧
    (c.state = qReject → ∀ n, machine.run n c = c) :=
  endpoints_absorb c

/-- The handoff is phase-local: the start configuration *is* the retagged actual
G2p-b endpoint configuration, not a composed raw-input execution. -/
theorem check_handoff_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let p := FixedGammaTargetFirstPayload.machine.run
      (FixedGammaTargetFirstPayload.deadline (a + m))
      (FixedGammaTargetFirstPayload.startConfig B x w)
    let c := startConfig B x w
    c = retagFirstPayload p ∧ c.state = machine.start ∧ c.head = p.head ∧
      c.tape = p.tape :=
  handoff_exact x w

theorem check_room_iff (a m B : Nat) :
    a + m + 3 < tapeLength (pairLength a m) B ↔ 2 ≤ a + B :=
  room_iff a m B

theorem check_malformed_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none)
    (s : Nat) (hs : 1 ≤ s) :
    let d := machine.run s (startConfig B x w)
    d.state = qReject ∧ d.head.val = a + m ∧
      d.tape = FixedPairContentMarkerErase.contentTape B x w :=
  malformed_exact x w htag hg s hs

theorem check_malformed_at_deadline {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none) :
    let d := machine.run (deadline (a + m)) (startConfig B x w)
    d.state = qReject ∧ d.head.val = a + m ∧
      d.tape = FixedPairContentMarkerErase.contentTape B x w :=
  malformed_at_deadline x w htag hg

/-- The first-arrival direction of the malformed clock: before
`malformedExactClock` — a premise that admits `s = 0` only — neither terminal
state is reached, so `1` is the *first* terminal time and not merely a time by
which the run has rejected.  What excludes the terminals at `s = 0` is the
handoff's own control tag, `machine.start = qStart`; the malformed premises are
carried so that the wrapper is scoped to the same branch as
`check_malformed_exact`. -/
theorem check_malformed_strict {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none)
    (s : Nat) (hs : s < malformedExactClock) :
    let d := machine.run s (startConfig B x w)
    d.state ≠ qDone ∧ d.state ≠ qReject :=
  malformed_strict x w htag hg s hs

theorem check_zero_width_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 0)
    (s : Nat) (hs : 3 ≤ s) :
    let d := machine.run s (startConfig B x w)
    d.state = qDone ∧ d.head.val = 7 ∧
      d.tape = FixedGammaTerminatorScratchBootstrap.scratchTape B x w :=
  zero_width_exact x w htag hg s hs

theorem check_zero_width_at_deadline {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 0) :
    let d := machine.run (deadline (a + m)) (startConfig B x w)
    d.state = qDone ∧ d.head.val = 7 ∧
      d.tape = FixedGammaTerminatorScratchBootstrap.scratchTape B x w :=
  zero_width_at_deadline x w htag hg

theorem check_zero_width_strict {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 0)
    (s : Nat) (hs : s < exactClock (a + m) 0) :
    let d := machine.run s (startConfig B x w)
    d.state ≠ qDone ∧ d.state ≠ qReject :=
  zero_width_strict x w htag hg s hs

theorem check_width_one_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 1)
    (hroom : a + m + 2 < tapeLength (pairLength a m) B) (s : Nat) (hs : 5 ≤ s) :
    let d := machine.run s (startConfig B x w)
    d.state = qDone ∧ d.head.val = 7 ∧
      d.tape = FixedGammaTargetFirstPayload.firstPayloadTape B x w
        ((FixedContentTagGate.physicalSymbol (Fin.append x w) 10).getD false) ∧
      ∀ i : Fin (tapeLength (pairLength a m) B), a + m + 2 < i.val → d.tape i = none :=
  width_one_exact x w htag hg hroom s hs

theorem check_width_one_at_deadline {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 1)
    (hroom : a + m + 2 < tapeLength (pairLength a m) B) :
    let d := machine.run (deadline (a + m)) (startConfig B x w)
    d.state = qDone ∧ d.head.val = 7 ∧
      d.tape = FixedGammaTargetFirstPayload.firstPayloadTape B x w
        ((FixedContentTagGate.physicalSymbol (Fin.append x w) 10).getD false) ∧
      ∀ i : Fin (tapeLength (pairLength a m) B), a + m + 2 < i.val → d.tape i = none :=
  width_one_at_deadline x w htag hg hroom

theorem check_width_one_strict {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 1)
    (hroom : a + m + 2 < tapeLength (pairLength a m) B)
    (s : Nat) (hs : s < exactClock (a + m) 1) :
    let d := machine.run s (startConfig B x w)
    d.state ≠ qDone ∧ d.state ≠ qReject :=
  width_one_strict x w htag hg hroom s hs

/-! ### Positive width (`2 ≤ zeros`): the second payload digit is copied

Every wrapper below carries the full premise set of the theorem it restates:
matching tag, a *decoded* width `2 ≤ zeros`, and the exact room
`a + m + 3 < tapeLength (pairLength a m) B` that the run needs — equivalently
`2 ≤ a + B` by `check_room_iff`, so the premises are satisfiable and the
theorems are not vacuous: `check_two_premises` and `check_two_tight_premises`
below instantiate these premise sets at concrete inputs, while the literal
probes independently execute the machine by kernel computation and invoke no
endpoint theorem of this slice.  The copied value is the *content* symbol at the
logical source address `10 + zeros`, which `Option.getD` records as `false` once
that address is at or past the blank boundary `a + m`.  These wrappers restate
tape endpoints, not schedules: `check_second_physical_exact` and
`check_second_virtual_exact` differ only in the premise that selects the copied
value, and neither asserts any intermediate control state.  The schedule itself
has three shapes — `qRead` reads a physical source at `10 + zeros < a + m`;
`qRead` is entered but scans the boundary blank at `10 + zeros = a + m`;
`qStepOne` scans that blank and bypasses `qRead` at `9 + zeros = a + m` — and
the probes below pin the two extremes of the three (`check_two_probe`,
`check_two_tight_probe`).  `qDone` is an internal endpoint, not language
acceptance, and no wrapper states a converse. -/

theorem check_second_source_cell {zeros : Nat} (hz : 2 ≤ zeros) :
    10 + zeros = 9 + zeros + 1 ∧ 9 + zeros < 10 + zeros ∧ 10 + zeros < 9 + 2 * zeros :=
  second_source_cell hz

theorem check_secondPayloadTape_layout {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
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
      secondPayloadTape B x w b0 c i = none :=
  secondPayloadTape_layout x w b0 c hroom

/-- The execution theorem of the slice, at its full signature: first terminal
time `exactClock (a + m) zeros = 2 * (a + m) - 7`, terminal state `qDone`, head
`7`, and the whole endpoint tape with the second payload digit at `a + m + 3`. -/
theorem check_second_payload_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 2 ≤ zeros) (hroom : a + m + 3 < tapeLength (pairLength a m) B)
    (s : Nat) (hs : exactClock (a + m) zeros ≤ s) :
    let d := machine.run s (startConfig B x w)
    d.state = qDone ∧ d.head.val = 7 ∧
      d.tape = secondPayloadTape B x w
        ((FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros)).getD false)
        ((FixedContentTagGate.physicalSymbol (Fin.append x w) (10 + zeros)).getD false) :=
  second_payload_exact x w htag hg hz hroom s hs

/-- The first-arrival direction: before `2 * (a + m) - 7` the control is in
neither terminal state, so the clock above is the *first* terminal time. -/
theorem check_second_payload_strict {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 2 ≤ zeros) (hroom : a + m + 3 < tapeLength (pairLength a m) B)
    (s : Nat) (hs : s < exactClock (a + m) zeros) :
    let d := machine.run s (startConfig B x w)
    d.state ≠ qDone ∧ d.state ≠ qReject :=
  second_payload_strict x w htag hg hz hroom s hs

theorem check_second_payload_at_deadline {a m B zeros : Nat} (x : Bitstring a)
    (w : Bitstring m) (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 2 ≤ zeros) (hroom : a + m + 3 < tapeLength (pairLength a m) B) :
    let d := machine.run (deadline (a + m)) (startConfig B x w)
    d.state = qDone ∧ d.head.val = 7 ∧
      d.tape = secondPayloadTape B x w
        ((FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros)).getD false)
        ((FixedContentTagGate.physicalSymbol (Fin.append x w) (10 + zeros)).getD false) :=
  second_payload_at_deadline x w htag hg hz hroom

theorem check_second_physical_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (b : Bool) (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 2 ≤ zeros)
    (hread : FixedContentTagGate.physicalSymbol (Fin.append x w) (10 + zeros) = some b)
    (hroom : a + m + 3 < tapeLength (pairLength a m) B)
    (s : Nat) (hs : exactClock (a + m) zeros ≤ s) :
    let d := machine.run s (startConfig B x w)
    d.state = qDone ∧ d.head.val = 7 ∧
      d.tape = secondPayloadTape B x w
        ((FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros)).getD false) b :=
  second_physical_exact x w b htag hg hz hread hroom s hs

theorem check_second_virtual_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 2 ≤ zeros) (hvirtual : a + m ≤ 10 + zeros)
    (hroom : a + m + 3 < tapeLength (pairLength a m) B)
    (s : Nat) (hs : exactClock (a + m) zeros ≤ s) :
    let d := machine.run s (startConfig B x w)
    d.state = qDone ∧ d.head.val = 7 ∧
      d.tape = secondPayloadTape B x w
        ((FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros)).getD false)
        false :=
  second_virtual_exact x w htag hg hz hvirtual hroom s hs

/-- A head range, not a footprint: it bounds the cells the head visits on this
branch, and says nothing about which cells may differ from the incoming tape.
The all-times footprint/budget package stays deferred for every branch. -/
theorem check_positive_width_head_range {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 2 ≤ zeros) (hroom : a + m + 3 < tapeLength (pairLength a m) B) (s : Nat) :
    let d := machine.run s (startConfig B x w)
    7 ≤ d.head.val ∧ d.head.val ≤ a + m + 3 :=
  positive_width_head_range x w htag hg hz hroom s

theorem check_positive_width_no_boundary_clamp {a m B zeros : Nat} (x : Bitstring a)
    (w : Bitstring m) (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 2 ≤ zeros) (hroom : a + m + 3 < tapeLength (pairLength a m) B) (s : Nat) :
    let d := machine.run s (startConfig B x w)
    let move := (machine.step d.state (d.tape d.head)).2.2
    (move = .right → d.head.val + 1 < tapeLength (pairLength a m) B) ∧
    (move = .left → 0 < d.head.val) :=
  positive_width_no_boundary_clamp x w htag hg hz hroom s

/-! ### Independent literal reduction probes

These probes deliberately do **not** invoke this module's endpoint theorems.
Each branch is handled in two steps.  First, `check_*_handoff` identifies the
*actual* phase-local start configuration with an explicit configuration, using
only the previously landed G2p-b endpoint theorem and the definitional
`retagFirstPayload` handoff; these hold for every budget `B`.  Second, at the
concrete budget `B = 0`, this module's own `machine.run` is reduced by kernel
computation on that configuration, exposing intermediate state/head/cell facts.
They therefore check the address choreography — the width dispatch at cells `8`
and `9`, the anchor blank at cell `7` and its restoration, the target cell
`a + m + 3` (which every one of these concrete inputs allocates, and which the
width-one probe pins still blank while the two positive-width probes pin blank
and then written), and on the positive-width inputs the whole copy route down to
the step at which the digit appears there — rather than restating a public
endpoint.  Not every probe pins every item: the malformed probe pins none of
them, only the handed-over configuration in neither terminal state and the
one-step rejection in place at the boundary head, still there at step `5`; and
the width-zero probe pins no cell beyond the anchor.

The tag is `10110010`.  `widthZero` decodes to `zeros = 0` (terminator at cell
`8`, `N = 9`); `widthOne` decodes to `zeros = 1` (terminator at cell `9`,
`N = 11`, first payload digit `true` at cell `10`); `malformed` has no gamma
terminator below the boundary (`N = 11`).  `widthTwo` decodes to `zeros = 2`
(terminator at cell `10`, `N = 13`, payload digits `false` at cell `11` and
`true` at the source cell `12`); `widthTwoTight` also decodes to `zeros = 2` but
ends at the terminator (`N = 11`), so *both* payload digits are virtual. -/

private def tag : Bitstring 8 := ![true, false, true, true, false, false, true, false]
private def malformed : Bitstring 3 := ![false, false, false]
private def widthZero : Bitstring 1 := ![true]
private def widthOne : Bitstring 3 := ![false, true, true]
private def widthTwo : Bitstring 5 := ![false, false, true, false, true]
private def widthTwoTight : Bitstring 3 := ![false, false, true]

/-- Rebuild a configuration from its three projections.  Stated over a
configuration *variable*, so that identifying the phase-local start
configuration never has to reduce the G2p-b run term inside it. -/
private theorem config_of_parts {K n B : Nat} {c : Config K n B} {q : Fin K} {k : Nat}
    {hk : k < tapeLength n B} {T : Fin (tapeLength n B) → Option Bool}
    (hq : c.state = q) (hh : c.head.val = k) (ht : c.tape = T) :
    c = ⟨q, ⟨k, hk⟩, T⟩ := by
  obtain ⟨cs, ch, ct⟩ := c
  cases hq
  cases ht
  exact congrArg (fun h => (⟨cs, h, ct⟩ : Config K n B)) (Fin.ext hh)

theorem check_malformed_handoff (B : Nat) :
    startConfig B tag malformed =
      ⟨qStart, ⟨8 + 3, by unfold tapeLength pairLength; omega⟩,
        FixedPairContentMarkerErase.contentTape B tag malformed⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTargetFirstPayload.malformed_at_deadline
    (B := B) tag malformed (by decide) (by decide)
  config_of_parts rfl hh ht

theorem check_zero_handoff (B : Nat) :
    startConfig B tag widthZero =
      ⟨qStart, ⟨7, by unfold tapeLength pairLength; omega⟩,
        FixedGammaTerminatorScratchBootstrap.scratchTape B tag widthZero⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTargetFirstPayload.zero_width_at_deadline
    (B := B) tag widthZero (by decide) (by decide)
  config_of_parts rfl hh ht

theorem check_one_handoff (B : Nat) :
    startConfig B tag widthOne =
      ⟨qStart, ⟨7, by unfold tapeLength pairLength; omega⟩,
        FixedGammaTargetFirstPayload.firstPayloadTape B tag widthOne true⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTargetFirstPayload.first_physical_at_deadline
    (B := B) (zeros := 1) tag widthOne true (by decide) (by decide) (by omega) (by decide)
    (by unfold tapeLength pairLength; omega)
  config_of_parts rfl hh ht

/-- Malformed: the handed-over configuration is in neither terminal state, one
step rejects in place at the boundary head `N = 11`, and the rejection is
absorbing — so for this input `malformedExactClock = 1` is literally the first
terminal time. -/
theorem check_malformed_probe :
    (machine.run 0 (startConfig 0 tag malformed)).state ≠ qDone ∧
    (machine.run 0 (startConfig 0 tag malformed)).state ≠ qReject ∧
    (machine.run 1 (startConfig 0 tag malformed)).state = qReject ∧
    (machine.run 1 (startConfig 0 tag malformed)).head.val = 11 ∧
    (machine.run 1 (startConfig 0 tag malformed)).tape ⟨11, by decide⟩ = none ∧
    (machine.run 5 (startConfig 0 tag malformed)).state = qReject ∧
    (machine.run 5 (startConfig 0 tag malformed)).head.val = 11 := by
  rw [check_malformed_handoff 0]
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Width zero: step 1 blanks the anchor at cell `7` and lands on cell `8`; the
terminator there dispatches straight to the leftward sweep (`qScanLeft`, so no
`qInspectNine`); step 3 restores the anchor and halts at head `7`.  For this
concrete input the heads pinned below are the whole run, so they do show that no
cell past `8` is read — that is a fact about these literals, not a footprint
theorem, which the module does not export. -/
theorem check_zero_probe :
    (machine.run 1 (startConfig 0 tag widthZero)).state = qInspectEight ∧
    (machine.run 1 (startConfig 0 tag widthZero)).head.val = 8 ∧
    (machine.run 1 (startConfig 0 tag widthZero)).tape ⟨7, by decide⟩ = none ∧
    (machine.run 2 (startConfig 0 tag widthZero)).state = qScanLeft ∧
    (machine.run 2 (startConfig 0 tag widthZero)).head.val = 7 ∧
    (machine.run 3 (startConfig 0 tag widthZero)).state = qDone ∧
    (machine.run 3 (startConfig 0 tag widthZero)).head.val = 7 ∧
    (machine.run 3 (startConfig 0 tag widthZero)).tape ⟨7, by decide⟩ = some false := by
  rw [check_zero_handoff 0]
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

/-- Width one: step 2 reaches `qInspectNine` at head `9` — the gamma zero at cell
`8` is *not* mistaken for the terminator — and the terminator at cell `9` turns
the run around; step 5 restores the anchor at cell `7` and halts at head `7`,
with the G2p-b digit at `N + 2 = 13` intact and the second-digit target cell
`N + 3 = 14` still blank. -/
theorem check_one_probe :
    (machine.run 1 (startConfig 0 tag widthOne)).state = qInspectEight ∧
    (machine.run 1 (startConfig 0 tag widthOne)).head.val = 8 ∧
    (machine.run 1 (startConfig 0 tag widthOne)).tape ⟨7, by decide⟩ = none ∧
    (machine.run 2 (startConfig 0 tag widthOne)).state = qInspectNine ∧
    (machine.run 2 (startConfig 0 tag widthOne)).head.val = 9 ∧
    (machine.run 3 (startConfig 0 tag widthOne)).state = qScanLeft ∧
    (machine.run 3 (startConfig 0 tag widthOne)).head.val = 8 ∧
    (machine.run 5 (startConfig 0 tag widthOne)).state = qDone ∧
    (machine.run 5 (startConfig 0 tag widthOne)).head.val = 7 ∧
    (machine.run 5 (startConfig 0 tag widthOne)).tape ⟨7, by decide⟩ = some false ∧
    (machine.run 5 (startConfig 0 tag widthOne)).tape ⟨13, by decide⟩ = some true ∧
    (machine.run 5 (startConfig 0 tag widthOne)).tape ⟨14, by decide⟩ = none := by
  rw [check_one_handoff 0]
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

/-! ### Positive-width probes

These two probes exercise the `2 ≤ zeros` route by kernel computation only; they
do not invoke `second_payload_exact`, `second_physical_exact`,
`second_virtual_exact`, or any other endpoint theorem of the module.  Both
budgets are `B = 0`, which for `a = 8` allocates the target cell (`2 ≤ a + B`). -/

theorem check_two_handoff (B : Nat) :
    startConfig B tag widthTwo =
      ⟨qStart, ⟨7, by unfold tapeLength pairLength; omega⟩,
        FixedGammaTargetFirstPayload.firstPayloadTape B tag widthTwo false⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTargetFirstPayload.first_physical_at_deadline
    (B := B) (zeros := 2) tag widthTwo false (by decide) (by decide) (by omega) (by decide)
    (by unfold tapeLength pairLength; omega)
  config_of_parts rfl hh ht

theorem check_two_tight_handoff (B : Nat) :
    startConfig B tag widthTwoTight =
      ⟨qStart, ⟨7, by unfold tapeLength pairLength; omega⟩,
        FixedGammaTargetFirstPayload.firstPayloadTape B tag widthTwoTight false⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTargetFirstPayload.first_virtual_at_deadline
    (B := B) (zeros := 2) tag widthTwoTight (by decide) (by decide) (by omega) (by omega)
    (by unfold tapeLength pairLength; omega)
  config_of_parts rfl hh ht

/-- The premise set of the positive-width theorems is satisfiable, and the
clock is a concrete number: these are the literal premises of
`second_payload_exact` and `second_physical_exact` at the first probe input,
each decided by kernel computation.  `B = 0` already allocates the target cell,
so the endpoint theorems are not vacuous. -/
theorem check_two_premises :
    FixedContentTagGate.tagMatches (Fin.append tag widthTwo) = true ∧
    FixedContentGammaTerminator.gammaZeros? (Fin.append tag widthTwo) = some 2 ∧
    8 + 5 + 3 < tapeLength (pairLength 8 5) 0 ∧
    FixedContentTagGate.physicalSymbol (Fin.append tag widthTwo) (10 + 2) = some true ∧
    exactClock (8 + 5) 2 = 19 :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- The same for the virtual input, including the `a + m ≤ 10 + zeros` premise
of `second_virtual_exact` and the blank *content* symbol at the logical source
address it describes.  The input has no symbol at that address; the phase tape
does have a cell there, holding the register `true`, as `check_two_tight_probe`
pins. -/
theorem check_two_tight_premises :
    FixedContentTagGate.tagMatches (Fin.append tag widthTwoTight) = true ∧
    FixedContentGammaTerminator.gammaZeros? (Fin.append tag widthTwoTight) = some 2 ∧
    8 + 3 ≤ 10 + 2 ∧
    8 + 3 + 3 < tapeLength (pairLength 8 3) 0 ∧
    FixedContentTagGate.physicalSymbol (Fin.append tag widthTwoTight) (10 + 2) = none ∧
    exactClock (8 + 3) 2 = 15 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 4000 in
/-- Width two with a physical source cell (`N = 13`).  The run blanks the anchor
at cell `7`, walks past the two gamma zeros at `8` and `9` — neither is mistaken
for the terminator — meets the terminator at `10`, *steps over* the first payload
cell `11` in `qStepOne`, and reads the source cell `12`, whose `true` sends it
into `qCarry1` at the blank boundary `13`.  It then crosses the register cells
`14` and `15` without taking either as source; the probe pins the `qCarry1` at
`13` (step `6`) and the `qReg1` at `16` (step `9`) that bracket that crossing,
not the two intermediate configurations.  At step `9` the head is on
`16 = N + 3` and that cell is still blank; the transition taken *there* is the
write, so the `true` at `16` is first visible at step `10`, by which time the
control is already `qBackReg`.  At step `18` the control is in neither terminal
state, and both terminal states absorb (`check_endpoints_absorb`), so no
terminal state was reached before `18` either; together with the `qDone` at step
`19` that makes `2 * N - 7 = 19` literally the first terminal time for this
input.  At step `19` it halts at head `7` with the anchor restored, the register
`true` at `14` and the G2p-b digit `false` at `15` intact, the second digit
`true` at `16`, and `17` still blank. -/
theorem check_two_probe :
    (machine.run 1 (startConfig 0 tag widthTwo)).state = qInspectEight ∧
    (machine.run 1 (startConfig 0 tag widthTwo)).tape ⟨7, by decide⟩ = none ∧
    (machine.run 2 (startConfig 0 tag widthTwo)).state = qInspectNine ∧
    (machine.run 3 (startConfig 0 tag widthTwo)).state = qSeekTerm ∧
    (machine.run 3 (startConfig 0 tag widthTwo)).head.val = 10 ∧
    (machine.run 4 (startConfig 0 tag widthTwo)).state = qStepOne ∧
    (machine.run 4 (startConfig 0 tag widthTwo)).head.val = 11 ∧
    (machine.run 5 (startConfig 0 tag widthTwo)).state = qRead ∧
    (machine.run 5 (startConfig 0 tag widthTwo)).head.val = 12 ∧
    (machine.run 5 (startConfig 0 tag widthTwo)).tape ⟨12, by decide⟩ = some true ∧
    (machine.run 6 (startConfig 0 tag widthTwo)).state = qCarry1 ∧
    (machine.run 6 (startConfig 0 tag widthTwo)).head.val = 13 ∧
    (machine.run 9 (startConfig 0 tag widthTwo)).state = qReg1 ∧
    (machine.run 9 (startConfig 0 tag widthTwo)).head.val = 16 ∧
    (machine.run 9 (startConfig 0 tag widthTwo)).tape ⟨16, by decide⟩ = none ∧
    (machine.run 10 (startConfig 0 tag widthTwo)).state = qBackReg ∧
    (machine.run 10 (startConfig 0 tag widthTwo)).tape ⟨16, by decide⟩ = some true ∧
    (machine.run 18 (startConfig 0 tag widthTwo)).state ≠ qDone ∧
    (machine.run 18 (startConfig 0 tag widthTwo)).state ≠ qReject ∧
    (machine.run 19 (startConfig 0 tag widthTwo)).state = qDone ∧
    (machine.run 19 (startConfig 0 tag widthTwo)).head.val = 7 ∧
    (machine.run 19 (startConfig 0 tag widthTwo)).tape ⟨7, by decide⟩ = some false ∧
    (machine.run 19 (startConfig 0 tag widthTwo)).tape ⟨14, by decide⟩ = some true ∧
    (machine.run 19 (startConfig 0 tag widthTwo)).tape ⟨15, by decide⟩ = some false ∧
    (machine.run 19 (startConfig 0 tag widthTwo)).tape ⟨16, by decide⟩ = some true ∧
    (machine.run 19 (startConfig 0 tag widthTwo)).tape ⟨17, by decide⟩ = none := by
  rw [check_two_handoff 0]
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

set_option maxRecDepth 4000 in
/-- Width two with *both* payload digits virtual (`N = 11`): the content ends at
the terminator, so the first payload cell `11` *is* the blank boundary.
`qStepOne` reads that blank and hands straight to `qReg0`, so `qRead` is never
entered on this shape.  The logical source address `10 + zeros = 12` is here
`N + 1`, the register cell: the head does pass it at step `5`, and the step-`5`
conjuncts pin that it does so in `qReg0`.  That the cell holds the register
`true` is pinned at the endpoint, step `15`, and not at step `5`; the run
crosses it rather than reading it as a source, as it does the G2p-b digit at
`13`.  The virtual zero `false` appears at `14 = N + 3` at step `8`, written by
the transition taken at step `7`, where the head is on that still-blank cell.
At step `14` the control is in neither terminal state, and both terminal states
absorb (`check_endpoints_absorb`), so no terminal state was reached before `14`
either; together with the `qDone` at step `15` that makes `2 * N - 7 = 15`
literally the first terminal time for this input. -/
theorem check_two_tight_probe :
    (machine.run 4 (startConfig 0 tag widthTwoTight)).state = qStepOne ∧
    (machine.run 4 (startConfig 0 tag widthTwoTight)).head.val = 11 ∧
    (machine.run 4 (startConfig 0 tag widthTwoTight)).tape ⟨11, by decide⟩ = none ∧
    (machine.run 5 (startConfig 0 tag widthTwoTight)).state = qReg0 ∧
    (machine.run 5 (startConfig 0 tag widthTwoTight)).head.val = 12 ∧
    (machine.run 7 (startConfig 0 tag widthTwoTight)).head.val = 14 ∧
    (machine.run 7 (startConfig 0 tag widthTwoTight)).tape ⟨14, by decide⟩ = none ∧
    (machine.run 8 (startConfig 0 tag widthTwoTight)).tape ⟨14, by decide⟩ = some false ∧
    (machine.run 14 (startConfig 0 tag widthTwoTight)).state ≠ qDone ∧
    (machine.run 14 (startConfig 0 tag widthTwoTight)).state ≠ qReject ∧
    (machine.run 15 (startConfig 0 tag widthTwoTight)).state = qDone ∧
    (machine.run 15 (startConfig 0 tag widthTwoTight)).head.val = 7 ∧
    (machine.run 15 (startConfig 0 tag widthTwoTight)).tape ⟨7, by decide⟩ = some false ∧
    (machine.run 15 (startConfig 0 tag widthTwoTight)).tape ⟨12, by decide⟩ = some true ∧
    (machine.run 15 (startConfig 0 tag widthTwoTight)).tape ⟨14, by decide⟩ = some false := by
  rw [check_two_tight_handoff 0]
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

end Pnp3.Tests.UniformV1FixedGammaTargetSecondPayloadSurfaceTests
