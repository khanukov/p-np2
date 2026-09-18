import Complexity.Uniform.V1.FixedGammaTargetSecondPayload

/-!
Surface pins for the Part A G2p-c1 foundation slice of the second gamma payload
digit: the fixed 14-state/42-row table, the phase-local handoff ABI, exact room,
the phase-local clocks, and the two decoded widths at which the machine provably
makes no net payload or register write and leaves the tape unchanged end to end (the
anchor *is* blanked in flight and restored, so what is pinned is the absence of a
net tape change).  The positive-width (`2 ≤ zeros`) trace and every pnp4/parser
claim are deferred to later slices, and so is the all-times
clamp/footprint/budget package, which the slice exports for no branch at all —
not even for the two proved widths, so no wrapper below pins a head range or a
read footprint, and none is available to pin: the module's head-range prose
(`no cell past 9`, `no cell past 8`, `no boundary clamp`) lives inside its
private traces.  What the endpoint wrappers restate are tape equalities, which
pin the *net* effect of a run rather than the cells it visited.  The clocks are
pinned in both directions — `check_*_exact` for the endpoint from the clock on
and `check_*_strict` for the exclusion of both terminals before it, malformed
branch included.  The eight positive-route states pinned below
(`qSeekTerm`, `qStepOne`, `qRead`, `qCarry0`, `qCarry1`, `qReg0`, `qReg1`,
`qBackReg`) are pinned as deliberately landed control; no public execution
theorem of this slice exercises them.
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

/-! ### Independent literal reduction probes

These probes deliberately do **not** invoke this module's endpoint theorems.
Each branch is handled in two steps.  First, `check_*_handoff` identifies the
*actual* phase-local start configuration with an explicit configuration, using
only the previously landed G2p-b endpoint theorem and the definitional
`retagFirstPayload` handoff; these hold for every budget `B`.  Second, at the
concrete budget `B = 0`, this module's own `machine.run` is reduced by kernel
computation on that configuration, exposing intermediate state/head/cell facts.
They therefore check the address choreography — the width dispatch at cells `8`
and `9`, the anchor blank at cell `7` and its restoration, and the target cell
`a + m + 3`, which these concrete inputs do allocate, staying blank — rather than
restating a public endpoint.

The tag is `10110010`.  `widthZero` decodes to `zeros = 0` (terminator at cell
`8`, `N = 9`); `widthOne` decodes to `zeros = 1` (terminator at cell `9`,
`N = 11`, first payload digit `true` at cell `10`); `malformed` has no gamma
terminator below the boundary (`N = 11`). -/

private def tag : Bitstring 8 := ![true, false, true, true, false, false, true, false]
private def malformed : Bitstring 3 := ![false, false, false]
private def widthZero : Bitstring 1 := ![true]
private def widthOne : Bitstring 3 := ![false, true, true]

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

end Pnp3.Tests.UniformV1FixedGammaTargetSecondPayloadSurfaceTests
