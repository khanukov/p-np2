import Complexity.Uniform.V1.FixedGammaTargetPayloadRound

/-!
Surface pins for the Part A G2p-d round: the fixed 22-state/66-row machine that
executes **one** round of the self-stopping gamma payload loop on the phase-local
retag of the *actual* G2p-d foundation endpoint, and the exact endpoint that carries
the loop invariant `loopTape B x w zeros r` from `r = 2` to `r = 3`.  All 66
transition rows are restated literally below, not aliased.  `roundClock N` is
`2 * N - 7`, length-only, counts this phase alone, and is an *exact* time, not one
from which the endpoint persists, because `qLoop` does not absorb — so no wrapper
pins the endpoint later and there is no phase deadline to pin.  Not here and not
available to pin: the iteration, the exhaustion finish, the complete register, the
loop's own deadline, a cell-by-cell `r = 3` layout, a first-arrival/strictness
direction, the all-times clamp/footprint/budget package, the degenerate widths
`zeros ≤ 2`, any parsed header value, and any pnp4 bridge.  Runs satisfying
`round_step`'s premises do not execute `qFin`; public `startConfig` at `zeros = 2` can follow
exhaustion through `qFin` to `qDone`, but no theorem wrapper covers that behavior;
`qDone` is not language acceptance, and no wrapper states a converse. -/

namespace Pnp3.Tests.UniformV1FixedGammaTargetPayloadRoundSurfaceTests
open Complexity.Uniform.V1
open Complexity.Uniform.V1.PairEncoding
open Complexity.Uniform.V1.FixedGammaTargetPayloadRound
open Complexity.Uniform.V1.FixedGammaTargetPayloadLoopFoundation (walk registerBit loopTape)

def check_stateCount : Nat := stateCount
def check_states : List (Fin stateCount) :=
  [qLoop, qCntL, qCntZ, qCntMark, qCntBack, qSrc, qClear0, qClear1, qCarry0, qCarry1,
    qReg0, qReg1, qBackReg, qBackCont, qVa, qVb, qRegV, qBackRegV, qVc, qFin, qDone, qReject]
def check_raw :
    Fin stateCount → Option Bool → Fin stateCount × Option Bool × Move := raw
def check_machine : UniformTM := machine
def check_retagLoopFoundation {N B : Nat} :
    Config FixedGammaTargetPayloadLoopFoundation.stateCount N B → Config stateCount N B :=
  retagLoopFoundation
def check_startConfig {a m : Nat} :
    (B : Nat) → Bitstring a → Bitstring m → Config stateCount (pairLength a m) B :=
  startConfig
def check_roundClock (N : Nat) : Nat := roundClock N
def check_malformedExactClock : Nat := malformedExactClock
def check_sourceCell (N zeros : Nat) : Nat := sourceCell N zeros

/-- All 66 transition rows of the fixed table, restated literally and re-derived by `rfl`,
with the resource counts; the 22 `.val` index pins are surfaced by the alias below. -/
theorem check_table_rows :
    machine.step qLoop none = (qReject, none, .stay) ∧
    machine.step qLoop (some false) = (qReject, some false, .stay) ∧
    machine.step qLoop (some true) = (qCntL, some true, .left) ∧
    machine.step qCntL none = (qCntL, none, .left) ∧
    machine.step qCntL (some false) = (qCntZ, some false, .left) ∧
    machine.step qCntL (some true) = (qFin, some false, .left) ∧
    machine.step qCntZ none = (qReject, none, .stay) ∧
    machine.step qCntZ (some false) = (qCntZ, some false, .left) ∧
    machine.step qCntZ (some true) = (qCntMark, some true, .right) ∧
    machine.step qCntMark none = (qReject, none, .stay) ∧
    machine.step qCntMark (some false) = (qCntBack, some true, .right) ∧
    machine.step qCntMark (some true) = (qReject, some true, .stay) ∧
    machine.step qCntBack none = (qCntBack, none, .right) ∧
    machine.step qCntBack (some false) = (qCntBack, some false, .right) ∧
    machine.step qCntBack (some true) = (qSrc, some true, .right) ∧
    machine.step qSrc none = (qVa, none, .left) ∧
    machine.step qSrc (some false) = (qClear0, some true, .left) ∧
    machine.step qSrc (some true) = (qClear1, some true, .left) ∧
    machine.step qClear0 none = (qReject, none, .stay) ∧
    machine.step qClear0 (some false) = (qReject, some false, .stay) ∧
    machine.step qClear0 (some true) = (qCarry0, none, .right) ∧
    machine.step qClear1 none = (qReject, none, .stay) ∧
    machine.step qClear1 (some false) = (qReject, some false, .stay) ∧
    machine.step qClear1 (some true) = (qCarry1, none, .right) ∧
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
    machine.step qBackReg none = (qBackCont, none, .left) ∧
    machine.step qBackReg (some false) = (qBackReg, some false, .left) ∧
    machine.step qBackReg (some true) = (qBackReg, some true, .left) ∧
    machine.step qBackCont none = (qLoop, none, .right) ∧
    machine.step qBackCont (some false) = (qBackCont, some false, .left) ∧
    machine.step qBackCont (some true) = (qBackCont, some true, .left) ∧
    machine.step qVa none = (qReject, none, .stay) ∧
    machine.step qVa (some false) = (qReject, some false, .stay) ∧
    machine.step qVa (some true) = (qVb, some true, .right) ∧
    machine.step qVb none = (qRegV, none, .right) ∧
    machine.step qVb (some false) = (qReject, some false, .stay) ∧
    machine.step qVb (some true) = (qReject, some true, .stay) ∧
    machine.step qRegV none = (qBackRegV, some false, .left) ∧
    machine.step qRegV (some false) = (qRegV, some false, .right) ∧
    machine.step qRegV (some true) = (qRegV, some true, .right) ∧
    machine.step qBackRegV none = (qVc, none, .left) ∧
    machine.step qBackRegV (some false) = (qBackRegV, some false, .left) ∧
    machine.step qBackRegV (some true) = (qBackRegV, some true, .left) ∧
    machine.step qVc none = (qReject, none, .stay) ∧
    machine.step qVc (some false) = (qReject, some false, .stay) ∧
    machine.step qVc (some true) = (qLoop, some true, .stay) ∧
    machine.step qFin none = (qReject, none, .stay) ∧
    machine.step qFin (some false) = (qDone, some false, .stay) ∧
    machine.step qFin (some true) = (qFin, some false, .left) ∧
    machine.step qDone none = (qDone, none, .stay) ∧
    machine.step qDone (some false) = (qDone, some false, .stay) ∧
    machine.step qDone (some true) = (qDone, some true, .stay) ∧
    machine.step qReject none = (qReject, none, .stay) ∧
    machine.step qReject (some false) = (qReject, some false, .stay) ∧
    machine.step qReject (some true) = (qReject, some true, .stay) ∧
    machine.stateCount = 22 ∧ machine.start = qLoop ∧
    machine.accept = qDone ∧ machine.reject = qReject ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 66 := by
  repeat' apply And.intro
  all_goals rfl

def check_table_and_resource_pins := @table_and_resource_pins

theorem check_per_step_budget_independent :
    ∀ q s, machine.step q s = machine.rawStep q s :=
  per_step_budget_independent

theorem check_endpoints_absorb {N B : Nat} (c : Config stateCount N B) :
    (c.state = qDone → ∀ n, machine.run n c = c) ∧
    (c.state = qReject → ∀ n, machine.run n c = c) :=
  endpoints_absorb c

theorem check_handoff_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let p := FixedGammaTargetPayloadLoopFoundation.machine.run
      (FixedGammaTargetPayloadLoopFoundation.deadline (a + m))
      (FixedGammaTargetPayloadLoopFoundation.startConfig B x w)
    let c := startConfig B x w
    c = retagLoopFoundation p ∧ c.state = machine.start ∧ c.head = p.head ∧
      c.tape = p.tape :=
  handoff_exact x w

theorem check_clock_pins (N zeros : Nat) :
    roundClock N = 2 * N - 7 ∧ malformedExactClock = 1 ∧
      sourceCell N zeros = 9 + zeros + walk N zeros 2 :=
  clock_pins N zeros

theorem check_room_iff (a m B : Nat) :
    (a + m + 4 < tapeLength (pairLength a m) B ↔ 3 ≤ a + B) ∧
      (a + m + 4 < tapeLength (pairLength a m) B →
        a + m + 3 < tapeLength (pairLength a m) B) :=
  room_iff a m B

theorem check_source_pins {N zeros : Nat} (hz : 3 ≤ zeros) (hN : 9 + zeros ≤ N) :
    (11 + zeros < N → sourceCell N zeros = 11 + zeros) ∧
      (N ≤ 11 + zeros → sourceCell N zeros = N) ∧
      (9 + zeros ≤ 11 + zeros ∧ 11 + zeros < 9 + 2 * zeros) ∧
      sourceCell N zeros ≤ N :=
  source_pins hz hN

theorem check_registerBit_source {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (zeros : Nat) :
    registerBit x w zeros 3 =
      (FixedContentTagGate.physicalSymbol (Fin.append x w) (11 + zeros)).getD false :=
  registerBit_source x w zeros

theorem check_round_step {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 3 ≤ zeros) (hroom : a + m + 4 < tapeLength (pairLength a m) B) :
    let d := machine.run (roundClock (a + m)) (startConfig B x w)
    d.state = qLoop ∧ d.head.val = 8 + zeros + walk (a + m) zeros 3 ∧
      d.tape = loopTape B x w zeros 3 :=
  round_step x w htag hg hzeros hroom

theorem check_malformed_rejects {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none)
    (s : Nat) (hs : malformedExactClock ≤ s) :
    let d := machine.run s (startConfig B x w)
    d.state = qReject ∧ d.head.val = a + m ∧
      d.tape = FixedPairContentMarkerErase.contentTape B x w :=
  malformed_rejects x w htag hg s hs

/-! ### Independent literal reduction probes

These probes deliberately do **not** invoke this module's execution theorems.
`check_*_handoff` first identifies the *actual* phase-local start configuration
with an explicit configuration for every budget, using only the landed G2p-d
foundation endpoint theorem and the definitional `retagLoopFoundation` handoff;
then, at `B = 0`, this module's own `machine.run` is reduced by kernel computation
on it.  Each probe is a claim about its own input.  The tag is `10110010` and both
words decode to `zeros = 3`.  `physWord` has `N = 15`, so the source
`11 + zeros = 14` is a physical content cell; `virtWord` has `N = 12`, where
`walk N 3 2 = 0` and the source address `9 + zeros = 12` *is* the boundary blank. -/

private def tag : Bitstring 8 := ![true, false, true, true, false, false, true, false]
private def physWord : Bitstring 7 := ![false, false, false, true, false, true, true]
private def virtWord : Bitstring 4 := ![false, false, false, true]

/-- Rebuild a configuration from its three projections.  Stated over a
configuration *variable*, so that identifying the phase-local start configuration
never has to reduce the foundation run term inside it. -/
private theorem config_of_parts {K n B : Nat} {c : Config K n B} {q : Fin K} {k : Nat}
    {hk : k < tapeLength n B} {T : Fin (tapeLength n B) → Option Bool}
    (hq : c.state = q) (hh : c.head.val = k) (ht : c.tape = T) :
    c = ⟨q, ⟨k, hk⟩, T⟩ := by
  obtain ⟨cs, ch, ct⟩ := c
  cases hq
  cases ht
  exact congrArg (fun h => (⟨cs, h, ct⟩ : Config K n B)) (Fin.ext hh)

theorem check_phys_handoff (B : Nat) :
    startConfig B tag physWord =
      ⟨qLoop, ⟨13, by unfold tapeLength pairLength; omega⟩,
        loopTape B tag physWord 3 2⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTargetPayloadLoopFoundation.markers_at_deadline
    (B := B) (zeros := 3) tag physWord (by decide) (by decide) (by decide)
    (by unfold tapeLength pairLength; omega)
  config_of_parts rfl (hh.trans (by decide)) ht

theorem check_virt_handoff (B : Nat) :
    startConfig B tag virtWord =
      ⟨qLoop, ⟨11, by unfold tapeLength pairLength; omega⟩,
        loopTape B tag virtWord 3 2⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTargetPayloadLoopFoundation.markers_at_deadline
    (B := B) (zeros := 3) tag virtWord (by decide) (by decide) (by decide)
    (by unfold tapeLength pairLength; omega)
  config_of_parts rfl (hh.trans (by decide)) ht

set_option maxRecDepth 100000 in
/-- Physical source (`N = 15`, `roundClock 15 = 23`): cell `10` carries the third
counter mark at step six, the head is on the source `14` at step nine, the `true`
there is carried in the control (`qClear1` at step ten), the vacated `13` is blank at
step eleven, `N + 4 = 19` goes from blank at step sixteen to `true` at step seventeen,
step twenty-two is `qBackCont`, one step before the end, and step twenty-three is `qLoop`
on the new terminator `14`, with `13` blank, `10` marked, `17` `false` and `19` `true`. -/
theorem check_phys_probe :
    (machine.run 6 (startConfig 0 tag physWord)).tape ⟨10, by decide⟩ = some true ∧
    (machine.run 9 (startConfig 0 tag physWord)).head.val = 14 ∧
    (machine.run 10 (startConfig 0 tag physWord)).state = qClear1 ∧
    (machine.run 11 (startConfig 0 tag physWord)).tape ⟨13, by decide⟩ = none ∧
    (machine.run 16 (startConfig 0 tag physWord)).tape ⟨19, by decide⟩ = none ∧
    (machine.run 17 (startConfig 0 tag physWord)).tape ⟨19, by decide⟩ = some true ∧
    (machine.run 22 (startConfig 0 tag physWord)).state = qBackCont ∧
    (machine.run 23 (startConfig 0 tag physWord)).state = qLoop ∧
    (machine.run 23 (startConfig 0 tag physWord)).head.val = 14 ∧
    (machine.run 23 (startConfig 0 tag physWord)).tape ⟨10, by decide⟩ = some true ∧
    (machine.run 23 (startConfig 0 tag physWord)).tape ⟨13, by decide⟩ = none ∧
    (machine.run 23 (startConfig 0 tag physWord)).tape ⟨14, by decide⟩ = some true ∧
    (machine.run 23 (startConfig 0 tag physWord)).tape ⟨17, by decide⟩ = some false ∧
    (machine.run 23 (startConfig 0 tag physWord)).tape ⟨19, by decide⟩ = some true := by
  rw [check_phys_handoff 0]
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 100000 in
/-- Virtual source (`N = 12`, `roundClock 12 = 17`): cell `10` carries the third
counter mark at step four, the head is on the boundary cell `12` in `qSrc` at step
five, the padding states `qVa`/`qVb` are entered at steps six and seven,
`N + 4 = 16` goes from blank at step eleven to the virtual `false` at step twelve,
step sixteen is `qVc`, and step seventeen is `qLoop` on the *unmoved*
terminator `11`, with `12` blank and the digits at `14` and `16` both `false`. -/
theorem check_virt_probe :
    (machine.run 4 (startConfig 0 tag virtWord)).tape ⟨10, by decide⟩ = some true ∧
    (machine.run 5 (startConfig 0 tag virtWord)).head.val = 12 ∧
    (machine.run 5 (startConfig 0 tag virtWord)).state = qSrc ∧
    (machine.run 6 (startConfig 0 tag virtWord)).state = qVa ∧
    (machine.run 7 (startConfig 0 tag virtWord)).state = qVb ∧
    (machine.run 11 (startConfig 0 tag virtWord)).tape ⟨16, by decide⟩ = none ∧
    (machine.run 12 (startConfig 0 tag virtWord)).tape ⟨16, by decide⟩ = some false ∧
    (machine.run 16 (startConfig 0 tag virtWord)).state = qVc ∧
    (machine.run 17 (startConfig 0 tag virtWord)).state = qLoop ∧
    (machine.run 17 (startConfig 0 tag virtWord)).head.val = 11 ∧
    (machine.run 17 (startConfig 0 tag virtWord)).tape ⟨11, by decide⟩ = some true ∧
    (machine.run 17 (startConfig 0 tag virtWord)).tape ⟨12, by decide⟩ = none ∧
    (machine.run 17 (startConfig 0 tag virtWord)).tape ⟨14, by decide⟩ = some false ∧
    (machine.run 17 (startConfig 0 tag virtWord)).tape ⟨16, by decide⟩ = some false := by
  rw [check_virt_handoff 0]
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

end Pnp3.Tests.UniformV1FixedGammaTargetPayloadRoundSurfaceTests
