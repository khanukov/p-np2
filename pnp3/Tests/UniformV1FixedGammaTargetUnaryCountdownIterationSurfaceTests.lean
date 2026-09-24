import Complexity.Uniform.V1.FixedGammaTargetUnaryCountdownIteration

/-!
Surface pins for the Part A G2u countdown iteration: **no new machine and no new table row**, only
longer runs of the G2s-a fixed 11-state, 33-row table.  Write `N = a + m`.

What is pinned.  `check_rounds_clock_pins` fixes the closed form
`roundsClock zeros r k = k*k + k*(2*zeros + 2*r + 6)`, the recurrence that drives the induction and
both compositions; `check_clock_values` reduces every literal clock the probes below execute.
`check_iterate_generic` runs `k` rounds out of an arbitrary `qLoop` configuration in exactly
`roundsClock zeros r k` steps, leaving the register holding `v - k` with `r + k` marks;
`check_drain_generic` takes `k := v`, so the register empties and the exhaustion fires, and the
`qDone` endpoint persists; `check_register_drained` does both out of the landed phase-local
`startConfig`.  `check_lane_room` is the room the fence-parameter `F` buys.

The three execution probes below do **not** invoke those execution theorems: each reduces its own
configuration by kernel computation and is a claim about its own input.  `check_drain_probe` drains
a five-digit register holding `3` to `qDone` with three marks; `check_start_iterate_probe` runs two rounds out
of the *actual* `startConfig`; `check_below_room_drain_probe` is the honesty probe for the room
premise -- it completes a drain on a budget where `check_lane_room`'s condition fails, because that
condition reserves the cell an installed cutoff would occupy.  `check_register_drained_instance`
inhabits the capstone's hypotheses and `check_register_drained_literal_endpoint` derives its
endpoint at those literals.

Not here and not available to pin.  The **fence phase**: the lane is still uncapped in the machine,
so a register too large for the budget still runs `qRunEnd` off the tape and sticks, which is a
timeout and so neither verdict; the `qRunEnd`-on-`some false` row stays pinned and unexercised, no
wrapper lays a cutoff cell, and `F = N` is claimed nowhere -- no wrapper instantiates `F` beyond its
own probe's literals.  These are canonical bounded execution lemmas, not execution with an installed
cutoff: an installed `some false` in the lane is not a `loopTape`, and nothing here is evidence that
any wrapper above survives one.  Any **pnp4 bridge**, and with it every connection to
`contentHeader?`, `contentInput?` or a parsed target -- the `24`, `23` and `3` below are hand-written
literals.  A **footprint or budget theorem**, so no room premise is shown necessary.  Every
**converse**, and **first arrival** -- `qDone` absorbs, so every persistence conjunct is persistence
and nothing more.  A malformed-gamma branch, and any restoration of the gamma leading-digit
convention.

The lane holds `v` marks, where `v` is the parameter whose register digits are *hypothesised*:
calling them a target in unary would be a claim about a decoded value, and no wrapper here decodes
anything.  The concrete `startConfig` tests use a retag of an actual prior run; the generic drain
tests supply canonical configurations directly.  Reaching `qDone` proves no raw-input language
acceptance, and the clocks count this phase's steps alone. -/

namespace Pnp3.Tests.UniformV1FixedGammaTargetUnaryCountdownIterationSurfaceTests

open Complexity.Uniform.V1
open Complexity.Uniform.V1.PairEncoding
open Complexity.Uniform.V1.FixedGammaTargetUnaryCountdown
open Complexity.Uniform.V1.FixedGammaTargetUnaryCountdownIteration
open Complexity.Uniform.V1.FixedGammaTargetRegisterDecrement (decBit borrow deadline)

def check_roundsClock (zeros r k : Nat) : Nat := roundsClock zeros r k
def check_drainClock (zeros r v : Nat) : Nat := drainClock zeros r v
def check_fullClock (zeros d v : Nat) : Nat := fullClock zeros d v

/-- The register-width hypothesis in its two interchangeable forms, restated in full.  Pure
arithmetic: no machine, no tape and no decoded value occurs. -/
theorem check_high_iff_lt (v zeros : Nat) :
    (∀ b, zeros < b → v.testBit b = false) ↔ v < 2 ^ (zeros + 1) :=
  high_iff_lt v zeros

/-- The closed forms, the recurrence and the two compositions, restated in full.  Each is an exact
time out of its own configuration; only the drain's endpoint absorbs. -/
theorem check_rounds_clock_pins (zeros r k v d : Nat) :
    roundsClock zeros r k = k * k + k * (2 * zeros + 2 * r + 6) ∧
      roundsClock zeros r 0 = 0 ∧
      roundsClock zeros r 1 = roundClock zeros r ∧
      roundsClock zeros r (k + 1) = roundClock zeros r + roundsClock zeros (r + 1) k ∧
      drainClock zeros r v = roundsClock zeros r v + zeroClock zeros ∧
      fullClock zeros d v = (d + 2) + drainClock zeros 0 v ∧
      fullClock zeros d 1 = firstClock zeros d + zeroClock zeros :=
  rounds_clock_pins zeros r k v d

/-- The lane budget, restated in full.  `F` is an explicit parameter; nothing here instantiates it
and nothing lays a cutoff at `N + 3 + zeros + F`.  Sufficient and used, never shown necessary --
`check_below_room_drain_probe` below completes a drain on a budget where it fails. -/
theorem check_lane_room {a m B zeros r k F : Nat} (hfence : r + k ≤ F)
    (hroom : zeros + 2 + F ≤ a + B) :
    (∀ i, i ≤ k → a + m + 3 + zeros + (r + i) < tapeLength (pairLength a m) B) ∧
      a + m + 2 + zeros < tapeLength (pairLength a m) B :=
  lane_room hfence hroom

/-- Arbitrary iteration out of an arbitrary `qLoop` configuration, restated in full: exactly
`roundsClock zeros r k` steps, the register holding `v - k`, the lane holding `r + k` marks, on the
same canonical `loopTape`.  `k ≤ v` and the width hypothesis are both load-bearing.  `qLoop` does
not absorb, so this is an exact time and not a deadline. -/
theorem check_iterate_generic {a m B zeros F : Nat} (x : Bitstring a) (w : Bitstring m)
    (hroom : zeros + 2 + F ≤ a + B) :
    ∀ k v r : Nat, r + k ≤ F → k ≤ v → (∀ b, zeros < b → v.testBit b = false) →
      ∀ c : Config stateCount (pairLength a m) B, c.state = qLoop →
        c.head.val = a + m + 2 + zeros → c.tape = loopTape B x w zeros v r →
        let e := machine.run (roundsClock zeros r k) c
        e.state = qLoop ∧ e.head.val = a + m + 2 + zeros ∧
          e.tape = loopTape B x w zeros (v - k) (r + k) :=
  iterate_generic x w hroom

/-- The drain, restated in full: exactly `drainClock zeros r v` steps to the absorbing `qDone` on
the separator blank, an all-`false` register and `r + v` marks.  There is no `1 ≤ v` hypothesis.
The last conjunct is persistence, not first arrival. -/
theorem check_drain_generic {a m B zeros v r F : Nat} (x : Bitstring a) (w : Bitstring m)
    (hfence : r + v ≤ F) (hroom : zeros + 2 + F ≤ a + B)
    (hhigh : ∀ b, zeros < b → v.testBit b = false)
    (c : Config stateCount (pairLength a m) B) (hq : c.state = qLoop)
    (hh : c.head.val = a + m + 2 + zeros) (ht : c.tape = loopTape B x w zeros v r) :
    let e := machine.run (drainClock zeros r v) c
    e.state = qDone ∧ e.head.val = a + m + 2 + zeros ∧
      e.tape = loopTape B x w zeros 0 (r + v) ∧
      (∀ t, drainClock zeros r v ≤ t → machine.run t c = e) :=
  drain_generic x w hfence hroom hhigh c hq hh ht

/-- The concrete exact run out of the landed phase-local `startConfig`, restated in full: the entry
at `d + 2` and the whole drain at `fullClock zeros d v`, with the register emptied, exactly `v`
marks in the lane, blanks beyond and the endpoint persisting.  No wrapper supplies the `v`, and no
conjunct decodes the register into a number. -/
theorem check_register_drained {a m B zeros v F : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hfence : v ≤ F) (hroom : zeros + 2 + F ≤ a + B)
    (hv : ∀ j, j ≤ zeros → v.testBit (zeros - j) = decBit x w zeros (borrow x w zeros) j)
    (hhigh : ∀ b, zeros < b → v.testBit b = false) :
    let d := borrow x w zeros
    let c0 := machine.run (d + 2) (startConfig B x w)
    let e := machine.run (fullClock zeros d v) (startConfig B x w)
    c0.state = qLoop ∧ c0.head.val = a + m + 2 + zeros ∧ c0.tape = loopTape B x w zeros v 0 ∧
      e.state = qDone ∧ e.head.val = a + m + 2 + zeros ∧
        e.tape = loopTape B x w zeros 0 v ∧
        (∀ t, fullClock zeros d v ≤ t → machine.run t (startConfig B x w) = e) ∧
        (∀ j, j ≤ zeros → ∀ i : Fin (tapeLength (pairLength a m) B), i.val = a + m + 1 + j →
          e.tape i = some false) ∧
        (∀ i : Fin (tapeLength (pairLength a m) B), a + m + 3 + zeros ≤ i.val →
          i.val < a + m + 3 + zeros + v → e.tape i = some true) ∧
        (∀ i : Fin (tapeLength (pairLength a m) B), a + m + 3 + zeros + v ≤ i.val →
          e.tape i = none) :=
  register_drained x w htag hg hzeros hfence hroom hv hhigh

/-- Every literal clock the probes below execute, reduced by kernel computation, together with the
two compositions at those literals.  `roundsClock 4 0 1` is one round, so it is `roundClock 4 0`. -/
theorem check_clock_values :
    roundsClock 4 0 0 = 0 ∧ roundsClock 4 0 1 = 15 ∧ roundsClock 4 0 1 = roundClock 4 0 ∧
      roundsClock 4 0 2 = 32 ∧ roundsClock 4 0 3 = 51 ∧ roundsClock 4 0 24 = 912 ∧
      drainClock 4 0 3 = 64 ∧ drainClock 0 0 1 = 12 ∧ fullClock 4 0 24 = 927 ∧
      fullClock 4 0 1 = firstClock 4 0 + zeroClock 4 ∧
      fullClock 4 3 1 = firstClock 4 3 + zeroClock 4 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Independent literal reduction probes

These probes deliberately do **not** invoke the execution theorems above: each reduces its own
configuration by kernel computation, and each is a claim about its own input.  The tag is `10110010`
and `physWord` decodes to `zeros = 4` with `N = 17`, so the register `[18,22]` is five digits wide,
the separator blank is `23` and the lane starts at `24`.  `check_start_iterate_probe` identifies the
*actual* phase-local start configuration first, using only the landed G2q endpoint theorem and G2q's
own clock bound, which executes nothing. -/

private def tag : Bitstring 8 := ![true, false, true, true, false, false, true, false]
private def physWord : Bitstring 9 :=
  ![false, false, false, false, true, true, false, false, true]
private def emptyWord : Bitstring 0 := ![]

/-- Rebuild a configuration from its three projections.  Stated over a configuration *variable*, so
that identifying the phase-local start configuration never has to reduce the G2q run term inside
it. -/
private theorem config_of_parts {K n B : Nat} {c : Config K n B} {q : Fin K} {k : Nat}
    {hk : k < tapeLength n B} {T : Fin (tapeLength n B) → Option Bool}
    (hq : c.state = q) (hh : c.head.val = k) (ht : c.tape = T) :
    c = ⟨q, ⟨k, hk⟩, T⟩ := by
  obtain ⟨cs, ch, ct⟩ := c
  cases hq; cases ht
  exact congrArg (fun h => (⟨cs, h, ct⟩ : Config K n B)) (Fin.ext hh)

private theorem phys_handoff (B : Nat) :
    startConfig B tag physWord =
      ⟨qStart, ⟨22, by unfold tapeLength pairLength; omega⟩,
        FixedGammaTargetRegisterDecrement.decTape B tag physWord 4 0⟩ := by
  obtain ⟨-, hh, ht, -, -, -⟩ :=
    FixedGammaTargetRegisterDecrement.register_decremented (B := B) (zeros := 4) tag physWord
      (by decide) (by decide) (by omega) (by unfold tapeLength pairLength; omega)
  obtain ⟨-, -, -, -, -, hclamp⟩ :=
    FixedGammaTargetRegisterDecrement.register_decremented (B := B) (zeros := 4) tag physWord
      (by decide) (by decide) (by omega) (by unfold tapeLength pairLength; omega)
  have hb : borrow tag physWord 4 = 0 := by decide
  have hstart := hclamp (deadline (8 + 9))
    ((FixedGammaTargetRegisterDecrement.clock_pins (8 + 9) 4
      (borrow tag physWord 4)).2.2.2.2 (by omega) (by rw [hb]; omega))
  refine config_of_parts rfl ?_ ?_
  · change (FixedGammaTargetRegisterDecrement.machine.run (deadline (8 + 9))
      (FixedGammaTargetRegisterDecrement.startConfig B tag physWord)).head.val = 22
    rw [hstart, hh, hb]
  · change (FixedGammaTargetRegisterDecrement.machine.run (deadline (8 + 9))
      (FixedGammaTargetRegisterDecrement.startConfig B tag physWord)).tape = _
    rw [hstart, ht, hb]

/-- An explicit `qLoop` configuration on the separator blank `23` of `physWord`'s layout at budget
`B = 1`, with the five register cells `[18,22]` holding the digits `f f f t t` and an empty lane.
It is written out rather than reached by a run: the digits are chosen by hand, and nothing decodes
them. -/
private def drainConfig : Config stateCount (pairLength 8 9) 1 :=
  ⟨qLoop, ⟨23, by decide⟩, loopTape 1 tag physWord 4 3 0⟩

set_option maxRecDepth 1000000 in
/-- **The drain, reduced.**  Three rounds cost `roundsClock 4 0 3 = 51` steps and empty the register
while laying three marks; the exhaustion then costs `zeroClock 4 = 13` more, so `qDone` is on the
separator blank `23` at `drainClock 4 0 3 = 64` with the five register cells `[18,22]` all
`some false`, marks at `24`, `25` and `26` and a blank at `27`.  Step `80` shows `qDone` absorbing,
which is persistence and not a claim that `64` is the first arrival.  The marks are marks: nothing
here reads them as a value. -/
theorem check_drain_probe :
    (machine.run 51 drainConfig).state = qLoop ∧
    (machine.run 51 drainConfig).head.val = 23 ∧
    (machine.run 51 drainConfig).tape ⟨22, by decide⟩ = some false ∧
    (machine.run 51 drainConfig).tape ⟨26, by decide⟩ = some true ∧
    (machine.run 64 drainConfig).state = qDone ∧
    (machine.run 64 drainConfig).head.val = 23 ∧
    (machine.run 64 drainConfig).tape ⟨18, by decide⟩ = some false ∧
    (machine.run 64 drainConfig).tape ⟨19, by decide⟩ = some false ∧
    (machine.run 64 drainConfig).tape ⟨20, by decide⟩ = some false ∧
    (machine.run 64 drainConfig).tape ⟨21, by decide⟩ = some false ∧
    (machine.run 64 drainConfig).tape ⟨22, by decide⟩ = some false ∧
    (machine.run 64 drainConfig).tape ⟨23, by decide⟩ = none ∧
    (machine.run 64 drainConfig).tape ⟨24, by decide⟩ = some true ∧
    (machine.run 64 drainConfig).tape ⟨25, by decide⟩ = some true ∧
    (machine.run 64 drainConfig).tape ⟨26, by decide⟩ = some true ∧
    (machine.run 64 drainConfig).tape ⟨27, by decide⟩ = none ∧
    (machine.run 80 drainConfig).state = qDone ∧
    (machine.run 80 drainConfig).head.val = 23 := by
  repeat' apply And.intro
  all_goals decide

/-- `check_drain_generic`'s hypotheses are satisfiable at `drainConfig`'s literals, so it is not a
statement about an empty premise set: `zeros = 4`, `v = 3`, `r = 0` and `F = 3` meet the lane budget
exactly at `a + B = 9`.  The `3` is supplied by hand. -/
theorem check_drain_generic_instance :
    0 + 3 ≤ 3 ∧ 4 + 2 + 3 ≤ 8 + 1 ∧ (∀ b, 4 < b → (3 : Nat).testBit b = false) ∧
      drainConfig.state = qLoop ∧ drainConfig.head.val = 8 + 9 + 2 + 4 ∧
      drainConfig.tape = loopTape 1 tag physWord 4 3 0 :=
  ⟨by omega, by omega,
    fun b hb => Nat.testBit_lt_two_pow (by
      have h : (2 : Nat) ^ 5 ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hb; omega),
    rfl, rfl, rfl⟩

set_option maxRecDepth 1000000 in
/-- **Two rounds out of the actual `startConfig`.**  `physWord`'s entry offset is `d = 0`, so the
entry costs two steps and `2 + roundsClock 4 0 k` is the cost of `k` rounds after it: at `17` the
lane holds one mark at `24` and at `34` a second at `25`, with a blank at `26` and the head back on
the separator blank `23` both times.  As a bit pattern read from cell `18` the register went
`11000`, `10111`, `10110`; nothing here claims any of those to be a decoded value, and the marks are
marks. -/
theorem check_start_iterate_probe :
    (machine.run 17 (startConfig 0 tag physWord)).state = qLoop ∧
    (machine.run 17 (startConfig 0 tag physWord)).head.val = 23 ∧
    (machine.run 17 (startConfig 0 tag physWord)).tape ⟨24, by decide⟩ = some true ∧
    (machine.run 17 (startConfig 0 tag physWord)).tape ⟨25, by decide⟩ = none ∧
    (machine.run 34 (startConfig 0 tag physWord)).state = qLoop ∧
    (machine.run 34 (startConfig 0 tag physWord)).head.val = 23 ∧
    (machine.run 34 (startConfig 0 tag physWord)).tape ⟨18, by decide⟩ = some true ∧
    (machine.run 34 (startConfig 0 tag physWord)).tape ⟨19, by decide⟩ = some false ∧
    (machine.run 34 (startConfig 0 tag physWord)).tape ⟨20, by decide⟩ = some true ∧
    (machine.run 34 (startConfig 0 tag physWord)).tape ⟨21, by decide⟩ = some true ∧
    (machine.run 34 (startConfig 0 tag physWord)).tape ⟨22, by decide⟩ = some false ∧
    (machine.run 34 (startConfig 0 tag physWord)).tape ⟨23, by decide⟩ = none ∧
    (machine.run 34 (startConfig 0 tag physWord)).tape ⟨24, by decide⟩ = some true ∧
    (machine.run 34 (startConfig 0 tag physWord)).tape ⟨25, by decide⟩ = some true ∧
    (machine.run 34 (startConfig 0 tag physWord)).tape ⟨26, by decide⟩ = none := by
  rw [phys_handoff 0]
  repeat' apply And.intro
  all_goals decide

/-- An explicit `qLoop` configuration in the smallest layout there is: `a = m = zeros = 0`, budget
`B = 2`, one register cell `1` holding `some true`, the separator blank at `2` and an empty lane at
`3`. -/
private def tinyConfig : Config stateCount (pairLength 0 0) 2 :=
  ⟨qLoop, ⟨2, by decide⟩, loopTape 2 emptyWord emptyWord 0 1 0⟩

set_option maxRecDepth 1000000 in
/-- **The room premise is sufficient, not necessary.**  At `v = F = 1` and `zeros = 0` the lane
budget `zeros + 2 + F ≤ a + B` reads `3 ≤ 2` and **fails**, because it reserves the cell at
`N + 3 + zeros + F` that an installed cutoff would occupy.  The canonical unfenced drain completes
on this tape all the same: `drainClock 0 0 1 = 12` steps reach `qDone` on the separator blank `2`
with the register cell `1` cleared and one mark at `3`.  So no theorem above may be read as showing
its room premise necessary, and none claims to; this probe reduces one configuration and claims
nothing beyond it. -/
theorem check_below_room_drain_probe :
    ¬ (0 + 2 + 1 ≤ 0 + 2) ∧
    (machine.run 12 tinyConfig).state = qDone ∧
    (machine.run 12 tinyConfig).head.val = 2 ∧
    (machine.run 12 tinyConfig).tape ⟨1, by decide⟩ = some false ∧
    (machine.run 12 tinyConfig).tape ⟨2, by decide⟩ = none ∧
    (machine.run 12 tinyConfig).tape ⟨3, by decide⟩ = some true ∧
    (machine.run 20 tinyConfig).state = qDone := by
  refine ⟨by omega, ?_⟩
  repeat' apply And.intro
  all_goals decide

/-- `check_register_drained`'s hypotheses are satisfiable, so it is not a statement about an empty
premise set: behind the matching tag `physWord` decodes to `zeros = 4`, its five decremented
register digits are the bits of `24`, and `F = 24` with `B = 22` meets the lane budget exactly at
`a + B = 30`.  The literal `24` is supplied **by hand**, chosen to match the digits; no theorem of
this slice or of pnp3 produces it from a parse, which is exactly the deferred pnp4 step.  Nothing
here calls the marks a target in unary. -/
theorem check_register_drained_instance :
    FixedContentTagGate.tagMatches (Fin.append tag physWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag physWord) = some 4 ∧
      2 ≤ 4 ∧ 24 ≤ 24 ∧ 4 + 2 + 24 ≤ 8 + 22 ∧
      (∀ j, j ≤ 4 → (24 : Nat).testBit (4 - j) = decBit tag physWord 4 (borrow tag physWord 4) j) ∧
      (∀ b, 4 < b → (24 : Nat).testBit b = false) :=
  ⟨by decide, by decide, by omega, by omega, by omega,
    fun j hj => by interval_cases j <;> decide,
    fun b hb => Nat.testBit_lt_two_pow (by
      have h : (2 : Nat) ^ 5 ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hb; omega)⟩

/-- The capstone's endpoint at those literals, derived from `register_drained` rather than reduced:
out of the actual `startConfig 22 tag physWord` the machine is in `qDone` on the separator blank `23`
after exactly `fullClock 4 0 24 = 927` steps with the register emptied and twenty-four marks in the
lane, and that endpoint persists.  The `24` is the hand-written literal of
`check_register_drained_instance`; nothing decodes it, and the lane holds `24` marks rather than a
target in unary. -/
theorem check_register_drained_literal_endpoint :
    let e := machine.run (fullClock 4 0 24) (startConfig 22 tag physWord)
    e.state = qDone ∧ e.head.val = 23 ∧ e.tape = loopTape 22 tag physWord 4 0 24 ∧
      (∀ t, fullClock 4 0 24 ≤ t → machine.run t (startConfig 22 tag physWord) = e) := by
  have hb : borrow tag physWord 4 = 0 := by decide
  obtain ⟨-, -, -, h1, h2, h3, h4, -, -, -⟩ :=
    register_drained (a := 8) (m := 9) (B := 22) (zeros := 4) (v := 24) (F := 24) tag physWord
      (by decide) (by decide) (by omega) (by omega) (by omega)
      (fun j hj => by interval_cases j <;> decide)
      (fun b hb => Nat.testBit_lt_two_pow (by
        have h : (2 : Nat) ^ 5 ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hb; omega))
  rw [hb] at h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end Pnp3.Tests.UniformV1FixedGammaTargetUnaryCountdownIterationSurfaceTests
