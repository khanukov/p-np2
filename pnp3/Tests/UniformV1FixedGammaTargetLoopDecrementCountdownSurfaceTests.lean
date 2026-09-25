import Complexity.Uniform.V1.FixedGammaTargetLoopDecrementCountdown

/-!
Surface pins for the Part A G2y concrete slice: G2p-d's payload round and G2x's
decrement-and-countdown composite as **one** closed 40-state, 120-row table, with the routed edge
`qFin`-on-`some false` → G2x's `qStart` (composed index `19` → `22`) as its newly executed handoff
H16 and G2x's `qBorrow`-on-`some true` (composed index `26` → `29`) inherited as H17.  Every public
declaration is restated in full; `check_clock_values` reduces the literal clocks the probes use:
`totalClock 17 4 = 64`, `decClock 17 4 0 = 18`, `fullClock 4 0 24 = 927`,
`composedClock 17 4 0 24 = 945`, `chainClock 17 4 0 24 = 1009`.

The probes.  The tag is `10110010` and `physWord` decodes to `zeros = 4` with `N = 17`: the register
`[18,22]` holds the digits `1 1 0 0 1` of `25`, the separator blank is `23`, the lane starts at `24`;
the literal `24` is supplied **by hand** and no theorem of pnp3 produces it from a parse.
`check_loop_handoff_instance` and `check_loop_drained_instance` inhabit the four and the seven
hypotheses at their own budgets — `B = 0` for the handoff, `B = 22` for the complete run, where
`4 + 2 + 24 = 8 + 22` meets the lane budget exactly — so budget `0` is never presented as validating
the 1009-step drain.  `check_handoff_literal` and `check_loop_decrement_countdown_literal_endpoint`
are **derived** from `handoff_exact` and `loop_decrement_countdown_drained` at those literals: no
composed verdict before step `64` and G2x's actual `startConfig 0 tag physWord` re-embedded at step
`64`; and the composed accept at step `1009 = 64 + 18 + 927` with the register emptied and
twenty-four marks laid, persisting.  `check_handoff_probe` is the **independent** reduction:
`phys_start` identifies the composed `startConfig 0 tag physWord` with an explicit configuration
using only G2p-d's landed foundation endpoint theorem, which executes nothing, and kernel
computation then reads back the loop's `qFin` (index `19`) on the tag cell `7` at step `63`, G2q's
`qStart` (index `22`) on that same cell at step `64` — the H16 row took the machine across the first
block boundary in that one transition — G2q's `qBorrow` (index `26`) on the digit `22` at step `81`,
and the countdown's `qStart` (index `29`) on that cell, now `some false`, at step `82`: the H17 row,
in the same reduction.

Not here: the composed `startConfig` still embeds every earlier phase as a retag, so no raw-input run
and none of the fifteen earlier handoffs is executed or pinned; no first arrival of the composed
accept — the first arrival proved is the payload loop's, inside the left block; no fence, so an
oversized register still times out; no rejecting run; no converse; no footprint theorem, so every
room premise is sufficient and used, never shown necessary; and no `accepts`, `AcceptsAt`,
`DecidesWithin`, `UniformP` or language-membership statement. -/

namespace Pnp3.Tests.UniformV1FixedGammaTargetLoopDecrementCountdownSurfaceTests

open Complexity.Uniform.V1
open Complexity.Uniform.V1.PairEncoding
open Complexity.Uniform.V1.FixedGammaTargetLoopDecrementCountdown
open Complexity.Uniform.V1.FixedGammaTargetPayloadExhaustion (totalClock)
open Complexity.Uniform.V1.FixedGammaTargetDecrementCountdown (composedClock)
open Complexity.Uniform.V1.FixedGammaTargetRegisterDecrement (decClock borrow decBit)
open Complexity.Uniform.V1.FixedGammaTargetUnaryCountdown (loopTape)
open Complexity.Uniform.V1.FixedGammaTargetUnaryCountdownIteration (fullClock)

def check_machine : UniformTM := machine
def check_inLoop :
    Fin FixedGammaTargetPayloadRound.stateCount → Fin machine.stateCount := inLoop
def check_inTail :
    Fin FixedGammaTargetDecrementCountdown.machine.stateCount → Fin machine.stateCount := inTail
def check_route : Fin FixedGammaTargetPayloadRound.stateCount → Fin machine.stateCount := route
def check_startConfig {a m : Nat} :
    (B : Nat) → Bitstring a → Bitstring m → Config machine.stateCount (pairLength a m) B :=
  startConfig
def check_chainClock (N zeros d v : Nat) : Nat := chainClock N zeros d v

/-- The composed table, restated in full. -/
theorem check_table_and_resource_pins :
    machine.stateCount = 40 ∧
      Fintype.card (Fin machine.stateCount × Option Bool) = 120 ∧
      machine.start = route FixedGammaTargetPayloadRound.qLoop ∧
      machine.start = inLoop FixedGammaTargetPayloadRound.qLoop ∧
      machine.accept = inTail FixedGammaTargetDecrementCountdown.machine.accept ∧
      machine.reject = inTail FixedGammaTargetDecrementCountdown.machine.reject ∧
      machine.start.val = 0 ∧ machine.accept.val = 38 ∧ machine.reject.val = 39 ∧
      (∀ q, (inLoop q).val = q.val) ∧ (∀ q, (inLoop q).val < 22) ∧
      (∀ q, (inTail q).val = 22 + q.val) ∧ (∀ q, 22 ≤ (inTail q).val) ∧
      (∀ q, (inTail (FixedGammaTargetDecrementCountdown.inDecrement q)).val = 22 + q.val) ∧
      (∀ q, (inTail (FixedGammaTargetDecrementCountdown.inCountdown q)).val = 29 + q.val) ∧
      Function.Injective inLoop ∧ Function.Injective inTail ∧
      (∀ p q, inLoop p ≠ inTail q) ∧
      route FixedGammaTargetPayloadRound.qDone =
        inTail FixedGammaTargetDecrementCountdown.machine.start ∧
      route FixedGammaTargetPayloadRound.qReject = machine.reject ∧
      (∀ q, q ≠ FixedGammaTargetPayloadRound.qDone → q ≠ FixedGammaTargetPayloadRound.qReject →
        route q = inLoop q) ∧
      (∀ q s, machine.step (inLoop q) s =
        (route (FixedGammaTargetPayloadRound.machine.step q s).1,
          (FixedGammaTargetPayloadRound.machine.step q s).2.1,
          (FixedGammaTargetPayloadRound.machine.step q s).2.2)) ∧
      (∀ q s, machine.step (inTail q) s =
        (inTail (FixedGammaTargetDecrementCountdown.machine.step q s).1,
          (FixedGammaTargetDecrementCountdown.machine.step q s).2.1,
          (FixedGammaTargetDecrementCountdown.machine.step q s).2.2)) ∧
      (∀ q s, machine.step q s = machine.rawStep q s) ∧
      (inLoop FixedGammaTargetPayloadRound.qFin).val = 19 ∧
      (inTail FixedGammaTargetDecrementCountdown.machine.start).val = 22 ∧
      machine.step (inLoop FixedGammaTargetPayloadRound.qFin) (some false) =
        (inTail FixedGammaTargetDecrementCountdown.machine.start, some false, .stay) ∧
      (inTail (FixedGammaTargetDecrementCountdown.inDecrement
        FixedGammaTargetRegisterDecrement.qBorrow)).val = 26 ∧
      (inTail (FixedGammaTargetDecrementCountdown.inCountdown
        FixedGammaTargetUnaryCountdown.qStart)).val = 29 ∧
      machine.step (inTail (FixedGammaTargetDecrementCountdown.inDecrement
          FixedGammaTargetRegisterDecrement.qBorrow)) (some true) =
        (inTail (FixedGammaTargetDecrementCountdown.inCountdown
          FixedGammaTargetUnaryCountdown.qStart), some false, .stay) ∧
      (∀ N zeros d v, chainClock N zeros d v = totalClock N zeros + composedClock N zeros d v) :=
  table_and_resource_pins

/-- The start, restated in full: the payload round's `startConfig` routed into the composed
control. -/
theorem check_handoff_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let p := FixedGammaTargetPayloadRound.startConfig B x w
    let c := startConfig B x w
    c = FixedGammaTargetPayloadRound.machine.seqEmbedRouted
        FixedGammaTargetDecrementCountdown.machine p ∧
      c.state = machine.start ∧ c.head = p.head ∧ c.tape = p.tape :=
  handoff_pins x w

/-- The payload loop's first arrival, restated in full. -/
theorem check_loop_strict {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hroom : a + m + 1 + zeros < tapeLength (pairLength a m) B) :
    ∀ t, t < totalClock (a + m) zeros →
      (FixedGammaTargetPayloadRound.machine.run t
        (FixedGammaTargetPayloadRound.startConfig B x w)).state ≠
          FixedGammaTargetPayloadRound.qDone :=
  loop_strict x w htag hg hzeros hroom

/-- The executed handoff H16, restated in full. -/
theorem check_handoff_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hroom : a + m + 1 + zeros < tapeLength (pairLength a m) B) :
    let T := totalClock (a + m) zeros
    let c := startConfig B x w
    (∀ t, t < T →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ t, t ≤ T → machine.run t c =
        FixedGammaTargetPayloadRound.machine.seqEmbedRouted
          FixedGammaTargetDecrementCountdown.machine
          (FixedGammaTargetPayloadRound.machine.run t
            (FixedGammaTargetPayloadRound.startConfig B x w))) ∧
      machine.run T c =
        FixedGammaTargetPayloadRound.machine.seqEmbedRight
          FixedGammaTargetDecrementCountdown.machine
          (FixedGammaTargetDecrementCountdown.startConfig B x w) ∧
      (∀ s, machine.run (T + s) c =
        FixedGammaTargetPayloadRound.machine.seqEmbedRight
          FixedGammaTargetDecrementCountdown.machine
          (FixedGammaTargetDecrementCountdown.machine.run s
            (FixedGammaTargetDecrementCountdown.startConfig B x w))) :=
  handoff_exact x w htag hg hzeros hroom

/-- The composed exact run, restated in full.  No wrapper supplies the `v`. -/
theorem check_loop_decrement_countdown_drained {a m B zeros v F : Nat} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hfence : v ≤ F) (hroom : zeros + 2 + F ≤ a + B)
    (hv : ∀ j, j ≤ zeros → v.testBit (zeros - j) = decBit x w zeros (borrow x w zeros) j)
    (hhigh : ∀ b, zeros < b → v.testBit b = false) :
    let d := borrow x w zeros
    let C := chainClock (a + m) zeros d v
    let e := machine.run C (startConfig B x w)
    e.state = machine.accept ∧ e.head.val = a + m + 2 + zeros ∧
      e.tape = loopTape B x w zeros 0 v ∧
      (∀ t, C ≤ t → machine.run t (startConfig B x w) = e) :=
  loop_decrement_countdown_drained x w htag hg hzeros hfence hroom hv hhigh

/-- The literal clocks the probes use, reduced by kernel computation: the loop's first arrival, the
decrement, the countdown drain, G2x's sum and this slice's sum. -/
theorem check_clock_values :
    totalClock 17 4 = 64 ∧ decClock 17 4 0 = 18 ∧ fullClock 4 0 24 = 927 ∧
      composedClock 17 4 0 24 = 945 ∧ chainClock 17 4 0 24 = 1009 ∧
      chainClock 17 4 0 24 = totalClock 17 4 + composedClock 17 4 0 24 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### The physical fixture -/

private def tag : Bitstring 8 := ![true, false, true, true, false, false, true, false]
private def physWord : Bitstring 9 :=
  ![false, false, false, false, true, true, false, false, true]

/-- `handoff_exact`'s four hypotheses are satisfiable at the fixture, at the *probe's* budget
`B = 0`: the tag matches, the word decodes to `zeros = 4`, and the loop's room `22 < 27` holds. -/
theorem check_loop_handoff_instance :
    FixedContentTagGate.tagMatches (Fin.append tag physWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag physWord) = some 4 ∧
      2 ≤ 4 ∧ 8 + 9 + 1 + 4 < tapeLength (pairLength 8 9) 0 :=
  ⟨by decide, by decide, by omega, by decide⟩

/-- `loop_decrement_countdown_drained`'s seven hypotheses are satisfiable at the fixture, at the
*drain's* budget `B = 22`: `zeros = 4`, the decremented digits are the bits of `24`, and `F = 24`,
`B = 22` meet the lane budget exactly.  The `24` is supplied by hand. -/
theorem check_loop_drained_instance :
    FixedContentTagGate.tagMatches (Fin.append tag physWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag physWord) = some 4 ∧
      2 ≤ 4 ∧ 24 ≤ 24 ∧ 4 + 2 + 24 ≤ 8 + 22 ∧
      (∀ j, j ≤ 4 → (24 : Nat).testBit (4 - j) = decBit tag physWord 4 (borrow tag physWord 4) j) ∧
      (∀ b, 4 < b → (24 : Nat).testBit b = false) :=
  ⟨by decide, by decide, by omega, by omega, by omega,
    fun j hj => by interval_cases j <;> decide,
    fun b hb => Nat.testBit_lt_two_pow (by
      have h : (2 : Nat) ^ 5 ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hb; omega)⟩

/-- H16 at the fixture, derived from `handoff_exact` rather than reduced: no composed verdict before
step `64`, and at step `64` G2x's actual `startConfig 0 tag physWord`, re-embedded. -/
theorem check_handoff_literal :
    (∀ t, t < 64 → (machine.run t (startConfig 0 tag physWord)).state ≠ machine.accept ∧
      (machine.run t (startConfig 0 tag physWord)).state ≠ machine.reject) ∧
    machine.run 64 (startConfig 0 tag physWord) =
      FixedGammaTargetPayloadRound.machine.seqEmbedRight
        FixedGammaTargetDecrementCountdown.machine
        (FixedGammaTargetDecrementCountdown.startConfig 0 tag physWord) := by
  obtain ⟨h1, -, h2, -⟩ := handoff_exact (B := 0) (zeros := 4) tag physWord (by decide)
    (by decide) (by omega) (by decide)
  exact ⟨h1, h2⟩

/-- The composed endpoint at the fixture, derived rather than reduced: the composed accept on the
separator blank `23` after exactly `chainClock 17 4 0 24 = 1009` steps — `64` for the payload loop,
none for H16, `18` for the decrement, none for H17, `927` for the countdown — with the register
emptied and twenty-four marks laid, persisting.  Nothing decodes the hand-written `24`. -/
theorem check_loop_decrement_countdown_literal_endpoint :
    let e := machine.run (chainClock (8 + 9) 4 0 24) (startConfig 22 tag physWord)
    e.state = machine.accept ∧ e.head.val = 23 ∧ e.tape = loopTape 22 tag physWord 4 0 24 ∧
      (∀ t, chainClock (8 + 9) 4 0 24 ≤ t →
        machine.run t (startConfig 22 tag physWord) = e) := by
  have hb : borrow tag physWord 4 = 0 := by decide
  obtain ⟨h1, h2, h3, h4⟩ :=
    loop_decrement_countdown_drained (a := 8) (m := 9) (B := 22) (zeros := 4) (v := 24) (F := 24)
      tag physWord (by decide) (by decide) (by omega) (by omega) (by omega)
      (fun j hj => by interval_cases j <;> decide)
      (fun b hb => Nat.testBit_lt_two_pow (by
        have h : (2 : Nat) ^ 5 ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hb; omega))
  rw [hb] at h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

/-! ### Independent literal reduction probe -/

/-- Rebuild a configuration from its projections, over a configuration *variable*. -/
private theorem config_of_parts {K n B : Nat} {c : Config K n B} {q : Fin K} {k : Nat}
    {hk : k < tapeLength n B} {T : Fin (tapeLength n B) → Option Bool}
    (hq : c.state = q) (hh : c.head.val = k) (ht : c.tape = T) : c = ⟨q, ⟨k, hk⟩, T⟩ :=
  Config.ext_parts hq (Fin.ext hh) ht

/-- The composed `startConfig B tag physWord`: the composed start on the walking terminator `14`
over the `r = 2` loop invariant.  Only G2p-d's landed foundation endpoint theorem is used, and it
executes nothing. -/
private theorem phys_start (B : Nat) :
    startConfig B tag physWord =
      ⟨route FixedGammaTargetPayloadRound.qLoop,
        ⟨14, by unfold tapeLength pairLength; omega⟩,
        FixedGammaTargetPayloadLoopFoundation.loopTape B tag physWord 4 2⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTargetPayloadLoopFoundation.markers_at_deadline
    (B := B) (zeros := 4) tag physWord (by decide) (by decide) (by decide)
    (by unfold tapeLength pairLength; omega)
  config_of_parts rfl (hh.trans (by decide)) ht

set_option maxRecDepth 1000000 in
/-- **Both handoffs, reduced.**  Out of the actual composed `startConfig 0 tag physWord`: at step
`63` the payload loop's `qFin` (index `19`) on the tag cell `7`; at step `64` G2q's `qStart` (index
`22`) on that same cell, which the loop restored to `some false` — the H16 row took the machine
across the first block boundary in that one transition; at step `81` G2q's `qBorrow` (index `26`) on
the register digit `22`, still `some true`; and at step `82` the countdown's `qStart` (index `29`)
on that cell, now `some false` — the H17 row, in the same reduction.  Steps `63`/`64` are the ones
this slice adds; `81`/`82` are G2x's, shifted by the `64` steps the loop takes. -/
theorem check_handoff_probe :
    (machine.run 63 (startConfig 0 tag physWord)).state.val = 19 ∧
    (machine.run 63 (startConfig 0 tag physWord)).head.val = 7 ∧
    (machine.run 64 (startConfig 0 tag physWord)).state.val = 22 ∧
    (machine.run 64 (startConfig 0 tag physWord)).head.val = 7 ∧
    (machine.run 64 (startConfig 0 tag physWord)).tape ⟨7, by decide⟩ = some false ∧
    (machine.run 81 (startConfig 0 tag physWord)).state.val = 26 ∧
    (machine.run 81 (startConfig 0 tag physWord)).head.val = 22 ∧
    (machine.run 81 (startConfig 0 tag physWord)).tape ⟨22, by decide⟩ = some true ∧
    (machine.run 82 (startConfig 0 tag physWord)).state.val = 29 ∧
    (machine.run 82 (startConfig 0 tag physWord)).head.val = 22 ∧
    (machine.run 82 (startConfig 0 tag physWord)).tape ⟨22, by decide⟩ = some false := by
  rw [phys_start 0]
  repeat' apply And.intro
  all_goals decide

end Pnp3.Tests.UniformV1FixedGammaTargetLoopDecrementCountdownSurfaceTests
