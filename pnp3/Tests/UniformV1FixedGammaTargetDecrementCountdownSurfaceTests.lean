import Complexity.Uniform.V1.FixedGammaTargetDecrementCountdown

/-!
Surface pins for the Part A G2x concrete half: G2q's decrement and G2s-a's countdown as **one**
closed 18-state, 54-row table with the routed edge `qBorrow`-on-`some true` → countdown `qStart`
as its executed handoff.  Every public declaration is restated in full; `check_clock_values`
reduces the literal clocks the probes use: `decClock 17 4 0 = 18`, `fullClock 4 0 24 = 927`,
`composedClock 17 4 0 24 = 945`.

The probes.  The tag is `10110010` and `physWord` decodes to `zeros = 4` with `N = 17`: the
register `[18,22]` holds the digits `1 1 0 0 1` of `25`, the separator blank is `23`, the lane
starts at `24`; the literal `24` is supplied **by hand** and no theorem of pnp3 produces it from a
parse.  `check_handoff_literal` and `check_decrement_countdown_literal_endpoint` are **derived**
from `handoff_exact` and `decrement_countdown_drained` at those literals: the switch at step `18`
into the countdown's actual `startConfig 22 tag physWord`, and the composed accept at step `945`
with the register emptied and twenty-four marks laid, persisting.  `check_handoff_probe` is the
**independent** reduction: `phys_start` identifies the composed `startConfig 0 tag physWord` with an
explicit configuration using only the landed G2p-f endpoint theorem and G2q's prior bound, which
executes nothing, and kernel computation then reads back G2q's `qBorrow` on the digit `22` at step
`17`, the countdown's `qStart` on that same cell — now `some false` — at step `18`, and `qLoop` on
the separator `23` with one mark at `24` at step `35`, which is step `17` of G2u's
`check_start_iterate_probe` shifted by the `18` steps G2q takes.

Not here: the composed `startConfig` still embeds every earlier phase as a retag, so no raw-input
run and no earlier handoff is executed or pinned; no first arrival of the composed accept; no
fence, so an oversized register still times out; no rejecting run; no converse; no footprint
theorem, so every room premise is sufficient and used, never shown necessary; and no `accepts`,
`AcceptsAt`, `DecidesWithin`, `UniformP` or language-membership statement. -/

namespace Pnp3.Tests.UniformV1FixedGammaTargetDecrementCountdownSurfaceTests

open Complexity.Uniform.V1
open Complexity.Uniform.V1.PairEncoding
open Complexity.Uniform.V1.FixedGammaTargetDecrementCountdown
open Complexity.Uniform.V1.FixedGammaTargetRegisterDecrement (decClock deadline borrow decBit)
open Complexity.Uniform.V1.FixedGammaTargetUnaryCountdown (loopTape)
open Complexity.Uniform.V1.FixedGammaTargetUnaryCountdownIteration (fullClock)

def check_machine : UniformTM := machine
def check_inDecrement :
    Fin FixedGammaTargetRegisterDecrement.stateCount → Fin machine.stateCount := inDecrement
def check_inCountdown :
    Fin FixedGammaTargetUnaryCountdown.stateCount → Fin machine.stateCount := inCountdown
def check_route : Fin FixedGammaTargetRegisterDecrement.stateCount → Fin machine.stateCount := route
def check_startConfig {a m : Nat} :
    (B : Nat) → Bitstring a → Bitstring m → Config machine.stateCount (pairLength a m) B :=
  startConfig
def check_composedClock (N zeros d v : Nat) : Nat := composedClock N zeros d v

/-- The composed table, restated in full. -/
theorem check_table_and_resource_pins :
    machine.stateCount = 18 ∧
      Fintype.card (Fin machine.stateCount × Option Bool) = 54 ∧
      machine.start = inDecrement FixedGammaTargetRegisterDecrement.qStart ∧
      machine.accept = inCountdown FixedGammaTargetUnaryCountdown.qDone ∧
      machine.reject = inCountdown FixedGammaTargetUnaryCountdown.qReject ∧
      machine.start.val = 0 ∧ machine.accept.val = 16 ∧ machine.reject.val = 17 ∧
      (∀ q, (inDecrement q).val = q.val) ∧ (∀ q, (inCountdown q).val = 7 + q.val) ∧
      Function.Injective inDecrement ∧ Function.Injective inCountdown ∧
      (∀ p q, inDecrement p ≠ inCountdown q) ∧
      route FixedGammaTargetRegisterDecrement.qDone =
        inCountdown FixedGammaTargetUnaryCountdown.qStart ∧
      route FixedGammaTargetRegisterDecrement.qReject = machine.reject ∧
      (∀ q, q ≠ FixedGammaTargetRegisterDecrement.qDone →
        q ≠ FixedGammaTargetRegisterDecrement.qReject → route q = inDecrement q) ∧
      (∀ q s, machine.step (inDecrement q) s =
        (route (FixedGammaTargetRegisterDecrement.machine.step q s).1,
          (FixedGammaTargetRegisterDecrement.machine.step q s).2.1,
          (FixedGammaTargetRegisterDecrement.machine.step q s).2.2)) ∧
      (∀ q s, machine.step (inCountdown q) s =
        (inCountdown (FixedGammaTargetUnaryCountdown.machine.step q s).1,
          (FixedGammaTargetUnaryCountdown.machine.step q s).2.1,
          (FixedGammaTargetUnaryCountdown.machine.step q s).2.2)) ∧
      machine.step (inDecrement FixedGammaTargetRegisterDecrement.qBorrow) (some true) =
        (inCountdown FixedGammaTargetUnaryCountdown.qStart, some false, .stay) :=
  table_and_resource_pins

/-- Budget independence, restated in full. -/
theorem check_per_step_budget_independent : ∀ q s, machine.step q s = machine.rawStep q s :=
  per_step_budget_independent

/-- The start, restated in full: G2q's `startConfig` routed into the composed control. -/
theorem check_handoff_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let p := FixedGammaTargetRegisterDecrement.startConfig B x w
    let c := startConfig B x w
    c = FixedGammaTargetRegisterDecrement.machine.seqEmbedRouted
        FixedGammaTargetUnaryCountdown.machine p ∧
      c.state = machine.start ∧ c.head = p.head ∧ c.tape = p.tape :=
  handoff_pins x w

/-- The composed clock, restated in full. -/
theorem check_clock_pins (N zeros d v : Nat) :
    composedClock N zeros d v = decClock N zeros d + fullClock zeros d v ∧
      composedClock N zeros d v =
        (N + zeros + d - 3) + (d + v * v + v * (2 * zeros + 6) + 2 * zeros + 7) ∧
      (9 + zeros ≤ N → d ≤ zeros →
        composedClock N zeros d v ≤ deadline N + fullClock zeros d v) :=
  clock_pins N zeros d v

/-- The executed handoff, restated in full. -/
theorem check_handoff_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hroom : a + m + 2 + zeros < tapeLength (pairLength a m) B) :
    let T := decClock (a + m) zeros (borrow x w zeros)
    let c := startConfig B x w
    (∀ t, t < T →
        (machine.run t c).state ≠ machine.accept ∧ (machine.run t c).state ≠ machine.reject) ∧
      (∀ t, t ≤ T → machine.run t c =
        FixedGammaTargetRegisterDecrement.machine.seqEmbedRouted
          FixedGammaTargetUnaryCountdown.machine
          (FixedGammaTargetRegisterDecrement.machine.run t
            (FixedGammaTargetRegisterDecrement.startConfig B x w))) ∧
      machine.run T c =
        FixedGammaTargetRegisterDecrement.machine.seqEmbedRight
          FixedGammaTargetUnaryCountdown.machine
          (FixedGammaTargetUnaryCountdown.startConfig B x w) ∧
      (∀ s, machine.run (T + s) c =
        FixedGammaTargetRegisterDecrement.machine.seqEmbedRight
          FixedGammaTargetUnaryCountdown.machine
          (FixedGammaTargetUnaryCountdown.machine.run s
            (FixedGammaTargetUnaryCountdown.startConfig B x w))) :=
  handoff_exact x w htag hg hzeros hroom

/-- The composed exact run, restated in full.  No wrapper supplies the `v`. -/
theorem check_decrement_countdown_drained {a m B zeros v F : Nat} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 2 ≤ zeros) (hfence : v ≤ F) (hroom : zeros + 2 + F ≤ a + B)
    (hv : ∀ j, j ≤ zeros → v.testBit (zeros - j) = decBit x w zeros (borrow x w zeros) j)
    (hhigh : ∀ b, zeros < b → v.testBit b = false) :
    let d := borrow x w zeros
    let C := composedClock (a + m) zeros d v
    let e := machine.run C (startConfig B x w)
    e.state = machine.accept ∧ e.head.val = a + m + 2 + zeros ∧
      e.tape = loopTape B x w zeros 0 v ∧
      (∀ t, C ≤ t → machine.run t (startConfig B x w) = e) ∧
      (∀ j, j ≤ zeros → ∀ i : Fin (tapeLength (pairLength a m) B), i.val = a + m + 1 + j →
        e.tape i = some false) ∧
      (∀ i : Fin (tapeLength (pairLength a m) B), a + m + 3 + zeros ≤ i.val →
        i.val < a + m + 3 + zeros + v → e.tape i = some true) ∧
      (∀ i : Fin (tapeLength (pairLength a m) B), a + m + 3 + zeros + v ≤ i.val →
        e.tape i = none) :=
  decrement_countdown_drained x w htag hg hzeros hfence hroom hv hhigh

/-- The literal clocks the probes use, reduced by kernel computation. -/
theorem check_clock_values :
    decClock 17 4 0 = 18 ∧ fullClock 4 0 24 = 927 ∧ composedClock 17 4 0 24 = 945 ∧
      composedClock 17 4 0 24 = decClock 17 4 0 + fullClock 4 0 24 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### The physical fixture -/

private def tag : Bitstring 8 := ![true, false, true, true, false, false, true, false]
private def physWord : Bitstring 9 :=
  ![false, false, false, false, true, true, false, false, true]

/-- `decrement_countdown_drained`'s seven hypotheses are satisfiable at the fixture: `zeros = 4`,
the decremented digits are the bits of `24`, and `F = 24`, `B = 22` meet the lane budget exactly.
The `24` is supplied by hand. -/
theorem check_decrement_countdown_instance :
    FixedContentTagGate.tagMatches (Fin.append tag physWord) = true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append tag physWord) = some 4 ∧
      2 ≤ 4 ∧ 24 ≤ 24 ∧ 4 + 2 + 24 ≤ 8 + 22 ∧
      (∀ j, j ≤ 4 → (24 : Nat).testBit (4 - j) = decBit tag physWord 4 (borrow tag physWord 4) j) ∧
      (∀ b, 4 < b → (24 : Nat).testBit b = false) :=
  ⟨by decide, by decide, by omega, by omega, by omega,
    fun j hj => by interval_cases j <;> decide,
    fun b hb => Nat.testBit_lt_two_pow (by
      have h : (2 : Nat) ^ 5 ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hb; omega)⟩

/-- The handoff at the fixture, derived from `handoff_exact` rather than reduced: no composed verdict
before step `18`, and at step `18` the countdown's actual `startConfig 22 tag physWord`,
re-embedded. -/
theorem check_handoff_literal :
    (∀ t, t < 18 → (machine.run t (startConfig 22 tag physWord)).state ≠ machine.accept ∧
      (machine.run t (startConfig 22 tag physWord)).state ≠ machine.reject) ∧
    machine.run 18 (startConfig 22 tag physWord) =
      FixedGammaTargetRegisterDecrement.machine.seqEmbedRight
        FixedGammaTargetUnaryCountdown.machine
        (FixedGammaTargetUnaryCountdown.startConfig 22 tag physWord) := by
  have hb : borrow tag physWord 4 = 0 := by decide
  obtain ⟨h1, -, h2, -⟩ := handoff_exact (B := 22) (zeros := 4) tag physWord (by decide)
    (by decide) (by omega) (by unfold tapeLength pairLength; omega)
  rw [hb] at h1 h2
  exact ⟨h1, h2⟩

/-- The composed endpoint at the fixture, derived rather than reduced: the composed accept on the
separator blank `23` after exactly `composedClock 17 4 0 24 = 945` steps — `18` for the decrement,
none for the handoff, `927` for the countdown — with the register emptied and twenty-four marks
laid, persisting.  Nothing decodes the hand-written `24`. -/
theorem check_decrement_countdown_literal_endpoint :
    let e := machine.run (composedClock (8 + 9) 4 0 24) (startConfig 22 tag physWord)
    e.state = machine.accept ∧ e.head.val = 23 ∧ e.tape = loopTape 22 tag physWord 4 0 24 ∧
      (∀ t, composedClock (8 + 9) 4 0 24 ≤ t → machine.run t (startConfig 22 tag physWord) = e) := by
  have hb : borrow tag physWord 4 = 0 := by decide
  obtain ⟨h1, h2, h3, h4, -, -, -⟩ :=
    decrement_countdown_drained (a := 8) (m := 9) (B := 22) (zeros := 4) (v := 24) (F := 24) tag
      physWord (by decide) (by decide) (by omega) (by omega) (by omega)
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

/-- The composed `startConfig B tag physWord`: the composed start on the tag cell `7` over the G2p-f
finish tape.  Only the landed G2p-f endpoint theorem and G2q's prior bound are used. -/
private theorem phys_start (B : Nat) :
    startConfig B tag physWord =
      ⟨route FixedGammaTargetRegisterDecrement.qStart, ⟨7, by unfold tapeLength pairLength; omega⟩,
        FixedGammaTargetPayloadExhaustion.finishTape B tag physWord 4⟩ := by
  obtain ⟨-, hfh, hft, -, -, -, hprior⟩ :=
    FixedGammaTargetPayloadExhaustion.payload_exhausted (B := B) (zeros := 4) tag physWord
      (by decide) (by decide) (by omega) (by unfold tapeLength pairLength; omega)
  have hstart := hprior _
    (FixedGammaTargetRegisterDecrement.prior_covers (N := 8 + 9) (zeros := 4) (by omega))
  refine config_of_parts rfl ?_ ?_
  · change (FixedGammaTargetPayloadRound.machine.run
      (FixedGammaTargetRegisterDecrement.priorDeadline (8 + 9))
      (FixedGammaTargetPayloadRound.startConfig B tag physWord)).head.val = 7
    rw [hstart, hfh]
  · change (FixedGammaTargetPayloadRound.machine.run
      (FixedGammaTargetRegisterDecrement.priorDeadline (8 + 9))
      (FixedGammaTargetPayloadRound.startConfig B tag physWord)).tape = _
    rw [hstart, hft]

set_option maxRecDepth 1000000 in
/-- **The handoff, reduced.**  Out of the actual composed `startConfig 0 tag physWord`: at step `17`
G2q's `qBorrow` (index `4`) on the digit `22`, still `some true`; at step `18` the countdown's
`qStart` (index `7`) on that cell, now `some false` — the routed handoff row took the machine across,
in that one transition; at step `35`, after the entry and one round, `qLoop` (index `9`) on the
separator `23` with one mark at `24` and a blank at `25`.  The mark is a mark. -/
theorem check_handoff_probe :
    (machine.run 17 (startConfig 0 tag physWord)).state.val = 4 ∧
    (machine.run 17 (startConfig 0 tag physWord)).head.val = 22 ∧
    (machine.run 17 (startConfig 0 tag physWord)).tape ⟨22, by decide⟩ = some true ∧
    (machine.run 18 (startConfig 0 tag physWord)).state.val = 7 ∧
    (machine.run 18 (startConfig 0 tag physWord)).head.val = 22 ∧
    (machine.run 18 (startConfig 0 tag physWord)).tape ⟨22, by decide⟩ = some false ∧
    (machine.run 35 (startConfig 0 tag physWord)).state.val = 9 ∧
    (machine.run 35 (startConfig 0 tag physWord)).head.val = 23 ∧
    (machine.run 35 (startConfig 0 tag physWord)).tape ⟨23, by decide⟩ = none ∧
    (machine.run 35 (startConfig 0 tag physWord)).tape ⟨24, by decide⟩ = some true ∧
    (machine.run 35 (startConfig 0 tag physWord)).tape ⟨25, by decide⟩ = none := by
  rw [phys_start 0]
  repeat' apply And.intro
  all_goals decide

end Pnp3.Tests.UniformV1FixedGammaTargetDecrementCountdownSurfaceTests
