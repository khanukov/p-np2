import Complexity.Uniform.V1.FixedPairTagRemovalShiftAlignmentCountdown
namespace Pnp3.Tests.UniformV1FixedPairTagRemovalShiftAlignmentCountdownSurfaceTests
open Complexity.Uniform.V1
open PairEncoding
open FixedPairTagRemovalShiftAlignmentCountdown
open FixedContentGammaTerminator (gammaZeros?)
open FixedGammaPayloadDispatcherFirstArrival (StrictFirstTerminalAt first_true_strict_first_terminal)
open FixedGammaTargetRegisterDecrement (borrow decBit)
open FixedGammaTargetUnaryCountdown (loopTape)

/-! Infrastructure surfaces: tiny runs reduce independently; the large fixture is theorem-derived.
No first arrival of composed accept, raw-input execution, or language acceptance is asserted. -/
private def emptyWord : Bitstring 0 := fun i => i.elim0
set_option maxRecDepth 4000000 in
theorem check_empty_two_step_probe :
    (machine.run 1 (startConfig 0 emptyWord emptyWord)).state.val = 1 ∧
    (machine.run 1 (startConfig 0 emptyWord emptyWord)).head.val = 0 ∧
    (machine.run 2 (startConfig 0 emptyWord emptyWord)).state.val = 9 ∧
    (machine.run 2 (startConfig 0 emptyWord emptyWord)).head.val = 0 ∧
    List.ofFn (machine.run 2 (startConfig 0 emptyWord emptyWord)).tape = [none, some true] := by
  repeat' apply And.intro
  all_goals decide

theorem check_leftMachine : leftMachine = FixedPairTagRemoval.machine := rfl
theorem check_tailMachine : tailMachine = FixedPairOriginShiftAlignmentCountdown.machine := rfl
theorem check_tailStartConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    tailStartConfig B x w = FixedPairOriginShiftAlignmentCountdown.startConfig B x w := rfl
theorem check_machine : machine = leftMachine.seq tailMachine := rfl
theorem check_inRemoval (q : Fin leftMachine.stateCount) :
    inRemoval q = leftMachine.seqLeft tailMachine q := rfl
theorem check_inTail (q : Fin tailMachine.stateCount) :
    inTail q = leftMachine.seqRight tailMachine q := rfl
theorem check_route (q : Fin leftMachine.stateCount) :
    route q = leftMachine.seqRoute tailMachine q := rfl
theorem check_tailStart : tailStart = inTail tailMachine.start := rfl
theorem check_startConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    startConfig B x w = leftMachine.seqEmbedRouted tailMachine
      (FixedPairTagRemoval.startConfig B x w) := rfl
theorem check_switchTime (a : Nat) : switchTime a = a * (a + 5) + 2 := rfl
theorem check_removalChainClock (C a m zeros d v : Nat) :
    removalChainClock C a m zeros d v = switchTime a +
      FixedPairOriginShiftAlignmentCountdown.shiftChainClock C a m zeros d v := rfl

theorem check_table_and_resource_pins :
    machine.stateCount = 193 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 579 ∧
    machine.start.val = 0 ∧ machine.accept.val = 191 ∧
    machine.reject.val = 192 ∧ tailStart.val = 9 ∧
    (∀ q, (inRemoval q).val = q.val) ∧
    (∀ q, (inTail q).val = 9 + q.val) ∧
    Function.Injective inRemoval ∧ Function.Injective inTail ∧
    (∀ p q, inRemoval p ≠ inTail q) ∧
    (∀ q, (∃ p, q = inRemoval p) ∨ (∃ p, q = inTail p)) ∧
    (∀ q s,
      machine.step (inRemoval q) s =
        (route (leftMachine.step q s).1,
          (leftMachine.step q s).2.1,
          (leftMachine.step q s).2.2)) ∧
    (∀ q s,
      machine.step (inTail q) s =
        (inTail (tailMachine.step q s).1,
          (tailMachine.step q s).2.1,
          (tailMachine.step q s).2.2)) :=
  table_and_resource_pins

theorem check_accept_rows_unique
    (q : Fin leftMachine.stateCount) (s : Option Bool)
    (ha : q ≠ leftMachine.accept) :
    (leftMachine.rawStep q s).1 = leftMachine.accept ↔
      q.val = 1 ∧ s = none :=
  accept_rows_unique q s ha

theorem check_reject_rows_unique
    (q : Fin leftMachine.stateCount) (s : Option Bool)
    (ha : q ≠ leftMachine.accept)
    (hr : q ≠ leftMachine.reject) :
    (leftMachine.rawStep q s).1 = leftMachine.reject ↔
      (s ≠ none ∧ (q.val = 0 ∨ q.val = 4 ∨ q.val = 5)) ∨
      (q.val = 6 ∧ s = some true) :=
  reject_rows_unique q s ha hr

theorem check_tail_start_at_first_arrival {a m B : Nat}
    (x : Bitstring a) (w : Bitstring m) :
    let g := leftMachine.run (switchTime a)
      (FixedPairTagRemoval.startConfig B x w)
    g = FixedPairTagRemoval.finalConfig B x w ∧
      tailStartConfig B x w = ⟨tailMachine.start, g.head, g.tape⟩ :=
  tail_start_at_first_arrival x w

theorem check_handoff_exact {a m B : Nat}
    (x : Bitstring a) (w : Bitstring m) :
    let cR := FixedPairTagRemoval.startConfig B x w
    let c := startConfig B x w
    (∀ t, t < switchTime a → (machine.run t c).state.val < 9) ∧
    (∀ t, t ≤ switchTime a →
      (machine.run t c).state ≠ machine.accept ∧
      (machine.run t c).state ≠ machine.reject) ∧
    (∀ t, t ≤ switchTime a →
      machine.run t c =
        leftMachine.seqEmbedRouted tailMachine (leftMachine.run t cR)) ∧
    machine.run (switchTime a) c =
      leftMachine.seqEmbedRight tailMachine (tailStartConfig B x w) ∧
    (machine.run (switchTime a) c).state.val = 9 ∧
    (machine.run (switchTime a) c).head.val = 0 ∧
    (machine.run (switchTime a) c).tape =
      FixedPairTagRemoval.compactTape B x w ∧
    (∀ s, machine.run (switchTime a + s) c =
      leftMachine.seqEmbedRight tailMachine
        (tailMachine.run s (tailStartConfig B x w))) :=
  handoff_exact x w

theorem check_tag_removal_countdown_drained
    {a m B C zeros v F : Nat}
    {q : Fin FixedGammaPayloadDispatcher.stateCount}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : gammaZeros? (Fin.append x w) = some zeros)
    (h : StrictFirstTerminalAt B x w C q)
    (hzeros : 2 ≤ zeros)
    (hfence : v ≤ F)
    (hroom : zeros + 2 + F ≤ a + B)
    (hv : ∀ j, j ≤ zeros →
      v.testBit (zeros - j) =
        decBit x w zeros (borrow x w zeros) j)
    (hhigh : ∀ b, zeros < b → v.testBit b = false) :
    let D := removalChainClock C a m zeros (borrow x w zeros) v
    let e := machine.run D (startConfig B x w)
    e.state = machine.accept ∧
    e.head.val = a + m + 2 + zeros ∧
    e.tape = loopTape B x w zeros 0 v ∧
    (∀ t, D ≤ t → machine.run t (startConfig B x w) = e) :=
  tag_removal_countdown_drained x w htag hg h hzeros hfence hroom hv hhigh

set_option maxRecDepth 4000000 in
/-- Independent whole-tape probes at both budgets, including the blank fetch before H4. -/
theorem check_empty_unit_probe :
    (machine.run 1 (startConfig 1 emptyWord emptyWord)).state.val = 1 ∧
    (machine.run 1 (startConfig 1 emptyWord emptyWord)).head.val = 0 ∧
    List.ofFn (machine.run 1 (startConfig 1 emptyWord emptyWord)).tape = [none, some true, none] ∧
    (machine.run 2 (startConfig 1 emptyWord emptyWord)).state.val = 9 ∧
    (machine.run 2 (startConfig 1 emptyWord emptyWord)).head.val = 0 ∧
    List.ofFn (machine.run 2 (startConfig 1 emptyWord emptyWord)).tape = [none, some true, none] ∧
    (machine.run 1 (startConfig 0 emptyWord emptyWord)).tape ⟨0, by decide⟩ = none := by
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 4000000 in
/-- Both singleton bit values, with empty and nonempty witnesses, including zero budget. -/
theorem check_singleton_probes :
    ∀ b c : Bool, ∀ B : Fin 2,
      let x : Bitstring 1 := ![b]
      let w : Bitstring 1 := ![c]
      (machine.run 8 (startConfig B.val x emptyWord)).state.val = 9 ∧
      (machine.run 8 (startConfig B.val x emptyWord)).head.val = 0 ∧
      (machine.run 8 (startConfig B.val x emptyWord)).tape =
        FixedPairTagRemoval.compactTape B.val x emptyWord ∧
      (machine.run 8 (startConfig B.val x w)).state.val = 9 ∧
      (machine.run 8 (startConfig B.val x w)).head.val = 0 ∧
      (machine.run 8 (startConfig B.val x w)).tape = FixedPairTagRemoval.compactTape B.val x w := by
  decide

/-- The origin clamp precedes H4's stationary row; these are separate transitions. -/
theorem check_origin_clamp {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    (let c := leftMachine.run (switchTime a - 2) (FixedPairTagRemoval.startConfig B x w)
     c.head.val = 0 ∧ (leftMachine.step c.state (c.tape c.head)).2.2 = .left) ∧
    machine.step (inRemoval ⟨1, by decide⟩) none = (tailStart, none, .stay) :=
  ⟨(FixedPairTagRemoval.boundary_clamps x w).2.2, by decide⟩

/-- Universal suffix transport locates H5, H6 and H7, preserving the H6 head and whole tape. -/
theorem check_inherited_switches {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    (machine.run (switchTime a + FixedPairOriginShiftAlignmentCountdown.switchTime a m)
      (startConfig B x w)).state.val = 16 ∧
    (let e := machine.run (switchTime a + (FixedPairOriginShiftAlignmentCountdown.switchTime a m +
          FixedPairOriginShiftAlignmentCountdown.tailSwitchTime a m)) (startConfig B x w)
     e.state.val = 42 ∧ e.head.val = 0 ∧ e.tape = FixedPairOriginAlignment.alignedTape B x w) ∧
    (machine.run (switchTime a + (FixedPairOriginShiftAlignmentCountdown.switchTime a m +
        (FixedPairOriginShiftAlignmentCountdown.tailSwitchTime a m + (a + m + 3))))
      (startConfig B x w)).state.val = 46 := by
  obtain ⟨-, -, -, -, -, -, -, hs⟩ := handoff_exact (B := B) x w
  have h5 := (FixedPairOriginShiftAlignmentCountdown.handoff_exact (B := B) x w).2.2.2.1
  obtain ⟨h6, -, -, hh, ht, -, -, h7⟩ :=
    FixedPairOriginShiftAlignmentCountdown.inherited_alignment_switch (B := B) x w
  refine ⟨?_, ?_, ?_⟩
  · rw [hs, h5]; rfl
  · dsimp only
    rw [hs]
    exact ⟨congrArg (9 + ·) h6, hh, ht⟩
  · rw [hs]
    exact congrArg (9 + ·) h7

/-- Forward rejection transport only; mismatch keeps the inherited deadline guarantee. -/
theorem check_rejection_transport {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    (FixedContentTagGate.tagMatches (Fin.append x w) = true →
      gammaZeros? (Fin.append x w) = none →
      ∀ s, FixedPairOriginShiftAlignmentCountdown.switchTime a m +
        (FixedPairOriginShiftAlignmentCountdown.tailSwitchTime a m +
          (a + m + 3 + (3 * (a + m) + 7 + FixedContentGammaTerminator.deadline a m))) ≤ s →
        (machine.run (switchTime a + s) (startConfig B x w)).state = machine.reject ∧
        (machine.run (switchTime a + s) (startConfig B x w)).head.val = a + m ∧
        (machine.run (switchTime a + s) (startConfig B x w)).tape =
          FixedPairContentMarkerErase.contentTape B x w) ∧
    (FixedContentTagGate.tagMatches (Fin.append x w) = false →
      ∀ s, FixedPairOriginShiftAlignmentCountdown.switchTime a m +
        (FixedPairOriginShiftAlignmentCountdown.tailSwitchTime a m +
          (a + m + 3 + (3 * (a + m) + 7))) ≤ s →
        (machine.run (switchTime a + s) (startConfig B x w)).state = machine.reject ∧
        (machine.run (switchTime a + s) (startConfig B x w)).head =
          (FixedContentTagGate.finalConfig B x w).head ∧
        (machine.run (switchTime a + s) (startConfig B x w)).tape =
          FixedPairContentMarkerErase.contentTape B x w) := by
  obtain ⟨-, -, -, -, -, -, -, hs⟩ := handoff_exact (B := B) x w
  constructor
  · intro htag hg s hle
    obtain ⟨hr, hh, ht⟩ :=
      (FixedPairOriginShiftAlignmentCountdown.malformed_reject_handoff x w htag hg).2 s hle
    rw [hs]
    exact ⟨congrArg (leftMachine.seqRight tailMachine) hr, hh, ht⟩
  · intro htag s hle
    obtain ⟨hr, hh, ht⟩ :=
      FixedPairOriginShiftAlignmentCountdown.mismatched_tag_reject_handoff x w htag s hle
    rw [hs]
    exact ⟨congrArg (leftMachine.seqRight tailMachine) hr, hh, ht⟩

private def tag : Bitstring 8 := ![true, false, true, true, false, false, true, false]
private def physWord : Bitstring 9 :=
  ![false, false, false, false, true, true, false, false, true]

/-- Literal clocks: the new prefix costs 106 and leaves G3m's 2866 unchanged. -/
theorem check_clock_values : switchTime 0 = 2 ∧ switchTime 1 = 8 ∧ switchTime 8 = 106 ∧
    FixedPairOriginShiftAlignmentCountdown.shiftChainClock 18 8 9 4 0 24 = 2866 ∧
    removalChainClock 18 8 9 4 0 24 = 2972 ∧ (2972 : Nat) = 106 + 2866 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 40000 in
/-- Derived execution nonvacuity with hand-supplied v = 24; all eight premises discharged.
This is neither ContentAccepts nonvacuity nor first arrival of composed accept. -/
theorem check_drained_literal_endpoint :
    let e := machine.run 2972 (startConfig 22 tag physWord)
    e.state = machine.accept ∧ e.state.val = 191 ∧ e.head.val = 23 ∧
      e.tape = loopTape 22 tag physWord 4 0 24 ∧
      (∀ t, 2972 ≤ t → machine.run t (startConfig 22 tag physWord) = e) := by
  have hb : borrow tag physWord 4 = 0 := by decide
  have hc : removalChainClock (3 * 4 + 6) 8 9 4 0 24 = 2972 := rfl
  obtain ⟨h1, h2, h3, h4⟩ :=
    tag_removal_countdown_drained
      (a := 8) (m := 9) (B := 22) (C := 3 * 4 + 6) (zeros := 4) (v := 24) (F := 24) tag physWord
      (by decide) (by decide)
      (first_true_strict_first_terminal (zeros := 4) tag physWord (by decide) (by decide)
        (by omega) (by decide) (by decide)).1
      (by omega) (by omega) (by omega)
      (fun j hj => by interval_cases j <;> decide)
      (fun b hb => Nat.testBit_lt_two_pow (by
        have h : (2 : Nat) ^ 5 ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hb; omega))
  rw [hb] at h1 h2 h3 h4
  rw [hc] at h1 h2 h3 h4
  refine ⟨h1, ?_, h2, h3, h4⟩
  rw [h1]; decide

end Pnp3.Tests.UniformV1FixedPairTagRemovalShiftAlignmentCountdownSurfaceTests
