import Complexity.Uniform.V1.FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown
namespace Pnp3.Tests.UniformV1FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdownSurfaceTests
open Complexity.Uniform.V1
open PairEncoding
open FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown
open FixedContentGammaTerminator (gammaZeros?)
open FixedGammaPayloadDispatcherFirstArrival (StrictFirstTerminalAt first_true_strict_first_terminal)
open FixedGammaTargetRegisterDecrement (borrow decBit)
open FixedGammaTargetUnaryCountdown (loopTape)

/-! Infrastructure only. Full propositions below freeze every public contract.
Tiny probes reduce independently; the large execution witness is theorem-derived. -/
theorem check_leftMachine : leftMachine = FixedPairSeparatorHole.machine := rfl
theorem check_tailMachine : tailMachine = FixedPairTagRemovalShiftAlignmentCountdown.machine := rfl
theorem check_tailStartConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    tailStartConfig B x w = FixedPairTagRemovalShiftAlignmentCountdown.startConfig B x w := rfl
theorem check_machine : machine = leftMachine.seq tailMachine := rfl
theorem check_inHole (q : Fin leftMachine.stateCount) :
    inHole q = leftMachine.seqLeft tailMachine q := rfl
theorem check_inTail (q : Fin tailMachine.stateCount) :
    inTail q = leftMachine.seqRight tailMachine q := rfl
theorem check_route (q : Fin leftMachine.stateCount) :
    route q = leftMachine.seqRoute tailMachine q := rfl
theorem check_tailStart : tailStart = inTail tailMachine.start := rfl
theorem check_startConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    startConfig B x w = leftMachine.seqEmbedRouted tailMachine
      (FixedPairSeparatorHole.startConfig B x w) := rfl
theorem check_switchTime : switchTime = 1 := rfl
theorem check_holeChainClock (C a m zeros d v : Nat) :
    holeChainClock C a m zeros d v = switchTime +
      FixedPairTagRemovalShiftAlignmentCountdown.removalChainClock C a m zeros d v := rfl

theorem check_tail_start_at_first_arrival {a m B : Nat}
    (x : Bitstring a) (w : Bitstring m) :
    let g := leftMachine.run switchTime
      (FixedPairSeparatorHole.startConfig B x w)
    g = FixedPairSeparatorHole.finalConfig B x w ∧
      tailStartConfig B x w = ⟨tailMachine.start, g.head, g.tape⟩ :=
  tail_start_at_first_arrival x w

theorem check_hole_first_arrival {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    (∀ t, t < switchTime →
      (leftMachine.run t (FixedPairSeparatorHole.startConfig B x w)).state ≠ leftMachine.accept ∧
      (leftMachine.run t (FixedPairSeparatorHole.startConfig B x w)).state ≠ leftMachine.reject) ∧
    (leftMachine.run switchTime (FixedPairSeparatorHole.startConfig B x w)).state =
      leftMachine.accept ∧
    (∀ t, (leftMachine.run t (FixedPairSeparatorHole.startConfig B x w)).state ≠
      leftMachine.reject) :=
  hole_first_arrival x w

theorem check_suffix {a m B : Nat} (x : Bitstring a) (w : Bitstring m) (s : Nat) :
    machine.run (1 + s) (startConfig B x w) =
      leftMachine.seqEmbedRight tailMachine (tailMachine.run s (tailStartConfig B x w)) :=
  suffix x w s

theorem check_table_and_resource_pins :
    machine.stateCount = 196 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 588 ∧
    machine.start.val = 0 ∧ machine.accept.val = 194 ∧
    machine.reject.val = 195 ∧ tailStart.val = 3 ∧
    (∀ q, (inHole q).val = q.val) ∧
    (∀ q, (inTail q).val = 3 + q.val) ∧
    Function.Injective inHole ∧ Function.Injective inTail ∧
    (∀ p q, inHole p ≠ inTail q) ∧
    (∀ q, (∃ p, q = inHole p) ∨ (∃ p, q = inTail p)) ∧
    (∀ q s,
      machine.step (inHole q) s =
        (route (leftMachine.step q s).1,
          (leftMachine.step q s).2.1,
          (leftMachine.step q s).2.2)) ∧
    (∀ q s,
      machine.step (inTail q) s =
        (inTail (tailMachine.step q s).1,
          (tailMachine.step q s).2.1,
          (tailMachine.step q s).2.2)) :=
  table_and_resource_pins

theorem check_accept_rows_unique (q : Fin leftMachine.stateCount) (s : Option Bool)
    (ha : q ≠ leftMachine.accept) :
    (leftMachine.rawStep q s).1 = leftMachine.accept ↔
      q = FixedPairSeparatorHole.qStart ∧ s = some true :=
  accept_rows_unique q s ha

theorem check_reject_rows_unique (q : Fin leftMachine.stateCount) (s : Option Bool)
    (ha : q ≠ leftMachine.accept) (hr : q ≠ leftMachine.reject) :
    (leftMachine.rawStep q s).1 = leftMachine.reject ↔
      q = FixedPairSeparatorHole.qStart ∧ s ≠ some true :=
  reject_rows_unique q s ha hr

theorem check_handoff_exact {a m B : Nat}
    (x : Bitstring a) (w : Bitstring m) :
    let cR := FixedPairSeparatorHole.startConfig B x w
    let c := startConfig B x w
    (∀ t, t < switchTime → (machine.run t c).state.val < 3) ∧
    (∀ t, t ≤ switchTime →
      (machine.run t c).state ≠ machine.accept ∧
      (machine.run t c).state ≠ machine.reject) ∧
    (∀ t, t ≤ switchTime →
      machine.run t c =
        leftMachine.seqEmbedRouted tailMachine (leftMachine.run t cR)) ∧
    machine.run switchTime c =
      leftMachine.seqEmbedRight tailMachine (tailStartConfig B x w) ∧
    (machine.run switchTime c).state.val = 3 ∧
    (machine.run switchTime c).head.val = 2 * a ∧
    (machine.run switchTime c).tape =
      FixedPairSeparatorHole.holeTape B x w ∧
    (∀ s, machine.run (switchTime + s) c =
      leftMachine.seqEmbedRight tailMachine
        (tailMachine.run s (tailStartConfig B x w))) :=
  handoff_exact x w

theorem check_separator_hole_countdown_drained
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
    let D := holeChainClock C a m zeros (borrow x w zeros) v
    let e := machine.run D (startConfig B x w)
    e.state = machine.accept ∧
    e.head.val = a + m + 2 + zeros ∧
    e.tape = loopTape B x w zeros 0 v ∧
    (∀ t, D ≤ t → machine.run t (startConfig B x w) = e) :=
  separator_hole_countdown_drained x w htag hg h hzeros hfence hroom hv hhigh

theorem check_entry_pins {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    pairLength a m = 2 * a + 1 + m ∧
    tapeLength (pairLength a m) B = 2 * a + m + B + 2 ∧
    (startConfig B x w).state.val = 0 ∧
    (startConfig B x w).head.val = 2 * a ∧
    (startConfig B x w).tape = FixedPairConcatSentinel.sentinelTape B (encodePair x w) ∧
    (startConfig B x w).tape (startConfig B x w).head = some true :=
  entry_pins x w

theorem check_left_rows :
    machine.step (inHole FixedPairSeparatorHole.qStart) none = (machine.reject, none, .stay) ∧
    machine.step (inHole FixedPairSeparatorHole.qStart) (some false) =
      (machine.reject, some false, .stay) ∧
    machine.step (inHole FixedPairSeparatorHole.qStart) (some true) = (tailStart, none, .stay) ∧
    (∀ s, machine.step (inHole leftMachine.accept) s = (tailStart, s, .stay)) ∧
    (∀ s, machine.step (inHole leftMachine.reject) s = (machine.reject, s, .stay)) ∧
    machine.step ⟨4, by decide⟩ none = (⟨12, by decide⟩, none, .stay) :=
  left_rows

theorem check_step_eq_rawStep (q : Fin machine.stateCount) (s : Option Bool) :
    machine.step q s = machine.rawStep q s :=
  step_eq_rawStep q s

theorem check_dead_left_verdicts :
    machine.start.val ≠ 1 ∧ machine.start.val ≠ 2 ∧
    (∀ q s, (machine.step q s).1.val ≠ 1 ∧ (machine.step q s).1.val ≠ 2) :=
  dead_left_verdicts

theorem check_h3_stationary {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    (machine.step (startConfig B x w).state
      ((startConfig B x w).tape (startConfig B x w).head)).2.2 = .stay :=
  h3_stationary x w

theorem check_scanned_reject {N B : Nat} (cH : Config leftMachine.stateCount N B)
    (hstate : cH.state = FixedPairSeparatorHole.qStart)
    (hread : cH.tape cH.head ≠ some true) (s : Nat) :
    machine.run (1 + s) (leftMachine.seqEmbedRouted tailMachine cH) =
      ⟨machine.reject, cH.head, cH.tape⟩ :=
  scanned_reject cH hstate hread s

theorem check_inherited_h4 {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let e := machine.run (1 + FixedPairTagRemoval.clock a) (startConfig B x w)
    e = leftMachine.seqEmbedRight tailMachine
      (FixedPairTagRemovalShiftAlignmentCountdown.leftMachine.seqEmbedRight
        FixedPairTagRemovalShiftAlignmentCountdown.tailMachine
        (FixedPairOriginShiftAlignmentCountdown.startConfig B x w)) ∧
    e.state.val = 12 ∧ e.head.val = 0 ∧ e.tape = FixedPairTagRemoval.compactTape B x w :=
  inherited_h4 x w

theorem check_inherited_switches {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    (machine.run (1 + (FixedPairTagRemoval.clock a + FixedPairOriginShiftAlignmentCountdown.switchTime a m))
      (startConfig B x w)).state.val = 19 ∧
    (let e := machine.run (1 + (FixedPairTagRemoval.clock a + (FixedPairOriginShiftAlignmentCountdown.switchTime a m +
          FixedPairOriginShiftAlignmentCountdown.tailSwitchTime a m))) (startConfig B x w)
     e.state.val = 45 ∧ e.head.val = 0 ∧ e.tape = FixedPairOriginAlignment.alignedTape B x w) ∧
    (machine.run (1 + (FixedPairTagRemoval.clock a + (FixedPairOriginShiftAlignmentCountdown.switchTime a m +
        (FixedPairOriginShiftAlignmentCountdown.tailSwitchTime a m + (a + m + 3)))))
      (startConfig B x w)).state.val = 49 :=
  inherited_switches x w

theorem check_inherited_origin_clamp {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let c := machine.run (1 + (FixedPairTagRemoval.clock a - 2)) (startConfig B x w)
    c.head.val = 0 ∧ (machine.step c.state (c.tape c.head)).2.2 = .left :=
  inherited_origin_clamp x w

theorem check_rejection_transport {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    (FixedContentTagGate.tagMatches (Fin.append x w) = true →
      gammaZeros? (Fin.append x w) = none →
      ∀ s, FixedPairOriginShiftAlignmentCountdown.switchTime a m +
        (FixedPairOriginShiftAlignmentCountdown.tailSwitchTime a m +
          (a + m + 3 + (3 * (a + m) + 7 + FixedContentGammaTerminator.deadline a m))) ≤ s →
        (machine.run (1 + (FixedPairTagRemoval.clock a + s)) (startConfig B x w)).state = machine.reject ∧
        (machine.run (1 + (FixedPairTagRemoval.clock a + s)) (startConfig B x w)).head.val = a + m ∧
        (machine.run (1 + (FixedPairTagRemoval.clock a + s)) (startConfig B x w)).tape =
          FixedPairContentMarkerErase.contentTape B x w) ∧
    (FixedContentTagGate.tagMatches (Fin.append x w) = false →
      ∀ s, FixedPairOriginShiftAlignmentCountdown.switchTime a m +
        (FixedPairOriginShiftAlignmentCountdown.tailSwitchTime a m +
          (a + m + 3 + (3 * (a + m) + 7))) ≤ s →
        (machine.run (1 + (FixedPairTagRemoval.clock a + s)) (startConfig B x w)).state = machine.reject ∧
        (machine.run (1 + (FixedPairTagRemoval.clock a + s)) (startConfig B x w)).head =
          (FixedContentTagGate.finalConfig B x w).head ∧
        (machine.run (1 + (FixedPairTagRemoval.clock a + s)) (startConfig B x w)).tape =
          FixedPairContentMarkerErase.contentTape B x w) :=
  rejection_transport x w

private def emptyWord : Bitstring 0 := fun i => i.elim0

set_option maxRecDepth 4000000 in
/-- Empty pair at both budgets: entire initial and post-H3 tapes, then inherited H4. -/
theorem check_empty_probes :
    ∀ B : Fin 2,
      List.ofFn (startConfig B.val emptyWord emptyWord).tape =
        [some true, some true] ++ List.replicate B.val none ∧
      (machine.run 1 (startConfig B.val emptyWord emptyWord)).state.val = 3 ∧
      (machine.run 1 (startConfig B.val emptyWord emptyWord)).head.val = 0 ∧
      List.ofFn (machine.run 1 (startConfig B.val emptyWord emptyWord)).tape =
        [none, some true] ++ List.replicate B.val none ∧
      (machine.run 3 (startConfig B.val emptyWord emptyWord)).state.val = 12 ∧
      (machine.run 3 (startConfig B.val emptyWord emptyWord)).head.val = 0 ∧
      (machine.run 3 (startConfig B.val emptyWord emptyWord)).tape =
        FixedPairTagRemoval.compactTape B.val emptyWord emptyWord := by
  decide

set_option maxRecDepth 4000000 in
/-- Both query bits, both singleton witness bits and empty witnesses, budgets zero and one. -/
theorem check_singleton_probes :
    ∀ b c : Bool, ∀ B : Fin 2,
      let x : Bitstring 1 := ![b]
      let w : Bitstring 1 := ![c]
      (machine.run 1 (startConfig B.val x emptyWord)).state.val = 3 ∧
      (machine.run 1 (startConfig B.val x emptyWord)).head.val = 2 ∧
      (machine.run 1 (startConfig B.val x emptyWord)).tape =
        FixedPairSeparatorHole.holeTape B.val x emptyWord ∧
      (machine.run 1 (startConfig B.val x w)).state.val = 3 ∧
      (machine.run 1 (startConfig B.val x w)).head.val = 2 ∧
      (machine.run 1 (startConfig B.val x w)).tape = FixedPairSeparatorHole.holeTape B.val x w ∧
      (machine.run 9 (startConfig B.val x emptyWord)).state.val = 12 ∧
      (machine.run 9 (startConfig B.val x emptyWord)).head.val = 0 ∧
      (machine.run 9 (startConfig B.val x emptyWord)).tape =
        FixedPairTagRemoval.compactTape B.val x emptyWord ∧
      (machine.run 9 (startConfig B.val x w)).state.val = 12 ∧
      (machine.run 9 (startConfig B.val x w)).head.val = 0 ∧
      (machine.run 9 (startConfig B.val x w)).tape = FixedPairTagRemoval.compactTape B.val x w := by
  decide

private def badConfig (s : Option Bool) : Config leftMachine.stateCount 1 0 :=
  ⟨FixedPairSeparatorHole.qStart, ⟨1, by decide⟩, ![some true, s]⟩

set_option maxRecDepth 4000000 in
/-- Independent one-step reductions on each bad symbol, with a nonzero head and complete tape. -/
theorem check_bad_symbol_probes :
    ∀ b : Bool,
      let cH := badConfig (if b then none else some false)
      let e := machine.run 1 (leftMachine.seqEmbedRouted tailMachine cH)
      e.state.val = 195 ∧ e.head = cH.head ∧ e.tape = cH.tape := by
  decide

theorem check_bad_symbol_persistence (b : Bool) (s : Nat) :
    let cH := badConfig (if b then none else some false)
    machine.run (1 + s) (leftMachine.seqEmbedRouted tailMachine cH) =
      ⟨machine.reject, cH.head, cH.tape⟩ := by
  apply scanned_reject _ rfl
  cases b <;> decide

/-- Literal inherited clocks and the new one-step prefix. -/
theorem check_clock_values : switchTime = 1 ∧
    FixedPairTagRemoval.clock 0 = 2 ∧ FixedPairTagRemoval.clock 1 = 8 ∧
    FixedPairTagRemoval.clock 8 = 106 ∧
    FixedPairTagRemovalShiftAlignmentCountdown.removalChainClock 18 8 9 4 0 24 = 2972 ∧
    holeChainClock 18 8 9 4 0 24 = 2973 ∧ (2973 : Nat) = 1 + 2972 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private def tag : Bitstring 8 := ![true, false, true, true, false, false, true, false]
private def physWord : Bitstring 9 :=
  ![false, false, false, false, true, true, false, false, true]

/-- Small layout reduction, independent of the 2973-step run. Whole-function tape
identity in the drain theorem remains the authoritative execution endpoint. -/
theorem check_witness_layout :
    tapeLength (pairLength 8 9) 22 = 49 ∧ borrow tag physWord 4 = 0 ∧
    (∀ i : Fin 49, 18 ≤ i.val → i.val ≤ 22 → loopTape 22 tag physWord 4 0 24 i = some false) ∧
    loopTape 22 tag physWord 4 0 24 ⟨23, by decide⟩ = none ∧
    (∀ i : Fin 49, 24 ≤ i.val → i.val ≤ 47 → loopTape 22 tag physWord 4 0 24 i = some true) ∧
    loopTape 22 tag physWord 4 0 24 ⟨48, by decide⟩ = none := by
  decide

/-- Even the empty phase-local entry differs from a raw initial configuration. -/
theorem check_raw_entry_counterexample :
    List.ofFn (initialConfig machine 0 (encodePair emptyWord emptyWord)).tape = [some true, none] ∧
    List.ofFn (startConfig 0 emptyWord emptyWord).tape = [some true, some true] := by
  decide

set_option maxRecDepth 40000 in
/-- Derived execution nonvacuity with hand-supplied v = 24; all eight premises discharged.
This is neither ContentAccepts nonvacuity nor first arrival of composed accept. -/
theorem check_drained_literal_endpoint :
    let e := machine.run 2973 (startConfig 22 tag physWord)
    e.state = machine.accept ∧ e.state.val = 194 ∧ e.head.val = 23 ∧
      e.tape = loopTape 22 tag physWord 4 0 24 ∧
      (∀ t, 2973 ≤ t → machine.run t (startConfig 22 tag physWord) = e) := by
  have hb : borrow tag physWord 4 = 0 := by decide
  have hc : holeChainClock (3 * 4 + 6) 8 9 4 0 24 = 2973 := rfl
  obtain ⟨h1, h2, h3, h4⟩ :=
    separator_hole_countdown_drained
      (q := FixedGammaPayloadDispatcher.qHasOne)
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


end Pnp3.Tests.UniformV1FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdownSurfaceTests
