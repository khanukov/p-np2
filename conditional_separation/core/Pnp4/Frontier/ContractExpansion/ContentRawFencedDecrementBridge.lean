import Complexity.Uniform.V1.FixedRawLengthFenceCountdown
import Pnp4.Frontier.ContractExpansion.ContentFixedGammaTargetRegisterDecrementBridge
import Pnp4.Frontier.ContractExpansion.ConcreteTreeCodec
import Pnp4.Frontier.ContractExpansion.ThresholdGrowth

/-! G3t Infrastructure: the actual raw register holds the same dependent parser result's target.
G3u additionally executes the fenced countdown for that same field. No ContentVerifierBridge is constructed. -/
namespace Pnp4.Frontier.ContractExpansion
open AlgorithmsToLowerBounds Pnp3.Complexity.Uniform.V1
open PairEncoding FixedRawLengthFence

theorem raw_fenced_h17_parsed_target (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    {pr : Sigma fun r : Nat =>
      PrefixInput (treeMCSPSearchProblem (thresholdPoly k)
        (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
        (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) r)}
    (hpr : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w) = some pr)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) (hn : 3 ≤ pr.2.n) :
    let B := allocation (pairLength a m)
    pr.2.n = pr.1 ∧
    ∃ (zeros C : Nat) (q : Fin FixedGammaPayloadDispatcher.stateCount),
      2 ≤ zeros ∧ FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros ∧
      contentHeader? (Fin.append x w) = some (pr.2.n, 2*zeros+1) ∧ C ≤ 2*(a+m)*(a+m) ∧
      FixedGammaPayloadDispatcherFirstArrival.StrictFirstTerminalAt B x w C q ∧
      let d := FixedGammaTargetRegisterDecrement.borrow x w zeros
      let T := h17RawClock a m zeros C d
      let e := prefixed.run T (initialConfig prefixed B (encodePair x w))
      T ≤ h17Deadline (pairLength a m) ∧ e.state.val = 245 ∧ e.head.val = a+m+1+zeros-d ∧
      e.tape = fencedDecTape B x w zeros ∧
      (∀ j : Nat, j ≤ zeros → a+m+1+j < tapeLength (pairLength a m) B ∧
        ∀ i : Fin (tapeLength (pairLength a m) B), i.val = a+m+1+j →
          e.tape i = some (pr.2.n.testBit (zeros-j))) ∧
      (∀ b : Nat, zeros < b → pr.2.n.testBit b = false) := by
  obtain ⟨consumed,hh,hnr⟩ := contentInput?_target_eq_contentHeader
    (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w) hpr
  rw [← hnr] at hh
  obtain ⟨zeros,hg,hcons,-,hhi,-,hdig,hhigh⟩ := decremented_register_digits x w hh
  have hz : 2 ≤ zeros := by
    by_contra h
    have hp : 2^(zeros+1) ≤ (2:Nat)^2 := Nat.pow_le_pow_right (by decide) (by omega)
    norm_num at hp; omega
  obtain ⟨C,q,hC,hfirst,hT,he⟩ := raw_fenced_h17_allocated x w htag hg hz
  have hc := (raw_fenced_h17_cells x w (resource_bounds (pairLength a m)).1 htag hg hz hfirst).1
  dsimp only
  refine ⟨hnr,zeros,C,q,hz,hg,?_,hC,hfirst,hT,?_,?_,?_,?_,hhigh⟩
  · simpa only [hcons] using hh
  · rw [he]; rfl
  · rw [he]; rfl
  · rw [he]; rfl
  · intro j hj; refine ⟨(hc j hj).1,fun i hi => ?_⟩
    rw [(hc j hj).2 i hi,hdig j hj]

/-- G3u: the same dependent parse target becomes exactly that many tally marks,
or literally rejects on strict overflow. Other parser fields and GN remain open. -/
theorem raw_fenced_countdown_parsed_target (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    {pr : Sigma fun r : Nat =>
      PrefixInput (treeMCSPSearchProblem (thresholdPoly k)
        (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
        (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) r)}
    (hpr : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w) = some pr)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) (hn : 3 ≤ pr.2.n) :
    let B := allocation (pairLength a m)
    pr.2.n = pr.1 ∧ ∃ (z C : Nat) (q : Fin FixedGammaPayloadDispatcher.stateCount)
      (hS : a+m+2+z < tapeLength (pairLength a m) B),
      2 ≤ z ∧ FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some z ∧
      contentHeader? (Fin.append x w) = some (pr.2.n,2*z+1) ∧ C ≤ 2*(a+m)*(a+m) ∧
      FixedGammaPayloadDispatcherFirstArrival.StrictFirstTerminalAt B x w C q ∧
      (pr.2.n ≤ capacity a m z →
        countdownSuccessClock a m z C (FixedGammaTargetRegisterDecrement.borrow x w z) pr.2.n ≤
          countdownDeadline (pairLength a m) ∧
        prefixed.run (countdownSuccessClock a m z C (FixedGammaTargetRegisterDecrement.borrow x w z) pr.2.n)
          (initialConfig prefixed B (encodePair x w)) =
          ⟨prefixed.accept,⟨a+m+2+z,hS⟩,countdownTape B x w z 0 pr.2.n⟩) ∧
      (capacity a m z < pr.2.n →
        countdownRejectClock a m z C (FixedGammaTargetRegisterDecrement.borrow x w z) ≤
          countdownDeadline (pairLength a m) ∧
        prefixed.run (countdownRejectClock a m z C (FixedGammaTargetRegisterDecrement.borrow x w z))
          (initialConfig prefixed B (encodePair x w)) =
          ⟨prefixed.reject,⟨fencePos (pairLength a m),by have h := (resource_bounds (pairLength a m)).1; simp only [fencePos,tapeLength]; omega⟩,
            countdownTape B x w z (pr.2.n-capacity a m z-1) (capacity a m z)⟩) := by
  obtain ⟨consumed,hh,hnr⟩ := contentInput?_target_eq_contentHeader
    (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w) hpr
  rw [← hnr] at hh
  obtain ⟨z,hg,hcons,-,hhi,-,hdig,hhigh⟩ := decremented_register_digits x w hh
  have hz : 2 ≤ z := by
    by_contra h
    have hp : 2^(z+1) ≤ (2:Nat)^2 := Nat.pow_le_pow_right (by decide) (by omega)
    norm_num at hp; omega
  have hr := (resource_bounds (pairLength a m)).1
  obtain ⟨C,q,hC,hfirst,-,-⟩ := raw_fenced_h17_allocated x w htag hg hz
  have hw : 9+z ≤ a+m := by
    have h := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z hg).1; omega
  have hS : a+m+2+z < tapeLength (pairLength a m) (allocation (pairLength a m)) := by
    simp only [tapeLength,pairLength] at *; omega
  dsimp only
  refine ⟨hnr,z,C,q,hS,hz,hg,?_,hC,hfirst,?_,?_⟩
  · simpa only [hcons] using hh
  · intro hc
    exact ⟨(countdown_clock_bound hw hz (FixedGammaTargetRegisterDecrement.borrow_pins x w z).1 hC hc).1,
      by simpa only [Nat.add_zero] using raw_fenced_countdown_success_exact x w hr htag hg hz hfirst (fun j hj => (hdig j hj).symm) hhigh hc 0⟩
  · intro hc
    exact ⟨(countdown_clock_bound hw hz (FixedGammaTargetRegisterDecrement.borrow_pins x w z).1 hC
        (Nat.zero_le (capacity a m z))).2.1,
      by simpa only [Nat.add_zero] using raw_fenced_countdown_reject_exact x w hr htag hg hz hfirst (fun j hj => (hdig j hj).symm) hhigh hc 0⟩
end Pnp4.Frontier.ContractExpansion
