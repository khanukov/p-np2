import Complexity.Uniform.V1.FixedRawFencedTableFirstBit
import Pnp4.Frontier.ContractExpansion.ContentRawFencedDecrementBridge
import Pnp4.Frontier.ContractExpansion.ContentParseFieldRecovery
import Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionGateClosure

/-! G3v Infrastructure. Execute one truth-table bit from the same dependent successful
parse, at a raw length-only deadline. Positive physical payload is required. This is
neither full parsing nor a ContentVerifierBridge, and reduces no lower-bound source. -/
namespace Pnp4.Frontier.ContractExpansion
open AlgorithmsToLowerBounds
open Pnp3.Complexity.Uniform.V1 PairEncoding FixedRawLengthFence

theorem contentInput?_x_apply_canonical
    {threshold : Nat → Nat} (codec : TreeCircuitWitnessCodec threshold)
    {N : Nat} (word : PrefixBitVec N)
    {pr : Sigma fun r : Nat =>
      PrefixInput (treeMCSPSearchProblem threshold
        (TreeMCSPSearchWitnessEncoding.ofCodec codec)) (treeMCSPPrefixM codec r)}
    (hpr : contentInput? codec word = some pr)
    (j : Fin (Pnp3.Models.Partial.tableLen pr.2.n)) :
    pr.2.x j = padRead word (tagLen + gammaLen pr.2.n + j.val) := by
  unfold contentInput? at hpr
  cases hheader : contentHeader? word with
  | none => simp [hheader] at hpr
  | some header =>
    obtain ⟨n',_⟩ := header
    simp only [hheader] at hpr
    cases hparse : parseTreeMCSPPrefixInput threshold codec (padWord word (treeMCSPPrefixM codec n')) with
    | none => simp [hparse] at hpr
    | some input =>
      simp only [hparse,Option.map_some] at hpr
      cases hpr
      obtain ⟨cg,hg,hslice⟩ := parseTreeMCSPPrefixInput_x_slice codec
        (padWord word (treeMCSPPrefixM codec n')) input hparse
      rw [decodeGamma?_consumed_eq_gammaLen _ hg] at hslice
      unfold sliceBits? at hslice
      split at hslice
      · exact (congrFun (Option.some.inj hslice) j).symm
      · cases hslice

theorem raw_first_table_bit_parsed_target
    (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    {pr : Sigma fun r : Nat =>
      PrefixInput (treeMCSPSearchProblem (thresholdPoly k)
        (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
        (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) r)}
    (hpr : contentInput? (treeCircuitWitnessCodec (thresholdPoly k))
      (Fin.append x w) = some pr)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hn : 3 ≤ pr.2.n)
    (htrail : 9 + (gammaLen pr.2.n - 1)/2 < a+m)
    (hcap : pr.2.n ≤ capacity a m ((gammaLen pr.2.n - 1)/2)) :
    let z := (gammaLen pr.2.n - 1)/2
    let B := allocation (pairLength a m)
    pr.2.n = pr.1 ∧
    contentHeader? (Fin.append x w) = some (pr.2.n, 2*z+1) ∧
    ∀ s : Nat,
      FixedRawFencedTableFirstBit.machine.run
        (FixedRawFencedTableFirstBit.deadline (pairLength a m)+s)
        (initialConfig FixedRawFencedTableFirstBit.machine B (encodePair x w)) =
      ⟨FixedRawFencedTableFirstBit.machine.accept,
        ⟨a+m+1, by simp only [tapeLength, pairLength]; omega⟩,
        FixedRawFencedTableFirstBit.outputTape B x w z pr.2.n
          (pr.2.x ⟨0, by exact Nat.two_pow_pos _⟩)⟩ := by
  obtain ⟨consumed,hh,hnr⟩ := contentInput?_target_eq_contentHeader
    (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w) hpr
  rw [← hnr] at hh
  obtain ⟨z,hg,hcons,-,hhi,-,hdig,hhigh⟩ := decremented_register_digits x w hh
  have hz : 2 ≤ z := by
    by_contra h
    have hp : 2^(z+1) ≤ (2:Nat)^2 := Nat.pow_le_pow_right (by decide) (by omega)
    norm_num at hp; omega
  have hlen : 2*z+1 = gammaLen pr.2.n := by
    simpa only [hcons] using contentHeader?_consumed_eq_gammaLen (Fin.append x w) hh
  have hzEq : (gammaLen pr.2.n-1)/2 = z := by omega
  rw [hzEq] at htrail hcap
  have hr := (resource_bounds (pairLength a m)).1
  obtain ⟨C,q,hC,hfirst,-,-⟩ := raw_fenced_h17_allocated x w htag hg hz
  have hT := (FixedRawFencedTableFirstBit.raw_clock_bound (by omega) hz
    (FixedGammaTargetRegisterDecrement.borrow_pins x w z).1 hC hcap).1
  have hx : FixedRawFencedTableFirstBit.sourceBit x w z =
      pr.2.x ⟨0,by exact Nat.two_pow_pos _⟩ := by
    rw [contentInput?_x_apply_canonical _ _ hpr]
    have hoff : tagLen+gammaLen pr.2.n = FixedRawFencedTableFirstBit.sourceOffset z := by
      unfold tagLen FixedRawFencedTableFirstBit.sourceOffset; omega
    simp only [Nat.add_zero,hoff]
    simp only [FixedRawFencedTableFirstBit.sourceBit,FixedContentTagGate.physicalSymbol,padRead]; split_ifs <;> rfl
  dsimp only; rw [hzEq]
  refine ⟨hnr,by simpa only [hcons] using hh,fun s => ?_⟩
  have he := FixedRawFencedTableFirstBit.raw_first_bit_exact x w hr htag hg hz hfirst
    (fun j hj => (hdig j hj).symm) hhigh hcap htrail
    (FixedRawFencedTableFirstBit.deadline (pairLength a m)-
      FixedRawFencedTableFirstBit.rawClock a m z C (FixedGammaTargetRegisterDecrement.borrow x w z) pr.2.n+s)
  rw [show FixedRawFencedTableFirstBit.rawClock a m z C (FixedGammaTargetRegisterDecrement.borrow x w z) pr.2.n+
      (FixedRawFencedTableFirstBit.deadline (pairLength a m)-
        FixedRawFencedTableFirstBit.rawClock a m z C (FixedGammaTargetRegisterDecrement.borrow x w z) pr.2.n+s) =
      FixedRawFencedTableFirstBit.deadline (pairLength a m)+s by omega,hx] at he
  exact he
end Pnp4.Frontier.ContractExpansion
