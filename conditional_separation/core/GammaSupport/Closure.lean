import GammaSupport.Target
namespace GammaSupport
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds

private theorem width_le (n : Nat) : gammaZeros n ≤ n := by
  have hlo : 2^gammaZeros n ≤ n+1 := by
    unfold gammaZeros
    exact two_pow_bitLength_pred_le (a := n+1) (Nat.succ_pos n)
  have hlt : gammaZeros n < 2^gammaZeros n := Nat.lt_two_pow_self
  omega

private theorem row_growth (n : Nat) (hn : 3 ≤ n) : 2*n+1 ≤ 2^n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih => rw [Nat.pow_succ]; omega

private theorem wide_support (k : Nat) {N : Nat} (z : PrefixBitVec N)
    {pr : Sigma fun r : Nat =>
      PrefixInput (treeMCSPSearchProblem (thresholdPoly k)
        (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
        (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) r)}
    (parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) z = some pr)
    (accepted : contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k)) z = true)
    (positive : 0 < pr.2.n)
    (wide : N < treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) pr.2.n) :
    tagLen + Pnp3.Models.Partial.tableLen pr.2.n ≤ N := by
  let codec := treeCircuitWitnessCodec (thresholdPoly k)
  obtain ⟨pr',hpr',_hp,hrelation⟩ := (contentSemanticAccepts_eq_true_iff codec z).1 accepted
  have same : pr'=pr := Option.some.inj (hpr'.symm.trans parsed)
  cases same
  have blank := contentWitness_eq_false_of_lt codec z pr.2.n wide
  change codec.verifies pr.2.n pr.2.x (contentWitness codec z pr.2.n) at hrelation
  obtain ⟨c,hdecode,_size,computes⟩ := hrelation
  rw [blank,treeCircuitWitnessCodec_decode_blank_pos k positive] at hdecode
  cases hdecode
  have last := input_zero_computes_forces_last_true positive pr.2.x computes
  obtain ⟨cg,read⟩ := contentInput?_x_apply codec z parsed
  have tpos : 0 < Pnp3.Models.Partial.tableLen pr.2.n := by
    change 0 < 2^pr.2.n
    exact Nat.two_pow_pos _
  let j : Fin (Pnp3.Models.Partial.tableLen pr.2.n) :=
    ⟨Pnp3.Models.Partial.tableLen pr.2.n-1,by omega⟩
  have trueRead : padRead z (tagLen+cg+j.val)=true := by
    rw [←read j]
    exact last
  have support := lt_of_padRead_eq_true z trueRead
  dsimp [j] at support
  omega

/-- Acceptance, unlike parse success alone, puts the complete canonical gamma
field inside physical support in the n>=3 branch. No whole-table support claim. -/
theorem canonical (k : Nat) {N : Nat} (z : PrefixBitVec N)
    {pr : Sigma fun r : Nat =>
      PrefixInput (treeMCSPSearchProblem (thresholdPoly k)
        (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
        (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) r)}
    (parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) z = some pr)
    (accepted : contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k)) z = true)
    (hn : 3 ≤ pr.2.n) : tagLen + gammaLen pr.2.n ≤ N := by
  by_cases wide : N < treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) pr.2.n
  · have support := wide_support k z parsed accepted (by omega) wide
    have width := width_le pr.2.n
    have rows := row_growth pr.2.n hn
    have length := gammaLen_eq_two_mul_gammaZeros_add_one pr.2.n
    change tagLen + 2^pr.2.n ≤ N at support
    omega
  · exact (gammaLen_le_treeMCSPPrefixM _ _).trans (Nat.le_of_not_gt wide)

/-- The actual physical width from the same source has its whole payload in
support. This discharges a later raw-reader feasibility guard, not that run. -/
theorem exact : Exact := by
  intro k a m x w pr parsed accepted hn g gamma
  have support := canonical k (Fin.append x w) parsed accepted hn
  obtain ⟨consumed,header,target⟩ :=
    contentInput?_target_eq_contentHeader (treeCircuitWitnessCodec (thresholdPoly k))
      (Fin.append x w) parsed
  rw [←target] at header
  have width := (countdown_width_eq_gammaZeros x w header gamma).1
  have length := gammaLen_eq_two_mul_gammaZeros_add_one pr.2.n
  simp only [tagLen] at support
  omega
end GammaSupport
