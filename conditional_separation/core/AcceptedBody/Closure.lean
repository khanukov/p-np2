import AcceptedBody.Target
namespace AcceptedBody
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
set_option maxRecDepth 12000

/-- Computable concatenation has precisely the physical compacted source view. -/
theorem concat_eq_append {a m : Nat} (x : Bitstring a) (w : Bitstring m) :
    PartAEndpoint.concatV1ToPrefixBitVec x w = Fin.append x w := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [PartAEndpoint.concatV1ToPrefixBitVec, j.isLt]
  · have h : ¬ a+j.val < a := by omega
    simp [PartAEndpoint.concatV1ToPrefixBitVec, h]

/-- Accepted virtual content still bounds the number of assignment rows, not
necessarily the offset of the last physically present table cell. -/
theorem table_support (k : Nat) {N : Nat} (z : PrefixBitVec N) {pr : Parsed k}
    (parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) z = some pr)
    (accepted : contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k)) z = true) :
    Pnp3.Models.Partial.tableLen pr.2.n ≤ N := by
  have ha := (contentSemanticAccepts_eq_true_iff _ z).1 accepted
  obtain ⟨consumed,header,target⟩ := contentInput?_target_eq_contentHeader _ z parsed
  rw [← target] at header
  by_cases wide : N < treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) pr.2.n
  · obtain ⟨pr',hp',ht⟩ := contentAccepts_parsed_tableLen_le_of_header_target_wide
      k z pr.2.n consumed header ha wide
    have eq : pr'=pr := Option.some.inj (hp'.symm.trans parsed)
    cases eq
    exact ht
  · exact (tableLen_le_treeMCSPPrefixM _ _).trans (Nat.le_of_not_gt wide)

/-- A bound on the same parsed target discharges the producer's strict fence
capacity; no capacity-reject verdict is inferred for arbitrary rejected words. -/
theorem strict_capacity {a m z n : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some z)
    (target : n ≤ a+m) : n < FixedRawLengthFence.capacity a m z := by
  have support := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z gamma).1
  simp only [FixedRawLengthFence.capacity, FixedRawLengthFence.fencePos, pairLength]
  omega

/-- Explicit quadratic time for the already defined literal tape allocation. -/
theorem clock_bound (R n r T : Nat) (hn : n ≤ R) (hr : r ≤ R)
    (ht : T ≤ 128*(R+1)^2) :
    T+n+2+Body.iterClock (List.replicate n false) r ≤ deadline R := by
  have hc := Body.iter_clock_le (List.replicate n false) r
  simp only [List.length_replicate] at hc
  have hm : r*(2*n+3) ≤ R*(2*R+3) := Nat.mul_le_mul hr (by omega)
  unfold deadline
  nlinarith

/-- All physical premises follow from the exact guarded relation. This theorem
still does not execute a runtime read or conclude a language verdict. -/
theorem exact (k : Nat) : AcceptedOrbit k := by
  intro a m x w accepted
  have semantic : contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k))
      (PartAEndpoint.concatV1ToPrefixBitVec x w) = true := by
    unfold PartAEndpoint.thresholdContentWitnessRelation PartAEndpoint.contentWitnessRelation at accepted
    split at accepted
    · rename_i shape
      cases shape
      exact accepted
    · contradiction
  rw [concat_eq_append] at semantic
  have tag : FixedContentTagGate.tagMatches (Fin.append x w) = true := by
    have factor := fixedTag_semantic_factorization.1
      (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)
    rw [semantic] at factor
    simpa using factor.symm
  cases parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w) with
  | none => simp [contentSemanticAccepts,parsed] at semantic
  | some pr =>
    have table := table_support k (Fin.append x w) parsed semantic
    have small : pr.2.n ≤ a+m := by
      have lt : pr.2.n < Pnp3.Models.Partial.tableLen pr.2.n := Nat.lt_two_pow_self
      omega
    refine ⟨pr,rfl,table,?_⟩
    intro hn
    obtain ⟨z,hz,gamma,orbit⟩ := Body.raw_repeated_parsed k x w parsed tag hn
    have capacity := strict_capacity x w gamma small
    obtain ⟨T,hT,run⟩ := orbit capacity
    refine ⟨z,T,hz,gamma,capacity,hT,?_⟩
    intro r hr
    have pair : a+m ≤ pairLength a m := by simp only [pairLength]; omega
    have rows : r ≤ a+m := by change 2^pr.2.n ≤ a+m at table; omega
    refine ⟨clock_bound (pairLength a m) pr.2.n r T (small.trans pair) (rows.trans pair) hT,?_⟩
    exact run r hr
end AcceptedBody
