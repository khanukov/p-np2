import VirtualFinalClosure.Joint
namespace VirtualFinalClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds
/-- The original truth-table enumeration, derived from its vector round trips. -/
private theorem input_table {n : Nat} (positive : 0<n) (tt : TruthTable n) :
    ComputesTruthTable treeCircuitClass (Pnp3.Models.Circuit.input ⟨0,positive⟩) tt ↔
      ∀ j : Fin (2^n), tt j=Nat.testBit j.val 0 := by
  constructor
  · intro computes j
    obtain ⟨beta,index⟩:=Pnp3.Models.assignmentIndex_surjective j
    have row:=computes beta
    change beta ⟨0,positive⟩=tt (Pnp3.Models.assignmentIndex beta) at row
    rw [index] at row
    have bit:=congrFun (Pnp3.Models.vecOfNat_assignmentIndex_val beta) ⟨0,positive⟩
    rw [index] at bit
    exact row.symm.trans bit.symm
  · intro rows beta
    have row:=rows (Pnp3.Models.assignmentIndex beta)
    have bit:=congrFun (Pnp3.Models.vecOfNat_assignmentIndex_val beta) ⟨0,positive⟩
    change beta ⟨0,positive⟩=tt (Pnp3.Models.assignmentIndex beta)
    exact (row.trans bit).symm
private theorem blank_codec (k n : Nat) (positive : 0<n) (tt : TruthTable n) :
    (treeCircuitWitnessCodec (thresholdPoly k)).verifies n tt (fun _=>false) ↔
      ∀ j : Fin (2^n), tt j=Nat.testBit j.val 0 := by
  constructor
  · rintro ⟨c,decoded,_size,computes⟩
    rw [treeCircuitWitnessCodec_decode_blank_pos k positive] at decoded
    have same:=Option.some.inj decoded
    subst c
    exact (input_table positive tt).1 computes
  · intro rows
    refine ⟨Pnp3.Models.Circuit.input ⟨0,positive⟩,
      treeCircuitWitnessCodec_decode_blank_pos k positive,?_,(input_table positive tt).2 rows⟩
    change 1≤n^k+k
    cases k with
    | zero => simp
    | succ k => omega
/-- Semantic specification only. The original parser and prefix agreement
remain explicit; this result supplies no runtime parser/control oracle. -/
theorem virtual_relation {a m : Nat} (k : Nat) (x : Bitstring a) (w : Bitstring m)
    {pr : AcceptedBody.Parsed k} (canonical : m=a+1) (positive : 0<pr.2.n)
    (parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr)
    (blank : contentWitness (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w) pr.2.n=(fun _=>false)) :
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=true ↔
      pr.2.prefixAgrees (fun _=>false) ∧
      ∀ j : Fin (2^pr.2.n),pr.2.x j=Nat.testBit j.val 0 := by
  have reduce : PartAEndpoint.thresholdContentWitnessRelation k a m x w=
      contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w) := by
    unfold PartAEndpoint.thresholdContentWitnessRelation PartAEndpoint.contentWitnessRelation
    split
    · rename_i length
      cases length
      exact congrArg (contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k)))
        (AcceptedBody.concat_eq_append x w)
    · rename_i bad
      have length : m=Pnp3.ComplexityInterfaces.certificateLength a 1 := by
        simpa [Pnp3.ComplexityInterfaces.certificateLength] using canonical
      exact (bad length).elim
  rw [reduce]
  dsimp only [contentSemanticAccepts]
  rw [parsed]
  dsimp only
  rw [Bool.and_eq_true,prefixAgreesBool_eq_true_iff,verifiesBool_eq_true_iff,blank]
  exact and_congr Iff.rfl (blank_codec k pr.2.n positive pr.2.x)
set_option autoImplicit false in
theorem check_virtual_relation :
    ∀ {a m : Nat} (k : Nat) (x : Bitstring a) (w : Bitstring m)
      {pr : Σ n' : Nat,PrefixInput
        (treeMCSPSearchProblem (thresholdPoly k)
          (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
        (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n')}, m=a+1 → 0<pr.2.n →
      contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr →
      contentWitness (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w) pr.2.n=(fun _=>false) →
      (PartAEndpoint.thresholdContentWitnessRelation k a m x w=true ↔
        pr.2.prefixAgrees (fun _=>false) ∧
        ∀ j : Fin (2^pr.2.n),pr.2.x j=Nat.testBit j.val 0) := by
  intro a m k x w pr canonical positive parsed blank
  exact virtual_relation k x w canonical positive parsed blank
#print axioms virtual_relation
#print axioms check_virtual_relation
end VirtualFinalClosure
