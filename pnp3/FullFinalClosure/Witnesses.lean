import FullFinalClosure.Target
namespace FullFinalClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
set_option autoImplicit false
set_option maxRecDepth 512
set_option maxHeartbeats 200000
/-- Independent original-query witness bound, not arity or encoded length. -/
private theorem original_witnesses (k : Nat) : Target.Witnesses k := by
  intro a x
  let codec:=treeCircuitWitnessCodec (thresholdPoly k)
  constructor
  · intro yes
    obtain ⟨w,accepted⟩:=(contentSemanticAccepts_correct codec x).mp yes
    refine ⟨Pnp3.ComplexityInterfaces.certificateLength a 1,w,le_rfl,?_⟩
    change PartAEndpoint.contentWitnessRelation codec a _ x w=true
    rw [PartAEndpoint.contentWitnessRelation_at_certificateLength_concatBitstring]
    exact accepted
  · rintro ⟨m,w,_bound,accepted⟩
    change PartAEndpoint.contentWitnessRelation codec a m x w=true at accepted
    by_cases same:m=Pnp3.ComplexityInterfaces.certificateLength a 1
    · subst m
      rw [PartAEndpoint.contentWitnessRelation_at_certificateLength_concatBitstring] at accepted
      exact (contentSemanticAccepts_correct codec x).mpr ⟨w,accepted⟩
    · rw [PartAEndpoint.contentWitnessRelation_of_wrongLength codec x w same] at accepted
      cases accepted
private theorem original_length (k a m : Nat) (x : Bitstring a) (w : Bitstring m)
    (accepted:PartAEndpoint.thresholdContentWitnessRelation k a m x w=true) :
    m=a+1 ∧ pairLength a m=3*a+2 ∧ m≤polyClock 1 a := by
  have same:m=Pnp3.ComplexityInterfaces.certificateLength a 1:=by
    by_contra no
    have bad:=PartAEndpoint.contentWitnessRelation_of_wrongLength (treeCircuitWitnessCodec (thresholdPoly k)) x w no
    rw [show PartAEndpoint.contentWitnessRelation (treeCircuitWitnessCodec (thresholdPoly k)) a m x w=
      PartAEndpoint.thresholdContentWitnessRelation k a m x w from rfl,accepted] at bad
    cases bad
  have length:m=a+1:=by simpa only [Pnp3.ComplexityInterfaces.certificateLength,pow_one] using same
  refine ⟨length,?_,?_⟩
  · change 2*a+1+m=3*a+2;omega
  · change m≤a^1+1;rw [pow_one];omega
end FullFinalClosure
