import ConnectedRead.Target
namespace ConnectedRead
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding

/-- Compose the completed same-table raw run with accepted gamma feasibility.
The execution time/allocation and entire lifted-hole Config are unchanged. -/
theorem exact (k : Nat) : Exact k := by
  intro a m x w accepted
  have semantic : contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k))
      (Fin.append x w)=true := by
    have h := accepted
    unfold PartAEndpoint.thresholdContentWitnessRelation PartAEndpoint.contentWitnessRelation at h
    split at h
    · rename_i shape
      cases shape
      rwa [AcceptedBody.concat_eq_append] at h
    · contradiction
  obtain ⟨pr,parsed,table,old⟩ := InputRead.accepted_cursor k x w accepted
  refine ⟨pr,parsed,table,?_⟩
  intro hn
  obtain ⟨z,T,hz,gamma,run⟩ := old hn
  have full := GammaSupport.exact k x w parsed semantic hn z gamma
  obtain ⟨hR,mode,clock,virtual,bit,config⟩ := run full
  exact ⟨z,T,hR,mode,hz,gamma,full,clock,virtual,bit,config⟩
end ConnectedRead
