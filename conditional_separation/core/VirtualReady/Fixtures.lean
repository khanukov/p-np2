import VirtualReady.Raw
import AllArityWorkspace.Nonvacuity
namespace VirtualReady
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
set_option maxRecDepth 4000
/-- Symbolic genuine accepted RAW non-vacuity, including n0/1/2 and both
Boolean values. Prepared cleanup diagnostics are not used as acceptance facts. -/
theorem canonical_outcome (k : Nat) (n : Fin 3) (b : Bool) :
    let codec := treeCircuitWitnessCodec (thresholdPoly k)
    let a := treeMCSPPrefixM codec n.val
    let m := Pnp3.ComplexityInterfaces.certificateLength a 1
    let x := zeroPrefixQueryValue codec n.val (fun _ => b)
    ∃ w : Bitstring m, PartAEndpoint.thresholdContentWitnessRelation k a m x w=true ∧
      ∃ t, t ≤ 134217728*(pairLength a m+1)^4 ∧
        let c := initialConfig (IngressRepair.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
        (((IngressRepair.machine k).run t c).state=IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k 329) ∨
         ((IngressRepair.machine k).run t c).state=IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.mReady k ⟨2,by decide⟩)) ∧
        (∀ u, u ≤ t → ((IngressRepair.machine k).run u c).state≠(IngressRepair.machine k).accept ∧
          ((IngressRepair.machine k).run u c).state≠(IngressRepair.machine k).reject) := by
  dsimp only
  obtain ⟨w,accepted,_prior⟩ := AllArityWorkspace.canonical_raw k n b
  obtain ⟨pr,_parsed,_table,z,_hH,_gamma,eof,physical⟩ := accepted_virtual k _ w accepted
  let a := treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n.val
  let m := Pnp3.ComplexityInterfaces.certificateLength a 1
  let p := min (9+2*z+2^pr.2.n) (a+m)
  by_cases phys : p < a+m
  · obtain ⟨_fit,seed,overflow⟩ := physical phys
    by_cases fits : bitLength pr.2.n ≤ a+m-p
    · obtain ⟨t,_h,price,run,_first,safe⟩ := seed fits
      exact ⟨w,accepted,t,price,Or.inl (congrArg Config.state run),safe⟩
    · obtain ⟨t,price,_logical,_read,run,safe⟩ := overflow (Nat.lt_of_not_ge fits)
      exact ⟨w,accepted,t,price,Or.inr (congrArg Config.state run),safe⟩
  · have eq : p=a+m := by have le := Nat.min_le_right (9+2*z+2^pr.2.n) (a+m); omega
    obtain ⟨t,price,_logical,_read,run,safe⟩ := eof eq
    exact ⟨w,accepted,t,price,Or.inr (congrArg Config.state run),safe⟩
end VirtualReady
