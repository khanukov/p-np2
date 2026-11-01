import AllArityWorkspace.Runtime
namespace AllArityWorkspace
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
set_option maxRecDepth 4000
attribute [local irreducible] UniformTM.run
/-- Real canonical accepted certificates, not prepared tapes; symbolic raw
non-vacuity for each n0/1/2 and each constant Boolean truth table. -/
theorem canonical_raw (k : Nat) (n : Fin 3) (b : Bool) :
    let codec := treeCircuitWitnessCodec (thresholdPoly k)
    let a := treeMCSPPrefixM codec n.val
    let m := Pnp3.ComplexityInterfaces.certificateLength a 1
    let x := zeroPrefixQueryValue codec n.val (fun _ => b)
    ∃ w : Bitstring m, PartAEndpoint.thresholdContentWitnessRelation k a m x w=true ∧
      ∃ t, t ≤ 1048576*(pairLength a m+1)^3 ∧
        let c := initialConfig (AllArityCursor.machine k)
          (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
        (((AllArityCursor.machine k).run t c).state=
            SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 201) ∨
          ((AllArityCursor.machine k).run t c).state=
            SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.mReady k ⟨2,by decide⟩)) ∧
        (∀ u, u ≤ t → ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).accept ∧
          ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).reject) := by
  dsimp only
  let codec := treeCircuitWitnessCodec (thresholdPoly k)
  let a := treeMCSPPrefixM codec n.val
  let m := Pnp3.ComplexityInterfaces.certificateLength a 1
  let x := zeroPrefixQueryValue codec n.val (fun _ => b)
  obtain ⟨w,accepted,_previous⟩ := AllArityCounted.canonical_raw k n b
  obtain ⟨pr,_parsed,_table,z,t,_hH,_gamma,_price,_hp,_pre,_prefix,physical,eof⟩ := accepted_raw k x w accepted
  let p := min (9+2*z+2^pr.2.n) (a+m)
  by_cases hp : p < a+m
  · obtain ⟨_hS,_counted,_firstCount,v,_hF,_bodyPrice,price,_fit,done,_first,safe⟩ := physical hp
    refine ⟨w,accepted,_,price,Or.inl ?_,safe⟩
    exact congrArg Config.state done
  · have he : p=a+m := by
      have bound : p ≤ a+m := Nat.min_le_right _ _
      omega
    obtain ⟨price,_logical,_false,done,safe⟩ := eof he
    refine ⟨w,accepted,_,price,Or.inr ?_,safe⟩
    exact congrArg Config.state done
theorem Audit.check_canonical_raw (k : Nat) (n : Fin 3) (b : Bool) :
    let codec := treeCircuitWitnessCodec (thresholdPoly k)
    let a := treeMCSPPrefixM codec n.val
    let m := Pnp3.ComplexityInterfaces.certificateLength a 1
    let x := zeroPrefixQueryValue codec n.val (fun _ => b)
    ∃ w : Bitstring m, PartAEndpoint.thresholdContentWitnessRelation k a m x w=true ∧
      ∃ t, t ≤ 1048576*(pairLength a m+1)^3 ∧
        let c := initialConfig (AllArityCursor.machine k)
          (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
        (((AllArityCursor.machine k).run t c).state=
            SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 201) ∨
          ((AllArityCursor.machine k).run t c).state=
            SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.mReady k ⟨2,by decide⟩)) ∧
        (∀ u, u ≤ t → ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).accept ∧
          ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).reject) := @AllArityWorkspace.canonical_raw k n b
end AllArityWorkspace
#print axioms AllArityWorkspace.canonical_raw
#print axioms AllArityWorkspace.Audit.check_canonical_raw
