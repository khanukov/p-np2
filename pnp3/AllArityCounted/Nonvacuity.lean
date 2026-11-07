import AllArityCounted.Runtime
import Lean
namespace AllArityCounted
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
set_option maxRecDepth 4000
attribute [local irreducible] UniformTM.run
/-- Symbolic canonical semantic certificates reach the new raw phase endpoints.
This is separate from prepared body fixtures and literal trace-word reduction. -/
theorem canonical_raw (k : Nat) (n : Fin 3) (b : Bool) :
    let codec := treeCircuitWitnessCodec (thresholdPoly k)
    let a := treeMCSPPrefixM codec n.val
    let m := Pnp3.ComplexityInterfaces.certificateLength a 1
    let x := zeroPrefixQueryValue codec n.val (fun _ => b)
    ∃ w : Bitstring m, PartAEndpoint.thresholdContentWitnessRelation k a m x w=true ∧
      ∃ t, t ≤ 65536*(pairLength a m+1)^2 ∧
        let c := initialConfig (AllArityCursor.machine k)
          (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
        (((AllArityCursor.machine k).run t c).state=
            SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.rReady k) ∨
          ((AllArityCursor.machine k).run t c).state=
            SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.mReady k ⟨2,by decide⟩)) ∧
        (∀ u, u ≤ t → ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).accept ∧
          ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).reject) := by
  dsimp only
  let codec := treeCircuitWitnessCodec (thresholdPoly k)
  let a := treeMCSPPrefixM codec n.val
  let m := Pnp3.ComplexityInterfaces.certificateLength a 1
  let x := zeroPrefixQueryValue codec n.val (fun _ => b)
  obtain ⟨w,accepted,_previousHandoff⟩ := AllArityCursor.Fixtures.canonical_raw_handoff k n b
  obtain ⟨pr,_parsed,_table,z,t,_hH,_gamma,_price,_hp,_pre,_prefix,physical,eof⟩ := accepted_raw k x w accepted
  let p := min (9+2*z+2^pr.2.n) (a+m)
  by_cases hp : p < a+m
  · obtain ⟨_hS,_fit,price,_first,done,safe⟩ := physical hp
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
      ∃ t, t ≤ 65536*(pairLength a m+1)^2 ∧
        let c := initialConfig (AllArityCursor.machine k)
          (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
        (((AllArityCursor.machine k).run t c).state=
            SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.rReady k) ∨
          ((AllArityCursor.machine k).run t c).state=
            SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.mReady k ⟨2,by decide⟩)) ∧
        (∀ u, u ≤ t → ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).accept ∧
          ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).reject) := @AllArityCounted.canonical_raw k n b
end AllArityCounted
#print axioms AllArityCounted.canonical_raw
#print axioms AllArityCounted.Audit.check_canonical_raw
open Lean in
run_cmd do
  let e ← getEnv
  for (n, _) in e.constants.toList do
    if n.toString.startsWith "AllArityCounted." then logInfo m!"surface|{n}"
    if (e.getModuleIdxFor? n).isNone && !n.toString.startsWith "_private." then logInfo m!"owned|{n}"
  for n in e.header.moduleNames do logInfo m!"imported|{n}"
