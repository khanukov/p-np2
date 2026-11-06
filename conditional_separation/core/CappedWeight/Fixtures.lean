import CappedWeight.Raw
import AllArityWorkspace.Nonvacuity
namespace CappedWeight
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
set_option maxRecDepth 4000
attribute [local irreducible] UniformTM.run
/-- Symbolic canonical accepted certificates, distinct from the literal host pilots. -/
theorem canonical_outcome (k : Nat) (hk : 0 < k) (n : Fin 3) (b : Bool) :
    let codec:=treeCircuitWitnessCodec (thresholdPoly k)
    let a:=treeMCSPPrefixM codec n.val
    let m:=Pnp3.ComplexityInterfaces.certificateLength a 1
    let x:=zeroPrefixQueryValue codec n.val (fun _ => b)
    ∃ w : Bitstring m, PartAEndpoint.thresholdContentWitnessRelation k a m x w=true ∧
      ∃ t, t ≤ 268435456*(pairLength a m+1)^4 ∧
        let c:=initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
        (((AllArityCursor.machine k).run t c).state=SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 411) ∨
         ((AllArityCursor.machine k).run t c).state=SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k (798+93*k)) ∨
         ((AllArityCursor.machine k).run t c).state=SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 250) ∨
         ((AllArityCursor.machine k).run t c).state=SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 304) ∨
         ((AllArityCursor.machine k).run t c).state=SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.mReady k ⟨2,by decide⟩)) := by
  dsimp only
  let codec:=treeCircuitWitnessCodec (thresholdPoly k)
  let a:=treeMCSPPrefixM codec n.val
  let m:=Pnp3.ComplexityInterfaces.certificateLength a 1
  let x:=zeroPrefixQueryValue codec n.val (fun _ => b)
  obtain ⟨w,accepted,_prior⟩:=AllArityWorkspace.canonical_raw k n b
  let c:=initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
  obtain ⟨pr,_parsed,_table,z,_hH,_gamma,eof,physical⟩:=accepted_first_product k hk x w accepted
  let p:=min (9+2*z+2^pr.2.n) (a+m)
  have priceLift {t : Nat} (h : t ≤ 67108864*(pairLength a m+1)^4) : t ≤ 268435456*(pairLength a m+1)^4 :=
    h.trans (Nat.mul_le_mul_right _ (by decide : 67108864 ≤ 268435456))
  by_cases hp : p < a+m
  · obtain ⟨t,_h,price,fit,done,_first,_logical,cont⟩:=physical hp
    by_cases fits : bitLength pr.2.n ≤ a+m-p
    · obtain ⟨d,_pd,run,bound,_before,_virtual⟩:=cont fits fit
      refine ⟨w,accepted,t+d,bound,?_⟩
      have state:=congrArg Config.state run
      change ((AllArityCursor.machine k).run (t+d) c).state=SmallIngress.producer.seqRight (Cursor.machine k)
        (Cursor.q k (if pr.2.n ≤ a+m-p then 411 else 798+93*k)) at state
      by_cases product : pr.2.n ≤ a+m-p
      · rw [if_pos product] at state; exact Or.inl state
      · rw [if_neg product] at state; exact Or.inr (Or.inl state)
    · have state:=congrArg Config.state done
      change ((AllArityCursor.machine k).run t c).state=SmallIngress.producer.seqRight (Cursor.machine k)
        (Cursor.q k (if bitLength pr.2.n ≤ a+m-p then 329 else if (a+m-p+1)%2=1 then 250 else 304)) at state
      rw [if_neg fits] at state
      refine ⟨w,accepted,t,priceLift price,?_⟩
      by_cases odd : (a+m-p+1)%2=1
      · rw [if_pos odd] at state; exact Or.inr (Or.inr (Or.inl state))
      · rw [if_neg odd] at state; exact Or.inr (Or.inr (Or.inr (Or.inl state)))
  · have eq : p=a+m := by have le : p ≤ a+m:=Nat.min_le_right _ _; omega
    obtain ⟨t,price,_logical,_false,done⟩:=eof eq
    exact ⟨w,accepted,t,priceLift price,Or.inr (Or.inr (Or.inr (Or.inr (congrArg Config.state done))))⟩
end CappedWeight
