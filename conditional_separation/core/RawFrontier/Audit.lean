import RawFrontier.Syntactic
import RawFrontier.Capacity
import RawFrontier.Counterexample
namespace RawFrontier.Audit
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
open FixedGammaTargetRegisterDecrement (borrow decBit)
def pin_Frontier (k : Nat) : Prop := @RawFrontier.Target.Frontier k
theorem check_early_reject_sound (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m) (t : Nat)
    (reject : ((AllArityCursor.machine k).run t (initialConfig (AllArityCursor.machine k)
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=(AllArityCursor.machine k).reject)
    (noWork : ∀ u, u < t →
      ((AllArityCursor.machine k).run u (initialConfig (AllArityCursor.machine k)
        (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state≠
          SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 57) ∧
      ((AllArityCursor.machine k).run u (initialConfig (AllArityCursor.machine k)
        (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state≠
          SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 58)) :
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=false := @RawFrontier.early_reject_sound k a m x w t reject noWork
theorem check_producer_reject_frontier (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m) (T : Nat)
    (price : T ≤ 128*(pairLength a m+1)^2)
    (hit : (SmallIngress.producer.run T (initialConfig SmallIngress.producer
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=SmallIngress.producer.reject) :
    let c := initialConfig (AllArityCursor.machine k)
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
    ∃ t, t ≤ 128*(pairLength a m+1)^2 ∧
      ((AllArityCursor.machine k).run t c).state=(AllArityCursor.machine k).reject ∧
      (∀ u, u < t →
        ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).reject ∧
        ((AllArityCursor.machine k).run u c).state≠SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 57) ∧
        ((AllArityCursor.machine k).run u c).state≠SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 58)) ∧
      (∀ u, u ≤ t → ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).accept) ∧
      PartAEndpoint.thresholdContentWitnessRelation k a m x w=false := @RawFrontier.producer_reject_frontier k a m x w T price hit
theorem check_syntactic_reject (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (bad : FixedContentTagGate.tagMatches (Fin.append x w)=false ∨
      FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=none) :
    let c := initialConfig (AllArityCursor.machine k)
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
    ∃ t, t ≤ 128*(pairLength a m+1)^2 ∧
      ((AllArityCursor.machine k).run t c).state=(AllArityCursor.machine k).reject ∧
      (∀ u, u < t →
        ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).reject ∧
        ((AllArityCursor.machine k).run u c).state≠SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 57) ∧
        ((AllArityCursor.machine k).run u c).state≠SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 58)) ∧
      (∀ u, u ≤ t → ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).accept) ∧
      PartAEndpoint.thresholdContentWitnessRelation k a m x w=false ∧
      ((AllArityCursor.machine k).run t c).tape=
        FixedRawLengthFence.fencedContentTape (FixedRawLengthFence.allocation (pairLength a m)) x w ∧
      ((AllArityCursor.machine k).run t c).head.val ≤ a+m := @RawFrontier.syntactic_reject k a m x w bad
theorem check_capacity_reject (k : Nat) {a m z v : Nat} (x : Bitstring a) (w : Bitstring m)
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z) (wide : 2 ≤ z)
    (digits : ∀ j, j ≤ z → v.testBit (z-j)=decBit x w z (borrow x w z) j)
    (high : ∀ b, z < b → v.testBit b=false) (overflow : FixedRawLengthFence.capacity a m z < v) :
    let B := FixedRawLengthFence.allocation (pairLength a m)
    let c := initialConfig (AllArityCursor.machine k) B (encodePair x w)
    ∃ t, t ≤ 128*(pairLength a m+1)^2 ∧
      ((AllArityCursor.machine k).run t c).state=(AllArityCursor.machine k).reject ∧
      (∀ u, u < t →
        ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).reject ∧
        ((AllArityCursor.machine k).run u c).state≠SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 57) ∧
        ((AllArityCursor.machine k).run u c).state≠SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 58)) ∧
      (∀ u, u ≤ t → ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).accept) ∧
      PartAEndpoint.thresholdContentWitnessRelation k a m x w=false ∧
      ((AllArityCursor.machine k).run t c).head.val=FixedRawLengthFence.fencePos (pairLength a m) ∧
      ((AllArityCursor.machine k).run t c).tape=FixedRawLengthFence.countdownTape B x w z
        (v-FixedRawLengthFence.capacity a m z-1) (FixedRawLengthFence.capacity a m z) := @RawFrontier.capacity_reject k a m z v x w tag gamma wide digits high overflow
theorem check_raw_stalls (k : Nat) :
    let x : Bitstring 11 := fun i => i.val==0 || i.val==2 || i.val==3 || i.val==6 || i.val==10
    let c := initialConfig (AllArityCursor.machine k) 9216 (encodePair x (Fin.elim0 : Bitstring 0))
    (∀ u, ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).reject ∧
      ((AllArityCursor.machine k).run u c).state≠SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 57) ∧
      ((AllArityCursor.machine k).run u c).state≠SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 58) ∧
      ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).accept) ∧
    ∃ t, t ≤ 73752 ∧
      (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
        ⟨Cursor.q k 5,⟨0,by decide⟩,Body.installedTape (FixedRawLengthFence.countdownTape 9216 x Fin.elim0 2 0 3) 15 3⟩ ∧
      (AllArityCursor.machine k).stepConfig ((AllArityCursor.machine k).run t c)=
        (AllArityCursor.machine k).run t c ∧
      (∀ s, (AllArityCursor.machine k).run (t+s) c=(AllArityCursor.machine k).run t c) := @RawFrontier.raw_stalls k
theorem check_sample_relation_false (k : Nat) :
    PartAEndpoint.thresholdContentWitnessRelation k 11 0
      (fun i => i.val==0 || i.val==2 || i.val==3 || i.val==6 || i.val==10) Fin.elim0=false := @RawFrontier.sample_relation_false k
theorem check_frontier_impossible (k : Nat) :
  ¬(
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m),
    let c := initialConfig (AllArityCursor.machine k)
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
    ∃ t, t ≤ 16777216*(pairLength a m+1)^4 ∧
      (((AllArityCursor.machine k).run t c).state=(AllArityCursor.machine k).reject ∨
       ((AllArityCursor.machine k).run t c).state=SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 57) ∨
       ((AllArityCursor.machine k).run t c).state=SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 58)) ∧
      (∀ u, u < t →
        ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).reject ∧
        ((AllArityCursor.machine k).run u c).state≠SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 57) ∧
        ((AllArityCursor.machine k).run u c).state≠SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 58)) ∧
      (∀ u, u ≤ t → ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).accept) ∧
      (((AllArityCursor.machine k).run t c).state=(AllArityCursor.machine k).reject →
        PartAEndpoint.thresholdContentWitnessRelation k a m x w=false)
  ) := @RawFrontier.frontier_impossible k
end RawFrontier.Audit
#print axioms RawFrontier.Target.Frontier
#print axioms RawFrontier.Audit.pin_Frontier
#print axioms RawFrontier.early_reject_sound
#print axioms RawFrontier.Audit.check_early_reject_sound
#print axioms RawFrontier.producer_reject_frontier
#print axioms RawFrontier.Audit.check_producer_reject_frontier
#print axioms RawFrontier.syntactic_reject
#print axioms RawFrontier.Audit.check_syntactic_reject
#print axioms RawFrontier.capacity_reject
#print axioms RawFrontier.Audit.check_capacity_reject
#print axioms RawFrontier.raw_stalls
#print axioms RawFrontier.Audit.check_raw_stalls
#print axioms RawFrontier.sample_relation_false
#print axioms RawFrontier.Audit.check_sample_relation_false
#print axioms RawFrontier.frontier_impossible
#print axioms RawFrontier.Audit.check_frontier_impossible
