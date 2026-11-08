import AllArityWorkspace.Surface
namespace RawFrontier.Target
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
/-- Every actual raw pair reaches the FIRST literal reject/work frontier.
No parser, header, capacity or acceptance premise is supplied by the caller. -/
def Frontier (k : Nat) : Prop :=
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
end RawFrontier.Target
