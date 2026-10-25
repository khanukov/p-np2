import IngressRepair.Runtime
namespace RepairedFrontier.Target
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
/-- Every actual raw pair reaches the FIRST literal reject/work frontier.
No parser, header, capacity or acceptance premise is supplied by the caller. -/
def Frontier (k : Nat) : Prop :=
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m),
    let c := initialConfig (IngressRepair.machine k)
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
    ∃ t, t ≤ 16777216*(pairLength a m+1)^4 ∧
      (((IngressRepair.machine k).run t c).state=(IngressRepair.machine k).reject ∨
       ((IngressRepair.machine k).run t c).state=IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k 57) ∨
       ((IngressRepair.machine k).run t c).state=IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k 58)) ∧
      (∀ u, u < t →
        ((IngressRepair.machine k).run u c).state≠(IngressRepair.machine k).reject ∧
        ((IngressRepair.machine k).run u c).state≠IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k 57) ∧
        ((IngressRepair.machine k).run u c).state≠IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k 58)) ∧
      (∀ u, u ≤ t → ((IngressRepair.machine k).run u c).state≠(IngressRepair.machine k).accept) ∧
      (((IngressRepair.machine k).run t c).state=(IngressRepair.machine k).reject →
        PartAEndpoint.thresholdContentWitnessRelation k a m x w=false)
/-- Separate arbitrary-word target. Canonical pair totality alone does not prove this. -/
def RawWords (k : Nat) : Prop :=
  ∀ N (y : Bitstring N),
    let c := initialConfig (IngressRepair.machine k)
      (FixedRawLengthFence.allocation N) y
    ∃ t, t ≤ 16777216*(N+1)^4 ∧
      (((IngressRepair.machine k).run t c).state=(IngressRepair.machine k).reject ∨
       ((IngressRepair.machine k).run t c).state=IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k 57) ∨
       ((IngressRepair.machine k).run t c).state=IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k 58)) ∧
      (∀ u, u < t →
        ((IngressRepair.machine k).run u c).state≠(IngressRepair.machine k).reject ∧
        ((IngressRepair.machine k).run u c).state≠IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k 57) ∧
        ((IngressRepair.machine k).run u c).state≠IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k 58)) ∧
      (∀ u, u ≤ t → ((IngressRepair.machine k).run u c).state≠(IngressRepair.machine k).accept) ∧
      (((IngressRepair.machine k).run t c).state=(IngressRepair.machine k).reject →
        encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y=false)
end RepairedFrontier.Target
