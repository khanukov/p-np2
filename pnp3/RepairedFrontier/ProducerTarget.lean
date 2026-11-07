import RepairedFrontier.Target
namespace RepairedFrontier.Target
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding
/-- Dependency boundary before the unchanged live Cursor body. This does not
replace Frontier: the consumer entry is q0 (absolute288), not work q57/q58. -/
def ProducerEntry (k : Nat) : Prop :=
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m),
    let c := initialConfig (IngressRepair.machine k)
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
    ∃ t, t ≤ 128*(pairLength a m+1)^2 ∧
      (((IngressRepair.machine k).run t c).state=(IngressRepair.machine k).reject ∨
       ((IngressRepair.machine k).run t c).state=IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.machine k).start) ∧
      (∀ u, u < t →
        ((IngressRepair.machine k).run u c).state≠(IngressRepair.machine k).reject ∧
        ((IngressRepair.machine k).run u c).state≠IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.machine k).start) ∧
      (∀ u, u ≤ t →
        ((IngressRepair.machine k).run u c).state≠(IngressRepair.machine k).accept ∧
        ((IngressRepair.machine k).run u c).state≠IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k 57) ∧
        ((IngressRepair.machine k).run u c).state≠IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k 58)) ∧
      (((IngressRepair.machine k).run t c).state=(IngressRepair.machine k).reject →
        PartAEndpoint.thresholdContentWitnessRelation k a m x w=false)
end RepairedFrontier.Target
