import IngressRepair.Machine
namespace IngressRepair.Target
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
/-- SAME producer288/Cursor machine and original allocation. Physical branch:
FIRST q201 with the complete six-bank tape. EOF: executed virtual mode2 only. -/
def AcceptedRaw (k : Nat) : Prop :=
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m),
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=true →
    ∃ pr : (Sigma fun r : Nat => PrefixInput
      (treeMCSPSearchProblem (thresholdPoly k)
        (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
      (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) r)),
      contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr ∧
      Pnp3.Models.Partial.tableLen pr.2.n ≤ a+m ∧
      ∃ (z t : Nat)
        (hH : a+m+z+pr.2.n+3 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
        FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
        t ≤ 4096*(pairLength a m+1)^2 ∧
        let S := a+m
        let F := FixedRawLengthFence.fencePos (pairLength a m)
        let Q := 2^pr.2.n
        let L := S+z+2
        let U := Body.extend (Body.installedTape (SmallIngress.prepared
          (FixedRawLengthFence.allocation (pairLength a m)) x w z pr.2.n) L pr.2.n)
        let V := Stream.Target.image U S z pr.2.n (9+2*z) Q Q false
        let p := min (9+2*z+Q) S
        let r := S-p
        let C := SuffixCap.Target.image V F r
        let c := initialConfig (IngressRepair.machine k)
          (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
        ∃ hp : p < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)),
          (IngressRepair.machine k).run t c=IngressRepair.producer.seqEmbedRight (Cursor.machine k)
            ⟨Cursor.q k (if p=S then 57 else 58),⟨p,hp⟩,fun i => V i.val⟩ ∧
          (∀ u, u < t → ((IngressRepair.machine k).run u c).state.val < 352) ∧
          (p < S → ∃ hS : S < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)),
            let d := 2+r*(2*(F-p)+6)
            (IngressRepair.machine k).run (t+d) c=IngressRepair.producer.seqEmbedRight (Cursor.machine k)
              ⟨Cursor.rReady k,⟨S,hS⟩,fun i => C i.val⟩ ∧
            (∀ u, u < t+d → ((IngressRepair.machine k).run u c).state≠
              IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.rReady k)) ∧
            ∃ (v : Nat) (hF : F+1 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
              v ≤ 128*(pr.2.n+r+1)*(F+5*r+pr.2.n+9) ∧
              t+d+v ≤ 1048576*(pairLength a m+1)^3 ∧
              F+5*r+pr.2.n+7 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)) ∧
              (IngressRepair.machine k).run (t+d+v) c=IngressRepair.producer.seqEmbedRight (Cursor.machine k)
                ⟨Cursor.q k 201,⟨F+1,hF⟩,fun i => CappedWorkspace.Target.image C L pr.2.n F r i.val⟩ ∧
              (∀ u, u < t+d+v → ((IngressRepair.machine k).run u c).state≠
                IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k 201)) ∧
              (∀ u, u ≤ t+d+v →
                ((IngressRepair.machine k).run u c).state≠(IngressRepair.machine k).accept ∧
                ((IngressRepair.machine k).run u c).state≠(IngressRepair.machine k).reject)) ∧
          (p=S → t+(z+pr.2.n+5) ≤ 1048576*(pairLength a m+1)^3 ∧
            S ≤ Cursor.Target.M k pr.2.n z ∧
            padRead (Fin.append x w) (Cursor.Target.M k pr.2.n z)=false ∧
            (IngressRepair.machine k).run (t+(z+pr.2.n+5)) c=
              IngressRepair.producer.seqEmbedRight (Cursor.machine k)
                ⟨Cursor.mReady k ⟨2,by decide⟩,⟨S+z+pr.2.n+3,hH⟩,fun i => V i.val⟩ ∧
            (∀ u, u ≤ t+(z+pr.2.n+5) →
              ((IngressRepair.machine k).run u c).state≠(IngressRepair.machine k).accept ∧
              ((IngressRepair.machine k).run u c).state≠(IngressRepair.machine k).reject))
end IngressRepair.Target

namespace IngressRepair.Target
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
/-- The original all-k stall word must now FIRST literally reject on B9216. -/
def RepairWitness (k : Nat) : Prop :=
  let x : Bitstring 11 := fun i => i.val==0 || i.val==2 || i.val==3 || i.val==6 || i.val==10
  let w : Bitstring 0 := Fin.elim0
  let c := initialConfig (IngressRepair.machine k) 9216 (encodePair x w)
  ∃ t, t ≤ 128*(pairLength 11 0+1)^2 ∧
    (IngressRepair.machine k).run t c=
      ⟨(IngressRepair.machine k).reject,⟨11,by decide⟩,
        Function.update (Function.update (FixedRawLengthFence.fencedContentTape 9216 x w)
          ⟨7,by decide⟩ none) ⟨8,by decide⟩ none⟩ ∧
    (∀ u, u<t → ((IngressRepair.machine k).run u c).state.val<139) ∧
    (∀ u, u≤t → ((IngressRepair.machine k).run u c).state≠(IngressRepair.machine k).accept) ∧
    PartAEndpoint.thresholdContentWitnessRelation k 11 0 x w=false
/-- No physical payload cell after a supported terminator: connected general negative domain. -/
def AbsentFirstPayload (k : Nat) : Prop :=
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m) (z : Nat),
    FixedContentTagGate.tagMatches (Fin.append x w)=true →
    FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z →
    0<z → a+m=9+z →
    let c := initialConfig (IngressRepair.machine k)
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
    ∃ t, t ≤ 128*(pairLength a m+1)^2 ∧
      ((IngressRepair.machine k).run t c).state=(IngressRepair.machine k).reject ∧
      (∀ u, u<t → ((IngressRepair.machine k).run u c).state.val<139) ∧
      (∀ u, u≤t → ((IngressRepair.machine k).run u c).state≠(IngressRepair.machine k).accept) ∧
      PartAEndpoint.thresholdContentWitnessRelation k a m x w=false
/-- Exact full-Config equality at every accepted raw time; no retagging. -/
def AcceptedTransport (k : Nat) : Prop :=
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m),
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=true →
    ∀ u, (IngressRepair.machine k).run u
      (initialConfig (IngressRepair.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))=
      (AllArityCursor.machine k).run u
      (initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))
end IngressRepair.Target
