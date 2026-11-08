import IngressAllocation.Target
namespace IngressAllocation.Target
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
def MissingPayload (k : Nat) : Prop:=
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m) (z : Nat),
    FixedContentTagGate.tagMatches (Fin.append x w)=true →
    FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z → 0 < z → a+m=9+z →
    let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R
    let c:=initialConfig (BodyIngress.machine k) B (encodePair x w)
    let large:=initialConfig (BodyIngress.machine k) (allocation k R) (encodePair x w)
    ∃ hBudget : B ≤ allocation k R,
      FixedPairParser.ConfigExtension hBudget c large ∧
      ∃ (t : Nat) (hS : a+m < tapeLength R B),t ≤ 12*(R+1)^2 ∧
        (BodyIngress.machine k).run t c=
          ⟨(BodyIngress.machine k).reject,⟨a+m,hS⟩,
            Function.update (Function.update (FixedRawLengthFence.fencedContentTape B x w)
              ⟨7,by change 7 < R+16*(R+1)^2+1;nlinarith only [Nat.zero_le R,Nat.zero_le (R^2)]⟩ none) ⟨8,by change 8 < R+16*(R+1)^2+1;nlinarith only [Nat.zero_le R,Nat.zero_le (R^2)]⟩ none⟩ ∧
        Footprint (BodyIngress.machine k) (C:=B) (encodePair x w) t (12*(R+1)^2) ∧
        MoveRoom (BodyIngress.machine k) (C:=B) (encodePair x w) t ∧
        Trace (BodyIngress.machine k) hBudget (encodePair x w) t ∧
        (BodyIngress.machine k).run t large=extendConfig hBudget ((BodyIngress.machine k).run t c) ∧
        ((BodyIngress.machine k).run t large).state=(BodyIngress.machine k).reject ∧
        (∀ u,u ≤ t → ((BodyIngress.machine k).run u large).state ≠ (BodyIngress.machine k).accept) ∧
        PartAEndpoint.thresholdContentWitnessRelation k a m x w=false
end IngressAllocation.Target
