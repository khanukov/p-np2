import AllArityCounted.Runtime
import Lean
namespace AllArityCounted.Audit
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
def pin_AcceptedRaw (k : Nat) : Prop := @AllArityCounted.Target.AcceptedRaw k
theorem check_eof_body (k : Nat) {N B : Nat} (V : Nat → Option Bool) (S z n : Nat)
    (fit : S+z+n+3 < tapeLength N B) (eof : V S=none)
    (reg : ∀ i, S < i → i < S+z+2 → V i=some false) (sep : V (S+z+2)=none)
    (assn : ∀ i, S+z+2 < i → i < S+z+n+3 → ∃ b, V i=some b)
    (right : V (S+z+n+3)=none) :
    (Cursor.machine k).run (z+n+5)
      (⟨Cursor.q k 57,⟨S,by omega⟩,fun i => V i.val⟩ : Config (Cursor.machine k).stateCount N B)=
      ⟨Cursor.mReady k ⟨2,by decide⟩,⟨S+z+n+3,fit⟩,fun i => V i.val⟩ := @AllArityCounted.eof_body k N B V S z n fit eof reg sep assn right
theorem check_accepted_raw (k : Nat) :
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
        let U := Body.extend (Body.installedTape (SmallIngress.prepared
          (FixedRawLengthFence.allocation (pairLength a m)) x w z pr.2.n) (S+z+2) pr.2.n)
        let V := Stream.Target.image U S z pr.2.n (9+2*z) Q Q false
        let p := min (9+2*z+Q) S
        let r := S-p
        let c := initialConfig (AllArityCursor.machine k)
          (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
        ∃ hp : p < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)),
          (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
            ⟨Cursor.q k (if p=S then 57 else 58),⟨p,hp⟩,fun i => V i.val⟩ ∧
          (∀ u, u < t → ((AllArityCursor.machine k).run u c).state.val < 352) ∧
          (p < S → ∃ hS : S < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)),
            F+r+2 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)) ∧
            t+(2+r*(2*(F-p)+6)) ≤ 65536*(pairLength a m+1)^2 ∧
            (∀ u, u < t+(2+r*(2*(F-p)+6)) → ((AllArityCursor.machine k).run u c).state≠
              SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.rReady k)) ∧
            (AllArityCursor.machine k).run (t+(2+r*(2*(F-p)+6))) c=
              SmallIngress.producer.seqEmbedRight (Cursor.machine k)
                ⟨Cursor.rReady k,⟨S,hS⟩,fun i => SuffixCap.Target.image V F r i.val⟩ ∧
            (∀ u, u ≤ t+(2+r*(2*(F-p)+6)) →
              ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).accept ∧
              ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).reject)) ∧
          (p=S → t+(z+pr.2.n+5) ≤ 65536*(pairLength a m+1)^2 ∧
            S ≤ Cursor.Target.M k pr.2.n z ∧
            padRead (Fin.append x w) (Cursor.Target.M k pr.2.n z)=false ∧
            (AllArityCursor.machine k).run (t+(z+pr.2.n+5)) c=
              SmallIngress.producer.seqEmbedRight (Cursor.machine k)
                ⟨Cursor.mReady k ⟨2,by decide⟩,⟨S+z+pr.2.n+3,hH⟩,fun i => V i.val⟩ ∧
            (∀ u, u ≤ t+(z+pr.2.n+5) →
              ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).accept ∧
              ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).reject)) := @AllArityCounted.accepted_raw k
end AllArityCounted.Audit
#print axioms AllArityCounted.Target.AcceptedRaw
#print axioms AllArityCounted.Audit.pin_AcceptedRaw
#print axioms AllArityCounted.eof_body
#print axioms AllArityCounted.Audit.check_eof_body
#print axioms AllArityCounted.accepted_raw
#print axioms AllArityCounted.Audit.check_accepted_raw
open Lean in
run_cmd do
  let e ← getEnv
  for (n, _) in e.constants.toList do
    if n.toString.startsWith "AllArityCounted." then logInfo m!"surface|{n}"
    if (e.getModuleIdxFor? n).isNone && !n.toString.startsWith "_private." then logInfo m!"owned|{n}"
  for n in e.header.moduleNames do logInfo m!"imported|{n}"
