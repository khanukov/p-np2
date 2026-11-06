import PhysicalCallerClosure.RoundTarget
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
/-- Accepted raw normal arm, SAME parsed input and literal first BODY terminal.
Virtual/cap arms remain the original BodyIngress.Target.Raw theorem. -/
def RawFirst (k : Nat) : Prop :=
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m),
  PartAEndpoint.thresholdContentWitnessRelation k a m x w=true →
  ∃ pr : (Sigma fun q : Nat => PrefixInput
    (treeMCSPSearchProblem (thresholdPoly k)
      (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
    (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) q)),
  contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr ∧
  ∃ (z : Nat) (hH : a+m+z+pr.2.n+3 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
  FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
  let S:=a+m;let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R
  let n:=pr.2.n;let L:=S+z+2;let F:=FixedRawLengthFence.fencePos R
  let p:=min (9+2*z+2^n) S;let r:=S-p;let W:=Cursor.Target.W k n;let M:=Cursor.Target.M k n z
  let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
  let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
  let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
  let Y:=RuntimeBitLength.Target.fullImage X L n F r
  let Z:=AllArityBitLength.Target.seedImage Y F r n
  let I:=CarryWindow.Target.image (CappedWeight.Target.image Z L n F r 0 (n^k+k) W 0 0)
    F r n (n^k+k) (bitLength W) 0 0 W
  let c:=initialConfig (BodyIngress.machine k) B (encodePair x w)
  let H : Fin (tapeLength R B):=⟨S+z+n+3,hH⟩
  p < S → bitLength n ≤ r → W ≤ r →
  let bits:=SerializedBody.window (Fin.append x w) M W
  let semantics:=do
    let (circuit,tail) ← decodeCircuitFull n (bitLength n) bits
    if circuit.size ≤ n^k+k then some ((circuit.size,Pnp3.Models.Circuit.eval circuit (fun _=>false)),tail) else none
  ∃ handoff t,handoff ≤ 17179869184*(k+1)*(R+1)^6 ∧ t ≤ 1073741824*(R+1)^6 ∧
    handoff+t ≤ 34359738368*(k+1)*(R+1)^6 ∧
    (BodyIngress.machine k).run handoff c=
      ⟨BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode (Fin.append x w) M)),H,
        fun i=>SerializedBody.prepared I S M F r n (n^k+k) W i.val⟩ ∧
    (∀ u,u<handoff → ∀ mode:Fin 3,((BodyIngress.machine k).run u c).state≠
      BodyIngress.body k (SerializedBody.entry mode)) ∧
    (∀ u,u ≤ handoff+t → ((BodyIngress.machine k).run u c).state≠(BodyIngress.machine k).accept) ∧
    (∀ u,u < handoff+t → ((BodyIngress.machine k).run u c).state≠(BodyIngress.machine k).reject ∧
      ((BodyIngress.machine k).run u c).state≠BodyIngress.body k (SerializedBody.done false) ∧
      ((BodyIngress.machine k).run u c).state≠BodyIngress.body k (SerializedBody.done true)) ∧
    match semantics with
    | none=>(BodyIngress.machine k).run (handoff+t) c=
        ⟨(BodyIngress.machine k).reject,H,
          fun i=>SerializedBody.image I F r n (n^k+k) W (S-min M S) 0 0 0 0 i.val⟩
    | some ((size,b),tail)=>∃ consumed,consumed ≤ W ∧ tail=bits.drop consumed ∧
        (BodyIngress.machine k).run (handoff+t) c=
          ⟨BodyIngress.body k (SerializedBody.done b),H,
            fun i=>SerializedBody.image I F r n (n^k+k) W (S-min M S) size consumed (W-consumed) 0 i.val⟩
end PhysicalCallerClosure
