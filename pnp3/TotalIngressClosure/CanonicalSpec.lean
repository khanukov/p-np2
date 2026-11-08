import TotalIngressClosure.FirstEvents
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
open IngressAllocation (Footprint)
run_cmd do
  let env ← getEnv
  for key in ["Before"] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith "_private.TotalIngressClosure.FirstEvents." && n.toString.endsWith (".TotalIngressClosure."++key)
    match found with
    | [(n,.defnInfo ci)]=>
      logInfo m!"private-term|{n}|kind=definition|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous key) n::st.openDecls}
    | _=>throwError "Nonunique canonical first-event predicate {found.map Prod.fst}"
private def Outcome (k:Nat) {a m:Nat} (x:Bitstring a) (w:Bitstring m) (d:Nat) : Prop:=
  let N:=pairLength a m;let B0:=FixedRawLengthFence.allocation N
  let O:=BodyIngress.machine k;let c0:=initialConfig O B0 (encodePair x w)
  (((O.run d c0).state=O.reject ∧
                PartAEndpoint.thresholdContentWitnessRelation k a m x w=false) ∨
             ∃ (n z : Nat) (hH:a+m+z+n+3 < tapeLength N B0),
              FixedContentTagGate.tagMatches (Fin.append x w)=true ∧
              FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
              contentHeader? (Fin.append x w)=some (n,2*z+1) ∧
              let S:=a+m;let L:=S+z+2;let F:=FixedRawLengthFence.fencePos N
              let Q:=2^n;let p:=min (9+2*z+Q) S;let r:=S-p
              let W:=Cursor.Target.W k n;let address:=Cursor.Target.M k n z
              let H:Fin (tapeLength N B0):=⟨S+z+n+3,hH⟩
              let U:=Body.extend (Body.installedTape (SmallIngress.prepared B0 x w z n) L n)
              let V:=Stream.Target.image U S z n (9+2*z) Q Q false
              let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
              let Y:=RuntimeBitLength.Target.fullImage X L n F r
              let Z:=AllArityBitLength.Target.seedImage Y F r n
              let I:=CarryWindow.Target.image (CappedWeight.Target.image Z L n F r 0 (n^k+k) W 0 0)
                F r n (n^k+k) (bitLength W) 0 0 W
              n < FixedRawLengthFence.capacity a m z ∧ H.val+Q < F ∧
              ((p < S ∧ bitLength n ≤ r ∧ W ≤ r ∧
                  SerializedBody.delimiter F r n 12 < tapeLength N B0 ∧
                  (∀ i,address ≤ i → ∀ hi:i < S,I i=some ((Fin.append x w) ⟨i,hi⟩)) ∧
                  O.run d c0=⟨BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode (Fin.append x w) address)),H,
                    fun i=>SerializedBody.prepared I S address F r n (n^k+k) W i.val⟩) ∨
               (∃ positive : 0 < n, S ≤ address ∧
                  (∀ j:Fin W,padRead (Fin.append x w) (address+j.val)=false) ∧
                  (treeCircuitWitnessCodec (thresholdPoly k)).decode n (fun _=>false)=
                    some (Pnp3.Models.Circuit.input ⟨0,positive⟩) ∧
                  ((p=S ∧ O.run d c0=
                      ⟨BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k false)),H,
                        Function.update (fun i=>V i.val) H (some false)⟩) ∨
                   (p < S ∧
                      ((r < bitLength n) ∨
                       (bitLength n ≤ r ∧ ∃ v2 v3 v4 v5 residual,
                          CappedWeight.Target.Cap k n r v2 v3 v4 v5 residual)) ∧
                      O.run d c0=
                        ⟨BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k false)),H,
                          Function.update (fun i=>Cursor.Target.image V k S n z F i.val) H (some false)⟩)))))
private def CanonicalResult (k:Nat) {a m:Nat} (x:Bitstring a)(w:Bitstring m) : Prop:=
  let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R
  let c:=initialConfig (BodyIngress.machine k) B (encodePair x w)
  ∃ d,d ≤ 4294967296*(k+1)*(R+1)^3 ∧ Footprint (BodyIngress.machine k) (C:=B) (encodePair x w) d (12*(R+1)^2) ∧
    Before c d ∧ (∀ u,u ≤ d → ((BodyIngress.machine k).run u c).state≠(BodyIngress.machine k).accept) ∧ Outcome k x w d
end TotalIngressClosure
