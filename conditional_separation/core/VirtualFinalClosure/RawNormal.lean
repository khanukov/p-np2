import VirtualFinalClosure.OldNormal
import VirtualFinalClosure.NormalRun
namespace VirtualFinalClosure.RawNormal
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("VirtualFinalClosure.OldNormal","VirtualFinalClosure.OldNormal","raw_normal","oldNormal"),
      ("VirtualFinalClosure.NormalRun","VirtualFinalClosure.NormalRun","normal_prefix","normalPrefix"),
      ("VirtualFinalClosure.NormalImage","VirtualFinalClosure.NormalImage","high_blank","imageHigh"),
      ("VirtualFinalClosure.NormalImage","VirtualFinalClosure.NormalImage","extended_tape","extendTape"),
      ("IngressAllocation.Geometry","IngressAllocation","old_le_new","bodyBudget"),
      ("VirtualFinalClosure.Resources","VirtualFinalClosure.Resources","old_le_new","oldNew")] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,.thmInfo ci)]=>
      logInfo m!"private-term|{name}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique complete normal raw/elastic component {mod}/{key}"
private theorem tape_mono {N C B : Nat} (h:C ≤ B) : tapeLength N C ≤ tapeLength N B:=by
  dsimp only [tapeLength]
  omega
/-- Literal raw input through the exact guard and all normal ingress rows on
THIS frozen elastic table. Every prefix has the actual varying finite flag;
the final native row resets8 and returns the unchanged complete BODY ABI. -/
private theorem raw_normal (k : Nat) {a m n z : Nat} (x : Bitstring a) (w : Bitstring m)
    (canonical:m=a+1) (header:contentHeader? (Fin.append x w)=some (n,2*z+1))
    (tag:FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (firstPhysical:z=0 ∨ 9+z < a+m) (cap:n < FixedRawLengthFence.capacity a m z)
    (rows:2^n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1)
    (physical:min (9+2*z+2^n) (a+m) < a+m)
    (ellFits:bitLength n ≤ a+m-min (9+2*z+2^n) (a+m))
    (wFits:Cursor.Target.W k n ≤ a+m-min (9+2*z+2^n) (a+m)) :
    let S:=a+m;let R:=pairLength a m;let B0:=FixedRawLengthFence.allocation R
    let C:=CertificateGuardClosure.allocation k R;let B:=allocation k R;let O:=CertificateGuardClosure.machine k
    let L:=S+z+2;let F:=3*R+2;let p:=min (9+2*z+2^n) S;let r:=S-p;let W:=Cursor.Target.W k n;let g:=n^k+k
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared B0 x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
    let Y:=RuntimeBitLength.Target.fullImage X L n F r;let Z:=AllArityBitLength.Target.seedImage Y F r n
    let I:=CarryWindow.Target.image (CappedWeight.Target.image Z L n F r 0 g W 0 0) F r n g (bitLength W) 0 0 W
    let mode:=SerializedBody.sourceMode (Fin.append x w) (Cursor.Target.M k n z)
    let old:=initialConfig O C (encodePair x w);let c:=initialConfig (machine k) B (encodePair x w)
    ∃ (t:Nat) (hH:S+z+n+3 < tapeLength R B) (h:C ≤ B),t ≤ CertificateGuardClosure.deadline k R ∧
      SerializedBody.delimiter F r n 12 < tapeLength R B ∧
      (∀ i,Cursor.Target.M k n z ≤ i → ∀ hi:i < S,I i=some ((Fin.append x w) ⟨i,hi⟩)) ∧
      (∀ u,u ≤ t → ∃ flag:Fin 144,(machine k).run u c=config k flag (IngressAllocation.extendConfig h (O.run u old))) ∧
      (machine k).run t c=⟨control k (CertificateGuardClosure.old k (TotalIngressClosure.old k
        (BodyIngress.body k (SerializedBody.entry mode)))) ⟨8,by decide⟩,
          ⟨S+z+n+3,hH⟩,fun i=>SerializedBody.prepared I S (Cursor.Target.M k n z) F r n g W i.val⟩ ∧
      (∀ u,u < t → ((machine k).run u c).state≠(machine k).accept ∧
        ((machine k).run u c).state≠(machine k).reject ∧
        ∀ (j:Fin 3) (flag:Fin 144),((machine k).run u c).state≠control k
          (CertificateGuardClosure.old k (TotalIngressClosure.old k (BodyIngress.body k (SerializedBody.entry j)))) flag) ∧
      (∀ u,u ≤ t → ((machine k).run u c).head.val ≤ 12*(R+1)^2):=by
  intro S R B0 C B O L F p r W g U V X Y Z I mode old c
  obtain ⟨t,hH,tp,fit,source,atBody,first,heads⟩:=oldNormal k x w canonical header tag gamma firstPhysical cap rows physical ellFits wFits
  obtain ⟨every,final,safe,newHeads⟩:=normalPrefix k R t (encodePair x w) mode heads (congrArg (fun q=>q.state) atBody) first
  have budget:C ≤ B:=oldNew k R
  have small:B0 ≤ C:=bodyBudget k R
  have blank (i:Nat) (hi:tapeLength R C ≤ i) :
      SerializedBody.prepared I S (Cursor.Target.M k n z) F r n g W i=none:=by
    apply imageHigh k x w gamma cap rows fit i
    exact (tape_mono small).trans hi
  have hHB : S+z+n+3 < tapeLength R B:=by
    exact hH.trans_le (tape_mono budget)
  have whole : IngressAllocation.extendConfig budget (O.run t old)=
      ⟨CertificateGuardClosure.old k (TotalIngressClosure.old k (BodyIngress.body k (SerializedBody.entry mode))),
        ⟨S+z+n+3,hHB⟩,fun i=>SerializedBody.prepared I S (Cursor.Target.M k n z) F r n g W i.val⟩:=by
    rw [atBody]
    exact extendTape budget _ _ _ blank
  refine ⟨t,hHB,budget,tp,?_,source,every,?_,safe,newHeads⟩
  · exact fit.trans_le (tape_mono (small.trans budget))
  · exact final.trans (congrArg (fun q=>config k ⟨8,by decide⟩ q) whole)
#print axioms tape_mono
#print axioms raw_normal
end VirtualFinalClosure.RawNormal
