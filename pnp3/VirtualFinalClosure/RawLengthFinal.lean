import VirtualFinalClosure.RawFlaggedGuard
import VirtualFinalClosure.RawLengthZero
import VirtualFinalClosure.GuardBranchFinish
import VirtualFinalClosure.MarkerMeaning
namespace VirtualFinalClosure.RawLengthFinal
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.RawFlaggedGuard","VirtualFinalClosure.RawFlaggedGuard","raw_guard","rawGuard",(1:Nat)),
      ("VirtualFinalClosure.RawLengthZero","VirtualFinalClosure.RawLengthZero","raw_zero","rawZero",1),
      ("VirtualFinalClosure.GuardBranchFinish","VirtualFinalClosure.GuardBranchFinish","prepared","finish",1),
      ("VirtualFinalClosure.MarkerMeaning","VirtualFinalClosure.MarkerMeaning","reentry","fields",1),
      ("VirtualFinalClosure.FinalResources","VirtualFinalClosure.FinalResources","small_price","smallPrice",1),
      ("VirtualFinalClosure.Resources","VirtualFinalClosure.Resources","prefix_space","prefixSpace",1),
      ("VirtualFinalClosure.CapMeaning","VirtualFinalClosure.CapMeaning","length_shortage","weightShort",1),
      ("VirtualFinalClosure.MarkerState","VirtualFinalClosure.MarkerState","modes","modes",0),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","image","marked",0),
      ("VirtualFinalClosure.LengthBanks","VirtualFinalClosure.LengthBanks","masked","masked",0),
      ("VirtualFinalClosure.GrowDouble","VirtualFinalClosure.GrowDouble","doubled","doubled",0),
      ("VirtualFinalClosure.PaintPath","VirtualFinalClosure.PaintPath","block","block",0),
      ("VirtualFinalClosure.WeightCapFrame","VirtualFinalClosure.WeightCapFrame","residual","residual",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","changeMeta","changeMeta",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","flag","flag",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","bad","bad",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong complete raw elln-cap FINAL term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique complete raw elln-cap FINAL {mod}/{key}"
/-- BOTH real elln-cap continuations, from the same original raw initialConfig.
The finite seen flag dispatches zero restore or native growth/BE; neither branch
has a rho, arithmetic-success, supplied tape or prepared-frame caller premise. -/
private theorem raw_final (k : Nat) {a m n z : Nat} (x : Bitstring a) (w : Bitstring m)
    (canonical : m=a+1) (header : contentHeader? (Fin.append x w)=some (n,2*z+1))
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (firstPhysical : z=0 ∨ 9+z < a+m) (cap : n < FixedRawLengthFence.capacity a m z)
    (rows : 2^n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1)
    (physical : min (9+2*z+2^n) (a+m) < a+m)
    (shortage : a+m-min (9+2*z+2^n) (a+m) < bitLength n) :
    let S:=a+m;let R:=pairLength a m;let B0:=FixedRawLengthFence.allocation R;let B:=allocation k R
    let L:=S+z+2;let F:=3*R+2;let p:=min (9+2*z+2^n) S;let r:=S-p
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared B0 x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let c:=initialConfig (machine k) B (encodePair x w)
    ∃ (t C : Nat) (hH:S+z+n+3 < tapeLength R B),
      r ≤ C ∧ C ≤ 2*(Cursor.Target.W k n+r+1) ∧ t ≤ deadline k R ∧
      (machine k).run t c=
        ⟨if PartAEndpoint.thresholdContentWitnessRelation k a m x w then (machine k).accept else (machine k).reject,
          ⟨S+z+n+3,hH⟩,fun i=>Target.virtualImage V S z n F p C i.val⟩ ∧
      (∀ u,u < t → ((machine k).run u c).state≠(machine k).accept ∧
        ((machine k).run u c).state≠(machine k).reject ∧
        ∀ (mode : Fin 3) (md : Fin 144),((machine k).run u c).state≠control k
          (CertificateGuardClosure.old k (TotalIngressClosure.old k (BodyIngress.body k (SerializedBody.entry mode)))) md) ∧
      (∀ u,u ≤ t → ((machine k).run u c).head.val ≤ spaceBound k R):=by
  intro S R B0 B L F p r U V c
  let Y:=RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r
  let A:=masked Y (tapeLength R B0)
  let reverseBits:=fun j=>(A (S-1-j)).getD false
  obtain ⟨virtual,t,d,f,hp,_markerPrice,_marker,meaning,outcome⟩:=rawGuard k x w canonical header tag gamma firstPhysical cap rows physical shortage
  rcases outcome with zero|⟨s,C,h0,positive,fits,limit,sp,_atPost,v,mm,vp,mb,flagEq,_oldDeadline,heads,branch⟩
  · obtain ⟨s,_f,_hp,_sp,_arrived,runZero⟩:=rawZero k x w canonical header tag gamma firstPhysical cap rows physical shortage
    obtain ⟨e,hH,price,done,first,bounds⟩:=runZero zero
    refine ⟨s+e,r,hH,le_rfl,by omega,smallPrice k R (s+e) ?_,done,first,?_⟩
    · exact price.trans (Nat.mul_le_mul_right _ (by omega : 16777216 ≤ 268435456*(k+1)))
    · intro u hu
      exact (bounds u hu).trans (prefixSpace k R)
  · let md:=changeMeta 4 (modes (8+f.val) reverseBits r)
    have markerFields:=fields f reverseBits r
    have actualFlag : flag mm=f.val:=flagEq.trans markerFields.1
    have zeroBad : bad md=0:=markerFields.2
    obtain ⟨e,hH,price,done,first,bounds⟩:=finish k x w canonical header tag gamma cap rows physical virtual.le
      C s v mm f positive fits limit sp vp mb actualFlag meaning heads (by
        rcases branch with ⟨valid,clean,arrived⟩|⟨invalid,dirty,e,v0,out,ep,arrived⟩
        · exact Or.inl ⟨valid,clean.trans (and_iff_right zeroBad),h0,arrived⟩
        · exact Or.inr ⟨invalid,dirty,e,bitLength (Cursor.Target.W k n)-e-1,v0,out,ep,h0,arrived⟩)
    have bigger : r < Cursor.Target.W k n:=weightShort k n r shortage
    exact ⟨s+v+e,C,hH,bigger.le.trans fits,by omega,price,done,first,bounds⟩
#print axioms raw_final
end VirtualFinalClosure.RawLengthFinal
