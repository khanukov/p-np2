import VirtualFinalClosure.RawCapGuard
import VirtualFinalClosure.CapZeroFrame
import VirtualFinalClosure.ReverseSourceMeaning
import VirtualFinalClosure.RawCapZero
import VirtualFinalClosure.GuardBranchFinish
import VirtualFinalClosure.MarkerMeaning
namespace VirtualFinalClosure.RawCapFinal
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.RawCapGuard","VirtualFinalClosure.RawCapGuard","raw_guard","rawGuard",(1:Nat)),
      ("VirtualFinalClosure.CapZeroFrame","VirtualFinalClosure.CapZeroFrame","actual","actualFrame",1),
      ("VirtualFinalClosure.ReverseSourceMeaning","VirtualFinalClosure.ReverseSourceMeaning","zero_iff","zeroIff",1),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","physical","physicalValue",1),
      ("VirtualFinalClosure.TightCapPrices","VirtualFinalClosure.TightCapPrices","prefix_space","capSpace",1),
      ("VirtualFinalClosure.RawCapZero","VirtualFinalClosure.RawCapZero","raw_zero","rawZero",1),
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
private theorem raw_final (k : Nat) {a m n z : Nat} (x : Bitstring a) (w : Bitstring m)
    (canonical : m=a+1) (header : contentHeader? (Fin.append x w)=some (n,2*z+1))
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (firstPhysical : z=0 ∨ 9+z < a+m) (cap : n < FixedRawLengthFence.capacity a m z)
    (rows : 2^n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1)
    (physical : min (9+2*z+2^n) (a+m) < a+m)
    (fitsLength : bitLength n ≤ a+m-min (9+2*z+2^n) (a+m))
    (shortage : a+m-min (9+2*z+2^n) (a+m) < Cursor.Target.W k n) :
    let S:=a+m;let R:=pairLength a m;let B0:=FixedRawLengthFence.allocation R;let B:=allocation k R
    let L:=S+z+2;let F:=3*R+2;let p:=min (9+2*z+2^n) S;let r:=S-p
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared B0 x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let c:=initialConfig (machine k) B (encodePair x w)
    (∃ v2 v3 v4 v5 d0,CappedWeight.Target.Cap k n r v2 v3 v4 v5 d0) ∧
    ∃ (t C : Nat) (hH:S+z+n+3 < tapeLength R B),
      r ≤ C ∧ C ≤ 2*(Cursor.Target.W k n+r+1) ∧ t ≤ deadline k R ∧
      (machine k).run t c=
        ⟨if PartAEndpoint.thresholdContentWitnessRelation k a m x w then (machine k).accept else (machine k).reject,
          ⟨S+z+n+3,hH⟩,fun i=>Target.virtualImage V S z n F p C i.val⟩ ∧
      (∀ u,u < t → ((machine k).run u c).state≠(machine k).accept ∧
        ((machine k).run u c).state≠(machine k).reject ∧
        ∀ (mode : Fin 3) (md : Fin 144),((machine k).run u c).state≠control k
          (CertificateGuardClosure.old k (TotalIngressClosure.old k (BodyIngress.body k (SerializedBody.entry mode)))) md) ∧
      (∀ u,u ≤ t → ((machine k).run u c).head.val ≤ spaceBound k R) := by
  intro S R B0 B L F p r U V c
  let Y:=RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r
  let A:=masked Y (tapeLength R B0)
  let Z:=AllArityBitLength.Target.seedImage A F r n
  obtain ⟨t,a0,b0,f,_tp,_ap,_bp,meaning,outcome⟩:=rawGuard k x w canonical header tag gamma firstPhysical cap rows physical fitsLength
  rcases outcome with normal|⟨v2,v3,v4,v5,d0,data,virtual,d,_hp,_dp,_marker,_markerHeads,result⟩
  · exact (Nat.not_le_of_gt shortage normal.1).elim
  · refine ⟨⟨v2,v3,v4,v5,d0,data⟩,?_⟩
    let Icap:=CappedWeight.Target.image Z L n F r v2 v3 v4 v5 d0
    let reverseBits:=fun j=>(Icap (S-1-j)).getD false
    have reflected : a+m-(a+m-min (9+2*z+2^n) (a+m))=min (9+2*z+2^n) (a+m):=
      Nat.sub_sub_self (Nat.min_le_right _ _)
    have pLower : 9+2*z ≤ p:=by
      have pe : p=9+2*z+2^n:=Nat.min_eq_left (physicalValue S z n physical).le
      rw [pe];exact Nat.le_add_right _ _
    rcases result with zero|⟨s,C,h0,rLower,positive,fits,limit,sp,_atPost,v,mm,vp,mb,flagEq,_oldDeadline,heads,branch⟩
    · obtain ⟨_fr,_gap,_rp,_rs,_fit,_blank,_cells,_out,_assignment,source⟩:=actualFrame x w gamma cap rows physical v2 v3 v4 v5 d0
      have rawZeroSource : ∀ i,p ≤ i → i < S → padRead (Fin.append x w) i=false:=
        (zeroIff (Fin.append x w) p Icap (by intro i lo hi;exact source i (pLower.trans lo) hi)).mp zero
      obtain ⟨t1,a1,b1,_f1,_tp1,_ap1,_bp1,_meaning1,result1⟩:=rawZero k x w canonical header tag gamma firstPhysical cap rows physical fitsLength
      rcases result1 with normal1|⟨a2,b2,c2,d2,e2,_data1,_virtual1,d1,_hp1,_dp1,_marker1,_heads1,runZero⟩
      · exact (Nat.not_le_of_gt shortage normal1.1).elim
      · let I1:=CappedWeight.Target.image Z L n F r a2 b2 c2 d2 e2
        obtain ⟨_fr1,_gap1,_rp1,_rs1,_fit1,_blank1,_cells1,_out1,_assn1,source1⟩:=actualFrame x w gamma cap rows physical a2 b2 c2 d2 e2
        have reverseZero : ∀ j,j < r → (I1 (S-1-j)).getD false=false:=
          (zeroIff (Fin.append x w) p I1 (by intro i lo hi;exact source1 i (pLower.trans lo) hi)).mpr rawZeroSource
        obtain ⟨e,hH,price,done,first,bounds⟩:=runZero reverseZero
        refine ⟨t1+a1+b1+d1+e,r,hH,le_rfl,by omega,smallPrice k R _ price,?_,first,?_⟩
        · simpa only [reflected] using done
        · intro u hu
          exact (bounds u hu).trans (capSpace k R)
    · let md:=changeMeta 4 (modes (8+f.val) reverseBits r)
      have markerFields:=fields f reverseBits r
      have actualFlag : flag mm=f.val:=flagEq.trans markerFields.1
      have zeroBad : bad md=0:=markerFields.2
      obtain ⟨e,hH,price,done,first,bounds⟩:=finish k x w canonical header tag gamma cap rows physical virtual.le
        C s v mm f positive fits limit sp vp mb actualFlag meaning heads (by
          rcases branch with ⟨valid,clean,arrived⟩|⟨invalid,dirty,e,v0,out,ep,arrived⟩
          · refine Or.inl ⟨?_,?_,h0,?_⟩
            · simpa only [reflected] using valid
            · simpa only [reflected] using clean.trans (and_iff_right zeroBad)
            · simpa only [reflected] using arrived
          · refine Or.inr ⟨?_,dirty,e,bitLength (Cursor.Target.W k n)-e-1,v0,out,ep,h0,?_⟩
            · simpa only [reflected] using invalid
            · simpa only [reflected] using arrived)
      exact ⟨s+v+e,C,hH,rLower,by omega,price,done,first,bounds⟩
#print axioms raw_final
end VirtualFinalClosure.RawCapFinal
