import VirtualFinalClosure.RawFlaggedLength
import VirtualFinalClosure.LengthZeroFrame
import VirtualFinalClosure.ZeroBranch
import VirtualFinalClosure.ZeroMeaning
namespace VirtualFinalClosure.RawLengthZero
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.RawFlaggedLength","VirtualFinalClosure.RawFlaggedLength","raw_marked_length","rawMarked",(1:Nat)),
      ("VirtualFinalClosure.LengthZeroFrame","VirtualFinalClosure.LengthZeroFrame","actual","actualFrame",1),
      ("VirtualFinalClosure.ZeroBranch","VirtualFinalClosure.ZeroBranch","after_prefix","finish",1),
      ("VirtualFinalClosure.ZeroMeaning","VirtualFinalClosure.ZeroMeaning","physical_zero","physicalZero",1),
      ("VirtualFinalClosure.ZeroMeaning","VirtualFinalClosure.ZeroMeaning","mode_test","modeTest",1),
      ("VirtualFinalClosure.ZeroMeaning","VirtualFinalClosure.ZeroMeaning","relation","meaningZero",1),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","actual_width","actualWidth",1),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","physical","physicalValue",1),
      ("VirtualFinalClosure.Resources","VirtualFinalClosure.Resources","bitLength_le","lengthLe",1),
      ("VirtualFinalClosure.LengthPrefix","VirtualFinalClosure.LengthPrefix","small_le_new","smallBudget",1),
      ("VirtualFinalClosure.LengthPrefix","VirtualFinalClosure.LengthPrefix","small_room","smallRoom",1),
      ("VirtualFinalClosure.MarkerState","VirtualFinalClosure.MarkerState","modes","modes",0),
      ("VirtualFinalClosure.MarkerState","VirtualFinalClosure.MarkerState","modes_bound","modeBound",1),
      ("VirtualFinalClosure.LengthBanks","VirtualFinalClosure.LengthBanks","masked","masked",0),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","image","marked",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","flag","flag",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","bad","bad",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0),
      ("SmallIngress.Runtime","SmallIngress","put","put",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong raw elln seen0 literal-FINAL term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique raw elln seen0 literal-FINAL term {mod}/{key}"
private theorem reflected (S p : Nat) (le : p ≤ S) : S-(S-p)=p:=by omega
private theorem price (R n r S L s t : Nat) (nr : n ≤ R) (rr : r ≤ R)
    (prior : s ≤ 8388608*(R+1)^3)
    (tail : t ≤ ((3*R+2)-(S-r)+5)+((3*R+2)-(L+n+1)+18*r+6*n+45)+6) :
    s+t ≤ 16777216*(R+1)^3:=by
  have a:=Nat.sub_le (3*R+2) (S-r)
  have b:=Nat.sub_le (3*R+2) (L+n+1)
  nlinarith only [prior,tail,a,b,nr,rr,Nat.zero_le R,Nat.zero_le (R^2),Nat.zero_le (R^3)]
/-- Raw-origin paid elln-cap. Its actual seen0 branch reaches the literal
ORIGINAL-rho FINAL with strict global firstness and the full frozen virtual
image. The seen1 branch is not asserted to terminate by this component; its
physical W/growth/BE continuation is proved separately. No rho premise occurs. -/
private theorem raw_zero (k : Nat) {a m n z : Nat} (x : Bitstring a) (w : Bitstring m)
    (canonical : m=a+1) (header : contentHeader? (Fin.append x w)=some (n,2*z+1))
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (firstPhysical : z=0 ∨ 9+z < a+m) (cap : n < FixedRawLengthFence.capacity a m z)
    (rows : 2^n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1)
    (physical : min (9+2*z+2^n) (a+m) < a+m)
    (shortage : a+m-min (9+2*z+2^n) (a+m) < bitLength n) :
    let S:=a+m;let R:=pairLength a m;let C:=FixedRawLengthFence.allocation R
    let B:=allocation k R;let L:=S+z+2;let F:=3*R+2;let p:=min (9+2*z+2^n) S;let r:=S-p
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared C x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let Y:=RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r
    let T:=masked Y (tapeLength R C);let bits:=fun j=>(T (S-1-j)).getD false
    let c:=initialConfig (machine k) B (encodePair x w)
    ∃ (s : Nat) (f : Fin 4) (hp : p < tapeLength R B),
      s ≤ 8388608*(R+1)^3 ∧
      (machine k).run s c=⟨nc k 40 (modes (8+f.val) bits r),⟨p,hp⟩,fun i=>marked T F r S r i.val⟩ ∧
      ((∀ j,j < r → bits j=false) →
        ∃ (t : Nat) (hH : S+z+n+3 < tapeLength R B),s+t ≤ 16777216*(R+1)^3 ∧
          (machine k).run (s+t) c=
            ⟨if PartAEndpoint.thresholdContentWitnessRelation k a m x w then (machine k).accept else (machine k).reject,
              ⟨S+z+n+3,hH⟩,fun i=>Target.virtualImage V S z n F p r i.val⟩ ∧
          (∀ u,u < s+t → ((machine k).run u c).state≠(machine k).accept ∧
            ((machine k).run u c).state≠(machine k).reject ∧
            ∀ (mode : Fin 3) (md : Fin 144),((machine k).run u c).state≠control k
              (CertificateGuardClosure.old k (TotalIngressClosure.old k
                (BodyIngress.body k (SerializedBody.entry mode)))) md) ∧
          (∀ u,u ≤ s+t → ((machine k).run u c).head.val ≤ 12*(R+1)^2)):=by
  intro S R C B L F p r U V Y T bits c
  obtain ⟨virtual,t,d,f,hp,tp,dp,total,oldHeads,marker,_markerHeads,table,mode,seenZero⟩:=
    rawMarked k x w canonical header tag gamma firstPhysical cap rows physical shortage
  have pr : p < S:=physical
  have pe : S-r=p:=reflected S p pr.le
  change S-r < tapeLength R B at hp
  have hp' : p < tapeLength R B:=pe ▸ hp
  refine ⟨t+d,f,hp',total,?_,?_⟩
  · change (machine k).run (t+d) c=⟨nc k 40 (modes (8+f.val) bits r),⟨S-r,hp⟩,fun i=>marked T F r S r i.val⟩ at marker
    refine marker.trans ?_
    apply Config.ext_parts
    · rfl
    · exact Fin.ext pe
    · rfl
  · intro zero
    obtain ⟨fr,gap,rp,rs,oldFit,blank,cells,outside,assignment,source⟩:=actualFrame x w gamma cap rows physical
    have inside:=physicalValue S z n physical
    have logicalP : p=9+2*z+2^n:=Nat.min_eq_left inside.le
    have pLower : 9+2*z ≤ p:=by rw [logicalP];exact Nat.le_add_right _ _
    have physicalZeros:=physicalZero (Fin.append x w) T (p:=p)
      (by intro i lo hi;exact source i (pLower.trans lo) hi) zero
    have selected : T (S-r)=some false:=by
      have atP:=source p pLower pr
      have falseBit:=physicalZeros p le_rfl pr
      dsimp only [padRead] at falseBit
      rw [dif_pos pr] at falseBit
      rw [falseBit] at atP
      simpa only [pe] using atP
    have pos : 0 < n:=by have width:=lengthLe n;omega
    have modeZero : (if bits (r-1) then 1 else 0)=(0:Nat):=by rw [zero (r-1) (by omega)];rfl
    let md : Fin 144:=⟨modes (8+f.val) bits r,modeBound _ _ _ (by have h:=f.isLt;omega)⟩
    have finite : 12*(R+1)^2 < tapeLength R B:=by
      have old:=smallRoom R
      have monotone:=smallBudget k R
      dsimp only [tapeLength] at old ⊢
      omega
    have sr : S ≤ R:=by dsimp only [S,R,pairLength];omega
    have nr : n ≤ R:=actualWidth R S z n sr physical
    have rr : r ≤ R:=(Nat.sub_le _ _).trans sr
    have fit : F+5*r+n+7 ≤ 12*(R+1)^2:=by
      dsimp only [F]
      nlinarith only [nr,rr,Nat.zero_le R,Nat.zero_le (R^2)]
    obtain ⟨e,hH,ep,done,first,heads⟩:=finish k R B (12*(R+1)^2) S L n (2^n) F r (t+d) T V md c
      pos rp rs fr gap blank cells
      (by intro i lo hi;exact ⟨_,source i (pLower.trans (by omega)) hi⟩)
      selected (seenZero.mpr zero) (mode.trans modeZero) assignment outside fit finite oldHeads marker
    have semantics : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true ↔ f.val%2=1:=
      meaningZero k x w f canonical header tag pos virtual.le (by
        intro i lo hi
        exact physicalZeros i (by rw [logicalP];exact lo) hi) table
    have test : (flag md.val%2=1 ∧ bad md.val=0) ↔ PartAEndpoint.thresholdContentWitnessRelation k a m x w=true:=
      (modeTest f bits r).trans semantics.symm
    have image : put (Cursor.Target.scratch V F r n) (L+n+1) (some false)=Target.virtualImage V S z n F p r:=by
      funext i
      dsimp only [put,Target.virtualImage]
      simp only [if_neg (Nat.ne_of_gt pos),if_neg (Nat.ne_of_lt pr)]
      have equal : L+n+1=S+z+n+3:=by dsimp only [L];omega
      rw [equal]
    refine ⟨e,by dsimp only [L] at hH;omega,price R n r S L (t+d) e nr rr total ep,?_,first,heads⟩
    have actual : (machine k).run (t+d+e) c=
        ⟨if PartAEndpoint.thresholdContentWitnessRelation k a m x w then (machine k).accept else (machine k).reject,
          ⟨L+n+1,hH⟩,fun i=>put (Cursor.Target.scratch V F r n) (L+n+1) (some false) i.val⟩:=by
      simpa only [test] using done
    refine actual.trans ?_
    apply Config.ext_parts
    · rfl
    · apply Fin.ext
      dsimp only [L]
      omega
    · exact congrArg (fun W=>fun i : Fin (tapeLength R B)=>W i.val) image
#print axioms reflected
#print axioms price
#print axioms raw_zero
end VirtualFinalClosure.RawLengthZero
