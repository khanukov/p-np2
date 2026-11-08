import VirtualFinalClosure.RawFlaggedCap
import VirtualFinalClosure.CapZeroFrame
import VirtualFinalClosure.ZeroFinished
import VirtualFinalClosure.ZeroAllMeaning
import VirtualFinalClosure.TightCapPrices
import VirtualFinalClosure.ZeroBranch
import VirtualFinalClosure.ZeroMeaning
namespace VirtualFinalClosure.RawCapZero
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.RawFlaggedCap","VirtualFinalClosure.RawFlaggedCap","raw_cap","rawCap",(1:Nat)),
      ("VirtualFinalClosure.TightCapPrices","VirtualFinalClosure.TightCapPrices","initial_price","prefixPrice",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0),
      ("VirtualFinalClosure.CapZeroFrame","VirtualFinalClosure.CapZeroFrame","actual","actualFrame",1),
      ("VirtualFinalClosure.ZeroFinished","VirtualFinalClosure.ZeroFinished","prepared","finish",1),
      ("VirtualFinalClosure.ZeroMeaning","VirtualFinalClosure.ZeroMeaning","physical_zero","physicalZero",1),
      ("VirtualFinalClosure.ZeroMeaning","VirtualFinalClosure.ZeroMeaning","mode_test","modeTest",1),
      ("VirtualFinalClosure.ZeroAllMeaning","VirtualFinalClosure.ZeroAllMeaning","relation","meaningZero",1),
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
private theorem large_room (k R : Nat) : 256*(R+1)^2 < tapeLength R (allocation k R):=by
  have kp : 1 ≤ (k+1)^4:=by
    simpa only [pow_zero] using Nat.pow_le_pow_right (by omega : 0<k+1) (show 0 ≤ 4 by decide)
  have pn : (R+1)^2 ≤ (R+1)^(k+12):=Nat.pow_le_pow_right (by omega) (by omega)
  have lower : 281474976710656*(R+1)^2 ≤ allocation k R:=by
    change _ ≤ 281474976710656*(k+1)^4*(R+1)^(k+12)
    simpa only [Nat.mul_one] using Nat.mul_le_mul (Nat.mul_le_mul_left 281474976710656 kp) pn
  have positive : 1 ≤ (R+1)^2:=by
    simpa only [pow_zero] using Nat.pow_le_pow_right (by omega : 0<R+1) (show 0 ≤ 2 by decide)
  dsimp only [tapeLength]
  omega
private theorem raw_zero (k : Nat) {a m n z : Nat} (x : Bitstring a) (w : Bitstring m)
    (canonical : m=a+1) (header : contentHeader? (Fin.append x w)=some (n,2*z+1))
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (firstPhysical : z=0 ∨ 9+z < a+m) (cap : n < FixedRawLengthFence.capacity a m z)
    (rows : 2^n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1)
    (physical : min (9+2*z+2^n) (a+m) < a+m)
    (fits : bitLength n ≤ a+m-min (9+2*z+2^n) (a+m)) :
    let S:=a+m;let R:=pairLength a m;let C:=FixedRawLengthFence.allocation R
    let B:=allocation k R;let L:=S+z+2;let F:=3*R+2;let r:=S-min (9+2*z+2^n) S
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared C x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let Y:=RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r
    let T:=masked Y (tapeLength R C);let Z:=AllArityBitLength.Target.seedImage T F r n
    let c:=initialConfig (machine k) B (encodePair x w)
    ∃ (t a0 b0 : Nat) (f : Fin 4),
      t ≤ 4194304*(R+1)^3 ∧
      a0 ≤ 16*(F+5*r+n+8) ∧ b0 ≤ 2097152*(k+1)*(n+r+1)^2*(F+5*r+n+9) ∧
      (f.val%2=1 ↔ ∀ j : Fin (2^n),padRead (Fin.append x w) (9+2*z+j.val)=Nat.testBit j.val 0) ∧
      ((Cursor.Target.W k n ≤ r ∧ ∃ hD : F+r+n+3 < tapeLength R B,
        (machine k).run (t+a0+b0) c=
          ⟨control k (tableControl k (430+93*k)) ⟨8+f.val,by have h:=f.isLt;omega⟩,⟨F+r+n+3,hD⟩,
            fun i=>CappedWeight.Target.image Z L n F r 0 (n^k+k) (Cursor.Target.W k n) 0 0 i.val⟩) ∨
       ∃ v2 v3 v4 v5 d0,CappedWeight.Target.Cap k n r v2 v3 v4 v5 d0 ∧ S < Cursor.Target.M k n z ∧
         let I:=CappedWeight.Target.image Z L n F r v2 v3 v4 v5 d0
         let bits:=fun j=>(I (S-1-j)).getD false
         ∃ (d : Nat) (hp : S-r < tapeLength R B),d ≤ 64*(R+1)^2 ∧
           (machine k).run (t+a0+b0+d) c=
             ⟨nc k 40 (modes (8+f.val) bits r),⟨S-r,hp⟩,fun i=>marked I F r S r i.val⟩ ∧
           (∀ q,q ≤ t+a0+b0+d → ((machine k).run q c).head.val ≤ 256*(R+1)^2) ∧
           ((∀ j,j < r → bits j=false) →
             ∃ (e : Nat) (hH : S+z+n+3 < tapeLength R B),
               t+a0+b0+d+e ≤ 268435456*(k+1)*(R+1)^3 ∧
               (machine k).run (t+a0+b0+d+e) c=
                 ⟨if PartAEndpoint.thresholdContentWitnessRelation k a m x w then (machine k).accept else (machine k).reject,
                   ⟨S+z+n+3,hH⟩,fun i=>Target.virtualImage V S z n F (S-r) r i.val⟩ ∧
               (∀ u,u < t+a0+b0+d+e → ((machine k).run u c).state≠(machine k).accept ∧
                 ((machine k).run u c).state≠(machine k).reject ∧
                 ∀ (mode : Fin 3) (md : Fin 144),((machine k).run u c).state≠control k
                   (CertificateGuardClosure.old k (TotalIngressClosure.old k
                     (BodyIngress.body k (SerializedBody.entry mode)))) md) ∧
               (∀ u,u ≤ t+a0+b0+d+e → ((machine k).run u c).head.val ≤ 256*(R+1)^2))) := by
  intro S R C B L F r U V Y T Z c
  obtain ⟨t,a0,b0,f,tp,ap,bp,meaning,outcome⟩:=rawCap k x w canonical header tag gamma firstPhysical cap rows physical fits
  refine ⟨t,a0,b0,f,tp,ap,bp,meaning,?_⟩
  rcases outcome with normal|⟨v2,v3,v4,v5,d0,data,virtual,d,hp,dp,marker,oldHeads,mode,seenZero⟩
  · exact Or.inl normal
  · right
    let I:=CappedWeight.Target.image Z L n F r v2 v3 v4 v5 d0
    let bits:=fun j=>(I (S-1-j)).getD false
    refine ⟨v2,v3,v4,v5,d0,data,virtual,d,hp,dp,marker,oldHeads,?_⟩
    intro zero
    obtain ⟨fr,gap,rp,rs,oldFit,blank,cells,outside,assignment,source⟩:=
      actualFrame x w gamma cap rows physical v2 v3 v4 v5 d0
    have inside:=physicalValue S z n physical
    have pe : S-r=9+2*z+2^n:=by
      change S-(S-min (9+2*z+2^n) S)=9+2*z+2^n
      rw [Nat.min_eq_left inside.le]
      exact Nat.sub_sub_self inside.le
    have lower : 9+2*z ≤ S-r:=by rw [pe];exact Nat.le_add_right _ _
    have reflected : S-(S-r)=r:=Nat.sub_sub_self (Nat.sub_le _ _)
    have zeroTyped (j : Nat) (hj : j < S-(S-r)) : (I (S-1-j)).getD false=false:=by
      rw [reflected] at hj
      exact zero j hj
    have physicalZeros:=physicalZero (Fin.append x w) I (p:=S-r)
      (by intro i lo hi;exact source i (lower.trans lo) hi) zeroTyped
    have selected : I (S-r)=some false:=by
      have atP:=source (S-r) lower (by omega)
      have falseBit:=physicalZeros (S-r) le_rfl (by omega)
      dsimp only [padRead] at falseBit
      rw [dif_pos (by omega : S-r < S)] at falseBit
      rw [falseBit] at atP
      exact atP
    have modeZero : (if bits (r-1) then 1 else 0)=(0:Nat):=
      congrArg (fun b : Bool=>if b then (1:Nat) else 0) (zero (r-1) (by omega))
    let md : Fin 144:=⟨modes (8+f.val) bits r,modeBound _ _ _ (by have h:=f.isLt;omega)⟩
    have finite : 256*(R+1)^2 < tapeLength R B:=large_room k R
    have sr : S ≤ R:=by dsimp only [S,R,pairLength];omega
    have nr : n ≤ R:=actualWidth R S z n sr physical
    have rr : r ≤ R:=(Nat.sub_le _ _).trans sr
    have fit : F+5*r+n+7 ≤ 256*(R+1)^2:=by
      dsimp only [F]
      nlinarith only [nr,rr,Nat.zero_le R,Nat.zero_le (R^2)]
    obtain ⟨e,hH,ep,done,first,heads⟩:=finish k R B (256*(R+1)^2) S L n (2^n) F r (t+a0+b0+d) I V md c
      rp rs fr gap blank cells
      (by intro i lo hi;exact ⟨_,source i (lower.trans lo.le) hi⟩)
      selected (seenZero.mpr zero) (mode.trans modeZero) assignment outside fit finite oldHeads marker
    have semantics : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true ↔ 0<n ∧ f.val%2=1:=
      meaningZero k x w f canonical header tag virtual.le (by
        intro i lo hi
        exact physicalZeros i (by rw [pe];exact lo) hi) meaning
    have test : (0<n ∧ flag md.val%2=1 ∧ bad md.val=0) ↔ PartAEndpoint.thresholdContentWitnessRelation k a m x w=true:=
      (and_congr_right fun _=>modeTest f bits r).trans semantics.symm
    have image : (fun i=>if i=L+n+1 then (if n=0 then none else some false) else Cursor.Target.scratch V F r n i)=
        Target.virtualImage V S z n F (S-r) r:=by
      have sameH : L+n+1=S+z+n+3:=by dsimp only [L];omega
      funext i
      change (if i=L+n+1 then _ else _)=if i=S+z+n+3 then _ else if S-r=S then _ else _
      rw [sameH,if_neg (by omega : S-r≠S)]
    have ePrice : e ≤ 128*(R+1)^2:=by
      have a:=Nat.sub_le F (S-r)
      have b:=Nat.sub_le F (L+n+1)
      dsimp only [F] at a b ep
      nlinarith only [ep,a,b,nr,rr,Nat.zero_le R,Nat.zero_le (R^2)]
    refine ⟨e,by dsimp only [L] at hH;omega,
      prefixPrice k R n r t a0 b0 d e nr rr tp ap bp dp ePrice,?_,first,heads⟩
    have actual : (machine k).run (t+a0+b0+d+e) c=
        ⟨if PartAEndpoint.thresholdContentWitnessRelation k a m x w then (machine k).accept else (machine k).reject,
          ⟨L+n+1,hH⟩,fun i=>if i.val=L+n+1 then (if n=0 then none else some false) else Cursor.Target.scratch V F r n i.val⟩:=by
      simpa only [test] using done
    refine actual.trans ?_
    apply Config.ext_parts
    · rfl
    · apply Fin.ext
      dsimp only [L]
      omega
    · exact congrArg (fun U=>fun i : Fin (tapeLength R B)=>U i.val) image
#print axioms large_room
#print axioms raw_zero
end VirtualFinalClosure.RawCapZero
