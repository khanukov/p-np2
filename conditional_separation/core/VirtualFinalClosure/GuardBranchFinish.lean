import VirtualFinalClosure.GuardFinished
import VirtualFinalClosure.GuardFinalMeaning
import VirtualFinalClosure.GuardRestoredFrame
import VirtualFinalClosure.GrownFinalImage
import VirtualFinalClosure.FinalResources
import VirtualFinalClosure.RawSourceFrame
import VirtualFinalClosure.RawPaidLength
namespace VirtualFinalClosure.GuardBranchFinish
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.GuardFinished","VirtualFinalClosure.GuardFinished","prepared","finish",(1:Nat)),
      ("VirtualFinalClosure.GuardFinalMeaning","VirtualFinalClosure.GuardFinalMeaning","relation","guardMeaning",1),
      ("VirtualFinalClosure.GuardRestoredFrame","VirtualFinalClosure.GuardRestoredFrame","frame","restoredFrame",1),
      ("VirtualFinalClosure.GrownFinalImage","VirtualFinalClosure.GrownFinalImage","restored","restoredImage",1),
      ("VirtualFinalClosure.GrownFinalImage","VirtualFinalClosure.GrownFinalImage","high_blank","highBlank",1),
      ("VirtualFinalClosure.FinalResources","VirtualFinalClosure.FinalResources","room","finiteRoom",1),
      ("VirtualFinalClosure.FinalResources","VirtualFinalClosure.FinalResources","total","finalPrice",1),
      ("VirtualFinalClosure.Resources","VirtualFinalClosure.Resources","scratch_bound","scratchBound",1),
      ("VirtualFinalClosure.Resources","VirtualFinalClosure.Resources","bitLength_le","lengthLe",1),
      ("VirtualFinalClosure.RawSourceFrame","VirtualFinalClosure.RawSourceFrame","marked_source","rawSource",1),
      ("VirtualFinalClosure.RawPaidLength","VirtualFinalClosure.RawPaidLength","assn_false","assnFalse",1),
      ("VirtualFinalClosure.MaskedLength","VirtualFinalClosure.MaskedLength","actual","maskActual",1),
      ("VirtualFinalClosure.GrownFrame","VirtualFinalClosure.GrownFrame","actual","grownFrame",1),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","physical","physicalValue",1),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","actual_width","actualWidth",1),
      ("VirtualFinalClosure.WeightCapFrame","VirtualFinalClosure.WeightCapFrame","residual","residual",0),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","image","guardImage",0),
      ("VirtualFinalClosure.GuardDriver","VirtualFinalClosure.GuardDriver","value","value",0),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","image","marked",0),
      ("VirtualFinalClosure.LengthBanks","VirtualFinalClosure.LengthBanks","masked","masked",0),
      ("VirtualFinalClosure.GrowDouble","VirtualFinalClosure.GrowDouble","doubled","doubled",0),
      ("VirtualFinalClosure.PaintPath","VirtualFinalClosure.PaintPath","block","block",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","flag","flag",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","bad","bad",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0),
      ("SmallIngress.Runtime","SmallIngress","put","put",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong connected guard/FINAL composition term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique connected guard/FINAL composition {mod}/{key}"
/-- Both genuine BE outcomes at the SAME physical q238 are consumed. Whole
source restoration and rho interpretation are derived from the actual raw
base, never a chosen post-run tape. The raw callers supply the witnessed
prefix/time and actual guard counters; no rho/decoded-AST premise is used. -/
private theorem prepared (k : Nat) {a m n z : Nat} (x : Bitstring a) (w : Bitstring m)
    (canonical : m=a+1) (header : contentHeader? (Fin.append x w)=some (n,2*z+1))
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (cap : n < FixedRawLengthFence.capacity a m z)
    (rows : 2^n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1)
    (physical : min (9+2*z+2^n) (a+m) < a+m) (virtual : a+m ≤ Cursor.Target.M k n z)
    (C t v mm : Nat) (f : Fin 4)
    (positive : 0 < C) (fits : Cursor.Target.W k n ≤ C) (limit : C ≤ 2*Cursor.Target.W k n)
    (tp : t ≤ 562949953421312*(k+1)^5*(pairLength a m+1)^(4*k+4))
    (vp : v ≤ 1+((C+2)+(n+2))+(bitLength (Cursor.Target.W k n)+1)*(512*(C+1)^2+16*(3*pairLength a m+2+C+n+8))+128*(3*pairLength a m+2+C+n+8))
    (mb : mm < 144) (flagEq : flag mm=f.val)
    (meaning : f.val%2=1 ↔ ∀ j : Fin (2^n),padRead (Fin.append x w) (9+2*z+j.val)=Nat.testBit j.val 0) :
    let S:=a+m;let R:=pairLength a m;let B:=allocation k R;let B0:=FixedRawLengthFence.allocation R
    let L:=S+z+2;let F:=3*R+2;let p:=min (9+2*z+2^n) S;let r:=S-p;let W:=Cursor.Target.W k n
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared B0 x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let Y:=RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r
    let T:=masked Y (tapeLength R B0)
    let G:=block (doubled (marked T F r S r) F r n) (L+1) n (some false)
    let I:=residual G L n F C (bitLength W) 0 0 W 0
    let bits:=padRead (Fin.append x w);let J:=put I p (some (bits p))
    let c:=initialConfig (machine k) B (encodePair x w)
    (∀ u,u ≤ t+v → ((machine k).run u c).head.val ≤ spaceBound k R) →
    ((value bits S p (bitLength W) 0 ≤ W ∧
        (bad mm=0 ↔ ∀ j,min (p+bitLength W) S ≤ j → j < S → bits j=false) ∧
        ∃ h0:F+1 < tapeLength R B,(machine k).run (t+v) c=⟨nc k 238 mm,⟨F+1,h0⟩,
          fun i=>guardImage J L n F C 0 (value bits S p (bitLength W) 0) 0 (W-value bits S p (bitLength W) 0) i.val⟩) ∨
     (W < value bits S p (bitLength W) 0 ∧ bad mm≠0 ∧
        ∃ e a2 b2 c2,e < bitLength W ∧ ∃ h0:F+1 < tapeLength R B,
          (machine k).run (t+v) c=⟨nc k 238 mm,⟨F+1,h0⟩,fun i=>guardImage J L n F C a2 b2 c2 0 i.val⟩)) →
    ∃ (d : Nat) (hH:S+z+n+3 < tapeLength R B),t+v+d ≤ deadline k R ∧
      (machine k).run (t+v+d) c=
        ⟨if PartAEndpoint.thresholdContentWitnessRelation k a m x w then (machine k).accept else (machine k).reject,
          ⟨S+z+n+3,hH⟩,fun i=>Target.virtualImage V S z n F p C i.val⟩ ∧
      (∀ u,u < t+v+d → ((machine k).run u c).state≠(machine k).accept ∧
        ((machine k).run u c).state≠(machine k).reject ∧
        ∀ (mode : Fin 3) (md : Fin 144),((machine k).run u c).state≠control k
          (CertificateGuardClosure.old k (TotalIngressClosure.old k (BodyIngress.body k (SerializedBody.entry mode)))) md) ∧
      (∀ u,u ≤ t+v+d → ((machine k).run u c).head.val ≤ spaceBound k R):=by
  intro S R B B0 L F p r W U V Y T G I bits J c before branch
  have pair : S ≤ R:=by dsimp only [S,R,pairLength];omega
  have nr : n ≤ R:=actualWidth R S z n pair physical
  have rr : r ≤ R:=(Nat.sub_le _ _).trans pair
  have inside:=physicalValue S z n physical
  have pe : p=9+2*z+2^n:=Nat.min_eq_left inside.le
  have sr : p=S-r:=(Nat.sub_sub_self (Nat.min_le_right _ _)).symm
  obtain ⟨fr,_reg,_assn,_bank,_tail,_room⟩:=grownFrame x w gamma cap rows physical
  obtain ⟨source,hole,_suffix⟩:=rawSource x w gamma cap physical
  obtain ⟨frJ,banks,b0,b1,assignment⟩:=restoredFrame G S L n (2^n) F C W p (bits p) fr positive physical hole
  have geometry:=fr
  obtain ⟨sl,_lh,_paid,arena,_eof,_sep,_last,_start,_fence,_reg2,_assn2,_marks,_gap⟩:=geometry
  have room : L+n+1 < F:=by omega
  have rp : 0 < r:=Nat.sub_pos_of_lt physical
  have low : 9+2*z ≤ p:=by rw [pe];exact Nat.le_add_right _ _
  have cell : T p=some (bits p):=(source p low physical).trans (by dsimp only [bits,padRead];rw [dif_pos physical])
  have sameMask : T=Y:=maskActual x w gamma cap rows
  have same (i : Nat) (hi:i ≤ F+1) (out:¬(L < i ∧ i < L+n+1)) : T i=V i:=by
    refine (congrFun sameMask i).trans ?_
    dsimp only [Y,RuntimeBitLength.Target.fullImage,CappedWorkspace.Target.image,SuffixCap.Target.image]
    repeat' rw [if_neg (by omega)]
  have assnV (i : Nat) (lo:L < i) (hi:i < L+n+1) : V i=some false:=
    assnFalse U S z n (9+2*z) i lo (by dsimp only [L] at hi;omega)
  have image:=restoredImage V T S L n F r C p (bitLength W) W (bits p) room sr rp physical sl positive cell same assnV
    (highBlank x w gamma cap rows)
  have fit : F+5*C+n+7 ≤ spaceBound k R:=scratchBound k R n r C nr rr (by omega)
  have finite:=finiteRoom k R
  have semanticGuard :
      (value bits S p (bitLength W) 0 ≤ W ∧ (bad mm=0 ↔ ∀ j,min (p+bitLength W) S ≤ j → j < S → bits j=false)) ∨
      (W < value bits S p (bitLength W) 0 ∧ bad mm≠0):=by
    rcases branch with good|bad
    · exact Or.inl ⟨good.1,good.2.1⟩
    · exact Or.inr ⟨bad.1,bad.2.1⟩
  have semantic : (0 < n ∧ flag mm%2=1 ∧ bad mm=0) ↔ PartAEndpoint.thresholdContentWitnessRelation k a m x w=true:=
    guardMeaning k x w f mm canonical header tag inside virtual flagEq meaning (by simpa only [pe] using semanticGuard)
  have normalized : (fun i=>if i=L+n+1 then (if n=0 then none else some false) else Cursor.Target.scratch J F C n i)=
      Target.virtualImage V S z n F p C:=by
    funext i
    have head : L+n+1=S+z+n+3:=by dsimp only [L];omega
    change (if i=L+n+1 then _ else _)=if i=S+z+n+3 then _ else if p=S then _ else _
    rw [head,if_neg (Nat.ne_of_lt physical),congrFun image i]
  rcases branch with ⟨_valid,_clean,h0,arrived⟩|⟨_invalid,_dirty,e,a2,b2,c2,_ep,h0,arrived⟩
  all_goals
    obtain ⟨d,hH,dp,done,first,heads⟩:=finish k R B (spaceBound k R) S L n (2^n) F C _ _ _ _ (t+v) J ⟨mm,mb⟩ c
      frJ banks b0 b1 assignment fit finite before arrived
    refine ⟨d,by dsimp only [L] at hH;omega,?_,?_,first,heads⟩
    · apply finalPrice k R n C t v d nr limit tp vp ((lengthLe W).trans fits)
      have sub:=Nat.sub_le F (L+n+1)
      dsimp only [F] at dp sub
      omega
    · have actual : (machine k).run (t+v+d) c=
          ⟨if PartAEndpoint.thresholdContentWitnessRelation k a m x w then (machine k).accept else (machine k).reject,
            ⟨L+n+1,hH⟩,fun i=>if i.val=L+n+1 then (if n=0 then none else some false) else Cursor.Target.scratch J F C n i.val⟩:=by
        simpa only [semantic] using done
      refine actual.trans ?_
      apply Config.ext_parts
      · rfl
      · apply Fin.ext
        dsimp only [L]
        omega
      · exact congrArg (fun T=>fun i : Fin (tapeLength R B)=>T i.val) normalized
#print axioms prepared
end VirtualFinalClosure.GuardBranchFinish
