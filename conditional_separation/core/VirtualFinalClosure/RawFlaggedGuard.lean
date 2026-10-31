import VirtualFinalClosure.RawFlaggedPost
import VirtualFinalClosure.GuardTail
import VirtualFinalClosure.RawSourceFrame
import VirtualFinalClosure.ReadyGuardFrame
import VirtualFinalClosure.GuardResources
namespace VirtualFinalClosure.RawFlaggedGuard
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command Tactic
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.RawFlaggedPost","VirtualFinalClosure.RawFlaggedPost","raw_post","rawPost",1),
      ("VirtualFinalClosure.GuardTail","VirtualFinalClosure.GuardTail","prepared","nativeGuard",1),
      ("VirtualFinalClosure.RawSourceFrame","VirtualFinalClosure.RawSourceFrame","marked_source","rawSource",1),
      ("VirtualFinalClosure.ReadyGuardFrame","VirtualFinalClosure.ReadyGuardFrame","frame","readyFrame",1),
      ("VirtualFinalClosure.GrownFrame","VirtualFinalClosure.GrownFrame","actual","grownFrame",1),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","actual_width","actualWidth",1),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","actual_gap","actualGap",1),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","physical","physicalValue",1),
      ("VirtualFinalClosure.WeightResources","VirtualFinalClosure.WeightResources","room","weightRoom",1),
      ("VirtualFinalClosure.WeightResources","VirtualFinalClosure.WeightResources","heads","weightHeads",1),
      ("VirtualFinalClosure.GuardResources","VirtualFinalClosure.GuardResources","phase_price","phasePrice",1),
      ("VirtualFinalClosure.GuardResources","VirtualFinalClosure.GuardResources","total_price","totalPrice",1),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","image","guardImage",0),
      ("VirtualFinalClosure.GuardLayout","VirtualFinalClosure.GuardLayout","hole","hole",0),
      ("VirtualFinalClosure.GuardDriver","VirtualFinalClosure.GuardDriver","value","value",0),
      ("VirtualFinalClosure.WeightCapFrame","VirtualFinalClosure.WeightCapFrame","residual","residual",0),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","image","marked",0),
      ("VirtualFinalClosure.LengthBanks","VirtualFinalClosure.LengthBanks","masked","masked",0),
      ("VirtualFinalClosure.GrowDouble","VirtualFinalClosure.GrowDouble","doubled","doubled",0),
      ("VirtualFinalClosure.PaintPath","VirtualFinalClosure.PaintPath","block","block",0),
      ("VirtualFinalClosure.MarkerState","VirtualFinalClosure.MarkerState","modes","modes",0),
      ("VirtualFinalClosure.MarkerState","VirtualFinalClosure.MarkerState","modes_mode","modesMode",1),
      ("VirtualFinalClosure.GuardFlags","VirtualFinalClosure.GuardFlags","phase_one_mode","reentryMode",1),
      ("VirtualFinalClosure.GrowEntry","VirtualFinalClosure.GrowEntry","reentry_phase","reentryPhase",1),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","changed_bound","metaBound",1),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","source_write","sourceWrite",1),
      ("VirtualFinalClosure.Resources","VirtualFinalClosure.Resources","bitLength_le","lengthLe",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","changeMeta","changeMeta",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","mode","sourceMode",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","phase","phase",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","flag","flag",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","bad","bad",0),
      ("SmallIngress.Runtime","SmallIngress","Path.execute","execute",1),
      ("SmallIngress.Runtime","SmallIngress","put","put",0),
      ("VirtualFinalClosure.PathTrace","VirtualFinalClosure.PathTrace","through","through",1),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0) ] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | _=>9
      unless actual=kind do throwError "Wrong raw source/BE connection term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique raw source/BE connection {mod}/{key}"
private theorem reverse_index (S p : Nat) (inside : p < S) : S-1-(S-p-1)=p:=by omega
private theorem geometry_gap (R S z n : Nat) (gap : S+z+n+3+2^n+1 < 3*R+2) :
    (S+z+2)+n+1+2^n+1 < 3*R+2:=by omega
private theorem source_length (R S z n : Nat) (pair : S ≤ R) (inside : 9+2*z+2^n < S) :
    S+z+2 ≤ 2*R+2:=by
  have positive:=Nat.two_pow_pos n
  omega
private theorem phase_envelope (F C n L K : Nat) (cap : C ≤ 2*K) :
    F+5*C+n+7 ≤ L+16*(F+10*K+n+8):=by omega
/-- Actual raw prefix, all required capacity growth, native bitLength W,
AND the ENTIRE physical BE/payload/padding guard and literal return D0. Source and every bank cell are explicit
consequences of the same raw run; no runtime/source/fit/provider premise is added.
The zero-suffix fast branch remains separate and unconsumed. -/
private theorem raw_guard (k : Nat) {a m n consumed z : Nat} (x : Bitstring a) (w : Bitstring m)
    (canonical : m=a+1) (header : contentHeader? (Fin.append x w)=some (n,consumed))
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
    let T:=masked Y (tapeLength R C);let reverseBits:=fun j=>(T (S-1-j)).getD false
    let G:=block (doubled (marked T F r S r) F r n) (L+1) n (some false)
    let bits:=padRead (Fin.append x w);let W:=Cursor.Target.W k n
    let c:=initialConfig (machine k) B (encodePair x w)
    S < Cursor.Target.M k n z ∧
    ∃ (t d : Nat) (f : Fin 4) (hp : S-r < tapeLength R B),
      t+d ≤ 8388608*(R+1)^3 ∧
      (machine k).run (t+d) c=⟨nc k 40 (modes (8+f.val) reverseBits r),⟨S-r,hp⟩,fun j=>marked T F r S r j.val⟩ ∧
      (f.val%2=1 ↔ ∀ j : Fin (2^n),padRead (Fin.append x w) (9+2*z+j.val)=Nat.testBit j.val 0) ∧
      ((∀ j,j < r → reverseBits j=false) ∨
       ∃ (t0 width : Nat) (h0 : F+1 < tapeLength R B),
         let md : Fin 144:=⟨changeMeta 4 (modes (8+f.val) reverseBits r),metaBound 4 _⟩
         let I:=residual G L n F width (bitLength W) 0 0 W 0
         let J:=put I p (some (bits p))
         0 < width ∧ W ≤ width ∧ width ≤ 2*W ∧
         t0 ≤ 562949953421312*(k+1)^5*(R+1)^(4*k+4) ∧
         (machine k).run t0 c=⟨control k (tableControl k (613+93*k)) md,⟨F+1,h0⟩,fun j=>I j.val⟩ ∧
         ∃ v mm,v ≤ 1+((width+2)+(n+2))+(bitLength W+1)*(512*(width+1)^2+16*(F+width+n+8))+128*(F+width+n+8) ∧
           mm < 144 ∧ flag mm=flag md.val ∧ t0+v ≤ deadline k R ∧
           (∀ q,q ≤ t0+v → ((machine k).run q c).head.val ≤ spaceBound k R) ∧
           ((value bits S p (bitLength W) 0 ≤ W ∧
             (bad mm=0 ↔ bad md.val=0 ∧ ∀ j,min (p+bitLength W) S ≤ j → j < S → bits j=false) ∧
             (machine k).run (t0+v) c=⟨nc k 238 mm,⟨F+1,h0⟩,
               fun j=>guardImage J L n F width 0 (value bits S p (bitLength W) 0) 0 (W-value bits S p (bitLength W) 0) j.val⟩) ∨
            (W < value bits S p (bitLength W) 0 ∧ bad mm≠0 ∧
             ∃ e v0 out,e < bitLength W ∧
             (machine k).run (t0+v) c=⟨nc k 238 mm,⟨F+1,h0⟩,
               fun j=>guardImage J L n F width (bitLength W-e-1) v0 out 0 j.val⟩))) := by
  intro S R C B L F p r U V Y T reverseBits G bits W c
  obtain ⟨virtual,t,d,f,hp,total,marker,meaning,result⟩:=rawPost k x w canonical header tag gamma firstPhysical cap rows physical shortage
  refine ⟨virtual,t,d,f,hp,total,marker,meaning,?_⟩
  rcases result with zero|⟨s,C1,h0,_rLower,positive,fitsW,limit1,oldPrice,atPost,oldHeads⟩
  · exact Or.inl zero
  · right
    let md : Fin 144:=⟨changeMeta 4 (modes (8+f.val) reverseBits r),metaBound 4 _⟩
    let I:=residual G L n F C1 (bitLength W) 0 0 W 0
    let J:=put I p (some (bits p))
    have pair : S ≤ R:=by dsimp only [S,R,pairLength];omega
    have nr : n ≤ R:=actualWidth R S z n pair physical
    have fit0:=weightRoom k R n nr
    have fit : F+5*C1+n+7 < tapeLength R B:=lt_of_le_of_lt (by omega) fit0
    obtain ⟨fr,_reg,_assn,_b0,_fresh,_fit⟩:=grownFrame x w gamma cap rows physical
    obtain ⟨tf,holeG,sg⟩:=rawSource x w gamma cap physical
    obtain ⟨frI,bi,hi,idempotent,sourceI,b0,b1⟩:=readyFrame G S L n (2^n) F C1 W p fr positive physical holeG
    have source (j : Nat) (lo : p < j) (hi : j < S) : I j=some (bits j):=by
      exact (sourceI j lo hi).trans ((sg j lo hi).trans (by
        dsimp only [bits,padRead];rw [dif_pos hi]))
    have lo : 9+2*z ≤ p:=by
      have pe : p=9+2*z+2^n:=Nat.min_eq_left (physicalValue S z n physical).le
      rw [pe];exact Nat.le_add_right _ _
    have originalP : T p=some (bits p):=by
      exact (tf p lo physical).trans (by dsimp only [bits,padRead];rw [dif_pos physical])
    have mode : sourceMode md.val=(if bits p then 1 else 0):=by
      dsimp only [md]
      rw [reentryMode,modesMode _ reverseBits r (Nat.sub_pos_of_lt physical)]
      have eq : reverseBits (r-1)=bits p:=by
        dsimp only [reverseBits]
        rw [reverse_index S p physical,originalP]
        rfl
      rw [eq]
    have phaseOne : phase md.val=1:=reentryPhase _
    have gap : L+n+1+2^n+1 < F:=geometry_gap R S z n (actualGap R S z n pair physical)
    obtain ⟨a,mm,ap,mb,flagEq,done⟩:=nativeGuard k (F+5*C1+n+7) md.val S L n (2^n) F C1 W p I bits
      md.isLt phaseOne frI bi gap le_rfl physical hi fitsW ((lengthLe W).trans fitsW) source mode idempotent b0 b1
    have price : a ≤ 2147483648*(k+1)^3*(R+1)^(3*k+3):=phasePrice k R n C1 (bitLength W) a nr (by omega)
      ((lengthLe W).trans fitsW) ap
    refine ⟨s,C1,h0,positive,fitsW,limit1,oldPrice,atPost,a,mm,ap,mb,flagEq,totalPrice k R _ _ oldPrice price,?_,?_⟩
    · intro q hq
      by_cases early : q ≤ s
      · exact oldHeads q early
      · rcases done with ⟨_,_,path⟩|⟨_,_,_,_,_,_,path⟩
        all_goals
          rw [show q=(s)+(q-(s)) by omega,UniformTM.run_add,atPost]
          have bound:=(through path fit (q-(s)) (by omega))
          calc
            _ ≤ F+5*C1+n+7:=bound
            _ ≤ spaceBound k R:=weightHeads k R n L _ nr
              (source_length R S z n pair (physicalValue S z n physical))
              (phase_envelope F C1 n L (W+3*R+1) (by omega))
    · rcases done with ⟨valid,clean,path⟩|⟨invalid,badNe,ee,v0,out,ei,path⟩
      · refine Or.inl ⟨valid,clean,?_⟩
        rw [UniformTM.run_add,atPost]
        exact execute path fit
      · refine Or.inr ⟨invalid,badNe,ee,v0,out,ei,?_⟩
        rw [UniformTM.run_add,atPost]
        exact execute path fit

#print axioms reverse_index
#print axioms geometry_gap
#print axioms source_length
#print axioms phase_envelope
#print axioms raw_guard
end VirtualFinalClosure.RawFlaggedGuard
