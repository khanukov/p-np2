import VirtualFinalClosure.RawFlaggedGrow
import VirtualFinalClosure.TightGrowth
import VirtualFinalClosure.TightPrices
import VirtualFinalClosure.GrownTail
import VirtualFinalClosure.WeightResources
namespace VirtualFinalClosure.RawFlaggedPost
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.RawFlaggedGrow","VirtualFinalClosure.RawFlaggedGrow","raw_length_growth","rawGrowth",(1:Nat)),
      ("VirtualFinalClosure.TightGrowth","VirtualFinalClosure.TightGrowth","prepared","driver",1),
      ("VirtualFinalClosure.TightPrices","VirtualFinalClosure.TightPrices","total","totalPrice",1),
      ("VirtualFinalClosure.GrownFrame","VirtualFinalClosure.GrownFrame","actual","grownFrame",1),
      ("VirtualFinalClosure.GrownTail","VirtualFinalClosure.GrownTail","actual","grownTail",1),
      ("VirtualFinalClosure.WeightResources","VirtualFinalClosure.WeightResources","room","weightRoom",1),
      ("VirtualFinalClosure.WeightResources","VirtualFinalClosure.WeightResources","heads","weightHeads",1),
      ("VirtualFinalClosure.Resources","VirtualFinalClosure.Resources","prefix_space","prefixSpace",1),
      ("VirtualFinalClosure.CapMeaning","VirtualFinalClosure.CapMeaning","length_shortage","lengthShortage",1),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","actual_width","actualWidth",1),
      ("VirtualFinalClosure.GrowEntry","VirtualFinalClosure.GrowEntry","reentry_phase","reentryPhase",1),
      ("VirtualFinalClosure.WeightCapFrame","VirtualFinalClosure.WeightCapFrame","residual","residual",0),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","image","marked",0),
      ("VirtualFinalClosure.MarkerState","VirtualFinalClosure.MarkerState","modes","modes",0),
      ("VirtualFinalClosure.LengthBanks","VirtualFinalClosure.LengthBanks","masked","masked",0),
      ("VirtualFinalClosure.GrowDouble","VirtualFinalClosure.GrowDouble","doubled","doubled",0),
      ("VirtualFinalClosure.PaintPath","VirtualFinalClosure.PaintPath","block","block",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","changeMeta","changeMeta",0),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","changed_bound","metaBound",1),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong paid raw tight-recomputation term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique paid raw tight-recomputation term {mod}/{key}"
/-- Actual raw elln-cap, physical source scan, then ALL required native
capacity growth and W/bitLengthW recomputation. The flag is the paid whole-table
flag of this SAME raw run. The zero-source arm is retained unconsumed. -/
private theorem raw_post (k : Nat) {a m n consumed z : Nat} (x : Bitstring a) (w : Bitstring m)
    (canonical : m=a+1) (header : contentHeader? (Fin.append x w)=some (n,consumed))
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (firstPhysical : z=0 ∨ 9+z < a+m) (cap : n < FixedRawLengthFence.capacity a m z)
    (rows : 2^n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1)
    (physical : min (9+2*z+2^n) (a+m) < a+m)
    (shortage : a+m-min (9+2*z+2^n) (a+m) < bitLength n) :
    let S:=a+m;let R:=pairLength a m;let C:=FixedRawLengthFence.allocation R
    let B:=allocation k R;let L:=S+z+2;let F:=3*R+2;let r:=S-min (9+2*z+2^n) S
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared C x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let Y:=RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r
    let T:=masked Y (tapeLength R C);let bits:=fun j=>(T (S-1-j)).getD false
    let G:=block (doubled (marked T F r S r) F r n) (L+1) n (some false)
    let c:=initialConfig (machine k) B (encodePair x w)
    S < Cursor.Target.M k n z ∧
    ∃ (t d : Nat) (f : Fin 4) (hp : S-r < tapeLength R B),
      t+d ≤ 8388608*(R+1)^3 ∧
      (machine k).run (t+d) c=⟨nc k 40 (modes (8+f.val) bits r),⟨S-r,hp⟩,fun j=>marked T F r S r j.val⟩ ∧
      (f.val%2=1 ↔ ∀ j : Fin (2^n),padRead (Fin.append x w) (9+2*z+j.val)=Nat.testBit j.val 0) ∧
      ((∀ j,j < r → bits j=false) ∨
        ∃ (s width : Nat) (h0 : F+1 < tapeLength R B),
          let md : Fin 144:=⟨changeMeta 4 (modes (8+f.val) bits r),metaBound 4 _⟩
          r ≤ width ∧ 0 < width ∧ Cursor.Target.W k n ≤ width ∧ width ≤ 2*Cursor.Target.W k n ∧
          s ≤ 562949953421312*(k+1)^5*(R+1)^(4*k+4) ∧
          (machine k).run s c=⟨control k (tableControl k (613+93*k)) md,⟨F+1,h0⟩,
            fun i=>residual G L n F width (bitLength (Cursor.Target.W k n)) 0 0 (Cursor.Target.W k n) 0 i.val⟩ ∧
          (∀ u,u ≤ s → ((machine k).run u c).head.val ≤ spaceBound k R)):=by
  intro S R C B L F r U V Y T bits G c
  obtain ⟨virtual,t,d,f,hp,total,marker,meaning,result⟩:=
    rawGrowth k x w canonical header tag gamma firstPhysical cap rows physical shortage
  refine ⟨virtual,t,d,f,hp,total,marker,meaning,?_⟩
  rcases result with zero|⟨e,hs,_ep,oldPrice,oldHeads,_nativeHeads,at98⟩
  · exact Or.inl zero
  · right
    let md : Fin 144:=⟨changeMeta 4 (modes (8+f.val) bits r),metaBound 4 _⟩
    obtain ⟨fr,reg,assn,_bank,_fresh,_oldFit⟩:=grownFrame x w gamma cap rows physical
    obtain ⟨_tail,identity⟩:=grownTail x w gamma cap rows physical
    have sr : S ≤ R:=by dsimp only [S,R,pairLength];omega
    have nr : n ≤ R:=actualWidth R S z n sr physical
    have rp : 0 < r:=by dsimp only [r];omega
    have short : r < Cursor.Target.W k n:=lengthShortage k n r shortage
    have fit : F+10*Cursor.Target.W k n+n+7 < tapeLength R B:=
      lt_of_le_of_lt (by dsimp only [F];omega) (weightRoom k R n nr)
    obtain ⟨a0,b0,u,j0,C0,j1,C1,h0,form0,_ellFits,_limit0,form1,weightFits,limit1,ap,bp,up,done,heads⟩:=
      driver k R B S L n (2^n) F (2*r) G md (reentryPhase _) (by omega) (by omega) fr reg assn fit
    rw [identity] at done heads
    have lower0 : 2*r ≤ C0:=by rw [form0];have pow:=Nat.two_pow_pos j0;nlinarith only [pow,Nat.zero_le r]
    have lower1 : C0 ≤ C1:=by rw [form1];have pow:=Nat.two_pow_pos j1;nlinarith only [pow,Nat.zero_le C0]
    have positive : 0 < C1:=by omega
    have price : t+d+e+a0+b0+u ≤ 562949953421312*(k+1)^5*(R+1)^(4*k+4):=
      totalPrice k R n (2*r) C0 C1 (t+d+e) a0 b0 u nr oldPrice limit1 ap bp up
    have sourceL : L ≤ 2*R+2:=by
      have inside : 9+2*z+2^n < S:=by omega
      dsimp only [L];omega
    refine ⟨t+d+e+a0+b0+u,C1,h0,by omega,positive,weightFits,limit1,price,?_,?_⟩
    · rw [show t+d+e+a0+b0+u=(t+d+e)+(a0+b0+u) by omega,UniformTM.run_add,at98]
      exact done
    · intro v hv
      by_cases early : v ≤ t+d+e
      · exact (oldHeads v early).trans (prefixSpace k R)
      · rw [show v=(t+d+e)+(v-(t+d+e)) by omega,UniformTM.run_add,at98]
        apply weightHeads k R n L _ nr sourceL
        exact (heads (v-(t+d+e)) (by omega)).trans (by omega)
#print axioms raw_post
end VirtualFinalClosure.RawFlaggedPost
