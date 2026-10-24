import VirtualFinalClosure.RawPaidLength
import VirtualFinalClosure.MaskedLength
import VirtualFinalClosure.InitialWeightFrame
import VirtualFinalClosure.SeedAndWeight
namespace VirtualFinalClosure.RawFlaggedWeight
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.RawPaidLength","VirtualFinalClosure.RawPaidLength","raw_length","rawLength",(1:Nat)),
      ("VirtualFinalClosure.MaskedLength","VirtualFinalClosure.MaskedLength","actual","maskActual",1),
      ("VirtualFinalClosure.InitialWeightFrame","VirtualFinalClosure.InitialWeightFrame","actual","actualFrame",1),
      ("VirtualFinalClosure.SeedAndWeight","VirtualFinalClosure.SeedAndWeight","prepared","weight",1),
      ("VirtualFinalClosure.LengthPrefix","VirtualFinalClosure.LengthPrefix","small_le_new","smallBudget",1),
      ("VirtualFinalClosure.LengthBanks","VirtualFinalClosure.LengthBanks","masked","masked",0),
      ("VirtualFinalClosure.StreamActiveOrbit","VirtualFinalClosure.StreamActiveOrbit","bits","bits",0),
      ("VirtualFinalClosure.TableFlagMeaning","VirtualFinalClosure.TableFlagMeaning","folded","folded",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong raw all-W flag-preserving term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique raw all-W flag-preserving term {mod}/{key}"
/-- SAME original raw input, physically observed whole table and native
bitLength, seed, all k power blocks, +k/+4/final multiplication. All four real
W caps remain explicit. The actual finite table flag is preserved, rather than
an arbitrary existential tag on an old endpoint. This is a classified component
of the frozen unconditional FINAL target, not an acceptance theorem. -/
private theorem raw_weight (k : Nat) {a m n consumed z : Nat} (x : Bitstring a) (w : Bitstring m)
    (canonical : m=a+1) (header : contentHeader? (Fin.append x w)=some (n,consumed))
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (firstPhysical : z=0 ∨ 9+z < a+m) (cap : n < FixedRawLengthFence.capacity a m z)
    (rows : 2^n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1)
    (physical : min (9+2*z+2^n) (a+m) < a+m)
    (fits : bitLength n ≤ a+m-min (9+2*z+2^n) (a+m)) :
    let S:=a+m;let R:=pairLength a m;let C:=FixedRawLengthFence.allocation R
    let B:=allocation k R;let F:=3*R+2;let A:=9+2*z;let Q:=2^n
    let L:=S+z+2;let r:=S-min (A+Q) S
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared C x w z n) L n)
    let V:=Stream.Target.image U S z n A Q Q false
    let Y:=RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r
    let T:=masked Y (tapeLength R C);let Z:=AllArityBitLength.Target.seedImage T F r n
    let f:=folded (bits U (min A S) S) Q
    let c:=initialConfig (machine k) B (encodePair x w)
    ∃ (t a0 b0 : Nat) (hL : L < tapeLength R B),
      t ≤ 4194304*(R+1)^3 ∧ a0 ≤ 16*(F+5*r+n+8) ∧
      b0 ≤ 2097152*(k+1)*(n+r+1)^2*(F+5*r+n+9) ∧
      (machine k).run t c=⟨control k (tableControl k 308) ⟨8+f.val,by have h:=f.isLt;omega⟩,
        ⟨L,hL⟩,fun i=>T i.val⟩ ∧
      (∀ u,u ≤ t → ((machine k).run u c).head.val ≤ 12*(R+1)^2) ∧
      (∀ u,u ≤ a0+b0 → ((machine k).run (t+u) c).head.val ≤ L+16*(F+5*r+n+8)) ∧
      (f.val%2=1 ↔ ∀ j : Fin Q,padRead (Fin.append x w) (A+j.val)=Nat.testBit j.val 0) ∧
      ((Cursor.Target.W k n ≤ r ∧ ∃ hD : F+r+n+3 < tapeLength R B,
          (machine k).run (t+a0+b0) c=
            ⟨control k (tableControl k (430+93*k)) ⟨8+f.val,by have h:=f.isLt;omega⟩,
              ⟨F+r+n+3,hD⟩,fun i=>CappedWeight.Target.image Z L n F r 0 (n^k+k) (Cursor.Target.W k n) 0 0 i.val⟩) ∨
       ∃ v2 v3 v4 v5 d0,CappedWeight.Target.Cap k n r v2 v3 v4 v5 d0 ∧
         ∃ hD : F+1 < tapeLength R B,(machine k).run (t+a0+b0) c=
           ⟨control k (tableControl k (798+93*k)) ⟨8+f.val,by have h:=f.isLt;omega⟩,
             ⟨F+1,hD⟩,fun i=>CappedWeight.Target.image Z L n F r v2 v3 v4 v5 d0 i.val⟩):=by
  intro S R C B F A Q L r U V Y T Z f c
  obtain ⟨t,h,tp,atLength,oldHeads,meaning⟩:=rawLength k x w canonical header tag gamma firstPhysical cap rows physical
  have fitsIncoming : bitLength n ≤ a+m-Stream.Target.cursor (9+2*z) (a+m) (2^n):=fits
  simp only [if_pos fitsIncoming] at h atLength
  have actual : (machine k).run t c=
      ⟨control k (tableControl k 308) ⟨8+f.val,by have h:=f.isLt;omega⟩,
        ⟨L,h⟩,fun i=>Y i.val⟩:=by
    exact atLength
  have same : T=Y:=maskActual x w gamma cap rows
  have at308 : (machine k).run t c=
      ⟨control k (tableControl k 308) ⟨8+f.val,by have h:=f.isLt;omega⟩,
        ⟨L,h⟩,fun i=>T i.val⟩:=by
    refine actual.trans ?_
    apply Config.ext_parts
    · rfl
    · rfl
    · exact congrArg (fun V=>fun i : Fin (tapeLength R B)=>V i.val) same.symm
  obtain ⟨fr,pos,oldFit,blank,occupied,empty,power⟩:=actualFrame x w gamma cap rows physical fits
  change F+5*r+n+7 < tapeLength R C at oldFit
  have fit : F+5*r+n+7 < tapeLength R B:=by
    have budget:=smallBudget k R
    dsimp only [tapeLength] at oldFit ⊢
    omega
  let md : Fin 144:=⟨8+f.val,by have h:=f.isLt;omega⟩
  obtain ⟨a0,b0,ap,bp,_seed,_weight,heads,_first,outcome⟩:=weight k R B S L n Q F r T md
    fr pos fits blank occupied empty power fit
  refine ⟨t,a0,b0,h,tp,ap,bp,at308,oldHeads,?_,meaning,?_⟩
  · intro u hu
    rw [UniformTM.run_add,at308]
    exact heads u hu
  · have split : t+a0+b0=t+(a0+b0):=by omega
    rw [split,UniformTM.run_add,at308]
    rcases outcome with ⟨wf,run⟩|⟨v2,v3,v4,v5,d0,data,run⟩
    · exact Or.inl ⟨wf,by omega,run⟩
    · exact Or.inr ⟨v2,v3,v4,v5,d0,data,by omega,run⟩
#print axioms raw_weight
end VirtualFinalClosure.RawFlaggedWeight
