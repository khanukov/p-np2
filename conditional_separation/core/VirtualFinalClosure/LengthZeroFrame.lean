import VirtualFinalClosure.RawPaidLength
import VirtualFinalClosure.MaskedLength
import VirtualFinalClosure.RawSourceFrame
import VirtualFinalClosure.DirtyBanks
namespace VirtualFinalClosure.LengthZeroFrame
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.LengthFrame","VirtualFinalClosure.LengthFrame","actual_length_frame","actualFrame",(1:Nat)),
      ("VirtualFinalClosure.MaskedLength","VirtualFinalClosure.MaskedLength","actual","maskActual",1),
      ("VirtualFinalClosure.LengthGrowFrame","VirtualFinalClosure.LengthGrowFrame","banks","banks",1),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","protected_frame","protect",1),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",2),
      ("VirtualFinalClosure.RawSourceFrame","VirtualFinalClosure.RawSourceFrame","marked_source","rawSource",1),
      ("VirtualFinalClosure.RawPaidLength","VirtualFinalClosure.RawPaidLength","assn_false","assnFalse",1),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","actual_cells","actualCells",1),
      ("VirtualFinalClosure.LengthBanks","VirtualFinalClosure.LengthBanks","masked","masked",0),
      ("VirtualReady.Raw","VirtualReady","bank","bank",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | _=>9
      unless actual=kind do throwError "Wrong raw elln-cap dirty-frame term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique raw elln-cap dirty-frame term {mod}/{key}"
private theorem below_gap (L n Q F : Nat) (h : L+n+1+Q+1 < F) : L+n+1 < F:=by omega
private theorem actual {a m z n : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (cap : n < FixedRawLengthFence.capacity a m z)
    (rows : 2^n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1)
    (physical : min (9+2*z+2^n) (a+m) < a+m) :
    let S:=a+m;let R:=pairLength a m;let C:=FixedRawLengthFence.allocation R
    let L:=S+z+2;let F:=3*R+2;let r:=S-min (9+2*z+2^n) S
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared C x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let Y:=RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r
    let T:=masked Y (tapeLength R C)
    Frame T S L (L+n+1) (2^n) F ∧ L+n+1+2^n+1 < F ∧ 0 < r ∧ r < S ∧
      F+5*r+n+7 < tapeLength R C ∧
      (∀ j,j ≤ 6 → T (SerializedBody.delimiter F r n j)=none) ∧
      (∀ j,j < 6 → ∀ i,SerializedBody.delimiter F r n j < i →
        i < SerializedBody.delimiter F r n (j+1) → ∃ b,T i=some b) ∧
      (∀ i,¬(L < i ∧ i < L+n+1) → ¬bank F r n i → T i=V i) ∧
      (∀ i,L < i → i < L+n+1 → V i=some false) ∧
      (∀ i,9+2*z ≤ i → ∀ hi : i < S,T i=some ((Fin.append x w) ⟨i,hi⟩)):=by
  intro S R C L F r U V Y T
  obtain ⟨fr,gap,rp,rs,_b0,_d1,_src⟩:=actualFrame x w gamma cap rows physical
  obtain ⟨_cells,_short,fresh⟩:=actualCells x w gamma cap rows
  obtain ⟨_tail,fit⟩:=Cursor.raw_tail_blank x w gamma cap rows
  change F+5*r+n+7 < tapeLength R C at fit
  change ∀ i : Fin (tapeLength R C),F < i.val → V i.val=none at fresh
  have same : T=Y:=maskActual x w gamma cap rows
  have below : L+n+1 < F:=below_gap L n (2^n) F gap
  obtain ⟨blank,cells⟩:=banks V L n F r below (by
    intro i lo hi
    exact fresh ⟨i,lt_of_le_of_lt hi fit⟩ lo)
  obtain ⟨source,_hole,_suffix⟩:=rawSource x w gamma cap physical
  refine ⟨protect fr (by intro i _lo _hi;exact congrFun same i),gap,rp,rs,fit,?_,?_,?_,?_,source⟩
  · intro j hj
    exact (congrFun same _).trans (blank j hj)
  · intro j hj i lo hi
    obtain ⟨b,cell⟩:=cells j hj i lo hi
    exact ⟨b,(congrFun same i).trans cell⟩
  · intro i assn outside
    refine (congrFun same i).trans ?_
    dsimp only [bank] at outside
    dsimp only [Y,RuntimeBitLength.Target.fullImage,CappedWorkspace.Target.image,SuffixCap.Target.image]
    repeat' rw [if_neg (by omega)]
  · intro i lo hi
    exact assnFalse U S z n (9+2*z) i lo (by dsimp only [L] at hi;omega)
#print axioms below_gap
#print axioms actual
end VirtualFinalClosure.LengthZeroFrame
