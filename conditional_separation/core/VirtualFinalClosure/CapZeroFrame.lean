import VirtualFinalClosure.CapImageFrame
import VirtualFinalClosure.RawPaidLength
import VirtualFinalClosure.LengthZeroFrame
import VirtualFinalClosure.MaskedLength
import VirtualFinalClosure.RawSourceFrame
import VirtualFinalClosure.DirtyBanks
namespace VirtualFinalClosure.CapZeroFrame
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.LengthZeroFrame","VirtualFinalClosure.LengthZeroFrame","actual","lengthFrame",(1:Nat)),
      ("VirtualFinalClosure.CapImageFrame","VirtualFinalClosure.CapImageFrame","frame","capFrame",1),
      ("VirtualFinalClosure.CapImageFrame","VirtualFinalClosure.CapImageFrame","low","capLow",1),
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
    (physical : min (9+2*z+2^n) (a+m) < a+m) (v2 v3 v4 v5 d0 : Nat) :
    let S:=a+m;let R:=pairLength a m;let C:=FixedRawLengthFence.allocation R
    let L:=S+z+2;let F:=3*R+2;let r:=S-min (9+2*z+2^n) S
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared C x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let Y:=RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r
    let T:=masked Y (tapeLength R C)
    let I:=CappedWeight.Target.image (AllArityBitLength.Target.seedImage T F r n) L n F r v2 v3 v4 v5 d0
    Frame I S L (L+n+1) (2^n) F ∧ L+n+1+2^n+1 < F ∧ 0 < r ∧ r < S ∧
      F+5*r+n+7 < tapeLength R C ∧
      (∀ j,j ≤ 6 → I (SerializedBody.delimiter F r n j)=none) ∧
      (∀ j,j < 6 → ∀ i,SerializedBody.delimiter F r n j < i →
        i < SerializedBody.delimiter F r n (j+1) → ∃ b,I i=some b) ∧
      (∀ i,¬(L < i ∧ i < L+n+1) → ¬bank F r n i → I i=V i) ∧
      (∀ i,L < i → i < L+n+1 → V i=some false) ∧
      (∀ i,9+2*z ≤ i → ∀ hi : i < S,I i=some ((Fin.append x w) ⟨i,hi⟩)):=by
  intro S R C L F r U V Y T I
  obtain ⟨fr,gap,rp,rs,fit,blank,cells,_outside,assignment,source⟩:=lengthFrame x w gamma cap rows physical
  have room : L+n+1 < F:=below_gap L n (2^n) F gap
  have same : T=Y:=maskActual x w gamma cap rows
  refine ⟨capFrame T S L n (2^n) F r v2 v3 v4 v5 d0 fr,gap,rp,rs,fit,?_,?_,?_,assignment,?_⟩
  · intro j hj
    have zero:=blank j hj
    interval_cases j <;>
      dsimp only [I,CappedWeight.Target.image,AllArityBitLength.Target.seedImage,SerializedBody.delimiter] <;>
      repeat' rw [if_neg (by omega)]
    all_goals exact zero
  · intro j hj i lo hi
    dsimp only [I,CappedWeight.Target.image,AllArityBitLength.Target.seedImage]
    split_ifs
    all_goals first | exact ⟨_,rfl⟩ | exact cells j hj i lo hi
  · intro i assn outside
    dsimp only [I,CappedWeight.Target.image,AllArityBitLength.Target.seedImage]
    dsimp only [bank] at outside
    repeat' rw [if_neg (by omega)]
    refine (congrFun same i).trans ?_
    dsimp only [Y,RuntimeBitLength.Target.fullImage,CappedWorkspace.Target.image,SuffixCap.Target.image]
    repeat' rw [if_neg (by omega)]
  · intro i lo hi
    exact (capLow T L n F r v2 v3 v4 v5 d0 i room (by dsimp only [L] at room;omega)
      (by dsimp only [L];omega)).trans (source i lo hi)

#print axioms below_gap
#print axioms actual
end VirtualFinalClosure.CapZeroFrame
