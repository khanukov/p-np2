import VirtualFinalClosure.GrownFrame
import VirtualFinalClosure.CapacityImage
namespace VirtualFinalClosure.GrownTail
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.GrownFrame","VirtualFinalClosure.GrownFrame","actual","actualFrame",(1:Nat)),
      ("VirtualFinalClosure.CapacityImage","VirtualFinalClosure.CapacityImage","identity","identity",1),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","actual_cells","actualCells",1),
      ("VirtualFinalClosure.LengthBanks","VirtualFinalClosure.LengthBanks","masked","masked",0),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","image","marked",0),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","unary","unary",0),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","lifted","lifted",0),
      ("VirtualFinalClosure.GrowDouble","VirtualFinalClosure.GrowDouble","doubled","doubled",0),
      ("VirtualFinalClosure.PaintPath","VirtualFinalClosure.PaintPath","block","block",0),
      ("VirtualFinalClosure.CapacityImage","VirtualFinalClosure.CapacityImage","image","capacityImage",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong actual globally blank grown exterior {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual globally blank grown exterior {mod}/{key}"
private theorem room_lower (S L n Q F : Nat) (sl : S < L) (room : L+n+1+Q < F) : S < F ∧ L+n+1 < F := by omega
/-- The blank tail is derived BOTH below and above the original finite tape:
actual raw fresh cells in the old allocation, actual ConfigExtension NONE above.
This is fixed before later growth, not a clean-scratch assumption on the caller. -/
private theorem actual {a m z n : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (cap : n < FixedRawLengthFence.capacity a m z)
    (rows : 2^n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1)
    (physical : min (9+2*z+2^n) (a+m) < a+m) :
    let S:=a+m;let R:=pairLength a m;let C:=FixedRawLengthFence.allocation R
    let L:=S+z+2;let F:=3*R+2;let r:=S-min (9+2*z+2^n) S
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared C x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let Y:=RuntimeBitLength.Target.fullImage
      (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r
    let T:=masked Y (tapeLength R C)
    let G:=block (doubled (marked T F r S r) F r n) (L+1) n (some false)
    (∀ i,F+2*r+2 ≤ i → G i=none) ∧ capacityImage G F (2*r)=G := by
  intro S R C L F r U V Y T G
  obtain ⟨fr,_reg,_assn,digits,localTail,_fit⟩:=actualFrame x w gamma cap rows physical
  obtain ⟨sl,_lh,_paid,room,_eof,_sep,_right,_d0,_ff,_rg,_as,_marks,_gap⟩:=fr
  have below:=room_lower S L n (2^n) F sl room
  obtain ⟨_cells,_short,fresh⟩:=actualCells x w gamma cap rows
  change ∀ i : Fin (tapeLength R C),F < i.val → V i.val=none at fresh
  have allTail : ∀ i,F+2*r+2 ≤ i → G i=none := by
    intro i lo
    by_cases bounded : i ≤ F+10*r+n+7
    · exact localTail i lo bounded
    · dsimp only [G,block,doubled,marked,unary,lifted]
      rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
      change masked Y (tapeLength R C) i=none
      dsimp only [masked]
      by_cases low : i < tapeLength R C
      · rw [if_pos low]
        dsimp only [Y,RuntimeBitLength.Target.fullImage,CappedWorkspace.Target.image,SuffixCap.Target.image]
        rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
        exact fresh ⟨i,low⟩ (by change F < i;omega)
      · rw [if_neg low]
  exact ⟨allTail,identity G F (2*r) digits allTail⟩
#print axioms room_lower
#print axioms actual
end VirtualFinalClosure.GrownTail
