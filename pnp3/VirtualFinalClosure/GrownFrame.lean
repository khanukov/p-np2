import VirtualFinalClosure.RawLengthGrow
import VirtualFinalClosure.WorkspaceReplay
namespace VirtualFinalClosure.GrownFrame
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",(2:Nat)),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame.mk","frameMk",3),
      ("VirtualFinalClosure.LengthFrame","VirtualFinalClosure.LengthFrame","actual_length_frame","actualFrame",1),
      ("VirtualFinalClosure.LengthFrame","VirtualFinalClosure.LengthFrame","image_lower","imageLower",1),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","protected_frame","protect",1),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","actual_width","actualWidth",1),
      ("VirtualFinalClosure.SourceLoop","VirtualFinalClosure.SourceLoop","protected_image","protectedImage",1),
      ("VirtualFinalClosure.LengthBanks","VirtualFinalClosure.LengthBanks","masked","masked",0),
      ("VirtualFinalClosure.LengthBanks","VirtualFinalClosure.LengthBanks","masked_low","maskedLow",1),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","image","image",0),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","unary","unary",0),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","lifted","lifted",0),
      ("VirtualFinalClosure.GrowDouble","VirtualFinalClosure.GrowDouble","doubled","doubled",0),
      ("VirtualFinalClosure.PaintPath","VirtualFinalClosure.PaintPath","block","block",0),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","actual_cells","actualCells",1),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","Cells.reg","cellReg",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong actual enlarged workspace frame {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual enlarged workspace frame {mod}/{key}"
private theorem enlarged_room (R n r : Nat) (nr : n ≤ R) (rr : r ≤ R) :
    3*R+2+10*r+n+7  <  tapeLength R (FixedRawLengthFence.allocation R) := by
  dsimp only [tapeLength,FixedRawLengthFence.allocation]
  nlinarith only [nr,rr,Nat.zero_le R,Nat.zero_le (R^2)]
private theorem room_lower (L n Q F : Nat) (h : L+n+1+Q+1 < F) : L+n+1 < F := by omega
private theorem index_lower (L n F i : Nat) (h : L+n+1 < F) (hi : i < L) : i ≤ F+1 := by omega
private theorem lower (A : Nat → Option Bool) (L n F r i : Nat)
    (small : i ≤ F+1) (out : ¬(L < i ∧ i < L+n+1)) :
    block (doubled A F r n) (L+1) n (some false) i=A i := by
  dsimp only [block,doubled]
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]
/-- Actual growth does not invent a clean exterior: bank0 was written by the
native copy/merge, the old workspace was erased by reset, and only the remaining
high interval is supplied by the ORIGINAL raw blank-tail theorem. -/
private theorem frame (A : Nat → Option Bool) (S L n Q F r : Nat)
    (fr : Frame A S L (L+n+1) Q F)
    (reg : ∀ i,S < i → i < L → A i=some false)
    (tail : ∀ i,F+5*r+n+7 < i → i ≤ F+10*r+n+7 → A i=none) :
    let G:=block (doubled A F r n) (L+1) n (some false)
    Frame G S L (L+n+1) Q F ∧
      (∀ i,S < i → i < L → G i=some false) ∧
      (∀ i,L < i → i < L+n+1 → G i=some false) ∧
      (∀ i,F+1 < i → i < F+2*r+2 → G i=some true) ∧
      (∀ i,F+2*r+2 ≤ i → i ≤ F+10*r+n+7 → G i=none) := by
  intro G
  obtain ⟨sl,lh,paid,room,eof,sep,right,d0,fence,register,assignment,marks,gap⟩:=fr
  have below : L+n+1 < F := by omega
  have low (i : Nat) (hi : i ≤ F+1) (out : ¬(L < i ∧ i < L+n+1)) : G i=A i:=lower A L n F r i hi out
  have assn : ∀ i,L < i → i < L+n+1 → G i=some false := by
    intro i lo hi
    dsimp only [G,block]
    rw [if_pos (by omega)]
  refine ⟨frameMk sl lh paid room ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_,?_,assn,?_,?_⟩
  · exact (low S (by omega) (by omega)).trans eof
  · exact (low L (by omega) (by omega)).trans sep
  · exact (low (L+n+1) (by omega) (by omega)).trans right
  · exact (low (F+1) le_rfl (by omega)).trans d0
  · exact (low F (by omega) (by omega)).trans fence
  · intro i lo hi
    exact ⟨false,(low i (by omega) (by omega)).trans (reg i lo hi)⟩
  · intro i lo hi
    exact ⟨false,assn i lo hi⟩
  · intro i lo hi
    exact (low i (by omega) (by omega)).trans (marks i lo hi)
  · intro i lo hi
    exact (low i (by omega) (by omega)).trans (gap i lo hi)
  · intro i lo hi
    exact (low i (by omega) (by omega)).trans (reg i lo hi)
  · intro i lo hi
    dsimp only [G,block,doubled]
    rw [if_neg (by omega),if_pos ⟨lo,hi⟩]
  · intro i lo hi
    dsimp only [G,block,doubled]
    rw [if_neg (by omega),if_neg (by omega)]
    by_cases old : i ≤ F+5*r+n+7
    · rw [if_pos ⟨lo,old⟩]
    · rw [if_neg (by omega)]
      exact tail i (by omega) hi
/-- First growth's whole enlarged frame is derived from the SAME parsed raw
source. No scratch/register/assignment installation is a caller premise. -/
private theorem actual {a m z n : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (cap : n  <  FixedRawLengthFence.capacity a m z)
    (rows : 2^n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1)
    (physical : min (9+2*z+2^n) (a+m) < a+m) :
    let S:=a+m;let R:=pairLength a m;let C:=FixedRawLengthFence.allocation R
    let L:=S+z+2;let F:=3*R+2;let r:=S-min (9+2*z+2^n) S
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared C x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let Y:=RuntimeBitLength.Target.fullImage
      (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r
    let T:=masked Y (tapeLength R C)
    let G:=block (doubled (image T F r S r) F r n) (L+1) n (some false)
    Frame G S L (L+n+1) (2^n) F ∧
      (∀ i,S < i → i < L → G i=some false) ∧
      (∀ i,L < i → i < L+n+1 → G i=some false) ∧
      (∀ i,F+1 < i → i < F+2*r+2 → G i=some true) ∧
      (∀ i,F+2*r+2 ≤ i → i ≤ F+10*r+n+7 → G i=none) ∧
      F+10*r+n+7 < tapeLength R C := by
  intro S R C L F r U V Y T G
  let A:=image T F r S r
  have sr : S ≤ R := by dsimp only [S,R,pairLength];omega
  have nr : n ≤ R:=actualWidth R S z n sr physical
  have rr : r ≤ R:=(Nat.sub_le _ _).trans sr
  have fit : F+10*r+n+7 < tapeLength R C:=enlarged_room R n r nr rr
  have oldFit : F+5*r+n+7 < tapeLength R C:=lt_of_le_of_lt (by omega) fit
  have same (i : Nat) (hi : i ≤ F+5*r+n+7) : T i=Y i:=maskedLow Y (tapeLength R C) i (lt_of_le_of_lt hi oldFit)
  obtain ⟨fr,gap,pos,short,_bank,_d1,_source⟩:=actualFrame x w gamma cap rows physical
  change L+n+1+2^n+1 < F at gap
  change r < S at short
  have below : L+n+1 < F:=room_lower L n (2^n) F gap
  obtain ⟨cells,_short,fresh⟩:=actualCells x w gamma cap rows
  change ∀ i : Fin (tapeLength R C),F < i.val → V i.val=none at fresh
  have sf : S ≤ F := by dsimp only [S,R,F,pairLength];omega
  have frT:=protect fr (by intro i _lo hi;exact same i (by omega))
  have frA : Frame A S L (L+n+1) (2^n) F:=
    protect frT (by intro i lo hi;exact protectedImage T F r S r i short lo hi)
  have reg : ∀ i,S < i → i < L → A i=some false := by
    intro i lo hi
    have low : i ≤ F+1:=index_lower L n F i below hi
    have aeq : A i=T i:=protectedImage T F r S r i short lo.le low
    have yeq : Y i=V i:=imageLower V L n F r i low (by omega)
    exact aeq.trans ((same i (by omega)).trans (yeq.trans (cellReg cells i lo hi)))
  have tail : ∀ i,F+5*r+n+7 < i → i ≤ F+10*r+n+7 → A i=none := by
    intro i lo hi
    have fi : i < tapeLength R C:=lt_of_le_of_lt hi fit
    dsimp only [A,image,unary,lifted]
    rw [if_neg (by omega),if_neg (by omega)]
    change masked Y (tapeLength R C) i=none
    rw [maskedLow Y (tapeLength R C) i fi]
    dsimp only [Y,RuntimeBitLength.Target.fullImage,CappedWorkspace.Target.image,SuffixCap.Target.image]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
    exact fresh ⟨i,fi⟩ (by change F < i;omega)
  obtain ⟨fg,rg,ag,bg,cg⟩:=frame A S L n (2^n) F r frA reg tail
  exact ⟨fg,rg,ag,bg,cg,fit⟩
#print axioms enlarged_room
#print axioms room_lower
#print axioms index_lower
#print axioms lower
#print axioms frame
#print axioms actual
end VirtualFinalClosure.GrownFrame
