import VirtualFinalClosure.InitialWeightFrame
import VirtualFinalClosure.GuardLayout
namespace VirtualFinalClosure.CapImageFrame
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",2),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame.mk","frameMk",3),
      ("VirtualFinalClosure.GuardLayout","VirtualFinalClosure.GuardLayout","image_frame","zeroFrame",1),
      ("VirtualFinalClosure.InitialWeightFrame","VirtualFinalClosure.InitialWeightFrame","actual","actualFrame",1),
      ("VirtualFinalClosure.LengthFrame","VirtualFinalClosure.LengthFrame","actual_length_frame","lengthFrame",1),
      ("VirtualFinalClosure.LengthBanks","VirtualFinalClosure.LengthBanks","masked","masked",0),
      ("VirtualFinalClosure.LengthBanks","VirtualFinalClosure.LengthBanks","masked_low","maskedLow",1) ] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong original dirty-cap frame term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique original dirty-cap frame term {mod}/{key}"
private theorem low (T : Nat → Option Bool) (L n F r a b c d e i : Nat)
    (_room : L+n+1 < F) (hi : i ≤ F+1) (out : ¬(L < i ∧ i < L+n+1)) :
    CappedWeight.Target.image (AllArityBitLength.Target.seedImage T F r n) L n F r a b c d e i=T i:=by
  dsimp only [CappedWeight.Target.image,AllArityBitLength.Target.seedImage]
  rw [if_neg out,if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
/-- Every dirty original cap keeps the real source/register/tally/fence
frame. Arbitrary partially marked assignment cells remain OCCUPIED data. -/
private theorem frame (T : Nat → Option Bool) (S L n Q F r a b c d e : Nat)
    (fr : Frame T S L (L+n+1) Q F) :
    Frame (CappedWeight.Target.image (AllArityBitLength.Target.seedImage T F r n) L n F r a b c d e)
      S L (L+n+1) Q F:=by
  obtain ⟨sl,lh,qp,room,eof,sep,right,d0,fence,reg,assignment,tally,gap⟩:=fr
  have rm : L+n+1 < F:=lt_of_le_of_lt (Nat.le_add_right (L+n+1) Q) room
  have same:=low T L n F r a b c d e
  refine frameMk sl lh qp room ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact (same S rm (by omega) (by omega)).trans eof
  · exact (same L rm (by omega) (by omega)).trans sep
  · exact (same (L+n+1) rm (by omega) (by omega)).trans right
  · exact (same (F+1) rm le_rfl (by omega)).trans d0
  · exact (same F rm (by omega) (by omega)).trans fence
  · intro i lo hi
    obtain ⟨v,cell⟩:=reg i lo hi
    exact ⟨v,(same i rm (by omega) (by omega)).trans cell⟩
  · intro i lo hi
    dsimp only [CappedWeight.Target.image]
    rw [if_pos ⟨lo,hi⟩]
    exact ⟨_,rfl⟩
  · intro i lo hi
    exact (same i rm (by omega) (by omega)).trans (tally i lo hi)
  · intro i lo hi
    exact (same i rm (by omega) (by omega)).trans (gap i lo hi)
/-- SAME raw n-fits image, any one of the four genuine cap residuals: the
source counter bank0 remains exactly r TRUE marks, even when assignment is dirty. -/
private theorem actual {a m z n : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (cap : n < FixedRawLengthFence.capacity a m z)
    (rows : 2^n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1)
    (physical : min (9+2*z+2^n) (a+m) < a+m)
    (fits : bitLength n ≤ a+m-min (9+2*z+2^n) (a+m))
    (v2 v3 v4 v5 d0 : Nat) :
    let S:=a+m;let L:=S+z+2;let R:=pairLength a m;let C:=FixedRawLengthFence.allocation R
    let F:=3*R+2;let r:=S-min (9+2*z+2^n) S;let P:=F+5*r+n+7
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared C x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let Y:=RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r
    let T:=masked Y (tapeLength R C)
    let D:=CappedWeight.Target.image (AllArityBitLength.Target.seedImage T F r n) L n F r v2 v3 v4 v5 d0
    Frame D S L (L+n+1) (2^n) F ∧ L+n+1+2^n+1 < F ∧ 0 < r ∧ r < S ∧ P < tapeLength R C ∧
      (∀ i,F+1 < i → i < F+r+2 → D i=some true) ∧ D (F+r+2)=none ∧
      (∀ i,i < r → D (S-1-i)=T (S-1-i)):=by
  intro S L R C F r P U V Y T D
  obtain ⟨fr,pos,oldFit,_blanks,_occupied,_empty,_power⟩:=actualFrame x w gamma cap rows physical fits
  obtain ⟨_frame,arena,_positive,short,b0,d1,_cells⟩:=lengthFrame x w gamma cap rows physical
  change L+n+1+2^n+1 < F at arena
  change r < S at short
  have rm : L+n+1 < F:=lt_of_le_of_lt (Nat.le_add_right (L+n+1) (2^n+1))
    (by simpa only [Nat.add_assoc] using arena)
  have same (i : Nat) (hi : i ≤ P) : T i=Y i:=maskedLow Y (tapeLength R C) i (lt_of_le_of_lt hi oldFit)
  refine ⟨frame T S L n (2^n) F r v2 v3 v4 v5 d0 fr,arena,pos,short,oldFit,?_,?_,?_⟩
  · intro i lo hi
    dsimp only [D,CappedWeight.Target.image,AllArityBitLength.Target.seedImage]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),same i (by dsimp only [P];omega)]
    exact b0 i lo hi
  · dsimp only [D,CappedWeight.Target.image,AllArityBitLength.Target.seedImage]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),same _ (by dsimp only [P];omega)]
    exact d1
  · intro i hi
    exact low T L n F r v2 v3 v4 v5 d0 (S-1-i) rm (by omega) (by dsimp only [L];omega)
#print axioms low
#print axioms frame
#print axioms actual
end VirtualFinalClosure.CapImageFrame
