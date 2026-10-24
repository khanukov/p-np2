import VirtualFinalClosure.MarkerEnd
import TotalIngressClosure.LengthTotal
namespace VirtualFinalClosure.LengthFrame
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",(2:Nat)),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame.mk","frameMk",3),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","actual_cells","actualCells",1),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","Cells.arena","cell_arena",1),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","Cells.source","cell_source",1),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","Cells.eof","cell_eof",1),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","Cells.reg","cell_reg",1),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","Cells.sep","cell_sep",1),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","Cells.right","cell_right",1),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","Cells.marks","cell_marks",1),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","Cells.gap","cell_gap",1),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","Cells.fence","cell_fence",1),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","actual_gap","actualGap",1)] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong actual length-output frame interface {n}"
      logInfo m!"private-term|{n}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique actual length-output frame interface {mod}/{key}"
private theorem image_lower (V : Nat → Option Bool) (L n F r i : Nat)
    (low : i ≤ F+1) (outside : ¬(L < i ∧ i < L+n+1)) :
    RuntimeBitLength.Target.fullImage
      (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r i=V i := by
  dsimp only [RuntimeBitLength.Target.fullImage,CappedWorkspace.Target.image,SuffixCap.Target.image]
  rw [if_neg outside,if_neg (by omega),if_neg (by omega),if_neg outside,
    if_neg (by omega),if_neg (by omega)]
private theorem image_assignment (V : Nat → Option Bool) (L n F r i : Nat)
    (lo : L < i) (hi : i < L+n+1) :
    ∃ b,RuntimeBitLength.Target.fullImage
      (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r i=some b := by
  dsimp only [RuntimeBitLength.Target.fullImage]
  rw [if_pos ⟨lo,hi⟩]
  exact ⟨_,rfl⟩
private theorem source_index (S A Q r i : Nat) (inside : A+Q<S)
    (residual : r=S-(A+Q)) (hi : i<r) : A≤S-1-i := by omega
/-- All physical frame premises are derived from the real installed/stream tape;
no clean register, supplied assignment or source array is installed by this lemma. -/
private theorem actual_length_frame {a m z n : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (cap : n < FixedRawLengthFence.capacity a m z)
    (rows : 2^n ≤ FixedRawLengthFence.fencePos (PairEncoding.pairLength a m)-(a+m+z+n+3)-1)
    (physical : min (9+2*z+2^n) (a+m) < a+m) :
    let S:=a+m;let L:=S+z+2;let H:=L+n+1;let R:=PairEncoding.pairLength a m
    let F:=3*R+2;let r:=S-min (9+2*z+2^n) S
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared (FixedRawLengthFence.allocation R) x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let Y:=RuntimeBitLength.Target.fullImage
      (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r
    Frame Y S L H (2^n) F ∧ H+2^n+1 < F ∧ 0 < r ∧ r < S ∧
      (∀ i,F+1 < i → i < F+r+2 → Y i=some true) ∧ Y (F+r+2)=none ∧
      (∀ i,i < r → ∃ b,Y (S-1-i)=some b) := by
  intro S L H R F r U V Y
  obtain ⟨fr,shortFit,fresh⟩:=actualCells x w gamma cap rows
  change F+r+2 < tapeLength R (FixedRawLengthFence.allocation R) at shortFit
  change ∀ i : Fin (tapeLength R (FixedRawLengthFence.allocation R)),F < i.val → V i.val=none at fresh
  have hH : H=S+z+n+3 := by dsimp only [H,L];omega
  have arena : H+2^n < F := by
    have h:=cell_arena fr
    change S+z+n+3+2^n < F at h
    rw [←hH] at h
    exact h
  have geom : H < F := lt_of_le_of_lt (Nat.le_add_right _ _) arena
  have lower (i : Nat) (hi : i ≤ F+1) (outside : ¬(L < i ∧ i < L+n+1)) : Y i=V i :=
    image_lower V L n F r i hi outside
  have v0 : V (F+1)=none := fresh ⟨F+1,by omega⟩ (by change F < F+1;omega)
  have frame : Frame Y S L H (2^n) F := by
    refine frameMk (by dsimp only [L];omega) (by dsimp only [H];omega) (by positivity) arena ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [lower S (by dsimp only [L,H] at geom;omega) (by dsimp only [L];omega)]
      exact cell_eof fr
    · rw [lower L (by dsimp only [H] at geom;omega) (by omega)]
      exact cell_sep fr
    · rw [lower H (by omega) (by dsimp only [H];omega)]
      rw [hH]
      exact cell_right fr
    · rw [lower (F+1) le_rfl (by dsimp only [H] at geom;omega)]
      exact v0
    · rw [lower F (by omega) (by dsimp only [H] at geom;omega)]
      exact cell_fence fr
    · intro i lo hi
      rw [lower i (by omega) (by omega)]
      exact ⟨false,cell_reg fr i lo hi⟩
    · intro i lo hi
      exact image_assignment V L n F r i lo hi
    · intro i lo hi
      rw [lower i (by omega) (by intro h;have below : i < H := h.2;exact (Nat.not_lt_of_ge lo.le) below)]
      rw [hH] at lo hi
      exact cell_marks fr i lo hi
    · intro i lo hi
      rw [lower i (by omega) (by intro h;have below : i < H := h.2;exact (Nat.not_lt_of_ge ((Nat.le_add_right H (2^n)).trans lo.le)) below)]
      rw [hH] at lo
      exact cell_gap fr i lo hi
  have positive : 0 < r := by dsimp only [r];omega
  have ppos : 0 < min (9+2*z+2^n) S := by
    have pe:=Nat.min_eq_left (by omega : 9+2*z+2^n ≤ S)
    rw [pe]
    positivity
  have source : r < S := by dsimp only [r];omega
  have gap : H+2^n+1 < F := by
    rw [hH]
    exact actualGap R S z n (by dsimp only [R,S,PairEncoding.pairLength];omega) physical
  refine ⟨frame,gap,positive,source,?_,?_,?_⟩
  · intro i lo hi
    dsimp only [Y,RuntimeBitLength.Target.fullImage,CappedWorkspace.Target.image,SuffixCap.Target.image]
    rw [if_neg (by dsimp only [H] at geom;omega),if_neg (by omega),if_neg (by omega),
      if_neg (by dsimp only [H] at geom;omega),if_neg (by omega),if_pos (by omega)]
  · have freshLast : V (F+r+2)=none := fresh ⟨F+r+2,shortFit⟩ (by change F < F+r+2;omega)
    dsimp only [Y,RuntimeBitLength.Target.fullImage,CappedWorkspace.Target.image,SuffixCap.Target.image]
    rw [if_neg (by dsimp only [H] at geom;omega),if_neg (by omega),if_neg (by omega),
      if_neg (by dsimp only [H] at geom;omega),if_neg (by omega),if_neg (by omega)]
    exact freshLast
  · intro i hi
    have inside : 9+2*z+2^n < S := by omega
    have rEq : r=S-(9+2*z+2^n) := by dsimp only [r];rw [Nat.min_eq_left inside.le]
    have lo : 9+2*z ≤ S-1-i := source_index S (9+2*z) (2^n) r i inside rEq hi
    have upper : S-1-i < S := by omega
    rw [lower _ (by dsimp only [L,H] at geom;omega) (by dsimp only [L];omega)]
    exact cell_source fr _ lo upper
#print axioms image_lower
#print axioms image_assignment
#print axioms actual_length_frame
end VirtualFinalClosure.LengthFrame
