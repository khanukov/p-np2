import VirtualFinalClosure.WorkspaceImage
namespace VirtualFinalClosure.CapacityImage
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",(2:Nat)),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame.mk","frameMk",3),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","protected_frame","protect",1),
      ("VirtualFinalClosure.GrowDouble","VirtualFinalClosure.GrowDouble","doubled","doubled",0),
      ("VirtualFinalClosure.PaintPath","VirtualFinalClosure.PaintPath","block","block",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong exact repeated-capacity image interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique exact repeated-capacity image interface {mod}/{key}"
/-- Fixed PRE-RUN base T. This is a pointwise specification of the physically
written bank0 and already blank exterior, not a runtime operand installation. -/
private def image (T : Nat → Option Bool) (F C : Nat) : Nat → Option Bool := fun i=>
  if F+1 < i then if i < F+C+2 then some true else none else T i
private def image_type : (Nat → Option Bool) → Nat → Nat → Nat → Option Bool:=image
private theorem low (T : Nat → Option Bool) (F C i : Nat) (hi : i ≤ F+1) : image T F C i=T i := by
  dsimp only [image]
  rw [if_neg (by omega)]
private theorem digits (T : Nat → Option Bool) (F C i : Nat) (lo : F+1 < i) (hi : i < F+C+2) : image T F C i=some true := by
  dsimp only [image]
  rw [if_pos lo,if_pos hi]
private theorem tail (T : Nat → Option Bool) (F C i : Nat) (lo : F+C+2 ≤ i) : image T F C i=none := by
  dsimp only [image]
  rw [if_pos (by omega),if_neg (by omega)]
private theorem identity (T : Nat → Option Bool) (F C : Nat)
    (digits : ∀ i,F+1 < i → i < F+C+2 → T i=some true)
    (fresh : ∀ i,F+C+2 ≤ i → T i=none) : image T F C=T := by
  funext i
  by_cases lo : F+1 < i
  · by_cases hi : i < F+C+2
    · exact (VirtualFinalClosure.CapacityImage.digits T F C i lo hi).trans (digits i lo hi).symm
    · exact (tail T F C i (by omega)).trans (fresh i (by omega)).symm
  · exact low T F C i (by omega)
private theorem lower_full (T : Nat → Option Bool) (L n F C i : Nat)
    (hi : i ≤ F+1) (out : ¬(L < i ∧ i < L+n+1)) :
    RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image (image T F C) L n F C) L n F C i=T i := by
  dsimp only [RuntimeBitLength.Target.fullImage,CappedWorkspace.Target.image]
  rw [if_neg out,if_neg (by omega),if_neg (by omega),if_neg out,if_neg (by omega)]
  exact low T F C i hi
private theorem doubled_image (T : Nat → Option Bool) (L n F C : Nat) (room : L+n+1 < F)
    (assignment : ∀ i,L < i → i < L+n+1 → T i=some false) :
    block (doubled (RuntimeBitLength.Target.fullImage
      (CappedWorkspace.Target.image (image T F C) L n F C) L n F C) F C n) (L+1) n (some false)=image T F (2*C) := by
  funext i
  by_cases assn : L < i ∧ i < L+n+1
  · dsimp only [block]
    rw [if_pos (by omega),low T F (2*C) i (by omega),assignment i assn.1 assn.2]
  · dsimp only [block]
    rw [if_neg (by omega)]
    by_cases small : i ≤ F+1
    · dsimp only [doubled]
      rw [if_neg (by omega),if_neg (by omega),lower_full T L n F C i small assn,low T F (2*C) i small]
    · by_cases bank : i < F+2*C+2
      · dsimp only [doubled,image]
        rw [if_pos (by omega),if_pos (by omega),if_pos bank]
      · dsimp only [doubled]
        rw [if_neg (by omega),tail T F (2*C) i (by omega)]
        by_cases reset : i ≤ F+5*C+n+7
        · rw [if_pos (by omega)]
        · rw [if_neg (by omega)]
          dsimp only [RuntimeBitLength.Target.fullImage,CappedWorkspace.Target.image]
          rw [if_neg assn,if_neg (by omega),if_neg (by omega),if_neg assn,if_neg (by omega)]
          exact tail T F C i (by omega)
private theorem frame (T : Nat → Option Bool) (S L n Q F C : Nat)
    (fr : Frame T S L (L+n+1) Q F) : Frame (image T F C) S L (L+n+1) Q F :=
  protect fr (by intro i _lo hi;exact low T F C i hi)
private theorem full_frame (T : Nat → Option Bool) (S L n Q F C : Nat)
    (fr : Frame T S L (L+n+1) Q F) :
    Frame (RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image (image T F C) L n F C) L n F C) S L (L+n+1) Q F := by
  obtain ⟨sl,lh,paid,room,eof,sep,right,d0,fence,reg,_assn,marks,gap⟩:=fr
  have below : L+n+1 < F:=by omega
  let Y:=RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image (image T F C) L n F C) L n F C
  have same (i : Nat) (hi : i ≤ F+1) (out : ¬(L < i ∧ i < L+n+1)) : Y i=T i:=lower_full T L n F C i hi out
  refine frameMk sl lh paid room ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact (same S (by omega) (by omega)).trans eof
  · exact (same L (by omega) (by omega)).trans sep
  · exact (same (L+n+1) (by omega) (by omega)).trans right
  · exact (same (F+1) le_rfl (by omega)).trans d0
  · exact (same F (by omega) (by omega)).trans fence
  · intro i lo hi;obtain ⟨b,cell⟩:=reg i lo hi
    exact ⟨b,(same i (by omega) (by omega)).trans cell⟩
  · intro i lo hi
    dsimp only [Y,RuntimeBitLength.Target.fullImage]
    rw [if_pos ⟨lo,hi⟩]
    exact ⟨_,rfl⟩
  · intro i lo hi;exact (same i (by omega) (by omega)).trans (marks i lo hi)
  · intro i lo hi;exact (same i (by omega) (by omega)).trans (gap i lo hi)
#print axioms image_type
#print axioms low
#print axioms digits
#print axioms tail
#print axioms identity
#print axioms lower_full
#print axioms doubled_image
#print axioms frame
#print axioms full_frame
end VirtualFinalClosure.CapacityImage
