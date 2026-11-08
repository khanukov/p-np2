import VirtualFinalClosure.GuardImage
import VirtualFinalClosure.Geometry
namespace VirtualFinalClosure.GuardLayout
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("PostWeight.Kernel","PostWeight","Banks","Banks",2),
      ("PostWeight.Kernel","PostWeight","D","oldD",0),
      ("PostWeight.Kernel","PostWeight","Banks.mk","banksMk",3),
      ("PostWeight.Kernel","PostWeight","Banks.room","room",1),
      ("PostWeight.Kernel","PostWeight","Banks.blank","bankBlank",1),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",2),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame.mk","frameMk",3),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","protected_frame","protect",1),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","image","image",0),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","source_write","sourceWrite",1),
      ("SmallIngress.Runtime","SmallIngress","put","put",0) ] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong exact native guard image interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique exact native guard image interface {mod}/{key}"
/-- Exact source hole, fixed BEFORE execution. Logical EOF has no physical hole. -/
private def hole (T : Nat → Option Bool) (h S : Nat) : Nat → Option Bool:=
  if h < S then put T h none else T
private def hole_type : (Nat → Option Bool) → Nat → Nat → Nat → Option Bool:=hole
private theorem hole_high (T : Nat → Option Bool) (h S i : Nat) (hi : S ≤ i) : hole T h S i=T i := by
  dsimp only [hole]
  split_ifs with inside
  · dsimp only [put];rw [if_neg (by omega)]
  · rfl
private theorem image_low (T : Nat → Option Bool) (L n F width a b c d i : Nat)
    (room : L+n+1 < F) (low : i ≤ L) : image T L n F width a b c d i=T i := by
  dsimp only [image,CappedWeight.Target.image]
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
private theorem image_frame {T : Nat → Option Bool} {S L n Q F width : Nat}
    (fr : Frame T S L (L+n+1) Q F) (a b c d : Nat) :
    Frame (image T L n F width a b c d) S L (L+n+1) Q F := by
  obtain ⟨sl,lh,qp,room,s0,l0,h0,f0,ff,register,assignment,tally,gap⟩:=fr
  have same (i : Nat) (low : i ≤ F+1) (out : ¬(L < i ∧ i < L+n+1)) :
      image T L n F width a b c d i=T i:=by
    dsimp only [image,CappedWeight.Target.image]
    rw [if_neg out,if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  refine frameMk sl lh qp room ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact (same S (by omega) (by omega)).trans s0
  · exact (same L (by omega) (by omega)).trans l0
  · exact (same (L+n+1) (by omega) (by omega)).trans h0
  · exact (same (F+1) le_rfl (by omega)).trans f0
  · exact (same F (by omega) (by omega)).trans ff
  · intro i lo hi
    obtain ⟨v,hv⟩:=register i lo hi
    exact ⟨v,(same i (by omega) (by omega)).trans hv⟩
  · intro i lo hi
    refine ⟨false,?_⟩
    dsimp only [image,CappedWeight.Target.image]
    rw [if_pos ⟨lo,hi⟩]
    exact congrArg some (decide_eq_false (by omega))
  · intro i lo hi
    exact (same i (by omega) (by omega)).trans (tally i lo hi)
  · intro i lo hi
    exact (same i (by omega) (by omega)).trans (gap i lo hi)
private theorem hole_frame {T : Nat → Option Bool} {S L n Q F : Nat}
    (fr : Frame T S L (L+n+1) Q F) (h : Nat) :
    Frame (hole T h S) S L (L+n+1) Q F :=
  protect fr (by intro i lo _hi;exact hole_high T h S i lo)
private theorem hole_banks {T : Nat → Option Bool} {S L n F width : Nat}
    (fr : Banks T L n F width) (sl : S < L) (h : Nat) : Banks (hole T h S) L n F width := by
  have rm:=room fr
  refine banksMk rm ?_
  intro j hj
  interval_cases j
  all_goals rw [hole_high T h S _ (by dsimp only [oldD];omega)]
  all_goals exact bankBlank fr _ (by omega)
private theorem exterior_banks {T U : Nat → Option Bool} {L n F width : Nat}
    (fr : Banks T L n F width) (same : ∀ i,F < i → U i=T i) : Banks U L n F width := by
  refine banksMk (room fr) ?_
  intro j hj
  interval_cases j
  all_goals rw [same _ (by dsimp only [oldD];omega)]
  all_goals exact bankBlank fr _ (by omega)
private theorem hole_bank0 (T : Nat → Option Bool) (S L n F width h : Nat)
    (room : L+n+1 < F) (sl : S < L)
    (occupied : ∀ i,F+1 < i → i < F+width+2 → ∃ v,T i=some v) :
    ∀ i,F+1 < i → i < F+width+2 → ∃ v,hole T h S i=some v := by
  intro i lo hi
  rw [hole_high T h S i (by omega)]
  exact occupied i lo hi
private theorem hole_bank1 (T : Nat → Option Bool) (S L n F width h : Nat)
    (room : L+n+1 < F) (sl : S < L)
    (occupied : ∀ i,F+width+2 < i → i < F+width+n+3 → ∃ v,T i=some v) :
    ∀ i,F+width+2 < i → i < F+width+n+3 → ∃ v,hole T h S i=some v := by
  intro i lo hi
  rw [hole_high T h S i (by omega)]
  exact occupied i lo hi
private theorem restore_hole (T : Nat → Option Bool) (S h : Nat) (b : Bool)
    (inside : h < S) (cell : T h=some b) : put (hole T h S) h (some b)=T := by
  funext i
  dsimp only [hole]
  rw [if_pos inside]
  dsimp only [put]
  by_cases same : i=h
  · rw [if_pos same];subst i;exact cell.symm
  · rw [if_neg same,if_neg same]
private theorem next_image (T : Nat → Option Bool) (S L n F width a b c d h : Nat) (oldBit : Bool)
    (sl : S < L) (room : L+n+1 < F) (inside : h < S) (cell : T h=some oldBit) :
    (if h+1=S then put (image (hole T h S) L n F width a b c d) h (some oldBit)
     else put (put (image (hole T h S) L n F width a b c d) h (some oldBit)) (h+1) none)=
      image (hole T (h+1) S) L n F width a b c d := by
  by_cases eof : h+1=S
  · rw [if_pos eof,sourceWrite (hole T h S) L n F width a b c d h (some oldBit) room (by omega),restore_hole T S h oldBit inside cell]
    dsimp only [hole]
    rw [if_neg (by omega)]
  · rw [if_neg eof,sourceWrite (hole T h S) L n F width a b c d h (some oldBit) room (by omega),restore_hole T S h oldBit inside cell,sourceWrite T L n F width a b c d (h+1) none room (by omega)]
    dsimp only [hole]
    rw [if_pos (by omega)]
#print axioms hole_type
#print axioms hole_high
#print axioms image_low
#print axioms image_frame
#print axioms hole_frame
#print axioms hole_banks
#print axioms exterior_banks
#print axioms hole_bank0
#print axioms hole_bank1
#print axioms restore_hole
#print axioms next_image
end VirtualFinalClosure.GuardLayout
