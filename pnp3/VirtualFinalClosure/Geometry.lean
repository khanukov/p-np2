import VirtualFinalClosure.Resources
import VirtualFinalClosure.SourceWalk
namespace VirtualFinalClosure.Geometry
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,isThm) in [
      ("VirtualFinalClosure.Resources","VirtualFinalClosure.Resources","power_two","linearPower",true),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",false),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame.mk","frameMk",false)] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      let good:=match ci with | .thmInfo _=>isThm | .inductInfo _=>!isThm | .ctorInfo _=>!isThm | _=>false
      unless good do throwError "Wrong literal geometry declaration kind {n}"
      logInfo m!"private-term|{n}|isTheorem={isThm}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique native geometry interface {mod}/{key}"
private theorem physical (S z n : Nat) (h : min (9+2*z+2^n) S < S) :
    9+2*z+2^n < S := by
  by_contra no
  rw [Nat.min_eq_right (by omega)] at h
  exact Nat.lt_irrefl _ h
/-- The source-return scan's required blank gap is DERIVED on the actual physical
cap branch. The weaker prepared room H+Q<F alone would not be sufficient. -/
private theorem actual_gap (R S z n : Nat) (length : S≤R)
    (h : min (9+2*z+2^n) S < S) : S+z+n+3+2^n+1 < 3*R+2 := by
  have inside:=physical S z n h
  have width:=linearPower n
  omega
private theorem actual_width (R S z n : Nat) (length : S≤R)
    (h : min (9+2*z+2^n) S < S) : n≤R := by
  have inside:=physical S z n h
  have width:=linearPower n
  omega
private theorem protected_frame {S L H Q F : Nat} {T U : Nat → Option Bool}
    (fr : Frame T S L H Q F) (same : ∀ i, S ≤ i → i ≤ F+1 → U i = T i) : Frame U S L H Q F := by
  obtain ⟨sl,lh,qp,room,s0,l0,h0,f0,ff,reg,assign,tally,gap⟩:=fr
  refine frameMk sl lh qp room ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact (same S le_rfl (by omega)).trans s0
  · exact (same L (by omega) (by omega)).trans l0
  · exact (same H (by omega) (by omega)).trans h0
  · exact (same (F+1) (by omega) le_rfl).trans f0
  · exact (same F (by omega) (by omega)).trans ff
  · intro i lo hi
    obtain ⟨b,hb⟩:=reg i lo hi
    exact ⟨b,(same i (by omega) (by omega)).trans hb⟩
  · intro i lo hi
    obtain ⟨b,hb⟩:=assign i lo hi
    exact ⟨b,(same i (by omega) (by omega)).trans hb⟩
  · intro i lo hi
    exact (same i (by omega) (by omega)).trans (tally i lo hi)
  · intro i lo hi
    exact (same i (by omega) (by omega)).trans (gap i lo hi)
#print axioms physical
#print axioms actual_gap
#print axioms actual_width
#print axioms protected_frame
end VirtualFinalClosure.Geometry
