import VirtualFinalClosure.GuardUnary
import PostWeight.Kernel
namespace VirtualFinalClosure.GuardImage
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("PostWeight.Kernel","PostWeight","Banks","Banks",(2:Nat)),
      ("PostWeight.Kernel","PostWeight","Banks.room","bankRoom",(1:Nat)),
      ("PostWeight.Kernel","PostWeight","Banks.mk","banksMk",(3:Nat)),
      ("PostWeight.Kernel","PostWeight","atD","atD",(1:Nat)),
      ("PostWeight.Kernel","PostWeight","atBank","atBank",(1:Nat)),
      ("PostWeight.Kernel","PostWeight","set3","set3",(1:Nat)),
      ("PostWeight.Kernel","PostWeight","set4","set4",(1:Nat)),
      ("PostWeight.Kernel","PostWeight","set5","set5",(1:Nat)),
      ("PostWeight.Kernel","PostWeight","unset3","unset3",(1:Nat)),
      ("PostWeight.Kernel","PostWeight","unset4","unset4",(1:Nat)),
      ("SmallIngress.Runtime","SmallIngress","put","put",(0:Nat)) ] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong exact native guard image interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique exact native guard image interface {mod}/{key}"
private def image (T : Nat → Option Bool) (L n F C a b c d : Nat) : Nat → Option Bool:=
  CappedWeight.Target.image T L n F C a b c d 0
private def image_type : (Nat → Option Bool) → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Option Bool:=image
private theorem delimiters {T : Nat → Option Bool} {L n F C : Nat} (fr : Banks T L n F C)
    (a b c d : Nat) : ∀ j,j ≤ 6 → image T L n F C a b c d (SerializedBody.delimiter F C n j)=none := by
  intro j hj
  interval_cases j <;> exact atD fr a b c d _ (by omega)
private theorem digit {T : Nat → Option Bool} {L n F C : Nat} (fr : Banks T L n F C)
    (a b c d j i : Nat) (lo : 2 ≤ j) (hi : j < 6)
    (il : SerializedBody.delimiter F C n j < i) (ih : i < SerializedBody.delimiter F C n (j+1)) :
    image T L n F C a b c d i=some (decide (i ≤ SerializedBody.delimiter F C n j+
      (if j=2 then a else if j=3 then b else if j=4 then c else d))) := by
  interval_cases j
  · exact atBank fr a b c d 2 i (by decide) (by decide) il ih
  · exact atBank fr a b c d 3 i (by decide) (by decide) il ih
  · exact atBank fr a b c d 4 i (by decide) (by decide) il ih
  · exact atBank fr a b c d 5 i (by decide) (by decide) il ih
private theorem occupied {T : Nat → Option Bool} {L n F C : Nat} (fr : Banks T L n F C)
    (b0 : ∀ i,F+1 < i → i < F+C+2 → ∃ b,T i=some b)
    (b1 : ∀ i,F+C+2 < i → i < F+C+n+3 → ∃ b,T i=some b)
    (a b c d : Nat) : ∀ j,j < 6 → ∀ i,SerializedBody.delimiter F C n j < i →
      i < SerializedBody.delimiter F C n (j+1) → ∃ v,image T L n F C a b c d i=some v := by
  intro j hj i lo hi
  by_cases small : j < 2
  · have room:=bankRoom fr
    interval_cases j <;> dsimp only [SerializedBody.delimiter] at lo hi <;>
      dsimp only [image,CappedWeight.Target.image] <;>
      rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
    · exact b0 i lo hi
    · exact b1 i lo hi
  · exact ⟨_,digit fr a b c d j i (by omega) hj lo hi⟩
private theorem add3 {T : Nat → Option Bool} {L n F C : Nat} (fr : Banks T L n F C)
    (a b c d : Nat) (fit : b < C) :
    put (image T L n F C a b c d) (F+2*C+n+4+b+1) (some true)=image T L n F C a (b+1) c d :=
  set3 fr a b c d fit
private theorem add4 {T : Nat → Option Bool} {L n F C : Nat} (fr : Banks T L n F C)
    (a b c d : Nat) (fit : c < C) :
    put (image T L n F C a b c d) (F+3*C+n+5+c+1) (some true)=image T L n F C a b (c+1) d :=
  set4 fr a b c d fit
private theorem add5 {T : Nat → Option Bool} {L n F C : Nat} (fr : Banks T L n F C)
    (a b c d : Nat) (fit : d < C) :
    put (image T L n F C a b c d) (F+4*C+n+6+d+1) (some true)=image T L n F C a b c (d+1) :=
  set5 fr a b c d fit
private theorem take3 {T : Nat → Option Bool} {L n F C : Nat} (fr : Banks T L n F C)
    (a b c d : Nat) (positive : 0 < b) (fit : b ≤ C) :
    put (image T L n F C a b c d) (F+2*C+n+4+b) (some false)=image T L n F C a (b-1) c d := by
  have old:=unset3 fr a (b-1) c d (by omega)
  change put (image T L n F C a (b-1+1) c d) (F+2*C+n+4+(b-1)+1) (some false)=image T L n F C a (b-1) c d at old
  simpa only [show b-1+1=b by omega,show F+2*C+n+4+(b-1)+1=F+2*C+n+4+b by omega] using old
private theorem take4 {T : Nat → Option Bool} {L n F C : Nat} (fr : Banks T L n F C)
    (a b c d : Nat) (positive : 0 < c) (fit : c ≤ C) :
    put (image T L n F C a b c d) (F+3*C+n+5+c) (some false)=image T L n F C a b (c-1) d := by
  have old:=unset4 fr a b (c-1) d (by omega)
  change put (image T L n F C a b (c-1+1) d) (F+3*C+n+5+(c-1)+1) (some false)=image T L n F C a b (c-1) d at old
  simpa only [show c-1+1=c by omega,show F+3*C+n+5+(c-1)+1=F+3*C+n+5+c by omega] using old
private theorem take2 {T : Nat → Option Bool} {L n F C : Nat} (fr : Banks T L n F C)
    (a b c d : Nat) (positive : 0 < a) (fit : a ≤ C) :
    put (image T L n F C a b c d) (F+C+n+3+a) (some false)=image T L n F C (a-1) b c d := by
  have room:=bankRoom fr
  funext i
  dsimp only [put,image,CappedWeight.Target.image]
  split_ifs <;> first | rfl | (exfalso;omega) |
    (congr 1;first | exact (decide_eq_true (by omega)).symm | exact (decide_eq_false (by omega)).symm |
      exact decide_eq_decide.mpr (by omega))
private theorem take5 {T : Nat → Option Bool} {L n F C : Nat} (fr : Banks T L n F C)
    (a b c d : Nat) (positive : 0 < d) (fit : d ≤ C) :
    put (image T L n F C a b c d) (F+4*C+n+6+d) (some false)=image T L n F C a b c (d-1) := by
  have room:=bankRoom fr
  funext i
  dsimp only [put,image,CappedWeight.Target.image]
  split_ifs <;> first | rfl | (exfalso;omega) |
    (congr 1;first | exact (decide_eq_true (by omega)).symm | exact (decide_eq_false (by omega)).symm |
      exact decide_eq_decide.mpr (by omega))
/-- A real source-hole write below L commutes with the unchanged bank image.
This is used by the physical source advance, preserving all other cells. -/
private theorem source_write (T : Nat → Option Bool) (L n F width a b c d p : Nat) (v : Option Bool)
    (room : L+n+1 < F) (low : p ≤ L) :
    put (image T L n F width a b c d) p v=image (put T p v) L n F width a b c d := by
  funext i
  by_cases hit : i=p
  · subst i
    dsimp only [put,image,CappedWeight.Target.image]
    rw [if_pos rfl,if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_pos rfl]
  · dsimp only [put,image,CappedWeight.Target.image]
    rw [if_neg hit]
    split_ifs <;> rfl
#print axioms image_type
#print axioms delimiters
#print axioms digit
#print axioms occupied
#print axioms add3
#print axioms add4
#print axioms add5
#print axioms take2
#print axioms take3
#print axioms take4
#print axioms take5
#print axioms source_write
end VirtualFinalClosure.GuardImage
