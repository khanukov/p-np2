import VirtualFinalClosure.GuardLayout
import VirtualReady.Raw
namespace VirtualFinalClosure.CleanupFrame
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualReady.Kernel","VirtualReady","Frame","CleanFrame",(2:Nat)),
      ("VirtualReady.Kernel","VirtualReady","Frame.mk","cleanMk",3),
      ("VirtualReady.Kernel","VirtualReady","D","D",0),
      ("VirtualReady.Kernel","VirtualReady","paint","paint",0),
      ("VirtualReady.Kernel","VirtualReady","stage","stage",0),
      ("VirtualReady.Raw","VirtualReady","stage_exact","stageExact",1),
      ("VirtualReady.Raw","VirtualReady","bank","bank",0),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","SourceFrame",2),
      ("PostWeight.Kernel","PostWeight","Banks","Banks",2),
      ("VirtualFinalClosure.GuardLayout","VirtualFinalClosure.GuardLayout","image_frame","imageFrame",1),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","delimiters","delimiters",1),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","occupied","occupied",1),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","image","image",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong actual dirty-bank cleanup frame {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual dirty-bank cleanup frame {mod}/{key}"
private theorem delimiter_eq (F width n j : Nat) (hj : j ≤ 6) :
    D F width n j=SerializedBody.delimiter F width n j:=by
  interval_cases j <;> rfl
/-- Every genuine BE-success/BE-abort image has the ORIGINAL literal cleanup
frame, without assuming clean banks or counter-fit inequalities. -/
private theorem actual {T : Nat → Option Bool} {S L n Q F width : Nat}
    (fr : SourceFrame T S L (L+n+1) Q F) (banks : Banks T L n F width)
    (b0 : ∀ i,F+1 < i → i < F+width+2 → ∃ b,T i=some b)
    (b1 : ∀ i,F+width+2 < i → i < F+width+n+3 → ∃ b,T i=some b)
    (a b c d : Nat) : CleanFrame (image T L n F width a b c d) L n Q F width := by
  have img:=imageFrame (width:=width) fr a b c d
  obtain ⟨_sl,_lh,positive,room,_source,sep,last,_start,fence,_reg,assn,tally,gap⟩:=img
  refine cleanMk positive room ?_ ?_ fence gap tally sep last assn
  · intro j hj
    rw [delimiter_eq F width n j hj]
    exact delimiters banks a b c d j hj
  · intro j hj i lo hi
    rw [delimiter_eq F width n j (by omega)] at lo
    rw [delimiter_eq F width n (j+1) (by omega)] at hi
    exact occupied banks b0 b1 a b c d j hj i lo hi
/-- Exact post-cleanup tape for ANY actual guard counters. The pre-run base U
is fixed before execution; assignment is physically false and no exterior tape
is selected after the fact. Delimiters/source/header holes are unchanged. -/
private theorem image_cleared (U : Nat → Option Bool) (L n F width a b c d : Nat)
    (room : L+n+1 < F) (assn : ∀ i,L < i → i < L+n+1 → U i=some false) :
    paint (stage (image U L n F width a b c d) F width n 6) (L+1) (L+n+1)=
      Cursor.Target.scratch U F width n := by
  funext i
  have exactStage : stage (image U L n F width a b c d) F width n 6 i=
      (if bank F width n i then some false else image U L n F width a b c d i):=
    stageExact (image U L n F width a b c d) F width n i
  by_cases assignment : L < i ∧ i < L+n+1
  · dsimp only [paint,Cursor.Target.scratch]
    rw [if_pos (by omega),if_neg (by omega),assn i assignment.1 assignment.2]
  · dsimp only [paint]
    rw [if_neg (by omega),exactStage]
    change (if bank F width n i then some false else image U L n F width a b c d i)=
      if bank F width n i then some false else U i
    by_cases inside : bank F width n i
    · rw [if_pos inside,if_pos inside]
    · rw [if_neg inside,if_neg inside]
      dsimp only [bank] at inside
      dsimp only [image,CappedWeight.Target.image]
      rw [if_neg assignment,if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
#print axioms delimiter_eq
#print axioms actual
#print axioms image_cleared
end VirtualFinalClosure.CleanupFrame
