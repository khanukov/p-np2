import VirtualFinalClosure.CleanupFrame
import VirtualFinalClosure.InitialCapGrow
namespace VirtualFinalClosure.DirtyBanks
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
      ("VirtualFinalClosure.CleanupFrame","VirtualFinalClosure.CleanupFrame","delimiter_eq","delimiterEq",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong dirty-bank physical image term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique dirty-bank physical image term {mod}/{key}"
private theorem frame {I : Nat → Option Bool} {S L n Q F width : Nat}
    (fr : SourceFrame I S L (L+n+1) Q F)
    (blank : ∀ j,j ≤ 6 → I (SerializedBody.delimiter F width n j)=none)
    (cells : ∀ j,j < 6 → ∀ i,SerializedBody.delimiter F width n j < i →
      i < SerializedBody.delimiter F width n (j+1) → ∃ b,I i=some b) :
    CleanFrame I L n Q F width:=by
  obtain ⟨_sl,_lh,positive,room,_source,sep,last,_start,fence,_reg,assn,tally,gap⟩:=fr
  refine cleanMk positive room ?_ ?_ fence gap tally sep last assn
  · intro j hj
    rw [delimiterEq F width n j hj]
    exact blank j hj
  · intro j hj i lo hi
    rw [delimiterEq F width n j (by omega)] at lo
    rw [delimiterEq F width n (j+1) (by omega)] at hi
    exact cells j hj i lo hi
/-- Full cleanup equality is insensitive to the actual occupied assignment
and dirty counters that were present on entry. Every changed cell is charged
to the real assignment paint or one of the six executed bank paints. -/
private theorem cleared (I V : Nat → Option Bool) (L n F width : Nat)
    (room : L+n+1 < F)
    (assignment : ∀ i,L < i → i < L+n+1 → V i=some false)
    (outside : ∀ i,¬(L < i ∧ i < L+n+1) → ¬bank F width n i → I i=V i) :
    paint (stage I F width n 6) (L+1) (L+n+1)=Cursor.Target.scratch V F width n:=by
  funext i
  have exactStage:=stageExact I F width n i
  by_cases assn : L < i ∧ i < L+n+1
  · dsimp only [paint,Cursor.Target.scratch]
    rw [if_pos (by omega),if_neg (by omega),assignment i assn.1 assn.2]
  · dsimp only [paint]
    rw [if_neg (by omega)]
    change stage I F width n 6 i=Cursor.Target.scratch V F width n i
    refine exactStage.trans ?_
    change (if bank F width n i then some false else I i)=
      if bank F width n i then some false else V i
    by_cases inside : bank F width n i
    · rw [if_pos inside,if_pos inside]
    · rw [if_neg inside,if_neg inside,outside i assn inside]
private theorem cap_cleared (V : Nat → Option Bool) (L n F r a b c d e : Nat)
    (positive : 0 < r) (room : L+n+1 < F) (assignment : ∀ i,L < i → i < L+n+1 → V i=some false) :
    let Y:=RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r
    let I:=CappedWeight.Target.image (AllArityBitLength.Target.seedImage Y F r n) L n F r a b c d e
    paint (stage I F r n 6) (L+1) (L+n+1)=Cursor.Target.scratch V F r n:=by
  intro Y I
  apply cleared I V L n F r room assignment
  intro i assn outside
  dsimp only [bank] at outside
  dsimp only [I,Y,CappedWeight.Target.image,AllArityBitLength.Target.seedImage,
    RuntimeBitLength.Target.fullImage,CappedWorkspace.Target.image,SuffixCap.Target.image]
  repeat' rw [if_neg (by omega)]
private theorem length_cleared (V : Nat → Option Bool) (L n F r : Nat)
    (room : L+n+1 < F) (assignment : ∀ i,L < i → i < L+n+1 → V i=some false) :
    let Y:=RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r
    paint (stage Y F r n 6) (L+1) (L+n+1)=Cursor.Target.scratch V F r n:=by
  intro Y
  apply cleared Y V L n F r room assignment
  intro i assn outside
  dsimp only [bank] at outside
  dsimp only [Y,RuntimeBitLength.Target.fullImage,CappedWorkspace.Target.image,SuffixCap.Target.image]
  repeat' rw [if_neg (by omega)]
#print axioms frame
#print axioms cleared
#print axioms cap_cleared
#print axioms length_cleared
end VirtualFinalClosure.DirtyBanks
