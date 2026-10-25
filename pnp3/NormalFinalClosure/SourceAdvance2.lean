import NormalFinalClosure.SourceRoute2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["Node","Path","keep","hop","put","sweepR"]),
    (`NormalFinalClosure.SourceRoute2,`NormalFinalClosure,["LowFrame","LowFrame.room","LowFrame.eof","LocateRows","SDToRows","locate","sd","low_put"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing exact source consumer API {name}"
      let some i:=e.getModuleIdxFor? name | throwError "Missing source consumer owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong source consumer owner"
      logInfo m!"literal-source-consumer-interface|{name}|{ci.type}"
      let aliasName:=(leaf.splitOn ".").getLast!
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac do
    let owner:=`PhysicalCallerClosure.Engine
    let name:=Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") "Node") "mk"
    let e←getEnv
    let some (.ctorInfo ci):=e.find? name | throwError "Missing source consumer Node constructor"
    let some i:=e.getModuleIdxFor? name | throwError "Missing source consumer Node owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong source consumer Node owner"
    closeMainGoal `node (mkConst name (ci.levelParams.map Level.param))
variable {M : UniformTM} {Safe : Fin M.stateCount → Prop}
private def AdvanceRows (entry : Fin M.stateCount) (out : Fin 3 → Fin M.stateCount) (b : Bool) : Prop :=
  ∃ hole next virtual : Fin M.stateCount,∃ scan atS : Bool → Fin M.stateCount,
    LocateRows (Safe:=Safe) entry hole ∧ Safe hole ∧ Safe next ∧
    M.step hole none=(next,some b,.right) ∧
    M.step next none=(virtual,none,.stay) ∧ SDToRows (Safe:=Safe) virtual (out 2) ∧
    (∀ v,Safe (scan v)) ∧
    (∀ v,M.step next (some v)=(scan v,none,.right)) ∧
    (∀ v b',M.step (scan v) (some b')=(scan v,some b',.right)) ∧
    (∀ v,M.step (scan v) none=(atS v,none,.stay)) ∧
    (∀ v,SDToRows (Safe:=Safe) (atS v) (out (if v then 1 else 0)))
/-- One physical source consume, retaining the exact carried bit and next real
hole. At the last source cell it returns distinct virtual mode2 and no new hole.
Every shuttle/restore/lift/return row is included in the path and price. -/
private theorem advance {T S z n F P c entry out b} (fr:LowFrame T S z n F)
    (fit:F+1 ≤ P) (physical:c < S) (hole:T c=none)
    (source:∀ i,c < i → i < S → ∃ v,T i=some v)
    (code:AdvanceRows (Safe:=Safe) entry out b) :
    ∃ (mode : Fin 3) (E : Nat → Option Bool),
      ((c+1=S ∧ mode=2 ∧ E=put T c (some b)) ∨
       (∃ v,c+1 < S ∧ mode=(if v then 1 else 0) ∧ T (c+1)=some v ∧
         E=put (put T c (some b)) (c+1) none)) ∧
      Path M Safe P (2*(F+1-c)+5) (node entry (F+1) T) (node (out mode) (F+1) E) := by
  obtain ⟨holeState,next,virtual,scan,atS,find,sh,sn,write,atEOF,backEOF,ss,lift,loop,stop,back⟩:=code
  have begin:=locate fr fit physical hole source find
  have bound:=room fr
  have one:=hop holeState next c (c+1) T (some b) .right (P:=P)
    (by omega) (by omega) sh (by rw [hole];exact write) rfl
  let E1:=put T c (some b)
  have fr1:LowFrame E1 S z n F:=low_put fr physical
  by_cases last:c+1=S
  · have eof1:E1 S=none:=eof fr1
    have two:=keep next virtual S S E1 .stay (P:=P) (by omega) (by omega) sn (by rw [eof1];exact atEOF) rfl
    rw [last] at one
    have finish:=sd fr1 fit backEOF
    have path:=begin.append (one.append (two.append finish))
    refine ⟨2,E1,Or.inl ⟨last,rfl,rfl⟩,?_⟩
    convert path using 1
    omega
  · have before:c+1 < S:=by omega
    obtain ⟨v,hv⟩:=source (c+1) (by omega) before
    have bit1:E1 (c+1)=some v:=by
      dsimp only [E1,put]
      rw [if_neg (by omega)]
      exact hv
    have two:=hop next (scan v) (c+1) (c+2) E1 none .right (P:=P)
      (by omega) (by omega) sn (by rw [bit1];exact lift v) rfl
    let E2:=put E1 (c+1) none
    have fr2:LowFrame E2 S z n F:=low_put fr1 before
    have middle:=sweepR (scan v) E2 (c+2) (S-(c+2)) (P:=P) (by omega) (ss v) (by
      intro i lo hi
      obtain ⟨b',hb⟩:=source i (by omega) (by omega)
      change M.step (scan v) (put (put T c (some b)) (c+1) none i)=
        (scan v,put (put T c (some b)) (c+1) none i,.right)
      rw [show put (put T c (some b)) (c+1) none i=T i by
        simp only [put,show i≠c+1 by omega,show i≠c by omega,if_false],hb]
      exact loop v b')
    rw [show c+2+(S-(c+2))=S by omega] at middle
    have stay:=keep (scan v) (atS v) S S E2 .stay (P:=P) (by omega) (by omega) (ss v)
      (by rw [eof fr2];exact stop v) rfl
    have finish:=sd fr2 fit (back v)
    have path:=begin.append (one.append (two.append (middle.append (stay.append finish))))
    refine ⟨(if v then 1 else 0),E2,Or.inr ⟨v,before,rfl,hv,rfl⟩,?_⟩
    convert path using 1
    omega
end NormalFinalClosure
