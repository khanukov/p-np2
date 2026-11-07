import NormalFinalClosure.CompareKernel2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["Node","Path","Grid","keep"]),
    (`PhysicalCallerClosure.UnaryCopy,`PhysicalCallerClosure,["mono"]),
    (`NormalFinalClosure.CompareSupport2,`NormalFinalClosure,["CompareRows","retreat_run"]),
    (`NormalFinalClosure.CompareKernel2,`NormalFinalClosure,["compare_seek","compare_cycle"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing actual comparison termination API"
      let some i:=e.getModuleIdxFor? name | throwError "Missing comparison termination owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong comparison termination owner"
      logInfo m!"actual-comparison-termination-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous (leaf.splitOn ".").getLast!) name::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac do
    let owner:=`PhysicalCallerClosure.Engine
    let name:=Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") "Node") "mk"
    let e←getEnv
    let some (.ctorInfo ci):=e.find? name | throwError "Missing comparison stop Node constructor"
    let some i:=e.getModuleIdxFor? name | throwError "Missing comparison stop Node owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong comparison stop Node owner"
    closeMainGoal `node (mkConst name (ci.levelParams.map Level.param))
variable {M : UniformTM} {Safe : Fin M.stateCount → Prop}
/-- Both real termination observations (111 free OR000 inactive), including all
processed-record scan and return rows. Neither is a blank-tape convention. -/
private theorem compare_stop {D T P entry good done bad value} (g:Grid D T) (room:D 13 ≤ P)
    (seen : Nat) (fit:D 10+3*seen+3 < D 11)
    (processed:∀ j,j < seen → T (D 10+1+3*j)=some false ∧
      T (D 10+1+3*j+1)=some true ∧ T (D 10+1+3*j+2)=some true)
    (stop:T (D 10+1+3*seen)=some true ∨
      (T (D 10+1+3*seen)=some false ∧ T (D 10+1+3*seen+1)=some false ∧ T (D 10+1+3*seen+2)=some false))
    (code:CompareRows (Safe:=Safe) entry good done bad value) :
    ∃ t,t ≤ 128*(P+1) ∧ Path M Safe P t (node entry (D 0) T) (node done (D 0) T) := by
  obtain ⟨enter,first,second,third0,third1,write2,back,ret,rd,rb,route,outRoute,se,sf,ss,st0,st1,sw,sb,enterRow,freeRow,firstRow,secondRow,zeroRow,processedRow,matchRow,writeRow,backRow,stopRow,doneRows,badRows⟩:=code
  let h:=D 10+1+3*seen
  have dP:=(mono g 11 13 (by decide) le_rfl).trans room
  have seek:=compare_seek g room seen (by omega) route se enterRow
    (compare_cycle sf ss st1 firstRow secondRow processedRow) processed
  rcases stop with free|⟨zero,secondZero,thirdZero⟩
  · have step:=keep first rd h h T .stay (P:=P) (by omega) (by omega) sf (by rw [free];exact freeRow) rfl
    have finish:=retreat_run g room h (by omega) (by omega) doneRows
    have path:=seek.append (step.append finish)
    refine ⟨2*(D 10-D 0+10)+6*seen+4,by omega,?_⟩
    convert path using 1
    omega
  · have one:=keep first second h (h+1) T .right (P:=P) (by omega) (by omega) sf (by rw [zero];exact firstRow) rfl
    have two:=keep second third0 (h+1) (h+2) T .right (P:=P) (by omega) (by omega) ss
      (by rw [secondZero];exact secondRow false) rfl
    have three:=keep third0 rd (h+2) (h+2) T .stay (P:=P) (by omega) (by omega) st0
      (by rw [thirdZero];exact zeroRow) rfl
    have finish:=retreat_run g room (h+2) (by omega) (by omega) doneRows
    have path:=seek.append (one.append (two.append (three.append finish)))
    refine ⟨2*(D 10-D 0+10)+6*seen+8,by omega,?_⟩
    convert path using 1
    omega
end NormalFinalClosure
