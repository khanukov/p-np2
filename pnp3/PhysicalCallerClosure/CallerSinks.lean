import PhysicalCallerClosure.Reset
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
private def checkedEngine (leaf kind : String) : TacticM Unit := do
  let e←getEnv
  let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.Engine 0) "PhysicalCallerClosure") leaf
  let some ci:=e.find? n | throwError "Missing exact Engine constant {n}"
  let actual:=match ci with | .defnInfo _=>"definition" | .thmInfo _=>"theorem" | _=>"other"
  unless actual==kind do throwError "Wrong Engine kind {n}"
  let some i:=e.getModuleIdxFor? n | throwError "Missing Engine owner"
  unless i.toNat<e.header.moduleNames.size do throwError "Owner index outside header"
  unless e.header.moduleNames[i]! == `PhysicalCallerClosure.Engine do throwError "Wrong Engine owner"
  logInfo m!"literal-support|{actual}|{n}|{ci.type}"
  closeMainGoal `checkedEngine (mkConst n (ci.levelParams.map Level.param))
run_cmd do
  let e←getEnv
  for leaf in ["ns","NativeSafe","nativeRoute","nativeRow","ns_safe"] do
    let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.Engine 0) "PhysicalCallerClosure") leaf
    let some ci:=e.find? n | throwError "Missing exact Engine support {n}"
    let some i:=e.getModuleIdxFor? n | throwError "Missing Engine support owner"
    unless i.toNat<e.header.moduleNames.size do throwError "Owner index outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.Engine do throwError "Wrong support owner"
    logInfo m!"literal-open|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private abbrev pin_ns : ∀ k,Nat → Fin (callerMachine k).stateCount := by run_tac checkedEngine "ns" "definition"
private abbrev pin_NativeSafe : ∀ k,Fin (callerMachine k).stateCount → Prop := by run_tac checkedEngine "NativeSafe" "definition"
private abbrev pin_nativeRoute : Nat → TacticM Unit := by run_tac checkedEngine "nativeRoute" "definition"
private abbrev pin_nativeRow : TacticM Unit := by run_tac checkedEngine "nativeRow" "definition"
private theorem pin_ns_safe : ∀ k i,i<3337 → i≠1432 → NativeSafe k (ns k i) := by
  run_tac checkedEngine "ns_safe" "theorem"
private theorem safe_verdict : ∀ k q,NativeSafe k q →
    q≠(callerMachine k).accept ∧ q≠(callerMachine k).reject ∧ q≠rowsDone k := by
  run_tac do
    let e←getEnv
    let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.Reset 0) "PhysicalCallerClosure") "safe_verdict"
    let some (.thmInfo ci):=e.find? n | throwError "Missing exact native safety proof"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.Reset do throwError "Wrong safety proof owner"
    logInfo m!"sink-safety-adapter|{n}|{ci.type}"
    closeMainGoal `safe_verdict (mkConst n (ci.levelParams.map Level.param))
section LiteralRows
set_option maxRecDepth 4000
private theorem done_row (k : Nat) (b : Option Bool) :
    (callerMachine k).step (rowsDone k) b=(rowsDone k,b,.stay) := by
  change (callerMachine k).step (ns k 1432) b=(ns k 1432,b,.stay)
  cases b with
  | none => run_tac nativeRow
  | some b => cases b <;> run_tac nativeRow
end LiteralRows
private theorem done_step {k N B : Nat} (c : Config (callerMachine k).stateCount N B) (h:c.state=rowsDone k) :
    (callerMachine k).stepConfig c=c := by
  apply Config.ext_parts
  · dsimp only [UniformTM.stepConfig];rw [h,done_row]
  · dsimp only [UniformTM.stepConfig];rw [h,done_row];rfl
  · dsimp only [UniformTM.stepConfig];rw [h,done_row]
    funext i
    split_ifs with hi
    · cases hi;rfl
    · rfl
private theorem done_run {k N B : Nat} (c : Config (callerMachine k).stateCount N B) (h:c.state=rowsDone k) :
    ∀ t,(callerMachine k).run t c=c := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => rw [UniformTM.run,ih,done_step c h]
private theorem work_prefix {k N B t : Nat} (c : Config (callerMachine k).stateCount N B)
    (na:((callerMachine k).run t c).state≠(callerMachine k).accept)
    (nr:((callerMachine k).run t c).state≠(callerMachine k).reject)
    (nd:((callerMachine k).run t c).state≠rowsDone k) :
    ∀ u,u ≤ t → ((callerMachine k).run u c).state≠(callerMachine k).accept ∧
      ((callerMachine k).run u c).state≠(callerMachine k).reject ∧ ((callerMachine k).run u c).state≠rowsDone k := by
  intro u hu
  refine ⟨?_,?_,?_⟩
  · intro bad
    have fixed:=(callerMachine k).run_accept ((callerMachine k).run u c) bad (t-u)
    rw [←UniformTM.run_add,show u+(t-u)=t by omega] at fixed
    exact na ((congrArg Config.state fixed).trans bad)
  · intro bad
    have fixed:=(callerMachine k).run_reject ((callerMachine k).run u c) bad (t-u)
    rw [←UniformTM.run_add,show u+(t-u)=t by omega] at fixed
    exact nr ((congrArg Config.state fixed).trans bad)
  · intro bad
    have fixed:=done_run ((callerMachine k).run u c) bad (t-u)
    rw [←UniformTM.run_add,show u+(t-u)=t by omega] at fixed
    exact nd ((congrArg Config.state fixed).trans bad)
end PhysicalCallerClosure
