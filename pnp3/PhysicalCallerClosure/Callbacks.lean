import PhysicalCallerClosure.Engine
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Tactic Command
private def select (owner : Name) (leaf kind : String) : TacticM Unit := do
  let e←getEnv
  let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
  let some ci:=e.find? n | throwError "Missing exact callback term {n}"
  let actual:=match ci with | .defnInfo _=>"definition" | .thmInfo _=>"theorem" | _=>"other"
  unless actual==kind do throwError "Wrong callback term kind"
  let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
  unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
  unless e.header.moduleNames[i]! == owner do throwError "Wrong callback owner"
  logInfo m!"callback-adapter|{n}|{ci.type}"
  closeMainGoal `select (mkConst n (ci.levelParams.map Level.param))
private abbrev pinRows : ∀ k,Fin (callerMachine k).stateCount → Option Bool →
    Fin (callerMachine k).stateCount × Option Bool × Move := by
  run_tac select `PhysicalCallerClosure.Controller "rows" "definition"
private abbrev pinEval : ∀ k,Fin 7500 → Fin (callerMachine k).stateCount := by
  run_tac select `PhysicalCallerClosure.Controller "liftEval" "definition"
private abbrev ns : ∀ k,Nat → Fin (callerMachine k).stateCount := by
  run_tac select `PhysicalCallerClosure.Engine "ns" "definition"
run_cmd do
  let e←getEnv
  for (leaf,aliasName) in [("rows",`actualRows),("liftEval",`actualEval)] do
    let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.Controller 0) "PhysicalCallerClosure") leaf
    let some (.defnInfo ci):=e.find? n | throwError "Missing exact controller definition {n}"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.Controller do throwError "Wrong controller owner"
    logInfo m!"callback-open|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit aliasName n::st.openDecls}
private def callback (k : Nat) (q : Fin 7500) : Fin (callerMachine k).stateCount :=
  ns k (if q.val=1 then 3334 else if q.val=2 then 2714 else 3211)
private theorem callback_rows (k : Nat) (q : Fin 7500) (b : Option Bool) (lo:0 < q.val) (hi:q.val < 4) :
    (callerMachine k).step (evalState k q) b=(callback k q,b,.stay) := by
  have na:evalState k q≠(callerMachine k).accept:=by
    intro bad;have values:=congrArg Fin.val bad
    change (BodyIngress.machine k).stateCount+q.val=(BodyIngress.machine k).accept.val at values
    have bound:=(BodyIngress.machine k).accept.isLt;omega
  have nr:evalState k q≠(callerMachine k).reject:=by
    intro bad;have values:=congrArg Fin.val bad
    change (BodyIngress.machine k).stateCount+q.val=(BodyIngress.machine k).reject.val at values
    have bound:=(BodyIngress.machine k).reject.isLt;omega
  rw [UniformTM.step_of_ne (callerMachine k) na nr]
  change actualRows k (actualEval k q) b=_
  dsimp only [actualRows,actualEval]
  rw [dif_neg (by omega : ¬(BodyIngress.machine k).stateCount+q.val < (BodyIngress.machine k).stateCount),
    dif_pos (by omega : (BodyIngress.machine k).stateCount+q.val < (BodyIngress.machine k).stateCount+7500)]
  have eqQ:(⟨(BodyIngress.machine k).stateCount+q.val-(BodyIngress.machine k).stateCount,by omega⟩:Fin 7500)=q:=by
    apply Fin.ext;dsimp;omega
  rw [eqQ,show (BodyIngress.machine k).stateCount+q.val-(BodyIngress.machine k).stateCount=q.val by omega,
    if_neg (by omega : q.val≠0)]
  by_cases one:q.val=1
  · rw [if_pos one]
    simp only [callback,if_pos one]
    rfl
  · rw [if_neg one]
    by_cases two:q.val=2
    · rw [if_pos two]
      simp only [callback,if_neg one,if_pos two]
      rfl
    · have three:q.val=3:=by omega
      rw [if_neg two,if_pos three]
      simp only [callback,if_neg one,if_neg two]
      rfl
private theorem callback_step (k : Nat) (N B : Nat) (q : Fin 7500) (h : Fin (tapeLength N B))
    (T : Fin (tapeLength N B) → Option Bool) (lo:0 < q.val) (hi:q.val < 4) :
    (callerMachine k).run 1 ⟨evalState k q,h,T⟩=⟨callback k q,h,T⟩ := by
  change (callerMachine k).stepConfig ⟨evalState k q,h,T⟩=_
  apply Config.ext_parts
  · exact congrArg Prod.fst (callback_rows k q (T h) lo hi)
  · apply Fin.ext
    change (moveHead h ((callerMachine k).step (evalState k q) (T h)).2.2).val=h.val
    rw [callback_rows k q (T h) lo hi]
    rfl
  · funext i
    dsimp only [UniformTM.stepConfig]
    rw [callback_rows k q (T h) lo hi]
    by_cases eq:i=h
    · subst i;simp
    · simp only [if_neg eq]
end PhysicalCallerClosure
