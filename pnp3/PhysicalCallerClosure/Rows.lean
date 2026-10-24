import PhysicalCallerClosure.ControllerSurface
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Tactic Command
private def exactController (leaf : String) : TacticM Unit := do
  let env ← getEnv
  let n:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.Controller 0) "PhysicalCallerClosure")
  let some (.defnInfo ci):=env.find? n | throwError "Missing exact controller definition {n}"
  let some i:=env.getModuleIdxFor? n | throwError "No controller owner {n}"
  unless i.toNat<env.header.moduleNames.size do throwError "Owner index outside header"
  unless env.header.moduleNames[i]! == `PhysicalCallerClosure.Controller do throwError "Wrong controller owner"
  logInfo m!"controller-term|definition|{n}|{ci.type}"
  closeMainGoal `exactController (mkConst n (ci.levelParams.map Level.param))
private abbrev count : Nat → Nat := by run_tac exactController "count"
private abbrev codeRows : ∀ k,Fin ((BodyIngress.machine k).stateCount+7500+3337) → Option Bool →
    Fin ((BodyIngress.machine k).stateCount+7500+3337) × Option Bool × Move := by run_tac exactController "rows"
private abbrev native : ∀ k,Fin 3337 → Fin ((BodyIngress.machine k).stateCount+7500+3337) := by run_tac exactController "native"
private abbrev instruction : Nat → Nat := by run_tac exactController "instruction"
run_cmd do
  let e ← getEnv
  for (leaf,aliasName) in [("rows","actualRows"),("nativeRows","actualNativeRows"),("native","actualNative"),("liftOld","actualOld"),("liftEval","actualEval"),("count","actualCount")] do
    let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.Controller 0) "PhysicalCallerClosure") leaf
    let some (.defnInfo ci):=e.find? n | throwError "Missing guarded definition {n}"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner {n}"
    unless i.toNat<e.header.moduleNames.size do throwError "Owner index outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.Controller do throwError "Wrong controller owner"
    logInfo m!"controller-unfold|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
private def up (a b c : Nat) (s : Fin a) : Fin (a+b+c) := ⟨s.val,by have h:=s.isLt;omega⟩
private theorem up_injective (a b c : Nat) : Function.Injective (up a b c) := by
  intro s t h
  apply Fin.ext
  exact congrArg (fun q : Fin (a+b+c)=>q.val) h
private theorem old_injective (k : Nat) : Function.Injective (oldState k) := by
  exact up_injective (BodyIngress.machine k).stateCount 7500 3337
private theorem old_step_ne {k : Nat} (s : Fin (BodyIngress.machine k).stateCount)
    (a:s≠(BodyIngress.machine k).accept) (r:s≠(BodyIngress.machine k).reject) :
    oldState k s≠(callerMachine k).accept ∧ oldState k s≠(callerMachine k).reject := by
  exact ⟨fun h=>a (old_injective k h),fun h=>r (old_injective k h)⟩
/-- Every old row except the three explicit first-BODY-entry cuts is unchanged. -/
theorem old_rows (k : Nat) (s : Fin (BodyIngress.machine k).stateCount) (b : Option Bool)
    (uncut : ∀ mode : Fin 3,s≠BodyIngress.body k (SerializedBody.entry mode)) :
    (callerMachine k).step (oldState k s) b=
      (oldState k ((BodyIngress.machine k).step s b).1,((BodyIngress.machine k).step s b).2) := by
  by_cases a:s=(BodyIngress.machine k).accept
  · subst s;rw [UniformTM.step_accept]
    exact (callerMachine k).step_accept b
  by_cases r:s=(BodyIngress.machine k).reject
  · subst s;rw [UniformTM.step_reject]
    exact (callerMachine k).step_reject b
  rcases old_step_ne s a r with ⟨na,nr⟩
  rw [UniformTM.step_of_ne (callerMachine k) na nr]
  change actualRows k (actualOld k s) b=_
  dsimp only [actualRows,actualOld]
  rw [dif_pos s.isLt]
  rw [if_neg (uncut ⟨0,by decide⟩),if_neg (uncut ⟨1,by decide⟩),if_neg (uncut ⟨2,by decide⟩)]
  rfl
theorem old_rows_mirror : ∀ (k : Nat) (s : Fin (BodyIngress.machine k).stateCount) (b : Option Bool),
    (∀ mode : Fin 3,s≠BodyIngress.body k (SerializedBody.entry mode)) →
    (callerMachine k).step (oldState k s) b=
      (oldState k ((BodyIngress.machine k).step s b).1,((BodyIngress.machine k).step s b).2) := old_rows
/-- The copied BODY has identical literal rows at every strict pre-terminal control. -/
theorem eval_rows (k : Nat) (q : Fin SerializedBody.machine.stateCount) (b : Option Bool)
    (work : 4≤q.val) :
    (callerMachine k).step (evalState k q) b=
      (evalState k (SerializedBody.machine.step q b).1,(SerializedBody.machine.step q b).2) := by
  have na:evalState k q≠(callerMachine k).accept := by
    intro bad;have values:=congrArg Fin.val bad
    change (BodyIngress.machine k).stateCount+q.val=(BodyIngress.machine k).accept.val at values
    have bound:=(BodyIngress.machine k).accept.isLt;omega
  have nr:evalState k q≠(callerMachine k).reject := by
    intro bad;have values:=congrArg Fin.val bad
    change (BodyIngress.machine k).stateCount+q.val=(BodyIngress.machine k).reject.val at values
    have bound:=(BodyIngress.machine k).reject.isLt;omega
  rw [UniformTM.step_of_ne (callerMachine k) na nr]
  change actualRows k (actualEval k q) b=_
  dsimp only [actualRows,actualEval]
  rw [dif_neg (by omega : ¬(BodyIngress.machine k).stateCount+q.val<(BodyIngress.machine k).stateCount),
    dif_pos (by have bound:=q.isLt;change q.val<7500 at bound;omega)]
  have eqQ : (⟨(BodyIngress.machine k).stateCount+q.val-(BodyIngress.machine k).stateCount,by omega⟩ : Fin SerializedBody.machine.stateCount)=q := by
    apply Fin.ext;dsimp;omega
  rw [eqQ,show (BodyIngress.machine k).stateCount+q.val-(BodyIngress.machine k).stateCount=q.val by omega,if_neg (by omega : q.val≠0),if_neg (by omega : q.val≠1),if_neg (by omega : q.val≠2),if_neg (by omega : q.val≠3)]
  rfl
theorem eval_rows_mirror : ∀ (k : Nat) (q : Fin SerializedBody.machine.stateCount) (b : Option Bool),
    4≤q.val → (callerMachine k).step (evalState k q) b=
      (evalState k (SerializedBody.machine.step q b).1,(SerializedBody.machine.step q b).2) := eval_rows
private def symbol : Option Bool → Nat
  | none=>0
  | some false=>1
  | some true=>2
private def interpreted (k c : Nat) : Fin ((BodyIngress.machine k).stateCount+7500+3337) × Option Bool × Move :=
  let target:=c/9
  let q:=if h:target<3337 then native k ⟨target,h⟩
    else if h:target<3337+3 then evalState k (SerializedBody.entry ⟨target-3337,by omega⟩)
    else actualOld k (BodyIngress.machine k).reject
  (q,(if c/3%3=0 then none else some (decide (c/3%3=2))),
    if c%3=0 then .left else if c%3=1 then .stay else .right)
/-- A ROM code certificate is exactly one actual TM row, never an input-level instruction. -/
private theorem native_code (k : Nat) (q : Fin 3337) (b : Option Bool) (c : Nat)
    (code:instruction (3*q.val+symbol b)=c) :
    (callerMachine k).step (native k q) b=interpreted k c := by
  have na:native k q≠(callerMachine k).accept := by
    intro bad;have values:=congrArg Fin.val bad
    change (BodyIngress.machine k).stateCount+7500+q.val=(BodyIngress.machine k).accept.val at values
    have bound:=(BodyIngress.machine k).accept.isLt;omega
  have nr:native k q≠(callerMachine k).reject := by
    intro bad;have values:=congrArg Fin.val bad
    change (BodyIngress.machine k).stateCount+7500+q.val=(BodyIngress.machine k).reject.val at values
    have bound:=(BodyIngress.machine k).reject.isLt;omega
  rw [UniformTM.step_of_ne (callerMachine k) na nr]
  change actualRows k (actualNative k q) b=_
  dsimp only [actualRows,actualNative]
  rw [dif_neg (by omega : ¬(BodyIngress.machine k).stateCount+7500+q.val<(BodyIngress.machine k).stateCount),
    dif_neg (by omega : ¬(BodyIngress.machine k).stateCount+7500+q.val<(BodyIngress.machine k).stateCount+7500)]
  have eqQ : (⟨(BodyIngress.machine k).stateCount+7500+q.val-((BodyIngress.machine k).stateCount+7500),by omega⟩ : Fin 3337)=q := by
    apply Fin.ext;dsimp;omega
  rw [eqQ]
  change interpreted k (instruction (3*q.val+symbol b))=interpreted k c
  exact congrArg (interpreted k) code
#print axioms old_rows
#print axioms old_rows_mirror
#print axioms eval_rows
#print axioms eval_rows_mirror
end PhysicalCallerClosure
