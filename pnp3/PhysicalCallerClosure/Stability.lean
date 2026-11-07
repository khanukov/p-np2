import PhysicalCallerClosure.Embedding
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1
section LiteralRows
set_option maxRecDepth 4000
private theorem done_row (b : Bool) (v : Option Bool) :
    SerializedBody.machine.step (SerializedBody.done b) v=(SerializedBody.done b,v,.stay) := by
  cases b <;> cases v with
  | none=>rfl
  | some v=>cases v <;> rfl
end LiteralRows
private theorem done_step {k N B : Nat} (c : Config (BodyIngress.machine k).stateCount N B)
    (b : Bool) (state : c.state=BodyIngress.body k (SerializedBody.done b)) :
    (BodyIngress.machine k).stepConfig c=c := by
  apply Config.ext_parts
  · dsimp only [UniformTM.stepConfig]
    rw [state,BodyIngress.body_rows,done_row]
  · dsimp only [UniformTM.stepConfig]
    rw [state,BodyIngress.body_rows,done_row]
    rfl
  · dsimp only [UniformTM.stepConfig]
    rw [state,BodyIngress.body_rows,done_row]
    funext i
    split_ifs with h
    · cases h;rfl
    · rfl
private theorem done_run {k N B : Nat} (c : Config (BodyIngress.machine k).stateCount N B)
    (b : Bool) (state : c.state=BodyIngress.body k (SerializedBody.done b)) :
    ∀ t,(BodyIngress.machine k).run t c=c := by
  intro t;induction t with
  | zero=>rfl
  | succ t ih=>rw [UniformTM.run,ih,done_step c b state]
private theorem before_entry_no_done {k N B e : Nat} (c : Config (BodyIngress.machine k).stateCount N B)
    (mode : Fin 3) (last : ((BodyIngress.machine k).run e c).state=
      BodyIngress.body k (SerializedBody.entry mode)) :
    ∀ u,u ≤ e → ∀ b,((BodyIngress.machine k).run u c).state≠BodyIngress.body k (SerializedBody.done b) := by
  intro u hu b bad
  have fixed:=done_run ((BodyIngress.machine k).run u c) b bad (e-u)
  rw [← UniformTM.run_add,show u+(e-u)=e by omega] at fixed
  have eq : BodyIngress.body k (SerializedBody.entry mode)=BodyIngress.body k (SerializedBody.done b) :=
    last.symm.trans ((congrArg Config.state fixed).trans bad)
  have entryVal : (BodyIngress.body k (SerializedBody.entry mode)).val=
      (CarryWindow.machine k).stateCount+(4+mode.val) := by fin_cases mode <;> rfl
  have doneVal : (BodyIngress.body k (SerializedBody.done b)).val=
      (CarryWindow.machine k).stateCount+(if b then 3 else 2) := by cases b <;> rfl
  have values:=congrArg Fin.val eq
  rw [entryVal,doneVal] at values
  cases b <;> simp at values <;> omega
end PhysicalCallerClosure
