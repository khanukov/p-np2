import PhysicalCallerClosure.SourceInitialize
import PhysicalCallerClosure.Embedding
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command Tactic
private def select (owner : Name) (leaf kind : String) : TacticM Unit := do
  let e←getEnv
  let n:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure")
  let some ci:=e.find? n | throwError "Missing exact paid-row support {n}"
  let actual:=match ci with | .defnInfo _=>"definition" | .thmInfo _=>"theorem" | .ctorInfo _=>"constructor" | .inductInfo _=>"inductive" | _=>"other"
  unless actual==kind do throwError "Wrong paid-row support kind"
  let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
  unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
  unless e.header.moduleNames[i]! == owner do throwError "Wrong paid-row support owner"
  logInfo m!"paid-row-adapter|{n}|{ci.type}"
  closeMainGoal `select (mkConst n (ci.levelParams.map Level.param))
run_cmd do
  let e←getEnv
  for (owner,leaves) in [(`PhysicalCallerClosure.Controller,["rows","liftOld"]),
      (`PhysicalCallerClosure.SourceInitialize,["startControl"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing paid-row term {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong owner"
      logInfo m!"paid-row-open|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private theorem body_injective : ∀ k,Function.Injective (BodyIngress.body k) := by
  run_tac select `PhysicalCallerClosure.Embedding "body_injective" "theorem"
private theorem old_step_ne : ∀ {k : Nat} (s : Fin (BodyIngress.machine k).stateCount),
    s≠(BodyIngress.machine k).accept → s≠(BodyIngress.machine k).reject →
    oldState k s≠(callerMachine k).accept ∧ oldState k s≠(callerMachine k).reject := by
  run_tac select `PhysicalCallerClosure.Rows "old_step_ne" "theorem"
private theorem cut_ne (k : Nat) (mode : Fin 3) :
    oldState k (BodyIngress.body k (SerializedBody.entry mode))≠(callerMachine k).accept ∧
    oldState k (BodyIngress.body k (SerializedBody.entry mode))≠(callerMachine k).reject := by
  have entryVal:(BodyIngress.body k (SerializedBody.entry mode)).val=(CarryWindow.machine k).stateCount+(4+mode.val):=by
    fin_cases mode <;> rfl
  have na:BodyIngress.body k (SerializedBody.entry mode)≠(BodyIngress.machine k).accept:=by
    intro bad
    have values:=congrArg Fin.val bad
    rw [entryVal] at values
    change (CarryWindow.machine k).stateCount+(4+mode.val)=(CarryWindow.machine k).accept.val at values
    have bound:=(CarryWindow.machine k).accept.isLt
    omega
  have nr:BodyIngress.body k (SerializedBody.entry mode)≠(BodyIngress.machine k).reject:=by
    intro bad
    have values:=congrArg Fin.val bad
    rw [entryVal] at values
    change (CarryWindow.machine k).stateCount+(4+mode.val)=(CarryWindow.machine k).reject.val at values
    have bound:=(CarryWindow.machine k).reject.isLt
    omega
  exact old_step_ne _ na nr
private theorem cut_row (k : Nat) (mode : Fin 3) (b : Option Bool) :
    (callerMachine k).step (oldState k (BodyIngress.body k (SerializedBody.entry mode))) b=(startControl k mode,b,.stay) := by
  rw [UniformTM.step_of_ne (callerMachine k) (cut_ne k mode).1 (cut_ne k mode).2]
  change rows k (liftOld k (BodyIngress.body k (SerializedBody.entry mode))) b=_
  dsimp only [rows,liftOld]
  have bound:(BodyIngress.body k (SerializedBody.entry mode)).val < (BodyIngress.machine k).stateCount:=(BodyIngress.body k (SerializedBody.entry mode)).isLt
  rw [dif_pos bound]
  have eta:(⟨(BodyIngress.body k (SerializedBody.entry mode)).val,bound⟩:Fin (BodyIngress.machine k).stateCount)=
      BodyIngress.body k (SerializedBody.entry mode):=by apply Fin.ext;rfl
  rw [eta]
  fin_cases mode
  · rw [if_pos rfl];rfl
  · have ne:BodyIngress.body k (SerializedBody.entry ⟨1,by decide⟩)≠BodyIngress.body k (SerializedBody.entry ⟨0,by decide⟩):=by
      intro h;exact (show SerializedBody.entry ⟨1,by decide⟩≠SerializedBody.entry ⟨0,by decide⟩ by decide) (body_injective k h)
    rw [if_neg ne,if_pos rfl];rfl
  · have ne0:BodyIngress.body k (SerializedBody.entry ⟨2,by decide⟩)≠BodyIngress.body k (SerializedBody.entry ⟨0,by decide⟩):=by
      intro h;exact (show SerializedBody.entry ⟨2,by decide⟩≠SerializedBody.entry ⟨0,by decide⟩ by decide) (body_injective k h)
    have ne1:BodyIngress.body k (SerializedBody.entry ⟨2,by decide⟩)≠BodyIngress.body k (SerializedBody.entry ⟨1,by decide⟩):=by
      intro h;exact (show SerializedBody.entry ⟨2,by decide⟩≠SerializedBody.entry ⟨1,by decide⟩ by decide) (body_injective k h)
    rw [if_neg ne0,if_neg ne1,if_pos rfl];rfl
private theorem cut_step (k N B : Nat) (mode : Fin 3) (h : Fin (tapeLength N B))
    (T : Fin (tapeLength N B) → Option Bool) :
    (callerMachine k).run 1 ⟨oldState k (BodyIngress.body k (SerializedBody.entry mode)),h,T⟩=
      ⟨startControl k mode,h,T⟩ := by
  change (callerMachine k).stepConfig ⟨oldState k (BodyIngress.body k (SerializedBody.entry mode)),h,T⟩=⟨startControl k mode,h,T⟩
  apply Config.ext_parts
  · exact congrArg Prod.fst (cut_row k mode (T h))
  · apply Fin.ext
    change (moveHead h ((callerMachine k).step _ (T h)).2.2).val=h.val
    rw [cut_row];rfl
  · funext i
    dsimp only [UniformTM.stepConfig]
    rw [cut_row]
    by_cases eq:i=h
    · subst i;simp
    · simp only [if_neg eq]
end PhysicalCallerClosure
