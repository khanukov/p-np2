import BodyIngress.Native
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let env ← getEnv
  for (key,aliasName) in ([("rows","installerTable"),("native","installerAction")] :
    List (String × String)) do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith "_private.BodyIngress.Machine." &&
      n.toString.endsWith (".BodyIngress."++key)
    match found with
    | [(n,.defnInfo ci)] =>
      logInfo m!"private-term|{n}|kind=definition|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _ => throwError "Expected unique installer definition {key}: {found.map Prod.fst}"
run_cmd logInfo "stage|rows|private-definitions-selected"
private theorem extra_safe (k : Nat) (j : Fin 2035) :
    BodyIngress.extra k j ≠ (BodyIngress.machine k).accept ∧
    BodyIngress.extra k j ≠ (BodyIngress.machine k).reject ∧
    ∀ m : Fin 3, BodyIngress.extra k j ≠ BodyIngress.body k (SerializedBody.entry m) := by
  have high : (BodyIngress.extra k j).val=(CarryWindow.machine k).stateCount+7500+j.val := rfl
  have a : (BodyIngress.machine k).accept.val < (CarryWindow.machine k).stateCount :=
    (CarryWindow.machine k).accept.isLt
  have r : (BodyIngress.machine k).reject.val < (CarryWindow.machine k).stateCount :=
    (CarryWindow.machine k).reject.isLt
  refine ⟨?_,?_,?_⟩
  · intro eq
    have e:=congrArg Fin.val eq
    omega
  · intro eq
    have e:=congrArg Fin.val eq
    omega
  · intro m eq
    have low : (BodyIngress.body k (SerializedBody.entry m)).val=(CarryWindow.machine k).stateCount+4+m.val := by
      fin_cases m <;> rfl
    have e:=congrArg Fin.val eq
    have hm:=m.isLt
    omega
run_cmd logInfo "stage|rows|extra-safe-checked"
private theorem native_row (k : Nat) (j : Fin 2035) (b : Option Bool) :
    (BodyIngress.machine k).step (BodyIngress.extra k j) b=installerAction k j b := by
  have safe:=extra_safe k j
  rw [UniformTM.step_of_ne _ safe.1 safe.2.1]
  change installerTable k (BodyIngress.extra k j) b=_
  dsimp only [installerTable,BodyIngress.extra]
  rw [dif_neg (by omega),dif_neg (by omega)]
  have idx : (⟨(CarryWindow.machine k).stateCount+7500+j.val-
      ((CarryWindow.machine k).stateCount+7500),by omega⟩ : Fin 2035)=j := by
    apply Fin.ext
    dsimp only
    omega
  rw [idx]
run_cmd logInfo "stage|rows|native-row-checked"
end FullIngressClosure
