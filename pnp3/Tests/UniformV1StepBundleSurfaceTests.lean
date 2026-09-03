import Complexity.Uniform.V1.StepBundleExamples

/-! Explicit P1b-3 action and full-step proposition surface. -/

namespace Pnp3.Tests.UniformV1StepBundle

open Pnp3.Complexity.Uniform.V1
open Pnp3.Complexity.Uniform.V1.Circuit
open Pnp3.ComplexityInterfaces.DagCircuit

#check actionWidth
#check indexedSymbol
#check rowIndex
#check nextStateActionIndex
#check moveActionIndex
#check writePresentActionIndex
#check writeValueActionIndex
#check actionSupportCount
#check actionPredicate
#check actionBundle
#check actionEncoding
#check actionBundle_evalFun
#check actionBundle_gates
#check actionBundle_gates_le
#check actionBundle_gates_le_target
#check stepBundle
#check stepBundle_eval_encodeConfig
#check stepBundle_spec
#check stepBundle_gates
#check stepBundle_gates_le

theorem check_actionBundle_evalFun (M : UniformTM) (n budget : Nat)
    (v : Bitstring (configWidth M n budget)) :
    (actionBundle M n budget).evalFun v = actionEncoding M n budget v :=
  actionBundle_evalFun M n budget v

theorem check_actionBundle_nextState (M : UniformTM) (n budget : Nat)
    (v : Bitstring (configWidth M n budget)) (q : Fin M.stateCount) :
    (actionBundle M n budget).evalOutput
      (Fin.natAdd (configWidth M n budget) (nextStateActionIndex M q)) v =
      nextStateBit M n budget v q := actionBundle_nextState M n budget v q

theorem check_actionBundle_move (M : UniformTM) (n budget : Nat)
    (v : Bitstring (configWidth M n budget)) (move : Move) :
    (actionBundle M n budget).evalOutput
      (Fin.natAdd (configWidth M n budget) (moveActionIndex M move)) v =
      moveBit M n budget v move := actionBundle_move M n budget v move

theorem check_actionBundle_writePresent (M : UniformTM) (n budget : Nat)
    (v : Bitstring (configWidth M n budget)) :
    (actionBundle M n budget).evalOutput
        (Fin.natAdd (configWidth M n budget) (writePresentActionIndex M)) v =
        writePresent M n budget v := actionBundle_writePresent M n budget v

theorem check_actionBundle_writeValue (M : UniformTM) (n budget : Nat)
    (v : Bitstring (configWidth M n budget)) :
    (actionBundle M n budget).evalOutput
        (Fin.natAdd (configWidth M n budget) (writeValueActionIndex M)) v =
        writeValue M n budget v := actionBundle_writeValue M n budget v

theorem check_actionBundle_eval_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) :
    (actionBundle M n budget).evalFun (encodeConfig M c) =
      Fin.addCases (encodeConfig M c)
        (fun o => actionPredicate M o (M.step c.state (c.tape c.head))) :=
  actionBundle_eval_encodeConfig M c

theorem check_actionBundle_gates (M : UniformTM) (n budget : Nat) :
    (actionBundle M n budget).gates =
      4 * tapeLength n budget + 10 * M.stateCount + 12 +
        actionSupportCount M (fun a => symbolPresent a.2.1) +
        actionSupportCount M (fun a => symbolValue a.2.1) :=
  actionBundle_gates M n budget

theorem check_actionBundle_gates_le (M : UniformTM) (n budget : Nat) :
    (actionBundle M n budget).gates ≤
      4 * tapeLength n budget + 16 * M.stateCount + 12 :=
  actionBundle_gates_le M n budget

theorem check_actionBundle_gates_le_target (M : UniformTM) (n budget : Nat) :
    (actionBundle M n budget).gates ≤
      4 * tapeLength n budget + 22 * M.stateCount + 7 :=
  actionBundle_gates_le_target M n budget

theorem check_stepBundle_eval_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) :
    (stepBundle M n budget).evalFun (encodeConfig M c) =
      encodedStep M n budget (encodeConfig M c) :=
  stepBundle_eval_encodeConfig M c

theorem check_stepBundle_spec (M : UniformTM) (n budget : Nat) :
    StepSpec M (stepBundle M n budget) := stepBundle_spec M n budget

theorem check_stepBundle_gates (M : UniformTM) (n budget : Nat) :
    (stepBundle M n budget).gates =
      19 * tapeLength n budget + 10 * M.stateCount + 12 +
        actionSupportCount M (fun a => symbolPresent a.2.1) +
        actionSupportCount M (fun a => symbolValue a.2.1) :=
  stepBundle_gates M n budget

theorem check_stepBundle_gates_le (M : UniformTM) (n budget : Nat) :
    (stepBundle M n budget).gates ≤
      19 * tapeLength n budget + 16 * M.stateCount + 13 :=
  stepBundle_gates_le M n budget

theorem check_stepBundle_terminal_rows_absorb {n budget : Nat} :
    let M : UniformTM :=
      ⟨3, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, by decide,
        fun _ _ => (⟨0, by decide⟩, some true, .right)⟩
    ∀ (acceptConfig rejectConfig : Config M.stateCount n budget),
      acceptConfig.state = M.accept →
      rejectConfig.state = M.reject →
      (stepBundle M n budget).evalFun (encodeConfig M acceptConfig) =
          encodeConfig M acceptConfig ∧
        (stepBundle M n budget).evalFun (encodeConfig M rejectConfig) =
          encodeConfig M rejectConfig :=
  stepBundle_terminal_rows_absorb

theorem check_stepBundle_blank_vs_false_dispatch :
    let M : UniformTM :=
      ⟨4, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, by decide,
        fun _ s => match s with
          | none => (⟨1, by decide⟩, none, .stay)
          | some false => (⟨2, by decide⟩, some false, .stay)
          | some true => (⟨3, by decide⟩, some true, .stay)⟩
    let blank := initialConfig M 1 (fun i : Fin 0 => i.elim0)
    let tagged := initialConfig M 1 (fun _ : Fin 1 => false)
    (stepBundle M 0 1).evalFun (encodeConfig M blank)
        (stateIndex M 0 1 M.accept) = true ∧
      (stepBundle M 1 1).evalFun (encodeConfig M tagged)
        (stateIndex M 1 1 M.reject) = true :=
  stepBundle_blank_vs_false_dispatch

theorem check_stepBundle_blank_write_left_clamp :
    let M : UniformTM :=
      ⟨3, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, by decide,
        fun _ _ => (⟨1, by decide⟩, none, .left)⟩
    let c := initialConfig M 1 (fun _ : Fin 1 => true)
    let zero : Fin (tapeLength 1 1) := ⟨0, by decide⟩
    (stepBundle M 1 1).evalFun (encodeConfig M c)
        (headIndex M 1 1 zero) = true ∧
      (stepBundle M 1 1).evalFun (encodeConfig M c)
        (tapePresentIndex M 1 1 zero) = false :=
  stepBundle_blank_write_left_clamp

theorem check_stepBundle_moving_write_old_head_only :
    let M : UniformTM :=
      ⟨3, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, by decide,
        fun _ _ => (⟨1, by decide⟩, some false, .right)⟩
    let c := initialConfig M 1 (fun _ : Fin 1 => true)
    let zero : Fin (tapeLength 1 1) := ⟨0, by decide⟩
    let one : Fin (tapeLength 1 1) := ⟨1, by decide⟩
    (stepBundle M 1 1).evalFun (encodeConfig M c)
        (tapePresentIndex M 1 1 zero) = true ∧
      (stepBundle M 1 1).evalFun (encodeConfig M c)
        (tapeValueIndex M 1 1 zero) = false ∧
      (stepBundle M 1 1).evalFun (encodeConfig M c)
        (headIndex M 1 1 one) = true ∧
      (stepBundle M 1 1).evalFun (encodeConfig M c)
        (tapePresentIndex M 1 1 one) = false :=
  stepBundle_moving_write_old_head_only

end Pnp3.Tests.UniformV1StepBundle
