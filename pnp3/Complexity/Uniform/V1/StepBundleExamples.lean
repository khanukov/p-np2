import Complexity.Uniform.V1.StepBundle
import Complexity.Uniform.V1.Examples

namespace Pnp3.Complexity.Uniform.V1.Circuit

open Pnp3.ComplexityInterfaces.DagCircuit

private def dispatchProbe : UniformTM :=
  ⟨4, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, by decide,
    fun _ s => match s with
      | none => (⟨1, by decide⟩, none, .stay)
      | some false => (⟨2, by decide⟩, some false, .stay)
      | some true => (⟨3, by decide⟩, some true, .stay)⟩

/-- Blank and tagged false reach their distinct public rows through the same
general `StepSpec` proof. -/
theorem stepBundle_blank_vs_false_dispatch :
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
        (stateIndex M 1 1 M.reject) = true := by
  change
    (let blank := initialConfig dispatchProbe 1 (fun i : Fin 0 => i.elim0)
     let tagged := initialConfig dispatchProbe 1 (fun _ : Fin 1 => false)
     (stepBundle dispatchProbe 0 1).evalFun (encodeConfig dispatchProbe blank)
          (stateIndex dispatchProbe 0 1 dispatchProbe.accept) = true ∧
       (stepBundle dispatchProbe 1 1).evalFun (encodeConfig dispatchProbe tagged)
          (stateIndex dispatchProbe 1 1 dispatchProbe.reject) = true)
  dsimp
  constructor <;> rw [← DagBundle.evalFun_apply, stepBundle_spec] <;>
    simp [UniformTM.stepConfig, UniformTM.step, dispatchProbe, initialConfig]

private def maliciousTerminalProbe : UniformTM :=
  ⟨3, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, by decide,
    fun _ _ => (⟨0, by decide⟩, some true, .right)⟩

/-- Arbitrary raw accept and reject rows remain unobservable in the concrete bundle. -/
theorem stepBundle_terminal_rows_absorb {n budget : Nat} :
    let M : UniformTM :=
        ⟨3, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, by decide,
          fun _ _ => (⟨0, by decide⟩, some true, .right)⟩
      ∀ (acceptConfig rejectConfig : Config M.stateCount n budget),
        acceptConfig.state = M.accept →
        rejectConfig.state = M.reject →
        (stepBundle M n budget).evalFun (encodeConfig M acceptConfig) =
            encodeConfig M acceptConfig ∧
          (stepBundle M n budget).evalFun (encodeConfig M rejectConfig) =
            encodeConfig M rejectConfig := by
  change ∀ (acceptConfig rejectConfig :
      Config maliciousTerminalProbe.stateCount n budget),
    acceptConfig.state = maliciousTerminalProbe.accept →
    rejectConfig.state = maliciousTerminalProbe.reject →
    (stepBundle maliciousTerminalProbe n budget).evalFun
          (encodeConfig maliciousTerminalProbe acceptConfig) =
          encodeConfig maliciousTerminalProbe acceptConfig ∧
      (stepBundle maliciousTerminalProbe n budget).evalFun
          (encodeConfig maliciousTerminalProbe rejectConfig) =
          encodeConfig maliciousTerminalProbe rejectConfig
  intro acceptConfig rejectConfig ha hr
  constructor
  · rw [stepBundle_spec]
    rw [maliciousTerminalProbe.stepConfig_accept acceptConfig ha]
  · rw [stepBundle_spec]
    rw [maliciousTerminalProbe.stepConfig_reject rejectConfig hr]

private def writeMoveProbe : UniformTM :=
  ⟨3, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, by decide,
    fun _ _ => (⟨1, by decide⟩, none, .left)⟩

/-- A blank write and left boundary clamp are consequences of `StepSpec`. -/
theorem stepBundle_blank_write_left_clamp :
    let M : UniformTM :=
      ⟨3, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, by decide,
        fun _ _ => (⟨1, by decide⟩, none, .left)⟩
    let c := initialConfig M 1 (fun _ : Fin 1 => true)
    let zero : Fin (tapeLength 1 1) := ⟨0, by decide⟩
    (stepBundle M 1 1).evalFun (encodeConfig M c)
        (headIndex M 1 1 zero) = true ∧
      (stepBundle M 1 1).evalFun (encodeConfig M c)
        (tapePresentIndex M 1 1 zero) = false := by
  change
    (let c := initialConfig writeMoveProbe 1 (fun _ : Fin 1 => true)
     let zero : Fin (tapeLength 1 1) := ⟨0, by decide⟩
     (stepBundle writeMoveProbe 1 1).evalFun (encodeConfig writeMoveProbe c)
          (headIndex writeMoveProbe 1 1 zero) = true ∧
       (stepBundle writeMoveProbe 1 1).evalFun (encodeConfig writeMoveProbe c)
          (tapePresentIndex writeMoveProbe 1 1 zero) = false)
  dsimp
  constructor <;> rw [← DagBundle.evalFun_apply, stepBundle_spec] <;>
    simp [UniformTM.stepConfig, UniformTM.step, writeMoveProbe, initialConfig,
      moveHead, symbolPresent]

private def movingWriteProbe : UniformTM :=
  ⟨3, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, by decide,
    fun _ _ => (⟨1, by decide⟩, some false, .right)⟩

/-- Moving right writes the old head cell while the new-head cell stays blank. -/
theorem stepBundle_moving_write_old_head_only :
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
        (tapePresentIndex M 1 1 one) = false := by
  change
    (let c := initialConfig movingWriteProbe 1 (fun _ : Fin 1 => true)
     let zero : Fin (tapeLength 1 1) := ⟨0, by decide⟩
     let one : Fin (tapeLength 1 1) := ⟨1, by decide⟩
     (stepBundle movingWriteProbe 1 1).evalFun (encodeConfig movingWriteProbe c)
          (tapePresentIndex movingWriteProbe 1 1 zero) = true ∧
       (stepBundle movingWriteProbe 1 1).evalFun (encodeConfig movingWriteProbe c)
          (tapeValueIndex movingWriteProbe 1 1 zero) = false ∧
       (stepBundle movingWriteProbe 1 1).evalFun (encodeConfig movingWriteProbe c)
          (headIndex movingWriteProbe 1 1 one) = true ∧
       (stepBundle movingWriteProbe 1 1).evalFun (encodeConfig movingWriteProbe c)
          (tapePresentIndex movingWriteProbe 1 1 one) = false)
  dsimp
  repeat' apply And.intro
  all_goals rw [← DagBundle.evalFun_apply, stepBundle_spec]
  all_goals simp [UniformTM.stepConfig, UniformTM.step, movingWriteProbe,
    initialConfig, moveHead, symbolPresent, symbolValue, tapeLength]

end Pnp3.Complexity.Uniform.V1.Circuit
