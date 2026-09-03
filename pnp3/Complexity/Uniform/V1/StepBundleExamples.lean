import Complexity.Uniform.V1.StepBundle
import Complexity.Uniform.V1.Examples

namespace Pnp3.Complexity.Uniform.V1.Circuit

open Pnp3.ComplexityInterfaces.DagCircuit

def dispatchProbe : UniformTM :=
  ⟨4, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, by decide,
    fun _ s => match s with
      | none => (⟨1, by decide⟩, none, .stay)
      | some false => (⟨2, by decide⟩, some false, .stay)
      | some true => (⟨3, by decide⟩, some true, .stay)⟩

/-- Blank and tagged false reach their distinct public rows through the same
general `StepSpec` proof. -/
theorem stepBundle_blank_vs_false_dispatch :
    let blank := initialConfig dispatchProbe 1 (fun i : Fin 0 => i.elim0)
    let tagged := initialConfig dispatchProbe 1 (fun _ : Fin 1 => false)
    (stepBundle dispatchProbe 0 1).evalFun (encodeConfig dispatchProbe blank)
        (stateIndex dispatchProbe 0 1 dispatchProbe.accept) = true ∧
      (stepBundle dispatchProbe 1 1).evalFun (encodeConfig dispatchProbe tagged)
        (stateIndex dispatchProbe 1 1 dispatchProbe.reject) = true := by
  dsimp
  constructor <;> rw [← DagBundle.evalFun_apply, stepBundle_spec] <;>
    simp [UniformTM.stepConfig, UniformTM.step, dispatchProbe, initialConfig]

def maliciousTerminalProbe : UniformTM :=
  ⟨3, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, by decide,
    fun _ _ => (⟨0, by decide⟩, some true, .right)⟩

/-- Arbitrary raw terminal rows remain unobservable in the concrete bundle. -/
theorem stepBundle_terminal_rows_absorb {n budget : Nat}
    (c : Config maliciousTerminalProbe.stateCount n budget)
    (h : c.state = maliciousTerminalProbe.accept) :
    (stepBundle maliciousTerminalProbe n budget).evalFun
      (encodeConfig maliciousTerminalProbe c) = encodeConfig maliciousTerminalProbe c := by
  rw [stepBundle_spec]
  rw [maliciousTerminalProbe.stepConfig_accept c h]

def writeMoveProbe : UniformTM :=
  ⟨3, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, by decide,
    fun _ _ => (⟨1, by decide⟩, none, .left)⟩

/-- A blank write and left boundary clamp are consequences of `StepSpec`. -/
theorem stepBundle_blank_write_left_clamp :
    let c := initialConfig writeMoveProbe 1 (fun _ : Fin 1 => true)
    let zero : Fin (tapeLength 1 1) := ⟨0, by decide⟩
    (stepBundle writeMoveProbe 1 1).evalFun (encodeConfig writeMoveProbe c)
        (headIndex writeMoveProbe 1 1 zero) = true ∧
      (stepBundle writeMoveProbe 1 1).evalFun (encodeConfig writeMoveProbe c)
        (tapePresentIndex writeMoveProbe 1 1 zero) = false := by
  dsimp
  constructor <;> rw [← DagBundle.evalFun_apply, stepBundle_spec] <;>
    simp [UniformTM.stepConfig, UniformTM.step, writeMoveProbe, initialConfig,
      moveHead, symbolPresent]

def movingWriteProbe : UniformTM :=
  ⟨3, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, by decide,
    fun _ _ => (⟨1, by decide⟩, some false, .right)⟩

/-- Moving right writes the old head cell while the new-head cell stays blank. -/
theorem stepBundle_moving_write_old_head_only :
    let c := initialConfig movingWriteProbe 1 (fun _ : Fin 1 => true)
    let zero : Fin (tapeLength 1 1) := ⟨0, by decide⟩
    let one : Fin (tapeLength 1 1) := ⟨1, by decide⟩
    (stepBundle movingWriteProbe 1 1).evalFun (encodeConfig movingWriteProbe c)
        (tapePresentIndex movingWriteProbe 1 1 zero) = true ∧
      (stepBundle movingWriteProbe 1 1).evalFun (encodeConfig movingWriteProbe c)
        (tapeValueIndex movingWriteProbe 1 1 zero) = false ∧
      (stepBundle movingWriteProbe 1 1).evalFun (encodeConfig movingWriteProbe c)
        (headIndex movingWriteProbe 1 1 one) = true ∧
      (stepBundle movingWriteProbe 1 1).evalFun (encodeConfig movingWriteProbe c)
        (tapePresentIndex movingWriteProbe 1 1 one) = false := by
  dsimp
  repeat' apply And.intro
  all_goals rw [← DagBundle.evalFun_apply, stepBundle_spec]
  all_goals simp [UniformTM.stepConfig, UniformTM.step, movingWriteProbe,
    initialConfig, moveHead, symbolPresent, symbolValue, tapeLength]

end Pnp3.Complexity.Uniform.V1.Circuit
