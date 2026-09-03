import Complexity.Uniform.V1.StepKernel
import Complexity.Uniform.V1.Examples

namespace Pnp3.Complexity.Uniform.V1.Circuit

open Pnp3.ComplexityInterfaces

/-- The general kernel theorem specializes to the true first-bit row: the
machine selects accept and preserves the tagged true symbol. -/
theorem firstBit_true_encodedStep :
    let x : Bitstring 1 := fun _ => true
    let c := initialConfig firstBitMachine 1 x
    let cell0 : Fin (tapeLength 1 1) := ⟨0, by simp [tapeLength]⟩
    encodedStep firstBitMachine 1 1 (encodeConfig firstBitMachine c)
        (stateIndex firstBitMachine 1 1 firstBitMachine.accept) = true ∧
      encodedStep firstBitMachine 1 1 (encodeConfig firstBitMachine c)
        (tapePresentIndex firstBitMachine 1 1 cell0) = true ∧
      encodedStep firstBitMachine 1 1 (encodeConfig firstBitMachine c)
        (tapeValueIndex firstBitMachine 1 1 cell0) = true := by
  dsimp
  rw [encodedStep_encodeConfig]
  simp [UniformTM.stepConfig, UniformTM.step, firstBitMachine, initialConfig,
    symbolPresent, symbolValue]

/-- Empty input scans the literal blank, selects reject, and preserves blank
on the old head cell. -/
theorem firstBit_empty_encodedStep :
    let x : Bitstring 0 := fun i => i.elim0
    let c := initialConfig firstBitMachine 1 x
    let cell0 : Fin (tapeLength 0 1) := ⟨0, by simp [tapeLength]⟩
    encodedStep firstBitMachine 0 1 (encodeConfig firstBitMachine c)
        (stateIndex firstBitMachine 0 1 firstBitMachine.reject) = true ∧
      encodedStep firstBitMachine 0 1 (encodeConfig firstBitMachine c)
        (tapePresentIndex firstBitMachine 0 1 cell0) = false ∧
      encodedStep firstBitMachine 0 1 (encodeConfig firstBitMachine c)
        (tapeValueIndex firstBitMachine 0 1 cell0) = false := by
  dsimp
  rw [encodedStep_encodeConfig]
  simp [UniformTM.stepConfig, UniformTM.step, firstBitMachine, initialConfig,
    symbolPresent, symbolValue]

/-- One parity-scanner step moves right into the odd scan state, preserves the
written old cell, and leaves the destination cell blank. -/
theorem lengthParity_one_step_encodedStep (bit : Bool) :
    let x : Bitstring 1 := fun _ => bit
    let c := initialConfig lengthParityMachine 1 x
    let cell0 : Fin (tapeLength 1 1) := ⟨0, by simp [tapeLength]⟩
    let cell1 : Fin (tapeLength 1 1) := ⟨1, by simp [tapeLength]⟩
    encodedStep lengthParityMachine 1 1 (encodeConfig lengthParityMachine c)
        (stateIndex lengthParityMachine 1 1 ⟨1, by decide⟩) = true ∧
      encodedStep lengthParityMachine 1 1 (encodeConfig lengthParityMachine c)
        (headIndex lengthParityMachine 1 1 cell1) = true ∧
      encodedStep lengthParityMachine 1 1 (encodeConfig lengthParityMachine c)
        (tapePresentIndex lengthParityMachine 1 1 cell0) = true ∧
      encodedStep lengthParityMachine 1 1 (encodeConfig lengthParityMachine c)
        (tapeValueIndex lengthParityMachine 1 1 cell0) = bit ∧
      encodedStep lengthParityMachine 1 1 (encodeConfig lengthParityMachine c)
        (tapePresentIndex lengthParityMachine 1 1 cell1) = false ∧
      encodedStep lengthParityMachine 1 1 (encodeConfig lengthParityMachine c)
        (tapeValueIndex lengthParityMachine 1 1 cell1) = false := by
  dsimp
  rw [encodedStep_encodeConfig]
  simp [UniformTM.stepConfig, UniformTM.step, lengthParityMachine, initialConfig,
    moveHead, symbolPresent, symbolValue]
  norm_num [tapeLength]

end Pnp3.Complexity.Uniform.V1.Circuit
