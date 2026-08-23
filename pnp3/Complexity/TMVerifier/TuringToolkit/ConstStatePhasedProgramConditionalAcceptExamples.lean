import Complexity.TMVerifier.TuringToolkit.GateWrappers
import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgramConditionalAccept
import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgramInitialConfig

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace TM
namespace GateEvalCS

open Pnp3.Internal.PsubsetPpoly.TM
open ConstStatePhasedProgram

/-!
## Constant gate followed by conditional acceptance

**Progress classification:** Infrastructure.  This module is a focused
end-to-end exercise of the existing sequential-run API.  It constructs no
content verifier, proves no verifier runtime bound, reduces neither pnp4
mainline source obligation, and makes no `P ≠ NP` claim.

The two operands already have the same standalone time bound, so their tape
lengths agree and no padding is used.  Generic padding, arbitrary functional
clocks, and a uniform clock discipline remain deliberately open.
-/

/-- Write the constant `b` at cell `d`, then accept exactly when that cell is
true.  The conditional terminal is the explicit right operand, so its final
local state is not erased by an `idleCS` handoff. -/
def gateConstThenAcceptIfCS (b : Bool) (d : Nat) :
    ConstStatePhasedProgram (Bool × Bool) :=
  seq (gateConstCS b d) (acceptIfCellCS d)

/-- The two standalone operands have definitionally equal clocks.  This is
kept out of the simp set because `gateConstCS_timeBound` already rewrites the
same left-hand side to its arithmetic normal form. -/
theorem gateConstCS_timeBound_eq_acceptIfCellCS_timeBound
    (b : Bool) (d n : Nat) :
    (gateConstCS b d).timeBound n = (acceptIfCellCS d).timeBound n := rfl

/-- Exact clock of the concrete two-program composite, including its single
handoff step. -/
@[simp] theorem gateConstThenAcceptIfCS_timeBound
    (b : Bool) (d n : Nat) :
    (gateConstThenAcceptIfCS b d).timeBound n = 4 * d + 7 := by
  simp [gateConstThenAcceptIfCS, ConstStatePhasedProgram.seq_timeBound]
  omega

/-- Dependency-closed correctness from the composite machine's actual input
configuration.  At the exact clock, the local state is `(b,b)`, the head is
back at its initial cell, and the complete widened tape is exactly the initial
tape with cell `d` set to `b`. -/
theorem gateConstThenAcceptIfCS_runSpec
    (b : Bool) (d : Nat) {n : Nat}
    (x : Boolcube.Point n) :
    let R := gateConstThenAcceptIfCS b d
    let c₀ := R.toPhased.toTM.initialConfig x
    let hd : d < R.toPhased.toTM.tapeLength n := by
      simp [R, gateConstThenAcceptIfCS, TM.tapeLength]
      omega
    RunSpec R c₀ (fun cf =>
      cf.state.snd = (b, b) ∧
      cf.head = c₀.head ∧
      cf.tape = c₀.write ⟨d, hd⟩ b) := by
  dsimp only
  let P₁ := gateConstCS b d
  let P₂ := acceptIfCellCS d
  let R := gateConstThenAcceptIfCS b d
  let c₁ := P₁.toPhased.toTM.initialConfig x
  let c₀ := R.toPhased.toTM.initialConfig x
  have hLen : P₁.toPhased.toTM.tapeLength n ≤ P₂.toPhased.toTM.tapeLength n := by
    show n + P₁.timeBound n + 1 ≤ n + P₂.timeBound n + 1
    simp only [P₁, P₂, gateConstCS_timeBound, acceptIfCellCS_timeBound]
    omega
  have hBound₁ : c₁.head.val + d < P₁.toPhased.toTM.tapeLength n := by
    simp [c₁, P₁, TM.initialConfig, TM.tapeLength]
    omega
  obtain ⟨_, _, hP₁Accept, _, hP₁Head, hP₁Tape⟩ :=
    CombineAtOffset.combineAtOffsetCS_run_full d d d
      (le_refl _) (le_refl _) (fun _ _ => b) c₁ rfl rfl hBound₁
  let c₁Final := TM.runConfig (M := P₁.toPhased.toTM) c₁ (P₁.timeBound n)
  have hP₁Head' : c₁Final.head = c₁.head := by
    simpa [c₁Final, P₁, gateConstCS_timeBound] using hP₁Head
  have hP₁Tape' : c₁Final.tape =
      c₁.write ⟨c₁.head.val + d, hBound₁⟩ b := by
    simpa [c₁Final, P₁, gateConstCS_timeBound] using hP₁Tape
  let post₁ : Configuration (M := P₁.toPhased.toTM) n → Prop := fun cf =>
    cf.head = c₁.head ∧ cf.tape = c₁.write ⟨c₁.head.val + d, hBound₁⟩ b
  let spec₁ : RunSpec P₁ c₁ post₁ := {
    prefixSafe := by
      intro s hs
      exact CombineAtOffset.combineAtOffsetCS_run_invariants_in_prefix
        d d d (le_refl _) (le_refl _) (fun _ _ => b)
        c₁ rfl rfl hBound₁ s (by simpa [P₁] using hs) |>.2
    reachesAcceptPhase := by simpa [P₁] using hP₁Accept
    postcondition := by exact ⟨hP₁Head', hP₁Tape'⟩
  }
  let hHead : c₁Final.head.val < P₂.toPhased.toTM.tapeLength n :=
    Nat.lt_of_lt_of_le c₁Final.head.isLt hLen
  let c₂Init := liftP1ToP2 P₁ P₂ c₁Final hHead
  have hBound₂ : c₂Init.head.val + d < P₂.toPhased.toTM.tapeLength n := by
    change c₁Final.head.val + d < P₂.toPhased.toTM.tapeLength n
    rw [hP₁Head']
    simp [c₁, P₂, TM.initialConfig, TM.tapeLength]
    omega
  have hFlag : c₂Init.tape ⟨c₂Init.head.val + d, hBound₂⟩ = b := by
    have hHeadVal : c₁Final.head.val = 0 := by
      rw [hP₁Head']
      rfl
    have hd₁ : d < P₁.toPhased.toTM.tapeLength n := by
      simpa [c₁, TM.initialConfig] using hBound₁
    dsimp only [c₂Init, liftP1ToP2]
    simp only [hHeadVal, Nat.zero_add]
    rw [dif_pos hd₁, hP₁Tape']
    simp [c₁, TM.initialConfig]
  let post₂ : Configuration (M := P₂.toPhased.toTM) n → Prop := fun cf =>
    cf.state.snd = (b, b) ∧ cf.head = c₂Init.head ∧ cf.tape = c₂Init.tape
  let spec₂Raw := acceptIfCellCS_runSpec d c₂Init rfl rfl hBound₂
  let spec₂ : RunSpec P₂ c₂Init post₂ := {
    prefixSafe := spec₂Raw.prefixSafe
    reachesAcceptPhase := spec₂Raw.reachesAcceptPhase
    postcondition := by
      exact ⟨by simpa [hFlag] using spec₂Raw.postcondition.1,
        spec₂Raw.postcondition.2⟩
  }
  let c₂Final := TM.runConfig (M := P₂.toPhased.toTM) c₂Init (P₂.timeBound n)
  have hInit : c₀ = embedSeqConfig P₁ P₂ c₁ := by
    simpa [c₀, c₁, R, P₁, P₂, gateConstThenAcceptIfCS] using
      (initialConfig_seq_eq_embedSeqConfig_initialConfig P₁ P₂ x)
  have combined := RunSpec.seq P₁ P₂ c₁ post₁ post₂ hLen spec₁ spec₂
  let hd : d < R.toPhased.toTM.tapeLength n := by
    simp [R, gateConstThenAcceptIfCS, TM.tapeLength]
    omega
  change RunSpec R c₀ (fun cf =>
    cf.state.snd = (b, b) ∧ cf.head = c₀.head ∧
      cf.tape = c₀.write ⟨d, hd⟩ b)
  rw [hInit]
  change RunSpec (seq P₁ P₂) (embedSeqConfig P₁ P₂ c₁) (fun cf =>
    cf.state.snd = (b, b) ∧
      cf.head = (embedSeqConfig P₁ P₂ c₁).head ∧
      cf.tape = (embedSeqConfig P₁ P₂ c₁).write ⟨d, hd⟩ b)
  refine {
    prefixSafe := combined.prefixSafe
    reachesAcceptPhase := combined.reachesAcceptPhase
    postcondition := ?_
  }
  have h := combined.postcondition
  rcases h with ⟨hFinal, hPost₁, hPost₂⟩
  rw [hFinal]
  refine ⟨embedSeqP2Config_state_snd P₁ P₂ c₂Final ▸ hPost₂.1, ?_, ?_⟩
  · apply Fin.ext
    rw [embedSeqP2Config_head_val, hPost₂.2.1]
    change c₁Final.head.val = c₀.head.val
    rw [hP₁Head']
    rfl
  · have hFinalToLift :
        (embedSeqP2Config P₁ P₂ c₂Final).tape =
          (embedSeqP2Config P₁ P₂ c₂Init).tape := by
      funext i
      by_cases hi : i.val < P₂.toPhased.toTM.tapeLength n
      · rw [embedSeqP2Config_tape_in_range P₁ P₂ c₂Final i hi,
          embedSeqP2Config_tape_in_range P₁ P₂ c₂Init i hi]
        exact congrFun hPost₂.2.2 ⟨i.val, hi⟩
      · rw [embedSeqP2Config_tape_out_of_range P₁ P₂ c₂Final i (Nat.not_lt.mp hi),
          embedSeqP2Config_tape_out_of_range P₁ P₂ c₂Init i (Nat.not_lt.mp hi)]
    rw [hFinalToLift,
      embedSeqP2Config_liftP1ToP2_tape P₁ P₂ c₁Final hHead hLen]
    funext i
    by_cases hid : i.val = d
    · have hi₁ : i.val < P₁.toPhased.toTM.tapeLength n := by
        rw [hid]
        simpa [c₁, TM.initialConfig] using hBound₁
      rw [embedSeqConfig_tape_in_range P₁ P₂ c₁Final i hi₁, hP₁Tape']
      have hiEq : (⟨i.val, hi₁⟩ : Fin (P₁.toPhased.toTM.tapeLength n)) =
          ⟨c₁.head.val + d, hBound₁⟩ := by
        apply Fin.ext
        simpa [c₁, TM.initialConfig] using hid
      rw [hiEq, Configuration.write_self]
      have hCompEq : i = (⟨d, hd⟩ : Fin (R.toPhased.toTM.tapeLength n)) :=
        Fin.ext hid
      rw [hCompEq]
      exact (Configuration.write_self (embedSeqConfig P₁ P₂ c₁) ⟨d, hd⟩ b).symm
    · have hCompNe : i ≠ (⟨d, hd⟩ : Fin (R.toPhased.toTM.tapeLength n)) := by
        intro hEq
        exact hid (congrArg Fin.val hEq)
      rw [Configuration.write_other (embedSeqConfig P₁ P₂ c₁) hCompNe b]
      by_cases hi₁ : i.val < P₁.toPhased.toTM.tapeLength n
      · rw [embedSeqConfig_tape_in_range P₁ P₂ c₁Final i hi₁, hP₁Tape']
        have hGateNe : (⟨i.val, hi₁⟩ : Fin (P₁.toPhased.toTM.tapeLength n)) ≠
            ⟨c₁.head.val + d, hBound₁⟩ := by
          intro hEq
          apply hid
          simpa [c₁, TM.initialConfig] using congrArg Fin.val hEq
        rw [Configuration.write_other c₁ hGateNe b]
        exact (embedSeqConfig_tape_in_range P₁ P₂ c₁ i hi₁).symm
      · rw [embedSeqConfig_tape_out_of_range P₁ P₂ c₁Final i (Nat.not_lt.mp hi₁)]
        exact (embedSeqConfig_tape_out_of_range P₁ P₂ c₁ i (Nat.not_lt.mp hi₁)).symm

/-- End-to-end acceptance of the concrete composite, uniformly covering the
accepting (`b = true`) and rejecting (`b = false`) executions. -/
theorem gateConstThenAcceptIfCS_accepts
    (b : Bool) (d : Nat) {n : Nat}
    (x : Boolcube.Point n) :
    TM.accepts (M := (gateConstThenAcceptIfCS b d).toPhased.toTM) n x = b := by
  let R := gateConstThenAcceptIfCS b d
  let c₀ := R.toPhased.toTM.initialConfig x
  let hd : d < R.toPhased.toTM.tapeLength n := by
    simp [R, gateConstThenAcceptIfCS, TM.tapeLength]
    omega
  let spec := gateConstThenAcceptIfCS_runSpec b d x
  have hLocal : (R.toPhased.toTM.run x).state.snd = (b, b) := by
    exact spec.postcondition.1
  rw [spec.accepts_eq_decide_local]
  rw [hLocal]
  change decide ((b, b) = (true, true)) = b
  cases b <;> rfl

end GateEvalCS
end TM
end PsubsetPpoly
end Internal
end Pnp3
