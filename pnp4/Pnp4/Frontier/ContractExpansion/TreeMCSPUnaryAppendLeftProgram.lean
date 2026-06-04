import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram
import Complexity.TMVerifier.TuringToolkit.BinaryCounter

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM

/-!
# Self-loop leftward unary-append (NP-verifier track — D2 transcoder, D2t-3c-α)

The binary→unary loop (`TM_VERIFIER_STRATEGY.md` §12, D2t-3c) keeps the unary output `U` to the **left**
of the binary counter `B`, and grows `U` **leftward**, so the loop body navigates only over uniform
`1`-stretches (never `B`'s mixed bits — the resolution of the navigation crux).  `selfLoopAppendLeftOne`
is that growth step: starting on `U`'s `1`-block it scans **left** over the `1`s (writing each back) to
the first `0`, where it writes a single `1` (the append) and stops — extending `U` by one cell on its
left end.

It is the writing dual of `selfLoopScanLeftOne` (which scans the same `1`-block leftward but stops
*without* writing) and the leftward mirror of `selfLoopAppendOne`.  Fixed 2-phase, variable-width.  This
ships the program and its standalone run-behaviour (scan invariant + append-stop); the `seqP2`
composition lift is the follow-up iteration.  Builds no verifier and proves no separation; all surfaces
carry only the standard `[propext, Classical.choice, Quot.sound]` triple.
-/

/-- Leftward unary single-append: phase `0` reading a `1` writes it back and moves **left** (scanning
`U`'s block); reading the first `0` writes a `1` (the append) and stops (phase `1`). -/
def selfLoopAppendLeftOne : ConstStatePhasedProgram Unit where
  numPhases := 2
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨1, by omega⟩
  acceptState := ()
  transition := fun i _ b =>
    if i.val = 0 then
      if b then (⟨0, by omega⟩, (), true, Move.left)
      else (⟨1, by omega⟩, (), true, Move.stay)
    else
      (⟨1, by omega⟩, (), b, Move.stay)
  timeBound := fun n => n

@[simp] theorem selfLoopAppendLeftOne_timeBound (n : Nat) : selfLoopAppendLeftOne.timeBound n = n := rfl
@[simp] theorem selfLoopAppendLeftOne_numPhases : selfLoopAppendLeftOne.numPhases = 2 := rfl
@[simp] theorem selfLoopAppendLeftOne_startPhase_val :
    (selfLoopAppendLeftOne.startPhase : Nat) = 0 := rfl
@[simp] theorem selfLoopAppendLeftOne_acceptPhase_val :
    (selfLoopAppendLeftOne.acceptPhase : Nat) = 1 := rfl

/-- The leftward append never moves the head right (it moves left while scanning, otherwise stays). -/
theorem selfLoopAppendLeftOne_transition_move (i : Fin 2) (s : Unit) (b : Bool) :
    (selfLoopAppendLeftOne.transition i s b).2.2.2 ≠ Move.right := by
  unfold selfLoopAppendLeftOne
  dsimp only
  split_ifs <;> simp

/-! ### Single-step lemmas -/

/-- Scan step (phase `0`, bit `1`): the phase stays `0` (the leftward self-loop). -/
theorem selfLoopAppendLeftOne_stepConfig_scan_phase {L : Nat}
    (c : Configuration (M := selfLoopAppendLeftOne.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := selfLoopAppendLeftOne.toPhased.toTM) c).state).fst.val = 0 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopAppendLeftOne, hi, hbit]

/-- Scan step (phase `0`, bit `1`): the head moves left. -/
theorem selfLoopAppendLeftOne_stepConfig_scan_head {L : Nat}
    (c : Configuration (M := selfLoopAppendLeftOne.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := selfLoopAppendLeftOne.toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.left := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopAppendLeftOne, hi, hbit]

/-- Scan step (phase `0`, bit `1`): the tape is unchanged (the `1` is written back). -/
theorem selfLoopAppendLeftOne_stepConfig_scan_tape {L : Nat}
    (c : Configuration (M := selfLoopAppendLeftOne.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := selfLoopAppendLeftOne.toPhased.toTM) c).tape = c.tape := by
  have hwrite : (TM.stepConfig (M := selfLoopAppendLeftOne.toPhased.toTM) c).tape
      = c.write c.head true := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, selfLoopAppendLeftOne, hi, hbit]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write, hbit]
  · simp [Configuration.write, hj]

/-- Append step (phase `0`, bit `0`): the phase becomes the done phase `1`. -/
theorem selfLoopAppendLeftOne_stepConfig_stop_phase {L : Nat}
    (c : Configuration (M := selfLoopAppendLeftOne.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := selfLoopAppendLeftOne.toPhased.toTM) c).state).fst.val = 1 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopAppendLeftOne, hi, hbit]

/-- Append step (phase `0`, bit `0`): the head stays put. -/
theorem selfLoopAppendLeftOne_stepConfig_stop_head {L : Nat}
    (c : Configuration (M := selfLoopAppendLeftOne.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := selfLoopAppendLeftOne.toPhased.toTM) c).head = c.head := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopAppendLeftOne, hi, hbit, Configuration.moveHead]

/-- Append step (phase `0`, bit `0`): the terminating `0` is overwritten with `1` (the append). -/
theorem selfLoopAppendLeftOne_stepConfig_stop_tape {L : Nat}
    (c : Configuration (M := selfLoopAppendLeftOne.toPhased.toTM) L)
    {i : Fin 2} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := selfLoopAppendLeftOne.toPhased.toTM) c).tape = c.write c.head true := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, selfLoopAppendLeftOne, hi, hbit]

/-- Leftward scan invariant (over `U`'s `1`-block): from `c0` in phase `0`, if the `j` cells
`(c0.head − j, c0.head]` are all `1`, then after `j ≤ c0.head` steps the phase is still `0`, the head
has retreated to `c0.head − j`, and the tape is unchanged.  Identical to `selfLoopScanLeftOne`'s
scanning (the append only differs at the terminating `0`). -/
theorem selfLoopAppendLeftOne_runConfig_scan {L : Nat}
    (c0 : Configuration (M := selfLoopAppendLeftOne.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) :
    ∀ j : Nat, j ≤ (c0.head : Nat) →
      (∀ p : Fin (selfLoopAppendLeftOne.toPhased.toTM.tapeLength L),
        (c0.head : Nat) - j < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) → c0.tape p = true) →
      (((TM.runConfig (M := selfLoopAppendLeftOne.toPhased.toTM) c0 j).state).fst : Nat) = 0
      ∧ ((TM.runConfig (M := selfLoopAppendLeftOne.toPhased.toTM) c0 j).head : Nat)
          = (c0.head : Nat) - j
      ∧ (TM.runConfig (M := selfLoopAppendLeftOne.toPhased.toTM) c0 j).tape = c0.tape := by
  intro j
  induction j with
  | zero => intro _ _; exact ⟨hphase, by simp, rfl⟩
  | succ j ih =>
      intro hj h1
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp1 hp2 => h1 p (by omega) hp2)
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := selfLoopAppendLeftOne.toPhased.toTM) c0 j with hc
      have hbit : c.tape c.head = true := by
        rw [htp]; exact h1 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      have hheadne : ¬ (c.head : Nat) = 0 := by rw [hhd]; omega
      refine ⟨?_, ?_, ?_⟩
      · exact selfLoopAppendLeftOne_stepConfig_scan_phase c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit
      · rw [selfLoopAppendLeftOne_stepConfig_scan_head c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
        simp only [Configuration.moveHead, dif_neg hheadne]
        rw [hhd]; omega
      · rw [selfLoopAppendLeftOne_stepConfig_scan_tape c
          (i := c.state.fst) (s := c.state.snd) hph rfl hbit, htp]

/-- Leftward append: from `c0` in phase `0`, if the cells `(k, c0.head]` are all `1` and cell `k` is
`0` (`k < c0.head`), then after `(c0.head − k) + 1` steps the head rests on `k` at the done phase `1`,
with cell `k` now set to `1` (the unary block extended by one on its left end), everything else
unchanged.  Combines the leftward scan to the marker with one append step. -/
theorem selfLoopAppendLeftOne_runConfig_append {L : Nat}
    (c0 : Configuration (M := selfLoopAppendLeftOne.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) (k : Nat) (hk : k < (c0.head : Nat))
    (hones : ∀ p : Fin (selfLoopAppendLeftOne.toPhased.toTM.tapeLength L),
      k < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) → c0.tape p = true)
    (hterm : ∀ p : Fin (selfLoopAppendLeftOne.toPhased.toTM.tapeLength L),
      (p : Nat) = k → c0.tape p = false) :
    (((TM.runConfig (M := selfLoopAppendLeftOne.toPhased.toTM) c0 (((c0.head : Nat) - k) + 1)).state).fst
        : Nat) = 1
      ∧ ((TM.runConfig (M := selfLoopAppendLeftOne.toPhased.toTM) c0 (((c0.head : Nat) - k) + 1)).head
          : Nat) = k
      ∧ ∀ p : Fin (selfLoopAppendLeftOne.toPhased.toTM.tapeLength L),
          (TM.runConfig (M := selfLoopAppendLeftOne.toPhased.toTM) c0 (((c0.head : Nat) - k) + 1)).tape p
            = (if (p : Nat) = k then true else c0.tape p) := by
  obtain ⟨hph, hhd, htp⟩ :=
    selfLoopAppendLeftOne_runConfig_scan c0 hphase ((c0.head : Nat) - k) (by omega)
      (fun p hp1 hp2 => hones p (by omega) hp2)
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := selfLoopAppendLeftOne.toPhased.toTM) c0 ((c0.head : Nat) - k) with hc
  have hhdk : (c.head : Nat) = k := by rw [hhd]; omega
  have hhead_eq : c.head = ⟨k, by rw [← hhdk]; exact c.head.isLt⟩ := Fin.ext hhdk
  have hbit : c.tape c.head = false := by rw [htp]; exact hterm c.head hhdk
  refine ⟨?_, ?_, ?_⟩
  · exact selfLoopAppendLeftOne_stepConfig_stop_phase c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit
  · rw [selfLoopAppendLeftOne_stepConfig_stop_head c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
    exact hhdk
  · rw [selfLoopAppendLeftOne_stepConfig_stop_tape c
      (i := c.state.fst) (s := c.state.snd) hph rfl hbit]
    intro p
    by_cases hp : p = c.head
    · subst hp
      rw [Configuration.write_self, if_pos hhdk]
    · rw [Configuration.write_other c hp true, congrFun htp p]
      have hpc : (p : Nat) ≠ k := fun h => hp (by rw [hhead_eq]; exact Fin.ext h)
      rw [if_neg hpc]

end ContractExpansion
end Frontier
end Pnp4
