import Pnp4.Frontier.ContractExpansion.TreeMCSPScanLeftProgram

/-!
# `bitProbe` — D2t-5b (Block A5m-6a): the in-place bit prober

The leaf arms branch on a certificate bit that the tag trie does **not** consume: after
`certTrie`'s const hop the head rests **on** the leaf's value bit `b`, and the const chains for
`b = 0` / `b = 1` differ (the emitted record is `[1,0,b]`).  The input arm likewise peeks the
first index bit.  `bitProbe` is the three-phase in-place prober: `φ0` reads the scanned cell and
moves to the outcome phase — `φ1` on `0`, `φ2` on `1` — head and tape untouched; the outcome
phases idle, so a region union exits them via redirects on both slots.

`settleProbe` is the step-left-then-peek variant of the same shape; this one probes **in place**.

**Progress classification (AGENTS.md): Infrastructure** — a staging-machine primitive and its
single-step run facts; builds no verifier and proves no separation.  Standard
`[propext, Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- **The in-place bit prober** (3 phases): `φ0` reads the scanned cell and decides — `0` lands in
the outcome phase `φ1`, `1` lands in `φ2` — head and tape untouched; the outcome phases idle. -/
def bitProbe : ConstStatePhasedProgram Unit where
  numPhases := 3
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨2, by omega⟩
  acceptState := ()
  transition := fun i _ b =>
    if i.val = 0 then
      if b then (⟨2, by omega⟩, (), b, Move.stay)
      else (⟨1, by omega⟩, (), b, Move.stay)
    else (⟨i.val, i.isLt⟩, (), b, Move.stay)
  timeBound := fun _ => 1

/-- φ0 on a `0`: the **zero** verdict — phase `1`, head stays. -/
theorem bitProbe_stepConfig_p0_zero_phase {L : Nat}
    (c : Configuration (M := bitProbe.toPhased.toTM) L)
    {i : Fin 3} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := bitProbe.toPhased.toTM) c).state).fst.val = 1 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, bitProbe, hi, hbit]

/-- φ0 on a `1`: the **one** verdict — phase `2`, head stays. -/
theorem bitProbe_stepConfig_p0_one_phase {L : Nat}
    (c : Configuration (M := bitProbe.toPhased.toTM) L)
    {i : Fin 3} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := bitProbe.toPhased.toTM) c).state).fst.val = 2 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, bitProbe, hi, hbit]

/-- φ0: the head stays. -/
theorem bitProbe_stepConfig_p0_head {L : Nat}
    (c : Configuration (M := bitProbe.toPhased.toTM) L)
    {i : Fin 3} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := bitProbe.toPhased.toTM) c).head = c.head := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  by_cases hbit : c.tape c.head
  · simp [ConstStatePhasedProgram.toPhased, bitProbe, hi, hbit, Configuration.moveHead]
  · simp only [Bool.not_eq_true] at hbit
    simp [ConstStatePhasedProgram.toPhased, bitProbe, hi, hbit, Configuration.moveHead]

/-- φ0: the tape is unchanged (the scanned bit is written back). -/
theorem bitProbe_stepConfig_p0_tape {L : Nat}
    (c : Configuration (M := bitProbe.toPhased.toTM) L)
    {i : Fin 3} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := bitProbe.toPhased.toTM) c).tape = c.tape := by
  have hwrite : (TM.stepConfig (M := bitProbe.toPhased.toTM) c).tape
      = c.write c.head (c.tape c.head) := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    by_cases hbit : c.tape c.head
    · simp [ConstStatePhasedProgram.toPhased, bitProbe, hi, hbit]
    · simp only [Bool.not_eq_true] at hbit
      simp [ConstStatePhasedProgram.toPhased, bitProbe, hi, hbit]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-- **The zero probe, discharged**: from `φ0` on a `0` cell, one step lands in the outcome phase
`φ1`, head and tape untouched. -/
theorem bitProbe_runConfig_zero {L : Nat}
    (c : Configuration (M := bitProbe.toPhased.toTM) L)
    (hphase : (c.state.fst : Nat) = 0)
    (hbit : c.tape c.head = false) :
    (((TM.runConfig (M := bitProbe.toPhased.toTM) c 1).state).fst : Nat) = 1
      ∧ (TM.runConfig (M := bitProbe.toPhased.toTM) c 1).head = c.head
      ∧ (TM.runConfig (M := bitProbe.toPhased.toTM) c 1).tape = c.tape := by
  have hstate : c.state = ⟨c.state.fst, c.state.snd⟩ := rfl
  rw [show (1 : Nat) = 0 + 1 from rfl, TM.runConfig_succ, TM.runConfig_zero]
  exact ⟨bitProbe_stepConfig_p0_zero_phase c (by omega) hstate hbit,
    bitProbe_stepConfig_p0_head c (by omega) hstate,
    bitProbe_stepConfig_p0_tape c (by omega) hstate⟩

/-- **The one probe, discharged**: from `φ0` on a `1` cell, one step lands in the outcome phase
`φ2`, head and tape untouched. -/
theorem bitProbe_runConfig_one {L : Nat}
    (c : Configuration (M := bitProbe.toPhased.toTM) L)
    (hphase : (c.state.fst : Nat) = 0)
    (hbit : c.tape c.head = true) :
    (((TM.runConfig (M := bitProbe.toPhased.toTM) c 1).state).fst : Nat) = 2
      ∧ (TM.runConfig (M := bitProbe.toPhased.toTM) c 1).head = c.head
      ∧ (TM.runConfig (M := bitProbe.toPhased.toTM) c 1).tape = c.tape := by
  have hstate : c.state = ⟨c.state.fst, c.state.snd⟩ := rfl
  rw [show (1 : Nat) = 0 + 1 from rfl, TM.runConfig_succ, TM.runConfig_zero]
  exact ⟨bitProbe_stepConfig_p0_one_phase c (by omega) hstate hbit,
    bitProbe_stepConfig_p0_head c (by omega) hstate,
    bitProbe_stepConfig_p0_tape c (by omega) hstate⟩

end ContractExpansion
end Frontier
end Pnp4
