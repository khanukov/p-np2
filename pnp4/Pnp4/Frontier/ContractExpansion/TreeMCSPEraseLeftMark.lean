import Pnp4.Frontier.ContractExpansion.TreeMCSPDriverCorridor

/-!
# `eraseLeftMark` — D2t-5b (Block A4a): plant the new cursor marker, erase the consumed token

After a token's cells have been read (the head resting on its **last** cell), the reading arm must
**advance the cursor**: the last consumed cell becomes the **new marker** `M` (write `1`), and the
`w` cells to its left — the token's remaining cells and the **old** marker — are erased to `0`,
re-establishing the all-`0` corridor between the control zone and the new marker.  `eraseLeftMark w`
is that fixed-width writer (the width `w` is per-arm: `3` for a node token — two leading tag cells
plus the old marker — `4` for a `const` leaf, `3 + width` for an `input` leaf), ending `w` cells left
of the marker, exactly where the leftward corridor scan of the next leg starts.

Phases: φ0 — write `1` (the new marker), step left; φ1 … φw — write `0`, step left; φ(w+1) — accept
(the head rests on the cell `w + 1` left of the marker).

**Progress classification (AGENTS.md): Infrastructure** — a verifier machine component; builds no
verifier and proves no separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.
**No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- **Plant-and-erase**: write `1` at the head (the new marker), then erase `w` cells leftward,
ending a further cell left.  `w + 2` phases: φ0 the marker write, φ1…φw the erasures, φ(w+1) accept. -/
def eraseLeftMark (w : Nat) : ConstStatePhasedProgram Unit where
  numPhases := w + 2
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨w + 1, by omega⟩
  acceptState := ()
  transition := fun i _ _ =>
    if h : i.val = 0 then
      (⟨1, by omega⟩, (), true, Move.left)
    else if h2 : i.val ≤ w then
      (⟨i.val + 1, by omega⟩, (), false, Move.left)
    else
      (⟨w + 1, by omega⟩, (), false, Move.stay)
  timeBound := fun n => n

@[simp] theorem eraseLeftMark_numPhases (w : Nat) : (eraseLeftMark w).numPhases = w + 2 := rfl

@[simp] theorem eraseLeftMark_startPhase (w : Nat) : ((eraseLeftMark w).startPhase : Nat) = 0 := rfl

@[simp] theorem eraseLeftMark_acceptPhase (w : Nat) :
    ((eraseLeftMark w).acceptPhase : Nat) = w + 1 := rfl

/-- φ0 marker-write step: phase to `1`. -/
theorem eraseLeftMark_stepConfig_p0_phase {w L : Nat}
    (c : Configuration (M := (eraseLeftMark w).toPhased.toTM) L)
    {i : Fin (w + 2)} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (eraseLeftMark w).toPhased.toTM) c).state).fst.val = 1 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, eraseLeftMark, hi]

theorem eraseLeftMark_stepConfig_p0_head {w L : Nat}
    (c : Configuration (M := (eraseLeftMark w).toPhased.toTM) L)
    {i : Fin (w + 2)} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (eraseLeftMark w).toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.left := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, eraseLeftMark, hi]

theorem eraseLeftMark_stepConfig_p0_tape {w L : Nat}
    (c : Configuration (M := (eraseLeftMark w).toPhased.toTM) L)
    {i : Fin (w + 2)} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (eraseLeftMark w).toPhased.toTM) c).tape
      = c.write c.head true := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, eraseLeftMark, hi]

/-- Erasure step (`1 ≤ i ≤ w`): phase advances, head left, the cell is zeroed. -/
theorem eraseLeftMark_stepConfig_erase_phase {w L : Nat}
    (c : Configuration (M := (eraseLeftMark w).toPhased.toTM) L)
    {i : Fin (w + 2)} {s : Unit} (hi1 : 1 ≤ i.val) (hi2 : i.val ≤ w) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := (eraseLeftMark w).toPhased.toTM) c).state).fst.val = i.val + 1 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, eraseLeftMark, Nat.ne_of_gt hi1, hi2]

theorem eraseLeftMark_stepConfig_erase_head {w L : Nat}
    (c : Configuration (M := (eraseLeftMark w).toPhased.toTM) L)
    {i : Fin (w + 2)} {s : Unit} (hi1 : 1 ≤ i.val) (hi2 : i.val ≤ w) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (eraseLeftMark w).toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.left := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, eraseLeftMark, Nat.ne_of_gt hi1, hi2]

theorem eraseLeftMark_stepConfig_erase_tape {w L : Nat}
    (c : Configuration (M := (eraseLeftMark w).toPhased.toTM) L)
    {i : Fin (w + 2)} {s : Unit} (hi1 : 1 ≤ i.val) (hi2 : i.val ≤ w) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (eraseLeftMark w).toPhased.toTM) c).tape
      = c.write c.head false := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, eraseLeftMark, Nat.ne_of_gt hi1, hi2]

/-- **The plant-and-erase run.**  From φ0 at head `p` with `w + 1 ≤ p`, after `w + 1` steps: the
machine accepts at `p − (w + 1)`; the cell `p` holds `1` (the new marker), the cells
`[p − w, p)` hold `0` (the erased token/marker), and every other cell is untouched. -/
theorem eraseLeftMark_runConfig {w L : Nat}
    (c0 : Configuration (M := (eraseLeftMark w).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) (hh : w + 1 ≤ (c0.head : Nat)) :
    (((TM.runConfig (M := (eraseLeftMark w).toPhased.toTM) c0 (w + 1)).state).fst : Nat) = w + 1
    ∧ ((TM.runConfig (M := (eraseLeftMark w).toPhased.toTM) c0 (w + 1)).head : Nat)
        = (c0.head : Nat) - (w + 1)
    ∧ ∀ q : Fin ((eraseLeftMark w).toPhased.toTM.tapeLength L),
        (TM.runConfig (M := (eraseLeftMark w).toPhased.toTM) c0 (w + 1)).tape q
          = if (q : Nat) = (c0.head : Nat) then true
            else if (c0.head : Nat) - w ≤ (q : Nat) ∧ (q : Nat) < (c0.head : Nat) then false
            else c0.tape q := by
  -- Invariant after 1 + j steps (j ≤ w): phase 1 + j, head = p − (1 + j), marker planted, j cells erased.
  suffices H : ∀ j : Nat, j ≤ w →
      (((TM.runConfig (M := (eraseLeftMark w).toPhased.toTM) c0 (1 + j)).state).fst : Nat) = 1 + j
      ∧ ((TM.runConfig (M := (eraseLeftMark w).toPhased.toTM) c0 (1 + j)).head : Nat)
          = (c0.head : Nat) - (1 + j)
      ∧ ∀ q : Fin ((eraseLeftMark w).toPhased.toTM.tapeLength L),
          (TM.runConfig (M := (eraseLeftMark w).toPhased.toTM) c0 (1 + j)).tape q
            = if (q : Nat) = (c0.head : Nat) then true
              else if (c0.head : Nat) - j ≤ (q : Nat) ∧ (q : Nat) < (c0.head : Nat) then false
              else c0.tape q by
    have := H w (le_refl w)
    rwa [show 1 + w = w + 1 from by omega] at this
  intro j
  induction j with
  | zero =>
      intro _
      rw [TM.runConfig_one]
      have hst0 : c0.state = ⟨c0.state.fst, c0.state.snd⟩ := rfl
      refine ⟨?_, ?_, ?_⟩
      · exact eraseLeftMark_stepConfig_p0_phase c0 hphase hst0
      · rw [eraseLeftMark_stepConfig_p0_head c0 hphase hst0]
        simp only [Configuration.moveHead, dif_neg (by omega : ¬ (c0.head : Nat) = 0)]
      · intro q
        rw [eraseLeftMark_stepConfig_p0_tape c0 hphase hst0]
        by_cases hq : q = c0.head
        · subst hq; simp [Configuration.write]
        · have hqn : (q : Nat) ≠ (c0.head : Nat) := fun h => hq (Fin.ext h)
          simp only [Configuration.write, dif_neg hq]
          rw [if_neg hqn,
            if_neg (by omega : ¬((c0.head : Nat) - 0 ≤ (q : Nat) ∧ (q : Nat) < (c0.head : Nat)))]
  | succ j ih =>
      intro hj
      obtain ⟨hph, hhd, htp⟩ := ih (by omega)
      rw [show 1 + (j + 1) = (1 + j) + 1 from by omega, TM.runConfig_succ]
      set c := TM.runConfig (M := (eraseLeftMark w).toPhased.toTM) c0 (1 + j) with hc
      have hst : c.state = ⟨c.state.fst, c.state.snd⟩ := rfl
      have hi1 : 1 ≤ (c.state.fst : Nat) := by omega
      have hi2 : (c.state.fst : Nat) ≤ w := by omega
      refine ⟨?_, ?_, ?_⟩
      · rw [eraseLeftMark_stepConfig_erase_phase c hi1 hi2 hst, hph]
      · rw [eraseLeftMark_stepConfig_erase_head c hi1 hi2 hst]
        simp only [Configuration.moveHead, dif_neg (by rw [hhd]; omega : ¬ (c.head : Nat) = 0)]
        rw [hhd]
        omega
      · intro q
        rw [eraseLeftMark_stepConfig_erase_tape c hi1 hi2 hst]
        by_cases hq : q = c.head
        · subst hq
          have hqv : (c.head : Nat) = (c0.head : Nat) - (1 + j) := hhd
          rw [if_neg (show ¬((c.head : Nat) = (c0.head : Nat)) by omega),
            if_pos (show (c0.head : Nat) - (j + 1) ≤ (c.head : Nat)
              ∧ (c.head : Nat) < (c0.head : Nat) by omega)]
          simp [Configuration.write]
        · have hqn : (q : Nat) ≠ (c.head : Nat) := fun h => hq (Fin.ext h)
          simp only [Configuration.write, dif_neg hq]
          rw [htp q]
          have hqv : (c.head : Nat) = (c0.head : Nat) - (1 + j) := hhd
          by_cases h1 : (q : Nat) = (c0.head : Nat)
          · rw [if_pos h1, if_pos h1]
          · rw [if_neg h1, if_neg h1]
            by_cases h2 : (c0.head : Nat) - j ≤ (q : Nat) ∧ (q : Nat) < (c0.head : Nat)
            · rw [if_pos h2, if_pos (by omega)]
            · rw [if_neg h2, if_neg (by omega)]

end ContractExpansion
end Frontier
end Pnp4
