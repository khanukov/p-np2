import Pnp4.Frontier.ContractExpansion.TreeMCSPDriverCorridor

/-!
# `zoneWalkRight` — D2t-5b (Block A4w): traversing a corridor stack zone left-to-right

The **return** legs of the driver's routes (frontier → marker) cross the stack zones rightward.  A
zone reads `[sentinel 1] [0 1^{k₁}] … [0 1^{kⱼ}]` left-to-right, and past its content lie **at least
two** dead `0`s (the strict corridor gaps) — so the rightward walker distinguishes a block boundary
from the zone exit with one extra peek: after a `0`, a `1` opens the next block, a second `0` is the
exit.

Phases (entry: head **on the base sentinel**, or any block's last `1`):

* **φ0** — step right off the sentinel (→ φ1);
* **φ1** — confirm the `0` after it (always a `0` under the invariant; a `1` routes to the explicit
  fail phase φ5, keeping the semantics honest), move right (→ φ2);
* **φ2** — decide: a `1` is the next block's first unit (→ φ3, walk it); a `0` is the second dead
  cell — the zone exit (→ φ4, **done**, head resting on it);
* **φ3** — walk the block's `1`s rightward; on the `0` past them, move right and re-decide (→ φ2);
* **φ4** — done; **φ5** — fail (unreachable under the corridor invariant).

Step budget: `2` (entry) `+ Σ (kᵢ + 2)` (per block) `+ 1` (exit decide) — the run lemmas land in the
follow-up module; this brick ships the program and its single-step semantics.

**Progress classification (AGENTS.md): Infrastructure** — a verifier machine component; builds no
verifier and proves no separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.
**No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- **The rightward zone walker** (6 phases).  φ0 step off the sentinel; φ1 confirm the `0` (→ right);
φ2 decide (`1` = block → φ3 | `0` = exit → φ4 done); φ3 walk the block's ones (on the `0` past them,
right and → φ2); φ4 done; φ5 fail (unreachable under the invariant). -/
def zoneWalkRight : ConstStatePhasedProgram Unit where
  numPhases := 6
  startPhase := ⟨0, by decide⟩
  startState := ()
  acceptPhase := ⟨4, by decide⟩
  acceptState := ()
  transition := fun i _ b =>
    if i.val = 0 then
      -- on the base sentinel (a 1): step right
      (⟨1, by decide⟩, (), b, Move.right)
    else if i.val = 1 then
      -- the cell after the sentinel: always a 0 under the invariant; confirm and move right
      if b then (⟨5, by decide⟩, (), b, Move.stay)
      else (⟨2, by decide⟩, (), b, Move.right)
    else if i.val = 2 then
      -- decide: 1 = the next block's first unit; 0 = the second dead cell (zone exit)
      if b then (⟨3, by decide⟩, (), b, Move.stay)
      else (⟨4, by decide⟩, (), b, Move.stay)
    else if i.val = 3 then
      -- walk the block's ones rightward; on the 0 past them, step right and re-decide
      if b then (⟨3, by decide⟩, (), b, Move.right)
      else (⟨2, by decide⟩, (), b, Move.right)
    else if i.val = 4 then
      -- done — idle
      (⟨4, by decide⟩, (), b, Move.stay)
    else
      -- φ5: fail — idle
      (⟨5, by decide⟩, (), b, Move.stay)
  timeBound := fun n => n

@[simp] theorem zoneWalkRight_numPhases : zoneWalkRight.numPhases = 6 := rfl

@[simp] theorem zoneWalkRight_startPhase : (zoneWalkRight.startPhase : Nat) = 0 := rfl

@[simp] theorem zoneWalkRight_acceptPhase : (zoneWalkRight.acceptPhase : Nat) = 4 := rfl

/-! ### Transition lemmas -/

theorem zoneWalkRight_t0 (b : Bool) :
    zoneWalkRight.transition ⟨0, by decide⟩ () b = (⟨1, by decide⟩, (), b, Move.right) := rfl

theorem zoneWalkRight_t1_one :
    zoneWalkRight.transition ⟨1, by decide⟩ () true = (⟨5, by decide⟩, (), true, Move.stay) := rfl

theorem zoneWalkRight_t1_zero :
    zoneWalkRight.transition ⟨1, by decide⟩ () false = (⟨2, by decide⟩, (), false, Move.right) := rfl

theorem zoneWalkRight_t2_one :
    zoneWalkRight.transition ⟨2, by decide⟩ () true = (⟨3, by decide⟩, (), true, Move.stay) := rfl

theorem zoneWalkRight_t2_zero :
    zoneWalkRight.transition ⟨2, by decide⟩ () false = (⟨4, by decide⟩, (), false, Move.stay) := rfl

theorem zoneWalkRight_t3_one :
    zoneWalkRight.transition ⟨3, by decide⟩ () true = (⟨3, by decide⟩, (), true, Move.right) := rfl

theorem zoneWalkRight_t3_zero :
    zoneWalkRight.transition ⟨3, by decide⟩ () false = (⟨2, by decide⟩, (), false, Move.right) := rfl

theorem zoneWalkRight_t4 (b : Bool) :
    zoneWalkRight.transition ⟨4, by decide⟩ () b = (⟨4, by decide⟩, (), b, Move.stay) := rfl

theorem zoneWalkRight_t5 (b : Bool) :
    zoneWalkRight.transition ⟨5, by decide⟩ () b = (⟨5, by decide⟩, (), b, Move.stay) := rfl

/-! ### `stepConfig` lemmas -/

/-- φ0: phase to `1`, head right, tape unchanged. -/
theorem zoneWalkRight_stepConfig_p0_phase {L : Nat}
    (c : Configuration (M := zoneWalkRight.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := zoneWalkRight.toPhased.toTM) c).state).fst.val = 1 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkRight, hi]

theorem zoneWalkRight_stepConfig_p0_head {L : Nat}
    (c : Configuration (M := zoneWalkRight.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := zoneWalkRight.toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.right := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkRight, hi]

theorem zoneWalkRight_stepConfig_p0_tape {L : Nat}
    (c : Configuration (M := zoneWalkRight.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := zoneWalkRight.toPhased.toTM) c).tape = c.tape := by
  have hwrite : (TM.stepConfig (M := zoneWalkRight.toPhased.toTM) c).tape
      = c.write c.head (c.tape c.head) := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, zoneWalkRight, hi]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-- φ1 on a `0`: confirm — phase to `2`, head right, tape unchanged. -/
theorem zoneWalkRight_stepConfig_p1_zero_phase {L : Nat}
    (c : Configuration (M := zoneWalkRight.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := zoneWalkRight.toPhased.toTM) c).state).fst.val = 2 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkRight, hi, hbit]

theorem zoneWalkRight_stepConfig_p1_zero_head {L : Nat}
    (c : Configuration (M := zoneWalkRight.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := zoneWalkRight.toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.right := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkRight, hi, hbit]

theorem zoneWalkRight_stepConfig_p1_zero_tape {L : Nat}
    (c : Configuration (M := zoneWalkRight.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := zoneWalkRight.toPhased.toTM) c).tape = c.tape := by
  have hwrite : (TM.stepConfig (M := zoneWalkRight.toPhased.toTM) c).tape
      = c.write c.head false := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, zoneWalkRight, hi, hbit]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write, hbit]
  · simp [Configuration.write, hj]

/-- φ2 on a `1`: a block follows — phase to `3`, head stays, tape unchanged. -/
theorem zoneWalkRight_stepConfig_p2_one_phase {L : Nat}
    (c : Configuration (M := zoneWalkRight.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 2) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := zoneWalkRight.toPhased.toTM) c).state).fst.val = 3 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkRight, hi, hbit]

theorem zoneWalkRight_stepConfig_p2_one_head {L : Nat}
    (c : Configuration (M := zoneWalkRight.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 2) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := zoneWalkRight.toPhased.toTM) c).head = c.head := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkRight, hi, hbit, Configuration.moveHead]

/-- φ2 on a `0`: the zone exit — phase to the done phase `4`, head stays, tape unchanged. -/
theorem zoneWalkRight_stepConfig_p2_zero_phase {L : Nat}
    (c : Configuration (M := zoneWalkRight.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 2) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := zoneWalkRight.toPhased.toTM) c).state).fst.val = 4 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkRight, hi, hbit]

theorem zoneWalkRight_stepConfig_p2_zero_head {L : Nat}
    (c : Configuration (M := zoneWalkRight.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 2) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := zoneWalkRight.toPhased.toTM) c).head = c.head := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkRight, hi, hbit, Configuration.moveHead]

/-- φ2, either bit: the tape is unchanged. -/
theorem zoneWalkRight_stepConfig_p2_tape {L : Nat}
    (c : Configuration (M := zoneWalkRight.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 2) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := zoneWalkRight.toPhased.toTM) c).tape = c.tape := by
  have hwrite : (TM.stepConfig (M := zoneWalkRight.toPhased.toTM) c).tape
      = c.write c.head (c.tape c.head) := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, zoneWalkRight, hi]
    cases c.tape c.head <;> simp
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-- φ3 on a `1`: walk — phase stays `3`, head right, tape unchanged. -/
theorem zoneWalkRight_stepConfig_p3_one_phase {L : Nat}
    (c : Configuration (M := zoneWalkRight.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 3) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := zoneWalkRight.toPhased.toTM) c).state).fst.val = 3 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkRight, hi, hbit]

theorem zoneWalkRight_stepConfig_p3_one_head {L : Nat}
    (c : Configuration (M := zoneWalkRight.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 3) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := zoneWalkRight.toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.right := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkRight, hi, hbit]

theorem zoneWalkRight_stepConfig_p3_one_tape {L : Nat}
    (c : Configuration (M := zoneWalkRight.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 3) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := zoneWalkRight.toPhased.toTM) c).tape = c.tape := by
  have hwrite : (TM.stepConfig (M := zoneWalkRight.toPhased.toTM) c).tape
      = c.write c.head true := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, zoneWalkRight, hi, hbit]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write, hbit]
  · simp [Configuration.write, hj]

/-- φ3 on a `0` (past the block): phase to `2`, head right, tape unchanged. -/
theorem zoneWalkRight_stepConfig_p3_zero_phase {L : Nat}
    (c : Configuration (M := zoneWalkRight.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 3) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := zoneWalkRight.toPhased.toTM) c).state).fst.val = 2 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkRight, hi, hbit]

theorem zoneWalkRight_stepConfig_p3_zero_head {L : Nat}
    (c : Configuration (M := zoneWalkRight.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 3) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := zoneWalkRight.toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.right := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkRight, hi, hbit]

theorem zoneWalkRight_stepConfig_p3_zero_tape {L : Nat}
    (c : Configuration (M := zoneWalkRight.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 3) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := zoneWalkRight.toPhased.toTM) c).tape = c.tape := by
  have hwrite : (TM.stepConfig (M := zoneWalkRight.toPhased.toTM) c).tape
      = c.write c.head false := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, zoneWalkRight, hi, hbit]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write, hbit]
  · simp [Configuration.write, hj]

end ContractExpansion
end Frontier
end Pnp4
