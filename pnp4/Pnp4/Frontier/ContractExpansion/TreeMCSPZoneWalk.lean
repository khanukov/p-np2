import Pnp4.Frontier.ContractExpansion.TreeMCSPDriverCorridor

/-!
# `zoneWalkLeft` — D2t-5b (Block A4w): traversing a corridor stack zone right-to-left

The corridor layout (A3) stores both stacks as `[sentinel 1] [0 1^{k₁}] [0 1^{k₂}] …` (left→right;
the **top is rightmost**) with every field block carrying **≥ 2** ones and the base sentinel exactly
**1** — so a zone can be *walked* right-to-left without any markers: from a block's rightmost `1`, step
left and peek — another `1` means the block is a field (≥ 2 ones; walk its remaining ones and cross its
`0` delimiter to the next block), a `0` means the block was the single-`1` **base sentinel** (we have
stepped onto the dead-zone `0` just left of it): stop.  `zoneWalkLeft` is that walker; the driver's
cross-zone routes (cursor → control top → value top → WORK frontier and back) chain it with the
0-corridor scans.

Phases (started on a block's rightmost `1`, the **loop-head invariant**):

* **φ0** — step left to peek the cell left of the block's rightmost `1`;
* **φ1** — decide: a `1` is a field block (→ φ2, walk it); a `0` is the dead-zone left of the base
  sentinel (→ φ4, **done**);
* **φ2** — walk the field's remaining ones (self-loop left, stop on the delimiter `0`);
* **φ3** — step left off the delimiter onto the next block's rightmost `1` (→ φ0, the loop head);
* **φ4** — done: the head rests on the `0` immediately **left of the sentinel**, exactly where the
  caller's next leftward 0-corridor scan begins.

(The single-`1` sentinel is handled uniformly: φ0 steps left off it onto the dead `0`, and φ1 reads
that `0` and stops — no special case.)

**Progress classification (AGENTS.md): Infrastructure** — a verifier machine component; builds no
verifier and proves no separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.
**No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- **The leftward zone walker** (5 phases).  φ0 step-left-to-peek; φ1 decide (field → φ2 | sentinel
dead-zone → φ4 done); φ2 walk the field's ones; φ3 cross the delimiter (→ φ0); φ4 done. -/
def zoneWalkLeft : ConstStatePhasedProgram Unit where
  numPhases := 5
  startPhase := ⟨0, by decide⟩
  startState := ()
  acceptPhase := ⟨4, by decide⟩
  acceptState := ()
  transition := fun i _ b =>
    if i.val = 0 then
      -- on a block's rightmost 1: step left to peek the cell to its left
      (⟨1, by decide⟩, (), b, Move.left)
    else if i.val = 1 then
      -- decide: 1 = a ≥2 field block (walk it); 0 = the dead 0 left of the single-1 sentinel (done)
      if b then (⟨2, by decide⟩, (), b, Move.stay)
      else (⟨4, by decide⟩, (), b, Move.stay)
    else if i.val = 2 then
      -- walk the field's remaining ones leftward; the 0 is the field's left delimiter
      if b then (⟨2, by decide⟩, (), b, Move.left)
      else (⟨3, by decide⟩, (), b, Move.stay)
    else if i.val = 3 then
      -- step left off the delimiter onto the next block's rightmost 1 (back to the loop head)
      (⟨0, by decide⟩, (), b, Move.left)
    else
      -- φ4: done — idle
      (⟨4, by decide⟩, (), b, Move.stay)
  timeBound := fun n => n

@[simp] theorem zoneWalkLeft_numPhases : zoneWalkLeft.numPhases = 5 := rfl

@[simp] theorem zoneWalkLeft_startPhase : (zoneWalkLeft.startPhase : Nat) = 0 := rfl

@[simp] theorem zoneWalkLeft_acceptPhase : (zoneWalkLeft.acceptPhase : Nat) = 4 := rfl

/-! ### Transition lemmas -/

theorem zoneWalkLeft_t0 (b : Bool) :
    zoneWalkLeft.transition ⟨0, by decide⟩ () b = (⟨1, by decide⟩, (), b, Move.left) := rfl

theorem zoneWalkLeft_t1_one :
    zoneWalkLeft.transition ⟨1, by decide⟩ () true = (⟨2, by decide⟩, (), true, Move.stay) := rfl

theorem zoneWalkLeft_t1_zero :
    zoneWalkLeft.transition ⟨1, by decide⟩ () false = (⟨4, by decide⟩, (), false, Move.stay) := rfl

theorem zoneWalkLeft_t2_one :
    zoneWalkLeft.transition ⟨2, by decide⟩ () true = (⟨2, by decide⟩, (), true, Move.left) := rfl

theorem zoneWalkLeft_t2_zero :
    zoneWalkLeft.transition ⟨2, by decide⟩ () false = (⟨3, by decide⟩, (), false, Move.stay) := rfl

theorem zoneWalkLeft_t3 (b : Bool) :
    zoneWalkLeft.transition ⟨3, by decide⟩ () b = (⟨0, by decide⟩, (), b, Move.left) := rfl

theorem zoneWalkLeft_t4 (b : Bool) :
    zoneWalkLeft.transition ⟨4, by decide⟩ () b = (⟨4, by decide⟩, (), b, Move.stay) := rfl

/-! ### `stepConfig` lemmas (one machine step per phase/bit) -/

/-- φ0 (step-left-to-peek): the phase advances to `1`, the head moves left, tape unchanged. -/
theorem zoneWalkLeft_stepConfig_p0_phase {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 5} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).state).fst.val = 1 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkLeft, hi]

theorem zoneWalkLeft_stepConfig_p0_head {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 5} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.left := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkLeft, hi]

theorem zoneWalkLeft_stepConfig_p0_tape {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 5} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).tape = c.tape := by
  have hwrite : (TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).tape
      = c.write c.head (c.tape c.head) := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, zoneWalkLeft, hi]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-- φ1 (decide) on a `1`: a field block — advance to `2`, head stays. -/
theorem zoneWalkLeft_stepConfig_p1_one_phase {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 5} {s : Unit} (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).state).fst.val = 2 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkLeft, hi, hbit]

theorem zoneWalkLeft_stepConfig_p1_one_head {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 5} {s : Unit} (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).head = c.head := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkLeft, hi, hbit, Configuration.moveHead]

/-- φ1 (decide) on a `0`: the dead-zone left of the sentinel — advance to the done phase `4`, head stays. -/
theorem zoneWalkLeft_stepConfig_p1_zero_phase {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 5} {s : Unit} (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).state).fst.val = 4 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkLeft, hi, hbit]

theorem zoneWalkLeft_stepConfig_p1_zero_head {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 5} {s : Unit} (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).head = c.head := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkLeft, hi, hbit, Configuration.moveHead]

/-- φ1 (decide), either bit: the tape is unchanged. -/
theorem zoneWalkLeft_stepConfig_p1_tape {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 5} {s : Unit} (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).tape = c.tape := by
  have hwrite : (TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).tape
      = c.write c.head (c.tape c.head) := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, zoneWalkLeft, hi]
    cases c.tape c.head <;> simp
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-- φ2 (walk a field's ones) on a `1`: the phase stays `2`, the head moves left. -/
theorem zoneWalkLeft_stepConfig_p2_one_phase {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 5} {s : Unit} (hi : i.val = 2) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).state).fst.val = 2 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkLeft, hi, hbit]

theorem zoneWalkLeft_stepConfig_p2_one_head {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 5} {s : Unit} (hi : i.val = 2) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.left := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkLeft, hi, hbit]

theorem zoneWalkLeft_stepConfig_p2_one_tape {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 5} {s : Unit} (hi : i.val = 2) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).tape = c.tape := by
  have hwrite : (TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).tape
      = c.write c.head true := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, zoneWalkLeft, hi, hbit]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write, hbit]
  · simp [Configuration.write, hj]

/-- φ2 on a `0`: the field's left delimiter — advance to `3`, head stays. -/
theorem zoneWalkLeft_stepConfig_p2_zero_phase {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 5} {s : Unit} (hi : i.val = 2) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).state).fst.val = 3 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkLeft, hi, hbit]

theorem zoneWalkLeft_stepConfig_p2_zero_head {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 5} {s : Unit} (hi : i.val = 2) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).head = c.head := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkLeft, hi, hbit, Configuration.moveHead]

theorem zoneWalkLeft_stepConfig_p2_zero_tape {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 5} {s : Unit} (hi : i.val = 2) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).tape = c.tape := by
  have hwrite : (TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).tape
      = c.write c.head false := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, zoneWalkLeft, hi, hbit]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write, hbit]
  · simp [Configuration.write, hj]

/-- φ3 (cross the delimiter): advance to the loop head `0`, head moves left, tape unchanged. -/
theorem zoneWalkLeft_stepConfig_p3_phase {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 5} {s : Unit} (hi : i.val = 3) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).state).fst.val = 0 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkLeft, hi]

theorem zoneWalkLeft_stepConfig_p3_head {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 5} {s : Unit} (hi : i.val = 3) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.left := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkLeft, hi]

theorem zoneWalkLeft_stepConfig_p3_tape {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 5} {s : Unit} (hi : i.val = 3) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).tape = c.tape := by
  have hwrite : (TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).tape
      = c.write c.head (c.tape c.head) := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, zoneWalkLeft, hi]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-! ### The field sub-scan: φ2 walks a block's `1`s leftward (the inner loop)

The reusable inner step of the walk: from φ2 sitting on the second-rightmost cell of a field block
whose `j` cells `(head − j, head]` are all `1`, after `j` steps φ2 has retreated `j` cells (still in
φ2), tape unchanged — the exact `selfLoopScanLeftOne`-shaped invariant, specialised to `zoneWalkLeft`'s
φ2. -/
theorem zoneWalkLeft_runConfig_p2_scanning {L : Nat}
    (c0 : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 2) :
    ∀ j : Nat, j ≤ (c0.head : Nat) →
      (∀ p : Fin (zoneWalkLeft.toPhased.toTM.tapeLength L),
        (c0.head : Nat) - j < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) → c0.tape p = true) →
      (((TM.runConfig (M := zoneWalkLeft.toPhased.toTM) c0 j).state).fst : Nat) = 2
      ∧ ((TM.runConfig (M := zoneWalkLeft.toPhased.toTM) c0 j).head : Nat) = (c0.head : Nat) - j
      ∧ (TM.runConfig (M := zoneWalkLeft.toPhased.toTM) c0 j).tape = c0.tape := by
  intro j
  induction j with
  | zero => intro _ _; exact ⟨hphase, by simp, rfl⟩
  | succ j ih =>
      intro hj h1
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp1 hp2 => h1 p (by omega) hp2)
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := zoneWalkLeft.toPhased.toTM) c0 j with hc
      have hbit : c.tape c.head = true := by
        rw [htp]; exact h1 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      have hheadne : ¬ (c.head : Nat) = 0 := by rw [hhd]; omega
      have hstate : c.state = ⟨c.state.fst, c.state.snd⟩ := rfl
      refine ⟨?_, ?_, ?_⟩
      · exact zoneWalkLeft_stepConfig_p2_one_phase c hph hstate hbit
      · rw [zoneWalkLeft_stepConfig_p2_one_head c hph hstate hbit]
        simp only [Configuration.moveHead, dif_neg hheadne]
        rw [hhd]; omega
      · rw [zoneWalkLeft_stepConfig_p2_one_tape c hph hstate hbit, htp]

end ContractExpansion
end Frontier
end Pnp4
