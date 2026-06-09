import Pnp4.Frontier.ContractExpansion.TreeMCSPDriverCorridor
import Pnp4.Frontier.ContractExpansion.TreeMCSPLoopUntilSink

/-!
# `zoneWalkLeft` — D2t-5b (Block A4w): traversing a corridor stack zone right-to-left

The corridor layout (A3) stores both stacks as `[sentinel 1] [0 1^{k₁}] [0 1^{k₂}] …` with every
field block carrying **≥ 2** ones and the base sentinel exactly **1** — so a zone can be *walked*
right-to-left without any markers: enter a block at its rightmost `1`, peek one cell left — another
`1` means a field block (walk its remaining ones and hop its delimiter to the next block), a `0`
means the block was the single-`1` **base sentinel**: stop.  `zoneWalkLeft` is that walker; the
driver's cross-zone routes (cursor → control top → value top → WORK frontier and back) chain it with
the 0-corridor scans.

Phases: φ0 enter block (step left off its rightmost `1`); φ1 peek (`1` → field, φ2; `0` → it was the
sentinel, φ5 done); φ2 walk the field's remaining ones (self-loop left, stop on the delimiter `0`);
φ3 step left off the delimiter; φ4 confirm the next block's `1` (re-enter φ0 shape via a stay);
φ5 done — the head rests on the `0` immediately **left of the sentinel**, exactly where the caller's
next leftward 0-corridor scan begins.

**Progress classification (AGENTS.md): Infrastructure** — a verifier machine component; builds no
verifier and proves no separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.
**No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- **The leftward zone walker** (6 phases).  φ0 step into the block; φ1 peek (field vs sentinel);
φ2 walk the field's ones; φ3 step off the delimiter; φ4 re-enter; φ5 done (sentinel found, head on
the `0` just left of it). -/
def zoneWalkLeft : ConstStatePhasedProgram Unit where
  numPhases := 6
  startPhase := ⟨0, by decide⟩
  startState := ()
  acceptPhase := ⟨5, by decide⟩
  acceptState := ()
  transition := fun i _ b =>
    if i.val = 0 then
      -- on the block's rightmost 1: step left to peek
      (⟨1, by decide⟩, (), b, Move.left)
    else if i.val = 1 then
      -- peek: 1 = a ≥2 field block (walk it); 0 = the block was the single-1 sentinel (done)
      if b then (⟨2, by decide⟩, (), b, Move.stay)
      else (⟨5, by decide⟩, (), b, Move.stay)
    else if i.val = 2 then
      -- walk the field's remaining ones leftward; the 0 is the field's left delimiter
      if b then (⟨2, by decide⟩, (), b, Move.left)
      else (⟨3, by decide⟩, (), b, Move.stay)
    else if i.val = 3 then
      -- step left off the delimiter onto the next block's rightmost 1
      (⟨4, by decide⟩, (), b, Move.left)
    else if i.val = 4 then
      -- confirm and re-enter the block walk (the adjacency invariant guarantees a 1)
      if b then (⟨1, by decide⟩, (), b, Move.left)
      else (⟨5, by decide⟩, (), b, Move.stay)
    else
      -- φ5: done — idle
      (⟨5, by decide⟩, (), b, Move.stay)
  timeBound := fun n => n

@[simp] theorem zoneWalkLeft_numPhases : zoneWalkLeft.numPhases = 6 := rfl

@[simp] theorem zoneWalkLeft_startPhase : (zoneWalkLeft.startPhase : Nat) = 0 := rfl

@[simp] theorem zoneWalkLeft_acceptPhase : (zoneWalkLeft.acceptPhase : Nat) = 5 := rfl

/-! ### Transition lemmas -/

theorem zoneWalkLeft_t0 (b : Bool) :
    zoneWalkLeft.transition ⟨0, by decide⟩ () b = (⟨1, by decide⟩, (), b, Move.left) := rfl

theorem zoneWalkLeft_t1_one :
    zoneWalkLeft.transition ⟨1, by decide⟩ () true = (⟨2, by decide⟩, (), true, Move.stay) := rfl

theorem zoneWalkLeft_t1_zero :
    zoneWalkLeft.transition ⟨1, by decide⟩ () false = (⟨5, by decide⟩, (), false, Move.stay) := rfl

theorem zoneWalkLeft_t2_one :
    zoneWalkLeft.transition ⟨2, by decide⟩ () true = (⟨2, by decide⟩, (), true, Move.left) := rfl

theorem zoneWalkLeft_t2_zero :
    zoneWalkLeft.transition ⟨2, by decide⟩ () false = (⟨3, by decide⟩, (), false, Move.stay) := rfl

theorem zoneWalkLeft_t3 (b : Bool) :
    zoneWalkLeft.transition ⟨3, by decide⟩ () b = (⟨4, by decide⟩, (), b, Move.left) := rfl

theorem zoneWalkLeft_t4_one :
    zoneWalkLeft.transition ⟨4, by decide⟩ () true = (⟨1, by decide⟩, (), true, Move.left) := rfl

theorem zoneWalkLeft_t4_zero :
    zoneWalkLeft.transition ⟨4, by decide⟩ () false = (⟨5, by decide⟩, (), false, Move.stay) := rfl

theorem zoneWalkLeft_t5 (b : Bool) :
    zoneWalkLeft.transition ⟨5, by decide⟩ () b = (⟨5, by decide⟩, (), b, Move.stay) := rfl

/-! ### `stepConfig` lemmas (one machine step per phase/bit) -/

/-- φ0 (enter block): the phase advances to `1`. -/
theorem zoneWalkLeft_stepConfig_p0_phase {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).state).fst.val = 1 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkLeft, hi]

/-- φ0: the head moves left. -/
theorem zoneWalkLeft_stepConfig_p0_head {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.left := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkLeft, hi]

/-- φ0: the tape is unchanged (the read bit is written back). -/
theorem zoneWalkLeft_stepConfig_p0_tape {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) :
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

/-- φ1 (peek) on a `1`: a field block — advance to `2`, head stays, tape unchanged. -/
theorem zoneWalkLeft_stepConfig_p1_one_phase {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).state).fst.val = 2 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkLeft, hi, hbit]

theorem zoneWalkLeft_stepConfig_p1_one_head {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).head = c.head := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkLeft, hi, hbit, Configuration.moveHead]

/-- φ1 (peek) on a `0`: the base sentinel — advance to the done phase `5`, head stays. -/
theorem zoneWalkLeft_stepConfig_p1_zero_phase {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).state).fst.val = 5 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkLeft, hi, hbit]

theorem zoneWalkLeft_stepConfig_p1_zero_head {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).head = c.head := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkLeft, hi, hbit, Configuration.moveHead]

/-- φ1 (peek), either bit: the tape is unchanged. -/
theorem zoneWalkLeft_stepConfig_p1_tape {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩) :
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
    {i : Fin 6} {s : Unit} (hi : i.val = 2) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).state).fst.val = 2 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkLeft, hi, hbit]

theorem zoneWalkLeft_stepConfig_p2_one_head {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 2) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.left := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkLeft, hi, hbit]

theorem zoneWalkLeft_stepConfig_p2_one_tape {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 2) (hstate : c.state = ⟨i, s⟩)
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
    {i : Fin 6} {s : Unit} (hi : i.val = 2) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).state).fst.val = 3 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkLeft, hi, hbit]

theorem zoneWalkLeft_stepConfig_p2_zero_head {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 2) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).head = c.head := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkLeft, hi, hbit, Configuration.moveHead]

theorem zoneWalkLeft_stepConfig_p2_zero_tape {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 2) (hstate : c.state = ⟨i, s⟩)
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

/-- φ3 (step off the delimiter): advance to `4`, head moves left, tape unchanged. -/
theorem zoneWalkLeft_stepConfig_p3_phase {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 3) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).state).fst.val = 4 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkLeft, hi]

theorem zoneWalkLeft_stepConfig_p3_head {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 3) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.left := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkLeft, hi]

theorem zoneWalkLeft_stepConfig_p3_tape {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 3) (hstate : c.state = ⟨i, s⟩) :
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

/-- φ4 (confirm next block) on a `1`: re-enter the peek loop at `1`, head moves left. -/
theorem zoneWalkLeft_stepConfig_p4_one_phase {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 4) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).state).fst.val = 1 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkLeft, hi, hbit]

theorem zoneWalkLeft_stepConfig_p4_one_head {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 4) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.left := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkLeft, hi, hbit]

/-- φ4 on a `0`: the sentinel reached via the confirm path — advance to the done phase `5`, head stays. -/
theorem zoneWalkLeft_stepConfig_p4_zero_phase {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 4) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).state).fst.val = 5 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkLeft, hi, hbit]

theorem zoneWalkLeft_stepConfig_p4_zero_head {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 4) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    (TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c).head = c.head := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, zoneWalkLeft, hi, hbit, Configuration.moveHead]

theorem zoneWalkLeft_stepConfig_p4_tape {L : Nat}
    (c : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    {i : Fin 6} {s : Unit} (hi : i.val = 4) (hstate : c.state = ⟨i, s⟩) :
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

/-! ### The field sub-scan: φ2 walks a block's `1`s leftward (the inner loop)

The reusable inner step of the walk: from φ2 sitting on the rightmost `1` of a field block whose `j`
cells `(head − j, head]` are all `1`, after `j` steps φ2 has retreated `j` cells (still in φ2), tape
unchanged — the exact `selfLoopScanLeftOne`-shaped invariant, specialised to `zoneWalkLeft`'s φ2. -/
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
