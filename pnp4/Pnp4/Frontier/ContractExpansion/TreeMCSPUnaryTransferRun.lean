import Pnp4.Frontier.ContractExpansion.TreeMCSPUnaryTransferProgram
import Pnp4.Frontier.ContractExpansion.BoundedLoopProgram

/-!
# `unaryTransfer` — D2t-5b (Block A2): the transfer loop's run behaviour

Wraps `unaryTransferBody` in `loopUntilSink` (sink φ8) and proves the per-phase step facts and the
segment walk-throughs of one pass.  The pass/termination headline lemmas build on these (same file
chain as the binToUnary loop: program → run → reachesSink).

**Progress classification (AGENTS.md): Infrastructure** — verifier machine component run lemmas; builds
no verifier and proves no separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.
**No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- **The unary-block transfer loop**: run `unaryTransferBody` passes until the source-exhausted sink φ8. -/
def unaryTransfer : ConstStatePhasedProgram Unit :=
  loopUntilSink unaryTransferBody ⟨8, by decide⟩

@[simp] theorem unaryTransfer_numPhases : unaryTransfer.numPhases = 9 := rfl

@[simp] theorem unaryTransfer_startPhase : (unaryTransfer.startPhase : Nat) = 0 := rfl

/-- The wrapped transition agrees with the body's away from φ7 (back-edge) and φ8 (sink). -/
theorem unaryTransfer_transition_body {i : Fin 9} (h7 : i.val ≠ 7) (h8 : i.val ≠ 8)
    (s : Unit) (b : Bool) :
    unaryTransfer.transition i s b = unaryTransferBody.transition i () b := by
  refine loopUntilSink_transition_body unaryTransferBody ⟨8, by decide⟩ ?_ ?_ s b
  · intro h
    exact h7 (by simpa using congrArg Fin.val h)
  · intro h
    exact h8 (by simpa using congrArg Fin.val h)

/-- The φ7 back-edge: re-enter φ0, bit written back, head stays. -/
theorem unaryTransfer_transition_backedge (s : Unit) (b : Bool) :
    unaryTransfer.transition ⟨7, by decide⟩ s b = (⟨0, by decide⟩, (), b, Move.stay) := by
  have h := loopUntilSink_transition_loop unaryTransferBody ⟨8, by decide⟩ s b
  simpa [unaryTransfer] using h

/-- The φ8 sink: idle. -/
theorem unaryTransfer_transition_sink (s : Unit) (b : Bool) :
    unaryTransfer.transition ⟨8, by decide⟩ s b = (⟨8, by decide⟩, (), b, Move.stay) := by
  have h := loopUntilSink_transition_halt unaryTransferBody ⟨8, by decide⟩ (by decide) s b
  simpa [unaryTransfer] using h

/-! ### Generic step triple for the wrapped machine

Each lemma packages phase/head/tape of one `stepConfig` of `unaryTransfer` given the scanned bit, via
the `toTM_stepConfig_*` helpers and the transition characterizations above. -/

section StepTriples

variable {L : Nat} (c : Configuration (M := unaryTransfer.toPhased.toTM) L)

/-- φ0 on a `1`: stay in φ0, write the `1` back, move right. -/
theorem unaryTransfer_step_phi0_one {i : Fin 9} {s : Unit} (hi : i.val = 0)
    (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).state).fst.val = 0
    ∧ (TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).head = c.moveHead Move.right
    ∧ (TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).tape = c.write c.head true := by
  have hieq : i = ⟨0, by decide⟩ := Fin.ext hi
  subst hieq
  have htr : unaryTransfer.transition ⟨0, by decide⟩ s (c.tape c.head)
      = (⟨0, by decide⟩, (), true, Move.right) := by
    rw [unaryTransfer_transition_body (by decide) (by decide), hbit]
    exact unaryTransferBody_t0_one
  refine ⟨?_, ?_, ?_⟩
  · rw [toTM_stepConfig_phase unaryTransfer c hstate, htr]
  · rw [toTM_stepConfig_head unaryTransfer c hstate, htr]
  · rw [toTM_stepConfig_tape unaryTransfer c hstate, htr]

/-- φ0 on a `0` (the frontier): write the transferred unit, move right, → φ1. -/
theorem unaryTransfer_step_phi0_zero {i : Fin 9} {s : Unit} (hi : i.val = 0)
    (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).state).fst.val = 1
    ∧ (TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).head = c.moveHead Move.right
    ∧ (TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).tape = c.write c.head true := by
  have hieq : i = ⟨0, by decide⟩ := Fin.ext hi
  subst hieq
  have htr : unaryTransfer.transition ⟨0, by decide⟩ s (c.tape c.head)
      = (⟨1, by decide⟩, (), true, Move.right) := by
    rw [unaryTransfer_transition_body (by decide) (by decide), hbit]
    exact unaryTransferBody_t0_zero
  refine ⟨?_, ?_, ?_⟩
  · rw [toTM_stepConfig_phase unaryTransfer c hstate, htr]
  · rw [toTM_stepConfig_head unaryTransfer c hstate, htr]
  · rw [toTM_stepConfig_tape unaryTransfer c hstate, htr]

/-- φ1 on a `0` (gap): stay in φ1, bit back, move right. -/
theorem unaryTransfer_step_phi1_zero {i : Fin 9} {s : Unit} (hi : i.val = 1)
    (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).state).fst.val = 1
    ∧ (TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).head = c.moveHead Move.right
    ∧ (TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).tape = c.write c.head false := by
  have hieq : i = ⟨1, by decide⟩ := Fin.ext hi
  subst hieq
  have htr : unaryTransfer.transition ⟨1, by decide⟩ s (c.tape c.head)
      = (⟨1, by decide⟩, (), false, Move.right) := by
    rw [unaryTransfer_transition_body (by decide) (by decide), hbit]
    exact unaryTransferBody_t1_zero
  refine ⟨?_, ?_, ?_⟩
  · rw [toTM_stepConfig_phase unaryTransfer c hstate, htr]
  · rw [toTM_stepConfig_head unaryTransfer c hstate, htr]
  · rw [toTM_stepConfig_tape unaryTransfer c hstate, htr]

/-- φ1 on a `1` (the source's head): → φ2, stay. -/
theorem unaryTransfer_step_phi1_one {i : Fin 9} {s : Unit} (hi : i.val = 1)
    (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).state).fst.val = 2
    ∧ (TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).head = c.moveHead Move.stay
    ∧ (TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).tape = c.write c.head true := by
  have hieq : i = ⟨1, by decide⟩ := Fin.ext hi
  subst hieq
  have htr : unaryTransfer.transition ⟨1, by decide⟩ s (c.tape c.head)
      = (⟨2, by decide⟩, (), true, Move.stay) := by
    rw [unaryTransfer_transition_body (by decide) (by decide), hbit]
    exact unaryTransferBody_t1_one
  refine ⟨?_, ?_, ?_⟩
  · rw [toTM_stepConfig_phase unaryTransfer c hstate, htr]
  · rw [toTM_stepConfig_head unaryTransfer c hstate, htr]
  · rw [toTM_stepConfig_tape unaryTransfer c hstate, htr]

/-- φ2 (erase): write `0`, move right, → φ3. -/
theorem unaryTransfer_step_phi2 {i : Fin 9} {s : Unit} (hi : i.val = 2)
    (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).state).fst.val = 3
    ∧ (TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).head = c.moveHead Move.right
    ∧ (TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).tape = c.write c.head false := by
  have hieq : i = ⟨2, by decide⟩ := Fin.ext hi
  subst hieq
  have htr : unaryTransfer.transition ⟨2, by decide⟩ s (c.tape c.head)
      = (⟨3, by decide⟩, (), false, Move.right) := by
    rw [unaryTransfer_transition_body (by decide) (by decide)]
    exact unaryTransferBody_t2 _
  refine ⟨?_, ?_, ?_⟩
  · rw [toTM_stepConfig_phase unaryTransfer c hstate, htr]
  · rw [toTM_stepConfig_head unaryTransfer c hstate, htr]
  · rw [toTM_stepConfig_tape unaryTransfer c hstate, htr]

/-- φ3 peek on a `1` (more units): → φ4, move left, bit back. -/
theorem unaryTransfer_step_phi3_one {i : Fin 9} {s : Unit} (hi : i.val = 3)
    (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).state).fst.val = 4
    ∧ (TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).head = c.moveHead Move.left
    ∧ (TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).tape = c.write c.head true := by
  have hieq : i = ⟨3, by decide⟩ := Fin.ext hi
  subst hieq
  have htr : unaryTransfer.transition ⟨3, by decide⟩ s (c.tape c.head)
      = (⟨4, by decide⟩, (), true, Move.left) := by
    rw [unaryTransfer_transition_body (by decide) (by decide), hbit]
    exact unaryTransferBody_t3_one
  refine ⟨?_, ?_, ?_⟩
  · rw [toTM_stepConfig_phase unaryTransfer c hstate, htr]
  · rw [toTM_stepConfig_head unaryTransfer c hstate, htr]
  · rw [toTM_stepConfig_tape unaryTransfer c hstate, htr]

/-- φ3 peek on a `0` (the source terminator): → φ8 **sink**, stay, bit back. -/
theorem unaryTransfer_step_phi3_zero {i : Fin 9} {s : Unit} (hi : i.val = 3)
    (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).state).fst.val = 8
    ∧ (TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).head = c.moveHead Move.stay
    ∧ (TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).tape = c.write c.head false := by
  have hieq : i = ⟨3, by decide⟩ := Fin.ext hi
  subst hieq
  have htr : unaryTransfer.transition ⟨3, by decide⟩ s (c.tape c.head)
      = (⟨8, by decide⟩, (), false, Move.stay) := by
    rw [unaryTransfer_transition_body (by decide) (by decide), hbit]
    exact unaryTransferBody_t3_zero
  refine ⟨?_, ?_, ?_⟩
  · rw [toTM_stepConfig_phase unaryTransfer c hstate, htr]
  · rw [toTM_stepConfig_head unaryTransfer c hstate, htr]
  · rw [toTM_stepConfig_tape unaryTransfer c hstate, htr]

/-- φ4 on a `0` (gap, leftward): stay in φ4, bit back, move left. -/
theorem unaryTransfer_step_phi4_zero {i : Fin 9} {s : Unit} (hi : i.val = 4)
    (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).state).fst.val = 4
    ∧ (TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).head = c.moveHead Move.left
    ∧ (TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).tape = c.write c.head false := by
  have hieq : i = ⟨4, by decide⟩ := Fin.ext hi
  subst hieq
  have htr : unaryTransfer.transition ⟨4, by decide⟩ s (c.tape c.head)
      = (⟨4, by decide⟩, (), false, Move.left) := by
    rw [unaryTransfer_transition_body (by decide) (by decide), hbit]
    exact unaryTransferBody_t4_zero
  refine ⟨?_, ?_, ?_⟩
  · rw [toTM_stepConfig_phase unaryTransfer c hstate, htr]
  · rw [toTM_stepConfig_head unaryTransfer c hstate, htr]
  · rw [toTM_stepConfig_tape unaryTransfer c hstate, htr]

/-- φ4 on a `1` (the destination's right end): → φ5, stay. -/
theorem unaryTransfer_step_phi4_one {i : Fin 9} {s : Unit} (hi : i.val = 4)
    (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).state).fst.val = 5
    ∧ (TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).head = c.moveHead Move.stay
    ∧ (TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).tape = c.write c.head true := by
  have hieq : i = ⟨4, by decide⟩ := Fin.ext hi
  subst hieq
  have htr : unaryTransfer.transition ⟨4, by decide⟩ s (c.tape c.head)
      = (⟨5, by decide⟩, (), true, Move.stay) := by
    rw [unaryTransfer_transition_body (by decide) (by decide), hbit]
    exact unaryTransferBody_t4_one
  refine ⟨?_, ?_, ?_⟩
  · rw [toTM_stepConfig_phase unaryTransfer c hstate, htr]
  · rw [toTM_stepConfig_head unaryTransfer c hstate, htr]
  · rw [toTM_stepConfig_tape unaryTransfer c hstate, htr]

/-- φ5 on a `1` (destination walk, leftward): stay in φ5, bit back, move left. -/
theorem unaryTransfer_step_phi5_one {i : Fin 9} {s : Unit} (hi : i.val = 5)
    (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).state).fst.val = 5
    ∧ (TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).head = c.moveHead Move.left
    ∧ (TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).tape = c.write c.head true := by
  have hieq : i = ⟨5, by decide⟩ := Fin.ext hi
  subst hieq
  have htr : unaryTransfer.transition ⟨5, by decide⟩ s (c.tape c.head)
      = (⟨5, by decide⟩, (), true, Move.left) := by
    rw [unaryTransfer_transition_body (by decide) (by decide), hbit]
    exact unaryTransferBody_t5_one
  refine ⟨?_, ?_, ?_⟩
  · rw [toTM_stepConfig_phase unaryTransfer c hstate, htr]
  · rw [toTM_stepConfig_head unaryTransfer c hstate, htr]
  · rw [toTM_stepConfig_tape unaryTransfer c hstate, htr]

/-- φ5 on a `0` (the home delimiter): → φ6, stay. -/
theorem unaryTransfer_step_phi5_zero {i : Fin 9} {s : Unit} (hi : i.val = 5)
    (hstate : c.state = ⟨i, s⟩) (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).state).fst.val = 6
    ∧ (TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).head = c.moveHead Move.stay
    ∧ (TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).tape = c.write c.head false := by
  have hieq : i = ⟨5, by decide⟩ := Fin.ext hi
  subst hieq
  have htr : unaryTransfer.transition ⟨5, by decide⟩ s (c.tape c.head)
      = (⟨6, by decide⟩, (), false, Move.stay) := by
    rw [unaryTransfer_transition_body (by decide) (by decide), hbit]
    exact unaryTransferBody_t5_zero
  refine ⟨?_, ?_, ?_⟩
  · rw [toTM_stepConfig_phase unaryTransfer c hstate, htr]
  · rw [toTM_stepConfig_head unaryTransfer c hstate, htr]
  · rw [toTM_stepConfig_tape unaryTransfer c hstate, htr]

/-- φ6 (re-home): one step right, → φ7. -/
theorem unaryTransfer_step_phi6 {i : Fin 9} {s : Unit} (hi : i.val = 6)
    (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).state).fst.val = 7
    ∧ (TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).head = c.moveHead Move.right
    ∧ (TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).tape
        = c.write c.head (c.tape c.head) := by
  have hieq : i = ⟨6, by decide⟩ := Fin.ext hi
  subst hieq
  have htr : unaryTransfer.transition ⟨6, by decide⟩ s (c.tape c.head)
      = (⟨7, by decide⟩, (), c.tape c.head, Move.right) := by
    rw [unaryTransfer_transition_body (by decide) (by decide)]
    exact unaryTransferBody_t6 _
  refine ⟨?_, ?_, ?_⟩
  · rw [toTM_stepConfig_phase unaryTransfer c hstate, htr]
  · rw [toTM_stepConfig_head unaryTransfer c hstate, htr]
  · rw [toTM_stepConfig_tape unaryTransfer c hstate, htr]

/-- φ7 (back-edge): re-enter φ0, stay, bit back. -/
theorem unaryTransfer_step_phi7 {i : Fin 9} {s : Unit} (hi : i.val = 7)
    (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).state).fst.val = 0
    ∧ (TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).head = c.moveHead Move.stay
    ∧ (TM.stepConfig (M := unaryTransfer.toPhased.toTM) c).tape
        = c.write c.head (c.tape c.head) := by
  have hieq : i = ⟨7, by decide⟩ := Fin.ext hi
  subst hieq
  have htr : unaryTransfer.transition ⟨7, by decide⟩ s (c.tape c.head)
      = (⟨0, by decide⟩, (), c.tape c.head, Move.stay) :=
    unaryTransfer_transition_backedge s (c.tape c.head)
  refine ⟨?_, ?_, ?_⟩
  · rw [toTM_stepConfig_phase unaryTransfer c hstate, htr]
  · rw [toTM_stepConfig_head unaryTransfer c hstate, htr]
  · rw [toTM_stepConfig_tape unaryTransfer c hstate, htr]

end StepTriples

/-- A write that re-writes the scanned bit leaves the tape unchanged. -/
theorem write_self_eq {L : Nat} {M : TM}
    (c : Configuration (M := M) L) :
    c.write c.head (c.tape c.head) = c.tape := by
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-! ### Segment walk-throughs (per-phase self-loop runs) -/

/-- φ0 walk: `k` ones rightward leave phase/tape fixed and advance the head by `k`. -/
theorem unaryTransfer_run_phi0_walk {L : Nat}
    (c0 : Configuration (M := unaryTransfer.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) :
    ∀ k : Nat, (c0.head : Nat) + k < unaryTransfer.toPhased.toTM.tapeLength L →
      (∀ p : Fin (unaryTransfer.toPhased.toTM.tapeLength L),
        (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + k → c0.tape p = true) →
      (((TM.runConfig (M := unaryTransfer.toPhased.toTM) c0 k).state).fst : Nat) = 0
      ∧ ((TM.runConfig (M := unaryTransfer.toPhased.toTM) c0 k).head : Nat) = (c0.head : Nat) + k
      ∧ (TM.runConfig (M := unaryTransfer.toPhased.toTM) c0 k).tape = c0.tape := by
  intro k
  induction k with
  | zero => intro _ _; exact ⟨hphase, by simp, rfl⟩
  | succ k ih =>
      intro hk h1
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp1 hp2 => h1 p hp1 (by omega))
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := unaryTransfer.toPhased.toTM) c0 k with hc
      have hbit : c.tape c.head = true := by
        rw [htp]; exact h1 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      obtain ⟨hsp, hsh, hst⟩ := unaryTransfer_step_phi0_one c
        (i := c.state.fst) (s := c.state.snd) hph rfl hbit
      have hbnd : (c.head : Nat) + 1 < unaryTransfer.toPhased.toTM.tapeLength L := by
        rw [hhd]; omega
      refine ⟨hsp, ?_, ?_⟩
      · rw [hsh]
        simp only [Configuration.moveHead, dif_pos hbnd]
        omega
      · rw [hst, ← hbit, write_self_eq, htp]

/-- φ1 scan: `k` zeros rightward leave phase/tape fixed and advance the head by `k`. -/
theorem unaryTransfer_run_phi1_scan {L : Nat}
    (c0 : Configuration (M := unaryTransfer.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 1) :
    ∀ k : Nat, (c0.head : Nat) + k < unaryTransfer.toPhased.toTM.tapeLength L →
      (∀ p : Fin (unaryTransfer.toPhased.toTM.tapeLength L),
        (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + k → c0.tape p = false) →
      (((TM.runConfig (M := unaryTransfer.toPhased.toTM) c0 k).state).fst : Nat) = 1
      ∧ ((TM.runConfig (M := unaryTransfer.toPhased.toTM) c0 k).head : Nat) = (c0.head : Nat) + k
      ∧ (TM.runConfig (M := unaryTransfer.toPhased.toTM) c0 k).tape = c0.tape := by
  intro k
  induction k with
  | zero => intro _ _; exact ⟨hphase, by simp, rfl⟩
  | succ k ih =>
      intro hk h1
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp1 hp2 => h1 p hp1 (by omega))
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := unaryTransfer.toPhased.toTM) c0 k with hc
      have hbit : c.tape c.head = false := by
        rw [htp]; exact h1 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      obtain ⟨hsp, hsh, hst⟩ := unaryTransfer_step_phi1_zero c
        (i := c.state.fst) (s := c.state.snd) hph rfl hbit
      have hbnd : (c.head : Nat) + 1 < unaryTransfer.toPhased.toTM.tapeLength L := by
        rw [hhd]; omega
      refine ⟨hsp, ?_, ?_⟩
      · rw [hsh]
        simp only [Configuration.moveHead, dif_pos hbnd]
        omega
      · rw [hst, ← hbit, write_self_eq, htp]

/-- φ4 scan: `k` zeros **leftward** leave phase/tape fixed and retreat the head by `k`. -/
theorem unaryTransfer_run_phi4_scan {L : Nat}
    (c0 : Configuration (M := unaryTransfer.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 4) :
    ∀ k : Nat, k ≤ (c0.head : Nat) →
      (∀ p : Fin (unaryTransfer.toPhased.toTM.tapeLength L),
        (c0.head : Nat) - k < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) → c0.tape p = false) →
      (((TM.runConfig (M := unaryTransfer.toPhased.toTM) c0 k).state).fst : Nat) = 4
      ∧ ((TM.runConfig (M := unaryTransfer.toPhased.toTM) c0 k).head : Nat) = (c0.head : Nat) - k
      ∧ (TM.runConfig (M := unaryTransfer.toPhased.toTM) c0 k).tape = c0.tape := by
  intro k
  induction k with
  | zero => intro _ _; exact ⟨hphase, by simp, rfl⟩
  | succ k ih =>
      intro hk h1
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp1 hp2 => h1 p (by omega) hp2)
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := unaryTransfer.toPhased.toTM) c0 k with hc
      have hbit : c.tape c.head = false := by
        rw [htp]; exact h1 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      obtain ⟨hsp, hsh, hst⟩ := unaryTransfer_step_phi4_zero c
        (i := c.state.fst) (s := c.state.snd) hph rfl hbit
      have hpos : 0 < (c.head : Nat) := by rw [hhd]; omega
      refine ⟨hsp, ?_, ?_⟩
      · rw [hsh, Configuration.moveHead_left_val_of_pos c hpos, hhd]; omega
      · rw [hst, ← hbit, write_self_eq, htp]

/-- φ5 walk: `k` ones **leftward** leave phase/tape fixed and retreat the head by `k`. -/
theorem unaryTransfer_run_phi5_walk {L : Nat}
    (c0 : Configuration (M := unaryTransfer.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 5) :
    ∀ k : Nat, k ≤ (c0.head : Nat) →
      (∀ p : Fin (unaryTransfer.toPhased.toTM.tapeLength L),
        (c0.head : Nat) - k < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) → c0.tape p = true) →
      (((TM.runConfig (M := unaryTransfer.toPhased.toTM) c0 k).state).fst : Nat) = 5
      ∧ ((TM.runConfig (M := unaryTransfer.toPhased.toTM) c0 k).head : Nat) = (c0.head : Nat) - k
      ∧ (TM.runConfig (M := unaryTransfer.toPhased.toTM) c0 k).tape = c0.tape := by
  intro k
  induction k with
  | zero => intro _ _; exact ⟨hphase, by simp, rfl⟩
  | succ k ih =>
      intro hk h1
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp1 hp2 => h1 p (by omega) hp2)
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := unaryTransfer.toPhased.toTM) c0 k with hc
      have hbit : c.tape c.head = true := by
        rw [htp]; exact h1 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      obtain ⟨hsp, hsh, hst⟩ := unaryTransfer_step_phi5_one c
        (i := c.state.fst) (s := c.state.snd) hph rfl hbit
      have hpos : 0 < (c.head : Nat) := by rw [hhd]; omega
      refine ⟨hsp, ?_, ?_⟩
      · rw [hsh, Configuration.moveHead_left_val_of_pos c hpos, hhd]; omega
      · rw [hst, ← hbit, write_self_eq, htp]

/-! ### The pass invariant and the one-pass walk-through -/

/-- One step of `runConfig` is one `stepConfig`. -/
theorem unaryTransfer_runConfig_one {L : Nat}
    (c : Configuration (M := unaryTransfer.toPhased.toTM) L) :
    TM.runConfig (M := unaryTransfer.toPhased.toTM) c 1
      = TM.stepConfig (M := unaryTransfer.toPhased.toTM) c := by
  have h := TM.runConfig_succ (M := unaryTransfer.toPhased.toTM) c 0
  simpa using h

/-- **The transfer-pass layout** (the loop invariant, `γ`-additive so all position arithmetic is
linear).  With `S := opBase + d + γ`: the head rests at HOME `opBase` in φ0; `opBase − 1` holds the
home delimiter `0`; the destination block `1^(d+j)` fills `[opBase, opBase+d+j)`; the gap `0^γ` fills
`[opBase+d+j, S+j)`; the remaining source `1^(m−j)` fills `[S+j, S+m)`; `S+m` holds the source
terminator `0`. -/
structure TransferLayout {L : Nat} (c : Configuration (M := unaryTransfer.toPhased.toTM) L)
    (opBase d j γ m : Nat) : Prop where
  hphase : (c.state.fst : Nat) = 0
  hhead : (c.head : Nat) = opBase
  hopPos : 1 ≤ opBase
  hg1 : 1 ≤ γ
  hjm : j ≤ m
  hbound : opBase + d + γ + m + 1 < unaryTransfer.toPhased.toTM.tapeLength L
  hdelim : ∀ p : Fin (unaryTransfer.toPhased.toTM.tapeLength L),
    (p : Nat) = opBase - 1 → c.tape p = false
  hdst : ∀ p : Fin (unaryTransfer.toPhased.toTM.tapeLength L),
    opBase ≤ (p : Nat) → (p : Nat) < opBase + d + j → c.tape p = true
  hgap : ∀ p : Fin (unaryTransfer.toPhased.toTM.tapeLength L),
    opBase + d + j ≤ (p : Nat) → (p : Nat) < opBase + d + γ + j → c.tape p = false
  hsrc : ∀ p : Fin (unaryTransfer.toPhased.toTM.tapeLength L),
    opBase + d + γ + j ≤ (p : Nat) → (p : Nat) < opBase + d + γ + m → c.tape p = true
  hterm : ∀ p : Fin (unaryTransfer.toPhased.toTM.tapeLength L),
    (p : Nat) = opBase + d + γ + m → c.tape p = false

/-- **One more-pass** (`j + 1 < m`): exactly `2(d+j) + 2γ + 8` steps later the layout holds at
`j + 1`, and the tape outside `[opBase, opBase+d+γ+m]` is untouched. -/
theorem unaryTransfer_pass_more {L : Nat}
    (c : Configuration (M := unaryTransfer.toPhased.toTM) L)
    (opBase d j γ m : Nat) (hlay : TransferLayout c opBase d j γ m) (hjm1 : j + 1 < m) :
    TransferLayout
        (TM.runConfig (M := unaryTransfer.toPhased.toTM) c (2 * (d + j) + 2 * γ + 8))
        opBase d (j + 1) γ m
    ∧ ∀ p : Fin (unaryTransfer.toPhased.toTM.tapeLength L),
        ((p : Nat) < opBase ∨ opBase + d + γ + m ≤ (p : Nat)) →
        (TM.runConfig (M := unaryTransfer.toPhased.toTM) c (2 * (d + j) + 2 * γ + 8)).tape p
          = c.tape p := by
  obtain ⟨hphase, hhead, hopPos, hg1, hjm, hbound, hdelim, hdst, hgap, hsrc, hterm⟩ := hlay
  obtain ⟨g1, hg⟩ : ∃ g1, γ = g1 + 1 := ⟨γ - 1, by omega⟩
  -- φ0 walk over the d+j destination ones
  obtain ⟨h1p, h1h, h1t⟩ := unaryTransfer_run_phi0_walk c hphase (d + j)
    (by omega) (fun p hp1 hp2 => hdst p (by omega) (by omega))
  set c1 := TM.runConfig (M := unaryTransfer.toPhased.toTM) c (d + j) with hc1
  -- φ0 append at the frontier (gap cell)
  have hb1 : c1.tape c1.head = false := by
    rw [h1t]; exact hgap c1.head (by omega) (by omega)
  obtain ⟨h2p, h2h, h2t⟩ := unaryTransfer_step_phi0_zero c1
    (i := c1.state.fst) (s := c1.state.snd) h1p rfl hb1
  have hb1bnd : (c1.head : Nat) + 1 < unaryTransfer.toPhased.toTM.tapeLength L := by omega
  set c2 := TM.stepConfig (M := unaryTransfer.toPhased.toTM) c1 with hc2
  have h2h' : (c2.head : Nat) = opBase + d + j + 1 := by
    rw [hc2, h2h]
    simp only [Configuration.moveHead, dif_pos hb1bnd]
    omega
  have h2t' : ∀ p : Fin (unaryTransfer.toPhased.toTM.tapeLength L),
      c2.tape p = if (p : Nat) = opBase + d + j then true else c.tape p := by
    intro p
    rw [hc2, h2t]
    by_cases hp : p = c1.head
    · subst hp
      have hv : ((c1.head : Fin _) : Nat) = opBase + d + j := by omega
      rw [if_pos hv]
      simp [Configuration.write]
    · have hpv : (p : Nat) ≠ opBase + d + j := by
        intro hv; exact hp (Fin.ext (by omega))
      rw [if_neg hpv]
      have hw : (c1.write c1.head true) p = c1.tape p := by
        simp [Configuration.write, hp]
      rw [hw, h1t]
  -- φ1 scan across the remaining γ−1 gap zeros
  obtain ⟨h3p, h3h, h3t⟩ := unaryTransfer_run_phi1_scan c2 h2p g1
    (by omega)
    (fun p hp1 hp2 => by
      rw [h2t', if_neg (by omega : ¬ (p : Nat) = opBase + d + j)]
      exact hgap p (by omega) (by omega))
  set c3 := TM.runConfig (M := unaryTransfer.toPhased.toTM) c2 g1 with hc3
  have h3h' : (c3.head : Nat) = opBase + d + j + γ := by omega
  -- φ1 hits the source head (a 1)
  have hb3 : c3.tape c3.head = true := by
    rw [h3t, h2t', if_neg (by omega : ¬ ((c3.head : Fin _) : Nat) = opBase + d + j)]
    exact hsrc c3.head (by omega) (by omega)
  obtain ⟨h4p, h4h, h4t⟩ := unaryTransfer_step_phi1_one c3
    (i := c3.state.fst) (s := c3.state.snd) h3p rfl hb3
  set c4 := TM.stepConfig (M := unaryTransfer.toPhased.toTM) c3 with hc4
  have h4h' : (c4.head : Nat) = opBase + d + j + γ := by
    rw [hc4, h4h, Configuration.moveHead_stay]; omega
  have hwf3 : c3.write c3.head true = c3.tape := by
    rw [← hb3]; exact write_self_eq c3
  have h4t' : ∀ p : Fin (unaryTransfer.toPhased.toTM.tapeLength L),
      c4.tape p = if (p : Nat) = opBase + d + j then true else c.tape p := by
    intro p
    rw [hc4, h4t, hwf3, h3t, h2t']
  -- φ2 erases the source head
  obtain ⟨h5p, h5h, h5t⟩ := unaryTransfer_step_phi2 c4
    (i := c4.state.fst) (s := c4.state.snd) h4p rfl
  have hb4bnd : (c4.head : Nat) + 1 < unaryTransfer.toPhased.toTM.tapeLength L := by omega
  set c5 := TM.stepConfig (M := unaryTransfer.toPhased.toTM) c4 with hc5
  have h5h' : (c5.head : Nat) = opBase + d + j + γ + 1 := by
    rw [hc5, h5h]
    simp only [Configuration.moveHead, dif_pos hb4bnd]
    omega
  have h5t' : ∀ p : Fin (unaryTransfer.toPhased.toTM.tapeLength L),
      c5.tape p = if (p : Nat) = opBase + d + γ + j then false
        else if (p : Nat) = opBase + d + j then true else c.tape p := by
    intro p
    rw [hc5, h5t]
    by_cases hp : p = c4.head
    · subst hp
      have hv : ((c4.head : Fin _) : Nat) = opBase + d + γ + j := by omega
      rw [if_pos hv]
      simp [Configuration.write]
    · have hpv : (p : Nat) ≠ opBase + d + γ + j := by
        intro hv; exact hp (Fin.ext (by omega))
      rw [if_neg hpv]
      have hw : (c4.write c4.head false) p = c4.tape p := by
        simp [Configuration.write, hp]
      rw [hw, h4t']
  -- φ3 peeks the next source unit (a 1, since j+1 < m)
  have hb5 : c5.tape c5.head = true := by
    rw [h5t', if_neg (by omega : ¬ ((c5.head : Fin _) : Nat) = opBase + d + γ + j),
      if_neg (by omega : ¬ ((c5.head : Fin _) : Nat) = opBase + d + j)]
    exact hsrc c5.head (by omega) (by omega)
  obtain ⟨h6p, h6h, h6t⟩ := unaryTransfer_step_phi3_one c5
    (i := c5.state.fst) (s := c5.state.snd) h5p rfl hb5
  set c6 := TM.stepConfig (M := unaryTransfer.toPhased.toTM) c5 with hc6
  have h6h' : (c6.head : Nat) = opBase + d + j + γ := by
    rw [hc6, h6h, Configuration.moveHead_left_val_of_pos c5 (by omega)]
    omega
  have hwf5 : c5.write c5.head true = c5.tape := by
    rw [← hb5]; exact write_self_eq c5
  have h6t' : ∀ p : Fin (unaryTransfer.toPhased.toTM.tapeLength L),
      c6.tape p = if (p : Nat) = opBase + d + γ + j then false
        else if (p : Nat) = opBase + d + j then true else c.tape p := by
    intro p
    rw [hc6, h6t, hwf5, h5t']
  -- φ4 scans the γ gap zeros leftward (incl. the just-erased source head)
  obtain ⟨h7p, h7h, h7t⟩ := unaryTransfer_run_phi4_scan c6 h6p γ
    (by omega)
    (fun p hp1 hp2 => by
      rw [h6t']
      by_cases hpe : (p : Nat) = opBase + d + γ + j
      · rw [if_pos hpe]
      · rw [if_neg hpe, if_neg (by omega : ¬ (p : Nat) = opBase + d + j)]
        exact hgap p (by omega) (by omega))
  set c7 := TM.runConfig (M := unaryTransfer.toPhased.toTM) c6 γ with hc7
  have h7h' : (c7.head : Nat) = opBase + d + j := by omega
  -- φ4 hits the appended destination unit
  have hb7 : c7.tape c7.head = true := by
    rw [h7t, h6t', if_neg (by omega : ¬ ((c7.head : Fin _) : Nat) = opBase + d + γ + j),
      if_pos (by omega : ((c7.head : Fin _) : Nat) = opBase + d + j)]
  obtain ⟨h8p, h8h, h8t⟩ := unaryTransfer_step_phi4_one c7
    (i := c7.state.fst) (s := c7.state.snd) h7p rfl hb7
  set c8 := TM.stepConfig (M := unaryTransfer.toPhased.toTM) c7 with hc8
  have h8h' : (c8.head : Nat) = opBase + d + j := by
    rw [hc8, h8h, Configuration.moveHead_stay]; omega
  have hwf7 : c7.write c7.head true = c7.tape := by
    rw [← hb7]; exact write_self_eq c7
  have h8t' : ∀ p : Fin (unaryTransfer.toPhased.toTM.tapeLength L),
      c8.tape p = if (p : Nat) = opBase + d + γ + j then false
        else if (p : Nat) = opBase + d + j then true else c.tape p := by
    intro p
    rw [hc8, h8t, hwf7, h7t, h6t']
  -- φ5 walks the d+j+1 destination ones leftward
  obtain ⟨h9p, h9h, h9t⟩ := unaryTransfer_run_phi5_walk c8 h8p (d + j + 1)
    (by omega)
    (fun p hp1 hp2 => by
      rw [h8t', if_neg (by omega : ¬ (p : Nat) = opBase + d + γ + j)]
      by_cases h2 : (p : Nat) = opBase + d + j
      · rw [if_pos h2]
      · rw [if_neg h2]
        exact hdst p (by omega) (by omega))
  set c9 := TM.runConfig (M := unaryTransfer.toPhased.toTM) c8 (d + j + 1) with hc9
  have h9h' : (c9.head : Nat) = opBase - 1 := by omega
  -- φ5 stops on the home delimiter
  have hb9 : c9.tape c9.head = false := by
    rw [h9t, h8t', if_neg (by omega : ¬ ((c9.head : Fin _) : Nat) = opBase + d + γ + j),
      if_neg (by omega : ¬ ((c9.head : Fin _) : Nat) = opBase + d + j)]
    exact hdelim c9.head (by omega)
  obtain ⟨h10p, h10h, h10t⟩ := unaryTransfer_step_phi5_zero c9
    (i := c9.state.fst) (s := c9.state.snd) h9p rfl hb9
  set c10 := TM.stepConfig (M := unaryTransfer.toPhased.toTM) c9 with hc10
  have h10h' : (c10.head : Nat) = opBase - 1 := by
    rw [hc10, h10h, Configuration.moveHead_stay]; omega
  have hwf9 : c9.write c9.head false = c9.tape := by
    rw [← hb9]; exact write_self_eq c9
  have h10t' : ∀ p : Fin (unaryTransfer.toPhased.toTM.tapeLength L),
      c10.tape p = if (p : Nat) = opBase + d + γ + j then false
        else if (p : Nat) = opBase + d + j then true else c.tape p := by
    intro p
    rw [hc10, h10t, hwf9, h9t, h8t']
  -- φ6 re-homes
  obtain ⟨h11p, h11h, h11t⟩ := unaryTransfer_step_phi6 c10
    (i := c10.state.fst) (s := c10.state.snd) h10p rfl
  have hb10bnd : (c10.head : Nat) + 1 < unaryTransfer.toPhased.toTM.tapeLength L := by omega
  set c11 := TM.stepConfig (M := unaryTransfer.toPhased.toTM) c10 with hc11
  have h11h' : (c11.head : Nat) = opBase := by
    rw [hc11, h11h]
    simp only [Configuration.moveHead, dif_pos hb10bnd]
    omega
  have h11t' : ∀ p : Fin (unaryTransfer.toPhased.toTM.tapeLength L),
      c11.tape p = if (p : Nat) = opBase + d + γ + j then false
        else if (p : Nat) = opBase + d + j then true else c.tape p := by
    intro p
    rw [hc11, h11t, write_self_eq, h10t']
  -- φ7 back-edge re-enters φ0
  obtain ⟨h12p, h12h, h12t⟩ := unaryTransfer_step_phi7 c11
    (i := c11.state.fst) (s := c11.state.snd) h11p rfl
  set c12 := TM.stepConfig (M := unaryTransfer.toPhased.toTM) c11 with hc12
  have h12h' : (c12.head : Nat) = opBase := by
    rw [hc12, h12h, Configuration.moveHead_stay]; omega
  have h12t' : ∀ p : Fin (unaryTransfer.toPhased.toTM.tapeLength L),
      c12.tape p = if (p : Nat) = opBase + d + γ + j then false
        else if (p : Nat) = opBase + d + j then true else c.tape p := by
    intro p
    rw [hc12, h12t, write_self_eq, h11t']
  -- chain the 12 segments
  have htotal : TM.runConfig (M := unaryTransfer.toPhased.toTM) c (2 * (d + j) + 2 * γ + 8)
      = c12 := by
    have e : 2 * (d + j) + 2 * γ + 8
        = (d + j) + (1 + (g1 + (1 + (1 + (1 + (γ + (1 + ((d + j + 1) + (1 + (1 + 1)))))))))) := by
      omega
    rw [e, TM.runConfig_add, ← hc1,
      TM.runConfig_add, unaryTransfer_runConfig_one, ← hc2,
      TM.runConfig_add, ← hc3,
      TM.runConfig_add, unaryTransfer_runConfig_one, ← hc4,
      TM.runConfig_add, unaryTransfer_runConfig_one, ← hc5,
      TM.runConfig_add, unaryTransfer_runConfig_one, ← hc6,
      TM.runConfig_add, ← hc7,
      TM.runConfig_add, unaryTransfer_runConfig_one, ← hc8,
      TM.runConfig_add, ← hc9,
      TM.runConfig_add, unaryTransfer_runConfig_one, ← hc10,
      TM.runConfig_succ, unaryTransfer_runConfig_one, ← hc11, ← hc12]
  rw [htotal]
  constructor
  · exact {
      hphase := h12p
      hhead := h12h'
      hopPos := hopPos
      hg1 := hg1
      hjm := by omega
      hbound := hbound
      hdelim := fun p hp => by
        rw [h12t', if_neg (by omega), if_neg (by omega)]
        exact hdelim p hp
      hdst := fun p hp1 hp2 => by
        rw [h12t']
        by_cases h2 : (p : Nat) = opBase + d + j
        · rw [if_neg (by omega), if_pos h2]
        · rw [if_neg (by omega), if_neg h2]
          exact hdst p hp1 (by omega)
      hgap := fun p hp1 hp2 => by
        rw [h12t']
        by_cases he : (p : Nat) = opBase + d + γ + j
        · rw [if_pos he]
        · rw [if_neg he, if_neg (by omega)]
          exact hgap p (by omega) (by omega)
      hsrc := fun p hp1 hp2 => by
        rw [h12t', if_neg (by omega), if_neg (by omega)]
        exact hsrc p (by omega) hp2
      hterm := fun p hp => by
        rw [h12t', if_neg (by omega), if_neg (by omega)]
        exact hterm p hp }
  · intro p hp
    rw [h12t', if_neg (by omega), if_neg (by omega)]

/-- **The last pass** (`j + 1 = m`): exactly `d + j + γ + 3` steps later the loop is **in the sink φ8**
with the head on the source terminator, the destination block complete (`1^(d+m)`), the former
gap+source zone all `0`, and the tape outside `[opBase, opBase+d+γ+m]` untouched. -/
theorem unaryTransfer_pass_last {L : Nat}
    (c : Configuration (M := unaryTransfer.toPhased.toTM) L)
    (opBase d j γ m : Nat) (hlay : TransferLayout c opBase d j γ m) (hjm1 : j + 1 = m) :
    (((TM.runConfig (M := unaryTransfer.toPhased.toTM) c (d + j + γ + 3)).state).fst : Nat) = 8
    ∧ ((TM.runConfig (M := unaryTransfer.toPhased.toTM) c (d + j + γ + 3)).head : Nat)
        = opBase + d + γ + m
    ∧ (∀ p : Fin (unaryTransfer.toPhased.toTM.tapeLength L),
        opBase ≤ (p : Nat) → (p : Nat) < opBase + d + m →
        (TM.runConfig (M := unaryTransfer.toPhased.toTM) c (d + j + γ + 3)).tape p = true)
    ∧ (∀ p : Fin (unaryTransfer.toPhased.toTM.tapeLength L),
        opBase + d + m ≤ (p : Nat) → (p : Nat) ≤ opBase + d + γ + m →
        (TM.runConfig (M := unaryTransfer.toPhased.toTM) c (d + j + γ + 3)).tape p = false)
    ∧ (∀ p : Fin (unaryTransfer.toPhased.toTM.tapeLength L),
        ((p : Nat) < opBase ∨ opBase + d + γ + m < (p : Nat)) →
        (TM.runConfig (M := unaryTransfer.toPhased.toTM) c (d + j + γ + 3)).tape p = c.tape p) := by
  obtain ⟨hphase, hhead, hopPos, hg1, hjm, hbound, hdelim, hdst, hgap, hsrc, hterm⟩ := hlay
  obtain ⟨g1, hg⟩ : ∃ g1, γ = g1 + 1 := ⟨γ - 1, by omega⟩
  -- φ0 walk over the d+j destination ones
  obtain ⟨h1p, h1h, h1t⟩ := unaryTransfer_run_phi0_walk c hphase (d + j)
    (by omega) (fun p hp1 hp2 => hdst p (by omega) (by omega))
  set c1 := TM.runConfig (M := unaryTransfer.toPhased.toTM) c (d + j) with hc1
  -- φ0 append at the frontier (gap cell)
  have hb1 : c1.tape c1.head = false := by
    rw [h1t]; exact hgap c1.head (by omega) (by omega)
  obtain ⟨h2p, h2h, h2t⟩ := unaryTransfer_step_phi0_zero c1
    (i := c1.state.fst) (s := c1.state.snd) h1p rfl hb1
  have hb1bnd : (c1.head : Nat) + 1 < unaryTransfer.toPhased.toTM.tapeLength L := by omega
  set c2 := TM.stepConfig (M := unaryTransfer.toPhased.toTM) c1 with hc2
  have h2h' : (c2.head : Nat) = opBase + d + j + 1 := by
    rw [hc2, h2h]
    simp only [Configuration.moveHead, dif_pos hb1bnd]
    omega
  have h2t' : ∀ p : Fin (unaryTransfer.toPhased.toTM.tapeLength L),
      c2.tape p = if (p : Nat) = opBase + d + j then true else c.tape p := by
    intro p
    rw [hc2, h2t]
    by_cases hp : p = c1.head
    · subst hp
      have hv : ((c1.head : Fin _) : Nat) = opBase + d + j := by omega
      rw [if_pos hv]
      simp [Configuration.write]
    · have hpv : (p : Nat) ≠ opBase + d + j := by
        intro hv; exact hp (Fin.ext (by omega))
      rw [if_neg hpv]
      have hw : (c1.write c1.head true) p = c1.tape p := by
        simp [Configuration.write, hp]
      rw [hw, h1t]
  -- φ1 scan across the remaining γ−1 gap zeros
  obtain ⟨h3p, h3h, h3t⟩ := unaryTransfer_run_phi1_scan c2 h2p g1
    (by omega)
    (fun p hp1 hp2 => by
      rw [h2t', if_neg (by omega : ¬ (p : Nat) = opBase + d + j)]
      exact hgap p (by omega) (by omega))
  set c3 := TM.runConfig (M := unaryTransfer.toPhased.toTM) c2 g1 with hc3
  have h3h' : (c3.head : Nat) = opBase + d + j + γ := by omega
  -- φ1 hits the source head (the last remaining unit)
  have hb3 : c3.tape c3.head = true := by
    rw [h3t, h2t', if_neg (by omega : ¬ ((c3.head : Fin _) : Nat) = opBase + d + j)]
    exact hsrc c3.head (by omega) (by omega)
  obtain ⟨h4p, h4h, h4t⟩ := unaryTransfer_step_phi1_one c3
    (i := c3.state.fst) (s := c3.state.snd) h3p rfl hb3
  set c4 := TM.stepConfig (M := unaryTransfer.toPhased.toTM) c3 with hc4
  have h4h' : (c4.head : Nat) = opBase + d + j + γ := by
    rw [hc4, h4h, Configuration.moveHead_stay]; omega
  have hwf3 : c3.write c3.head true = c3.tape := by
    rw [← hb3]; exact write_self_eq c3
  have h4t' : ∀ p : Fin (unaryTransfer.toPhased.toTM.tapeLength L),
      c4.tape p = if (p : Nat) = opBase + d + j then true else c.tape p := by
    intro p
    rw [hc4, h4t, hwf3, h3t, h2t']
  -- φ2 erases the last source unit
  obtain ⟨h5p, h5h, h5t⟩ := unaryTransfer_step_phi2 c4
    (i := c4.state.fst) (s := c4.state.snd) h4p rfl
  have hb4bnd : (c4.head : Nat) + 1 < unaryTransfer.toPhased.toTM.tapeLength L := by omega
  set c5 := TM.stepConfig (M := unaryTransfer.toPhased.toTM) c4 with hc5
  have h5h' : (c5.head : Nat) = opBase + d + j + γ + 1 := by
    rw [hc5, h5h]
    simp only [Configuration.moveHead, dif_pos hb4bnd]
    omega
  have h5t' : ∀ p : Fin (unaryTransfer.toPhased.toTM.tapeLength L),
      c5.tape p = if (p : Nat) = opBase + d + γ + j then false
        else if (p : Nat) = opBase + d + j then true else c.tape p := by
    intro p
    rw [hc5, h5t]
    by_cases hp : p = c4.head
    · subst hp
      have hv : ((c4.head : Fin _) : Nat) = opBase + d + γ + j := by omega
      rw [if_pos hv]
      simp [Configuration.write]
    · have hpv : (p : Nat) ≠ opBase + d + γ + j := by
        intro hv; exact hp (Fin.ext (by omega))
      rw [if_neg hpv]
      have hw : (c4.write c4.head false) p = c4.tape p := by
        simp [Configuration.write, hp]
      rw [hw, h4t']
  -- φ3 peeks the source terminator (a 0: the source is exhausted) → sink φ8
  have hb5 : c5.tape c5.head = false := by
    rw [h5t', if_neg (by omega : ¬ ((c5.head : Fin _) : Nat) = opBase + d + γ + j),
      if_neg (by omega : ¬ ((c5.head : Fin _) : Nat) = opBase + d + j)]
    exact hterm c5.head (by omega)
  obtain ⟨h6p, h6h, h6t⟩ := unaryTransfer_step_phi3_zero c5
    (i := c5.state.fst) (s := c5.state.snd) h5p rfl hb5
  set c6 := TM.stepConfig (M := unaryTransfer.toPhased.toTM) c5 with hc6
  have h6h' : (c6.head : Nat) = opBase + d + γ + m := by
    rw [hc6, h6h, Configuration.moveHead_stay]; omega
  have hwf5 : c5.write c5.head false = c5.tape := by
    rw [← hb5]; exact write_self_eq c5
  have h6t' : ∀ p : Fin (unaryTransfer.toPhased.toTM.tapeLength L),
      c6.tape p = if (p : Nat) = opBase + d + γ + j then false
        else if (p : Nat) = opBase + d + j then true else c.tape p := by
    intro p
    rw [hc6, h6t, hwf5, h5t']
  -- chain the 6 segments
  have htotal : TM.runConfig (M := unaryTransfer.toPhased.toTM) c (d + j + γ + 3) = c6 := by
    have e : d + j + γ + 3 = (d + j) + (1 + (g1 + (1 + (1 + 1)))) := by omega
    rw [e, TM.runConfig_add, ← hc1,
      TM.runConfig_add, unaryTransfer_runConfig_one, ← hc2,
      TM.runConfig_add, ← hc3,
      TM.runConfig_add, unaryTransfer_runConfig_one, ← hc4,
      TM.runConfig_succ, unaryTransfer_runConfig_one, ← hc5, ← hc6]
  rw [htotal]
  refine ⟨h6p, h6h', ?_, ?_, ?_⟩
  · intro p hp1 hp2
    rw [h6t']
    by_cases h2 : (p : Nat) = opBase + d + j
    · rw [if_neg (by omega), if_pos h2]
    · rw [if_neg (by omega), if_neg h2]
      exact hdst p hp1 (by omega)
  · intro p hp1 hp2
    rw [h6t']
    by_cases he : (p : Nat) = opBase + d + γ + j
    · rw [if_pos he]
    · rw [if_neg he, if_neg (by omega)]
      by_cases hin : (p : Nat) < opBase + d + γ + j
      · exact hgap p (by omega) (by omega)
      · exact hterm p (by omega)
  · intro p hp
    rw [h6t', if_neg (by omega), if_neg (by omega)]

/-- **The transfer headline.**  From any `TransferLayout` with at least one source unit, the loop reaches
the sink φ8 within `(m − j) · (2(d+m) + 2γ + 8)` steps, with the head on the source terminator, the
destination block complete (`1^(d+m)`), the former gap+source zone all `0`, and the tape outside
`[opBase, opBase+d+γ+m]` untouched. -/
theorem unaryTransfer_transfers {L : Nat}
    (c : Configuration (M := unaryTransfer.toPhased.toTM) L)
    (opBase d j γ m : Nat) (hlay : TransferLayout c opBase d j γ m) (hjm : j < m) :
    ∃ t ≤ (m - j) * (2 * (d + m) + 2 * γ + 8),
      (((TM.runConfig (M := unaryTransfer.toPhased.toTM) c t).state).fst : Nat) = 8
      ∧ ((TM.runConfig (M := unaryTransfer.toPhased.toTM) c t).head : Nat) = opBase + d + γ + m
      ∧ (∀ p : Fin (unaryTransfer.toPhased.toTM.tapeLength L),
          opBase ≤ (p : Nat) → (p : Nat) < opBase + d + m →
          (TM.runConfig (M := unaryTransfer.toPhased.toTM) c t).tape p = true)
      ∧ (∀ p : Fin (unaryTransfer.toPhased.toTM.tapeLength L),
          opBase + d + m ≤ (p : Nat) → (p : Nat) ≤ opBase + d + γ + m →
          (TM.runConfig (M := unaryTransfer.toPhased.toTM) c t).tape p = false)
      ∧ (∀ p : Fin (unaryTransfer.toPhased.toTM.tapeLength L),
          ((p : Nat) < opBase ∨ opBase + d + γ + m < (p : Nat)) →
          (TM.runConfig (M := unaryTransfer.toPhased.toTM) c t).tape p = c.tape p) := by
  -- strong induction on the remaining units m − j
  suffices H : ∀ n (c : Configuration (M := unaryTransfer.toPhased.toTM) L) (j : Nat),
      TransferLayout c opBase d j γ m → j < m → m - j = n →
      ∃ t ≤ (m - j) * (2 * (d + m) + 2 * γ + 8),
        (((TM.runConfig (M := unaryTransfer.toPhased.toTM) c t).state).fst : Nat) = 8
        ∧ ((TM.runConfig (M := unaryTransfer.toPhased.toTM) c t).head : Nat) = opBase + d + γ + m
        ∧ (∀ p : Fin (unaryTransfer.toPhased.toTM.tapeLength L),
            opBase ≤ (p : Nat) → (p : Nat) < opBase + d + m →
            (TM.runConfig (M := unaryTransfer.toPhased.toTM) c t).tape p = true)
        ∧ (∀ p : Fin (unaryTransfer.toPhased.toTM.tapeLength L),
            opBase + d + m ≤ (p : Nat) → (p : Nat) ≤ opBase + d + γ + m →
            (TM.runConfig (M := unaryTransfer.toPhased.toTM) c t).tape p = false)
        ∧ (∀ p : Fin (unaryTransfer.toPhased.toTM.tapeLength L),
            ((p : Nat) < opBase ∨ opBase + d + γ + m < (p : Nat)) →
            (TM.runConfig (M := unaryTransfer.toPhased.toTM) c t).tape p = c.tape p) by
    exact H (m - j) c j hlay hjm rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c j hlay hjm hn
    by_cases hlast : j + 1 = m
    · -- the last pass: straight to the sink
      obtain ⟨hp8, hhd, hdst', hzero', hout'⟩ := unaryTransfer_pass_last c opBase d j γ m hlay hlast
      have hmj : m - j = 1 := by omega
      refine ⟨d + j + γ + 3, by rw [hmj, one_mul]; omega, hp8, hhd, hdst', hzero', hout'⟩
    · -- a more-pass, then the induction hypothesis
      have hjm1 : j + 1 < m := by omega
      obtain ⟨hlay', hout1⟩ := unaryTransfer_pass_more c opBase d j γ m hlay hjm1
      set c' := TM.runConfig (M := unaryTransfer.toPhased.toTM) c (2 * (d + j) + 2 * γ + 8)
        with hc'
      obtain ⟨t', ht'le, hp8, hhd, hdst', hzero', hout'⟩ :=
        ih (m - (j + 1)) (by omega) c' (j + 1) hlay' hjm1 rfl
      refine ⟨(2 * (d + j) + 2 * γ + 8) + t', ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have h2 : m - j = (m - (j + 1)) + 1 := by omega
        have hs : ((m - (j + 1)) + 1) * (2 * (d + m) + 2 * γ + 8)
            = (m - (j + 1)) * (2 * (d + m) + 2 * γ + 8) + (2 * (d + m) + 2 * γ + 8) :=
          Nat.succ_mul _ _
        rw [h2, hs]
        omega
      · rw [TM.runConfig_add, ← hc']; exact hp8
      · rw [TM.runConfig_add, ← hc']; exact hhd
      · intro p hp1 hp2
        rw [TM.runConfig_add, ← hc']; exact hdst' p hp1 hp2
      · intro p hp1 hp2
        rw [TM.runConfig_add, ← hc']; exact hzero' p hp1 hp2
      · intro p hp
        rw [TM.runConfig_add, ← hc']
        rw [hout' p hp]
        exact hout1 p (by omega)

end ContractExpansion
end Frontier
end Pnp4
