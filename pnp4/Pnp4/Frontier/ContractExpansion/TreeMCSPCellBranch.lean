import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM

/-!
# `cellBranch` — the single-cell routing atom (NP-verifier track — D2t-3c-δ groundwork)

`cellBranch` reads the cell under the head **once** and routes to one of two distinct terminal phases:
phase `1` (the accept phase) iff the cell is `1`, phase `2` iff the cell is `0`.  It never moves the head
and never writes.  This is the marker-free routing atom the binary→unary loop's zero-test (`bZeroTest`,
D2t-3c-δ) needs:

* applied to a `B`-cell, "`1` ⇒ phase `1`" is the *found-a-set-bit* route (`B > 0`);
* applied to the unary width counter's leftmost cell, "`0` ⇒ phase `2`" is the **marker-free unary
  zero-test "leftmost cell `= 0`"** (the width counter is *exhausted* ⇒ all `w` scanned cells of `B` were
  `0` ⇒ `B = 0`), per `TM_VERIFIER_STRATEGY.md` §12 (the width-counter resolution of the documented
  zero-test crux).

Unlike `gammaSelfLoopScan` (which self-loops over `0`s), `cellBranch` takes **exactly one step** and has
**two** terminal phases, so it is a pure local branch — the building block for the zero-test's routing
(it does not itself perform the lockstep scan).  **Progress classification: Infrastructure** — control
toolkit toward the NP-membership leg; builds no verifier and proves no separation.  All surfaces carry
only the standard `[propext, Classical.choice, Quot.sound]` triple.  **No `P ≠ NP` claim.**
-/

/-- Single-cell branch: phase `0` reads the head cell and jumps to phase `1` (accept) if it is `1`, or to
phase `2` if it is `0`; both terminal phases idle (stay).  The head never moves and nothing is written. -/
def cellBranch : ConstStatePhasedProgram Unit where
  numPhases := 3
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨1, by omega⟩
  acceptState := ()
  transition := fun i _ b =>
    if i.val = 0 then
      if b then (⟨1, by omega⟩, (), b, Move.stay)
      else (⟨2, by omega⟩, (), b, Move.stay)
    else
      (i, (), b, Move.stay)
  timeBound := fun _ => 1

@[simp] theorem cellBranch_numPhases : cellBranch.numPhases = 3 := rfl

@[simp] theorem cellBranch_startPhase_val : (cellBranch.startPhase : Nat) = 0 := rfl

@[simp] theorem cellBranch_acceptPhase_val : (cellBranch.acceptPhase : Nat) = 1 := rfl

@[simp] theorem cellBranch_timeBound (n : Nat) : cellBranch.timeBound n = 1 := rfl

/-- `cellBranch` never moves the head left: every branch and both idle transitions stay. -/
theorem cellBranch_transition_move (i : Fin 3) (s : Unit) (b : Bool) :
    (cellBranch.transition i s b).2.2.2 ≠ Move.left := by
  unfold cellBranch
  dsimp only
  split_ifs <;> simp

/-- The compiled `cellBranch` TM never moves its head left (lifts the transition fact through
`toPhased`/`toTM`; composes via `seqList_neverMovesLeft`). -/
theorem cellBranch_neverMovesLeft :
    TMNeverMovesLeft (cellBranch.toPhased.toTM) := by
  intro st b
  obtain ⟨i, s⟩ := st
  exact cellBranch_transition_move i s b

/-! ### Single-step lemmas

From the start phase `0`, one step routes by the scanned bit: a `1` lands in the accept phase `1`, a `0`
lands in phase `2`; in both cases the head and tape are unchanged. -/

/-- True branch (phase `0`, bit `1`): the phase jumps to the accept phase `1`. -/
theorem cellBranch_stepConfig_true_phase {L : Nat}
    (c : Configuration (M := cellBranch.toPhased.toTM) L)
    {i : Fin 3} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := cellBranch.toPhased.toTM) c).state).fst.val = 1 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, cellBranch, hi, hbit]

/-- False branch (phase `0`, bit `0`): the phase jumps to phase `2`. -/
theorem cellBranch_stepConfig_false_phase {L : Nat}
    (c : Configuration (M := cellBranch.toPhased.toTM) L)
    {i : Fin 3} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := cellBranch.toPhased.toTM) c).state).fst.val = 2 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, cellBranch, hi, hbit]

/-- Branch step (phase `0`): the head is unchanged (the branch stays put). -/
theorem cellBranch_stepConfig_head {L : Nat}
    (c : Configuration (M := cellBranch.toPhased.toTM) L)
    {i : Fin 3} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := cellBranch.toPhased.toTM) c).head = c.head := by
  have hmove : (TM.stepConfig (M := cellBranch.toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.stay := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    by_cases hbit : c.tape c.head = true
    · simp [ConstStatePhasedProgram.toPhased, cellBranch, hi, hbit]
    · simp [ConstStatePhasedProgram.toPhased, cellBranch, hi,
        (by simpa using hbit : c.tape c.head = false)]
  rw [hmove]; simp [Configuration.moveHead]

/-- Branch step (phase `0`): the tape is unchanged (the scanned bit is written back). -/
theorem cellBranch_stepConfig_tape {L : Nat}
    (c : Configuration (M := cellBranch.toPhased.toTM) L)
    {i : Fin 3} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := cellBranch.toPhased.toTM) c).tape = c.tape := by
  have hwrite : (TM.stepConfig (M := cellBranch.toPhased.toTM) c).tape
      = c.write c.head (c.tape c.head) := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    by_cases hbit : c.tape c.head = true
    · simp [ConstStatePhasedProgram.toPhased, cellBranch, hi, hbit]
    · simp [ConstStatePhasedProgram.toPhased, cellBranch, hi,
        (by simpa using hbit : c.tape c.head = false)]
  rw [hwrite]; funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-- One-step run behaviour: from the start phase `0`, after one step the phase is `1` iff the scanned
cell was `1` (else `2`), with the head and tape unchanged.  This is the routing fact the zero-test's
lockstep consumes at each cell. -/
theorem cellBranch_runConfig_one {L : Nat}
    (c : Configuration (M := cellBranch.toPhased.toTM) L)
    (hphase : (c.state.fst : Nat) = 0) :
    (((TM.runConfig (M := cellBranch.toPhased.toTM) c 1).state).fst : Nat)
        = (if c.tape c.head = true then 1 else 2)
      ∧ (TM.runConfig (M := cellBranch.toPhased.toTM) c 1).head = c.head
      ∧ (TM.runConfig (M := cellBranch.toPhased.toTM) c 1).tape = c.tape := by
  rw [TM.runConfig_one]
  refine ⟨?_, ?_, ?_⟩
  · by_cases hbit : c.tape c.head = true
    · rw [if_pos hbit]
      exact cellBranch_stepConfig_true_phase c (i := c.state.fst) (s := c.state.snd) hphase rfl hbit
    · rw [if_neg hbit]
      exact cellBranch_stepConfig_false_phase c (i := c.state.fst) (s := c.state.snd) hphase rfl
        (by simpa using hbit)
  · exact cellBranch_stepConfig_head c (i := c.state.fst) (s := c.state.snd) hphase rfl
  · exact cellBranch_stepConfig_tape c (i := c.state.fst) (s := c.state.snd) hphase rfl

end ContractExpansion
end Frontier
end Pnp4
