import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgramAccepts
import Complexity.TMVerifier.TuringToolkit.CombineAtOffset

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace TM
namespace ConstStatePhasedProgram

open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.CombineAtOffset

/-!
## Fixed conditional-accept terminal program

`acceptIfCellCS Δflag` reads the cell at offset `Δflag`, restores the
head, and leaves the tape unchanged.  Both bit values take exactly
`2 * Δflag + 3` steps.  The final phase is the declared accept phase for
both branches, but only a `true` flag produces the full accepting state;
`false` produces the distinct terminal local state `(false, false)`.

This program is intended to be the explicit right operand of the final
`ConstStatePhasedProgram.seq`.  It must not be hidden in `seqList`: that fold
appends `idleCS`, whose boundary resets the local state and would erase the
conditional result.  The predecessor tape-length comparison (or future
padding construction), and identification of the composite `initialConfig`
with the embedded predecessor `initialConfig`, are separate composition
obligations.
-/

/-- A fixed finite-control program that accepts exactly when the cell at
offset `Δflag` from the starting head is true.

The implementation specializes the already verified two-read combiner to
read the same cell twice and write their conjunction back.  Since
`b && b = b`, the write is observationally a no-op.  Only the declared local
accept state differs from the underlying combiner. -/
def acceptIfCellCS (Δflag : Nat) : ConstStatePhasedProgram (Bool × Bool) :=
  { combineAtOffsetCS Δflag Δflag Δflag le_rfl le_rfl (fun a b => a && b) with
    acceptState := (true, true) }

@[simp] theorem acceptIfCellCS_numPhases (Δflag : Nat) :
    (acceptIfCellCS Δflag).numPhases = 2 * Δflag + 4 := rfl

@[simp] theorem acceptIfCellCS_timeBound (Δflag n : Nat) :
    (acceptIfCellCS Δflag).timeBound n = 2 * Δflag + 3 := rfl

@[simp] theorem acceptIfCellCS_startPhase_val (Δflag : Nat) :
    (acceptIfCellCS Δflag).startPhase.val = 0 := rfl

@[simp] theorem acceptIfCellCS_startState (Δflag : Nat) :
    (acceptIfCellCS Δflag).startState = (false, false) := rfl

@[simp] theorem acceptIfCellCS_acceptPhase_val (Δflag : Nat) :
    (acceptIfCellCS Δflag).acceptPhase.val = 2 * Δflag + 3 := rfl

@[simp] theorem acceptIfCellCS_acceptState (Δflag : Nat) :
    (acceptIfCellCS Δflag).acceptState = (true, true) := rfl

/-- For the standalone program, or when it is the right operand of `seq`, the
terminal phase is absorbing at the transition level.  In particular, the
false result `(false, false)` is a nonaccepting sink, while the true result
`(true, true)` is the unique full accepting state. -/
theorem acceptIfCellCS_terminal_transition (Δflag : Nat)
    (q : Bool × Bool) (scan : Bool) :
    (acceptIfCellCS Δflag).transition
        (acceptIfCellCS Δflag).acceptPhase q scan =
      ((acceptIfCellCS Δflag).acceptPhase, q, scan, Move.stay) := by
  have h1 : ¬ 2 * Δflag + 3 < Δflag := by omega
  have h2 : ¬ 2 * Δflag + 3 = Δflag := by omega
  have h3 : ¬ 2 * Δflag + 3 < Δflag + 1 := by omega
  have h4 : ¬ 2 * Δflag + 3 = Δflag + 1 := by omega
  have h5 : ¬ 2 * Δflag + 3 < Δflag + 2 := by omega
  have h6 : ¬ 2 * Δflag + 3 = Δflag + 2 := by omega
  simp [acceptIfCellCS, combineAtOffsetCS, h1, h2, h3, h4, h5, h6]

/-- The configuration type of `acceptIfCellCS` is value-for-value the same
as that of its underlying combiner; only the machine's designated accept
value differs. -/
def castAcceptIfCellConfig (Δflag : Nat) {n : Nat}
    (c : Configuration (M := (acceptIfCellCS Δflag).toPhased.toTM) n) :
    Configuration
      (M := (combineAtOffsetCS Δflag Δflag Δflag le_rfl le_rfl
        (fun a b => a && b)).toPhased.toTM) n :=
  castConfig
    (T1 := (acceptIfCellCS Δflag).toPhased.toTM)
    (T2 := (combineAtOffsetCS Δflag Δflag Δflag le_rfl le_rfl
      (fun a b => a && b)).toPhased.toTM)
    rfl rfl c

@[simp] theorem castAcceptIfCellConfig_state (Δflag : Nat) {n : Nat}
    (c : Configuration (M := (acceptIfCellCS Δflag).toPhased.toTM) n) :
    (castAcceptIfCellConfig Δflag c).state = c.state := rfl

@[simp] theorem castAcceptIfCellConfig_head (Δflag : Nat) {n : Nat}
    (c : Configuration (M := (acceptIfCellCS Δflag).toPhased.toTM) n) :
    (castAcceptIfCellConfig Δflag c).head = c.head := rfl

@[simp] theorem castAcceptIfCellConfig_tape (Δflag : Nat) {n : Nat}
    (c : Configuration (M := (acceptIfCellCS Δflag).toPhased.toTM) n) :
    (castAcceptIfCellConfig Δflag c).tape = c.tape := rfl

/-- The cast commutes with one step because changing the declared accept
state does not change the transition function. -/
theorem castAcceptIfCellConfig_stepConfig (Δflag : Nat) {n : Nat}
    (c : Configuration (M := (acceptIfCellCS Δflag).toPhased.toTM) n) :
    castAcceptIfCellConfig Δflag
        (TM.stepConfig (M := (acceptIfCellCS Δflag).toPhased.toTM) c) =
      TM.stepConfig
        (M := (combineAtOffsetCS Δflag Δflag Δflag le_rfl le_rfl
          (fun a b => a && b)).toPhased.toTM)
        (castAcceptIfCellConfig Δflag c) := by
  rfl

/-- The value-preserving cast commutes with every finite run. -/
theorem castAcceptIfCellConfig_runConfig (Δflag : Nat) {n : Nat}
    (c : Configuration (M := (acceptIfCellCS Δflag).toPhased.toTM) n)
    (t : Nat) :
    castAcceptIfCellConfig Δflag
        (TM.runConfig (M := (acceptIfCellCS Δflag).toPhased.toTM) c t) =
      TM.runConfig
        (M := (combineAtOffsetCS Δflag Δflag Δflag le_rfl le_rfl
          (fun a b => a && b)).toPhased.toTM)
        (castAcceptIfCellConfig Δflag c) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [runConfig_succ, runConfig_succ, ← ih]
      exact castAcceptIfCellConfig_stepConfig Δflag _

/-- Exact run behavior from a ready configuration.  The theorem explicitly
requires the start phase, the full start local state, and the head bound needed
to prevent clamped right motion.  The `hstate` premise is inherited from the
current underlying combiner theorem: the two reads overwrite both local-state
bits, so the stated final semantics is independent of the initial local state. -/
theorem acceptIfCellCS_run_full (Δflag : Nat) {n : Nat}
    (c : Configuration (M := (acceptIfCellCS Δflag).toPhased.toTM) n)
    (hphase : c.state.fst.val = (acceptIfCellCS Δflag).startPhase.val)
    (hstate : c.state.snd = (acceptIfCellCS Δflag).startState)
    (hbound : c.head.val + Δflag <
      (acceptIfCellCS Δflag).toPhased.toTM.tapeLength n) :
    let b := c.tape ⟨c.head.val + Δflag, hbound⟩
    let cf := TM.runConfig
      (M := (acceptIfCellCS Δflag).toPhased.toTM) c
      ((acceptIfCellCS Δflag).timeBound n)
    cf.state =
        (⟨(acceptIfCellCS Δflag).acceptPhase, (b, b)⟩ :
          (acceptIfCellCS Δflag).toPhased.State) ∧
      cf.head = c.head ∧
      cf.tape = c.tape := by
  dsimp only
  let c' := castAcceptIfCellConfig Δflag c
  have hphase' : c'.state.fst.val = 0 := by simpa [c'] using hphase
  have hstate' : c'.state.snd = (false, false) := by simpa [c'] using hstate
  obtain ⟨hsrc1, hsrc2, hp, hs, hh, ht⟩ :=
    combineAtOffsetCS_run_full Δflag Δflag Δflag le_rfl le_rfl
      (fun a b => a && b) c' hphase' hstate' hbound
  let cf := TM.runConfig
    (M := (acceptIfCellCS Δflag).toPhased.toTM) c
    ((acceptIfCellCS Δflag).timeBound n)
  have hrun := castAcceptIfCellConfig_runConfig Δflag c
    ((acceptIfCellCS Δflag).timeBound n)
  have hphaseFinal : cf.state.fst = (acceptIfCellCS Δflag).acceptPhase := by
    apply Fin.ext
    rw [← castAcceptIfCellConfig_state Δflag cf, hrun]
    exact hp
  have hlocalFinal : cf.state.snd =
      (c.tape ⟨c.head.val + Δflag, hbound⟩,
       c.tape ⟨c.head.val + Δflag, hbound⟩) := by
    rw [← castAcceptIfCellConfig_state Δflag cf, hrun]
    simpa only [castAcceptIfCellConfig_tape, castAcceptIfCellConfig_head] using hs
  have hheadFinal : cf.head = c.head := by
    rw [← castAcceptIfCellConfig_head Δflag cf, hrun]
    simpa [c'] using hh
  refine ⟨?_, hheadFinal, ?_⟩
  · exact Sigma.ext hphaseFinal (by
      rw [hphaseFinal]
      exact heq_of_eq hlocalFinal)
  · have ht' : cf.tape = c.write ⟨c.head.val + Δflag, hbound⟩
        (c.tape ⟨c.head.val + Δflag, hbound⟩) := by
      rw [← castAcceptIfCellConfig_tape Δflag cf, hrun]
      simpa [c'] using ht
    rw [ht', BinaryCounter.write_self_eq]

private theorem acceptIfCellCS_stepConfig_terminal (Δflag : Nat) {n : Nat}
    (c : Configuration (M := (acceptIfCellCS Δflag).toPhased.toTM) n)
    (hphase : c.state.fst = (acceptIfCellCS Δflag).acceptPhase) :
    TM.stepConfig (M := (acceptIfCellCS Δflag).toPhased.toTM) c = c := by
  rcases c with ⟨⟨i, q⟩, head, tape⟩
  simp only at hphase
  subst i
  simp [TM.stepConfig, PhasedProgram.toTM, toPhased,
    acceptIfCellCS_terminal_transition]
  exact BinaryCounter.write_self_eq _ head

/-- Exact-clock stabilization from a ready configuration.  After the precise
`timeBound`-step arrival at the terminal phase, every additional `k` steps
leave the complete final configuration unchanged. -/
theorem acceptIfCellCS_runConfig_stabilizes (Δflag : Nat) {n : Nat}
    (c : Configuration (M := (acceptIfCellCS Δflag).toPhased.toTM) n)
    (hphase : c.state.fst.val = (acceptIfCellCS Δflag).startPhase.val)
    (hstate : c.state.snd = (acceptIfCellCS Δflag).startState)
    (hbound : c.head.val + Δflag <
      (acceptIfCellCS Δflag).toPhased.toTM.tapeLength n)
    (k : Nat) :
    TM.runConfig (M := (acceptIfCellCS Δflag).toPhased.toTM) c
        ((acceptIfCellCS Δflag).timeBound n + k) =
      TM.runConfig (M := (acceptIfCellCS Δflag).toPhased.toTM) c
        ((acceptIfCellCS Δflag).timeBound n) := by
  let cf := TM.runConfig (M := (acceptIfCellCS Δflag).toPhased.toTM) c
    ((acceptIfCellCS Δflag).timeBound n)
  obtain ⟨hrun, _, _⟩ := acceptIfCellCS_run_full Δflag c hphase hstate hbound
  have hterminal : cf.state.fst = (acceptIfCellCS Δflag).acceptPhase := by
    exact congrArg Sigma.fst hrun
  rw [runConfig_add]
  change TM.runConfig (M := (acceptIfCellCS Δflag).toPhased.toTM) cf k = cf
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [runConfig_succ, ih]
      exact acceptIfCellCS_stepConfig_terminal Δflag cf hterminal

/-- At the exact runtime, full accepting-state equality is equivalent to the
original flag cell being true. -/
theorem acceptIfCellCS_run_state_eq_accept_iff (Δflag : Nat) {n : Nat}
    (c : Configuration (M := (acceptIfCellCS Δflag).toPhased.toTM) n)
    (hphase : c.state.fst.val = (acceptIfCellCS Δflag).startPhase.val)
    (hstate : c.state.snd = (acceptIfCellCS Δflag).startState)
    (hbound : c.head.val + Δflag <
      (acceptIfCellCS Δflag).toPhased.toTM.tapeLength n) :
    (TM.runConfig (M := (acceptIfCellCS Δflag).toPhased.toTM) c
        ((acceptIfCellCS Δflag).timeBound n)).state =
      (acceptIfCellCS Δflag).toPhased.toTM.accept ↔
    c.tape ⟨c.head.val + Δflag, hbound⟩ = true := by
  obtain ⟨hrun, _, _⟩ := acceptIfCellCS_run_full Δflag c hphase hstate hbound
  rw [hrun]
  change
    ((⟨(acceptIfCellCS Δflag).acceptPhase,
        (c.tape ⟨c.head.val + Δflag, hbound⟩,
         c.tape ⟨c.head.val + Δflag, hbound⟩)⟩ :
      (acceptIfCellCS Δflag).toPhased.State) =
      ⟨(acceptIfCellCS Δflag).acceptPhase, (true, true)⟩) ↔ _
  constructor
  · intro h
    exact congrArg (fun q => q.fst) (congrArg Sigma.snd h)
  · intro hb
    rw [hb]

/-- Dependency-closed semantic run surface for use as the right operand of
an explicit final `seq`. -/
theorem acceptIfCellCS_runSpec (Δflag : Nat) {n : Nat}
    (c : Configuration (M := (acceptIfCellCS Δflag).toPhased.toTM) n)
    (hphase : c.state.fst.val = (acceptIfCellCS Δflag).startPhase.val)
    (hstate : c.state.snd = (acceptIfCellCS Δflag).startState)
    (hbound : c.head.val + Δflag <
      (acceptIfCellCS Δflag).toPhased.toTM.tapeLength n) :
    RunSpec (acceptIfCellCS Δflag) c (fun cf =>
      cf.state.snd =
          (c.tape ⟨c.head.val + Δflag, hbound⟩,
           c.tape ⟨c.head.val + Δflag, hbound⟩) ∧
      cf.head = c.head ∧ cf.tape = c.tape) := by
  refine {
    prefixSafe := ?_
    reachesAcceptPhase := ?_
    postcondition := ?_
  }
  · intro s hs
    let c' := castAcceptIfCellConfig Δflag c
    have hphase' : c'.state.fst.val = 0 := by simpa [c'] using hphase
    have hstate' : c'.state.snd = (false, false) := by simpa [c'] using hstate
    obtain ⟨_, hnot, hsafe⟩ :=
      combineAtOffsetCS_run_invariants_in_prefix
        Δflag Δflag Δflag le_rfl le_rfl (fun a b => a && b)
        c' hphase' hstate' hbound s (by simpa using hs)
    have hrun := castAcceptIfCellConfig_runConfig Δflag c s
    constructor
    · rw [← castAcceptIfCellConfig_state Δflag
          (TM.runConfig (M := (acceptIfCellCS Δflag).toPhased.toTM) c s), hrun]
      exact hnot
    · intro hmove
      rw [← castAcceptIfCellConfig_head Δflag
          (TM.runConfig (M := (acceptIfCellCS Δflag).toPhased.toTM) c s), hrun]
      apply hsafe
      rw [← hrun]
      simpa [castAcceptIfCellConfig, acceptIfCellCS] using hmove
  · obtain ⟨hrun, _, _⟩ := acceptIfCellCS_run_full Δflag c hphase hstate hbound
    rw [hrun]
  · obtain ⟨hrun, hh, ht⟩ := acceptIfCellCS_run_full Δflag c hphase hstate hbound
    exact ⟨congrArg Sigma.snd hrun, hh, ht⟩

/-- The flag value seen by the terminal program in an actual initial
configuration: input cells are read from `x`; offsets beyond the input are
blank and therefore false. -/
theorem acceptIfCellCS_initial_flag_eq (Δflag : Nat) {n : Nat}
    (x : Boolcube.Point n)
    (hbound : Δflag < (acceptIfCellCS Δflag).toPhased.toTM.tapeLength n) :
    ((acceptIfCellCS Δflag).toPhased.toTM.initialConfig x).tape
        ⟨Δflag, hbound⟩ =
      if h : Δflag < n then x ⟨Δflag, h⟩ else false := by
  rfl

/-- End-to-end exact-step acceptance theorem on the machine's actual input
configuration.  An out-of-input offset reads the blank `false` cell. -/
theorem acceptIfCellCS_accepts_iff_input_or_blank_flag (Δflag : Nat) {n : Nat}
    (x : Boolcube.Point n) :
    TM.accepts (M := (acceptIfCellCS Δflag).toPhased.toTM) n x = true ↔
      (if h : Δflag < n then x ⟨Δflag, h⟩ else false) = true := by
  let M := (acceptIfCellCS Δflag).toPhased.toTM
  let c := M.initialConfig x
  have hphase : c.state.fst.val = (acceptIfCellCS Δflag).startPhase.val := by
    rfl
  have hstate : c.state.snd = (acceptIfCellCS Δflag).startState := by
    rfl
  have hbound : c.head.val + Δflag < M.tapeLength n := by
    have h : Δflag < n + (2 * Δflag + 3) + 1 := by omega
    simpa [c, M, TM.initialConfig, TM.tapeLength, PhasedProgram.toTM,
      acceptIfCellCS] using h
  unfold TM.accepts TM.run
  rw [decide_eq_true_eq]
  change
    (TM.runConfig (M := (acceptIfCellCS Δflag).toPhased.toTM) c
        ((acceptIfCellCS Δflag).timeBound n)).state =
      (acceptIfCellCS Δflag).toPhased.toTM.accept ↔ _
  rw [acceptIfCellCS_run_state_eq_accept_iff Δflag c hphase hstate hbound]
  have hflag : c.tape ⟨c.head.val + Δflag, hbound⟩ =
      (if h : Δflag < n then x ⟨Δflag, h⟩ else false) := by
    simp only [c, M, TM.initialConfig, Nat.zero_add]
  rw [hflag]

end ConstStatePhasedProgram
end TM
end PsubsetPpoly
end Internal
end Pnp3
