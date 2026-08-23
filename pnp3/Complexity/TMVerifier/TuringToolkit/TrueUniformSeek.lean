import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram
import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekEncoding
import Mathlib.Tactic.DeriveFintype

/-!
# T1a fixed-control true uniform seek

This slice implements the complete read-only grammar pass and rewind.  The
`startMutation` state is an explicit handoff point for T1b; it is deliberately
idle in T1a.  Consequently this module makes no addressing or restoration
claim.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

inductive T1Mode
  | validateBof | validateIndex | validateData | validateFinish | validateBlank
  | rewindStart | rewind | startMutation | accept | reject
  deriving Fintype, DecidableEq, Repr

inductive T1FramePosition | p0 | p1 | p2 | p3
  deriving Fintype, DecidableEq, Repr

structure T1State where
  mode : T1Mode
  position : T1FramePosition
  b0 : Bool
  b1 : Bool
  b2 : Bool
  deriving Fintype, DecidableEq, Repr

def t1State (mode : T1Mode) (position : T1FramePosition)
    (b0 := false) (b1 := false) (b2 := false) : T1State :=
  ⟨mode, position, b0, b1, b2⟩

def t1AcceptState : T1State := t1State .accept .p0
def t1RejectState : T1State := t1State .reject .p0
def t1MutationState : T1State := t1State .startMutation .p0

def t1Advance : T1Mode → T1Frame → T1Mode
  | .validateBof, .bof => .validateIndex
  | .validateIndex, .index => .validateIndex
  | .validateIndex, .separator => .validateData
  | .validateData, .data _ => .validateData
  | .validateData, .output false => .validateFinish
  | .validateFinish, .finish => .validateBlank
  | .validateBlank, .blank => .rewindStart
  | _, _ => .reject

def t1Complete (mode : T1Mode) (b0 b1 b2 b3 : Bool) : T1Mode :=
  match decodeT1Frame? [b0, b1, b2, b3] with
  | some frame => t1Advance mode frame
  | none => .reject

def t1Transition (_phase : Fin 1) (s : T1State) (scan : Bool) :
    Fin 1 × T1State × Bool × Move :=
  match s.mode with
  | .accept => (0, t1AcceptState, scan, .stay)
  | .reject => (0, t1RejectState, scan, .stay)
  | .startMutation => (0, t1MutationState, scan, .stay)
  | .rewindStart => (0, t1State .rewind .p3, scan, .left)
  | .rewind =>
      match s.position with
      | .p3 => (0, t1State .rewind .p2 false false scan, scan, .left)
      | .p2 => (0, t1State .rewind .p1 false scan s.b2, scan, .left)
      | .p1 => (0, t1State .rewind .p0 scan s.b1 s.b2, scan, .left)
      | .p0 =>
          if decodeT1Frame? [scan, s.b0, s.b1, s.b2] = some .bof then
            (0, t1MutationState, scan, .stay)
          else (0, t1State .rewind .p3, scan, .left)
  | mode =>
      match s.position with
      | .p0 => (0, t1State mode .p1 scan, scan, .right)
      | .p1 => (0, t1State mode .p2 s.b0 scan, scan, .right)
      | .p2 => (0, t1State mode .p3 s.b0 s.b1 scan, scan, .right)
      | .p3 =>
          let next := t1Complete mode s.b0 s.b1 s.b2 scan
          if next = .reject then (0, t1RejectState, scan, .stay)
          else (0, t1State next .p0, scan, .right)

def t1Clock (N : Nat) : Nat := 128 * (N + 1) ^ 2 + 128

/-- The only T1 program declaration: closed finite control and no parameters. -/
def t1CS : ConstStatePhasedProgram T1State where
  numPhases := 1
  startPhase := 0
  startState := t1State .validateBof .p0
  acceptPhase := 0
  acceptState := t1AcceptState
  transition := t1Transition
  timeBound := t1Clock

@[simp] theorem t1CS_numPhases : t1CS.numPhases = 1 := rfl

/-- The public T1 clock in arithmetic normal form.  This theorem is kept out
of the simp set because the generic `toTM_runTime` and `toPhased_timeBound`
simps already reduce the same left-hand side to `t1CS.timeBound N`; callers use
this named theorem to take the additional program-specific step to the expanded
polynomial `t1Clock N` without adding a competing default rewrite. -/
theorem t1CS_runTime (N : Nat) :
    t1CS.toPhased.toTM.runTime N = 128 * (N + 1) ^ 2 + 128 := rfl

@[simp] theorem t1Transition_accept_sink (scan : Bool) :
    t1Transition 0 t1AcceptState scan = (0, t1AcceptState, scan, .stay) := by
  cases scan <;> rfl

@[simp] theorem t1Transition_reject_sink (scan : Bool) :
    t1Transition 0 t1RejectState scan = (0, t1RejectState, scan, .stay) := by
  cases scan <;> rfl

@[simp] theorem t1Transition_mutation_handoff_idle (scan : Bool) :
    t1Transition 0 t1MutationState scan = (0, t1MutationState, scan, .stay) := by
  cases scan <;> rfl

end Pnp3.Internal.PsubsetPpoly.TM
