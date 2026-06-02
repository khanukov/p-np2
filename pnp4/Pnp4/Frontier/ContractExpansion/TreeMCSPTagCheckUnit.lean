import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram
import Pnp4.Frontier.ContractExpansion.PrefixParserConvention

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM

/-!
# Unit-state tag-check verifier program (NP-verifier track, common-state assembly)

`TreeMCSPTagCheckProgram.lean` builds the tag check as a `ConstStatePhasedProgram Bool` (it AND-accumulates
"prefix matches tag so far" into a `Bool` control state).  But `seq`/`seqList` require *one* shared state
type for all phases of the assembled verifier `M`, and the self-loop phases (`gammaSelfLoopScan`,
`selfLoopIncrement`, …) are `ConstStatePhasedProgram Unit` (see `TM_VERIFIER_STRATEGY.md` §6a's
state-uniformity finding).  Rather than lift every self-loop to `Bool`, this module re-expresses the tag
check over **`Unit`**, so the common state can be `Unit` and the existing `Unit` composition machinery
applies directly.

The trick is to phase-encode the match state instead of carrying a `Bool`: phases `0 … tagLen-1` scan and
compare; a **match** advances to the next phase (moving right), a **mismatch** jumps to a dedicated
**reject sink** phase `tagLen + 1`; phase `tagLen` is the accept phase (reached iff *every* tag bit
matched).  Both the accept phase and the sink idle (stay).  `numPhases = tagLen + 2`.

This module builds the program and its structural facts (`timeBound`, never-moves-left).  It builds no
verifier and proves no separation. -/

/-- `Unit`-state tag-check: phase-encodes the match state.  Phases `0 … tagLen-1` compare the scanned bit
to the corresponding big-endian bit of `treePrefixTag`; a match advances (right), a mismatch jumps to the
reject sink phase `tagLen + 1`; the accept phase `tagLen` and the sink both idle. -/
def tagCheckProgramU : ConstStatePhasedProgram Unit where
  numPhases := tagLen + 2
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨tagLen, by omega⟩
  acceptState := ()
  transition := fun i _ b =>
    if h : i.val < tagLen then
      bif b == natBitBE treePrefixTag tagLen ⟨i.val, h⟩ then
        (⟨i.val + 1, by omega⟩, (), b, Move.right)
      else
        (⟨tagLen + 1, by omega⟩, (), b, Move.right)
    else
      (i, (), b, Move.stay)
  timeBound := fun _ => tagLen

@[simp] theorem tagCheckProgramU_timeBound (n : Nat) :
    tagCheckProgramU.timeBound n = tagLen := rfl

@[simp] theorem tagCheckProgramU_numPhases :
    tagCheckProgramU.numPhases = tagLen + 2 := rfl

@[simp] theorem tagCheckProgramU_startPhase_val :
    (tagCheckProgramU.startPhase : Nat) = 0 := rfl

@[simp] theorem tagCheckProgramU_acceptPhase_val :
    (tagCheckProgramU.acceptPhase : Nat) = tagLen := rfl

/-- The `Unit` tag-check transition only ever moves the head right (scanning, match or mismatch) or
stays (accept/sink); never left. -/
theorem tagCheckProgramU_transition_move (i : Fin (tagLen + 2)) (s : Unit) (b : Bool) :
    (tagCheckProgramU.transition i s b).2.2.2 ≠ Move.left := by
  unfold tagCheckProgramU
  dsimp only
  split_ifs with h
  · cases b == natBitBE treePrefixTag tagLen ⟨i.val, h⟩ <;> simp
  · simp

/-- The compiled `Unit` tag-check Turing machine never moves its head left (lifts
`tagCheckProgramU_transition_move` through `toPhased`/`toTM`; composes via `seqList_neverMovesLeft`). -/
theorem tagCheckProgramU_neverMovesLeft :
    TMNeverMovesLeft (tagCheckProgramU.toPhased.toTM) := by
  intro st b
  obtain ⟨i, s⟩ := st
  exact tagCheckProgramU_transition_move i s b

end ContractExpansion
end Frontier
end Pnp4
