import Pnp4.Frontier.ContractExpansion.TreeMCSPTagCheckProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPGammaScanProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPSelfLoopCounter
import Pnp4.Frontier.ContractExpansion.BoundedLoopProgram

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-!
# Heterogeneous-state skeleton composition (NP-verifier track, assembly milestone)

`seq`/`seqList` require a single shared state type, but `M`'s phases have *different* state types: the
tag check is `ConstStatePhasedProgram Bool` (it accumulates "prefix matches tag so far"), while the
self-loops (`gammaSelfLoopScan`, `selfLoopIncrement`, …) are `ConstStatePhasedProgram Unit`.  The
`liftUnitProgram` combinator (`BoundedLoopProgram.lean`) reinterprets a state-agnostic `Unit` program
over any inhabited state, so the self-loops can be lifted to the tag check's `Bool` and the whole list
composed.

This module demonstrates that the heterogeneous assembly actually works: a representative skeleton of
`M`'s leading phases — the tag check, then the gamma scan and a counter (both lifted to `Bool`) —
composes into one well-typed `ConstStatePhasedProgram Bool`, and inherits the two structural
guarantees the eventual `runTime_poly` / head-tracking arguments need: it never moves the head left,
and its `timeBound` is polynomially bounded.  No verifier and no separation are built; the per-phase
*run behaviour* of the lifted phases (the state-component bisimulation) is the documented follow-up.
-/

/-- A representative heterogeneous-state skeleton of `M`'s leading phases: the `Bool`-state tag check,
then the gamma scan and a counter (both `Unit`-state self-loops lifted to `Bool`), composed as a
`seqList` over the common state `Bool`. -/
def mSkeletonDemo : ConstStatePhasedProgram Bool :=
  seqList [tagCheckProgram, liftUnitProgram gammaSelfLoopScan, liftUnitProgram selfLoopIncrement]

/-- The heterogeneous skeleton never moves its head left: each phase is right-only/stay (the tag check
directly, the lifted self-loops via `liftUnitProgram_neverMovesLeft`), and `seqList` preserves it. -/
theorem mSkeletonDemo_neverMovesLeft : TMNeverMovesLeft (mSkeletonDemo.toPhased.toTM) := by
  apply seqList_neverMovesLeft
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h
  · subst h; exact tagCheckProgram_neverMovesLeft
  · subst h
    exact liftUnitProgram_neverMovesLeft gammaSelfLoopScan gammaSelfLoopScan_neverMovesLeft
  · subst h
    exact liftUnitProgram_neverMovesLeft selfLoopIncrement selfLoopIncrement_neverMovesLeft

/-- The heterogeneous skeleton's `timeBound` is polynomially bounded: with all three phases running
within `n` steps (for `n ≥ tagLen`), the composition runs within `3 · (n + 1)`.  This is the
`runTime_poly`-shaped guarantee, inherited from `seqList_timeBound_le` — now applicable to a
*heterogeneous-state* assembly thanks to `liftUnitProgram`. -/
theorem mSkeletonDemo_timeBound_le (n : Nat) (hn : tagLen ≤ n) :
    mSkeletonDemo.timeBound n ≤ 3 * (n + 1) := by
  have h3 : ([tagCheckProgram, liftUnitProgram gammaSelfLoopScan,
      liftUnitProgram selfLoopIncrement].length : Nat) = 3 := rfl
  have hbound := seqList_timeBound_le
    [tagCheckProgram, liftUnitProgram gammaSelfLoopScan, liftUnitProgram selfLoopIncrement] n n
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with h | h | h
      · subst h; rw [tagCheckProgram_timeBound]; exact hn
      · subst h; simp
      · subst h; simp)
  rw [h3] at hbound
  exact hbound

end ContractExpansion
end Frontier
end Pnp4
