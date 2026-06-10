import Pnp4.Frontier.ContractExpansion.TreeMCSPTagCheckProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPTagCheckUnit
import Pnp4.Frontier.ContractExpansion.TreeMCSPTagCheckComposition
import Pnp4.Frontier.ContractExpansion.TreeMCSPGammaScanProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPSelfLoopCounter
import Pnp4.Frontier.ContractExpansion.TreeMCSPScanComposition
import Pnp4.Frontier.ContractExpansion.TreeMCSPLeadingPhasesChain
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

/-! ### Native `Unit`-state skeleton (no lifting)

With the `Unit`-state tag check (`tagCheckProgramU`), the common state of `M` can simply be `Unit`, so
the leading phases compose **natively** — no `liftUnitProgram`/bisimulation required.  `mSkeletonU` is
the genuine M-leading-phases skeleton over `Unit`: tag check, then gamma scan and a counter.  It
inherits the same structural guarantees (never-left, polynomial `timeBound`) directly from the `Unit`
`seqList` machinery, superseding the lifted `mSkeletonDemo` as the assembly route. -/
def mSkeletonU : ConstStatePhasedProgram Unit :=
  seqList [tagCheckProgramU, gammaSelfLoopScan, selfLoopIncrement]

/-- The native-`Unit` skeleton never moves its head left (each phase is right-only/stay; `seqList`
preserves it). -/
theorem mSkeletonU_neverMovesLeft : TMNeverMovesLeft (mSkeletonU.toPhased.toTM) := by
  apply seqList_neverMovesLeft
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h
  · subst h; exact tagCheckProgramU_neverMovesLeft
  · subst h; exact gammaSelfLoopScan_neverMovesLeft
  · subst h; exact selfLoopIncrement_neverMovesLeft

/-- The native-`Unit` skeleton's `timeBound` is polynomially bounded: with all three phases within `n`
steps (for `n ≥ tagLen`), the composition runs within `3 · (n + 1)`.  The `runTime_poly`-shaped
guarantee for the genuine `Unit` assembly. -/
theorem mSkeletonU_timeBound_le (n : Nat) (hn : tagLen ≤ n) :
    mSkeletonU.timeBound n ≤ 3 * (n + 1) := by
  have h3 : ([tagCheckProgramU, gammaSelfLoopScan, selfLoopIncrement].length : Nat) = 3 := rfl
  have hbound := seqList_timeBound_le
    [tagCheckProgramU, gammaSelfLoopScan, selfLoopIncrement] n n
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with h | h | h
      · subst h; rw [tagCheckProgramU_timeBound]; exact hn
      · subst h; simp
      · subst h; simp)
  rw [h3] at hbound
  exact hbound

/-- Run behaviour of the **assembled** skeleton `mSkeletonU` (not a toy 2-phase `seq`): its tag-check
phase verifies and hands off correctly.  Since `mSkeletonU = seq tagCheckProgramU (seqList […])`
definitionally, the generic `tagCheckProgramU_seq_runConfig_handoff` (parametric over `P2`) applies
directly with `P2 := seqList [gammaSelfLoopScan, selfLoopIncrement]`: on a matching tag, after
`tagLen + 1` steps `mSkeletonU` reaches phase `tagLen + 2` (the start of the gamma-scan sub-program,
`tagCheckProgramU.numPhases + P2.startPhase = tagCheckProgramU.numPhases`), with the head at `tagLen`
and the tape unchanged.  Completes `mSkeletonU`'s run-level characterization alongside
`mSkeletonU_{neverMovesLeft,timeBound_le}`. -/
theorem mSkeletonU_tagCheck_handoff {L : Nat} (x : Boolcube.Point L)
    (hmatch : tagMatchPrefix x tagLen = true) :
    (((TM.runConfig (M := mSkeletonU.toPhased.toTM)
        (mSkeletonU.toPhased.toTM.initialConfig x) (tagLen + 1)).state).fst : Nat) = tagLen + 2
      ∧ ((TM.runConfig (M := mSkeletonU.toPhased.toTM)
          (mSkeletonU.toPhased.toTM.initialConfig x) (tagLen + 1)).head : Nat) = tagLen
      ∧ (TM.runConfig (M := mSkeletonU.toPhased.toTM)
          (mSkeletonU.toPhased.toTM.initialConfig x) (tagLen + 1)).tape
          = (mSkeletonU.toPhased.toTM.initialConfig x).tape := by
  -- `mSkeletonU` is definitionally `seq tagCheckProgramU (seqList […])`; rewrite it *syntactically*
  -- so the machines match without the defeq checker unfolding the concrete `tagLen+1`-fold `runConfig`.
  have hM : mSkeletonU = seq tagCheckProgramU (seqList [gammaSelfLoopScan, selfLoopIncrement]) := rfl
  rw [hM]
  exact tagCheckProgramU_seq_runConfig_handoff (seqList [gammaSelfLoopScan, selfLoopIncrement]) x hmatch

/-- The **assembled** skeleton `mSkeletonU` runs its first two real phases — tag check ▸ gamma
zero-scan — on one machine.  Since `mSkeletonU = seq tagCheckProgramU (seq gammaSelfLoopScan (seqList
[selfLoopIncrement]))` definitionally, the transitively-nested chain
`tagCheckThenNestedGammaScan_runConfig` (with `R := seqList [selfLoopIncrement]`) applies: on a matching
tag and an all-zero gamma prefix of length `k`, after `(tagLen + 1) + k` steps `mSkeletonU` rests in the
gamma-scan phase (`tagLen + 2`), the head advanced to `tagLen + k`, the tape unchanged.  The capstone
run-behaviour fact for the real assembled skeleton (the count `(tagLen + 1) + k` is non-constant, so it
typechecks directly against the nested chain up to the `seqList`-unfolding defeq). -/
theorem mSkeletonU_tagCheck_then_scan {L : Nat} (x : Boolcube.Point L)
    (hmatch : tagMatchPrefix x tagLen = true) (k : Nat) (hk : tagLen + k ≤ L)
    (hzeros : ∀ p : Fin (mSkeletonU.toPhased.toTM.tapeLength L),
      tagLen ≤ (p : Nat) → (p : Nat) < tagLen + k →
      (mSkeletonU.toPhased.toTM.initialConfig x).tape p = false) :
    (((TM.runConfig (M := mSkeletonU.toPhased.toTM)
        (mSkeletonU.toPhased.toTM.initialConfig x) ((tagLen + 1) + k)).state).fst : Nat) = tagLen + 2
      ∧ ((TM.runConfig (M := mSkeletonU.toPhased.toTM)
          (mSkeletonU.toPhased.toTM.initialConfig x) ((tagLen + 1) + k)).head : Nat) = tagLen + k
      ∧ (TM.runConfig (M := mSkeletonU.toPhased.toTM)
          (mSkeletonU.toPhased.toTM.initialConfig x) ((tagLen + 1) + k)).tape
          = (mSkeletonU.toPhased.toTM.initialConfig x).tape :=
  tagCheckThenNestedGammaScan_runConfig (seqList [selfLoopIncrement]) x hmatch k hk hzeros

end ContractExpansion
end Frontier
end Pnp4
