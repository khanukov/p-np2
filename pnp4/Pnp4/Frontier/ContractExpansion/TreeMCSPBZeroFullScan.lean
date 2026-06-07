import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram
import Complexity.TMVerifier.TuringToolkit.BinaryCounter
import Pnp4.Frontier.ContractExpansion.BoundedLoopProgram

/-!
# `bZeroFullScan` — the **sound** width-`w` `B = 0` test (NP-verifier track — D2t-3 `δ`)

`TM_VERIFIER_STRATEGY.md` §12 records that the merged routing test
`bZeroRouteProgram = seq gammaSelfLoopScan stepRightThenBranch` (scan to the first `1`, read the next
cell, branch) is **not a sound `B = 0` test** on a raw little-endian binary counter: for `B > 0` it
silently requires the cell *after* the lowest set bit to be `0`, which binary decrement does not
preserve (counterexample `B = 3 = "11"`).  Literature confirms a correct binary-counter zero-test
inspects **all** counter bits at the counter's fixed bit-length (Seiferas & Vitányi, *Counting Is Easy*,
arXiv `cs/0110038`; counter-machine constructions); the first-`1`+next-cell shortcut is unsound.

This module ships the corrected design: a **width-`w` full scan**.  As a `w`-parameterised program
(`numPhases = w + 2`, phase count growing with `w`, like `gammaZeroScanProgram`'s `maxIters`) it uses the
**known width `w`** as the scan bound — sidestepping the binary-alphabet delimiting wall (§6).

```
bZeroFullScan w :  scan B's window cell-by-cell using the known width w
  phases 0 .. w-1 :  read the cell  —  `0` → step right, next phase  /  `1` → phase w+1 (B > 0)
  phase  w        :  B = 0  (every one of the w cells was `0`)   — the accept phase
  phase  w+1      :  B > 0  (a set bit was found)                — the body-entry branch
```

So the head, started on `B`'s low end, accepts at phase `w` iff all `w` cells are `0` (`B = 0`), and
diverts to phase `w+1` on the first `1` it meets (`B > 0`).  Following the structural-first discipline
(`bZeroRouteProgram`, `loopUntilSink` shipped def + structural lemmas before run-invariants), this brick
ships the **program definition + structural lemmas** plus the **pure-spec foundation**
(`counterValue_eq_zero_imp_all_false`: a zero counter value forces every windowed cell to `false` — the
fact the `B = 0` run-through consumes).  The run-through and the `loopUntilSink` `hbase`/`hstep` discharge
are the follow-up bricks.

**Progress classification (AGENTS.md): Infrastructure** — control program toward the NP-membership leg;
it builds no verifier and proves no separation.  Standard `[propext, Classical.choice, Quot.sound]`
triple only.  **No `P ≠ NP` claim.**
-/

universe u

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram
open Pnp3.Internal.PsubsetPpoly.TM.BinaryCounter

/-! ## Pure-spec foundation: a zero counter value forces every windowed cell to `false` -/

/-- **Converse of `counterValue_of_all_false`.**  If the little-endian counter value of the width-`k`
window `[start, start + k)` is `0`, then every cell in that window reads `false`.  (Each set bit at
offset `i < k` contributes `2 ^ i ≥ 1`, so any set bit makes the value positive.)  This is the spec
fact the `bZeroFullScan` `B = 0` run-through consumes: `counterValue = 0` (the loop's `hbase`
hypothesis) ⇒ the scan reads `0` at every one of the `w` cells, so it reaches the accept phase. -/
theorem counterValue_eq_zero_imp_all_false {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) (start : Nat) :
    ∀ k, counterValue c start k = 0 →
      ∀ i, i < k → ∀ (hb : start + i < M.tapeLength n),
        c.tape ⟨start + i, hb⟩ = false := by
  intro k
  induction k with
  | zero => intro _ i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ k ih =>
    intro h0 i hi hb
    rw [counterValue_succ] at h0
    obtain ⟨hck, hadd⟩ := Nat.add_eq_zero.mp h0
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | rfl
    · exact ih hck i hlt hb
    · rw [dif_pos hb] at hadd
      by_cases ht : c.tape ⟨start + i, hb⟩ = true
      · rw [if_pos ht] at hadd
        have hpos := Nat.one_le_pow i 2 (by decide)
        omega
      · simpa using ht

/-! ## The `bZeroFullScan` program -/

/-- The sound width-`w` `B = 0` test (see the module docstring).  Started on `B`'s low end, the scan
reads each of the `w` cells: on `0` it steps right to the next cell, on `1` it diverts to phase `w + 1`
(`B > 0`); having read all `w` cells as `0` it rests at the accept phase `w` (`B = 0`). -/
def bZeroFullScan (w : Nat) : ConstStatePhasedProgram Unit where
  numPhases := w + 2
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨w, by omega⟩
  acceptState := ()
  transition := fun i _ b =>
    if h : (i : Nat) < w then
      if b then
        (⟨w + 1, by omega⟩, (), b, Move.stay)
      else
        (⟨(i : Nat) + 1, by omega⟩, (), b, Move.right)
    else
      (i, (), b, Move.stay)
  timeBound := fun _ => w + 1

@[simp] theorem bZeroFullScan_numPhases (w : Nat) :
    (bZeroFullScan w).numPhases = w + 2 := rfl

@[simp] theorem bZeroFullScan_startPhase_val (w : Nat) :
    ((bZeroFullScan w).startPhase : Nat) = 0 := rfl

@[simp] theorem bZeroFullScan_acceptPhase_val (w : Nat) :
    ((bZeroFullScan w).acceptPhase : Nat) = w := rfl

@[simp] theorem bZeroFullScan_timeBound (w n : Nat) :
    (bZeroFullScan w).timeBound n = w + 1 := rfl

/-- The scan only ever steps right or stays, so it never moves its head left — it therefore composes
further under `seq`/`loopUntilSink`. -/
theorem bZeroFullScan_transition_move (w : Nat) (i : Fin (w + 2)) (s : Unit) (b : Bool) :
    ((bZeroFullScan w).transition i s b).2.2.2 ≠ Move.left := by
  unfold bZeroFullScan
  dsimp only
  split_ifs <;> simp

theorem bZeroFullScan_neverMovesLeft (w : Nat) :
    TMNeverMovesLeft ((bZeroFullScan w).toPhased.toTM) := by
  intro st b
  obtain ⟨i, s⟩ := st
  exact bZeroFullScan_transition_move w i s b

/-- Every step writes back the scanned bit, so the scan leaves the tape unchanged. -/
theorem bZeroFullScan_transition_bit (w : Nat) (i : Fin (w + 2)) (s : Unit) (b : Bool) :
    ((bZeroFullScan w).transition i s b).2.2.1 = b := by
  unfold bZeroFullScan
  dsimp only
  split_ifs <;> rfl

end ContractExpansion
end Frontier
end Pnp4
