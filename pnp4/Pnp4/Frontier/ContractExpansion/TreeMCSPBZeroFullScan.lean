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

/-! ## Single-step behaviour -/

/-- Every step writes the scanned bit back, so the tape is unchanged after one step. -/
theorem bZeroFullScan_stepConfig_tape (w : Nat) {L : Nat}
    (c : Configuration (M := (bZeroFullScan w).toPhased.toTM) L)
    {i : Fin (w + 2)} {s : Unit} (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := (bZeroFullScan w).toPhased.toTM) c).tape = c.tape := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_tape (bZeroFullScan w) c hstate,
    bZeroFullScan_transition_bit]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-- **Scan step (read `0`).**  At a scan phase `i < w` reading `0`, advance to phase `i + 1`. -/
theorem bZeroFullScan_stepConfig_scan_phase (w : Nat) {L : Nat}
    (c : Configuration (M := (bZeroFullScan w).toPhased.toTM) L)
    {i : Fin (w + 2)} {s : Unit} (hi : (i : Nat) < w) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := (bZeroFullScan w).toPhased.toTM) c).state).fst.val = (i : Nat) + 1 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase (bZeroFullScan w) c hstate]
  simp [bZeroFullScan, dif_pos hi, hbit]

/-- **Scan step (read `0`).**  At a scan phase `i < w` reading `0`, advance the head by one. -/
theorem bZeroFullScan_stepConfig_scan_head (w : Nat) {L : Nat}
    (c : Configuration (M := (bZeroFullScan w).toPhased.toTM) L)
    {i : Fin (w + 2)} {s : Unit} (hi : (i : Nat) < w) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false)
    (hbound : (c.head : Nat) + 1 < (bZeroFullScan w).toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := (bZeroFullScan w).toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_head (bZeroFullScan w) c hstate]
  have hmove : ((bZeroFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.right := by
    simp [bZeroFullScan, dif_pos hi, hbit]
  rw [hmove]
  simp only [Configuration.moveHead, dif_pos hbound]

/-- **Divert step (read `1`).**  At a scan phase `i < w` reading `1`, jump to phase `w + 1` (`B > 0`). -/
theorem bZeroFullScan_stepConfig_divert_phase (w : Nat) {L : Nat}
    (c : Configuration (M := (bZeroFullScan w).toPhased.toTM) L)
    {i : Fin (w + 2)} {s : Unit} (hi : (i : Nat) < w) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := (bZeroFullScan w).toPhased.toTM) c).state).fst.val = w + 1 := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_phase (bZeroFullScan w) c hstate]
  simp [bZeroFullScan, dif_pos hi, hbit]

/-- **Divert step (read `1`).**  At a scan phase `i < w` reading `1`, the head stays put (on the set
bit). -/
theorem bZeroFullScan_stepConfig_divert_head (w : Nat) {L : Nat}
    (c : Configuration (M := (bZeroFullScan w).toPhased.toTM) L)
    {i : Fin (w + 2)} {s : Unit} (hi : (i : Nat) < w) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    (TM.stepConfig (M := (bZeroFullScan w).toPhased.toTM) c).head = c.head := by
  rw [ConstStatePhasedProgram.toTM_stepConfig_head (bZeroFullScan w) c hstate]
  have hmove : ((bZeroFullScan w).transition i s (c.tape c.head)).2.2.2 = Move.stay := by
    simp [bZeroFullScan, dif_pos hi, hbit]
  rw [hmove]
  simp [Configuration.moveHead]

/-! ## Run-through: the scan reaches the `B = 0` accept phase / the `B > 0` branch -/

/-- **Scanning invariant.**  From a start `c0` in phase `0`, if the `j` cells from the head are all `0`
(`j ≤ w`, in bounds), then after `j` steps the phase is `j`, the head has advanced to `c0.head + j`, and
the tape is unchanged. -/
theorem bZeroFullScan_runConfig_scanning (w : Nat) {L : Nat}
    (c0 : Configuration (M := (bZeroFullScan w).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) :
    ∀ j : Nat, j ≤ w → (c0.head : Nat) + j < (bZeroFullScan w).toPhased.toTM.tapeLength L →
      (∀ p : Fin ((bZeroFullScan w).toPhased.toTM.tapeLength L),
        (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + j → c0.tape p = false) →
      (((TM.runConfig (M := (bZeroFullScan w).toPhased.toTM) c0 j).state).fst : Nat) = j
      ∧ ((TM.runConfig (M := (bZeroFullScan w).toPhased.toTM) c0 j).head : Nat) = (c0.head : Nat) + j
      ∧ (TM.runConfig (M := (bZeroFullScan w).toPhased.toTM) c0 j).tape = c0.tape := by
  intro j
  induction j with
  | zero => intro _ _ _; exact ⟨hphase, by simp, rfl⟩
  | succ j ih =>
      intro hj hb h0
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (by omega) (fun p hp1 hp2 => h0 p hp1 (by omega))
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := (bZeroFullScan w).toPhased.toTM) c0 j with hc
      have hiw : (c.state.fst : Nat) < w := by rw [hph]; omega
      have hbit : c.tape c.head = false := by
        rw [htp]; exact h0 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      have hbnd : (c.head : Nat) + 1 < (bZeroFullScan w).toPhased.toTM.tapeLength L := by
        rw [hhd]; omega
      refine ⟨?_, ?_, ?_⟩
      · rw [bZeroFullScan_stepConfig_scan_phase w c (i := c.state.fst) (s := c.state.snd) hiw rfl hbit,
          hph]
      · rw [bZeroFullScan_stepConfig_scan_head w c (i := c.state.fst) (s := c.state.snd) hiw rfl hbit
          hbnd]
        omega
      · rw [bZeroFullScan_stepConfig_tape w c (i := c.state.fst) (s := c.state.snd) rfl, htp]

/-- **`B = 0` run-through.**  If all `w` cells of `B` (from the head) are `0`, after `w` steps the scan
rests at the accept phase `w` (`B = 0`), with the head at `c0.head + w` and the tape unchanged. -/
theorem bZeroFullScan_runConfig_zero (w : Nat) {L : Nat}
    (c0 : Configuration (M := (bZeroFullScan w).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0)
    (hb : (c0.head : Nat) + w < (bZeroFullScan w).toPhased.toTM.tapeLength L)
    (hzeros : ∀ p : Fin ((bZeroFullScan w).toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + w → c0.tape p = false) :
    (((TM.runConfig (M := (bZeroFullScan w).toPhased.toTM) c0 w).state).fst : Nat) = w
      ∧ ((TM.runConfig (M := (bZeroFullScan w).toPhased.toTM) c0 w).head : Nat) = (c0.head : Nat) + w
      ∧ (TM.runConfig (M := (bZeroFullScan w).toPhased.toTM) c0 w).tape = c0.tape :=
  bZeroFullScan_runConfig_scanning w c0 hphase w (le_refl w) hb hzeros

/-- **`B > 0` run-through.**  If `B`'s low `j` cells are `0` and cell `c0.head + j` is `1` (`j < w`),
after `j + 1` steps the scan has diverted to phase `w + 1` (`B > 0`), with the head on the set bit
(`c0.head + j`) and the tape unchanged. -/
theorem bZeroFullScan_runConfig_pos (w : Nat) {L : Nat}
    (c0 : Configuration (M := (bZeroFullScan w).toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) (j : Nat) (hjw : j < w)
    (hb : (c0.head : Nat) + j < (bZeroFullScan w).toPhased.toTM.tapeLength L)
    (hzeros : ∀ p : Fin ((bZeroFullScan w).toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + j → c0.tape p = false)
    (hone : ∀ p : Fin ((bZeroFullScan w).toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + j → c0.tape p = true) :
    (((TM.runConfig (M := (bZeroFullScan w).toPhased.toTM) c0 (j + 1)).state).fst : Nat) = w + 1
      ∧ ((TM.runConfig (M := (bZeroFullScan w).toPhased.toTM) c0 (j + 1)).head : Nat)
          = (c0.head : Nat) + j
      ∧ (TM.runConfig (M := (bZeroFullScan w).toPhased.toTM) c0 (j + 1)).tape = c0.tape := by
  obtain ⟨hph, hhd, htp⟩ :=
    bZeroFullScan_runConfig_scanning w c0 hphase j (le_of_lt hjw) hb hzeros
  rw [TM.runConfig_succ]
  set c := TM.runConfig (M := (bZeroFullScan w).toPhased.toTM) c0 j with hc
  have hiw : (c.state.fst : Nat) < w := by rw [hph]; exact hjw
  have hbit : c.tape c.head = true := by rw [htp]; exact hone c.head (by rw [hhd])
  refine ⟨?_, ?_, ?_⟩
  · rw [bZeroFullScan_stepConfig_divert_phase w c (i := c.state.fst) (s := c.state.snd) hiw rfl hbit]
  · rw [bZeroFullScan_stepConfig_divert_head w c (i := c.state.fst) (s := c.state.snd) hiw rfl hbit]
    exact hhd
  · rw [bZeroFullScan_stepConfig_tape w c (i := c.state.fst) (s := c.state.snd) rfl, htp]

end ContractExpansion
end Frontier
end Pnp4
