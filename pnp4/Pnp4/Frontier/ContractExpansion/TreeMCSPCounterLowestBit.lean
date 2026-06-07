import Complexity.TMVerifier.TuringToolkit.BinaryCounter

/-!
# `counterValue` lowest-set-bit existence (NP-verifier track — D2t-3 `ε`, `hstep` support)

The arithmetic ingredient `hstep` needs to invoke the `B > 0` body pass: a nonzero little-endian counter
has a **lowest set bit**.  Given `counterValue c start w ≠ 0`, there is a `j < w` with cells
`[start, start+j)` all `0` and cell `start+j` set — exactly the `hzeros`/`hone` hypotheses of
`binToUnaryLoopFullScan_runConfig_bodyPass` (with `start := head + 1`).

`counterValue_eq_zero_imp_false` is the supporting converse of `counterValue_of_all_false` (a zero counter
forces every counted cell to `0`), proved by the same per-bit induction.

**Progress classification (AGENTS.md): Infrastructure** — a `BinaryCounter` arithmetic lemma; no verifier,
no run behaviour.  Standard `[propext, Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace TM
namespace BinaryCounter

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM

/-- `counterValue = 0` forces every counted cell to be `false` (the converse of
`counterValue_of_all_false`). -/
theorem counterValue_eq_zero_imp_false {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) (start : Nat) :
    ∀ k, counterValue c start k = 0 →
      ∀ i, i < k → (h : start + i < M.tapeLength n) → c.tape ⟨start + i, h⟩ = false := by
  intro k
  induction k with
  | zero => intro _ i hi _; omega
  | succ k ih =>
      intro h0 i hi h
      rw [counterValue_succ] at h0
      have hlo : counterValue c start k = 0 := by omega
      have hbit : (if hh : start + k < M.tapeLength n then
            (if c.tape ⟨start + k, hh⟩ then 2 ^ k else 0) else 0) = 0 := by omega
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
      · exact ih hlo i hlt h
      · subst heq
        rw [dif_pos h] at hbit
        by_contra hc
        rw [Bool.not_eq_false] at hc
        rw [hc] at hbit
        simp at hbit

/-- **Lowest set bit.**  If the width-`w` little-endian counter at `start` is nonzero, there is a lowest
set bit `j < w`: cells `[start, start+j)` are all `0` and cell `start+j` is `1`.  Matches the
`hzeros`/`hone` hypotheses of `binToUnaryLoopFullScan_runConfig_bodyPass` (with `start := head + 1`). -/
theorem counterValue_pos_imp_lowestBit {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) (start : Nat) :
    ∀ w, counterValue c start w ≠ 0 →
      ∃ j, j < w
        ∧ (∀ q : Fin (M.tapeLength n), start ≤ (q : Nat) → (q : Nat) < start + j → c.tape q = false)
        ∧ (∀ q : Fin (M.tapeLength n), (q : Nat) = start + j → c.tape q = true) := by
  intro w
  induction w with
  | zero => intro h; simp [counterValue] at h
  | succ w ih =>
      intro hpos
      by_cases hcw : counterValue c start w = 0
      · refine ⟨w, Nat.lt_succ_self w, ?_, ?_⟩
        · intro q hq1 hq2
          have hi := counterValue_eq_zero_imp_false c start w hcw ((q : Nat) - start) (by omega)
            (by omega)
          simp only [show start + ((q : Nat) - start) = (q : Nat) from by omega, Fin.eta] at hi
          exact hi
        · intro q hq
          rw [counterValue_succ, hcw, Nat.zero_add] at hpos
          have hfit : start + w < M.tapeLength n := by
            by_contra hnf; rw [dif_neg hnf] at hpos; exact hpos rfl
          rw [dif_pos hfit] at hpos
          have hqeq : q = ⟨start + w, hfit⟩ := Fin.ext (by rw [hq])
          rw [hqeq]
          by_contra hc
          rw [Bool.not_eq_true] at hc
          rw [hc] at hpos; simp at hpos
      · obtain ⟨j, hj, hz, ho⟩ := ih hcw
        exact ⟨j, Nat.lt_succ_of_lt hj, hz, ho⟩

end BinaryCounter
end TM
end PsubsetPpoly
end Internal
end Pnp3
