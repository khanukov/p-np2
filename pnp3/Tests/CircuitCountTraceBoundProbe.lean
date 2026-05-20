import Mathlib.Data.Finset.Card
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Models.Model_PartialMCSP
import Counting.CircuitCounting

/-!
# Circuit-count trace bound L0 probe

This probe packages the counting bricks requested by the D0 audit:

1. monotonicity of `circuitCountBound` in size parameter;
2. row-trace map for arbitrary bounded-size circuits;
3. image-cardinality bound via existing circuit enumeration;
4. lifting from `sYES` to `sNO - 1` using `gap_ok`.

The file is intentionally local to `pnp3/Tests/` and does not modify endpoints.
-/

namespace Pnp3
namespace Tests
namespace CircuitCountTraceBoundProbe

open Models
open Counting

/-- One-step monotonicity of `circuitCountBound` in the size argument. -/
lemma circuitCountBound_le_succ (n s : Nat) :
    circuitCountBound n s ≤ circuitCountBound n (s + 1) := by
  cases hs : circuitCountBound n s with
  | zero =>
      simp [circuitCountBound, hs]
  | succ k =>
      simp [circuitCountBound, hs]
      nlinarith

/-- Monotone form of size monotonicity for `circuitCountBound`. -/
theorem circuitCountBound_mono (n : Nat) :
    Monotone (fun s => circuitCountBound n s) := by
  intro s t hst
  induction hst with
  | refl => rfl
  | @step t hst ih =>
      exact le_trans ih (circuitCountBound_le_succ n t)

/-- Binary-form monotonicity helper. -/
theorem circuitCountBound_le_of_le {n s t : Nat} (hst : s ≤ t) :
    circuitCountBound n s ≤ circuitCountBound n t :=
  circuitCountBound_mono n hst

/-- Trace of a circuit on an arbitrary finite family of truth-table rows. -/
def traceCircuitOnRows
    {n : Nat}
    (α : Type) [Fintype α]
    (row : α → Fin (Partial.tableLen n))
    (C : Circuit n) : α → Bool :=
  fun a => Circuit.eval C (Core.vecOfNat n (row a).val)

/--
The number of distinct traces induced by circuits from `circuitsOfSizeAtMost`
is bounded by `circuitCountBound`.
-/
theorem boundedSizeTrace_image_card_le
    (n s : Nat)
    (α : Type) [Fintype α]
    (row : α → Fin (Partial.tableLen n)) :
    ((circuitsOfSizeAtMost n s).image
      (traceCircuitOnRows (n := n) α row)).card
      ≤ circuitCountBound n s := by
  calc
    ((circuitsOfSizeAtMost n s).image
      (traceCircuitOnRows (n := n) α row)).card
      ≤ (circuitsOfSizeAtMost n s).card := Finset.card_image_le
    _ ≤ circuitCountBound n s := card_circuitsOfSizeAtMost_le n s

/--
`gap_ok` lifts the trace-count bound from `sYES` to `sNO - 1`.
This is the wrapper required by the future generalized iso-strong diagonal step.
-/
theorem boundedSizeTrace_image_card_le_sNO_minus_one
    (p : GapPartialMCSPParams)
    (α : Type) [Fintype α]
    (row : α → Fin (Partial.tableLen p.n)) :
    ((circuitsOfSizeAtMost p.n p.sYES).image
      (traceCircuitOnRows (n := p.n) α row)).card
      ≤ circuitCountBound p.n (p.sNO - 1) := by
  have hTrace :
      ((circuitsOfSizeAtMost p.n p.sYES).image
        (traceCircuitOnRows (n := p.n) α row)).card
        ≤ circuitCountBound p.n p.sYES :=
    boundedSizeTrace_image_card_le p.n p.sYES α row
  have hsYES_le_sNOm1 : p.sYES ≤ p.sNO - 1 := by
    exact Nat.le_pred_of_lt (lt_of_lt_of_le (Nat.lt_succ_self p.sYES) p.gap_ok)
  exact le_trans hTrace (circuitCountBound_le_of_le hsYES_le_sNOm1)

/-- Optional packaging lemma useful for future diagonal slack instantiations. -/
theorem boundedSizeTrace_image_card_lt_of_slack
    (p : GapPartialMCSPParams)
    (D : Finset (Fin (Partial.tableLen p.n)))
    (hSlack :
      circuitCountBound p.n (p.sNO - 1) <
        2 ^ ((Finset.univ \ D).card)) :
    ((circuitsOfSizeAtMost p.n p.sYES).image
      (traceCircuitOnRows
        (n := p.n)
        ((Finset.univ \ D).attach)
        (fun a => a.1))).card
      < 2 ^ ((Finset.univ \ D).card) := by
  have hLe :
      ((circuitsOfSizeAtMost p.n p.sYES).image
        (traceCircuitOnRows
          (n := p.n)
          ((Finset.univ \ D).attach)
          (fun a => a.1))).card
        ≤ circuitCountBound p.n (p.sNO - 1) :=
    boundedSizeTrace_image_card_le_sNO_minus_one p ((Finset.univ \ D).attach) (fun a => a.1)
  exact lt_of_le_of_lt hLe hSlack

end CircuitCountTraceBoundProbe
end Tests
end Pnp3
