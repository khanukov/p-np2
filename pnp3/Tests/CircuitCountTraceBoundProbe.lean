import Models.Model_PartialMCSP
import Counting.CircuitCounting
import Mathlib.Order.Monotone.Basic

/-!
# Circuit-count trace bound probe (L0)

This probe packages four counting bricks needed by the general iso-strong
conclusion audit:

1. monotonicity of `circuitCountBound` in size;
2. a reusable trace map of circuits on explicit truth-table rows;
3. image-cardinality bound for bounded-size circuit traces;
4. gap-parameter wrapper lifting `sYES` traces to `(sNO - 1)` via `gap_ok`.

The file is intentionally local to `pnp3/Tests/` and does not change endpoints.
-/

namespace Pnp3
namespace Tests
namespace CircuitCountTraceBoundProbe

open Models
open Counting

/-- Step monotonicity: one more size layer can only increase the recurrence bound. -/
lemma circuitCountBound_le_succ (n s : Nat) :
    circuitCountBound n s ≤ circuitCountBound n (s + 1) := by
  cases s with
  | zero =>
    simp [circuitCountBound]
  | succ t =>
    simp [circuitCountBound]

/-- Monotonicity of `circuitCountBound` in the size argument. -/
theorem circuitCountBound_mono (n : Nat) :
    Monotone (fun s => circuitCountBound n s) := by
  intro s t hst
  induction hst with
  | refl => rfl
  | @step t hst ih =>
    exact le_trans ih (circuitCountBound_le_succ n t)

/-- Pointwise monotonicity wrapper. -/
theorem circuitCountBound_le_of_le
    {n s t : Nat}
    (hst : s ≤ t) :
    circuitCountBound n s ≤ circuitCountBound n t :=
  circuitCountBound_mono n hst

/--
Trace of a circuit on an arbitrary finite row-indexed family.

`row a` supplies a row index in the partial truth-table domain;
we evaluate `C` on the corresponding `n`-bit assignment via `vecOfNat`.
-/
def traceCircuitOnRows
    {n : Nat}
    (α : Type) [Fintype α]
    (row : α → Fin (Partial.tableLen n))
    (C : Circuit n) : α → Bool :=
  fun a => Circuit.eval C (Core.vecOfNat n (row a).val)

/--
The number of distinct traces induced by circuits from `circuitsOfSizeAtMost n s`
is upper-bounded by `circuitCountBound n s`.
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
Gap-parameter wrapper: traces of size-`≤ sYES` circuits are bounded by the
`(sNO - 1)` circuit-count envelope, via `gap_ok` and monotonicity.
-/
theorem boundedSizeTrace_image_card_le_sNO_minus_one
    (p : GapPartialMCSPParams)
    (α : Type) [Fintype α]
    (row : α → Fin (Partial.tableLen p.n)) :
    ((circuitsOfSizeAtMost p.n p.sYES).image
      (traceCircuitOnRows (n := p.n) α row)).card
      ≤ circuitCountBound p.n (p.sNO - 1) := by
  have hCard :
      ((circuitsOfSizeAtMost p.n p.sYES).image
        (traceCircuitOnRows (n := p.n) α row)).card
        ≤ circuitCountBound p.n p.sYES :=
    boundedSizeTrace_image_card_le p.n p.sYES α row
  have hsYES_le : p.sYES ≤ p.sNO - 1 := by
    omega
  exact le_trans hCard (circuitCountBound_le_of_le (n := p.n) hsYES_le)

end CircuitCountTraceBoundProbe
end Tests
end Pnp3
