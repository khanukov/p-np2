import Mathlib.Data.Finset.Card
import Models.Model_PartialMCSP
import Counting.CircuitCounting

namespace Pnp3
namespace Tests
namespace CircuitCountTraceBoundProbe

open Models
open Counting

/-- One-step monotonicity of `circuitCountBound` in the size parameter. -/
lemma circuitCountBound_le_succ (n s : Nat) :
    circuitCountBound n s ≤ circuitCountBound n (s + 1) := by
  cases s <;> simp [circuitCountBound]

/-- Monotonicity of `circuitCountBound` in the size parameter. -/
theorem circuitCountBound_le_of_le
    {n s t : Nat}
    (hst : s ≤ t) :
    circuitCountBound n s ≤ circuitCountBound n t := by
  induction hst with
  | refl => exact le_rfl
  | @step t hst ih =>
      exact le_trans ih (circuitCountBound_le_succ n t)

/-- Monotone form of `circuitCountBound_le_of_le`. -/
theorem circuitCountBound_mono (n : Nat) :
    Monotone (fun s => circuitCountBound n s) := by
  intro s t hst
  exact circuitCountBound_le_of_le (n := n) hst

/--
Trace semantics of a circuit on a finite family of truth-table row indices.
This is the direct circuit analogue of row-trace probes used by iso-strong tests.
-/
def traceCircuitOnRows
    {n : Nat}
    (α : Type) [Fintype α]
    (row : α → Fin (Partial.tableLen n))
    (C : Circuit n) : α → Bool :=
  fun a => Circuit.eval C (Core.vecOfNat n (row a).val)

/--
The number of distinct traces realized by size-bounded circuits is at most the
counting upper bound `circuitCountBound`.
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
Gap-lifted trace-count bound: the YES-size trace image is controlled by the
`(sNO - 1)` counting budget using `gap_ok` and monotonicity.
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
  have hs_le : p.sYES ≤ p.sNO - 1 := by
    omega
  exact le_trans hTrace (circuitCountBound_le_of_le (n := p.n) hs_le)

end CircuitCountTraceBoundProbe
end Tests
end Pnp3
