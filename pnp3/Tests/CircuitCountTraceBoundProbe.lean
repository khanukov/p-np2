import Models.Model_PartialMCSP
import Counting.CircuitCounting

/-!
# Circuit-count trace bound probe (L0)

This probe packages the four counting bricks identified by the
`general_isoStrong_no_go_D0` audit
(`seed_packs/general_isoStrong_no_go_D0/reports/D0_general_isoStrong_no_go_codex53.md`)
as prerequisites for the generalised iso-strong conclusion-side argument:

1. monotonicity of `circuitCountBound` in the size parameter
   (`circuitCountBound_le_succ`, `circuitCountBound_mono`,
   `circuitCountBound_le_of_le`);
2. a reusable row-trace map for arbitrary bounded-size circuits
   (`traceCircuitOnRows`);
3. an image-cardinality bound for bounded-size circuit traces
   (`boundedSizeTrace_image_card_le`), obtained via the existing
   enumeration `circuitsOfSizeAtMost` and
   `card_circuitsOfSizeAtMost_le` in `pnp3/Counting/CircuitCounting.lean`;
4. a `gap_ok` wrapper lifting `sYES` traces to the `sNO - 1` counting
   envelope (`boundedSizeTrace_image_card_le_sNO_minus_one`).

An optional strict-slack packaging lemma
(`boundedSizeTrace_image_card_lt_of_slack`) is provided for direct
consumption in the future generalised diagonal step.

The file is intentionally local to `pnp3/Tests/` and does not modify
endpoints or trust-root surfaces.  No `axiom` / `opaque` / `sorry` /
`admit` / `native_decide` are introduced.
-/

namespace Pnp3
namespace Tests
namespace CircuitCountTraceBoundProbe

open Models
open Counting

/-- Monotonicity helper in one successor step. -/
lemma circuitCountBound_le_succ (n s : Nat) :
    circuitCountBound n s ≤ circuitCountBound n (s + 1) := by
  cases s with
  | zero =>
      simp [circuitCountBound]
  | succ k =>
      simp [circuitCountBound]
      omega

/-- Monotonicity of `circuitCountBound` in the size parameter. -/
theorem circuitCountBound_mono (n : Nat) :
    Monotone (fun s => circuitCountBound n s) := by
  intro s t hst
  induction hst with
  | refl => simp
  | @step t hst ih =>
      exact le_trans ih (circuitCountBound_le_succ n t)

/-- Convenient two-argument monotonicity corollary. -/
theorem circuitCountBound_le_of_le {n s t : Nat} (hst : s ≤ t) :
    circuitCountBound n s ≤ circuitCountBound n t :=
  circuitCountBound_mono n hst

/--
Trace semantics of a circuit on a finite family of truth-table rows.
This mirrors the row-based trace used in the canonical iso-strong probe.
-/
def traceCircuitOnRows
    {n : Nat}
    (α : Type) [Fintype α]
    (row : α → Fin (Partial.tableLen n))
    (C : Circuit n) : α → Bool :=
  fun a => Circuit.eval C (Core.vecOfNat n (row a).val)

/--
The image of bounded-size circuit traces on any finite row family is
cardinality-bounded by `circuitCountBound`.
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
Gap-lifted wrapper bound: traces of all size-`≤ sYES` circuits are bounded by
`circuitCountBound n (sNO - 1)` using `gap_ok` and monotonicity.
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
  have hyes_le : p.sYES ≤ p.sNO - 1 := by
    exact Nat.le_sub_of_add_le p.gap_ok
  exact le_trans hCard (circuitCountBound_le_of_le (n := p.n) hyes_le)

/--
Optional packaging lemma: combine the gap-lifted trace bound with an external
strict slack hypothesis to derive a strict trace-image inequality.
-/
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
  exact lt_of_le_of_lt
    (boundedSizeTrace_image_card_le_sNO_minus_one p ((Finset.univ \ D).attach) (fun a => a.1))
    hSlack

end CircuitCountTraceBoundProbe
end Tests
end Pnp3
