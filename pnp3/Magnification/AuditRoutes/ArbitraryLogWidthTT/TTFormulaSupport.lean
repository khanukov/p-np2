import Magnification.AuditRoutes.ArbitraryLogWidthTT.AllEssential
import Tests.FormulaSupportBoundsFalsifiabilityProbe
import Mathlib.Tactic

/-!
# Arbitrary log-width truth-table payload: support of `ttFormula`

Slot T2 for `seed_packs/fp3b2_arbitrary_logwidth_tt_payload/`.

The truth-table constructor `ttFormula` computes an arbitrary Boolean function
`f : Bitstring k → Bool`.  This file records the support fact needed by later
arbitrary-payload slots: if every input coordinate is semantically essential for
`f`, then every input coordinate must occur syntactically in `ttFormula f`.

The upper bound is purely finite-set bookkeeping (`support` is a `Finset (Fin k)`).
The lower bound is semantic: a coordinate absent from the formula support can be
flipped without changing formula evaluation, contradicting `ttFormula_eval` and
`AllEssential f`.

No lower-bound endpoint, bridge, provenance filter, source theorem, or final
P-vs-NP statement is introduced here.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace ArbitraryLogWidthTT

open Pnp3.ComplexityInterfaces
open Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe

/--
The syntactic support of any width-`k` truth-table formula has at most `k`
coordinates, simply because it is a finite subset of `Fin k`.
-/
theorem ttFormula_support_card_le {k : Nat} (f : Bitstring k → Bool) :
    (FormulaCircuit.support (ttFormula f)).card ≤ k := by
  simpa using (Finset.card_le_univ (FormulaCircuit.support (ttFormula f)))

/--
If a coordinate is absent from the support of `ttFormula f`, then flipping that
coordinate leaves the formula evaluation unchanged at every input.
-/
private theorem ttFormula_eval_eq_flip_of_not_mem_support
    {k : Nat} (f : Bitstring k → Bool) (i : Fin k)
    (hi : i ∉ FormulaCircuit.support (ttFormula f)) (x : Bitstring k) :
    FormulaCircuit.eval (ttFormula f) x =
      FormulaCircuit.eval (ttFormula f) (flipBit x i) := by
  refine FormulaCircuit.eval_eq_of_eq_on_support (ttFormula f) ?_
  intro j hj
  exact (flipBit_ne x (i := i) (j := j) (by
    intro hji
    exact hi (hji ▸ hj))).symm

/--
All-essential truth-table payloads force every coordinate of `Fin k` to occur in
`ttFormula f`'s syntactic support.
-/
private theorem univ_subset_ttFormula_support_of_allEssential
    {k : Nat} {f : Bitstring k → Bool} (hf : AllEssential f) :
    (Finset.univ : Finset (Fin k)) ⊆ FormulaCircuit.support (ttFormula f) := by
  intro i _
  by_contra hi
  rcases hf i with ⟨x, hx⟩
  have heval := ttFormula_eval_eq_flip_of_not_mem_support f i hi x
  rw [ttFormula_eval f x, ttFormula_eval f (flipBit x i)] at heval
  exact hx heval

/--
If all coordinates are semantically essential for `f`, the support of the
truth-table formula computing `f` contains at least all `k` coordinates.
-/
theorem ttFormula_support_card_ge_of_allEssential
    {k : Nat} {f : Bitstring k → Bool}
    (hf : AllEssential f) :
    k ≤ (FormulaCircuit.support (ttFormula f)).card := by
  simpa using Finset.card_le_card (univ_subset_ttFormula_support_of_allEssential hf)

/--
Tight support cardinality for all-essential truth-table payloads.
-/
theorem ttFormula_support_card_of_allEssential
    {k : Nat} {f : Bitstring k → Bool}
    (hf : AllEssential f) :
    (FormulaCircuit.support (ttFormula f)).card = k := by
  exact Nat.le_antisymm (ttFormula_support_card_le f)
    (ttFormula_support_card_ge_of_allEssential hf)

end ArbitraryLogWidthTT
end AuditRoutes
end Magnification
end Pnp3
