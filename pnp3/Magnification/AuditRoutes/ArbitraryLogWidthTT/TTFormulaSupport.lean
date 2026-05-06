import Magnification.AuditRoutes.ArbitraryLogWidthTT.AllEssential
import Tests.FormulaSupportBoundsFalsifiabilityProbe
import Mathlib.Tactic

/-!
# Arbitrary log-width truth-table payload: support of all-essential formulas

Slot T2 for `seed_packs/fp3b2_arbitrary_logwidth_tt_payload/`.

The truth-table constructor `ttFormula` is semantically exact for every Boolean
function `f : Bitstring k → Bool`.  This file records the support consequence
needed by the arbitrary-payload audit route: if every input coordinate is
essential for `f`, then every coordinate must occur in the syntactic support of
`ttFormula f`.

The lower-bound argument deliberately avoids any special `prefixAnd` reasoning.
If a coordinate `i` were absent from the formula support, the general
`FormulaCircuit.eval_eq_of_eq_on_support` lemma would make the formula invariant
under flipping `i`; `ttFormula_eval` would then make `f` invariant under that
same flip, contradicting `AllEssential f`.

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
If `f` depends essentially on every coordinate, then the syntactic support of
`ttFormula f` is all of `Fin k`.

This is the semantic heart of the T2 slot.  The proof uses only the already
kernel-checked correctness theorem for `ttFormula` and the general support
invariance lemma for formulas; it does not inspect the recursive shape of
`ttFormula` and therefore applies to a generic payload
`f : Bitstring k → Bool` rather than to the earlier `prefixAnd` special case.
-/
theorem ttFormula_support_eq_univ_of_allEssential
    {k : Nat} {f : Bitstring k → Bool}
    (hf : AllEssential f) :
    FormulaCircuit.support (ttFormula f) = Finset.univ := by
  classical
  apply Finset.eq_univ_iff_forall.mpr
  intro i
  by_contra hi
  rcases hf i with ⟨x, hx⟩
  have hEvalSame :
      FormulaCircuit.eval (ttFormula f) x =
        FormulaCircuit.eval (ttFormula f) (flipBit x i) := by
    apply FormulaCircuit.eval_eq_of_eq_on_support
    intro j hj
    have hji : j ≠ i := by
      intro hEq
      exact hi (hEq ▸ hj)
    exact (flipBit_ne x hji).symm
  have hfSame : f x = f (flipBit x i) := by
    rw [← ttFormula_eval f x, ← ttFormula_eval f (flipBit x i)]
    exact hEvalSame
  exact hx hfSame

/--
The support of `ttFormula f` never has more than the ambient `k` coordinates.

This bound is purely finite-set bookkeeping: the support is a finset of
`Fin k`, hence its cardinality is at most the cardinality of the full universe.
It is included as the split upper-bound theorem requested by the seed pack.
-/
theorem ttFormula_support_card_le
    {k : Nat} (f : Bitstring k → Bool) :
    (FormulaCircuit.support (ttFormula f)).card ≤ k := by
  classical
  calc
    (FormulaCircuit.support (ttFormula f)).card ≤ (Finset.univ : Finset (Fin k)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = k := by simp

/--
All-essential payloads force `ttFormula f` to mention at least all `k`
coordinates in its support.
-/
theorem ttFormula_support_card_ge_of_allEssential
    {k : Nat} {f : Bitstring k → Bool}
    (hf : AllEssential f) :
    k ≤ (FormulaCircuit.support (ttFormula f)).card := by
  classical
  rw [ttFormula_support_eq_univ_of_allEssential hf]
  simp

/--
Preferred T2 theorem: an all-essential truth-table payload has exactly full
support cardinality after conversion to `ttFormula`.
-/
theorem ttFormula_support_card_of_allEssential
    {k : Nat} {f : Bitstring k → Bool}
    (hf : AllEssential f) :
    (FormulaCircuit.support (ttFormula f)).card = k := by
  classical
  rw [ttFormula_support_eq_univ_of_allEssential hf]
  simp

end ArbitraryLogWidthTT
end AuditRoutes
end Magnification
end Pnp3
