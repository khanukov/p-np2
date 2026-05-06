import Magnification.AuditRoutes.SupportCardinalityBarrier.CanonicalHardwiringWitness
import Magnification.AuditRoutes.SupportCardinalityBarrier.SupportCardinalityOnly

/-!
# Support-cardinality barrier theorem (T5)

Slot T5 for `seed_packs/fp3b4_support_cardinality_barrier/`.

This module proves the headline support-cardinality barrier promised by the
first four slots.  It is intentionally narrow:

* it only transports an already-held filter predicate across witnesses with the
  same support-cardinality profile;
* it uses the canonical hardwiring witness from T3 and the exact support count
  theorem from T2;
* it does **not** apply the result to `FP3Attempt.InSupportFunctionalDiversity`,
  does **not** write a NoGoLog entry, and does **not** introduce any bridge to a
  final P-vs-NP endpoint.

Progress category: side-track audit formalization.  The theorem rules out a
class of support-cardinality-only audit filters as hardwiring-excluding filters,
but it is not mainline progress toward `P != NP`.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace SupportCardinalityBarrier

open Pnp3.ComplexityInterfaces

/--
Support-cardinality-only filters cannot separate a sublinear-support honest
witness from the canonical hardwiring witness with the same support profile.

Given an honest strict formula witness `w_honest` satisfying a filter `Π`, form
the support profile

`n ↦ |support (w_honest.family n)|`.

If this profile is pointwise bounded by `n`, T3 packages the corresponding
prefix-hardwiring family as `canonicalHardwiringWitness`.  T2 computes that the
canonical witness has exactly that same support-cardinality profile.  The T4
invariance hypothesis `IsSupportCardinalityOnly Filter` therefore transports `Filter` from
`w_honest` to the canonical hardwiring witness.
-/
theorem support_cardinality_barrier
    (Filter : ∀ {L : Language}, InPpolyFormula L → Prop)
    (hInvariant : IsSupportCardinalityOnly Filter)
    {L_honest : Language}
    (w_honest : InPpolyFormula L_honest)
    (hHonest : Filter w_honest)
    (hSubLinear :
      ∀ n, (FormulaCircuit.support (w_honest.family n)).card ≤ n) :
    Filter (canonicalHardwiringWitness
        (fun n => (FormulaCircuit.support (w_honest.family n)).card)
        hSubLinear) := by
  let supportProfile : Nat → Nat :=
    fun n => (FormulaCircuit.support (w_honest.family n)).card
  let canonicalWitness := canonicalHardwiringWitness supportProfile hSubLinear
  exact
    (IsSupportCardinalityOnly.apply
      hInvariant
      w_honest
      canonicalWitness
      (fun n => by
        -- The canonical family was built with support profile equal to the
        -- honest witness's support-cardinality profile.  T2 computes the
        -- canonical side exactly; the direction required by T4 is honest =
        -- canonical, hence `.symm`.
        exact (canonicalHardwiringFamily_support_card supportProfile hSubLinear n).symm)).mp
      hHonest

end SupportCardinalityBarrier
end AuditRoutes
end Magnification
end Pnp3
