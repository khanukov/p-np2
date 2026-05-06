import Magnification.AuditRoutes.SupportCardinalityBarrier.CanonicalHardwiringFamily
import Magnification.AuditRoutes.LogWidthAdversary.Composition

/-!
# Support-cardinality barrier: canonical hardwiring support (T2)

Slot T2 for `seed_packs/fp3b4_support_cardinality_barrier/`.

This module proves the exact support-cardinality theorem for the canonical
hardwiring family introduced by T1.  It intentionally does not define a witness,
a filter, or any barrier theorem; those belong to later slots.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace SupportCardinalityBarrier

open Pnp3.ComplexityInterfaces
open Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary
  (prefixAnd_support_card)

/--
The canonical hardwiring family has exactly the requested support cardinality.

At length `n`, T1 defined `canonicalHardwiringFamily s hs n` to be the prefix
conjunction `prefixAnd n (s n) (hs n)`.  The pre-existing fp3b1 lemma
`prefixAnd_support_card` computes that prefix conjunction's support size exactly,
so this theorem is just the parameterized specialization needed by downstream
fp3b4 slots.
-/
theorem canonicalHardwiringFamily_support_card
    (s : Nat → Nat) (hs : ∀ n, s n ≤ n) (n : Nat) :
    (FormulaCircuit.support (canonicalHardwiringFamily s hs n)).card = s n := by
  simpa [canonicalHardwiringFamily] using
    prefixAnd_support_card n (s n) (hs n)

end SupportCardinalityBarrier
end AuditRoutes
end Magnification
end Pnp3
