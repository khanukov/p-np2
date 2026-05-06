import Magnification.AuditRoutes.LogWidthAdversary.Family_NatLog2

/-!
# Support-cardinality barrier: canonical hardwiring family (T1)

Slot T1 for `seed_packs/fp3b4_support_cardinality_barrier/`.

This module supplies only the canonical hardwiring formula family and the
language it decides.  It deliberately stops before the later slots:

* no support-cardinality theorem (`T2`),
* no `InPpolyFormula` witness packaging (`T3`),
* no support-cardinality-only predicate or barrier theorem (`T4`/`T5`).

Progress category: side-track audit infrastructure.  The construction reuses
`prefixAnd` from the already-formalized log-width adversary route, but makes the
window an arbitrary function `s : Nat → Nat` with an explicit proof that every
selected prefix fits inside the ambient input length.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace SupportCardinalityBarrier

open Pnp3.ComplexityInterfaces
open Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.LogWidthAdversary
  (prefixAnd)

/--
Canonical hardwiring family for an arbitrary support-size profile.

At input length `n`, the formula is the conjunction of the first `s n` input
coordinates.  The hypothesis `hs n : s n ≤ n` is the only side condition needed
by `prefixAnd` to embed those prefix coordinates into `Fin n`.

The exact support-cardinality statement
`(FormulaCircuit.support (canonicalHardwiringFamily s hs n)).card = s n` is
intentionally left to the T2 module; this T1 surface only defines the family.
-/
def canonicalHardwiringFamily
    (s : Nat → Nat) (hs : ∀ n, s n ≤ n) (n : Nat) : FormulaCircuit n :=
  prefixAnd n (s n) (hs n)

/--
The language decided by `canonicalHardwiringFamily`.

For each length `n`, membership is by direct evaluation of the canonical
hardwired prefix-AND formula at that length.  This definition is designed so the
future T3 witness can use judgmental correctness (`rfl`) without adding any
semantic bridge in this T1 file.
-/
def canonicalHardwiringLanguage
    (s : Nat → Nat) (hs : ∀ n, s n ≤ n) : Language :=
  fun n x => FormulaCircuit.eval (canonicalHardwiringFamily s hs n) x

end SupportCardinalityBarrier
end AuditRoutes
end Magnification
end Pnp3
