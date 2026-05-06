import Complexity.Interfaces

/-!
# Support-cardinality-only filters

Slot T4 for `seed_packs/fp3b4_support_cardinality_barrier/`.

This audit-route module isolates the *invariance predicate* needed by the later
support-cardinality barrier theorem.  A filter `Π` on strict
`InPpolyFormula` witnesses is support-cardinality-only when it is unable to
distinguish two witnesses whose support-cardinality functions agree at every
input length.

Progress category: infrastructure / side-track audit formalization.  This file
only defines the invariant used by the fp3b4 barrier work.  It does **not**
construct the canonical hardwiring family, does **not** prove the barrier
headline theorem, and does **not** apply the barrier to
`FP3Attempt.InSupportFunctionalDiversity`.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace SupportCardinalityBarrier

open Pnp3.ComplexityInterfaces

/--
The support-cardinality profile of a strict formula witness.

At length `n`, this records only the number of syntactically mentioned input
coordinates in the `n`-th formula.  It intentionally forgets the language, the
formula shape, gate labels, depth, polynomial bound, and semantic behaviour.
-/
def supportCardinalityProfile {L : Language} (w : InPpolyFormula L) : Nat → Nat :=
  fun n => (FormulaCircuit.support (w.family n)).card

/--
A predicate/filter on `InPpolyFormula` witnesses is support-cardinality-only if
it is invariant under equality of support-cardinality profiles.

Equivalently: for any two witnesses, possibly for different languages, if their
functions

`n ↦ |support (family n)|`

are equal at every length, then the filter gives the same truth value on both
witnesses.  The definition is deliberately weak: it is only an extensionality
condition for the forgotten support-cardinality profile, not a claim that such a
profile is sufficient to prove any lower bound.
-/
def IsSupportCardinalityOnly
    (Filter : ∀ {L : Language}, InPpolyFormula L → Prop) : Prop :=
  ∀ {L₁ L₂ : Language} (w₁ : InPpolyFormula L₁) (w₂ : InPpolyFormula L₂),
    supportCardinalityProfile w₁ = supportCardinalityProfile w₂ →
      (Filter w₁ ↔ Filter w₂)

/-- Smoke theorem: the T4 module is wired into the build. -/
theorem isSupportCardinalityOnly_loaded : True := trivial

/--
Minimal unfolding lemma for the intended invariant.

Later slots can use this directly: after establishing equality of the support
cardinality functions for two witnesses, a support-cardinality-only filter
transports membership across the pair.
-/
theorem IsSupportCardinalityOnly.apply
    {Filter : ∀ {L : Language}, InPpolyFormula L → Prop}
    (hFilter : IsSupportCardinalityOnly Filter)
    {L₁ L₂ : Language} (w₁ : InPpolyFormula L₁) (w₂ : InPpolyFormula L₂)
    (hProfile : ∀ n,
      (FormulaCircuit.support (w₁.family n)).card =
        (FormulaCircuit.support (w₂.family n)).card) :
    Filter w₁ ↔ Filter w₂ := by
  apply hFilter w₁ w₂
  funext n
  exact hProfile n

end SupportCardinalityBarrier
end AuditRoutes
end Magnification
end Pnp3
