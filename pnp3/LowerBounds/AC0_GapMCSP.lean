import LowerBounds.AC0_GapMCSP_Final

/-!
  pnp3/LowerBounds/AC0_GapMCSP.lean

  Deprecated compatibility quarantine for the former Partial-MCSP AC0 surface.

  The standard-looking `in_AC0` / `not_in_AC0` names below range over
  `SmallAC0Solver_Partial`, whose `easyData` and `params` fields are already
  inconsistent without solver correctness.  New code should use the explicitly
  enriched names in `LowerBounds.AC0_GapMCSP_Final`.  Nothing in this module is
  a standard AC0 lower bound.
-/

namespace Pnp3
namespace LowerBounds

open Models

-- This entire module is a deprecated compatibility quarantine.
set_option linter.deprecated false

/--
Paper-facing "in AC0" predicate for the active fixed-slice Partial-MCSP
formalization.

This historical name does not denote standard AC0 membership.  Its witness is
the enriched `SmallAC0Solver_Partial` package.
-/
@[deprecated EnrichedSmallAC0PackagePartialExists (since := "2026-08-17")]
def GapPartialMCSP_in_AC0 (p : GapPartialMCSPParams) : Prop :=
  EnrichedSmallAC0PackagePartialExists p

/--
Deprecated negation of the enriched-package existence predicate.  This is not
standard AC0 non-membership.
-/
@[deprecated EnrichedSmallAC0PackagePartialInconsistent (since := "2026-08-17")]
def GapPartialMCSP_not_in_AC0 (p : GapPartialMCSPParams) : Prop :=
  ¬ GapPartialMCSP_in_AC0 p

/--
Deprecated compatibility theorem for the enriched package.
-/
@[deprecated false_of_enrichedSmallAC0PackagePartial (since := "2026-08-17")]
theorem gapPartialMCSP_no_semantic_AC0_solver
    (p : GapPartialMCSPParams) :
    ∀ _solver : SmallAC0Solver_Partial p, False :=
  false_of_enrichedSmallAC0PackagePartial p

/--
Deprecated compatibility theorem for a thin wrapper around the enriched package.
-/
@[deprecated false_of_enrichedSmallAC0PackagePartial (since := "2026-08-17")]
theorem gapPartialMCSP_no_syntactic_AC0_solver
    (p : GapPartialMCSPParams) :
    ∀ _solver : SmallAC0Solver_Partial_Syntactic p, False :=
  fun solver => false_of_enrichedSmallAC0PackagePartial p
    solver.toSmallAC0Solver_Partial

/--
Deprecated compatibility theorem for a thin wrapper around the enriched package.
-/
@[deprecated false_of_enrichedSmallAC0PackagePartial (since := "2026-08-17")]
theorem gapPartialMCSP_no_constructive_AC0_solver
    (p : GapPartialMCSPParams) :
    ∀ _solver : ConstructiveSmallAC0Solver_Partial p, False :=
  fun solver => false_of_enrichedSmallAC0PackagePartial p
    solver.toSmallAC0Solver_Partial

/--
Deprecated zero-hypothesis endpoint.  It proves only that the enriched package
cannot exist, because `params` and `easyData` already imply `False`.
-/
@[deprecated not_exists_enrichedSmallAC0PackagePartial (since := "2026-08-17")]
theorem gapPartialMCSP_not_in_AC0
    (p : GapPartialMCSPParams) :
    GapPartialMCSP_not_in_AC0 p := by
  exact not_exists_enrichedSmallAC0PackagePartial p

/--
Deprecated compatibility alias between two historical names for the same
enriched-package inconsistency.
-/
@[deprecated not_exists_enrichedSmallAC0PackagePartial (since := "2026-08-17")]
theorem gapPartialMCSP_notInSmallAC0_of_not_in_AC0
    (p : GapPartialMCSPParams) :
    GapPartialMCSP_NotInSmallAC0 p := by
  exact not_exists_enrichedSmallAC0PackagePartial p

/--
Deprecated definitional equivalence between the two historical predicates.
-/
@[deprecated EnrichedSmallAC0PackagePartialInconsistent (since := "2026-08-17")]
theorem gapPartialMCSP_not_in_AC0_iff_notInSmallAC0
    (p : GapPartialMCSPParams) :
    GapPartialMCSP_not_in_AC0 p ↔ GapPartialMCSP_NotInSmallAC0 p := by
  rfl

end LowerBounds
end Pnp3
