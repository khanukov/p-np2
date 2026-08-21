import Magnification.PipelineStatements_Partial

/-!
  pnp3/LowerBounds/AC0_GapMCSP_Final.lean

  Audit surface for the former Partial-MCSP AC0 endpoint.

  `SmallAC0Solver_Partial` is not merely a standard AC0 solver interface: its
  `easyData` field asserts an AC0-realizable family with all-functions-scale
  cardinality.  Together with `params.union_small`, that payload is already
  inconsistent.  The canonical statements below name the enriched package and
  expose that vacuity directly.  No standard `GapPartialMCSP ∉ AC0` claim is
  made by this module.
-/

namespace Pnp3
namespace LowerBounds

open Models

-- Compatibility declarations below intentionally mention deprecated names.
set_option linter.deprecated false

/-- Existence of the repository's enriched, internally inconsistent package. -/
def EnrichedSmallAC0PackagePartialExists (p : GapPartialMCSPParams) : Prop :=
  ∃ _package : SmallAC0Solver_Partial p, True

/-- Explicit inconsistency predicate for the repository's enriched package. -/
def EnrichedSmallAC0PackagePartialInconsistent (p : GapPartialMCSPParams) : Prop :=
  ¬ EnrichedSmallAC0PackagePartialExists p

/--
Pointwise vacuity certificate for the enriched package.

The proof projects only `params` and `easyData`; it does not use the package's
semantic decider, semantic witness, correctness proof, circuit, or `decide_eq`.
-/
theorem false_of_enrichedSmallAC0PackagePartial
    (p : GapPartialMCSPParams) :
    ∀ _package : SmallAC0Solver_Partial p, False := by
  intro package
  exact false_of_smallAC0Params_and_easyFamilyData
    package.params package.easyData

/--
Existential form of the enriched-package inconsistency.
-/
theorem not_exists_enrichedSmallAC0PackagePartial
    (p : GapPartialMCSPParams) :
    EnrichedSmallAC0PackagePartialInconsistent p := by
  intro hExists
  rcases hExists with ⟨package, _⟩
  exact false_of_enrichedSmallAC0PackagePartial p package

/--
Deprecated compatibility predicate.  Despite its historical name, this only
negates existence of the enriched package above, not standard AC0 membership.
-/
@[deprecated EnrichedSmallAC0PackagePartialInconsistent (since := "2026-08-17")]
def GapPartialMCSP_NotInSmallAC0 (p : GapPartialMCSPParams) : Prop :=
  EnrichedSmallAC0PackagePartialInconsistent p

/--
Deprecated solver-shaped compatibility theorem.  The replacement explicitly
names the enriched package whose `params` and `easyData` fields are
inconsistent.
-/
@[deprecated false_of_enrichedSmallAC0PackagePartial (since := "2026-08-17")]
theorem gapPartialMCSP_noSmallAC0Solver
    (p : GapPartialMCSPParams) :
    ∀ _solver : SmallAC0Solver_Partial p, False :=
  false_of_enrichedSmallAC0PackagePartial p

/-- Deprecated compatibility theorem for the thin syntactic wrapper. -/
@[deprecated false_of_enrichedSmallAC0PackagePartial (since := "2026-08-17")]
theorem gapPartialMCSP_noSyntacticSmallAC0Solver
    (p : GapPartialMCSPParams) :
    ∀ _solver : SmallAC0Solver_Partial_Syntactic p, False := by
  intro solver
  exact false_of_enrichedSmallAC0PackagePartial p
    solver.toSmallAC0Solver_Partial

/-- Deprecated compatibility theorem for the thin constructive wrapper. -/
@[deprecated false_of_enrichedSmallAC0PackagePartial (since := "2026-08-17")]
theorem gapPartialMCSP_noConstructiveSmallAC0Solver
    (p : GapPartialMCSPParams) :
    ∀ _solver : ConstructiveSmallAC0Solver_Partial p, False := by
  intro solver
  exact false_of_enrichedSmallAC0PackagePartial p
    solver.toSmallAC0Solver_Partial

/-- Deprecated compatibility alias for the enriched-package inconsistency. -/
@[deprecated not_exists_enrichedSmallAC0PackagePartial (since := "2026-08-17")]
theorem gapPartialMCSP_notInSmallAC0
    (p : GapPartialMCSPParams) :
    GapPartialMCSP_NotInSmallAC0 p := by
  exact not_exists_enrichedSmallAC0PackagePartial p

/-- Deprecated existential compatibility theorem for the syntactic wrapper. -/
@[deprecated false_of_enrichedSmallAC0PackagePartial (since := "2026-08-17")]
theorem gapPartialMCSP_notInSmallAC0_syntactic
    (p : GapPartialMCSPParams) :
    ¬ ∃ _solver : SmallAC0Solver_Partial_Syntactic p, True := by
  intro hExists
  rcases hExists with ⟨solver, _⟩
  exact false_of_enrichedSmallAC0PackagePartial p
    solver.toSmallAC0Solver_Partial

/-- Deprecated existential compatibility theorem for the constructive wrapper. -/
@[deprecated false_of_enrichedSmallAC0PackagePartial (since := "2026-08-17")]
theorem gapPartialMCSP_notInSmallAC0_constructive
    (p : GapPartialMCSPParams) :
    ¬ ∃ _solver : ConstructiveSmallAC0Solver_Partial p, True := by
  intro hExists
  rcases hExists with ⟨solver, _⟩
  exact false_of_enrichedSmallAC0PackagePartial p
    solver.toSmallAC0Solver_Partial

end LowerBounds
end Pnp3
