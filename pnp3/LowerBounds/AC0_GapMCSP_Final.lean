import Magnification.PipelineStatements_Partial

/-!
  pnp3/LowerBounds/AC0_GapMCSP_Final.lean

  Publishable AC0 endpoint for the Partial-MCSP track.

  This module isolates the strongest current in-repo AC0 lower-bound surface
  that:

  * is unconditional inside the active tree;
  * does not depend on the refuted formula-side support-bounds route;
  * does not mention `ResearchGapWitness` or the DAG/P-vs-NP final layer.

  The statement is intentionally phrased in terms of the active structured
  solver interface `SmallAC0Solver_Partial`.  That is the honest public surface
  currently supported by the formalization.
-/

namespace Pnp3
namespace LowerBounds

open Models

/--
Public fixed-slice AC0 lower-bound statement for the active Partial-MCSP
formalization.

This does not claim a standard external complexity-class theorem yet; it says
that the repository's structured notion of a small AC0 solver for the promise
problem cannot exist for the fixed parameter package `p`.
-/
def GapPartialMCSP_NotInSmallAC0 (p : GapPartialMCSPParams) : Prop :=
  ¬ ∃ _solver : SmallAC0Solver_Partial p, True

/--
Pointwise internalized AC0 contradiction for semantic small-AC0 solvers.

No external closure/provider/lift hypothesis is needed at this surface.
-/
theorem gapPartialMCSP_noSmallAC0Solver
    (p : GapPartialMCSPParams) :
    ∀ _solver : SmallAC0Solver_Partial p, False := by
  intro solver
  exact LB_Formulas_core_partial_closed_internalized (solver := solver)

/--
Closed-world syntactic packaging variant of the same AC0 contradiction.
-/
theorem gapPartialMCSP_noSyntacticSmallAC0Solver
    (p : GapPartialMCSPParams) :
    ∀ _solver : SmallAC0Solver_Partial_Syntactic p, False := by
  intro solver
  exact Magnification.ac0_statement_from_pipeline_partial_closed p solver

/--
Constructive packaging variant of the same AC0 contradiction.
-/
theorem gapPartialMCSP_noConstructiveSmallAC0Solver
    (p : GapPartialMCSPParams) :
    ∀ _solver : ConstructiveSmallAC0Solver_Partial p, False := by
  intro solver
  exact Magnification.ac0_statement_from_pipeline_partial_constructive p solver

/--
Existential "no semantic small AC0 solver exists" form of the publishable
endpoint.
-/
theorem gapPartialMCSP_notInSmallAC0
    (p : GapPartialMCSPParams) :
    GapPartialMCSP_NotInSmallAC0 p := by
  intro hExists
  rcases hExists with ⟨solver, _⟩
  exact gapPartialMCSP_noSmallAC0Solver p solver

/--
Existential closed-world syntactic form of the AC0 lower bound.
-/
theorem gapPartialMCSP_notInSmallAC0_syntactic
    (p : GapPartialMCSPParams) :
    ¬ ∃ _solver : SmallAC0Solver_Partial_Syntactic p, True := by
  intro hExists
  rcases hExists with ⟨solver, _⟩
  exact gapPartialMCSP_noSyntacticSmallAC0Solver p solver

/--
Existential constructive form of the AC0 lower bound.
-/
theorem gapPartialMCSP_notInSmallAC0_constructive
    (p : GapPartialMCSPParams) :
    ¬ ∃ _solver : ConstructiveSmallAC0Solver_Partial p, True := by
  intro hExists
  rcases hExists with ⟨solver, _⟩
  exact gapPartialMCSP_noConstructiveSmallAC0Solver p solver

end LowerBounds
end Pnp3
