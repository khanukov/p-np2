import LowerBounds.AC0_GapMCSP_Final

/-!
  pnp3/LowerBounds/AC0_GapMCSP.lean

  Paper-facing AC0 lower-bound surface for the Partial-MCSP track.

  This is the preferred import path for the restricted-model result.  It keeps
  the theorem names closer to standard complexity-theory prose (`in_AC0`,
  `not_in_AC0`) while reusing the implementation layer in
  `LowerBounds.AC0_GapMCSP_Final`.
-/

namespace Pnp3
namespace LowerBounds

open Models

/--
Paper-facing "in AC0" predicate for the active fixed-slice Partial-MCSP
formalization.

At the current repository boundary this is defined through the structured
semantic solver interface `SmallAC0Solver_Partial`.
-/
def GapPartialMCSP_in_AC0 (p : GapPartialMCSPParams) : Prop :=
  ∃ _solver : SmallAC0Solver_Partial p, True

/--
Paper-facing "not in AC0" predicate for the active fixed-slice Partial-MCSP
formalization.
-/
def GapPartialMCSP_not_in_AC0 (p : GapPartialMCSPParams) : Prop :=
  ¬ GapPartialMCSP_in_AC0 p

/--
Pointwise semantic AC0-solver exclusion for the fixed slice `p`.
-/
theorem gapPartialMCSP_no_semantic_AC0_solver
    (p : GapPartialMCSPParams) :
    ∀ _solver : SmallAC0Solver_Partial p, False :=
  gapPartialMCSP_noSmallAC0Solver p

/--
Pointwise syntactic-package AC0-solver exclusion for the fixed slice `p`.
-/
theorem gapPartialMCSP_no_syntactic_AC0_solver
    (p : GapPartialMCSPParams) :
    ∀ _solver : SmallAC0Solver_Partial_Syntactic p, False :=
  gapPartialMCSP_noSyntacticSmallAC0Solver p

/--
Pointwise constructive-package AC0-solver exclusion for the fixed slice `p`.
-/
theorem gapPartialMCSP_no_constructive_AC0_solver
    (p : GapPartialMCSPParams) :
    ∀ _solver : ConstructiveSmallAC0Solver_Partial p, False :=
  gapPartialMCSP_noConstructiveSmallAC0Solver p

/--
Main paper-facing restricted-model theorem:
the fixed-slice Partial-MCSP target is not in AC0 under the active structured
solver interface.
-/
theorem gapPartialMCSP_not_in_AC0
    (p : GapPartialMCSPParams) :
    GapPartialMCSP_not_in_AC0 p := by
  intro hIn
  rcases hIn with ⟨solver, _⟩
  exact gapPartialMCSP_no_semantic_AC0_solver p solver

/--
Compatibility alias from the paper-facing theorem back to the implementation
predicate used in `AC0_GapMCSP_Final`.
-/
theorem gapPartialMCSP_notInSmallAC0_of_not_in_AC0
    (p : GapPartialMCSPParams) :
    GapPartialMCSP_NotInSmallAC0 p := by
  intro hExists
  exact gapPartialMCSP_not_in_AC0 p hExists

/--
The implementation predicate and the paper-facing predicate are definitionally
equivalent.
-/
theorem gapPartialMCSP_not_in_AC0_iff_notInSmallAC0
    (p : GapPartialMCSPParams) :
    GapPartialMCSP_not_in_AC0 p ↔ GapPartialMCSP_NotInSmallAC0 p := by
  rfl

end LowerBounds
end Pnp3
