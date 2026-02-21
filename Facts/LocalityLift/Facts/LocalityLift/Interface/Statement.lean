import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Facts.LocalityLift.Interface.Parameters
import Facts.LocalityLift.Proof.Witness

/-!
# Locality-lift interface (witness-driven API)

This module packages the Lean-facing statement of locality lift.  The actual
construction of witnesses is delegated to `Proof.Witness`, which currently
stores the outstanding axiomatisation; once the shrinkage-based argument is
formalised, `Proof.Witness` will provide a genuine constructive definition.
-/

namespace Facts
namespace LocalityLift

/--
Locality-lift theorem (interface version).

Given a small general GapMCSP solver, we can extract:
* a polylogarithmic test-set `T` of inputs, and
* a local solver whose size, locality and depth are tightly controlled.

The inequalities are intentionally identical to the original axiom D.5 so that
downstream code in `pnp3` can adopt the final proof with zero churn.
-/
-- Restatement of the witness in the traditional tuple form.
theorem locality_lift
  {p : GapMCSPParams}
  (general : SmallGeneralCircuitSolver p)
  [ShrinkageWitness.Provider (p := p) general] :
    ∃ (T : Finset (BitVec (inputLen p)))
      (loc : SmallLocalCircuitSolver p),
        T.card ≤ polylogBudget (inputLen p) ∧
        loc.params.M ≤ general.params.size * (T.card.succ) ∧
        loc.params.ℓ ≤ polylogBudget (inputLen p) ∧
        loc.params.depth ≤ general.params.depth := by
  classical
  let witness := localityWitness (p := p) general
  refine
    ⟨witness.testSet, witness.toLocalSolver, witness.testSet_card_le,
      ?_, witness.locality_le, witness.depth_le⟩
  simpa [Facts.LocalityLift.LocalityWitness.toLocalSolver_params] using witness.size_le

/--
Contrapositive wrapper used by the magnification pipeline: once Step C rules
out local solvers, this lemma forbids a general solver with matching parameters.
-/
theorem no_general_solver_of_no_local
  {p : GapMCSPParams}
  (H : ∀ _solver : SmallLocalCircuitSolver p, False)
  (general : SmallGeneralCircuitSolver p)
  [ShrinkageWitness.Provider (p := p) general] : False := by
  obtain ⟨T, loc, -, -, -, -⟩ := locality_lift (p := p) general
  exact H loc

end LocalityLift
end Facts
