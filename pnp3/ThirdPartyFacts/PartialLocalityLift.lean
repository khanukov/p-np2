import Mathlib.Data.Finset.Basic
import Facts.LocalityLift.Exports
import Models.Model_PartialMCSP
import LowerBounds.AntiChecker_Partial
import ThirdPartyFacts.Facts_Switching
import Core.BooleanBasics
import Magnification.LocalityInterfaces_Partial

/-!
  Bridge between the stand-alone `Facts/LocalityLift` package and the internal
  Partial MCSP solver wrappers.  The external package uses the legacy name
  `GapMCSPParams` for its *numeric* parameters; we only reuse that record as a
  length container.  We map Partial MCSP parameters by shifting `n ↦ n+1`,
  so that input lengths coincide:

    inputLen (n+1) = 2^(n+1) = 2 * 2^n = partialInputLen n.
-/

namespace Pnp3
namespace ThirdPartyFacts

open Facts.LocalityLift
open Models
open LowerBounds
open Magnification

@[simp] def toFactsParamsPartial (p : Models.GapPartialMCSPParams) :
    Facts.LocalityLift.GapMCSPParams :=
  { n := p.n + 1 }

@[simp] lemma inputLen_toFactsPartial (p : Models.GapPartialMCSPParams) :
    Facts.LocalityLift.inputLen (toFactsParamsPartial p) = Models.partialInputLen p := by
  simp [toFactsParamsPartial, Facts.LocalityLift.inputLen, Models.partialInputLen,
    Partial.inputLen, Partial.tableLen, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc]

@[simp] lemma inputLen_toFactsPartial' (p : Models.GapPartialMCSPParams) :
    Facts.LocalityLift.inputLen { n := p.n + 1 } = Models.partialInputLen p := by
  simpa [toFactsParamsPartial] using inputLen_toFactsPartial p

@[simp] lemma polylogBudget_toFactsPartial (p : Models.GapPartialMCSPParams) :
    Facts.LocalityLift.polylogBudget
        (Facts.LocalityLift.inputLen (toFactsParamsPartial p)) =
      Models.polylogBudget (Models.partialInputLen p) := by
  simp [Facts.LocalityLift.polylogBudget, Models.polylogBudget, inputLen_toFactsPartial,
    toFactsParamsPartial]

@[simp] lemma polylogBudget_toFactsPartial' (p : Models.GapPartialMCSPParams) :
    Facts.LocalityLift.polylogBudget
        (Facts.LocalityLift.inputLen { n := p.n + 1 }) =
      Models.polylogBudget (Models.partialInputLen p) := by
  simpa [toFactsParamsPartial] using polylogBudget_toFactsPartial p

@[simp] lemma card_cast {α β : Type} (h : α = β) (s : Finset α) :
    (cast (congrArg Finset h) s).card = s.card := by
  cases h
  rfl

@[simp] def toFactsGeneralSolverPartial
    {p : Models.GapPartialMCSPParams}
    (solver : Magnification.SmallGeneralCircuitSolver_Partial p) :
    Facts.LocalityLift.SmallGeneralCircuitSolver (toFactsParamsPartial p) :=
  {
    params :=
      {
        n := solver.params.params.n
        size := solver.params.params.size
        depth := solver.params.params.depth
      }
    same_n := by
      simpa [toFactsParamsPartial, Facts.LocalityLift.inputLen,
        Models.partialInputLen, Partial.inputLen, Partial.tableLen, Nat.pow_succ, Nat.mul_comm,
        Nat.mul_left_comm, Nat.mul_assoc]
        using solver.params.same_n
  }

@[simp] def fromFactsLocalParametersPartial
    (params : Facts.LocalityLift.LocalCircuitParameters) :
    ThirdPartyFacts.LocalCircuitParameters :=
  {
    n := params.n
    M := params.M
    ℓ := params.ℓ
    depth := params.depth
  }

@[simp] def fromFactsLocalParamsPartial
    {p : Models.GapPartialMCSPParams}
    (solver : Facts.LocalityLift.SmallLocalCircuitSolver (toFactsParamsPartial p)) :
    LowerBounds.SmallLocalCircuitParamsPartial p :=
  {
    params := fromFactsLocalParametersPartial solver.params
    same_n := by
      simpa [fromFactsLocalParametersPartial, toFactsParamsPartial,
        Facts.LocalityLift.inputLen, Models.partialInputLen,
        Partial.inputLen, Partial.tableLen, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc] using solver.same_n
    small := by
      simpa [Facts.LocalityLift.LocalCircuitSmallEnough,
        ThirdPartyFacts.LocalCircuitSmallEnough, fromFactsLocalParametersPartial]
        using solver.small
  }

@[simp] def toFactsLocalSolverPartial
    {p : Models.GapPartialMCSPParams}
    (solver : LowerBounds.SmallLocalCircuitSolver_Partial p) :
    Facts.LocalityLift.SmallLocalCircuitSolver (toFactsParamsPartial p) :=
  {
    params :=
      {
        n := solver.params.params.n
        M := solver.params.params.M
        ℓ := solver.params.params.ℓ
        depth := solver.params.params.depth
      }
    same_n := by
      simpa [toFactsParamsPartial, Facts.LocalityLift.inputLen,
        Models.partialInputLen, Partial.inputLen, Partial.tableLen, Nat.pow_succ, Nat.mul_comm,
        Nat.mul_left_comm, Nat.mul_assoc]
        using solver.params.same_n
    small := by
      simpa [Facts.LocalityLift.LocalCircuitSmallEnough,
        ThirdPartyFacts.LocalCircuitSmallEnough, toFactsParamsPartial]
        using solver.params.small
  }

def locality_lift_partial
  {p : Models.GapPartialMCSPParams}
  (solver : Magnification.SmallGeneralCircuitSolver_Partial p) :
    ∃ (T : Finset (Core.BitVec (Models.partialInputLen p)))
      (loc : LowerBounds.SmallLocalCircuitSolver_Partial p),
        T.card ≤ Models.polylogBudget (Models.partialInputLen p) ∧
        loc.params.params.M ≤ solver.params.params.size * (T.card.succ) ∧
        loc.params.params.ℓ ≤ Models.polylogBudget (Models.partialInputLen p) ∧
        loc.params.params.depth ≤ solver.params.params.depth := by
  classical
  obtain ⟨T, locFacts, hT, hM, hℓ, hdepth⟩ :=
    Facts.LocalityLift.locality_lift (toFactsGeneralSolverPartial solver)
  let localParams : LowerBounds.SmallLocalCircuitParamsPartial p :=
    fromFactsLocalParamsPartial (p := p) locFacts
  let localSolver : LowerBounds.SmallLocalCircuitSolver_Partial p :=
    { params := localParams
      decide := solver.decide
      correct := solver.correct }
  refine ⟨(by
    simpa [Facts.LocalityLift.BitVec, Core.BitVec, inputLen_toFactsPartial,
      toFactsParamsPartial] using T),
    localSolver, ?_, ?_, ?_, ?_⟩
  · simpa [polylogBudget_toFactsPartial]
      using hT
  · simpa [localParams, localSolver, fromFactsLocalParamsPartial]
      using hM
  · simpa [polylogBudget_toFactsPartial, toFactsParamsPartial, localParams, localSolver,
      fromFactsLocalParamsPartial]
      using hℓ
  · simpa [localParams, localSolver, fromFactsLocalParamsPartial]
      using hdepth

def no_general_solver_of_no_local_partial
  {p : Models.GapPartialMCSPParams}
  (H : ∀ _solver : LowerBounds.SmallLocalCircuitSolver_Partial p, False) :
  ∀ _solver : Magnification.SmallGeneralCircuitSolver_Partial p, False := by
  classical
  intro solver
  have : ∀ solver' : Facts.LocalityLift.SmallLocalCircuitSolver (toFactsParamsPartial p),
      False := by
    intro solver'
    let localParams : LowerBounds.SmallLocalCircuitParamsPartial p :=
      fromFactsLocalParamsPartial (p := p) solver'
    let localSolver : LowerBounds.SmallLocalCircuitSolver_Partial p :=
      { params := localParams
        decide := solver.decide
        correct := solver.correct }
    exact H localSolver
  have h := Facts.LocalityLift.no_general_solver_of_no_local (p := toFactsParamsPartial p) this
  simpa using h (toFactsGeneralSolverPartial solver)

end ThirdPartyFacts
end Pnp3
