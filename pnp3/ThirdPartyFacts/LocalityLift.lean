import Mathlib.Data.Finset.Basic
import Facts.LocalityLift.Exports
import Models.Model_GapMCSP
import LowerBounds.AntiChecker
import ThirdPartyFacts.Facts_Switching
import Core.BooleanBasics
import Magnification.LocalityInterfaces -- for SmallGeneralCircuitSolver definition

/-!
  Bridge between the stand-alone `Facts.LocalityLift` package and the internal
  `pnp3` representations of GapMCSP solvers.  The code is intentionally verbose:
  every conversion is documented so that future refactors (e.g. moving the
  internal wrappers to the external package) remain transparent.

  ⚠️ **Текущий статус.** Пакет `Facts/LocalityLift` пока использует
  консервативный (одноточечный) свидетель локализации.  Финальное доказательство
  должно заменить его на shrinkage-свидетель из теоремы A.2
  (`shrinkage_for_localCircuit`).  Как только в шаге A появится внешнее
  `LocalCircuitWitness`, необходимо вернуться в этот модуль и обновить
  импортируемый свидетель (см. README подпроекта для подробностей).  До тех пор
  интерфейс остаётся совместимым и позволяет приостановить работу, не теряя
  контекст.
-/

namespace Pnp3
namespace ThirdPartyFacts

open Facts.LocalityLift
open Models
open LowerBounds
open Magnification

/-- Turn internal GapMCSP parameters into the external record. -/
@[simp] def toFactsParams (p : Models.GapMCSPParams) :
    Facts.LocalityLift.GapMCSPParams :=
  { n := p.n }

/-- Input length is preserved by the conversion. -/
@[simp] lemma inputLen_toFacts (p : Models.GapMCSPParams) :
    Facts.LocalityLift.inputLen (toFactsParams p) = Models.inputLen p := by
  rfl

/-- Polylog budget is preserved by the conversion. -/
@[simp] lemma polylogBudget_toFacts (p : Models.GapMCSPParams) :
    Facts.LocalityLift.polylogBudget
        (Facts.LocalityLift.inputLen (toFactsParams p)) =
      Models.polylogBudget (Models.inputLen p) := by
  rfl

/-- Lift a general solver into the external representation. -/
@[simp] def toFactsGeneralSolver
    {p : Models.GapMCSPParams}
    (solver : Magnification.SmallGeneralCircuitSolver p) :
    Facts.LocalityLift.SmallGeneralCircuitSolver (toFactsParams p) :=
  {
    params :=
      {
        n := solver.params.params.n
        size := solver.params.params.size
        depth := solver.params.params.depth
      }
    same_n := by
      -- both input length predicates reduce to `Nat.pow 2 p.n`
      simpa [toFactsParams, Facts.LocalityLift.inputLen, Models.inputLen]
        using solver.params.same_n
  }

/-- Push external local parameters back to the internal record. -/
@[simp] def fromFactsLocalParameters
    (params : Facts.LocalityLift.LocalCircuitParameters) :
    ThirdPartyFacts.LocalCircuitParameters :=
  {
    n := params.n
    M := params.M
    ℓ := params.ℓ
    depth := params.depth
  }

/-- Convert external local solvers into the internal parameter wrapper. -/
@[simp] def fromFactsLocalParams
    {p : Models.GapMCSPParams}
    (solver : Facts.LocalityLift.SmallLocalCircuitSolver (toFactsParams p)) :
    LowerBounds.SmallLocalCircuitParams p :=
  {
    params := fromFactsLocalParameters solver.params
    same_n := by
      simpa [fromFactsLocalParameters, toFactsParams,
        Facts.LocalityLift.inputLen, Models.inputLen] using solver.same_n
    small := by
      -- Внешний интерфейс уже хранит численное условие "малости".
      simpa [Facts.LocalityLift.LocalCircuitSmallEnough,
        ThirdPartyFacts.LocalCircuitSmallEnough, fromFactsLocalParameters]
        using solver.small
  }

/-- Convert internal local solvers into the external wrapper. -/
@[simp] def toFactsLocalSolver
    {p : Models.GapMCSPParams}
    (solver : LowerBounds.SmallLocalCircuitSolver p) :
    Facts.LocalityLift.SmallLocalCircuitSolver (toFactsParams p) :=
  {
    params :=
      {
        n := solver.params.params.n
        M := solver.params.params.M
        ℓ := solver.params.params.ℓ
        depth := solver.params.params.depth
      }
    same_n := by
      simpa [toFactsParams, Facts.LocalityLift.inputLen, Models.inputLen]
        using solver.params.same_n
    small := by
      simpa [Facts.LocalityLift.LocalCircuitSmallEnough,
        ThirdPartyFacts.LocalCircuitSmallEnough, toFactsParams]
        using solver.params.small
  }

/-- Specialised version of the locality-lift interface for the internal types. -/
def locality_lift
  {p : Models.GapMCSPParams}
  (solver : Magnification.SmallGeneralCircuitSolver p) :
    ∃ (T : Finset (Core.BitVec (Models.inputLen p)))
      (loc : LowerBounds.SmallLocalCircuitSolver p),
        T.card ≤ Models.polylogBudget (Models.inputLen p) ∧
        loc.params.params.M ≤ solver.params.params.size * (T.card.succ) ∧
        loc.params.params.ℓ ≤ Models.polylogBudget (Models.inputLen p) ∧
        loc.params.params.depth ≤ solver.params.params.depth := by
  classical
  obtain ⟨T, locFacts, hT, hM, hℓ, hdepth⟩ :=
    Facts.LocalityLift.locality_lift (toFactsGeneralSolver solver)
  let localParams : LowerBounds.SmallLocalCircuitParams p :=
    fromFactsLocalParams (p := p) locFacts
  let localSolver : LowerBounds.SmallLocalCircuitSolver p :=
    { params := localParams
      decide := solver.decide
      correct := solver.correct }
  refine ⟨T, localSolver, ?_, ?_, ?_, ?_⟩
  · simpa [polylogBudget_toFacts, inputLen_toFacts]
      using hT
  · simpa [localParams, localSolver, fromFactsLocalParams]
      using hM
  · simpa [polylogBudget_toFacts, inputLen_toFacts, localParams, localSolver,
      fromFactsLocalParams]
      using hℓ
  · simpa [localParams, localSolver, fromFactsLocalParams]
      using hdepth

/-- Contrapositive wrapper specialised to the internal types. -/
def no_general_solver_of_no_local
  {p : Models.GapMCSPParams}
  (H : ∀ _solver : LowerBounds.SmallLocalCircuitSolver p, False) :
  ∀ _solver : Magnification.SmallGeneralCircuitSolver p, False := by
  classical
  intro solver
  have : ∀ solver' : Facts.LocalityLift.SmallLocalCircuitSolver (toFactsParams p),
      False := by
    intro solver'
    -- Используем стандартную локализацию и корректность из внешнего witness.
    let localParams : LowerBounds.SmallLocalCircuitParams p :=
      fromFactsLocalParams (p := p) solver'
    let localSolver : LowerBounds.SmallLocalCircuitSolver p :=
      { params := localParams
        decide := solver.decide
        correct := solver.correct }
    exact H localSolver
  have h := Facts.LocalityLift.no_general_solver_of_no_local (p := toFactsParams p) this
  simpa using h (toFactsGeneralSolver solver)

end ThirdPartyFacts
end Pnp3
