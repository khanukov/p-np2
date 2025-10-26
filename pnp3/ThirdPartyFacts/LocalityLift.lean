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
  должно заменить его на результат, полученный из шринкаж-факта A.2
  (`shrinkage_for_localCircuit`).  Как только Step A будет завершён, необходимо
  вернуться в этот модуль и обновить импортируемый свидетель (см. README
  подпроекта для подробностей).  До тех пор интерфейс остаётся совместимым и
  позволяет приостановить работу, не теряя контекст.
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
        n := solver.params.n
        size := solver.params.size
        depth := solver.params.depth
      }
    same_n := by
      -- both input length predicates reduce to `Nat.pow 2 p.n`
      simpa [toFactsParams, Facts.LocalityLift.inputLen, Models.inputLen]
        using solver.same_n
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

/-- Convert external local solvers into the internal wrapper. -/
@[simp] def fromFactsLocalSolver
    {p : Models.GapMCSPParams}
    (solver : Facts.LocalityLift.SmallLocalCircuitSolver (toFactsParams p)) :
    LowerBounds.SmallLocalCircuitSolver p :=
  {
    params := fromFactsLocalParameters solver.params
    same_n := by
      simpa [fromFactsLocalParameters, toFactsParams,
        Facts.LocalityLift.inputLen, Models.inputLen] using solver.same_n
  }

/-- Convert internal local solvers into the external wrapper. -/
@[simp] def toFactsLocalSolver
    {p : Models.GapMCSPParams}
    (solver : LowerBounds.SmallLocalCircuitSolver p) :
    Facts.LocalityLift.SmallLocalCircuitSolver (toFactsParams p) :=
  {
    params :=
      {
        n := solver.params.n
        M := solver.params.M
        ℓ := solver.params.ℓ
        depth := solver.params.depth
      }
    same_n := by
      simpa [toFactsParams, Facts.LocalityLift.inputLen, Models.inputLen]
        using solver.same_n
  }

/-- Specialised version of the locality-lift interface for the internal types. -/
def locality_lift
  {p : Models.GapMCSPParams}
  (solver : Magnification.SmallGeneralCircuitSolver p) :
    ∃ (T : Finset (Core.BitVec (Models.inputLen p)))
      (loc : LowerBounds.SmallLocalCircuitSolver p),
        T.card ≤ Models.polylogBudget (Models.inputLen p) ∧
        loc.params.M ≤ solver.params.size * (T.card.succ) ∧
        loc.params.ℓ ≤ Models.polylogBudget (Models.inputLen p) ∧
        loc.params.depth ≤ solver.params.depth := by
  classical
  obtain ⟨T, locFacts, hT, hM, hℓ, hdepth⟩ :=
    Facts.LocalityLift.locality_lift (toFactsGeneralSolver solver)
  refine ⟨T, fromFactsLocalSolver (p := p) locFacts, ?_, ?_, ?_, ?_⟩
  · simpa [polylogBudget_toFacts, inputLen_toFacts]
      using hT
  · simpa [fromFactsLocalSolver]
      using hM
  · simpa [polylogBudget_toFacts, inputLen_toFacts, fromFactsLocalSolver]
      using hℓ
  · simpa [fromFactsLocalSolver]
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
    exact H (fromFactsLocalSolver (p := p) solver')
  have h := Facts.LocalityLift.no_general_solver_of_no_local (p := toFactsParams p) this
  simpa using h (toFactsGeneralSolver solver)

end ThirdPartyFacts
end Pnp3
