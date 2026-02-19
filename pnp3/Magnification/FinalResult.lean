import Magnification.Bridge_to_Magnification_Partial
import Models.Model_PartialMCSP
import Complexity.Interfaces

/-!
  # pnp3/Magnification/FinalResult.lean

  Финальный слой использует асимптотический realized-маршрут:
  при профиле `prof` и соответствующих асимптотических гипотезах
  получаем `P ≠ NP`.
-/

namespace Pnp3
namespace Magnification

open Models
open ComplexityInterfaces

/--
  Асимптотические гипотезы magnification-склейки для profile-версии языка.

  Сейчас мы явно фиксируем только «рабочее» условие, которое уже используется
  в формульном мосте: для всех локальных решателей доступны свидетельства
  `FamilyIsLocalCircuit`.

  В дальнейшем сюда естественно добавляются условия про редукции/триггеры,
  если они будут перенесены из external facts во внутреннюю формализацию.
-/
structure MagnificationAssumptions (prof : GapPartialMCSPProfile) : Type where
  m : Nat
  δ : Rat
  hδ : (0 : Rat) < δ
  hm_large : 8 ≤ m
  hAllLocalWitness :
    ∀ params : ThirdPartyFacts.LocalCircuitParameters,
      ThirdPartyFacts.LocalCircuitWitness params
        (Counting.allFunctionsFamily params.n)

/--
  Главный асимптотический финальный результат:

  если задан профиль `prof` и выполнены `MagnificationAssumptions prof`,
  то формульный bridge даёт `NP ⊄ P/poly`, а значит `P ≠ NP`.
-/
theorem P_ne_NP_final_asymptotic
    (prof : GapPartialMCSPProfile)
    (hA : MagnificationAssumptions prof) :
    P_ne_NP := by
  rcases hA with ⟨m, δ, hδ, hm_large, hAllLocalWitness⟩
  have hLocalizedR :
      LowerBounds.LocalizedFamilyWitnessHypothesis_partial_realized
        (prof.paramsAt m hm_large) :=
    LowerBounds.localizedFamilyWitnessHypothesis_partial_realized_of_locality_lift
      (p := prof.paramsAt m hm_large) hAllLocalWitness
  exact
    P_ne_NP_from_partial_formulas_realized
      (p := prof.paramsAt m hm_large) (δ := δ) hδ hLocalizedR

end Magnification
end Pnp3
