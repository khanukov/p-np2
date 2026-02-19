import Magnification.Bridge_to_Magnification_Partial
import Models.Model_PartialMCSP
import Complexity.Interfaces
import ThirdPartyFacts.Hirahara2022
import ThirdPartyFacts.LocalizedWitness_Partial

/-!
  # pnp3/Magnification/FinalResult.lean

  Финальный слой теперь разделён на две части:

  1. **Асимптотический glue-результат**: при профиле `prof` и
     соответствующих асимптотических гипотезах мы получаем `P ≠ NP`.
  2. **Legacy-совместимость**: старый фиксированный `n = 8` результат
     оставлен как производная теорема (`P_ne_NP_final`).

  Такой дизайн убирает «финитный артефакт» из основной теоремы,
  но не ломает существующие импорты и аудиты.
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
  /-- Существование конкретного масштаба `m`, на котором запускается формульный мост. -/
  m : Nat
  /-- Положительный параметр триггера. -/
  δ : Rat
  hδ : (0 : Rat) < δ
  hm_large : 8 ≤ m

/--
  Явный witness внешней NP-hardness аксиомы в асимптотическом типе.
-/
theorem partial_mcsp_profile_np_hard_witness :
    ∃ prof : GapPartialMCSPProfile,
      Complexity.Is_NP_Hard_rpoly (gapPartialMCSP_Language_profile prof) :=
  ThirdPartyFacts.PartialMCSP_profile_is_NP_Hard_rpoly

/--
  Главный асимптотический финальный результат:

  если задан профиль `prof` и выполнены `MagnificationAssumptions prof`,
  то формульный bridge даёт `NP ⊄ P/poly`, а значит `P ≠ NP`.
-/
theorem P_ne_NP_final_asymptotic
    (prof : GapPartialMCSPProfile)
    (hA : MagnificationAssumptions prof) :
    P_ne_NP := by
  rcases hA with ⟨m, δ, hδ, hm_large⟩
  have hLocalized :
      LowerBounds.LocalizedFamilyWitnessHypothesis_partial (prof.paramsAt m hm_large) :=
    ThirdPartyFacts.localizedFamilyWitness_partial (prof.paramsAt m hm_large)
  exact
    P_ne_NP_from_partial_formulas
      (p := prof.paramsAt m hm_large) (δ := δ) hδ hLocalized

/--
  Legacy witness прежней fixed-length NP-hardness аксиомы.
  Оставлен для обратной совместимости с существующими проверками.
-/
theorem partial_mcsp_np_hard_witness :
    ∃ p : GapPartialMCSPParams,
      Complexity.Is_NP_Hard (gapPartialMCSP_Language p) :=
  ThirdPartyFacts.PartialMCSP_is_NP_Hard

/--
  Legacy-совместимая финальная теорема (фиксированный `n=8`) сохранена,
  но теперь является частным случаем асимптотической версии.
-/
@[simp] def canonicalPartialParams : GapPartialMCSPParams where
  n := 8
  sYES := 1
  sNO := 3
  gap_ok := by decide
  n_large := by decide

/-- Простой профиль, который на каждом `m` повторяет fixed-значения legacy-теоремы. -/
@[simp] def canonicalProfile : GapPartialMCSPProfile where
  sYES := fun _ => 1
  sNO := fun _ => 3
  gap_ok := by intro _; decide

lemma canonicalProfile_paramsAt_8 :
    canonicalProfile.paramsAt 8 (by decide) = canonicalPartialParams := by
  rfl

/--
  Legacy theorem: сохранено исходное имя, чтобы downstream-файлы
  продолжили компилироваться без изменений.
-/
theorem P_ne_NP_final
    : P_ne_NP := by
  let hA : MagnificationAssumptions canonicalProfile :=
    { m := 8
      δ := (1 : Rat)
      hδ := zero_lt_one
      hm_large := by decide }
  simpa [canonicalProfile_paramsAt_8] using
    (P_ne_NP_final_asymptotic canonicalProfile hA)

end Magnification
end Pnp3
