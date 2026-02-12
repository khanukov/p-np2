import Models.Model_PartialMCSP
import Complexity.Reductions
import Magnification.FinalResult
import AC0.MultiSwitching.ShrinkageFromGood

/-!
  Compile-time regressions for asymptotic migration.

  Цель этих тестов — не «доказывать новые сложностные факты», а ловить
  регрессии интерфейсов (асимптотический язык, новые типы редукций,
  асимптотический финальный слой и контракт Stage 4).
-/

namespace Pnp3.Tests

open Pnp3.Models
open Pnp3.Complexity
open Pnp3.Magnification
open Pnp3.ComplexityInterfaces
open Pnp3.AC0.MultiSwitching

/-- Простой профиль для тестов совместимости. -/
def regressionProfile : GapPartialMCSPProfile where
  sYES := fun m => m + 1
  sNO := fun m => m + 3
  gap_ok := by
    intro m
    omega

/-- Асимптотический язык успешно имеет тип `Language`. -/
noncomputable example : ComplexityInterfaces.Language :=
  gapPartialMCSP_Language_profile regressionProfile

/-- Новые complexity-aware определения NP-hardness доступны в интерфейсе. -/
example (L : ComplexityInterfaces.Language) : Prop := Is_NP_Hard_poly L
example (L : ComplexityInterfaces.Language) : Prop := Is_NP_Hard_rpoly L

/-- Финальный асимптотический слой типизируется и возвращает `P_ne_NP`. -/
example (hA : MagnificationAssumptions regressionProfile) : ComplexityInterfaces.P_ne_NP :=
  P_ne_NP_final_asymptotic regressionProfile hA

/--
  Legacy-совместимость: из прежней гипотезы `hF_all` по `canonicalPartialParams`
  получаем старую финальную теорему с тем же именем `P_ne_NP_final`.
-/
example
    (hF_all : ∀ loc : LowerBounds.SmallLocalCircuitSolver_Partial canonicalPartialParams,
      ThirdPartyFacts.FamilyIsLocalCircuit loc.params.params
        (Counting.allFunctionsFamily loc.params.params.n)) :
    ComplexityInterfaces.P_ne_NP :=
  P_ne_NP_final hF_all

/--
  Stage 4 regression: `shrinkage_from_good_restriction` по-прежнему требует
  *явную* гипотезу `hgood` в сигнатуре.
-/
example {n k t : Nat} (F : FormulaFamily n k) (ρ : Core.Restriction n)
    (hgood : GoodFamilyCNF (F := F) t ρ) :=
  shrinkage_from_good_restriction F ρ hgood


/--
  Усиленный Stage 4 API также доступен: вместе с shrinkage он
  возвращает в явном виде `GoodFamilyCNF`, фиксируя proof-relevant
  зависимость от гипотезы `hgood`.
-/
example {n k t : Nat} (F : FormulaFamily n k) (ρ : Core.Restriction n)
    (hgood : GoodFamilyCNF (F := F) t ρ) :=
  shrinkage_from_good_restriction_with_depth F ρ hgood

end Pnp3.Tests
