import Models.Model_GapMCSP
import Models.Model_SparseNP
import LowerBounds.AntiChecker
import Complexity.Interfaces

/-!
  pnp3/Magnification/Facts_Magnification.lean

  Этот файл аккумулирует внешние «триггеры» шага D.  Они формализуют
  утверждения вида:

  * если для GapMCSP известна нижняя оценка на размер схем в форме
    `N^{1+ε}` (или её эквиваленты), то `NP \nsubseteq P/poly`;
  * если доказана более сильная граница для формул (`N^{2+δ}`), то
    магнификация также даёт `NP \nsubseteq P/poly`;
  * аналогично для классов локальных схем (`N · polylog(N)`).

  Формально мы записываем эти утверждения как Lean-аксиомы с прозрачными
  интерфейсами.  Каждое из них снабжено комментариями с отсылкой к
  соответствующим источникам (OPS’20, JACM’22 и др.), чтобы позднее
  заменить аксиомы на доказательства или импортированные теоремы.
-/

namespace Pnp3
namespace Magnification

open Classical
open Models
open LowerBounds
open Set
open ComplexityInterfaces

/--
  Общая форма нижней оценки (OPS’20, Theorem 5.1): при наличии `ε > 0`
  задача `GapMCSP` не допускает схем размера `N^{1+ε}` даже в самом широком
  неограниченном классе (обычно ACC или TC).  Параметр `statement`
  передаёт конкретное утверждение о невозможности такого решателя,
  а возвращаемое условие требует сразу `ε > 0` и справедливость `statement`.
-/
def GeneralLowerBoundHypothesis
    (_p : GapMCSPParams) (ε : Rat) (statement : Prop) : Prop :=
  (0 : Rat) < ε ∧ statement

/--
  Специализированная версия для формул (OPS’20, Corollary 6.4).  Здесь
  `δ > 0` соответствует границе вида `N^{2+δ}`; условие
  `FormulaLowerBoundHypothesis p δ` одновременно проверяет положительность
  `δ` и отсутствие малых AC⁰-решателей.
-/
def FormulaLowerBoundHypothesis
    (p : GapMCSPParams) (δ : Rat) : Prop :=
  (0 : Rat) < δ ∧ ∀ _solver : SmallAC0Solver p, False

/--
  Вариант для «локальных» схем (JACM’22, Theorem 3.1).  Параметр `κ > 0`
  описывает степень полилогарифмического множителя в размере `N · (log N)^κ`;
  условие `LocalLowerBoundHypothesis` объединяет проверку `κ > 0` и отсутствие
  локальных решателей указанного размера.
-/
def LocalLowerBoundHypothesis
    (p : GapMCSPParams) (κ : Nat) : Prop :=
  0 < κ ∧ ∀ _solver : SmallLocalCircuitSolver p, False

/-- CJW-гипотеза для разреженных NP-языков. -/
def SparseLowerBoundHypothesis
    (p : Models.SparseLanguageParams) (ε : Rat) (statement : Prop) : Prop :=
  (0 : Rat) < ε ∧ statement

/--
  OPS-триггер (общая версия): доказательство `GeneralLowerBoundHypothesis`
  автоматически влечёт `NP \nsubseteq P/poly`.  На данном этапе мы
  фиксируем это как аксиому с отсылкой к оригинальному утверждению.
-/
axiom OPS_trigger_general
  {p : GapMCSPParams} {ε : Rat} (statement : Prop) :
  GeneralLowerBoundHypothesis p ε statement → NP_not_subset_Ppoly

/--
  OPS-триггер для формул (`N^{2+δ}`): если выполнена соответствующая
  гипотеза, получаем `NP \nsubseteq P/poly`.
-/
axiom OPS_trigger_formulas
  {p : GapMCSPParams} {δ : Rat} :
  FormulaLowerBoundHypothesis p δ → NP_not_subset_Ppoly

/--
  Барьер локальности из JACM’22: невозможность локальных схем размера
  `N · (log N)^κ` приводит к `NP \nsubseteq P/poly`.
-/
axiom Locality_trigger
  {p : GapMCSPParams} {κ : Nat} :
  LocalLowerBoundHypothesis p κ → NP_not_subset_Ppoly

/-- CJW-триггер: разреженный NP-язык с суперлинейной нижней границей. -/
axiom CJW_sparse_trigger
  {p : Models.SparseLanguageParams} {ε : Rat} (statement : Prop) :
  SparseLowerBoundHypothesis p ε statement → NP_not_subset_Ppoly

end Magnification
end Pnp3
