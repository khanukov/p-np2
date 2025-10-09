import Magnification.Facts_Magnification
import LowerBounds.LB_Formulas_Core
import LowerBounds.LB_LocalCircuits
import LowerBounds.LB_GeneralFromLocal
import Models.Model_GapMCSP

/-!
  pnp3/Magnification/PipelineStatements.lean

  Этот файл фиксирует формулировки гипотез для триггеров магнификации,
  которые уже доказаны (или вынесены в виде аксиом) на шагах A–C.
  Цель — предоставить компактные леммы, переводящие результаты о
  несуществовании малых решателей в формат, ожидаемый блоком D.

  * `AC0Statement`, `LocalStatement` и `GeneralCircuitStatement` описывают
    запрет на маленькие решатели для формул, локальных схем и произвольных
    схем соответственно.
  * `ac0_statement_from_pipeline` и `local_statement_from_pipeline`
    извлекаются непосредственно из античекера и Covering-Power
    (теоремы `LB_Formulas_core` и `LB_LocalCircuits_core`).
  * `formula_hypothesis_from_pipeline` и
    `local_hypothesis_from_pipeline` приводят полученные утверждения
    к стандартным гипотезам магнификации (OPS’19, JACM’22).
  * `general_hypothesis_from_pipeline` демонстрирует, как тот же
    аргумент упаковывается в универсальную форму `GeneralLowerBoundHypothesis`.

  Таким образом блок D может ссылаться на эти леммы и не дублировать
  аргументацию шага C.
-/

namespace Pnp3
namespace Magnification

open Models
open LowerBounds

/--
  Утверждение «не существует малого AC⁰-решателя» для фиксированных
  параметров GapMCSP.  Именно его ожидает формулировка OPS-теоремы.
-/
def AC0Statement (p : GapMCSPParams) : Prop :=
  ∀ _solver : SmallAC0Solver p, False

/--
  Утверждение «не существует малой локальной схемы-решателя».  Это
  условие используется в JACM’22 (барьер локальности).
-/
def LocalStatement (p : GapMCSPParams) : Prop :=
  ∀ _solver : SmallLocalCircuitSolver p, False

/--
  Утверждение «не существует малого общего решателя».
-/
def GeneralCircuitStatement (p : GapMCSPParams) : Prop :=
  ∀ _solver : SmallGeneralCircuitSolver p, False

/--
  Переписываем гипотезу OPS для формул через упаковку `AC0Statement`.
  Определения совпадают буквально, поэтому возвращается эквивалентность.
-/
lemma formulaHypothesis_eq_general (p : GapMCSPParams) (δ : Rat) :
    FormulaLowerBoundHypothesis p δ ↔
      GeneralLowerBoundHypothesis p δ (AC0Statement p) := by
  rfl

/--
  Локальная гипотеза JACM также сводится к утверждению `LocalStatement`.
-/
lemma localHypothesis_eq_statement (p : GapMCSPParams) (κ : Nat) :
    LocalLowerBoundHypothesis p κ ↔
      (0 < κ ∧ LocalStatement p) := by
  rfl

/--
  Результат шага C немедленно даёт отрицание малых AC⁰-решателей.
-/
lemma ac0_statement_from_pipeline (p : GapMCSPParams) :
    AC0Statement p :=
  LB_Formulas_core (p := p)

/--
  Аналогичный вывод для локальных схем.
-/
lemma local_statement_from_pipeline (p : GapMCSPParams) :
    LocalStatement p :=
  LB_LocalCircuits_core (p := p)

/--
  Противоречие для произвольных схем: Locality-Lift и локальная нижняя
  граница немедленно запрещают любой малый общий решатель.
-/
lemma general_statement_from_locality (p : GapMCSPParams) :
    GeneralCircuitStatement p :=
  by
    intro solver
    exact LB_GeneralFromLocal (p := p) (solver := solver)

/--
  Переход к стандартной гипотезе OPS’19 для формул: достаточно иметь
  положительный `δ` и запрещающие утверждения из шага C.
-/
lemma formula_hypothesis_from_pipeline
    (p : GapMCSPParams) {δ : Rat} (hδ : (0 : Rat) < δ) :
    FormulaLowerBoundHypothesis p δ :=
  by
    refine And.intro hδ ?hStatement
    intro solver
    exact ac0_statement_from_pipeline (p := p) solver

/--
  Версия барьера локальности: положительный параметр `κ` и вывод шага C
  дают гипотезу JACM’22.
-/
lemma local_hypothesis_from_pipeline
    (p : GapMCSPParams) {κ : Nat} (hκ : 0 < κ) :
    LocalLowerBoundHypothesis p κ :=
  by
    refine And.intro hκ ?hStatement
    intro solver
    exact local_statement_from_pipeline (p := p) solver

/--
  Универсальная OPS-гипотеза, полученная напрямую из запрета общих схем.
-/
lemma general_hypothesis_from_locality
    (p : GapMCSPParams) {ε : Rat} (hε : (0 : Rat) < ε) :
    GeneralLowerBoundHypothesis p ε (GeneralCircuitStatement p) :=
  by
    refine And.intro hε ?hStatement
    exact general_statement_from_locality (p := p)

/--
  Упаковка в универсальную форму магнификации: фиксируем произвольное
  положительное `ε` и в качестве утверждения берём отрицание малых AC⁰-решателей.
-/
lemma general_hypothesis_from_pipeline
    (p : GapMCSPParams) {ε : Rat} (hε : (0 : Rat) < ε) :
    GeneralLowerBoundHypothesis p ε (AC0Statement p) :=
  by
    refine And.intro hε ?hStatement
    exact ac0_statement_from_pipeline (p := p)

/--
  Набор готовых выводов шага C: отрицание малых решателей и
  гипотезы магнификации для всех положительных параметров.
-/
structure PipelineBridgeKit (p : GapMCSPParams) : Type where
  /-- Формулировка «нет малых AC⁰-решателей».-/
  ac0_statement : AC0Statement p
  /-- Гипотеза «нет малых локальных схем».-/
  local_statement : LocalStatement p
  /-- Запрет малых общих схем.-/
  general_statement : GeneralCircuitStatement p
  /-- Любое положительное `δ` даёт OPS-гипотезу для формул.-/
  formula_hypothesis :
    ∀ {δ : Rat}, (0 : Rat) < δ → FormulaLowerBoundHypothesis p δ
  /-- Аналогичная гипотеза для локальных схем.-/
  local_hypothesis :
    ∀ {κ : Nat}, 0 < κ → LocalLowerBoundHypothesis p κ
  /-- Универсальная форма OPS-гипотезы.-/
  general_hypothesis :
    ∀ {ε : Rat}, (0 : Rat) < ε →
      GeneralLowerBoundHypothesis p ε (AC0Statement p)
  /-- Универсальная OPS-гипотеза для общих схем.-/
  general_circuit_hypothesis :
    ∀ {ε : Rat}, (0 : Rat) < ε →
      GeneralLowerBoundHypothesis p ε (GeneralCircuitStatement p)

/--
  Пакуем выводы шага C в готовый набор.
-/
def pipelineBridgeKit (p : GapMCSPParams) : PipelineBridgeKit p :=
  { ac0_statement := ac0_statement_from_pipeline (p := p)
    local_statement := local_statement_from_pipeline (p := p)
    general_statement := general_statement_from_locality (p := p)
    formula_hypothesis :=
      by
        intro δ hδ
        exact formula_hypothesis_from_pipeline (p := p) (δ := δ) hδ
    local_hypothesis :=
      by
        intro κ hκ
        exact local_hypothesis_from_pipeline (p := p) (κ := κ) hκ
    general_hypothesis :=
      by
        intro ε hε
        exact general_hypothesis_from_pipeline (p := p) (ε := ε) hε
    general_circuit_hypothesis :=
      by
        intro ε hε
        exact general_hypothesis_from_locality (p := p) (ε := ε) hε }

end Magnification
end Pnp3
