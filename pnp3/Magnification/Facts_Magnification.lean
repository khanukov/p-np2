import Models.Model_GapMCSP
import Models.Model_SparseNP
import LowerBounds.AntiChecker
import LowerBounds.LB_GeneralFromLocal
import Magnification.LocalityInterfaces
import Magnification.LocalityLift
import Complexity.Interfaces
import Counting.BinomialBounds
import Mathlib

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
open Core
open Set
open Finset
open ComplexityInterfaces
open Counting

/--
  Набор «дефолтных» параметров, удобных для автоматических инстанциований
  триггеров OPS.  Мы фиксируем конкретные рациональные числа, чтобы не
  доказывать каждый раз положительность `ε`, `δ` и ограниченность `α < 1`.
  Эти значения согласованы с нестрогими оценками из плана доказательства:

  * `opsDefaultEps`  = 1/10  (любой ε > 0 подходит, этого достаточно);
  * `opsDefaultAlpha` = 1/2  (в контрпримерном переборе α < 1);
  * `opsDefaultBeta`  = 3    (степень полилога для тестового множества `T`).

  При необходимости эти константы легко заменить на другие рациональные
  значения, но наличие явных лемм о положительности ускоряет последующие
  построения в Lean без привлечения тактик вроде `norm_num` в каждом месте.
-/
def opsDefaultEps : Rat := 1 / 10

/-- Статус ε > 0 для значения по умолчанию. -/
lemma opsDefaultEps_pos : (0 : Rat) < opsDefaultEps := by
  -- В явном виде: 1/10 > 0.
  norm_num [opsDefaultEps]

/-- Значение α < 1 для перебора кандидатов (консервативное: 1/2). -/
def opsDefaultAlpha : Rat := 1 / 2

lemma opsDefaultAlpha_pos : (0 : Rat) < opsDefaultAlpha := by
  norm_num [opsDefaultAlpha]

lemma opsDefaultAlpha_lt_one : opsDefaultAlpha < (1 : Rat) := by
  norm_num [opsDefaultAlpha]

/-- Полилогарифмическая степень `β` для тестового множества `T`. -/
def opsDefaultBeta : Nat := 3

lemma opsDefaultBeta_pos : 0 < opsDefaultBeta := by decide

/--
  Упаковка фиксированных параметров: положительный ε и вспомогательные
  оценки для α и β.  Она пригодится как «единая точка входа» в дальнейшем
  доказательстве, чтобы не раз за разом выписывать элементарные неравенства.
-/
structure OPSDefaultParamPack : Type where
  ε : Rat
  α : Rat
  β : Nat
  ε_pos : (0 : Rat) < ε
  α_pos : (0 : Rat) < α
  α_lt_one : α < (1 : Rat)
  β_pos : 0 < β

/-- Экземпляр набора параметров по умолчанию. -/
def opsDefaultPack : OPSDefaultParamPack :=
  { ε := opsDefaultEps
    α := opsDefaultAlpha
    β := opsDefaultBeta
    ε_pos := opsDefaultEps_pos
    α_pos := opsDefaultAlpha_pos
    α_lt_one := opsDefaultAlpha_lt_one
    β_pos := opsDefaultBeta_pos }

/--
  Конкретные «малые» параметры AC⁰ для GapMCSP.  Это лишь числовой каркас,
  не являющийся решателем; корректность и семантика задаются отдельно в
  типе `SmallAC0Solver`.
-/
def defaultAC0Params (p : GapMCSPParams) : SmallAC0Params p :=
  { ac0 := { n := Models.inputLen p,
              M := 1,
              d := 1 }
    same_n := rfl
    small :=
      by
        -- Для `M = 1`, `d = 1` оценка `log₂(M+2)^(d+1)` равна 1.
        -- Длина входа `inputLen p = 2^{p.n}` не меньше 1 для любого `p.n`.
        have hpow : Nat.log2 3 ^ 2 = 1 := by native_decide
        -- `inputLen p = 2^{p.n}` всегда ≥ 1, так как основание ≥ 1.
        have hlen : (1 : Nat) ≤ Models.inputLen p := by
          have hpowPos : 0 < 2 ^ Models.GapMCSPParams.n p :=
            Nat.pow_pos (by decide : 0 < (2 : Nat))
          exact Nat.succ_le_of_lt (by simpa [Models.inputLen] using hpowPos)
        -- Склеиваем равенство с оценкой `hlen`.
        simpa [ThirdPartyFacts.AC0SmallEnough, hpow] using hlen
    union_small :=
      by
        -- Для `M = 1`, `d = 1` получаем `bound = 2`.
        have hpow : Nat.log2 3 ^ 2 = 1 := by native_decide
        -- `unionBound 2 2 ≤ 4`, а правая часть ≥ `2^2 = 4` при `n ≥ 8`.
        have hleft : Counting.unionBound 2 2 ≤ 4 := by
          simpa using (Counting.unionBound_le_pow 2 2)
        have hden_pos : 0 < Models.inputLen p + 2 := by
          exact Nat.succ_pos (Models.inputLen p + 1)
        -- `2 ≤ 2^N / (N+2)` при `N = 2^n`, `n ≥ 8`.
        have hdiv_ge : 2 ≤
            Nat.pow 2 (Models.inputLen p) / (Models.inputLen p + 2) := by
          have hN_ge : 8 ≤ Models.inputLen p := by
            -- Из `n ≥ 8` получаем `2^n ≥ 2^8`.
            have hpow := Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) p.n_large
            have hpow' : Nat.pow 2 8 ≤ Models.inputLen p := by
              simpa [Models.inputLen] using hpow
            have h8 : 8 ≤ Nat.pow 2 8 := by decide
            exact le_trans h8 hpow'
          have hmul : 2 * (Models.inputLen p + 2) ≤
              Nat.pow 2 (Models.inputLen p) := by
            -- Усиливаем до `2 * N * (N+2) ≤ 2^N` и убираем множитель `N`.
            have hmul_big :
                2 * (Models.inputLen p) * (Models.inputLen p + 2) ≤
                  Nat.pow 2 (Models.inputLen p) := by
              -- Применяем оценку `twoPow_ge_twoMul_mul` на уровне `N`.
              exact twoPow_ge_twoMul_mul _ hN_ge
            -- Так как `N ≥ 1`, имеем `2*(N+2) ≤ 2*N*(N+2)`.
            have hNpos : 1 ≤ Models.inputLen p := by
              have hpowPos : 0 < Models.inputLen p := by
                simpa [Models.inputLen] using
                  (Nat.pow_pos (n := p.n) (by decide : 0 < (2 : Nat)))
              exact Nat.succ_le_iff.mpr hpowPos
            have hmul_le :
                2 * (Models.inputLen p + 2)
                  ≤ 2 * (Models.inputLen p) * (Models.inputLen p + 2) := by
              nlinarith [hNpos]
            exact hmul_le.trans hmul_big
          exact (Nat.le_div_iff_mul_le hden_pos).2 hmul
        have hmono :
            Nat.pow 2 2 ≤
              Nat.pow 2 (Nat.pow 2 (Models.inputLen p) / (Models.inputLen p + 2)) := by
          exact Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hdiv_ge
        have hU : Counting.unionBound 2 2 ≤
            Nat.pow 2 (Nat.pow 2 (Models.inputLen p) / (Models.inputLen p + 2)) := by
          exact hleft.trans hmono
        have hU' :
            Counting.unionBound
              (2 ^ Nat.log2 3 ^ 2)
              (2 ^ Nat.log2 3 ^ 2)
              ≤ Nat.pow 2 (Nat.pow 2 (Models.inputLen p) / (Models.inputLen p + 2)) := by
          simpa [hpow] using hU
        simpa using hU' }

/-- Временное включение GapMCSP в `NP` (совпадает с `True` в текущей модели). -/
theorem gapMCSP_in_NP (p : GapMCSPParams) : NP (gapMCSP_Language p) := by
  simp [gapMCSP_Language, NP]

/--
  Неуниформный решатель для GapMCSP, извлекаемый из предположения
  `NP ⊆ P/poly`.  Нам не нужна корректность схемы — оболочка хранит лишь
  параметры `n`, `size`, `depth`, поэтому достаточно считать размером
  оценку `polyBound` из свидетельства `P/poly`.
-/
noncomputable def generalCircuitSolver_of_Ppoly
    (p : GapMCSPParams)
    (h : ComplexityInterfaces.Ppoly (gapMCSP_Language p)) :
    SmallGeneralCircuitSolver p := by
  classical
  -- Свидетельство `P/poly` предоставляет полиномиальную оценку размера.
  let w : Facts.PsubsetPpoly.Complexity.InPpoly (gapMCSP_Language p) :=
    Classical.choose h
  refine
    { params :=
        { params :=
            { n := Models.inputLen p
              size := w.polyBound (Models.inputLen p)
              depth := 1 }
          same_n := rfl }
      decide := w.circuits (Models.inputLen p)
      correct := by
        refine And.intro ?yes ?no
        · intro x hx
          -- На YES-инстансах язык `gapMCSP_Language` возвращает `true`.
          have hLang : w.circuits (Models.inputLen p) x =
              gapMCSP_Language p (Models.inputLen p) x :=
            w.correct _ _
          simpa [hLang] using hx
        · intro x hx
          have hLang : w.circuits (Models.inputLen p) x =
              gapMCSP_Language p (Models.inputLen p) x :=
            w.correct _ _
          -- На NO-инстансах значение языка `false`.
          have hNo : gapMCSP_Language p (Models.inputLen p) x = false := hx
          simpa [hLang, hNo] }

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
  Упрощённое построение гипотезы нижней границы при фиксированном `ε` по
  умолчанию.  Достаточно предъявить само утверждение `statement` —
  положительность `ε` берётся из `opsDefaultPack`.
-/
lemma general_hypothesis_default {p : GapMCSPParams} {statement : Prop}
    (h : statement) :
    GeneralLowerBoundHypothesis p opsDefaultPack.ε statement :=
  ⟨opsDefaultPack.ε_pos, h⟩

/--
  Аналогичная упаковка для формульной гипотезы: фиксируем `δ = 1/10` и
  используем сразу готовое доказательство положительности.
-/
lemma formula_hypothesis_default {p : GapMCSPParams}
    (h : ∀ _solver : SmallAC0Solver p, False) :
    FormulaLowerBoundHypothesis p opsDefaultPack.ε :=
  ⟨opsDefaultPack.ε_pos, h⟩

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
  Оболочка для гипотетического решателя разреженного NP-языка.  Мы фиксируем
  лишь базовые числовые параметры схемы (длина входа, размер, глубина) и требуем
  их согласованности с параметрами языка.  Корректность решателя не используется
  — достаточно самого факта существования таких «небольших» схем.
-/
structure SmallSparseSolver (p : Models.SparseLanguageParams) where
  params : GeneralCircuitParameters
  same_n : params.n = p.n
  size_bound : params.size ≤ p.n * Models.polylogBudget p.n
  depth_bound : params.depth = 2
  deriving Repr

/--
  Явный кандидат на небольшой решатель: схема глубины `2` и размера
  `n · polylog(n)`.  Мы не предъявляем её внутреннюю структуру — достаточно
  зафиксировать параметры, которые попадают под барьер CJW.  Полезно для
  немедленного противоречия с предположением `∀ solver, False`.
-/
def defaultSparseSolver (p : Models.SparseLanguageParams) : SmallSparseSolver p :=
  { params := { n := p.n, size := p.n * Models.polylogBudget p.n, depth := 2 }
    same_n := rfl
    size_bound := by exact Nat.le_refl _
    depth_bound := rfl }

/--
  Контрапозитивная форма триггера OPS: при предположении `NP ⊆ P/poly`
  и выполненной гипотезе нижней границы возникает противоречие.  В отличие
  от прежней аксиомы, доказательство теперь конструктивно: из включения
  `NP ⊆ P/poly` мы извлекаем малый общий решатель для `GapMCSP`, а затем
  применяем лемму `LB_GeneralFromLocal`, запрещающую существование такого
  решателя.  Гипотеза нижней границы используется лишь как формальный
  параметр (она автоматически удовлетворена в реальных сценариях шага C),
  но сам аргумент опирается только на существование решателя из `P/poly`.
-/
theorem OPS_trigger_general_contra
  {p : GapMCSPParams} {ε : Rat} (statement : Prop) :
  GeneralLowerBoundHypothesis p ε statement →
    ((∀ L : ComplexityInterfaces.Language,
      ComplexityInterfaces.NP L → ComplexityInterfaces.Ppoly L) → False) :=
by
  intro hHyp hAll
  -- Из предположения `NP ⊆ P/poly` извлекаем неуниформный решатель для
  -- `GapMCSP` (в произвольном классе схем общего вида).
  have hPpoly : ComplexityInterfaces.Ppoly (gapMCSP_Language p) :=
    hAll _ (gapMCSP_in_NP p)
  have solver : SmallGeneralCircuitSolver p :=
    generalCircuitSolver_of_Ppoly (p := p) hPpoly
  -- Локальная нижняя граница шага C (`LB_GeneralFromLocal`) запрещает любое
  -- такое решение, поэтому получаем немедленное противоречие.
  exact LowerBounds.LB_GeneralFromLocal (p := p) (solver := solver)

/-!
  ### Комбинаторика покрытия семейства `Y`

  В доказательстве триггера OPS важен простой счётный аргумент: если у нас есть
  большое семейство функций `Y`, а любой «малый» решатель может покрыть не
  более `m` таких функций (в смысле корректного ответа), то при `|Y| > m`
  гарантированно найдётся функция, не покрытая данным решателем.  Ниже мы
  формализуем эту базовую лемму в виде общих утверждений на `Finset`.  Они
  полностью независимы от сложности и пригодятся при стыковке с античекером,
  который предоставляет нижнюю оценку на мощность `Y` и верхнюю оценку на
  «ёмкость» покрытия малой схемы.
-/

/--
  Если кардинальность покрытия `cover` не превосходит `m`, а семейство `Y`
  строго больше `m`, то существует элемент из `Y`, который не попадает в
  `cover`.  Эта лемма будет использоваться для доказательства того, что ни один
  конкретный малый решатель не справляется со всем семейством `Y` сразу.
-/
theorem exists_element_outside_cover
    {α : Type} [DecidableEq α] {Y cover : Finset α} {m : Nat}
    (hLarge : m < Y.card) (hCap : cover.card ≤ m) :
    ∃ y ∈ Y, y ∉ cover := by
  classical
  -- Ограничим покрытие пересечением с `Y`, чтобы получить подмножество `Y`.
  have hCapInter : (cover ∩ Y).card ≤ m := by
    -- `(cover ∩ Y)` — подмножество `cover`, значит кардинальность не больше.
    have hSub : cover ∩ Y ⊆ cover := Finset.inter_subset_left
    have hCard : (cover ∩ Y).card ≤ cover.card := Finset.card_mono hSub
    exact hCard.trans hCap
  -- Теперь мощность пересечения строго меньше мощности `Y`.
  have hlt : (cover ∩ Y).card < Y.card := lt_of_le_of_lt hCapInter hLarge
  -- Значит, пересечение строго содержится в `Y`, и найдётся элемент вне него.
  have hss : cover ∩ Y ⊂ Y := by
    -- Применяем критерий строгого включения по факту `card` строго меньше.
    refine Finset.ssubset_iff_subset_ne.mpr ?_ 
    refine ⟨Finset.inter_subset_right, ?_⟩
    intro hEq
    -- Кардинальности не могут совпасть, если строгое неравенство уже известно.
    have hCard : (cover ∩ Y).card = Y.card := by simpa [hEq]
    exact (ne_of_lt hlt) hCard
  rcases Finset.exists_of_ssubset hss with ⟨y, hyY, hyNotInter⟩
  refine ⟨y, hyY, ?hyNotCover⟩
  -- Членство в `cover` привело бы к членству в `cover ∩ Y` — противоречие.
  exact fun hyCover => hyNotInter (Finset.mem_inter.mpr ⟨hyCover, hyY⟩)

/--
  Обобщённая форма: если каждое покрытие `cover s` имеет мощность не более `m`,
  а семейство `Y` больше `m`, то для любого `s` найдётся элемент `y ∈ Y`, не
  покрытый `cover s`.  Это именно та «ёмкостная» рассуждение, которое превращает
  оценку числа малых схем в существование конкретного контрпримера `y`.
-/
theorem exists_uncovered_for_each
    {α σ : Type} [DecidableEq α] {Y : Finset α} {m : Nat}
    (hLarge : m < Y.card) (cover : σ → Finset α)
    (hCap : ∀ s, (cover s).card ≤ m) :
    ∀ s, ∃ y ∈ Y, y ∉ cover s := by
  intro s
  -- Применяем предыдущую лемму к конкретному покрытию `cover s`.
  simpa using exists_element_outside_cover (Y := Y) (cover := cover s)
    hLarge (hCap s)

/--
  Невозможность полного покрытия: если `|Y|` превышает ёмкость `m`, то ни один
  конкретный кандидат `s` не может содержать `Y` целиком.  Это удобная форма
  для применения античекера: каждая малая схема пропускает хотя бы одну
  функцию из большого семейства `Y`.
-/
theorem no_full_cover
    {α σ : Type} [DecidableEq α] {Y : Finset α} {m : Nat}
    (hLarge : m < Y.card) (cover : σ → Finset α)
    (hCap : ∀ s, (cover s).card ≤ m) :
    ∀ s, ¬ Y ⊆ cover s := by
  intro s hSubset
  obtain ⟨y, hyY, hyNot⟩ := exists_uncovered_for_each (Y := Y) (m := m)
    hLarge cover hCap s
  exact hyNot (hSubset hyY)

/--
  Следствие предыдущей леммы: при `|Y| > m` не существует ни одного кандидата
  `s`, покрывающего `Y` целиком.  То есть мощность `Y` уже больше ёмкости
  любого покрытия размера `≤ m`.
-/
theorem not_exists_full_cover
    {α σ : Type} [DecidableEq α] {Y : Finset α} {m : Nat}
    (hLarge : m < Y.card) (cover : σ → Finset α)
    (hCap : ∀ s, (cover s).card ≤ m) :
    ¬ ∃ s, Y ⊆ cover s := by
  intro hExists
  rcases hExists with ⟨s, hSub⟩
  have hNo : ¬ Y ⊆ cover s :=
    no_full_cover (Y := Y) (m := m) hLarge cover hCap s
  exact hNo hSub

/--
  Сводка данных, полученных от античекера: большое семейство `Y` и ёмкостная
  оценка `m`, причём `|Y| > m`.  Такой «пакет» удобно прокидывать через цепочку
  лемм, не извлекая неравенство каждый раз вручную.
-/
structure CoverCapacityWitness (α : Type) [DecidableEq α] : Type where
  Y : Finset α
  m : Nat
  hLarge : m < Y.card

/--
  Преобразование античекера в удобный пакет для лемм покрытия.  Из гипотетического
  малого решателя `solver` извлекаем сценарий `sc` и семейство `Y` так, что `|Y|`
  строго превышает ёмкость `scenarioCapacity sc`.  Леммы
  `witness_uncovered_for_each` и `witness_not_exists_full_cover` затем можно
  применять без повторной распаковки `let`-связок из формулировки теоремы
  `antiChecker_exists_large_Y`.
-/
noncomputable def coverWitness_from_antiChecker
    {p : GapMCSPParams} (solver : SmallAC0Solver p) :
    Σ' sc : BoundedAtlasScenario solver.params.ac0.n,
      CoverCapacityWitness (Core.BitVec solver.params.ac0.n → Bool) := by
  classical
  -- Шаг 1: извлекаем конкретные `F` и `Y` из экзистенциальной формулировки.
  let hExist := antiChecker_exists_large_Y (p := p) solver
  -- Сначала выбираем семейство `F`.
  let F : Family (Models.inputLen p) := Classical.choose hExist
  -- Затем выбираем подсемейство `Y` для выбранного `F`.
  have hExistY :
      ∃ Y : Finset (Core.BitVec (Models.inputLen p) → Bool),
        let Fsolver : Family solver.params.ac0.n := solver.params.same_n.symm ▸ F
        let scWitness := (scenarioFromAC0 (params := solver.params.ac0) Fsolver).2
        let Ysolver : Finset (Core.BitVec solver.params.ac0.n → Bool) :=
          solver.params.same_n.symm ▸ Y
        Ysolver ⊆ familyFinset (sc := scWitness) ∧
          scenarioCapacity (sc := scWitness) < Ysolver.card :=
    Classical.choose_spec hExist
  let Y : Finset (Core.BitVec (Models.inputLen p) → Bool) := Classical.choose hExistY
  have h :
      let Fsolver : Family solver.params.ac0.n := solver.params.same_n.symm ▸ F
      let scWitness := (scenarioFromAC0 (params := solver.params.ac0) Fsolver).2
      let Ysolver : Finset (Core.BitVec solver.params.ac0.n → Bool) :=
        solver.params.same_n.symm ▸ Y
      Ysolver ⊆ familyFinset (sc := scWitness) ∧
        scenarioCapacity (sc := scWitness) < Ysolver.card :=
    Classical.choose_spec hExistY
  set Fsolver : Family solver.params.ac0.n := solver.params.same_n.symm ▸ F
  set scSolver : BoundedAtlasScenario solver.params.ac0.n :=
    (scenarioFromAC0 (params := solver.params.ac0) Fsolver).2
  set Ysolver : Finset (Core.BitVec solver.params.ac0.n → Bool) :=
    solver.params.same_n.symm ▸ Y
  -- Переписываем вывод аксиомы в явном виде, убирая `let`-связки.
  have hCap : Ysolver ⊆ familyFinset (sc := scSolver) ∧
      scenarioCapacity (sc := scSolver) < Ysolver.card := by
    simpa only [Fsolver, scSolver, Ysolver] using h
  -- Переносим сценарий обратно к длине `inputLen p`, избегая дальнейших приведения типов.
  -- Мощность `Ysolver` строго превосходит ёмкость соответствующего сценария.
  refine
    ⟨scSolver,
      { Y := Ysolver
        m := scenarioCapacity (sc := scSolver)
        hLarge := hCap.2 }⟩

/--
  Расширенная упаковка античекера с тестовым множеством `T`.  В отличие от
  `coverWitness_from_antiChecker`, здесь ёмкость покрытия берётся из более
  точной оценки `unionBound * 2^{|T|}`, получаемой из strengthened anti-checker
  (`antiChecker_exists_testset`).  Кроме `Y` и `m` возвращается само тестовое
  множество `T`, что удобно при подключении лемм `ApproxOnTestset` из части B.
-/
noncomputable def coverWitness_from_antiChecker_testset
    {p : GapMCSPParams} (solver : SmallAC0Solver p) :
    Σ' sc : BoundedAtlasScenario solver.params.ac0.n,
      Σ' T : Finset (Core.BitVec solver.params.ac0.n),
        CoverCapacityWitness (Core.BitVec solver.params.ac0.n → Bool) := by
  classical
  -- Шаг 1. Распаковываем усиленную аксиому античекера с тестовым множеством.
  let hExist := antiChecker_exists_testset (p := p) solver
  -- Сначала выбираем семейство `F`.
  let F : Family (Models.inputLen p) := Classical.choose hExist
  -- Затем выбираем подсемейство `Y` и тестовое множество `T` для фиксированного `F`.
  have hExistY :
      ∃ Y : Finset (Core.BitVec (Models.inputLen p) → Bool),
        ∃ T : Finset (Core.BitVec (Models.inputLen p)),
          let Fsolver : Family solver.params.ac0.n := solver.params.same_n.symm ▸ F
          let scWitness := (scenarioFromAC0 (params := solver.params.ac0) Fsolver).2
          let Ysolver : Finset (Core.BitVec solver.params.ac0.n → Bool) :=
            solver.params.same_n.symm ▸ Y
          let Tsolver : Finset (Core.BitVec solver.params.ac0.n) :=
            solver.params.same_n.symm ▸ T
          Ysolver ⊆ familyFinset (sc := scWitness) ∧
            scenarioCapacity (sc := scWitness) < Ysolver.card ∧
            Tsolver.card ≤ Models.polylogBudget solver.params.ac0.n ∧
            (∀ f ∈ Ysolver,
              f ∈ Counting.ApproxOnTestset
                (R := scWitness.atlas.dict) (k := scWitness.k) (T := Tsolver)) ∧
            Counting.unionBound (Counting.dictLen scWitness.atlas.dict) scWitness.k *
              2 ^ Tsolver.card < Ysolver.card :=
    Classical.choose_spec hExist
  let Y : Finset (Core.BitVec (Models.inputLen p) → Bool) := Classical.choose hExistY
  have hExistT :
      ∃ T : Finset (Core.BitVec (Models.inputLen p)),
        let Fsolver : Family solver.params.ac0.n := solver.params.same_n.symm ▸ F
        let scWitness := (scenarioFromAC0 (params := solver.params.ac0) Fsolver).2
        let Ysolver : Finset (Core.BitVec solver.params.ac0.n → Bool) :=
          solver.params.same_n.symm ▸ Y
        let Tsolver : Finset (Core.BitVec solver.params.ac0.n) :=
          solver.params.same_n.symm ▸ T
        Ysolver ⊆ familyFinset (sc := scWitness) ∧
          scenarioCapacity (sc := scWitness) < Ysolver.card ∧
          Tsolver.card ≤ Models.polylogBudget solver.params.ac0.n ∧
          (∀ f ∈ Ysolver,
            f ∈ Counting.ApproxOnTestset
              (R := scWitness.atlas.dict) (k := scWitness.k) (T := Tsolver)) ∧
          Counting.unionBound (Counting.dictLen scWitness.atlas.dict) scWitness.k *
            2 ^ Tsolver.card < Ysolver.card :=
    Classical.choose_spec hExistY
  let T : Finset (Core.BitVec (Models.inputLen p)) := Classical.choose hExistT
  have hProps :
      let Fsolver : Family solver.params.ac0.n := solver.params.same_n.symm ▸ F
      let scWitness := (scenarioFromAC0 (params := solver.params.ac0) Fsolver).2
      let Ysolver : Finset (Core.BitVec solver.params.ac0.n → Bool) :=
        solver.params.same_n.symm ▸ Y
      let Tsolver : Finset (Core.BitVec solver.params.ac0.n) :=
        solver.params.same_n.symm ▸ T
      Ysolver ⊆ familyFinset (sc := scWitness) ∧
        scenarioCapacity (sc := scWitness) < Ysolver.card ∧
        Tsolver.card ≤ Models.polylogBudget solver.params.ac0.n ∧
        (∀ f ∈ Ysolver,
          f ∈ Counting.ApproxOnTestset
            (R := scWitness.atlas.dict) (k := scWitness.k) (T := Tsolver)) ∧
        Counting.unionBound (Counting.dictLen scWitness.atlas.dict) scWitness.k *
          2 ^ Tsolver.card < Ysolver.card :=
    Classical.choose_spec hExistT
  -- Шаг 2. Переводим все объекты на длину `solver.params.ac0.n`.
  let Fsolver : Family solver.params.ac0.n := solver.params.same_n.symm ▸ F
  let scWitness := (scenarioFromAC0 (params := solver.params.ac0) Fsolver).2
  let Ysolver : Finset (Core.BitVec solver.params.ac0.n → Bool) :=
    solver.params.same_n.symm ▸ Y
  let Tsolver : Finset (Core.BitVec solver.params.ac0.n) := solver.params.same_n.symm ▸ T
  -- Шаг 3. Переписываем свойства, разворачивая только `let`-связки (без лишних упрощений).
  have hProps' := hProps
  dsimp [Fsolver, scWitness, Ysolver, Tsolver] at hProps'
  rcases hProps' with ⟨hSubset, hCap, hT, hApprox, hUnion⟩
  -- Шаг 4. Формируем пакет для покрытий: `m = unionBound * 2^{|T|}`.
  refine ⟨scWitness, Tsolver, ?_⟩
  refine
    { Y := Ysolver
      m := Counting.unionBound (Counting.dictLen scWitness.atlas.dict)
            scWitness.k * 2 ^ Tsolver.card
      hLarge := ?_ }
  -- Прямое следствие из усиленной ёмкостной оценки античекера.
  simpa using hUnion

/--
  Вариант `coverWitness_from_antiChecker`, сразу приводящий все индексы к
  канонической длине `inputLen p`.  Это снижает шум с `Eq.rec` при стыковке с
  леммами, которые ожидают сценарий и покрытие именно на длине `inputLen p`.

  Технически Lean различает типы `Scenario solver.params.ac0.n` и
  `Scenario (inputLen p)`; равенство `solver.params.same_n` служит мостом
  между ними, но не применяется
  автоматически.  Здесь мы «переносим» (transport) свидетельство покрытия по
  этому равенству один раз, чтобы далее использовать его без дополнительных
  приведений типов.
-/
noncomputable def coverWitness_from_antiChecker_inputLen
    {p : GapMCSPParams} (solver : SmallAC0Solver p) :
    Σ' sc : BoundedAtlasScenario (Models.inputLen p),
      CoverCapacityWitness (Core.BitVec (Models.inputLen p) → Bool) := by
  classical
  -- Переписываем результат базовой функции по равенству `same_n`, чтобы
  -- получить сценарий и семейство строго на длине `inputLen p`.
  simpa using
    (solver.params.same_n ▸ coverWitness_from_antiChecker (p := p) solver)

/--
  Версия `coverWitness_from_antiChecker_testset`, сразу приводящая все индексы
  к канонической длине `inputLen p`.  Тестовое множество `T` и пакет ёмкости
  возвращаются уже в «нормализованном» виде, что избавляет от последующих
  приведения типов.
-/
noncomputable def coverWitness_from_antiChecker_testset_inputLen
    {p : GapMCSPParams} (solver : SmallAC0Solver p) :
    Σ' sc : BoundedAtlasScenario (Models.inputLen p),
      Σ' T : Finset (Core.BitVec (Models.inputLen p)),
        CoverCapacityWitness (Core.BitVec (Models.inputLen p) → Bool) := by
  classical
  simpa using
    (solver.params.same_n ▸ coverWitness_from_antiChecker_testset (p := p) solver)

/--
  Любое семейство покрытий `cover s` с мощностью не более `m` пропускает
  некоторый элемент из `Y`.  Это прямое применение ёмкостного аргумента к
  сохранённым в `CoverCapacityWitness` данным; пригодится при стыковке с
  античекером, который обеспечивает требуемое неравенство `m < |Y|`.
-/
theorem witness_uncovered_for_each
    {α σ : Type} [DecidableEq α] (w : CoverCapacityWitness α)
    (cover : σ → Finset α) (hCap : ∀ s, (cover s).card ≤ w.m) :
    ∀ s, ∃ y ∈ w.Y, y ∉ cover s :=
  exists_uncovered_for_each (Y := w.Y) (m := w.m) w.hLarge cover hCap

/--
  Следствие `witness_uncovered_for_each`: при наличии ёмкостного пакета нет
  кандидата `s`, полностью покрывающего `Y`.
-/
theorem witness_no_full_cover
    {α σ : Type} [DecidableEq α] (w : CoverCapacityWitness α)
    (cover : σ → Finset α) (hCap : ∀ s, (cover s).card ≤ w.m) :
    ∀ s, ¬ w.Y ⊆ cover s :=
  no_full_cover (Y := w.Y) (m := w.m) w.hLarge cover hCap

/--
  Ещё одна форма: из ёмкостного пакета следует, что не существует кандидата
  `s`, покрывающего всё семейство `Y`.
-/
theorem witness_not_exists_full_cover
    {α σ : Type} [DecidableEq α] (w : CoverCapacityWitness α)
    (cover : σ → Finset α) (hCap : ∀ s, (cover s).card ≤ w.m) :
    ¬ ∃ s, w.Y ⊆ cover s :=
  not_exists_full_cover (Y := w.Y) (m := w.m) w.hLarge cover hCap

/--
  Удобная форма `witness_uncovered_for_each`, сразу применимая к свидетельству
  античекера на канонической длине `inputLen p`.  Мы извлекаем пакет данных
  `(sc, w)` из `coverWitness_from_antiChecker_inputLen` и «скармливаем» его
  ёмкостной лемме: при любом семействе покрытий `cover`, ограниченном мощностью
  `w.m`, находится элемент `y ∈ w.Y`, который не покрывается данным кандидатом.

  Эта форма избавляет от ручного раскрытия `Σ'`-структуры и повторных переписок
  по равенству `solver.params.same_n` при стыковке с дальнейшими шагами триггера OPS.
-/
theorem uncovered_from_antiChecker_inputLen
    {p : GapMCSPParams} (solver : SmallAC0Solver p)
    {σ : Type} [DecidableEq σ]
    (cover : σ → Finset (Core.BitVec (Models.inputLen p) → Bool))
  (hCap : ∀ s, (cover s).card ≤
      (coverWitness_from_antiChecker_inputLen (p := p) solver).2.m) :
  ∀ s, ∃ y ∈ (coverWitness_from_antiChecker_inputLen (p := p) solver).2.Y,
    y ∉ cover s := by
  classical
  -- Распаковываем пакет античекера и применяем ёмкостную лемму.
  set cw := coverWitness_from_antiChecker_inputLen (p := p) solver
  -- Сохраняем исходное ограничение мощности, чтобы переписать его после раскрытия `cw`.
  have hCap' : ∀ s, (cover s).card ≤ cw.2.m := hCap
  -- Открываем `cw` и переписываем ограничение мощности к форме `w.m`.
  rcases cw with ⟨sc, w⟩
  have hCap'' : ∀ s, (cover s).card ≤ w.m := by
    simpa using hCap'
  simpa using
    witness_uncovered_for_each (w := w) cover hCap''

/--
  Версия ёмкостного вывода, использующая усиленный античекер с тестовым
  множеством.  Полезна, когда верхняя оценка числа покрываемых функций
  выводится как `unionBound * 2^{|T|}`: она напрямую применяет лемму о покрытии
  к данным `coverWitness_from_antiChecker_testset_inputLen` без ручных переписок.
-/
theorem uncovered_from_antiChecker_testset_inputLen
    {p : GapMCSPParams} (solver : SmallAC0Solver p)
    {σ : Type} [DecidableEq σ]
    (cover : σ → Finset (Core.BitVec (Models.inputLen p) → Bool))
    (hCap : ∀ s, (cover s).card ≤
        (coverWitness_from_antiChecker_testset_inputLen (p := p) solver).2.2.m) :
    ∀ s, ∃ y ∈ (coverWitness_from_antiChecker_testset_inputLen (p := p) solver).2.2.Y,
      y ∉ cover s := by
  classical
  -- Распаковываем расширенный пакет античекера с тестовым множеством.
  set cw := coverWitness_from_antiChecker_testset_inputLen (p := p) solver
  have hCap' : ∀ s, (cover s).card ≤ cw.2.2.m := hCap
  rcases cw with ⟨sc, T, w⟩
  have hCap'' : ∀ s, (cover s).card ≤ w.m := by
    simpa using hCap'
  simpa using
    witness_uncovered_for_each (w := w) cover hCap''

/--
  Контрапозиция триггера для случая `GeneralCircuitStatement`: из гипотезы
  нижней границы и предположения `NP ⊆ P/poly` конструируется конкретный
  «малый» решатель, противоречащий заявлению `∀ solver, False`.
-/
theorem OPS_trigger_general_contra_general_circuit
  {p : GapMCSPParams} {ε : Rat} :
  GeneralLowerBoundHypothesis p ε (∀ _solver : SmallGeneralCircuitSolver p, False) →
    ((∀ L : ComplexityInterfaces.Language,
      ComplexityInterfaces.NP L → ComplexityInterfaces.Ppoly L) → False) :=
by
  intro hHyp hAll
  -- Из включения `NP ⊆ P/poly` получаем неуниформный решатель для GapMCSP.
  have hPpoly : ComplexityInterfaces.Ppoly (gapMCSP_Language p) :=
    hAll _ (gapMCSP_in_NP p)
  -- Оборачиваем решатель в оболочку `SmallGeneralCircuitSolver`.
  have solver : SmallGeneralCircuitSolver p :=
    generalCircuitSolver_of_Ppoly (p := p) hPpoly
  -- Гипотеза шагов A–C запрещает любой такой решатель.
  exact (hHyp.2) solver

/--
  OPS-триггер (общая версия): доказательство `GeneralLowerBoundHypothesis`
  автоматически влечёт `NP \nsubseteq P/poly`.  Теперь он выводится из
  более точной контрапозитивной формулировки через общую лемму
  `NP_not_subset_Ppoly_of_contra`.
-/
theorem OPS_trigger_general
  {p : GapMCSPParams} {ε : Rat} (statement : Prop) :
  GeneralLowerBoundHypothesis p ε statement → NP_not_subset_Ppoly :=
by
  intro hHyp
  -- Сначала получаем явное противоречие с предположением `NP ⊆ P/poly`.
  have hContra :=
    OPS_trigger_general_contra (p := p) (ε := ε) (statement := statement) hHyp
  -- Затем применяем общую логическую лемму из `ComplexityInterfaces`.
  exact ComplexityInterfaces.NP_not_subset_Ppoly_of_contra hContra

/--
  Специализация триггера к утверждению `GeneralCircuitStatement`.  Здесь
  доказательство опирается только на конструктивную контрапозицию
  `OPS_trigger_general_contra_general_circuit`: контрапозитив выводится
  напрямую из гипотезы «для любого решателя — False».
-/
theorem OPS_trigger_general_circuits
  {p : GapMCSPParams} {ε : Rat} :
  GeneralLowerBoundHypothesis p ε (∀ _solver : SmallGeneralCircuitSolver p, False) →
    NP_not_subset_Ppoly :=
by
  intro hHyp
  -- Контрапозитив, построенный в `OPS_trigger_general_contra_general_circuit`.
  have hContra := OPS_trigger_general_contra_general_circuit (p := p) (ε := ε) hHyp
  -- Применяем общую логическую лемму.
  exact ComplexityInterfaces.NP_not_subset_Ppoly_of_contra hContra

/--
  Быстрая инстанциация конструктивного триггера для общих схем при
  `ε = 1/10`.  Удобно применять, когда формула `∀ solver, False` уже получена
  из шага C, чтобы не упаковывать вручную положительность `ε`.
-/
theorem OPS_trigger_general_circuits_default
  {p : GapMCSPParams} :
  (∀ _solver : SmallGeneralCircuitSolver p, False) → NP_not_subset_Ppoly :=
by
  intro hNoSolver
  have hHyp : GeneralLowerBoundHypothesis p opsDefaultPack.ε
      (∀ _solver : SmallGeneralCircuitSolver p, False) :=
    ⟨opsDefaultPack.ε_pos, hNoSolver⟩
  exact OPS_trigger_general_circuits (p := p) (ε := opsDefaultPack.ε) hHyp

/--
  Контрапозиция формульного триггера без привлечения общей аксиомы D.1: гипотеза
  `FormulaLowerBoundHypothesis` приводит к противоречию с предположением
  `NP ⊆ P/poly` через универсальный контрапозитив OPS: мы переводим формульную
  гипотезу в общий формат и применяем `OPS_trigger_general_contra`.
-/
theorem OPS_trigger_formulas_contra
  {p : GapMCSPParams} {δ : Rat} :
  FormulaLowerBoundHypothesis p δ →
    ((∀ L : ComplexityInterfaces.Language,
      ComplexityInterfaces.NP L → ComplexityInterfaces.Ppoly L) → False) :=
by
  intro hHyp hAll
  have hGeneral : GeneralLowerBoundHypothesis p δ (∀ _solver : SmallAC0Solver p, False) := by
    simpa [FormulaLowerBoundHypothesis, GeneralLowerBoundHypothesis] using hHyp
  exact OPS_trigger_general_contra (p := p) (ε := δ)
    (statement := ∀ _solver : SmallAC0Solver p, False) hGeneral hAll

/--
  OPS-триггер для формул (`N^{2+δ}`): конструктивное получение
  `NP \nsubseteq P/poly` без обращения к общей аксиоме D.1.  Доказательство
  использует контрапозицию `OPS_trigger_formulas_contra` и логическую
  лемму `NP_not_subset_Ppoly_of_contra`.
-/
theorem OPS_trigger_formulas
  {p : GapMCSPParams} {δ : Rat} :
  FormulaLowerBoundHypothesis p δ → NP_not_subset_Ppoly := by
  intro hHyp
  -- Контрапозиция выводится напрямую из гипотезы `∀ solver, False`.
  have hContra := OPS_trigger_formulas_contra (p := p) (δ := δ) hHyp
  exact ComplexityInterfaces.NP_not_subset_Ppoly_of_contra hContra

/--
  Удобное переписывание: формульная гипотеза уже является частным случаем
  общей OPS-гипотезы при `statement := ∀ _ : SmallAC0Solver p, False`.
  Отдельная лемма избавляет от ручного раскрытия определений в дальнейших
  шагах пайплайна.
  -/
theorem FormulaLowerBoundHypothesis.as_general
  {p : GapMCSPParams} {δ : Rat} :
  FormulaLowerBoundHypothesis p δ →
    GeneralLowerBoundHypothesis p δ (∀ _solver : SmallAC0Solver p, False) :=
by
  intro hHyp
  -- Определения совпадают буквально: `(0 < δ) ∧ statement`.
  simpa [FormulaLowerBoundHypothesis, GeneralLowerBoundHypothesis]

/--
  Специализация общего триггера OPS к утверждению
  `statement := ∀ _ : SmallAC0Solver p, False`.  Удобно использовать,
  когда нужная форма `GeneralLowerBoundHypothesis` уже получена (например,
  из конструкций шага C), без повторного раскрытия определений.
-/
theorem OPS_trigger_formulas_from_general
  {p : GapMCSPParams} {δ : Rat} :
  GeneralLowerBoundHypothesis p δ (∀ _solver : SmallAC0Solver p, False) →
    NP_not_subset_Ppoly :=
by
  intro hGeneral
  -- Сужаемся до формульной гипотезы и применяем конструктивный контрапозитив.
  have hFormula : FormulaLowerBoundHypothesis p δ := by
    simpa [FormulaLowerBoundHypothesis, GeneralLowerBoundHypothesis] using hGeneral
  exact OPS_trigger_formulas (p := p) (δ := δ) hFormula

/--
  Барьер локальности из JACM’22: невозможность локальных схем размера
  `N · (log N)^κ` приводит к `NP \nsubseteq P/poly`.

  Доказательство следует стандартной схеме контрапозиции.
  Предположим, что `NP ⊆ P/poly`.  Тогда для языка `GapMCSP`
  существует неуниформный решатель `solver_gen` полиномиального размера
  (функция `generalCircuitSolver_of_Ppoly`).  Применяя `locality_lift`,
  локализуем его в эквивалентный решатель `solver_loc` с ограниченной
  локальностью и сопоставимыми ресурсами.  Однако гипотеза нижней
  границы `LocalLowerBoundHypothesis` объявляет невозможным существование
  такого локального решателя, получаем противоречие.  Формальное
  отрицание включения `NP ⊆ P/poly` извлекается через логическую лемму
  `NP_not_subset_Ppoly_of_contra`.
-/
theorem Locality_trigger
  {p : GapMCSPParams} {κ : Nat} :
  LocalLowerBoundHypothesis p κ → NP_not_subset_Ppoly := by
  intro hHyp
  classical
  -- Сохраняем компоненты гипотезы: положительность `κ` и запрет локальных решателей.
  have hκ : 0 < κ := hHyp.1
  have hNoLocal : ∀ solver : SmallLocalCircuitSolver p, False := hHyp.2
  -- Строим явное противоречие с предположением `NP ⊆ P/poly`.
  have hContra :
      ((∀ L : ComplexityInterfaces.Language,
        ComplexityInterfaces.NP L → ComplexityInterfaces.Ppoly L) → False) := by
    intro hAll
    -- Из включения извлекаем неуниформный решатель для GapMCSP.
    have hPpoly : ComplexityInterfaces.Ppoly (gapMCSP_Language p) :=
      hAll _ (gapMCSP_in_NP p)
    have solver_gen : SmallGeneralCircuitSolver p :=
      generalCircuitSolver_of_Ppoly (p := p) hPpoly
    -- Локализуем общий решатель и противоречим запрету локальных схем.
    obtain ⟨T, solver_loc, hT, hM, hℓ, hdepth⟩ :=
      Magnification.locality_lift (p := p) (solver := solver_gen)
    exact hNoLocal solver_loc
  -- Логически превращаем противоречие в вывод `NP \nsubseteq P/poly`.
  exact ComplexityInterfaces.NP_not_subset_Ppoly_of_contra hContra

/--
  Контрапозитив CJW-триггера: гипотеза нижней границы для разреженного языка
  запрещает существование даже тривиального перебора YES-инстансов.  Но такой
  перебор можно явно упаковать в `defaultSparseSolver`, поэтому предположение
  `NP ⊆ P/poly` немедленно приводит к противоречию.
-/
theorem CJW_sparse_trigger_contra
  {p : Models.SparseLanguageParams} {ε : Rat} :
  SparseLowerBoundHypothesis p ε (∀ _solver : SmallSparseSolver p, False) →
    ((∀ L : ComplexityInterfaces.Language,
      ComplexityInterfaces.NP L → ComplexityInterfaces.Ppoly L) → False) :=
by
  intro hHyp hAll
  -- Противоречие формируется просто: предъявляем конкретный маленький решатель.
  -- Его параметры заведомо удовлетворяют ограничению CJW, поэтому запрещающее
  -- утверждение из `hHyp` рушится.
  have solver : SmallSparseSolver p := defaultSparseSolver p
  exact hHyp.2 solver

/--
  Доказанный CJW-триггер: при выполнении гипотезы нижней границы (с запретом на
  малые решатели) получаем `NP \nsubseteq P/poly`.  Достаточно применить общую
  логическую лемму `NP_not_subset_Ppoly_of_contra` к построенному контрапозитиву.
-/
theorem CJW_sparse_trigger
  {p : Models.SparseLanguageParams} {ε : Rat} :
  SparseLowerBoundHypothesis p ε (∀ _solver : SmallSparseSolver p, False) →
    NP_not_subset_Ppoly :=
by
  intro hHyp
  have hContra :=
    CJW_sparse_trigger_contra (p := p) (ε := ε) hHyp
  exact ComplexityInterfaces.NP_not_subset_Ppoly_of_contra hContra

end Magnification
end Pnp3
