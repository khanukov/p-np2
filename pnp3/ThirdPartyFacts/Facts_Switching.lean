/-
  pnp3/ThirdPartyFacts/Facts_Switching.lean

  Здесь мы концентрируем все внешние допущения типа "мульти-switching лемма",
  которые в дальнейшем подключаются как готовые факты.  Формально они оформлены
  как Lean-аксиомы, но снабжены подробными комментариями, чтобы позднее было
  понятно, какие именно параметры предстоит доказать (или импортировать из
  внешних источников).

  На данном шаге нам достаточно интерфейса: "из параметров семейства AC⁰"
  следует существование объекта `Shrinkage`, который затем конвейер SAL
  превращает в общий атлас.
-/
import Mathlib.Algebra.Order.Field.Basic
import Core.BooleanBasics
import Core.SAL_Core
import Core.ShrinkageWitness
import AC0.Formulas
import ThirdPartyFacts.SwitchingParameters
import ThirdPartyFacts.HastadMSL

/-!
  В дополнение к основному shrinkage-факту нам понадобится ещё одна
  элементарная арифметическая оценка: если ошибка аппроксимации
  ограничена как `ε ≤ 1/(n+2)`, то автоматически `ε ≤ 1/2`.  Это
  полезно при связке с энтропийными оценками (Covering-Power).
-/

namespace Pnp3

namespace ThirdPartyFacts

open Core

/-- Параметры класса AC⁰, которые обычно фигурируют в switching-леммах.

* `n` — число входных переменных.
* `M` — размер формулы/схемы (число вентилей, листьев и т.д.).
* `d` — глубина схемы (число слоёв).

В более сложных вариантах добавляются ограничения на ширину DNF, число слоёв
OR/AND и пр., но для текущего интерфейса достаточно этих трёх чисел. -/
/-
  Усиленная версия shrinkage-факта: вместо полного PDT возвращается частичный
  сертификат с контролируемой глубиной хвостов.  Такой формат ближе к
  классическому изложению multi-switching-леммы и непосредственно пригоден для
  шага B, где важно знать глубину ствола и высоту хвостов по отдельности.  На
  текущем этапе мы рассматриваем это утверждение как внешнюю предпосылку и
  используем его для извлечения явных свидетелей.
-/
axiom partial_shrinkage_for_AC0
    (params : AC0Parameters) (F : Family params.n) :
    ∃ (ℓ : Nat) (C : Core.PartialCertificate params.n ℓ F),
      ℓ ≤ Nat.log2 (params.M + 2) ∧
      C.depthBound + ℓ ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) ∧
      (0 : Core.Q) ≤ C.epsilon ∧
      C.epsilon ≤ (1 : Core.Q) / (params.n + 2)

/-!
  В качестве первого шага к полной конструктивной multi-switching лемме
  реализуем частный случай: семейство `F` состоит из константных функций.
  В этой ситуации частичный shrinkage-сертификат строится вручную: ствол —
  одиночный лист, покрывающий весь булев куб, хвосты отсутствуют, а селекторы
  либо пусты (для константы `0`), либо содержат единственный лист (для
  константы `1`).  Несмотря на простоту случая, аккуратно прописанная версия
  полезна в тестах и позволяет проверять пайплайн SAL без обращения к
  аксиоме.
-/
lemma partial_shrinkage_for_AC0_of_constant
    (params : AC0Parameters) (F : Family params.n)
    (hconst : ∀ {f : Core.BitVec params.n → Bool}, f ∈ F →
        ∃ b : Bool, ∀ x, f x = b) :
    ∃ (C : Core.PartialCertificate params.n 0 F),
      C.depthBound ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) ∧
      (0 : Core.Q) ≤ C.epsilon ∧
      C.epsilon ≤ (1 : Core.Q) / (params.n + 2) := by
  classical
  -- Ствол частичного дерева: единственный лист, соответствующий всему кубу.
  let β₀ : Core.Subcube params.n := fun _ => none
  let trunk : Core.PDT params.n := Core.PDT.leaf β₀
  let selectorsFun : (Core.BitVec params.n → Bool) → List (Core.Subcube params.n) :=
    fun f =>
      if h : ∀ x, f x = true then [β₀] else []
  -- Определяем частичный сертификат. У хвостов глубина нулевая, поэтому
  -- `PartialDT.ofPDT` подходит идеально.
  let certificate : Core.PartialCertificate params.n 0 F :=
    { witness := Core.PartialDT.ofPDT trunk
      depthBound := 0
      epsilon := 0
      trunk_depth_le := by
        -- Глубина листа равна нулю.
        simp [Core.PartialDT.ofPDT, trunk, Core.PDT.depth]
      selectors := selectorsFun
      selectors_sub := by
        intro f β hf hβ
        -- Для функций семейства существует булевое значение, задающее константу.
        obtain ⟨b, hb⟩ := hconst hf
        have hβ' : β = β₀ := by
          by_cases hbTrue : b = true
          · -- Положительная ветка: список селекторов состоит из одного листа.
            have hAll : ∀ x, f x = true := by
              intro x; simpa [hbTrue] using hb x
            have := hβ
            simpa [selectorsFun, hAll] using this
          · -- Отрицательная ветка невозможна: список селекторов пуст.
            have hnot : ¬∀ x, f x = true := by
              intro hAll
              have hfx := hb (fun _ => false)
              have htrue := hAll (fun _ => false)
              have : b = true := (Eq.symm hfx).trans htrue
              exact hbTrue this
            have : False := by
              have := hβ
              simp [selectorsFun, hnot] at this
            exact this.elim
        subst hβ'
        -- Покажем, что единственный лист действительно принадлежит реализованному дереву.
        have hLeaves : Core.PDT.leaves (Core.PartialDT.ofPDT trunk).realize = [β₀] := by
          simp [Core.PartialDT.realize_ofPDT, trunk, Core.PDT.leaves]
        have hmem : β₀ ∈ [β₀] := by simp
        simpa [hLeaves]
      err_le := by
        intro f hf
        obtain ⟨b, hb⟩ := hconst hf
        have hval : ∀ x, f x = b := hb
        -- Достаточно показать, что покрытие `selectors f` совпадает с константой `b`.
        have hcover : ∀ x, Core.coveredB (selectorsFun f) x = b := by
          intro x
          by_cases hbIsTrue : b = true
          · -- Положительный случай: единственный лист покрывает весь куб.
            have hmem : Core.mem β₀ x := by
              simpa [β₀] using (Core.mem_top (x := x))
            have hmemB : Core.memB β₀ x = true := by
              simpa [Core.mem, β₀] using hmem
            have hAll : ∀ x, f x = true := by
              intro x'; simpa [hbIsTrue] using hb x'
            have hcovTrue : Core.coveredB (selectorsFun f) x = true := by
              simp [selectorsFun, hAll, hmemB, Core.coveredB, β₀]
            simpa [hbIsTrue] using hcovTrue
          · -- Отрицательный случай: список пуст, покрытие равно `false`.
            have hnot : ¬∀ x, f x = true := by
              intro hAll
              have hfx := hb (fun _ => false)
              have htrue := hAll (fun _ => false)
              have : b = true := (Eq.symm hfx).trans htrue
              exact hbIsTrue this
            have hcovFalse : Core.coveredB (selectorsFun f) x = false := by
              simp [selectorsFun, hnot, Core.coveredB]
            cases hbVal : b with
            | false => simpa [hbVal] using hcovFalse
            | true => exact (hbIsTrue hbVal).elim
        -- Ошибка равна нулю, потому что функции совпадают на всех точках.
        have herr := Core.errU_eq_zero_of_agree (f := f)
          (Rset := selectorsFun f) (h := fun x => by
            simpa [hcover x, hval x])
        have herr' : Core.errU f (selectorsFun f) = 0 := herr
        simpa [herr'] using (show (0 : Core.Q) ≤ 0 from le_rfl)
    }
  -- Подставляем построенный сертификат и убеждаемся, что численные ограничения выполняются.
  refine ⟨certificate, ?_⟩
  refine And.intro ?depthBound ?epsBounds
  · -- Полная глубина равна нулю, поэтому подходит любая верхняя оценка.
    have hpow : (0 : Nat) ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) :=
      Nat.zero_le _
    simpa [certificate] using hpow
  · refine And.intro ?epsNonneg ?epsLe
    · simp [certificate]
    · have hden : (0 : Core.Q) < (params.n + 2 : Core.Q) := by
        have : (0 : Nat) < params.n + 2 := Nat.succ_pos (params.n + 1)
        exact_mod_cast this
      have hfrac : (0 : Core.Q) ≤ (1 : Core.Q) / (params.n + 2 : Core.Q) :=
        div_nonneg (show (0 : Core.Q) ≤ 1 by exact zero_le_one) (le_of_lt hden)
      simpa [certificate] using hfrac

/--
  Constructive variant of `partial_shrinkage_for_AC0`: if the canonical point
  enumeration already fits under the desired depth bound, we can assemble the
  certificate without appealing to the external axiom.  This lemma is useful as
  a sanity check and for early experiments where the combinatorial shrinking is
  replaced by exhaustive enumeration.
-/
lemma partial_shrinkage_for_AC0_of_pointBound
    (params : AC0Parameters) (F : Family params.n)
    (hdepth : Nat.pow 2 params.n
        ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1)) :
    ∃ (ℓ : Nat) (C : Core.PartialCertificate params.n ℓ F),
      ℓ ≤ Nat.log2 (params.M + 2) ∧
      C.depthBound + ℓ ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) ∧
      (0 : Core.Q) ≤ C.epsilon ∧
      C.epsilon ≤ (1 : Core.Q) / (params.n + 2) := by
  classical
  refine ⟨0, pointPartialCertificate params.n F, ?_⟩
  refine And.intro ?hlevel ?hrest
  · exact Nat.zero_le _
  · refine And.intro ?hdepthBound ?herrBounds
    · have hcanon :=
        pointPartialCertificate_depth_le (n := params.n) (F := F)
      have hfinal := Nat.le_trans hcanon hdepth
      simpa [pointPartialCertificate, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using hfinal
    · refine And.intro ?hε_nonneg ?hε_le
      · simp [pointPartialCertificate]
      · have hden : (0 : Core.Q) < (params.n + 2 : Core.Q) := by
          have : (0 : Nat) < params.n + 2 := Nat.succ_pos (params.n + 1)
          exact_mod_cast this
        have hbound : (0 : Core.Q) ≤ (1 : Core.Q) / (params.n + 2 : Core.Q) :=
          div_nonneg (by exact zero_le_one) (le_of_lt hden)
        simpa [pointPartialCertificate] using hbound

/--
`AC0PartialWitness` собирает в одном месте весь набор параметров, выдаваемых
частичным shrinkage-фактом для AC⁰.  Помимо самого частичного PDT и глубины
хвостов мы сохраняем численные оценки, необходимые для шага B, что избавляет
от многократного обращения к `Classical.choose`.
-/
structure AC0PartialWitness
    (params : AC0Parameters) (F : Family params.n) where
  /-- Максимальная глубина хвостов частичного дерева. -/
  level          : Nat
  /-- Частичный shrinkage-сертификат. -/
  certificate    : Core.PartialCertificate params.n level F
  /-- Ограничение `level ≤ log₂(M+2)`. -/
  level_le_log   : level ≤ Nat.log2 (params.M + 2)
  /-- Верхняя граница на суммарную глубину. -/
  depth_le       : certificate.depthBound + level
      ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1)
  /-- Неотрицательность ошибки. -/
  epsilon_nonneg : (0 : Core.Q) ≤ certificate.epsilon
  /-- Верхняя оценка ошибки `ε ≤ 1/(n+2)`. -/
  epsilon_le_inv : certificate.epsilon ≤ (1 : Core.Q) / (params.n + 2)

/--
Превращаем частичный свидетель в структуру `MultiSwitchingWitness`.  Отдельный
хелпер позволяет избегать дублирования при дальнейших преобразованиях: любые
дополнительные оценки из `AC0PartialWitness` автоматически переносятся в итоговый
объект, пригодный для последующего перехода к SAL.
-/
noncomputable def AC0PartialWitness.toMultiSwitching
    {params : AC0Parameters} {F : Family params.n}
    (W : AC0PartialWitness params F) :
    MultiSwitchingWitness params F :=
  MultiSwitchingWitness.ofPartialCertificate
    (params := params) (F := F) (ℓ := W.level)
    W.certificate
    W.level_le_log
    W.depth_le
    W.epsilon_nonneg
    W.epsilon_le_inv

/--
Из внешнего факта `partial_shrinkage_for_AC0` конструируем объект `AC0PartialWitness`.
Доказательство чисто распаковочное: мы последовательно извлекаем глубину хвостов,
частичный PDT и перечисленные численные границы.
-/
noncomputable def ac0PartialWitness
    (params : AC0Parameters) (F : Family params.n) :
    AC0PartialWitness params F := by
  classical
  let h := partial_shrinkage_for_AC0 params F
  let ℓ := Classical.choose h
  let rest := Classical.choose_spec h
  let C := Classical.choose rest
  have hprop := Classical.choose_spec rest
  refine
    { level := ℓ
      certificate := C
      level_le_log := ?_
      depth_le := ?_
      epsilon_nonneg := ?_
      epsilon_le_inv := ?_ }
  · exact hprop.left
  · exact hprop.right.left
  · exact hprop.right.right.left
  · exact hprop.right.right.right

/--
  Constructive partial witness for constant families: wraps the certificate
  produced by `partial_shrinkage_for_AC0_of_constant` into the structured record
  used across the SAL pipeline.  This avoids any appeal to the multi-switching
  axiom in simple smoke tests.
-/
noncomputable def ac0PartialWitness_of_constant
    (params : AC0Parameters) (F : Family params.n)
    (hconst : ∀ f ∈ F, ∃ b : Bool, ∀ x, f x = b) :
    AC0PartialWitness params F := by
  classical
  have hconst' : ∀ {f : Core.BitVec params.n → Bool}, f ∈ F →
      ∃ b : Bool, ∀ x, f x = b := by
    intro f hf; exact hconst f hf
  let hexists :=
    partial_shrinkage_for_AC0_of_constant
      (params := params) (F := F) hconst'
  let C := Classical.choose hexists
  have hprop := Classical.choose_spec hexists
  have hdepth :
      C.depthBound ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) :=
    hprop.left
  have hε_nonneg : (0 : Core.Q) ≤ C.epsilon :=
    hprop.right.left
  have hε_le : C.epsilon ≤ (1 : Core.Q) / (params.n + 2) :=
    hprop.right.right
  refine
    { level := 0
      certificate := C
      level_le_log := by exact Nat.zero_le _
      depth_le := by simpa using hdepth
      epsilon_nonneg := hε_nonneg
      epsilon_le_inv := hε_le }

/-- Высота хвостов частичного PDT из AC⁰-свидетельства. -/
noncomputable def partialCertificate_level_from_AC0
    (params : AC0Parameters) (F : Family params.n) : Nat :=
  (ac0PartialWitness params F).level

/-- Сам частичный shrinkage-сертификат из факта `partial_shrinkage_for_AC0`. -/
noncomputable def partialCertificate_from_AC0
    (params : AC0Parameters) (F : Family params.n) :
    Core.PartialCertificate params.n
      (partialCertificate_level_from_AC0 params F) F :=
  (ac0PartialWitness params F).certificate

/-- Ограничение на глубину хвостов: `ℓ ≤ log₂(M+2)`. -/
lemma partialCertificate_level_from_AC0_le
    (params : AC0Parameters) (F : Family params.n) :
    partialCertificate_level_from_AC0 params F ≤ Nat.log2 (params.M + 2) := by
  classical
  change (ac0PartialWitness params F).level ≤ Nat.log2 (params.M + 2)
  exact (ac0PartialWitness params F).level_le_log

/-- Граница на суммарную глубину: `depthBound + ℓ` ограничена классической оценкой. -/
lemma partialCertificate_depthBound_add_level_le
    (params : AC0Parameters) (F : Family params.n) :
    (partialCertificate_from_AC0 params F).depthBound
        + partialCertificate_level_from_AC0 params F
      ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) := by
  classical
  change
      (ac0PartialWitness params F).certificate.depthBound
        + (ac0PartialWitness params F).level
        ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1)
  exact (ac0PartialWitness params F).depth_le

/-- Неотрицательность ошибки частичного сертификата. -/
lemma partialCertificate_epsilon_nonneg
    (params : AC0Parameters) (F : Family params.n) :
    (0 : Core.Q) ≤ (partialCertificate_from_AC0 params F).epsilon := by
  classical
  change (0 : Core.Q)
      ≤ (ac0PartialWitness params F).certificate.epsilon
  exact (ac0PartialWitness params F).epsilon_nonneg

/-- Оценка ошибки сверху: `ε ≤ 1/(n+2)`. -/
lemma partialCertificate_epsilon_le_inv
    (params : AC0Parameters) (F : Family params.n) :
    (partialCertificate_from_AC0 params F).epsilon
      ≤ (1 : Core.Q) / (params.n + 2) := by
  classical
  change (ac0PartialWitness params F).certificate.epsilon
      ≤ (1 : Core.Q) / (params.n + 2)
  exact (ac0PartialWitness params F).epsilon_le_inv

/--
Multi-switching свидетель, полученный напрямую из аксиомы
`partial_shrinkage_for_AC0`.  Благодаря этому глобальная аксиома в модуле
`HastadMSL` больше не требуется: все необходимые данные извлекаются из
частичного сертификата и упаковываются в структуру `MultiSwitchingWitness`.
-/
noncomputable def hastad_multiSwitching
    (params : AC0Parameters) (F : Family params.n) :
    MultiSwitchingWitness params F :=
  (ac0PartialWitness params F).toMultiSwitching

/-- Заготовка для "внешнего" факта: псевдослучайная multi-switching лемма
Servedio–Tan/Håstad.  Возвращает объект `Shrinkage`, совместимый с конвейером
SAL.  Параметры оценок записаны максимально прозрачно; их значения будут
уточняться по мере подключения конкретных источников.

Обратите внимание: мы фиксируем семейство функций `F` (список) и утверждаем,
что существует общая PDT глубины `t` и ошибка `ε`, удовлетворяющие стандартным
для SAL условиям.  В дальнейшем этот факт будет служить мостом между
комбинаторным ядром и оценками размера атласа. -/
theorem shrinkage_for_AC0
    (params : AC0Parameters) (F : Family params.n) :
    ∃ (t : Nat) (ε : Q) (S : Shrinkage params.n),
      S.F = F ∧ S.t = t ∧ S.ε = ε ∧
        t ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) ∧
        (0 : Q) ≤ ε ∧
        ε ≤ (1 : Q) / (params.n + 2) :=
  by
    classical
    -- извлекаем частичный сертификат и переводим его в shrinkage
    let ℓ := partialCertificate_level_from_AC0 params F
    let C := partialCertificate_from_AC0 params F
    let S := Core.PartialCertificate.toShrinkage (n := params.n)
      (ℓ := ℓ) (F := F) C
    refine ⟨C.depthBound + ℓ, C.epsilon, S, ?_⟩
    -- сначала равенство семейства
    have hF : S.F = F := Core.PartialCertificate.toShrinkage_family
      (n := params.n) (ℓ := ℓ) (F := F) C
    refine And.intro hF ?_
    -- затем равенство глубины и ошибки
    have ht : S.t = C.depthBound + ℓ :=
      Core.PartialCertificate.toShrinkage_depth
        (n := params.n) (ℓ := ℓ) (F := F) C
    have hε : S.ε = C.epsilon :=
      Core.PartialCertificate.toShrinkage_epsilon
        (n := params.n) (ℓ := ℓ) (F := F) C
    refine And.intro ht ?_
    -- оставшиеся численные границы
    have htBound := partialCertificate_depthBound_add_level_le
      (params := params) (F := F)
    have hε0 := partialCertificate_epsilon_nonneg
      (params := params) (F := F)
    have hεBound := partialCertificate_epsilon_le_inv
      (params := params) (F := F)
    exact And.intro hε (And.intro htBound (And.intro hε0 hεBound))

/--
  Внешний факт для локальных схем: после применения подходящих ограничений
  схема становится «малой» PDT.  Конкретные численные границы отражают
  стандартные оценки: глубина дерева пропорциональна произведению локальности
  и логарифмических факторов по размеру и глубине схемы.
-/
axiom shrinkage_for_localCircuit
    (params : LocalCircuitParameters) (F : Family params.n) :
    ∃ (t : Nat) (ε : Q) (S : Shrinkage params.n),
      S.F = F ∧ S.t = t ∧ S.ε = ε ∧
        t ≤ params.ℓ * (Nat.log2 (params.M + 2) + params.depth + 1) ∧
        (0 : Q) ≤ ε ∧
        ε ≤ (1 : Q) / (params.n + 2)

/--
`LocalCircuitWitness` фиксирует shrinkage-сертификат для локальных схем и все
соответствующие численные оценки.  Это избавляет от громоздкого вручного
распаковки `Classical.choose` в местах, где требуется использовать данный факт.
-/
structure LocalCircuitWitness
    (params : LocalCircuitParameters) (F : Family params.n) where
  /-- Shrinkage-сертификат для семейства `F`. -/
  shrinkage        : Shrinkage params.n
  /-- Семейство, зафиксированное в сертификате, совпадает с исходным `F`. -/
  family_eq        : shrinkage.F = F
  /-- Глубина PDT ограничена стандартной функцией от параметров схемы. -/
  depth_le         : shrinkage.t
      ≤ params.ℓ * (Nat.log2 (params.M + 2) + params.depth + 1)
  /-- Ошибка неотрицательна. -/
  epsilon_nonneg   : (0 : Q) ≤ shrinkage.ε
  /-- Ошибка не превосходит `1/(n+2)`. -/
  epsilon_le_inv   : shrinkage.ε ≤ (1 : Q) / (params.n + 2)

/--
Построение `LocalCircuitWitness` напрямую использует аксиому
`shrinkage_for_localCircuit`.  Из кортежа `(t, ε, S, …)` извлекаем сертифицирующее
дерево и последовательно переносим численные ограничения в поля структуры.
-/
noncomputable def localCircuitWitness
    (params : LocalCircuitParameters) (F : Family params.n) :
    LocalCircuitWitness params F := by
  classical
  let h := shrinkage_for_localCircuit params F
  let t := Classical.choose h
  let rest₁ := Classical.choose_spec h
  let ε := Classical.choose rest₁
  let rest₂ := Classical.choose_spec rest₁
  let S := Classical.choose rest₂
  have hspec := Classical.choose_spec rest₂
  refine
    { shrinkage := S
      family_eq := hspec.left
      depth_le := ?_
      epsilon_nonneg := ?_
      epsilon_le_inv := ?_ }
  · have hchain := hspec.right
    have ht : S.t = t := hchain.left
    have hrest := hchain.right
    have hdepth := hrest.right.left
    have hrewrite : t = S.t := Eq.symm ht
    have hconverted := Eq.subst (motive := fun x => x ≤ _) hrewrite hdepth
    exact hconverted
  · have hchain := hspec.right
    have hrest := hchain.right
    have hε := hrest.left
    have hfinal := hrest.right.right.left
    have hrewrite : ε = S.ε := Eq.symm hε
    have hconverted := Eq.subst (motive := fun x => (0 : Q) ≤ x) hrewrite hfinal
    exact hconverted
  · have hchain := hspec.right
    have hrest := hchain.right
    have hε := hrest.left
    have hfinal := hrest.right.right.right
    have hrewrite : ε = S.ε := Eq.symm hε
    have hconverted := Eq.subst (motive := fun x => x ≤ (1 : Q) / (params.n + 2))
      hrewrite hfinal
    exact hconverted

/--
  Техническая лемма: при любом `n` имеем `1 / (n + 2) ≤ 1 / 2`.
  Доказательство — аккуратная алгебра на ℚ: сводим утверждение к
  очевидному неравенству `2 ≤ n + 2` и раскрываем деление.
-/
lemma inv_nat_succ_succ_le_half (n : Nat) :
    (1 : Q) / (n + 2) ≤ (1 : Q) / 2 := by
  have hNat : (2 : Q) ≤ (n + 2 : Q) := by
    exact_mod_cast (Nat.le_add_left 2 n)
  have hpos : (0 : Q) < (2 : Q) := by norm_num
  have hdiv :=
    (one_div_le_one_div_of_le (a := (2 : Q)) (b := (n + 2 : Q)) hpos hNat)
  exact hdiv

/--
  Из оценки `ε ≤ 1 / (n + 2)` немедленно следует `ε ≤ 1 / 2`.
  Это условие нужно для дальнейших энтропийных оценок шара Хэмминга.
-/
lemma eps_le_half_of_eps_le_inv_nplus2 (n : Nat) {ε : Q}
    (h : ε ≤ (1 : Q) / (n + 2)) : ε ≤ (1 : Q) / 2 :=
  h.trans (inv_nat_succ_succ_le_half n)

/-- Удобная оболочка: сразу извлекаем атлас из факта shrinkage.  Эта
функция подчёркивает, что на практике мы используем именно словарь подкубов,
а не сам PDT. -/
noncomputable def atlas_from_AC0
    (params : AC0Parameters) (F : Family params.n) : Atlas params.n := by
  classical
  let h := shrinkage_for_AC0 params F
  let t := Classical.choose h
  let h₁ := Classical.choose_spec h
  let ε := Classical.choose h₁
  let h₂ := Classical.choose_spec h₁
  let S := Classical.choose h₂
  exact Atlas.fromShrinkage S

/-- Свойство корректности атласа, полученного из внешнего shrinkage.
    Оно напрямую следует из `SAL_from_Shrinkage`. -/
theorem atlas_from_AC0_works
    (params : AC0Parameters) (F : Family params.n) :
    WorksFor (atlas_from_AC0 params F) F := by
  classical
  let h := shrinkage_for_AC0 params F
  let t := Classical.choose h
  let h₁ := Classical.choose_spec h
  let ε := Classical.choose h₁
  let h₂ := Classical.choose_spec h₁
  let S := Classical.choose h₂
  have hspec := Classical.choose_spec h₂
  have hF : S.F = F := hspec.left
  have hworks : WorksFor (Atlas.fromShrinkage S) S.F :=
    SAL_from_Shrinkage S
  have hdict : Atlas.fromShrinkage S = atlas_from_AC0 params F := rfl
  have hworks' := hworks
  simp [hdict] at hworks'
  have hworks'' := hworks'
  simp [hF] at hworks''
  exact hworks''

/--
  В дополнение к атласу полезно иметь явный shrinkage-сертификат, который
  сохраняет дерево и выбор листьев.  Он используется на шаге B.
-/
noncomputable def certificate_from_AC0
    (params : AC0Parameters) (F : Family params.n) :
    Core.Shrinkage params.n :=
  let witness := ac0PartialWitness params F
  Core.PartialCertificate.toShrinkage
    (n := params.n)
    (ℓ := witness.level)
    (F := F)
    witness.certificate

lemma certificate_from_AC0_depth_bound
    (params : AC0Parameters) (F : Family params.n) :
    (Core.Shrinkage.depthBound
      (S := certificate_from_AC0 params F))
      ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) := by
  classical
  let witness := ac0PartialWitness params F
  have hbound := witness.depth_le
  have hrewrite := Core.PartialCertificate.toShrinkage_depth
    (n := params.n)
    (ℓ := witness.level)
    (F := F)
    witness.certificate
  have htarget := Eq.subst
    (motive := fun t => t ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1))
    (Eq.symm hrewrite) hbound
  change (certificate_from_AC0 params F).t
      ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1)
  dsimp [certificate_from_AC0, witness] at htarget ⊢
  exact htarget

lemma certificate_from_AC0_eps_bound
    (params : AC0Parameters) (F : Family params.n) :
    Core.Shrinkage.errorBound
      (S := certificate_from_AC0 params F)
      ≤ (1 : Core.Q) / (params.n + 2) := by
  classical
  let witness := ac0PartialWitness params F
  have hbound := witness.epsilon_le_inv
  have hrewrite := Core.PartialCertificate.toShrinkage_epsilon
    (n := params.n)
    (ℓ := witness.level)
    (F := F)
    witness.certificate
  have htarget := Eq.subst
    (motive := fun ε => ε ≤ (1 : Core.Q) / (params.n + 2))
    (Eq.symm hrewrite) hbound
  change (certificate_from_AC0 params F).ε ≤ (1 : Core.Q) / (params.n + 2)
  dsimp [certificate_from_AC0, witness] at htarget ⊢
  exact htarget

/-- Семейство в сертификате AC⁰ совпадает с исходным списком `F`. -/
lemma certificate_from_AC0_family
    (params : AC0Parameters) (F : Family params.n) :
    (certificate_from_AC0 params F).F = F := by
  classical
  let witness := ac0PartialWitness params F
  have h := Core.PartialCertificate.toShrinkage_family
    (n := params.n)
    (ℓ := witness.level)
    (F := F)
    witness.certificate
  have hgoal := h
  dsimp [certificate_from_AC0, witness] at hgoal
  exact hgoal

/-- Ошибка сертификата AC⁰ неотрицательна.  Это важное условие для части B. -/
lemma certificate_from_AC0_eps_nonneg
    (params : AC0Parameters) (F : Family params.n) :
    (0 : Core.Q) ≤ Core.Shrinkage.errorBound
      (S := certificate_from_AC0 params F) := by
  classical
  let witness := ac0PartialWitness params F
  have h := witness.epsilon_nonneg
  have hrewrite := Core.PartialCertificate.toShrinkage_epsilon
    (n := params.n)
    (ℓ := witness.level)
    (F := F)
    witness.certificate
  have hgoal := Eq.subst
    (motive := fun ε => (0 : Core.Q) ≤ ε)
    (Eq.symm hrewrite) h
  change (0 : Core.Q) ≤ (certificate_from_AC0 params F).ε
  dsimp [certificate_from_AC0, witness] at hgoal ⊢
  exact hgoal

/-- Из внешней границы `ε ≤ 1/(n+2)` выводим привычное условие `ε ≤ 1/2`. -/
lemma certificate_from_AC0_eps_le_half
    (params : AC0Parameters) (F : Family params.n) :
    Core.Shrinkage.errorBound
      (S := certificate_from_AC0 params F)
      ≤ (1 : Core.Q) / 2 := by
  classical
  have hbase := certificate_from_AC0_eps_bound (params := params) (F := F)
  exact eps_le_half_of_eps_le_inv_nplus2
    params.n (ε := Core.Shrinkage.errorBound (S := certificate_from_AC0 params F)) hbase

/--
Глубина ствола частичного дерева из AC⁰-сертификата ограничена классической
квазиполиномиальной функцией от размера и глубины схемы.
-/
lemma partial_from_AC0_trunk_depth_le
    (params : AC0Parameters) (F : Family params.n) :
    PDT.depth (Core.Shrinkage.partial (S := certificate_from_AC0 params F)).trunk
      ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) := by
  classical
  have hdepth :=
    Core.Shrinkage.depth_le_depthBound
      (S := certificate_from_AC0 params F)
  have hbound :=
    certificate_from_AC0_depth_bound (params := params) (F := F)
  have hbound' :
      Core.Shrinkage.depthBound (S := certificate_from_AC0 params F)
        ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) := hbound
  have htree_depth :
      PDT.depth (certificate_from_AC0 params F).tree
        ≤ Core.Shrinkage.depthBound (S := certificate_from_AC0 params F) := by
    exact hdepth
  have hpartial :
      PDT.depth (Core.Shrinkage.partial (S := certificate_from_AC0 params F)).trunk
        = PDT.depth (certificate_from_AC0 params F).tree := by
    rfl
  have hchain :
      PDT.depth (Core.Shrinkage.partial (S := certificate_from_AC0 params F)).trunk
        ≤ Core.Shrinkage.depthBound (S := certificate_from_AC0 params F) := by
    have htmp := htree_depth
    exact Eq.subst (motive := fun s => s ≤
        Core.Shrinkage.depthBound (S := certificate_from_AC0 params F))
      (Eq.symm hpartial) htmp
  exact hchain.trans hbound'

/--
Число листьев словаря из AC⁰-сертификата контролируется той же границей,
что и глубина: `|R| ≤ 2^{(log₂(M+2))^{d+1}}`.  Лемма напрямую использует
оценку из `ShrinkageWitness`.
-/
lemma partial_from_AC0_leafDict_len_le
    (params : AC0Parameters) (F : Family params.n) :
    (Core.Shrinkage.partial (S := certificate_from_AC0 params F)).leafDict.length
      ≤ Nat.pow 2 (Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1)) := by
  classical
  have hbase :=
    Core.Shrinkage.partial_leafDict_length_le_pow
      (S := certificate_from_AC0 params F)
  have hbound :
      Nat.pow 2 (Core.Shrinkage.depthBound (S := certificate_from_AC0 params F))
        ≤ Nat.pow 2 (Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1)) := by
    have hdepthBound :=
      certificate_from_AC0_depth_bound (params := params) (F := F)
    exact Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hdepthBound
  have hpartial_pow :
      Nat.pow 2 (certificate_from_AC0 params F).t
        ≤ Nat.pow 2 (Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1)) := by
    have htmp := hbound
    simp [Core.Shrinkage.depthBound] at htmp
    exact htmp
  have hgoal := hbase.trans hpartial_pow
  exact hgoal

end ThirdPartyFacts
end Pnp3
