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

/-!
  В дополнение к основному shrinkage-факту нам понадобится ещё одна
  элементарная арифметическая оценка: если ошибка аппроксимации
  ограничена как `ε ≤ 1/(n+2)`, то автоматически `ε ≤ 1/2`.  Это
  полезно при связке с энтропийными оценками (Covering-Power).
-/

namespace Pnp3

namespace Core

/-- Подкуб, задающий ровно точку `x`. -/
@[simp] def pointSubcube {n : Nat} (x : BitVec n) : Subcube n :=
  fun i => some (x i)

/-- Точка всегда принадлежит своему точечному подкубу. -/
@[simp] lemma mem_pointSubcube_self {n : Nat} (x : BitVec n) :
    mem (pointSubcube x) x := by
  classical
  apply (mem_iff (β := pointSubcube x) (x := x)).mpr
  intro i b hb
  have hsome : some (x i) = some b := by
    exact hb
  exact Option.some.inj hsome

/-- Принадлежность точечному подкубу означает точное совпадение вектора. -/
@[simp] lemma mem_pointSubcube_iff {n : Nat} {x y : BitVec n} :
    mem (pointSubcube x) y ↔ x = y := by
  classical
  constructor
  · intro hmem
    have hprop := (mem_iff (β := pointSubcube x) (x := y)).mp hmem
    funext i
    have : pointSubcube x i = some (x i) := by simp [pointSubcube]
    have hy := hprop i (x i) this
    exact hy.symm
  · intro hxy
    subst hxy
    exact mem_pointSubcube_self x

end Core

namespace ThirdPartyFacts

open Core

/-- Параметры класса AC⁰, которые обычно фигурируют в switching-леммах.

* `n` — число входных переменных.
* `M` — размер формулы/схемы (число вентилей, листьев и т.д.).
* `d` — глубина схемы (число слоёв).

В более сложных вариантах добавляются ограничения на ширину DNF, число слоёв
OR/AND и пр., но для текущего интерфейса достаточно этих трёх чисел. -/
structure AC0Parameters where
  n : Nat
  M : Nat
  d : Nat
  deriving Repr

/--
  Предикат «малости» для AC⁰-параметров.  Он фиксирует грубое требование
  на рост размера `M` и глубины `d` относительно числа входных переменных
  `n`: даже после применения оценки `log₂(M+2)^(d+1)` результат остаётся
  не больше `n`.  Такой формат хорошо согласуется со switching-леммой,
  где глубина PDT контролируется именно логарифмом размера схемы.
-/
def AC0SmallEnough (ac0 : AC0Parameters) : Prop :=
  Nat.pow (Nat.log2 (ac0.M + 2)) (ac0.d + 1) ≤ ac0.n

/--
  Параметры для класса «локальных схем».  Мы сохраняем только наиболее
  необходимые числовые характеристики:

  * `n` — число входных бит (длина таблицы истинности).
  * `M` — общий размер схемы (например, число вентилей).
  * `ℓ` — параметр локальности: каждое выходное значение зависит не более
    чем от `ℓ` входов.
  * `depth` — число слоёв (глубина схемы).

  В дальнейшем эта структура служит лишь для записи тех величин, которые
  фигурируют в внешнем факте о shrinkage для локальных схем.  Дополнительные
  ограничения (например, на тип вентилей) можно будет добавить позже, не
  меняя интерфейс Lean.
-/
structure LocalCircuitParameters where
  n      : Nat
  M      : Nat
  ℓ      : Nat
  depth  : Nat
  deriving Repr

/--
  Предикат «малости» для локальных схем.  Мы требуем, чтобы суммарная длина
  «ствола» в shrinkage-свидетельстве была существенно меньше входной длины.
  Конкретно, ограничиваем произведение локальности на логарифмические факторы:

  `ℓ * (log₂(M+2) + depth + 1) ≤ n / 2`.

  Эта форма напрямую согласуется с оценкой на глубину PDT из
  `shrinkage_for_localCircuit` и даёт запас для применения Covering-Power.
-/
def LocalCircuitSmallEnough (params : LocalCircuitParameters) : Prop :=
  params.ℓ * (Nat.log2 (params.M + 2) + params.depth + 1) ≤ params.n / 2

/-- Уточняющая структура, описывающая гарантии shrinkage.

`depthBound` и `errorBound` — ожидаемые верхние оценки на глубину PDT и ошибку
аппроксимации, получаемые из multi-switching леммы.  Мы оставляем их в явном
виде, чтобы позднее подставлять сюда конкретные полиномиальные/квазиполиномиальные
формулы. -/
structure ShrinkageBounds where
  depthBound : Nat
  errorBound : Q
  deriving Repr

/--
  Усиленная версия shrinkage-факта: вместо полного PDT возвращается частичный
  сертификат с контролируемой глубиной хвостов.  Такой формат ближе к
  классическому изложению multi-switching-леммы и непосредственно пригоден для
  шага B, где важно знать глубину ствола и высоту хвостов по отдельности.
-/
axiom partial_shrinkage_for_AC0
    (params : AC0Parameters) (F : Family params.n) :
    ∃ (ℓ : Nat) (C : Core.PartialCertificate params.n ℓ F),
      ℓ ≤ Nat.log2 (params.M + 2) ∧
      C.depthBound + ℓ ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) ∧
      (0 : Core.Q) ≤ C.epsilon ∧
      C.epsilon ≤ (1 : Core.Q) / (params.n + 2)

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
