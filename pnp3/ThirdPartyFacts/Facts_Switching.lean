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
import Core.ShrinkageAC0
import AC0.Formulas
import ThirdPartyFacts.AC0Witness

/-!
  В дополнение к основному shrinkage-факту нам понадобится ещё одна
  элементарная арифметическая оценка: если ошибка аппроксимации
  ограничена как `ε ≤ 1/(n+2)`, то автоматически `ε ≤ 1/2`.  Это
  полезно при связке с энтропийными оценками (Covering-Power).
-/

namespace Pnp3

namespace ThirdPartyFacts

open Core

/-,
Параметры класса AC⁰, используемые далее, заданы в модуле
`ThirdPartyFacts.AC0Witness` (см. `AC0Parameters`).  Мы оставляем здесь
напоминание о семантике полей: `n` — число переменных, `M` — размер формулы,
`d` — глубина схемы.
-/
/-- Заготовка для "внешнего" факта: псевдослучайная multi-switching лемма
Servedio–Tan/Håstad.  Возвращает объект `Shrinkage`, совместимый с конвейером
SAL.  Параметры оценок записаны максимально прозрачно; их значения будут
уточняться по мере подключения конкретных источников.

Обратите внимание: мы фиксируем семейство функций `F` (список) и утверждаем,
что существует общая PDT глубины `t` и ошибка `ε`, удовлетворяющие стандартным
для SAL условиям.  В дальнейшем этот факт будет служить мостом между
комбинаторным ядром и оценками размера атласа. -/
theorem shrinkage_for_AC0
    (params : AC0Parameters) (F : Family params.n)
    [HasAC0PartialWitness params F] :
    ∃ (t : Nat) (ε : Q) (S : Shrinkage params.n),
      S.F = F ∧ S.t = t ∧ S.ε = ε ∧
        t ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) ∧
        (0 : Q) ≤ ε ∧
        ε ≤ (1 : Q) / (params.n + 2) :=
  by
    classical
    -- извлекаем частичный сертификат и переводим его в shrinkage
    let tail := partialCertificate_tailDepth_from_AC0 params F
    let C := partialCertificate_from_AC0 params F
    let S := Core.PartialCertificate.toShrinkage (n := params.n)
      (ℓ := tail) (F := F) C
    refine ⟨C.depthBound + tail, C.epsilon, S, ?_⟩
    -- сначала равенство семейства
    have hF : S.F = F := Core.PartialCertificate.toShrinkage_family
      (n := params.n) (ℓ := tail) (F := F) C
    refine And.intro hF ?_
    -- затем равенство глубины и ошибки
    have ht : S.t = C.depthBound + tail :=
      Core.PartialCertificate.toShrinkage_depth
        (n := params.n) (ℓ := tail) (F := F) C
    have hε : S.ε = C.epsilon :=
      Core.PartialCertificate.toShrinkage_epsilon
        (n := params.n) (ℓ := tail) (F := F) C
    refine And.intro ht ?_
    -- оставшиеся численные границы
    have htBound := partialCertificate_depthBound_add_tail_le
      (params := params) (F := F)
    have hε0 := partialCertificate_epsilon_nonneg
      (params := params) (F := F)
    have hεBound := partialCertificate_epsilon_le_inv
      (params := params) (F := F)
    exact And.intro hε (And.intro htBound (And.intro hε0 hεBound))

/-!
  Внешний факт для локальных схем: после применения подходящих ограничений
  схема становится «малой» PDT.  Конкретные численные границы отражают
  стандартные оценки: глубина дерева пропорциональна произведению локальности
  и логарифмических факторов по размеру и глубине схемы.
-/
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
  Внешний факт для локальных схем: наличие экземпляра `HasLocalCircuitWitness`
  предоставляет нужный shrinkage-сертификат.  Он упакован в структуру
  `LocalCircuitWitness`, чтобы последующие леммы могли свободно извлекать
  численные ограничения.
-/
class HasLocalCircuitWitness
    (params : LocalCircuitParameters) (F : Family params.n) : Type where
  /-- Shrinkage-сертификат для семейства `F` с локальными параметрами. -/
  witness : LocalCircuitWitness params F

/--
Экземпляр `HasLocalCircuitWitness` непосредственно содержит shrinkage-
сертификат, поэтому определение ниже просто извлекает его и возвращает в
явном виде.  Все численные ограничения уже упакованы в полях структуры.
-/
noncomputable def localCircuitWitness
    (params : LocalCircuitParameters) (F : Family params.n)
    [w : HasLocalCircuitWitness params F] :
    LocalCircuitWitness params F :=
  w.witness

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

/--
  В дополнение к атласу полезно иметь явный shrinkage-сертификат, который
  сохраняет дерево и выбор листьев.  Он используется на шаге B.
-/
noncomputable def certificate_from_AC0
    (params : AC0Parameters) (F : Family params.n)
    [HasAC0PartialWitness params F] :
    Core.Shrinkage params.n :=
  let witness := ac0PartialWitness params F
  Core.PartialCertificate.toShrinkage
    (n := params.n)
    (ℓ := witness.tailDepth)
    (F := F)
    witness.certificate

/-- Удобная оболочка: сразу извлекаем атлас из факта shrinkage.  Эта
функция подчёркивает, что на практике мы используем именно словарь подкубов,
а не сам PDT. -/
noncomputable def atlas_from_AC0
    (params : AC0Parameters) (F : Family params.n)
    [HasAC0PartialWitness params F] : Atlas params.n :=
  Atlas.fromShrinkage (certificate_from_AC0 params F)

/-- Семейство в сертификате AC⁰ совпадает с исходным списком `F`. -/
lemma certificate_from_AC0_family
    (params : AC0Parameters) (F : Family params.n)
    [HasAC0PartialWitness params F] :
    (certificate_from_AC0 params F).F = F := by
  classical
  let witness := ac0PartialWitness params F
  have h := Core.PartialCertificate.toShrinkage_family
    (n := params.n)
    (ℓ := witness.tailDepth)
    (F := F)
    witness.certificate
  have hgoal := h
  dsimp [certificate_from_AC0, witness] at hgoal
  exact hgoal

/-- Свойство корректности атласа, полученного из внешнего shrinkage.
    Оно напрямую следует из `SAL_from_Shrinkage`. -/
theorem atlas_from_AC0_works
    (params : AC0Parameters) (F : Family params.n)
    [HasAC0PartialWitness params F] :
    WorksFor (atlas_from_AC0 params F) F := by
  classical
  have hworks : WorksFor (Atlas.fromShrinkage (certificate_from_AC0 params F))
      (certificate_from_AC0 params F).F :=
    SAL_from_Shrinkage (certificate_from_AC0 params F)
  simpa [atlas_from_AC0, certificate_from_AC0_family]

lemma certificate_from_AC0_depth_bound
    (params : AC0Parameters) (F : Family params.n)
    [HasAC0PartialWitness params F] :
    (Core.Shrinkage.depthBound
      (S := certificate_from_AC0 params F))
      ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) := by
  classical
  let witness := ac0PartialWitness params F
  have hbound := witness.depth_le
  have hrewrite := Core.PartialCertificate.toShrinkage_depth
    (n := params.n)
    (ℓ := witness.tailDepth)
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
    (params : AC0Parameters) (F : Family params.n)
    [HasAC0PartialWitness params F] :
    Core.Shrinkage.errorBound
      (S := certificate_from_AC0 params F)
      ≤ (1 : Core.Q) / (params.n + 2) := by
  classical
  let witness := ac0PartialWitness params F
  have hbound := witness.epsilon_le_inv
  have hrewrite := Core.PartialCertificate.toShrinkage_epsilon
    (n := params.n)
    (ℓ := witness.tailDepth)
    (F := F)
    witness.certificate
  have htarget := Eq.subst
    (motive := fun ε => ε ≤ (1 : Core.Q) / (params.n + 2))
    (Eq.symm hrewrite) hbound
  change (certificate_from_AC0 params F).ε ≤ (1 : Core.Q) / (params.n + 2)
  dsimp [certificate_from_AC0, witness] at htarget ⊢
  exact htarget

/-- Ошибка сертификата AC⁰ неотрицательна.  Это важное условие для части B. -/
lemma certificate_from_AC0_eps_nonneg
    (params : AC0Parameters) (F : Family params.n)
    [HasAC0PartialWitness params F] :
    (0 : Core.Q) ≤ Core.Shrinkage.errorBound
      (S := certificate_from_AC0 params F) := by
  classical
  let witness := ac0PartialWitness params F
  have h := witness.epsilon_nonneg
  have hrewrite := Core.PartialCertificate.toShrinkage_epsilon
    (n := params.n)
    (ℓ := witness.tailDepth)
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
    (params : AC0Parameters) (F : Family params.n)
    [HasAC0PartialWitness params F] :
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
    (params : AC0Parameters) (F : Family params.n)
    [HasAC0PartialWitness params F] :
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
    (params : AC0Parameters) (F : Family params.n)
    [HasAC0PartialWitness params F] :
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

theorem shrinkage_for_localCircuit
    (params : LocalCircuitParameters) (F : Family params.n)
    [HasLocalCircuitWitness params F] :
    ∃ (t : Nat) (ε : Q) (S : Shrinkage params.n),
      S.F = F ∧ S.t = t ∧ S.ε = ε ∧
        t ≤ params.ℓ * (Nat.log2 (params.M + 2) + params.depth + 1) ∧
        (0 : Q) ≤ ε ∧
        ε ≤ (1 : Q) / (params.n + 2) := by
  classical
  let witness := localCircuitWitness params F
  refine ⟨witness.shrinkage.t, witness.shrinkage.ε, witness.shrinkage, ?_⟩
  refine And.intro witness.family_eq ?_
  refine And.intro rfl ?_
  refine And.intro rfl ?_
  refine And.intro witness.depth_le ?_
  refine And.intro witness.epsilon_nonneg ?_
  exact witness.epsilon_le_inv

end ThirdPartyFacts
end Pnp3
