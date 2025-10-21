import Core.BooleanBasics
import Core.PDT
import Core.Atlas
import Core.SAL_Core
import ThirdPartyFacts.LeafBudget
import ThirdPartyFacts.Facts_Switching

open Core
open ThirdPartyFacts

namespace Pnp3
namespace Tests

/-!
# Smoke-тест SAL для игрушечного примера AC⁰

В этом файле мы не обращаемся к внешней multi-switching лемме. Вместо этого
мы явно строим объект `Shrinkage` для одномерной константной функции `f ≡ 0` и
проверяем, что конвейер `SAL` выдаёт корректный атлас. Такой тест выполняет две
задачи одновременно:

* демонстрирует, что поля структуры `Shrinkage` согласованы между собой;
* обеспечивает регрессионную проверку для вспомогательных лемм о покрытии
  `errU`, `listSubset` и т.п.
-/

/-- Константная функция нуля на одном бите. -/
@[simp] def f₀ : BitVec 1 → Bool := fun _ => false

/-- Константная функция единицы на одном бите. -/
@[simp] def f₁ : BitVec 1 → Bool := fun _ => true

/-- Тривиальный PDT: один лист, соответствующий всему кубу. -/
def trivialSubcube : Subcube 1 := fun _ => none

def trivialTree : PDT 1 := PDT.leaf trivialSubcube

/-- Удобное обозначение для единственного индекса в `Fin 1`. -/
@[simp] def idx0 : Fin 1 := ⟨0, by decide⟩

/-- Подкуб, фиксирующий нулевой бит равным `false`. -/
def zeroSubcube : Subcube 1 :=
  fun j => if h : j = idx0 then some false else trivialSubcube j

/-- Для удобства: список фиксаций, задающий `zeroSubcube`. -/
@[simp] def zeroFixes : List (BitFix 1) := [(idx0, false)]

/-- Полезная вспомогательная оценка: глубина нашего дерева нулевая. -/
lemma depth_trivialTree : PDT.depth trivialTree = 0 := by
  simp [trivialTree, PDT.depth]

/-- Для подкубов конечного размера у нас имеется decidable equality. -/
instance : DecidableEq (Subcube 1) := inferInstance

/-- Присваивание нулевого бита `false` даёт подкуб `zeroSubcube`. -/
lemma assign_trivial_eq_zeroSubcube :
    Subcube.assign trivialSubcube idx0 false = some zeroSubcube := by
  classical
  have hfree : trivialSubcube idx0 = none := rfl
  simp [Subcube.assign, zeroSubcube, trivialSubcube, idx0, hfree]

/-- Вектор `x = 0` удовлетворяет подкубу `zeroSubcube`. -/
lemma zeroSubcube_contains_zero :
    mem zeroSubcube (fun _ : BitVec 1 => false) := by
  classical
  have hassignMany :
      Subcube.assignMany trivialSubcube zeroFixes = some zeroSubcube := by
    simp [zeroFixes] using assign_trivial_eq_zeroSubcube
  have htop : mem trivialSubcube (fun _ : BitVec 1 => false) := by
    simp [trivialSubcube] using (mem_top (x := fun _ : BitVec 1 => false))
  have hcond : ∀ u ∈ zeroFixes, (fun _ : BitVec 1 => false) u.1 = u.2 := by
    intro u hu
    -- В списке всего одна фиксация, проверка сводится к очевидному равенству.
    have : u = (idx0, false) := by
      simp [zeroFixes] using hu
    subst this
    simp
  exact
    (mem_assignMany_iff (β := trivialSubcube) (γ := zeroSubcube)
      (updates := zeroFixes) hassignMany (x := fun _ : BitVec 1 => false)).2
      ⟨htop, hcond⟩

/-- Напротив, вектор `x = 1` не принадлежит подкубу `zeroSubcube`. -/
lemma zeroSubcube_excludes_one :
    ¬ mem zeroSubcube (fun _ : BitVec 1 => true) := by
  classical
  have hassignMany :
      Subcube.assignMany trivialSubcube zeroFixes = some zeroSubcube := by
    simp [zeroFixes] using assign_trivial_eq_zeroSubcube
  intro hmem
  have hdecomp :=
    (mem_assignMany_iff (β := trivialSubcube) (γ := zeroSubcube)
      (updates := zeroFixes) hassignMany (x := fun _ : BitVec 1 => true)).1 hmem
  -- Достаём условие на конкретную фиксацию и получаем противоречие.
  have hbit : (fun _ : BitVec 1 => true) idx0 = false := by
    have := hdecomp.2 (idx0, false) (by simp [zeroFixes])
    exact this
  exact hbit

/--
Конструкция shrinkage для игрушечного примера. Мы намеренно выбираем
подмножество листьев пустым списком: константа `0` уже идеально совпадает с
покрытием пустого семейства подкубов.
-/
@[simp] def shrinkage₀ : Shrinkage 1 :=
{ F        := [f₀]
  , t        := 0
  , ε        := 0
  , tree     := trivialTree
  , depth_le := by
      simp [depth_trivialTree]
  , Rsel     := fun _ => []
  , Rsel_sub := by
      intro f β hf hβ
      -- Пустой список листьев: противоречие с предположением о принадлежности.
      cases hβ
  , err_le   := by
      intro f hf
      have hf' : f = f₀ := List.mem_singleton.mp hf
      subst hf'
      exact (show (0 : Q) ≤ 0 from le_rfl)
}

/-- Атлас, полученный из shrinkage, содержит единственный подкуб. -/
@[simp] lemma atlas_from_shrinkage₀_dict :
    (Atlas.fromShrinkage shrinkage₀).dict = [trivialSubcube] := by
  rfl

/-- Финальное утверждение smoke-теста: атлас работает для семейства `[f₀]`. -/
lemma sal_smoke_ac0 :
    WorksFor (Atlas.fromShrinkage shrinkage₀) [f₀] := by
  classical
  exact SAL_from_Shrinkage shrinkage₀

/-- Эквивалентная формулировка через промежуточный объект `CommonPDT`. -/
lemma sal_smoke_ac0_via_commonPDT :
    WorksFor ((Core.shrinkage_to_commonPDT shrinkage₀).toAtlas) [f₀] := by
  classical
  exact
    (Core.commonPDT_to_atlas (C := Core.shrinkage_to_commonPDT shrinkage₀))

/-- Проверяем, что новая лемма о бюджете листьев для `CommonPDT` даёт ту же
оценку в тривиальном примере. -/
lemma commonPDT_leaf_budget_smoke :
    ∃ k : Nat,
      k ≤ (PDT.leaves shrinkage₀.tree).length ∧
      ((Core.shrinkage_to_commonPDT shrinkage₀).selectors f₀).dedup.length ≤ k := by
  classical
  have h :=
    leaf_budget_from_commonPDT
      (n := 1)
      (F := [f₀])
      (C := Core.shrinkage_to_commonPDT shrinkage₀)
  rcases h with ⟨k, hk, hbound⟩
  refine ⟨k, hk, ?_⟩
  have hf : f₀ ∈ ([f₀] : List (BitVec 1 → Bool)) := by simp
  have hbound' := hbound (f := f₀) hf
  exact hbound'

/-- Ошибка после `dedup` не превосходит исходного значения `ε`. -/
lemma commonPDT_err_dedup_smoke :
    Core.errU f₀
        (((Core.shrinkage_to_commonPDT shrinkage₀).selectors f₀).dedup)
      ≤ (Core.shrinkage_to_commonPDT shrinkage₀).epsilon := by
  classical
  have hf : f₀ ∈ ([f₀] : List (BitVec 1 → Bool)) := by simp
  have herr :=
    (err_le_of_dedup_commonPDT
      (n := 1)
      (F := [f₀])
      (C := Core.shrinkage_to_commonPDT shrinkage₀)
      (f := f₀)
      hf)
  exact herr

/--
Конструктивный shrinkage из `partial_shrinkage_for_AC0_of_constant` покрывает
тот же пример, что и ручной свидетель `shrinkage₀`. В частности, полученный
атлас работает для семейства `[f₀]`.
-/
lemma partial_shrinkage_constant_smoke :
    WorksFor (Atlas.fromShrinkage
      (Core.PartialCertificate.toShrinkage
        (n := 1) (ℓ := 0) (F := [f₀])
        (Classical.choose
          (partial_shrinkage_for_AC0_of_constant
            (params := { n := 1, M := 0, d := 0 })
            (F := [f₀])
            (hconst := by
              intro f hf
              have hf' : f = f₀ := List.mem_singleton.mp hf
              subst hf'
              refine ⟨false, ?_⟩
              intro x
              simp [f₀]
            ))))) [f₀] := by
  classical
  -- Фиксируем параметры и константное семейство.
  let params : AC0Parameters := { n := 1, M := 0, d := 0 }
  have hconst : ∀ {f : BitVec 1 → Bool}, f ∈ ([f₀] : Family params.n) → ∃ b, ∀ x, f x = b := by
    intro f hf
    have hf' : f = f₀ := List.mem_singleton.mp hf
    subst hf'
    exact ⟨false, by intro x; simp [f₀]⟩
  -- Получаем частичный сертификат и превращаем его в shrinkage.
  let witness := ThirdPartyFacts.ac0PartialWitness_of_constant
    (params := params) (F := ([f₀] : Family params.n))
    (hconst := by
      intro f hf
      have hf' : f = f₀ := List.mem_singleton.mp hf
      subst hf'
      exact ⟨false, by intro x; simp [f₀]⟩)
  let shrinkage := Core.PartialCertificate.toShrinkage
    (n := params.n) (ℓ := witness.level) (F := ([f₀] : Family params.n))
    witness.certificate
  -- Применяем общий факт SAL.
  simpa [params, shrinkage]
    using (SAL_from_Shrinkage shrinkage)

/--
Конструктивный свидетель для пары константных функций `[f₀, f₁]` также имеет нулевой
ствол и корректно покрывает обе функции: селекторы для `f₀` пусты, а для `f₁`
содержат весь куб.  Этот тест проверяет, что вспомогательный хелпер
`ac0PartialWitness_of_constant` корректно работает на семействах большего
размера и выдаёт ожидаемые покрывающие наборы подкубов.
-/
lemma partial_shrinkage_constant_pair_smoke :
    WorksFor (Atlas.fromShrinkage
      (Core.PartialCertificate.toShrinkage
        (n := 1) (ℓ := 0) (F := [f₀, f₁])
        (ThirdPartyFacts.ac0PartialWitness_of_constant
          (params := { n := 1, M := 0, d := 0 })
          (F := ([f₀, f₁] : Family 1))
          (by
            intro f hf
            have hf' : f = f₀ ∨ f = f₁ := by
              simp [Family, List.mem_cons] at hf
              exact hf
            cases hf' with
            | inl hzero =>
                subst hzero
                exact ⟨false, by intro x; simp [f₀]⟩
            | inr hone =>
                subst hone
                exact ⟨true, by intro x; simp [f₁]⟩)).certificate))
      [f₀, f₁] := by
  classical
  -- Для удобства зададим параметры и семейство явными именами.
  let params : AC0Parameters := { n := 1, M := 0, d := 0 }
  let F : Family params.n := [f₀, f₁]
  have hconst : ∀ f ∈ F, ∃ b : Bool, ∀ x, f x = b := by
    intro f hf
    have hf' : f = f₀ ∨ f = f₁ := by
      simpa [F, Family, List.mem_cons] using hf
    cases hf' with
    | inl hzero =>
        subst hzero
        exact ⟨false, by intro x; simp [f₀]⟩
    | inr hone =>
        subst hone
        exact ⟨true, by intro x; simp [f₁]⟩
  -- Конструируем свидетель с помощью хелпера.
  let witness := ThirdPartyFacts.ac0PartialWitness_of_constant
    (params := params) (F := F) hconst
  -- Убедимся, что глубина ствола равна нулю.
  have hlevel : witness.level = 0 := rfl
  -- Распакуем определение сертификата, чтобы явно увидеть селекторы.
  have hcert :=
    partial_shrinkage_for_AC0_of_constant
      (params := params) (F := F)
      (by
        intro f hf
        have hf' : f = f₀ ∨ f = f₁ := by
          simpa [F, Family, List.mem_cons] using hf
        cases hf' with
        | inl hzero =>
            subst hzero
            exact ⟨false, by intro x; simp [f₀]⟩
        | inr hone =>
            subst hone
            exact ⟨true, by intro x; simp [f₁]⟩)
  have hwitness_eq : witness.certificate =
      (Classical.choose hcert) := rfl
  -- Вычисляем селекторы для каждой функции.
  have hsel₀ : witness.certificate.selectors f₀ = [] := by
    simp [witness, params, F, ThirdPartyFacts.ac0PartialWitness_of_constant,
      hconst, hcert, hwitness_eq, partial_shrinkage_for_AC0_of_constant,
      f₀, f₁]
  have hsel₁ : witness.certificate.selectors f₁ = [fun _ => none] := by
    simp [witness, params, F, ThirdPartyFacts.ac0PartialWitness_of_constant,
      hconst, hcert, hwitness_eq, partial_shrinkage_for_AC0_of_constant,
      f₀, f₁]
  -- Проверяем, что покрытие действительно совпадает с исходными функциями.
  have hcover₀ : ∀ x, Core.coveredB (witness.certificate.selectors f₀) x = false := by
    intro x
    simpa [hsel₀, Core.coveredB]
  have hcover₁ : ∀ x, Core.coveredB (witness.certificate.selectors f₁) x = true := by
    intro x
    have hmem : Core.mem (fun _ => none) x := by
      simpa [Core.mem, Core.Subcube, Option.map, Option.bind] using (Core.mem_top (x := x))
    have hmemB : Core.memB (fun _ => none) x = true := by
      simpa [Core.memB, hmem]
    simpa [hsel₁, Core.coveredB, hmemB]
  -- Формируем shrinkage и передаём его в SAL.
  let shrinkage := Core.PartialCertificate.toShrinkage
    (n := params.n) (ℓ := witness.level) (F := F) witness.certificate
  have hworks := SAL_from_Shrinkage (C := shrinkage)
  -- Переписываем результат в нужную форму.
  simpa [params, F, witness, shrinkage, hlevel, hcover₀, hcover₁]
    using hworks

/--
  Даже когда `partial_shrinkage_for_AC0` недоступна, мы можем собрать shrinkage
  напрямую из точечного атласа (`pointPartialCertificate`) при условии, что
  размер куба `2^n` укладывается в требуемое ограничение
  `(log₂(M+2))^(d+1)`.  Этот smoke-тест проверяет, что конструкция из леммы
  `partial_shrinkage_for_AC0_of_pointBound` корректно интегрируется в SAL.
-/
lemma point_certificate_smoke :
    ∃ ℓ (C : Core.PartialCertificate 1 ℓ ([f₀, f₁] : Family 1)),
      WorksFor (Atlas.fromShrinkage
        (Core.PartialCertificate.toShrinkage
          (n := 1) (ℓ := ℓ) (F := [f₀, f₁]) C))
        ([f₀, f₁] : Family 1) := by
  classical
  -- Параметры соответствуют кубу размерности 1 и формуле размера 2.
  let params : AC0Parameters := { n := 1, M := 2, d := 0 }
  let F : Family params.n := [f₀, f₁]
  -- Гарантируем, что канонический атлас точек удовлетворяет требуемой оценке.
  have hdepth : Nat.pow 2 params.n
      ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) := by
    simp [params]
  -- Получаем сертификат из леммы `partial_shrinkage_for_AC0_of_pointBound`.
  obtain ⟨ℓ, C, hℓ, hdepthBound, hεnonneg, hεbound⟩ :=
    ThirdPartyFacts.partial_shrinkage_for_AC0_of_pointBound
      (params := params) (F := F) hdepth
  -- Преобразуем сертификат в shrinkage.
  let shrinkage :=
    Core.PartialCertificate.toShrinkage (n := params.n) (ℓ := ℓ) (F := F) C
  -- Применяем SAL к построенному shrinkage.
  have hworks := SAL_from_Shrinkage (S := shrinkage)
  -- Переводим утверждение в требуемую форму.
  have hfamily : shrinkage.F = F :=
    Core.PartialCertificate.toShrinkage_family
      (n := params.n) (ℓ := ℓ) (F := F) C
  refine ⟨ℓ, C, ?_⟩
  simpa [params, F, shrinkage, Atlas.fromShrinkage, hfamily]
    using hworks

end Tests
end Pnp3
