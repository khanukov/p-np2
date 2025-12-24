/-
  pnp3/ThirdPartyFacts/ConstructiveSwitching.lean

  Первый шаг на пути к замене аксиомы `partial_shrinkage_for_AC0`
  полноценным доказательством.  В этом модуле мы реализуем два
  конструктивных сертификата shrinkage для самых простых семейств:

  * пустого семейства булевых функций,
  * семейства, состоящего из одной константной функции.

  Оба примера не требуют вероятностных аргументов.  Мы напрямую
  строим частичные деревья решений и выписываем все ограничения
  на глубину и ошибку.  Такие базы послужат отправной точкой для
  дальнейшей индукции по глубине схемы AC⁰.
-/

import Mathlib.Tactic
import Core.BooleanBasics
import Core.PDTPartial
import Core.SAL_Core
import Core.ShrinkageWitness
import ThirdPartyFacts.Facts_Switching

namespace Pnp3
namespace ThirdPartyFacts
namespace ConstructiveSwitching

open Core

/-!
### Базовые конструкции

* `fullSubcube` — самый простой подкуб, в котором все переменные свободны.
  Его удобно использовать в листьях тривиальных PDT: такой лист покрывает
  абсолютно все входы, что позволяет мгновенно построить сертификат для
  константной функции `true`.
-/
/-- Полный подкуб: ни одна переменная не фиксирована. -/
@[simp] def fullSubcube (n : Nat) : Subcube n := fun _ => none

/-!
### Пустое семейство функций

Для пустого семейства `F = []` частичный сертификат можно построить
моментально.  Стволом служит дерево из одного листа, все хвосты нулевые,
ошибка равна нулю, и условий на `selectors` нет (они никогда не используются).
-/
/--
  Частичный сертификат для пустого семейства функций.  Мы явно указываем:
  * глубину ствола (`0`),
  * пустой словарь листьев (в силу отсутствия функций),
  * нулевую ошибку.
-/
theorem partial_shrinkage_empty_family {n : Nat} :
    let F : Family n := []
    ∃ (ℓ : Nat) (C : PartialCertificate n ℓ F),
      ℓ = 0 ∧ C.depthBound = 0 ∧ C.epsilon = 0 := by
  intro F
  classical
  -- В качестве подкуба берём полный куб: он не фиксирует ни одну переменную.
  let β : Subcube n := fullSubcube n
  -- Ствол частичного PDT: одно-единственное ветвление, равное листу β.
  let tree : PDT n := PDT.leaf β
  -- Частичное дерево с нулевыми хвостами строится через `PartialDT.ofPDT`.
  refine ⟨0, {
    witness := PartialDT.ofPDT tree
    depthBound := 0
    epsilon := 0
    trunk_depth_le := by
      -- Глубина листа равна нулю, поэтому оценка очевидна.
      simpa [tree, PartialDT.ofPDT, PDT.depth]
    selectors := fun _ => []
    selectors_sub := by
      intro f β' hf hβ'
      -- Противоречие: в пустом семействе нет функций.
      simpa [F] using hf
    err_le := by
      intro f hf
      -- Ошибка аппроксимации вакуозна: таких функций не существует.
      simpa [F] using hf
  }, rfl, rfl, rfl⟩

/--
  Версия конструктивного сертификата, согласованная с интерфейсом
  `partial_shrinkage_for_AC0`.  Для пустого семейства мы получаем
  параметры `ℓ = 0`, `depthBound = 0`, `epsilon = 0`, после чего
  проверяем требуемые неравенства на логарифмах и рационалях.
-/
theorem partial_shrinkage_for_AC0_empty
    (params : AC0Parameters) :
    let F : Family params.n := []
    ∃ (ℓ : Nat) (C : PartialCertificate params.n ℓ F),
      ℓ ≤ Nat.log2 (params.M + 2) ∧
      C.depthBound + ℓ ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) ∧
      (0 : Q) ≤ C.epsilon ∧
      C.epsilon ≤ (1 : Q) / (params.n + 2) := by
  intro F
  classical
  -- Используем только что построенный сертификат.
  obtain ⟨ℓ, C, hℓ, hdepth, hε⟩ := partial_shrinkage_empty_family (n := params.n)
  -- Подставляем и проверяем ограничения на параметры.
  refine ⟨ℓ, C, ?_, ?_, ?_, ?_⟩
  · -- Ограничение на `ℓ` тривиально: обе стороны равны нулю.
    simpa [F, hℓ]
  · -- Суммарная глубина также равна нулю, что удовлетворяет любой верхней границе.
    simpa [F, hℓ, hdepth]
  · -- Ошибка неотрицательна.
    simpa [F, hε]
  · -- Ошибка не превосходит 1/(n+2).
    have hpos : (0 : Q) ≤ (params.n + 2 : Q) := by
      exact_mod_cast (Nat.zero_le (params.n + 2))
    have hnum : (0 : Q) ≤ (1 : Q) := by
      norm_num
    have hdiv := div_nonneg hnum hpos
    simpa [F, hε] using hdiv

/-!
### Семейство из одной константной функции

Следующий шаг — явный сертификат для семейства `F = [fun _ ↦ c]`.  Здесь
уже нужно учитывать значение `c`:
* если `c = false`, достаточно пустого списка листьев;
* если `c = true`, используем полный подкуб `β`, который покрывает все входы.
В обоих случаях ошибку удаётся обнулить.
-/
/--
  Частичный сертификат для константной функции.  Мы вновь используем полный
  подкуб `β` и выбираем селекторы в зависимости от значения `c`.
-/
theorem partial_shrinkage_constant {n : Nat} (c : Bool) :
    let f : BitVec n → Bool := fun _ => c
    let F : Family n := [f]
    ∃ (ℓ : Nat) (C : PartialCertificate n ℓ F),
      ℓ = 0 ∧ C.depthBound = 0 ∧ C.epsilon = 0 := by
  intro f F
  classical
  -- Полный подкуб β и дерево из одного листа — как и в предыдущем случае.
  let β : Subcube n := fullSubcube n
  let tree : PDT n := PDT.leaf β
  -- Приступаем к построению сертификата.
  refine ⟨0, {
    witness := PartialDT.ofPDT tree
    depthBound := 0
    epsilon := 0
    trunk_depth_le := by
      simpa [tree, PartialDT.ofPDT, PDT.depth]
    selectors := fun g => if g = f then (if c then [β] else []) else []
    selectors_sub := by
      intro g γ hg hγ
      -- Из `hg` следует, что g = f.
      have hg' : g = f := by
        simpa [F] using hg
      subst hg'
      -- Разбираем два случая: c = true и c = false.
      by_cases hc : c
      · -- Когда c = true, селекторы содержат единственный подкуб β.
        simp [F, hc] at hγ
        rcases hγ with hγ | hγ
        · -- Лист совпадает с β, а он очевидно принадлежит дереву.
          subst hγ
          simp [tree, PartialDT.ofPDT, PartialDT.realize]
        · cases hγ
      · -- Когда c = false, селекторы пусты, противоречий не возникает.
        simpa [F, hc] using hγ
    err_le := by
      intro g hg
      -- Как и раньше, g обязан совпадать с f.
      have hg' : g = f := by
        simpa [F] using hg
      subst hg'
      -- Два случая по значению c.
      by_cases hc : c
      · -- Селекторы состоят из полного подкуба β, поэтому покрытие равно true.
        have hcover : ∀ x : BitVec n, coveredB [β] x = true := by
          intro x
          -- Для полного подкуба принадлежность выполнена для любого x.
          have hmem : mem β x := by
            simp [β, fullSubcube]
          -- Переводим Prop в Bool.
          have hmemB : memB β x = true := by
            simpa [mem] using hmem
          -- Для списка из одного элемента coveredB совпадает с memB.
          have hcons := coveredB_cons (β := β) (R := ([] : List (Subcube n))) (x := x)
          have hnil := coveredB_nil (x := x)
          simpa [hcons, hnil] using hmemB
        -- Ошибка равна нулю, так как f совпадает с покрытием β.
        have hzero : errU f [β] = 0 :=
          errU_eq_zero_of_agree (n := n) (f := f) (Rset := [β]) (h := by
            intro x
            have hf : f x = true := by
              simp [f, hc]
            have hcov : coveredB [β] x = true := hcover x
            -- Преобразуем равенство Bool → Bool через «if».
            simpa [hf, hcov]
          )
        simpa [F, hc, hzero]
      · -- Селекторы пусты, поэтому покрытие всегда false.
        have hzero : errU f [] = 0 := by
          -- Функция f в этом случае постоянно false.
          have hf : f = fun _ : BitVec n => false := by
            funext x; simp [f, hc]
          -- Подставляем и используем готовую лемму.
          simpa [hf]
        simpa [F, hc, hzero]
  }, rfl, rfl, rfl⟩

/--
  Константная функция удовлетворяет ограничениям аксиомы AC⁰.  Это даёт
  полностью конструктивную версию shrinkage без обращения к аксиоме.
-/
theorem partial_shrinkage_for_AC0_constant
    (params : AC0Parameters) (c : Bool) :
    let f : BitVec params.n → Bool := fun _ => c
    let F : Family params.n := [f]
    ∃ (ℓ : Nat) (C : PartialCertificate params.n ℓ F),
      ℓ ≤ Nat.log2 (params.M + 2) ∧
      C.depthBound + ℓ ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) ∧
      (0 : Q) ≤ C.epsilon ∧
      C.epsilon ≤ (1 : Q) / (params.n + 2) := by
  intro f F
  classical
  -- Применяем построение из предыдущей леммы.
  obtain ⟨ℓ, C, hℓ, hdepth, hε⟩ := partial_shrinkage_constant (n := params.n) (c := c)
  refine ⟨ℓ, C, ?_, ?_, ?_, ?_⟩
  · -- Ограничение на ℓ.
    simpa [F, hℓ]
  · -- Верхняя граница на суммарную глубину.
    simpa [F, hℓ, hdepth]
  · -- Ошибка неотрицательна.
    simpa [F, hε]
  · -- Ошибка ≤ 1/(n+2).
    have hpos : (0 : Q) ≤ (params.n + 2 : Q) := by
      exact_mod_cast (Nat.zero_le (params.n + 2))
    have hnum : (0 : Q) ≤ (1 : Q) := by
      norm_num
    have hdiv := div_nonneg hnum hpos
    simpa [F, hε] using hdiv

end ConstructiveSwitching
end ThirdPartyFacts
end Pnp3
