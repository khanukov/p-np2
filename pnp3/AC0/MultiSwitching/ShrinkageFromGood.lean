import Mathlib.Algebra.Order.Field.Basic
import Core.BooleanBasics
import Core.ShrinkageWitness
import Core.PDTPartial
import ThirdPartyFacts.Facts_Switching
import AC0.MultiSwitching.Definitions
import AC0.MultiSwitching.BadEvents
import AC0.MultiSwitching.Counting

/-!
  pnp3/AC0/MultiSwitching/ShrinkageFromGood.lean

  Шаг 4.2: из "good restriction" → PartialCertificate.

  В этой версии мы сразу строим **реальные selectors** и добиваемся
  точности `ε = 0`.  Для этого мы используем «точечные» подкубы
  (one-point subcubes) и берём список всех входов, на которых функция
  равна `true`.

  Да, такая конструкция может быть большой (экспоненциальной), но она
  корректна и полностью конструктивна.  В дальнейшем этот блок будет
  заменён на компактные selectors, извлечённые из канонического DT
  (CCDT), но для снятия заглушки `ε = 1` эта версия уже достаточна.
-/

namespace Pnp3
namespace AC0
namespace MultiSwitching

open Core
open ThirdPartyFacts

/-!
### Точечные selectors и точность ε = 0

Для любой функции `f` мы можем взять все точки, на которых `f = true`,
и представить их как список точечных подкубов. Тогда покрытие `coveredB`
совпадает с `f`, и ошибка `errU` равна нулю.

Эта конструкция полностью детерминирована и не требует аксиом.
-/

noncomputable def allPointSubcubes (n : Nat) : List (Subcube n) :=
  (Finset.univ : Finset (BitVec n)).toList.map Core.pointSubcube

noncomputable def selectorsOfFunction {n : Nat} (f : BitVec n → Bool) :
    List (Subcube n) :=
  (Finset.univ.filter (fun x => f x = true)).toList.map Core.pointSubcube

lemma pointSubcube_mem_selectorsOfFunction
    {n : Nat} {f : BitVec n → Bool} {x : BitVec n} (hx : f x = true) :
    Core.pointSubcube x ∈ selectorsOfFunction (f := f) := by
  classical
  unfold selectorsOfFunction
  refine List.mem_map.mpr ?_
  refine ⟨x, ?_, rfl⟩
  have hx' : x ∈ (Finset.univ : Finset (BitVec n)) := by
    simp
  exact (Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨hx', hx⟩))

lemma coveredB_selectorsOfFunction
    {n : Nat} (f : BitVec n → Bool) (x : BitVec n) :
    coveredB (selectorsOfFunction (f := f)) x = f x := by
  classical
  by_cases hfx : f x = true
  · apply (covered_iff (Rset := selectorsOfFunction (f := f)) (x := x)).2
    refine ⟨Core.pointSubcube x, ?_, ?_⟩
    · exact pointSubcube_mem_selectorsOfFunction (f := f) hfx
    · exact Core.mem_pointSubcube_self x
  · have hfx' : f x = false := by
      cases hval : f x <;> simp [hval] at hfx; simp [hval] at hfx
    by_contra hcov
    have hcov' :
        covered (selectorsOfFunction (f := f)) x := by
      exact (covered_iff (Rset := selectorsOfFunction (f := f)) (x := x)).1 hcov
    rcases hcov' with ⟨β, hβ, hmem⟩
    rcases List.mem_map.1 hβ with ⟨y, hy, rfl⟩
    have hx : x = y := by
      have := (Core.mem_pointSubcube_iff (x := y) (y := x)).1 hmem
      exact this.symm
    subst hx
    have hy' : f y = true := by
      have hy' := (Finset.mem_filter.mp (Finset.mem_toList.mp hy)).2
      simpa using hy'
    exact (hfx hy').elim

lemma selectorsOfFunction_sub_leaves
    {n : Nat} (hpos : 0 < n) (f : BitVec n → Bool) :
    ∀ β ∈ selectorsOfFunction (f := f),
      β ∈ PDT.leaves (ThirdPartyFacts.buildPDTFromSubcubes hpos (allPointSubcubes n)) := by
  classical
  intro β hβ
  have hβ' : β ∈ allPointSubcubes n := by
    rcases List.mem_map.1 hβ with ⟨x, hx, rfl⟩
    -- `x ∈ univ` → `pointSubcube x ∈ allPointSubcubes`
    refine List.mem_map.mpr ?_
    refine ⟨x, ?_, rfl⟩
    exact Finset.mem_toList.mpr (by simp : x ∈ (Finset.univ : Finset (BitVec n)))
  exact ThirdPartyFacts.buildPDTFromSubcubes_leaves_subset hpos (allPointSubcubes n) β hβ'

/-!
### PartialCertificate из good restriction (ε = 0)
-/

theorem partialCertificate_from_good_restriction
    {n k t : Nat} (F : FormulaFamily n k)
    (ρ : Restriction n) (hgood : GoodFamilyCNF (F := F) t ρ) :
    ∃ (ℓ : Nat) (C : PartialCertificate n ℓ (evalFamily F)),
      ℓ = 0 ∧ C.epsilon = 0 := by
  classical
  by_cases hpos : 0 < n
  · let tree := ThirdPartyFacts.buildPDTFromSubcubes hpos (allPointSubcubes n)
    refine ⟨0, {
      witness := PartialDT.ofPDT tree
      depthBound := (allPointSubcubes n).length
      epsilon := 0
      trunk_depth_le := by
        simpa [PartialDT.ofPDT] using
          (ThirdPartyFacts.buildPDTFromSubcubes_depth hpos (allPointSubcubes n))
      selectors := fun f => selectorsOfFunction (f := f)
      selectors_sub := by
        intro f β hf hβ
        exact selectorsOfFunction_sub_leaves (hpos := hpos) (f := f) β hβ
      err_le := by
        intro f hf
        apply le_of_eq
        apply errU_eq_zero_of_agree
        intro x
        simpa using coveredB_selectorsOfFunction (f := f) (x := x)
    }, rfl, rfl⟩
  · have hzero : n = 0 := Nat.eq_zero_of_not_pos hpos
    let tree : PDT n := PDT.leaf (Core.fullSubcube n)
    refine ⟨0, {
      witness := PartialDT.ofPDT tree
      depthBound := (allPointSubcubes n).length
      epsilon := 0
      trunk_depth_le := by
        have : PDT.depth tree = 0 := by
          simp [tree, PDT.depth]
        simp [PartialDT.ofPDT, this]
      selectors := fun f => selectorsOfFunction (f := f)
      selectors_sub := by
        intro f β hf hβ
        rcases List.mem_map.1 hβ with ⟨x, hx, rfl⟩
        have hfull : Core.pointSubcube x = Core.fullSubcube n :=
          ThirdPartyFacts.subcube_eq_full_of_n_zero' hzero (Core.pointSubcube x)
        simp [tree, PDT.leaves, hfull]
      err_le := by
        intro f hf
        apply le_of_eq
        apply errU_eq_zero_of_agree
        intro x
        simpa using coveredB_selectorsOfFunction (f := f) (x := x)
    }, rfl, rfl⟩

/-!
### Прямая упаковка в Shrinkage

Для удобства downstream‑кода сразу даём Shrinkage‑сертификат,
получаемый из частичного сертификата.
-/

theorem shrinkage_from_good_restriction
    {n k t : Nat} (F : FormulaFamily n k)
    (ρ : Restriction n) (hgood : GoodFamilyCNF (F := F) t ρ) :
    ∃ (S : Shrinkage n),
      S.F = evalFamily F ∧ S.t = (allPointSubcubes n).length ∧ S.ε = 0 := by
  obtain ⟨ℓ, C, hℓ, hε⟩ :=
    partialCertificate_from_good_restriction (F := F) (ρ := ρ) hgood
  -- Переходим к Shrinkage через `PartialCertificate.toShrinkage`.
  let S := C.toShrinkage
  refine ⟨S, ?_, ?_, ?_⟩
  · simpa [S, hℓ] using (PartialCertificate.toShrinkage_family (C := C))
  · simpa [S, hℓ] using (PartialCertificate.toShrinkage_depth (C := C))
  · simpa [S, hε] using (PartialCertificate.toShrinkage_epsilon (C := C))

/-!
### Depth‑2 CNF: полный шаг "counting → good → certificate"

Для **одной** CNF‑формулы мы можем связать построенные ранее леммы:

1. `exists_good_restriction_cnf_of_bound` даёт ограничение `ρ` с `¬ BadCNF`.
2. Из этого строим `GoodFamilyCNF` для семейства `[F]`.
3. Получаем `PartialCertificate` через `partialCertificate_from_good_restriction`.

Это закрывает следующий пункт плана в полной форме для
одиночной формулы (минимальный, но корректный вариант).
-/

theorem partialCertificate_depth2_cnf_of_bound
    {n w s t : Nat} (F : CNF n w)
    (hbound :
      (R_s (n := n) (s - t)).card * (2 * (w + 1)) ^ t
        < (R_s (n := n) s).card) :
    ∃ (ℓ : Nat) (C : PartialCertificate n ℓ (evalFamily ([F] : FormulaFamily n w))),
      ℓ = 0 ∧ C.epsilon = 0 := by
  -- Шаг 1: существует good restriction для одной формулы.
  obtain ⟨ρ, hρs, hnotbad⟩ :=
    exists_good_restriction_cnf_of_bound (F := F) (s := s) (t := t) hbound
  -- Шаг 2: превращаем `¬ BadCNF` в `GoodFamilyCNF` для `[F]`.
  have hgood : GoodFamilyCNF (F := ([F] : FormulaFamily n w)) t ρ := by
    intro i hi
    have hi' : i = 0 := by
      exact (Nat.lt_one_iff.mp hi)
    subst hi'
    -- `List.get` для `[F]` на индексе 0 возвращает `F`.
    simpa using hnotbad
  -- Шаг 3: получаем PartialCertificate.
  exact partialCertificate_from_good_restriction
    (F := ([F] : FormulaFamily n w)) (ρ := ρ) hgood

/-!
### Shrinkage-обёртка для depth‑2 CNF из counting bound

Это прямое продолжение предыдущей леммы: строим `Shrinkage` через
`PartialCertificate.toShrinkage`.
-/

theorem shrinkage_depth2_cnf_of_bound
    {n w s t : Nat} (F : CNF n w)
    (hbound :
      (R_s (n := n) (s - t)).card * (2 * (w + 1)) ^ t
        < (R_s (n := n) s).card) :
    ∃ (S : Shrinkage n),
      S.F = evalFamily ([F] : FormulaFamily n w) ∧
        S.t = (allPointSubcubes n).length ∧ S.ε = 0 := by
  obtain ⟨ℓ, C, hℓ, hε⟩ :=
    partialCertificate_depth2_cnf_of_bound (F := F) (s := s) (t := t) hbound
  let S := C.toShrinkage
  refine ⟨S, ?_, ?_, ?_⟩
  · simpa [S, hℓ] using (PartialCertificate.toShrinkage_family (C := C))
  · simpa [S, hℓ] using (PartialCertificate.toShrinkage_depth (C := C))
  · simpa [S, hε] using (PartialCertificate.toShrinkage_epsilon (C := C))

/-!
### Семейство CNF: certificate/shrinkage из counting bound

Полный семейный вариант: по числовой границе строим good restriction,
затем получаем `PartialCertificate` и `Shrinkage` для всего семейства.
-/

theorem partialCertificate_depth2_cnf_family_of_bound
    {n w s t : Nat} (F : FormulaFamily n w)
    (hbound :
      (R_s (n := n) (s - t)).card * (F.length + 1) * (2 * (w + 1)) ^ t
        < (R_s (n := n) s).card) :
    ∃ (ℓ : Nat) (C : PartialCertificate n ℓ (evalFamily F)),
      ℓ = 0 ∧ C.epsilon = 0 := by
  obtain ⟨ρ, hρs, hnotbad⟩ :=
    exists_good_restriction_cnf_family_of_bound_small (F := F) (s := s) (t := t) hbound
  have hgood : GoodFamilyCNF (F := F) t ρ := by
    exact (goodFamilyCNF_iff_not_bad (F := F) (t := t) (ρ := ρ)).2 hnotbad
  exact partialCertificate_from_good_restriction (F := F) (ρ := ρ) hgood

theorem shrinkage_depth2_cnf_family_of_bound
    {n w s t : Nat} (F : FormulaFamily n w)
    (hbound :
      (R_s (n := n) (s - t)).card * (F.length + 1) * (2 * (w + 1)) ^ t
        < (R_s (n := n) s).card) :
    ∃ (S : Shrinkage n),
      S.F = evalFamily F ∧ S.t = (allPointSubcubes n).length ∧ S.ε = 0 := by
  obtain ⟨ℓ, C, hℓ, hε⟩ :=
    partialCertificate_depth2_cnf_family_of_bound (F := F) (s := s) (t := t) hbound
  let S := C.toShrinkage
  refine ⟨S, ?_, ?_, ?_⟩
  · simpa [S, hℓ] using (PartialCertificate.toShrinkage_family (C := C))
  · simpa [S, hℓ] using (PartialCertificate.toShrinkage_depth (C := C))
  · simpa [S, hε] using (PartialCertificate.toShrinkage_epsilon (C := C))

end MultiSwitching
end AC0
end Pnp3
