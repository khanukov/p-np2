import Mathlib.Algebra.Order.Field.Basic
import Core.BooleanBasics
import Core.ShrinkageWitness
import Core.PDTPartial
import ThirdPartyFacts.Facts_Switching
import AC0.MultiSwitching.Definitions
import AC0.MultiSwitching.BadEvents
import AC0.MultiSwitching.Counting
import AC0.MultiSwitching.Encoding
import AC0.MultiSwitching.TraceBridge
import AC0.MultiSwitching.Decides
import AC0.MultiSwitching.CommonCCDT
import AC0.MultiSwitching.DecidesAtoms
import AC0.MultiSwitching.CommonCCDT_Func

/-!
  pnp3/AC0/MultiSwitching/ShrinkageFromGood.lean

  Шаг 4.2: из "good restriction" → PartialCertificate.

  В этой версии мы сразу строим **реальные selectors** и добиваемся
  точности `ε = 1/(n+2)` (а фактически `errU = 0`). Для этого мы используем
  «точечные» подкубы
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
### Точечные selectors и точность ε = 1/(n+2)

Для любой функции `f` мы можем взять все точки, на которых `f = true`,
и представить их как список точечных подкубов. Тогда покрытие `coveredB`
совпадает с `f`, и ошибка `errU` равна нулю.

Эта конструкция полностью детерминирована и не требует аксиом. Поскольку
ошибка `errU` равна нулю, мы можем ослабить оценку до `1/(n+2)` — это
совместимо с числовой частью Stage‑3/Stage‑4.
-/

noncomputable def allPointSubcubes (n : Nat) : List (Subcube n) :=
  (Finset.univ : Finset (Core.BitVec n)).toList.map Core.pointSubcube

noncomputable def selectorsOfFunction {n : Nat} (f : Core.BitVec n → Bool) :
    List (Subcube n) :=
  (Finset.univ.filter (fun x => f x = true)).toList.map Core.pointSubcube

lemma pointSubcube_mem_selectorsOfFunction
    {n : Nat} {f : Core.BitVec n → Bool} {x : Core.BitVec n} (hx : f x = true) :
    Core.pointSubcube x ∈ selectorsOfFunction (f := f) := by
  classical
  unfold selectorsOfFunction
  refine List.mem_map.mpr ?_
  refine ⟨x, ?_, rfl⟩
  have hx' : x ∈ (Finset.univ : Finset (Core.BitVec n)) := by
    simp
  exact (Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨hx', hx⟩))

lemma mem_selectorsOfFunction_iff
    {n : Nat} {f : Core.BitVec n → Bool} {β : Subcube n} :
    β ∈ selectorsOfFunction (f := f) ↔
      ∃ x, f x = true ∧ β = Core.pointSubcube x := by
  classical
  constructor
  · intro hβ
    unfold selectorsOfFunction at hβ
    rcases List.mem_map.1 hβ with ⟨x, hx, rfl⟩
    have hx' := (Finset.mem_filter.mp (Finset.mem_toList.mp hx)).2
    exact ⟨x, hx', rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact pointSubcube_mem_selectorsOfFunction (f := f) hx

lemma coveredB_selectorsOfFunction
    {n : Nat} (f : Core.BitVec n → Bool) (x : Core.BitVec n) :
    coveredB (selectorsOfFunction (f := f)) x = f x := by
  classical
  by_cases hfx : f x = true
  · have hcov : covered (selectorsOfFunction (f := f)) x := by
      refine ⟨Core.pointSubcube x, ?_, ?_⟩
      · exact pointSubcube_mem_selectorsOfFunction (f := f) hfx
      · exact Core.mem_pointSubcube_self x
    have hcovB :
        coveredB (selectorsOfFunction (f := f)) x = true :=
      (covered_iff (Rset := selectorsOfFunction (f := f)) (x := x)).1 hcov
    simpa [hfx] using hcovB
  · have hfx' : f x = false := by
      cases hval : f x with
      | true =>
          exact (False.elim (hfx hval))
      | false =>
          simp
    by_cases hcovB : coveredB (selectorsOfFunction (f := f)) x = true
    · have hcov :
          covered (selectorsOfFunction (f := f)) x :=
        (covered_iff (Rset := selectorsOfFunction (f := f)) (x := x)).2 hcovB
      rcases hcov with ⟨β, hβ, hmem⟩
      rcases (mem_selectorsOfFunction_iff (f := f) (β := β)).1 hβ with ⟨y, hy, hβeq⟩
      subst hβeq
      have hx : x = y := by
        have := (Core.mem_pointSubcube_iff (x := y) (y := x)).1 hmem
        exact this.symm
      subst hx
      have : False := by
        have hfalse : false = true := hfx'.symm.trans hy
        exact Bool.false_ne_true hfalse
      exact this.elim
    · have hcovB' : coveredB (selectorsOfFunction (f := f)) x = false := by
        cases hval : coveredB (selectorsOfFunction (f := f)) x with
        | true =>
            exact (False.elim (hcovB hval))
        | false =>
            simp
      simpa [hfx'] using hcovB'

lemma selectorsOfFunction_sub_leaves
    {n : Nat} (hpos : 0 < n) (f : Core.BitVec n → Bool) :
    ∀ β ∈ selectorsOfFunction (f := f),
      β ∈ PDT.leaves (ThirdPartyFacts.buildPDTFromSubcubes hpos (allPointSubcubes n)) := by
  classical
  intro β hβ
  have hβ' : β ∈ allPointSubcubes n := by
    rcases List.mem_map.1 hβ with ⟨x, hx, rfl⟩
    -- `x ∈ univ` → `pointSubcube x ∈ allPointSubcubes`
    refine List.mem_map.mpr ?_
    refine ⟨x, ?_, rfl⟩
    exact Finset.mem_toList.mpr (by simp : x ∈ (Finset.univ : Finset (Core.BitVec n)))
  exact ThirdPartyFacts.buildPDTFromSubcubes_leaves_subset hpos (allPointSubcubes n) β hβ'

/-!
### PartialCertificate из restriction (ε = 1/(n+2))

Важно: для точечных selectors условие "good restriction" **не нужно**.
Мы строим сертификат напрямую из таблицы истинности, поэтому корректность
не зависит от свойств `ρ`. Это делает Stage 4 полностью замкнутым: как только
существует *какая-то* рестрикция (например, полученная на Stage 3),
мы уже можем произвести `PartialCertificate` и `Shrinkage`.
-/

theorem partialCertificate_from_restriction_trivial
    {n k : Nat} (F : FormulaFamily n k)
    (ρ : Restriction n) :
    ∃ (ℓ : Nat) (C : PartialCertificate n ℓ (evalFamily F)),
      ℓ = 0 ∧ C.depthBound = (allPointSubcubes n).length ∧
        C.epsilon = (1 : Q) / (n + 2) := by
  classical
  -- Важно: конструкция точечных selectors **не зависит** от restriction `ρ`.
  -- Явно отмечаем это, чтобы избежать предупреждений о неиспользуемой переменной.
  have _ := ρ
  by_cases hpos : 0 < n
  · let tree := ThirdPartyFacts.buildPDTFromSubcubes hpos (allPointSubcubes n)
    have hε : (0 : Q) ≤ (1 : Q) / (n + 2) := by
      have hnonneg : (0 : Q) ≤ (n + 2) := by
        exact_mod_cast (Nat.zero_le (n + 2))
      exact div_nonneg (show (0 : Q) ≤ (1 : Q) by exact zero_le_one) hnonneg
    refine ⟨0, {
      witness := PartialDT.ofPDT tree
      depthBound := (allPointSubcubes n).length
      epsilon := (1 : Q) / (n + 2)
      trunk_depth_le := by
        simpa [PartialDT.ofPDT] using
          (ThirdPartyFacts.buildPDTFromSubcubes_depth hpos (allPointSubcubes n))
      selectors := fun f => selectorsOfFunction (f := f)
      selectors_sub := by
        intro f β hf hβ
        have hleaf :
            β ∈ PDT.leaves
              (ThirdPartyFacts.buildPDTFromSubcubes hpos (allPointSubcubes n)) :=
          selectorsOfFunction_sub_leaves (hpos := hpos) (f := f) β hβ
        simpa [PartialDT.realize_ofPDT] using hleaf
      err_le := by
        intro f hf
        have herr : errU f (selectorsOfFunction (f := f)) = 0 := by
          apply errU_eq_zero_of_agree
          intro x
          simpa [eq_comm] using coveredB_selectorsOfFunction (f := f) (x := x)
        -- Ошибка 0 ≤ 1/(n+2).
        simpa [herr] using hε
    }, rfl, rfl, rfl⟩
  · have hzero : n = 0 := Nat.eq_zero_of_not_pos hpos
    let tree : PDT n := PDT.leaf (fullSubcube n)
    have hε : (0 : Q) ≤ (1 : Q) / (n + 2) := by
      have hnonneg : (0 : Q) ≤ (n + 2) := by
        exact_mod_cast (Nat.zero_le (n + 2))
      exact div_nonneg (show (0 : Q) ≤ (1 : Q) by exact zero_le_one) hnonneg
    refine ⟨0, {
      witness := PartialDT.ofPDT tree
      depthBound := (allPointSubcubes n).length
      epsilon := (1 : Q) / (n + 2)
      trunk_depth_le := by
        have : PDT.depth tree = 0 := by
          simp [tree, PDT.depth]
        simp [PartialDT.ofPDT, this]
      selectors := fun f => selectorsOfFunction (f := f)
      selectors_sub := by
        intro f β hf hβ
        rcases List.mem_map.1 hβ with ⟨x, hx, rfl⟩
        have hfull : Core.pointSubcube x = fullSubcube n :=
          ThirdPartyFacts.subcube_eq_full_of_n_zero' hzero (Core.pointSubcube x)
        simp [PartialDT.realize_ofPDT, tree, PDT.leaves, hfull]
      err_le := by
        intro f hf
        have herr : errU f (selectorsOfFunction (f := f)) = 0 := by
          apply errU_eq_zero_of_agree
          intro x
          simpa [eq_comm] using coveredB_selectorsOfFunction (f := f) (x := x)
        simpa [herr] using hε
    }, rfl, rfl, rfl⟩

theorem partialCertificate_from_restriction
    {n k : Nat} (F : FormulaFamily n k)
    (ρ : Restriction n) :
    ∃ (ℓ : Nat) (C : PartialCertificate n ℓ (evalFamily F)),
      ℓ = 0 ∧ C.depthBound = (allPointSubcubes n).length ∧
        C.epsilon = (1 : Q) / (n + 2) := by
  simpa using (partialCertificate_from_restriction_trivial (F := F) (ρ := ρ))

/-!
### PartialCertificate из good restriction (ε = 1/(n+2))

Это тонкая обёртка над `partialCertificate_from_restriction`,
оставляемая для логической читабельности Stage 4.
-/

theorem depth_lt_of_good_canonicalCCDT
    {n w t : Nat} (F : FormulaFamily n w) (ρ : Restriction n)
    (hgood : GoodFamilyCNF (F := F) t ρ) (ht : 0 < t) :
    PDT.depth ((canonicalCCDTAlgorithmCNF (F := F) t).ccdt ρ) < t := by
  have hnotbad : ¬ BadFamily (F := F) t ρ := by
    exact (goodFamilyCNF_iff_not_bad (F := F) (t := t) (ρ := ρ)).1 hgood
  have hnotbad_det : ¬ BadFamily_deterministic (F := F) t ρ := by
    intro hbad_det
    exact hnotbad (badFamily_deterministic_implies_badFamily
      (F := F) (t := t) (ρ := ρ) hbad_det)
  have hnot_bad_event :
      ¬ BadEvent (A := canonicalCCDTAlgorithmCNF (F := F) t) ρ := by
    intro hbad_event
    have hbad_det :
        BadFamily_deterministic (F := F) t ρ := by
      exact (badEvent_canonicalCCDT_iff_badFamilyDet
        (F := F) (ρ := ρ) ht).1 hbad_event
    exact hnotbad_det hbad_det
  have hnot_ge :
      ¬ t ≤ PDT.depth ((canonicalCCDTAlgorithmCNF (F := F) t).ccdt ρ) := by
    simpa [BadEvent] using hnot_bad_event
  exact lt_of_not_ge hnot_ge

/-!
### Stage‑4 (common CCDT): certificate for restricted family

Мы строим `PartialCertificate` для семейства, ограниченного рестрикцией `ρ`:
`f ↦ restrictFun ρ f`. Это согласует глобальную ошибку `errU` с тем,
что листья CCDT покрывают только подкуб `ρ`.
-/

noncomputable def defaultBitVec (n : Nat) : Core.BitVec n := fun _ => false

noncomputable def leafValue {n : Nat} (β : Subcube n) (f : Core.BitVec n → Bool) : Bool :=
  f ((⟨β⟩ : Restriction n).override (defaultBitVec n))

noncomputable def selectorsFromLeaves {n : Nat} (t : PDT n)
    (f : Core.BitVec n → Bool) : List (Subcube n) :=
  (PDT.leaves t).filter (fun β => leafValue (β := β) f = true)

lemma selectorsFromLeaves_sub {n : Nat} {t : PDT n} {f : Core.BitVec n → Bool}
    {β : Subcube n} :
  β ∈ selectorsFromLeaves (t := t) (f := f) → β ∈ PDT.leaves t := by
  intro hβ
  exact (List.mem_filter.mp hβ).1

lemma leafValue_eq_of_mem
    {n : Nat} {β : Subcube n} {f : Core.BitVec n → Bool} {x : Core.BitVec n}
    (hconst : (⟨β⟩ : Restriction n).isConstantOn f = true)
    (hmem : mem β x) :
    f x = leafValue (β := β) f := by
  classical
  have hconst' :=
    (Restriction.isConstantOn_iff (ρ := (⟨β⟩ : Restriction n)) (f := f)).1 hconst
  -- используем константность на `override`.
  have h := hconst' x (defaultBitVec n)
  -- `override` не меняет `x`, если `x` лежит в β.
  have hover : (⟨β⟩ : Restriction n).override x = x := by
    exact (Restriction.override_eq_of_mem (ρ := (⟨β⟩ : Restriction n)) (x := x) hmem)
  -- `override` по умолчанию определяет leafValue
  simpa [leafValue, defaultBitVec, hover] using h

lemma compatible_of_refines
    {n : Nat} {β : Subcube n} {ρ : Restriction n} {x : Core.BitVec n}
    (href : subcubeRefines β ρ.mask) (hmem : mem β x) :
    ρ.compatible x = true := by
  -- Достаточно показать `mem ρ.mask x`.
  apply (Restriction.compatible_iff (ρ := ρ) (x := x)).2
  apply (mem_iff (β := ρ.mask) (x := x)).2
  intro i b hmask
  have hβ : β i = some b := by
    -- из `subcubeRefines` получаем согласование с `ρ.mask`.
    simpa [subcubeRefines, hmask] using (href i)
  have hmem' := (mem_iff (β := β) (x := x)).1 hmem i b hβ
  exact hmem'

lemma coveredB_false_of_not_compatible
    {n : Nat} {t : PDT n} {ρ : Restriction n} {x : Core.BitVec n}
    {f : Core.BitVec n → Bool}
    (href_leaves :
      ∀ β ∈ PDT.leaves t, subcubeRefines β ρ.mask)
    (hnot : ρ.compatible x ≠ true) :
    coveredB (selectorsFromLeaves (t := t) (f := restrictFun ρ f)) x = false := by
  classical
  -- Если `coveredB` было бы `true`, то нашёлся бы β с mem β x,
  -- что дало бы совместимость с `ρ`.
  by_cases hcov : coveredB (selectorsFromLeaves (t := t)
      (f := restrictFun ρ f)) x = true
  · have hcover :
        covered (selectorsFromLeaves (t := t)
          (f := restrictFun ρ f)) x :=
      (covered_iff (Rset := selectorsFromLeaves (t := t)
        (f := restrictFun ρ f)) (x := x)).2 hcov
    rcases hcover with ⟨β, hβ, hmem⟩
    have hβleaf : β ∈ PDT.leaves t := selectorsFromLeaves_sub (t := t) (f := _) hβ
    have hcomp := compatible_of_refines (href := href_leaves β hβleaf) (hmem := hmem)
    exact (hnot hcomp).elim
  · simpa [hcov] using hcov

theorem partialCertificate_from_depth_lt_common
    {n w t : Nat} (F : FormulaFamily n w)
    (ρ : Restriction n)
    (hdepth : PDT.depth (commonCCDT_CNF_aux (F := F) t ρ) < t) :
    ∃ (ℓ : Nat) (C : PartialCertificate n ℓ (evalFamilyRestrict (ρ := ρ) F)),
      ℓ = 0 ∧ C.depthBound = t ∧
        C.epsilon = (1 : Q) / (n + 2) := by
  classical
  let tree := commonCCDT_CNF_aux (F := F) t ρ
  have hε : (0 : Q) ≤ (1 : Q) / (n + 2) := by
    have hnonneg : (0 : Q) ≤ (n + 2) := by
      exact_mod_cast (Nat.zero_le (n + 2))
    exact div_nonneg (show (0 : Q) ≤ (1 : Q) by exact zero_le_one) hnonneg
  refine ⟨0, ?_⟩
  refine ⟨{
    witness := PartialDT.ofPDT tree
    depthBound := t
    epsilon := (1 : Q) / (n + 2)
    trunk_depth_le := by
      exact Nat.le_of_lt hdepth
    selectors := fun f => selectorsFromLeaves (t := tree) (f := f)
    selectors_sub := by
      intro f β hf hβ
      have hleaf : β ∈ PDT.leaves tree :=
        selectorsFromLeaves_sub (t := tree) (f := f) hβ
      simpa [PartialDT.realize_ofPDT] using hleaf
    err_le := by
      intro f hf
      -- Раскладываем `f` как `restrictFun ρ g`.
      rcases (mem_evalFamilyRestrict_iff (ρ := ρ) (F := F)).1 hf with ⟨g, hg, rfl⟩
      -- Покажем, что `coveredB` совпадает с `restrictFun`.
      have hcov :
          ∀ x,
            restrictFun ρ g x =
              coveredB (selectorsFromLeaves (t := tree) (f := restrictFun ρ g)) x := by
        intro x
        -- Получаем `g = evalCNF G` для некоторого `G`.
        rcases (mem_evalFamily_iff (F := F) (f := g)).1 hg with ⟨G, hG, rfl⟩
        -- Константность `evalCNF G` на каждом листе.
        have hconstLeaf :
            ∀ β ∈ PDT.leaves tree,
              (⟨β⟩ : Restriction n).isConstantOn (evalCNF (n := n) (k := w) G) = true := by
          intro β hβ
          have hdec := leaf_decidesFamily_of_depth_lt
            (F := F) (t := t) (ρ := ρ) (β := β) hβ hdepth
          rcases (List.mem_iff_get.1 hG) with ⟨i, hi⟩
          cases hi
          exact hdec i
        -- leafValue для restrictFun совпадает с leafValue для evalCNF на листьях.
        have hleafVal_eq :
            ∀ β ∈ PDT.leaves tree,
              leafValue (β := β) (restrictFun ρ (evalCNF (n := n) (k := w) G)) =
                leafValue (β := β) (evalCNF (n := n) (k := w) G) := by
          intro β hβ
          have href :=
            commonCCDT_leaves_refine_root (F := F) (t := t) (ρ := ρ) (β := β) hβ
          have hy_mem :
              mem β ((⟨β⟩ : Restriction n).override (defaultBitVec n)) := by
            simpa using (Restriction.override_mem (ρ := (⟨β⟩ : Restriction n))
              (x := defaultBitVec n))
          have hy_comp := compatible_of_refines (href := href) (hmem := hy_mem)
          unfold leafValue
          unfold restrictFun
          rw [hy_comp]
          simp
        by_cases hcomp : ρ.compatible x = true
        · obtain ⟨β, hβleaf, hmem⟩ :=
            commonCCDT_leaf_of_compatible (F := F) (t := t) (ρ := ρ) (x := x) hcomp
          have hconst := hconstLeaf β hβleaf
          have hval :=
            leafValue_eq_of_mem (β := β) (f := evalCNF (n := n) (k := w) G)
              (hconst := hconst) (hmem := hmem)
          have hfx :
              restrictFun ρ (evalCNF (n := n) (k := w) G) x =
                evalCNF (n := n) (k := w) G x := by
            unfold restrictFun
            rw [hcomp]
            simp
          by_cases hx : evalCNF (n := n) (k := w) G x = true
          · have hleafTrue :
                leafValue (β := β)
                  (restrictFun ρ (evalCNF (n := n) (k := w) G)) = true := by
              have : leafValue (β := β) (evalCNF (n := n) (k := w) G) = true := by
                rw [← hval, hx]
              simpa [hleafVal_eq β hβleaf] using this
            have hleafTrue' : decide
                (leafValue (β := β)
                  (restrictFun ρ (evalCNF (n := n) (k := w) G)) = true) = true := by
              simpa using hleafTrue
            have hβsel :
                β ∈ selectorsFromLeaves (t := tree)
                  (f := restrictFun ρ (evalCNF (n := n) (k := w) G)) :=
              List.mem_filter.mpr ⟨hβleaf, hleafTrue'⟩
            have hcov' :
                coveredB (selectorsFromLeaves (t := tree)
                  (f := restrictFun ρ (evalCNF (n := n) (k := w) G))) x = true := by
              apply (covered_iff (Rset := selectorsFromLeaves (t := tree)
                (f := restrictFun ρ (evalCNF (n := n) (k := w) G))) (x := x)).1
              exact ⟨β, hβsel, hmem⟩
            have hfxtrue : restrictFun ρ (evalCNF (n := n) (k := w) G) x = true := by
              rw [hfx, hx]
            calc
              restrictFun ρ (evalCNF (n := n) (k := w) G) x = true := hfxtrue
              _ = coveredB (selectorsFromLeaves (t := tree)
                    (f := restrictFun ρ (evalCNF (n := n) (k := w) G))) x := by
                symm
                exact hcov'
          · have hfxfalse : restrictFun ρ (evalCNF (n := n) (k := w) G) x = false := by
              unfold restrictFun
              rw [hcomp]
              cases hvalx : evalCNF (n := n) (k := w) G x with
              | true =>
                  exact (hx hvalx).elim
              | false =>
                  rfl
            by_cases hcov' :
                coveredB (selectorsFromLeaves (t := tree)
                  (f := restrictFun ρ (evalCNF (n := n) (k := w) G))) x = true
            · have hcover :
                  covered (selectorsFromLeaves (t := tree)
                    (f := restrictFun ρ (evalCNF (n := n) (k := w) G))) x :=
                (covered_iff (Rset := selectorsFromLeaves (t := tree)
                  (f := restrictFun ρ (evalCNF (n := n) (k := w) G))) (x := x)).2 hcov'
              rcases hcover with ⟨β', hβ', hmem'⟩
              have hβ'leaf : β' ∈ PDT.leaves tree :=
                selectorsFromLeaves_sub (t := tree) (f := _) hβ'
              have hconst' := hconstLeaf β' hβ'leaf
              have hval' :=
                leafValue_eq_of_mem (β := β') (f := evalCNF (n := n) (k := w) G)
                  (hconst := hconst') (hmem := hmem')
              have hleafTrue :
                  leafValue (β := β') (restrictFun ρ (evalCNF (n := n) (k := w) G)) = true := by
                have h := (List.mem_filter.mp hβ').2
                simpa using h
              have hleafTrue' :
                  leafValue (β := β') (evalCNF (n := n) (k := w) G) = true := by
                have : leafValue (β := β')
                    (restrictFun ρ (evalCNF (n := n) (k := w) G)) =
                      leafValue (β := β') (evalCNF (n := n) (k := w) G) :=
                  hleafVal_eq β' hβ'leaf
                simpa [this] using hleafTrue
              have : evalCNF (n := n) (k := w) G x = true := by
                rw [hval']
                exact hleafTrue'
              exact (hx this).elim
            ·
              have hcovfalse :
                  coveredB (selectorsFromLeaves (t := tree)
                    (f := restrictFun ρ (evalCNF (n := n) (k := w) G))) x = false := by
                cases hcase : coveredB (selectorsFromLeaves (t := tree)
                    (f := restrictFun ρ (evalCNF (n := n) (k := w) G))) x with
                | true =>
                    exact (hcov' hcase).elim
                | false =>
                    rfl
              calc
                restrictFun ρ (evalCNF (n := n) (k := w) G) x = false := hfxfalse
                _ = coveredB (selectorsFromLeaves (t := tree)
                      (f := restrictFun ρ (evalCNF (n := n) (k := w) G))) x := by
                  symm
                  exact hcovfalse
        · have hfalse : restrictFun ρ (evalCNF (n := n) (k := w) G) x = false := by
            unfold restrictFun
            cases hcx : ρ.compatible x with
            | true =>
                -- contradiction with incompatible case
                exact (hcomp (by simpa [hcx])).elim
            | false =>
                simp [hcx]
          by_cases hcov' :
              coveredB (selectorsFromLeaves (t := tree)
                (f := restrictFun ρ (evalCNF (n := n) (k := w) G))) x = true
          · have hcover :
                covered (selectorsFromLeaves (t := tree)
                  (f := restrictFun ρ (evalCNF (n := n) (k := w) G))) x :=
              (covered_iff (Rset := selectorsFromLeaves (t := tree)
                (f := restrictFun ρ (evalCNF (n := n) (k := w) G))) (x := x)).2 hcov'
            rcases hcover with ⟨β, hβ, hmem⟩
            have hβleaf : β ∈ PDT.leaves tree :=
              selectorsFromLeaves_sub (t := tree) (f := _) hβ
            have href :=
              commonCCDT_leaves_refine_root (F := F) (t := t) (ρ := ρ) (β := β) hβleaf
            have hcomp' := compatible_of_refines (href := href) (hmem := hmem)
            exact (hcomp hcomp').elim
          ·
            have hcovfalse :
                coveredB (selectorsFromLeaves (t := tree)
                  (f := restrictFun ρ (evalCNF (n := n) (k := w) G))) x = false := by
              cases hcase : coveredB (selectorsFromLeaves (t := tree)
                  (f := restrictFun ρ (evalCNF (n := n) (k := w) G))) x with
              | true =>
                  exact (hcov' hcase).elim
              | false =>
                  rfl
            calc
              restrictFun ρ (evalCNF (n := n) (k := w) G) x = false := hfalse
              _ = coveredB (selectorsFromLeaves (t := tree)
                    (f := restrictFun ρ (evalCNF (n := n) (k := w) G))) x := by
                symm
                exact hcovfalse
      -- Ошибка 0 ≤ 1/(n+2).
      have herr : errU (restrictFun ρ g) (selectorsFromLeaves (t := tree) (f := restrictFun ρ g)) = 0 := by
        apply errU_eq_zero_of_agree
        intro x
        exact hcov x
      simpa [herr] using hε
  }, ?_⟩
  exact ⟨rfl, rfl, rfl⟩

theorem partialCertificate_from_good_restriction_common
    {n w t : Nat} (F : FormulaFamily n w)
    (ρ : Restriction n) (ht : 0 < t)
    (hgood : GoodFamilyCNF_common (F := F) t ρ) :
    ∃ (ℓ : Nat) (C : PartialCertificate n ℓ (evalFamilyRestrict (ρ := ρ) F)),
      ℓ = 0 ∧ C.depthBound = t ∧
        C.epsilon = (1 : Q) / (n + 2) := by
  have hdepth :=
    depth_lt_of_good_commonCCDT (F := F) (t := t) (ρ := ρ) ht hgood
  exact partialCertificate_from_depth_lt_common
    (F := F) (ρ := ρ) (t := t) hdepth

theorem shrinkage_from_good_restriction_common
    {n w t : Nat} (F : FormulaFamily n w)
    (ρ : Restriction n) (ht : 0 < t)
    (hgood : GoodFamilyCNF_common (F := F) t ρ) :
    ∃ (S : Shrinkage n),
      S.F = evalFamilyRestrict (ρ := ρ) F ∧ S.t = t ∧
        S.ε = (1 : Q) / (n + 2) := by
  obtain ⟨ℓ, C, hℓ, hdepth, hε⟩ :=
    partialCertificate_from_good_restriction_common
      (F := F) (ρ := ρ) (t := t) ht hgood
  let S := C.toShrinkage
  refine ⟨S, ?_, ?_, ?_⟩
  · simp [S]
  · simp [S, hdepth, hℓ]
  · simp [S, hε]

/-!
  Atom‑CNF variant: switching on FuncCNF families.
-/

theorem partialCertificate_from_depth_lt_common_atom
    {n t : Nat} (Fs : List (FuncCNF n))
    (ρ : Restriction n)
    (hdepth : PDT.depth (commonCCDT_Family_atom (Fs := Fs) t ρ) < t) :
    ∃ (ℓ : Nat) (C : PartialCertificate n ℓ (evalFamilyRestrictFuncCNF (ρ := ρ) (Fs := Fs))),
      ℓ = 0 ∧ C.depthBound = t ∧
        C.epsilon = (1 : Q) / (n + 2) := by
  classical
  let tree := commonCCDT_Family_atom (Fs := Fs) t ρ
  have hε : (0 : Q) ≤ (1 : Q) / (n + 2) := by
    have hnonneg : (0 : Q) ≤ (n + 2) := by
      exact_mod_cast (Nat.zero_le (n + 2))
    exact div_nonneg (show (0 : Q) ≤ (1 : Q) by exact zero_le_one) hnonneg
  refine ⟨0, ?_⟩
  refine ⟨{
    witness := PartialDT.ofPDT tree
    depthBound := t
    epsilon := (1 : Q) / (n + 2)
    trunk_depth_le := by
      exact Nat.le_of_lt hdepth
    selectors := fun f => selectorsFromLeaves (t := tree) (f := f)
    selectors_sub := by
      intro f β hf hβ
      have hleaf : β ∈ PDT.leaves tree :=
        selectorsFromLeaves_sub (t := tree) (f := f) hβ
      simpa [PartialDT.realize_ofPDT] using hleaf
    err_le := by
      intro f hf
      rcases (mem_evalFamilyRestrictFuncCNF_iff (ρ := ρ) (Fs := Fs)).1 hf with ⟨g, hg, rfl⟩
      have hcov :
          ∀ x,
            restrictFun ρ g x =
              coveredB (selectorsFromLeaves (t := tree) (f := restrictFun ρ g)) x := by
        intro x
        rcases (mem_evalFamilyFuncCNF_iff (n := n) (Fs := Fs) (f := g)).1 hg with ⟨G, hG, rfl⟩
        -- Константность `eval` на каждом листе.
        have hconstLeaf :
            ∀ β ∈ PDT.leaves tree,
              (⟨β⟩ : Restriction n).isConstantOn (FuncCNF.eval (n := n) G) = true := by
          intro β hβ
          have hdec := leaf_decidesFamily_of_depth_lt_atom
            (Fs := Fs) (t := t) (ρ := ρ) (β := β) hβ hdepth
          have hdecG : DecidesCNFOnAtom (ρ := ⟨β⟩) (F := G) := hdec G hG
          exact decidesCNFOnAtom_isConstantOn (ρ := ⟨β⟩) (F := G) hdecG
        -- leafValue для restrictFun совпадает с leafValue для eval на листьях.
        have hleafVal_eq :
            ∀ β ∈ PDT.leaves tree,
              leafValue (β := β) (restrictFun ρ (FuncCNF.eval (n := n) G)) =
                leafValue (β := β) (FuncCNF.eval (n := n) G) := by
          intro β hβ
          have href :=
            commonCCDT_leaves_refine_root_atom (Fs := Fs) (t := t) (ρ := ρ) (β := β)
              (by simpa [tree] using hβ)
          have hy_mem :
              mem β ((⟨β⟩ : Restriction n).override (defaultBitVec n)) := by
            simpa using (Restriction.override_mem (ρ := (⟨β⟩ : Restriction n))
              (x := defaultBitVec n))
          have hy_comp := compatible_of_refines (href := href) (hmem := hy_mem)
          unfold leafValue
          unfold restrictFun
          rw [hy_comp]
          simp
        by_cases hcomp : ρ.compatible x = true
        · obtain ⟨β, hβleaf, hmem⟩ :=
            commonCCDT_leaf_of_compatible_atom (Fs := Fs) (t := t) (ρ := ρ) (x := x) hcomp
          have hconst := hconstLeaf β hβleaf
          have hval :=
            leafValue_eq_of_mem (β := β) (f := FuncCNF.eval (n := n) G)
              (hconst := hconst) (hmem := hmem)
          have hfx :
              restrictFun ρ (FuncCNF.eval (n := n) G) x =
                FuncCNF.eval (n := n) G x := by
            unfold restrictFun
            rw [hcomp]
            simp [-FuncCNF.eval]
          cases hx : FuncCNF.eval (n := n) G x with
          | true =>
            have hleafTrue :
                leafValue (β := β) (FuncCNF.eval (n := n) G) = true := by
              simpa [hval, -FuncCNF.eval] using hx
            have hsel :
                β ∈ selectorsFromLeaves (t := tree)
                  (f := restrictFun ρ (FuncCNF.eval (n := n) G)) := by
              have hleafTrue' :
                  leafValue (β := β) (restrictFun ρ (FuncCNF.eval (n := n) G)) = true := by
                simpa [hleafVal_eq β hβleaf] using hleafTrue
              have hβleaf' : β ∈ PDT.leaves tree := by
                simpa [tree] using hβleaf
              exact (List.mem_filter).2 ⟨hβleaf', by simpa using hleafTrue'⟩
            have hcov' :
                coveredB (selectorsFromLeaves (t := tree)
                  (f := restrictFun ρ (FuncCNF.eval (n := n) G))) x = true := by
              apply (covered_iff (Rset := selectorsFromLeaves (t := tree)
                (f := restrictFun ρ (FuncCNF.eval (n := n) G))) (x := x)).1
              exact ⟨β, hsel, hmem⟩
            simpa [hfx, hx, hcov', -FuncCNF.eval]
          | false =>
            have hleafFalse :
                leafValue (β := β) (FuncCNF.eval (n := n) G) = false := by
              exact hval.symm.trans hx
            have hcovfalse :
                coveredB (selectorsFromLeaves (t := tree)
                  (f := restrictFun ρ (FuncCNF.eval (n := n) G))) x = false := by
              -- если бы x был покрыт, то нашёлся бы leaf с value=true, что
              -- противоречит hleafFalse
              cases hcase : coveredB (selectorsFromLeaves (t := tree)
                  (f := restrictFun ρ (FuncCNF.eval (n := n) G))) x with
              | true =>
                  have hcov' :
                      covered (selectorsFromLeaves (t := tree)
                        (f := restrictFun ρ (FuncCNF.eval (n := n) G))) x :=
                    (covered_iff (Rset := selectorsFromLeaves (t := tree)
                      (f := restrictFun ρ (FuncCNF.eval (n := n) G))) (x := x)).2 hcase
                  rcases hcov' with ⟨β', hβ', hmem'⟩
                  have hβdata :
                      β' ∈ PDT.leaves tree ∧
                        leafValue (β := β')
                          (restrictFun ρ (FuncCNF.eval (n := n) G)) = true := by
                    simpa [selectorsFromLeaves] using hβ'
                  have hβleaf' : β' ∈ PDT.leaves tree := hβdata.1
                  have hval' :=
                    leafValue_eq_of_mem (β := β') (f := FuncCNF.eval (n := n) G)
                      (hconst := hconstLeaf β' hβleaf') (hmem := hmem')
                  have hleafTrue' :
                      leafValue (β := β') (FuncCNF.eval (n := n) G) = true := by
                    have hsel' :
                        leafValue (β := β') (restrictFun ρ (FuncCNF.eval (n := n) G)) = true :=
                      hβdata.2
                    simpa [hleafVal_eq β' hβleaf'] using hsel'
                  have : FuncCNF.eval (n := n) G x = true := by
                    simpa [hval', -FuncCNF.eval] using hleafTrue'
                  have hne : FuncCNF.eval (n := n) G x ≠ true := by
                    intro htrue
                    rw [hx] at htrue
                    cases htrue
                  exact (hne this).elim
              | false =>
                  rfl
            calc
              restrictFun ρ (FuncCNF.eval (n := n) G) x = false := by
                unfold restrictFun
                rw [hcomp]
                exact hval.trans hleafFalse
              _ = coveredB (selectorsFromLeaves (t := tree)
                    (f := restrictFun ρ (FuncCNF.eval (n := n) G))) x := by
                symm
                exact hcovfalse
        · have hcovfalse :
            coveredB (selectorsFromLeaves (t := tree)
              (f := restrictFun ρ (FuncCNF.eval (n := n) G))) x = false := by
            apply coveredB_false_of_not_compatible (t := tree) (ρ := ρ) (x := x)
            · intro β hβ
              exact commonCCDT_leaves_refine_root_atom (Fs := Fs) (t := t) (ρ := ρ) (β := β)
                (by simpa [tree] using hβ)
            · exact hcomp
          have hfx : ρ.compatible x = false := by
            cases hcx : ρ.compatible x with
            | true =>
                exact (hcomp hcx).elim
            | false =>
                rfl
          calc
            restrictFun ρ (FuncCNF.eval (n := n) G) x = false := by
              unfold restrictFun
              rw [hfx]
              rfl
            _ = coveredB (selectorsFromLeaves (t := tree)
                  (f := restrictFun ρ (FuncCNF.eval (n := n) G))) x := by
              exact hcovfalse.symm
      have herr : errU (restrictFun ρ g) (selectorsFromLeaves (t := tree) (f := restrictFun ρ g)) = 0 := by
        apply errU_eq_zero_of_agree
        intro x
        exact hcov x
      simpa [herr] using hε
  }, rfl, rfl, rfl⟩

theorem partialCertificate_from_good_restriction_common_atom
    {n t : Nat} (Fs : List (FuncCNF n))
    (ρ : Restriction n) (hgood : GoodFamily_common_atom (Fs := Fs) t ρ) :
    ∃ (ℓ : Nat) (C : PartialCertificate n ℓ (evalFamilyRestrictFuncCNF (ρ := ρ) (Fs := Fs))),
      ℓ = 0 ∧ C.depthBound = t ∧
        C.epsilon = (1 : Q) / (n + 2) := by
  have hdepth :=
    depth_lt_of_good_common_atom (Fs := Fs) (t := t) (ρ := ρ) hgood
  exact partialCertificate_from_depth_lt_common_atom
    (Fs := Fs) (ρ := ρ) (t := t) hdepth

theorem shrinkage_from_good_restriction_common_atom
    {n t : Nat} (Fs : List (FuncCNF n))
    (ρ : Restriction n) (hgood : GoodFamily_common_atom (Fs := Fs) t ρ) :
    ∃ (S : Shrinkage n),
      S.F = evalFamilyRestrictFuncCNF (ρ := ρ) (Fs := Fs) ∧ S.t = t ∧
        S.ε = (1 : Q) / (n + 2) := by
  obtain ⟨ℓ, C, hℓ, hdepth, hε⟩ :=
    partialCertificate_from_good_restriction_common_atom
      (Fs := Fs) (ρ := ρ) (t := t) hgood
  let S := C.toShrinkage
  refine ⟨S, ?_, ?_, ?_⟩
  · simp [S]
  · simp [S, hdepth, hℓ]
  · simp [S, hε]

theorem partialCertificate_from_good_restriction_trivial
    {n k t : Nat} (F : FormulaFamily n k)
    (ρ : Restriction n) (hgood : GoodFamilyCNF (F := F) t ρ) :
    ∃ (ℓ : Nat) (C : PartialCertificate n ℓ (evalFamily F)),
      ℓ = 0 ∧ C.depthBound = (allPointSubcubes n).length ∧
        C.epsilon = (1 : Q) / (n + 2) := by
  -- В этой версии `hgood` не используется: точечные selectors корректны всегда.
  -- Явно отмечаем использование, чтобы избежать предупреждения линтера.
  have _ := hgood
  simpa using (partialCertificate_from_restriction_trivial (F := F) (ρ := ρ))

theorem partialCertificate_from_good_restriction
    {n w t : Nat} (F : FormulaFamily n w)
    (ρ : Restriction n) (ht : 0 < t)
    (hgood : GoodFamilyCNF_common (F := F) t ρ) :
    ∃ (ℓ : Nat) (C : PartialCertificate n ℓ (evalFamilyRestrict (ρ := ρ) F)),
      ℓ = 0 ∧ C.depthBound = t ∧
        C.epsilon = (1 : Q) / (n + 2) := by
  simpa using
    (partialCertificate_from_good_restriction_common
      (F := F) (ρ := ρ) (t := t) ht hgood)

/-!
### Прямая упаковка в Shrinkage

Для удобства downstream‑кода сразу даём Shrinkage‑сертификат,
получаемый из частичного сертификата.
-/

theorem shrinkage_from_restriction_trivial
    {n k : Nat} (F : FormulaFamily n k)
    (ρ : Restriction n) :
    ∃ (S : Shrinkage n),
      S.F = evalFamily F ∧ S.t = (allPointSubcubes n).length ∧
        S.ε = (1 : Q) / (n + 2) := by
  obtain ⟨ℓ, C, hℓ, hdepth, hε⟩ :=
    partialCertificate_from_restriction_trivial (F := F) (ρ := ρ)
  -- Переходим к Shrinkage через `PartialCertificate.toShrinkage`.
  let S := C.toShrinkage
  refine ⟨S, ?_, ?_, ?_⟩
  · simp [S]
  · simp [S, hdepth, hℓ]
  · simp [S, hε]

theorem shrinkage_from_restriction
    {n k : Nat} (F : FormulaFamily n k)
    (ρ : Restriction n) :
    ∃ (S : Shrinkage n),
      S.F = evalFamily F ∧ S.t = (allPointSubcubes n).length ∧
        S.ε = (1 : Q) / (n + 2) := by
  simpa using (shrinkage_from_restriction_trivial (F := F) (ρ := ρ))

theorem shrinkage_from_good_restriction_trivial
    {n k t : Nat} (F : FormulaFamily n k)
    (ρ : Restriction n) (hgood : GoodFamilyCNF (F := F) t ρ) :
    ∃ (S : Shrinkage n),
      S.F = evalFamily F ∧ S.t = (allPointSubcubes n).length ∧
        S.ε = (1 : Q) / (n + 2) := by
  -- Обёртка над `shrinkage_from_restriction`: good restriction не требуется.
  have _ := hgood
  simpa using (shrinkage_from_restriction_trivial (F := F) (ρ := ρ))

theorem shrinkage_from_good_restriction
    {n w t : Nat} (F : FormulaFamily n w)
    (ρ : Restriction n) (ht : 0 < t)
    (hgood : GoodFamilyCNF_common (F := F) t ρ) :
    ∃ (S : Shrinkage n),
      S.F = evalFamilyRestrict (ρ := ρ) F ∧ S.t = t ∧
        S.ε = (1 : Q) / (n + 2) := by
  simpa using
    (shrinkage_from_good_restriction_common
      (F := F) (ρ := ρ) (t := t) ht hgood)

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
    {n w s t : Nat} (F : Core.CNF n w)
    (hbound :
      (R_s (n := n) (s - t)).card * (2 * n) ^ t
        < (R_s (n := n) s).card) :
    ∃ (ℓ : Nat) (C : PartialCertificate n ℓ (evalFamily ([F] : FormulaFamily n w))),
      ℓ = 0 ∧ C.depthBound = (allPointSubcubes n).length ∧
        C.epsilon = (1 : Q) / (n + 2) := by
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
  exact partialCertificate_from_good_restriction_trivial
    (F := ([F] : FormulaFamily n w)) (ρ := ρ) hgood

/-!
### Shrinkage-обёртка для depth‑2 CNF из counting bound

Это прямое продолжение предыдущей леммы: строим `Shrinkage` через
`PartialCertificate.toShrinkage`.
-/

theorem shrinkage_depth2_cnf_of_bound
    {n w s t : Nat} (F : Core.CNF n w)
    (hbound :
      (R_s (n := n) (s - t)).card * (2 * n) ^ t
        < (R_s (n := n) s).card) :
    ∃ (S : Shrinkage n),
      S.F = evalFamily ([F] : FormulaFamily n w) ∧
        S.t = (allPointSubcubes n).length ∧ S.ε = (1 : Q) / (n + 2) := by
  obtain ⟨ℓ, C, hℓ, hdepth, hε⟩ :=
    partialCertificate_depth2_cnf_of_bound (F := F) (s := s) (t := t) hbound
  let S := C.toShrinkage
  refine ⟨S, ?_, ?_, ?_⟩
  · simp [S]
  · simp [S, hdepth, hℓ]
  · simp [S, hε]

/-!
### Семейство CNF: certificate/shrinkage из counting bound

Полный семейный вариант: по числовой границе строим good restriction,
затем получаем `PartialCertificate` и `Shrinkage` для всего семейства.
-/

theorem partialCertificate_depth2_cnf_family_of_bound
    {n w s t : Nat} (F : FormulaFamily n w)
    (hbound :
      (R_s (n := n) (s - t)).card * (F.length + 1) * (2 * n) ^ t
        < (R_s (n := n) s).card) :
    ∃ (ℓ : Nat) (C : PartialCertificate n ℓ (evalFamily F)),
      ℓ = 0 ∧ C.depthBound = (allPointSubcubes n).length ∧
        C.epsilon = (1 : Q) / (n + 2) := by
  obtain ⟨ρ, hρs, hnotbad⟩ :=
    exists_good_restriction_cnf_family_of_bound_small (F := F) (s := s) (t := t) hbound
  have hgood : GoodFamilyCNF (F := F) t ρ := by
    exact (goodFamilyCNF_iff_not_bad (F := F) (t := t) (ρ := ρ)).2 hnotbad
  exact partialCertificate_from_good_restriction_trivial (F := F) (ρ := ρ) hgood

theorem shrinkage_depth2_cnf_family_of_bound
    {n w s t : Nat} (F : FormulaFamily n w)
    (hbound :
      (R_s (n := n) (s - t)).card * (F.length + 1) * (2 * n) ^ t
        < (R_s (n := n) s).card) :
    ∃ (S : Shrinkage n),
      S.F = evalFamily F ∧ S.t = (allPointSubcubes n).length ∧
        S.ε = (1 : Q) / (n + 2) := by
  obtain ⟨ℓ, C, hℓ, hdepth, hε⟩ :=
    partialCertificate_depth2_cnf_family_of_bound (F := F) (s := s) (t := t) hbound
  let S := C.toShrinkage
  refine ⟨S, ?_, ?_, ?_⟩
  · simp [S]
  · simp [S, hdepth, hℓ]
  · simp [S, hε]

end MultiSwitching
end AC0
end Pnp3
