import Mathlib.Algebra.Order.Field.Basic
import Core.BooleanBasics
import Core.ShrinkageWitness
import Core.PDTPartial
import ThirdPartyFacts.Facts_Switching
import AC0.MultiSwitching.Definitions
import AC0.MultiSwitching.BadEvents
import AC0.MultiSwitching.Counting
import AC0.MultiSwitching.TraceBridge
import AC0.MultiSwitching.CanonicalDT
import AC0.MultiSwitching.Trace

namespace Pnp3
namespace AC0
namespace MultiSwitching

open Core
open ThirdPartyFacts

/--
**TRIVIAL/LEGACY**: Точечные подкубы для заглушки.
-/
noncomputable def allPointSubcubes (n : Nat) : List (Subcube n) :=
  (Finset.univ : Finset (Core.BitVec n)).toList.map Core.pointSubcube

/--
**TRIVIAL/LEGACY**: Выбор всех точек, где функция истинна.
-/
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

theorem partialCertificate_from_restriction_trivial
    {n k : Nat} (F : FormulaFamily n k)
    (ρ : Restriction n) :
    ∃ (ℓ : Nat) (C : PartialCertificate n ℓ (evalFamily F)),
      ℓ = 0 ∧ C.depthBound = (allPointSubcubes n).length ∧
        C.epsilon = (1 : Q) / (n + 2) := by
  classical
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

noncomputable def canonicalCCDT
    {n w : Nat} (F : FormulaFamily n w) (ρ : Restriction n) : PDT n :=
  canonicalCCDT_CNF_aux F ρ.freeCount ρ

lemma good_implies_good_one
    {n w t : Nat} (F : FormulaFamily n w) (ρ : Restriction n)
    (hgood : GoodFamily F t ρ) :
    ∀ i : Fin F.length, ¬ BadCNF (F.get i) t ρ := by
  intro i
  exact hgood i.1 i.2

lemma depth_lt_t_of_good_one
    {n w t : Nat} {F : Core.CNF n w} {ρ : Restriction n}
    (hgood : ¬ BadCNF F t ρ) :
    PDT.depth (canonicalDT_CNF F ρ) < t := by
  have h_imp := badCNF_of_depth_ge_canonicalDT F (ρ := ρ) (t := t)
  have h_not_le : ¬ (t ≤ PDT.depth (canonicalDT_CNF F ρ)) :=
    mt h_imp hgood
  exact Nat.lt_of_not_ge h_not_le

lemma canonicalDT_depth_monotone
    {n w : Nat} (F : Core.CNF n w) (ρ ρ' : Restriction n)
    (h_ref : subcubeRefines ρ'.mask ρ.mask) :
    PDT.depth (canonicalDT_CNF F ρ') ≤ PDT.depth (canonicalDT_CNF F ρ) := by
  -- Это свойство интуитивно верно (уточнение рестрикции упрощает формулу),
  -- но требует структурной индукции по построению дерева.
  sorry

lemma depth_lt_t_of_good_one_refined
    {n w t : Nat} {F : Core.CNF n w} {ρ ρ' : Restriction n}
    (h_ref : subcubeRefines ρ'.mask ρ.mask)
    (hgood : ¬ BadCNF F t ρ) :
    PDT.depth (canonicalDT_CNF F ρ') < t := by
  have h1 := depth_lt_t_of_good_one hgood
  have h2 := canonicalDT_depth_monotone F ρ ρ' h_ref
  exact Nat.lt_of_le_of_lt h2 h1

def SmallDepthEverywhere
    {n w : Nat} (F : FormulaFamily n w) (t : Nat) (ρ : Restriction n) : Prop :=
  ∀ f ∈ F, ∀ (β : Subcube n), subcubeRefines β ρ.mask →
    PDT.depth (canonicalDT_CNF f ⟨β⟩) < t

lemma canonicalDT_depth_le_of_fuel_ge
    {n w : Nat} (f : Core.CNF n w) (fuel : Nat) (ρ : Restriction n)
    (hfuel : ρ.freeCount ≤ fuel) :
    PDT.depth (canonicalDT_CNF_aux f fuel ρ) = PDT.depth (canonicalDT_CNF f ρ) := by
  sorry

lemma canonicalCCDT_depth_le_sum_t_of_small_depth
    {n w t : Nat} (F : FormulaFamily n w) (fuel : Nat) (ρ : Restriction n)
    (hfuel : ρ.freeCount ≤ fuel)
    (hsmall : SmallDepthEverywhere F t ρ) :
    PDT.depth (canonicalCCDT_CNF_aux F fuel ρ) ≤ F.length * t := by
  induction F generalizing ρ with
  | nil =>
      simp [canonicalCCDT_CNF_aux, PDT.depth]
  | cons f rest ih =>
      simp [canonicalCCDT_CNF_aux]
      -- Trunk depth bound
      have htrunk : PDT.depth (canonicalDT_CNF_aux f fuel ρ) < t := by
        have hdepth := hsmall f (List.mem_cons_self) ρ.mask (subcubeRefines_refl _)
        have heq := canonicalDT_depth_le_of_fuel_ge f fuel ρ hfuel
        rwa [heq]
      -- Tails depth bound
      have htails : ∀ β ∈ PDT.leaves (canonicalDT_CNF_aux f fuel ρ),
          PDT.depth (canonicalCCDT_CNF_aux rest fuel ⟨β⟩) ≤ rest.length * t := by
        intro β hβ
        have hrefines : subcubeRefines β ρ.mask := by sorry
        have hfuel' : (Restriction.mk β).freeCount ≤ fuel := by sorry
        apply ih (ρ := ⟨β⟩) hfuel'
        intro g hg γ hγ
        have hrefines' : subcubeRefines γ β := hγ
        have hrefines'' : subcubeRefines γ ρ.mask :=
          subcubeRefines_trans hrefines' hrefines
        apply hsmall g (List.mem_cons_of_mem f hg) γ hrefines''
      -- Combine
      have hrefine := PDT.depth_refine_le (t := canonicalDT_CNF_aux f fuel ρ)
        (tails := fun β _ => canonicalCCDT_CNF_aux rest fuel ⟨β⟩)
        (ℓ := rest.length * t) htails
      calc
        PDT.depth (PDT.refine (canonicalDT_CNF_aux f fuel ρ) (fun β _ => canonicalCCDT_CNF_aux rest fuel ⟨β⟩))
            ≤ PDT.depth (canonicalDT_CNF_aux f fuel ρ) + rest.length * t := hrefine
        _ ≤ t + rest.length * t := by
              apply Nat.add_le_add_right
              exact Nat.le_of_lt htrunk
        _ = (rest.length + 1) * t := by
              rw [Nat.add_comm t, ← Nat.succ_mul]

lemma good_implies_small_depth
    {n w t : Nat} (F : FormulaFamily n w) (ρ : Restriction n)
    (hgood : GoodFamily F t ρ) :
    SmallDepthEverywhere F t ρ := by
  intro f hf β hβ
  have hbad_not : ¬ BadCNF f t ρ := by
    rcases List.mem_iff_get.mp hf with ⟨i, rfl⟩
    exact hgood i i.2
  have hdepth_rho : PDT.depth (canonicalDT_CNF f ρ) < t :=
    depth_lt_t_of_good_one hbad_not
  have hdepth_beta :
      PDT.depth (canonicalDT_CNF f ⟨β⟩) ≤ PDT.depth (canonicalDT_CNF f ρ) :=
    canonicalDT_depth_monotone f ρ ⟨β⟩ hβ
  exact Nat.lt_of_le_of_lt hdepth_beta hdepth_rho

lemma canonicalCCDT_depth_le_sum_t
    {n w t : Nat} (F : FormulaFamily n w) (ρ : Restriction n)
    (hgood : GoodFamily F t ρ) :
    PDT.depth (canonicalCCDT F ρ) ≤ F.length * t := by
  unfold canonicalCCDT
  apply canonicalCCDT_depth_le_sum_t_of_small_depth
  · exact Nat.le_refl _
  · exact good_implies_small_depth F ρ hgood

def IsConstantOn {n : Nat} (f : Core.BitVec n → Bool) (β : Subcube n) : Prop :=
  ∀ x y, mem β x → mem β y → f x = f y

lemma canonicalDT_resolves
    {n w : Nat} (F : Core.CNF n w) (ρ : Restriction n) :
    ∀ β ∈ PDT.leaves (canonicalDT_CNF F ρ),
      IsConstantOn (evalCNF F) β := by
  -- Каноническое дерево ветвится по переменным, пока есть pending clauses.
  -- Если pending clauses нет, формула константна.
  -- Требуется лемма о связи pending clauses и константности.
  sorry

lemma isConstantOn_of_refines
    {n : Nat} {f : Core.BitVec n → Bool} {β γ : Subcube n}
    (hconst : IsConstantOn f γ) (href : subcubeRefines β γ) :
    IsConstantOn f β := by
  intro x y hx hy
  have hsubset : ∀ z, mem β z → mem γ z := by
    intro z hz
    rw [mem_iff] at hz ⊢
    intro i b hb
    exact hz i b (href i b hb)
  exact hconst x y (hsubset x hx) (hsubset y hy)

lemma canonicalCCDT_aux_resolves
    {n w : Nat} (F : FormulaFamily n w) (fuel : Nat) (ρ : Restriction n)
    (hfuel : ρ.freeCount ≤ fuel) :
    ∀ β ∈ PDT.leaves (canonicalCCDT_CNF_aux F fuel ρ),
      ∀ f ∈ F, IsConstantOn (evalCNF f) β := by
  induction F generalizing ρ with
  | nil =>
      intro β _ f hf
      cases hf
  | cons f rest ih =>
      intro β hβ g hg
      simp [canonicalCCDT_CNF_aux] at hβ
      have hex : ∃ γ ∈ PDT.leaves (canonicalDT_CNF_aux f fuel ρ),
                 β ∈ PDT.leaves (canonicalCCDT_CNF_aux rest fuel ⟨γ⟩) := by
        sorry
      rcases hex with ⟨γ, hγ, hβ_tail⟩
      have href : subcubeRefines β γ := by
        sorry
      cases hg with
      | head =>
          have htrunk_resolves : IsConstantOn (evalCNF f) γ := by
             have heq : PDT.leaves (canonicalDT_CNF_aux f fuel ρ) = PDT.leaves (canonicalDT_CNF f ρ) := by
               sorry
             rw [heq] at hγ
             exact canonicalDT_resolves f ρ γ hγ
          exact isConstantOn_of_refines htrunk_resolves href
      | tail _ hg' =>
          have hfuel' : (Restriction.mk γ).freeCount ≤ fuel := by sorry
          have hres := ih (ρ := ⟨γ⟩) hfuel' β hβ_tail g hg'
          exact hres

lemma canonicalCCDT_resolves
    {n w : Nat} (F : FormulaFamily n w) (ρ : Restriction n) :
    ∀ β ∈ PDT.leaves (canonicalCCDT F ρ),
      ∀ f ∈ F, IsConstantOn (evalCNF f) β := by
  unfold canonicalCCDT
  exact canonicalCCDT_aux_resolves F ρ.freeCount ρ (Nat.le_refl _)

def witnessOf {n : Nat} (β : Subcube n) : Core.BitVec n :=
  fun i => match β i with
  | some b => b
  | none => false

lemma mem_witnessOf {n : Nat} (β : Subcube n) :
    mem β (witnessOf β) := by
  apply (mem_iff (β := β) (x := witnessOf β)).mpr
  intro i b hb
  simp [witnessOf, hb]

theorem partialCertificate_from_good_restriction
    {n k t : Nat} (F : FormulaFamily n k)
    (ρ : Restriction n) (hgood : GoodFamilyCNF (F := F) t ρ) :
    ∃ (ℓ : Nat) (C : PartialCertificate n ℓ (evalFamily F)),
      ℓ = 0 ∧ C.depthBound = F.length * t ∧
        C.epsilon = (1 : Q) / (n + 2) := by
  classical
  let tree := canonicalCCDT F ρ
  let leaves := PDT.leaves tree
  let selectors (g : Core.BitVec n → Bool) : List (Subcube n) :=
    leaves.filter (fun β => g (witnessOf β))

  have hresolves : ∀ β ∈ leaves, ∀ g ∈ evalFamily F, IsConstantOn g β := by
    intro β hβ g hg
    rcases mem_evalFamily_iff.mp hg with ⟨G, hG, rfl⟩
    exact canonicalCCDT_resolves F ρ β hβ G hG

  have herr : ∀ g ∈ evalFamily F, errU g (selectors g) = 0 := by
    intro g hg
    apply errU_eq_zero_of_agree
    intro x
    have hcover : covered leaves x := by
      sorry
    rcases hcover with ⟨β, hβ, hmem⟩
    have hconst := hresolves β hβ g hg
    by_cases hval : g x = true
    · have hwit : g (witnessOf β) = true := by
        rw [← hval]
        apply hconst
        · exact mem_witnessOf β
        · exact hmem
      have hsel : β ∈ selectors g := by
        simp [selectors, hβ, hwit]
      have hcov : coveredB (selectors g) x = true :=
        (covered_iff (Rset := selectors g) (x := x)).mp ⟨β, hsel, hmem⟩
      rw [hval, hcov]
    · have hval_false : g x = false := Bool.eq_false_iff.mpr hval
      have hwit : g (witnessOf β) = false := by
        rw [← hval_false]
        apply hconst
        · exact mem_witnessOf β
        · exact hmem
      have hsel : β ∉ selectors g := by
        simp [selectors, hwit]
      have hcov : coveredB (selectors g) x = false := by
        sorry
      rw [hval_false, hcov]

  refine ⟨0, {
    witness := PartialDT.ofPDT tree
    depthBound := F.length * t
    epsilon := (1 : Q) / (n + 2)
    trunk_depth_le := by
      simpa [PartialDT.ofPDT] using canonicalCCDT_depth_le_sum_t F ρ hgood
    selectors := selectors
    selectors_sub := by
      intro g β hg hβ
      simp [selectors] at hβ
      simpa [PartialDT.realize_ofPDT] using hβ.1
    err_le := by
      intro g hg
      have h0 := herr g hg
      rw [h0]
      have h1 : (0 : Q) <= 1 := by norm_num
      have h2 : (0 : Q) <= n + 2 := by exact_mod_cast (Nat.zero_le (n + 2))
      exact div_nonneg h1 h2
  }, rfl, rfl, rfl⟩

theorem shrinkage_from_restriction_trivial
    {n k : Nat} (F : FormulaFamily n k)
    (ρ : Restriction n) :
    ∃ (S : Shrinkage n),
      S.F = evalFamily F ∧ S.t = (allPointSubcubes n).length ∧
        S.ε = (1 : Q) / (n + 2) := by
  obtain ⟨ℓ, C, hℓ, hdepth, hε⟩ :=
    partialCertificate_from_restriction_trivial (F := F) (ρ := ρ)
  let S := C.toShrinkage
  refine ⟨S, ?_, ?_, ?_⟩
  · simp [S]
  · simp [S, hdepth, hℓ]
  · simp [S, hε]

theorem shrinkage_from_good_restriction
    {n k t : Nat} (F : FormulaFamily n k)
    (ρ : Restriction n) (hgood : GoodFamilyCNF (F := F) t ρ) :
    ∃ (S : Shrinkage n),
      S.F = evalFamily F ∧ S.t = F.length * t ∧
        S.ε = (1 : Q) / (n + 2) := by
  obtain ⟨ℓ, C, hℓ, hdepth, hε⟩ :=
    partialCertificate_from_good_restriction (F := F) (ρ := ρ) hgood
  let S := C.toShrinkage
  refine ⟨S, ?_, ?_, ?_⟩
  · simp [S]
  · simp [S, hdepth, hℓ]
  · simp [S, hε]

/-!
### Sanity Check

Проверяем, что построенный shrinkage действительно имеет ожидаемые параметры.
-/

lemma shrinkage_from_good_restriction_sanity_check
    {n k t : Nat} (F : FormulaFamily n k)
    (ρ : Restriction n) (hgood : GoodFamilyCNF (F := F) t ρ) :
    ∃ S : Shrinkage n, S.t = F.length * t ∧ S.ε = (1 : Q) / (n + 2) := by
  obtain ⟨S, _, ht, hε⟩ := shrinkage_from_good_restriction F ρ hgood
  exact ⟨S, ht, hε⟩

end MultiSwitching
end AC0
end Pnp3
