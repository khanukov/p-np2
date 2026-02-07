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

lemma Restriction.freeCount_le_n {n : Nat} (ρ : Restriction n) : ρ.freeCount ≤ n := by
  rw [← Restriction.freePositions_card_eq_freeCount]
  exact le_trans (Finset.card_filter_le _ _) (by simp)

lemma freeCount_le_of_subcubeRefines {n : Nat} {β γ : Restriction n}
    (h : subcubeRefines β.mask γ.mask) :
    β.freeCount ≤ γ.freeCount := by
  rw [← Restriction.freePositions_card_eq_freeCount]
  rw [← Restriction.freePositions_card_eq_freeCount]
  apply Finset.card_le_card
  intro i hi
  rw [Restriction.mem_freePositions] at hi ⊢
  rw [Option.isNone_iff_eq_none] at hi ⊢
  by_contra hsome
  have hsome' : γ.mask i ≠ none := hsome
  obtain ⟨b, hb⟩ := Restriction.mask_eq_some_of_not_none hsome'
  have hb_beta : β.mask i = some b := h i b hb
  simp [hb_beta] at hi

lemma canonicalDT_depth_monotone_global
    {n w : Nat} (F : Core.CNF n w) (ρ ρ' : Restriction n)
    (h_ref : subcubeRefines ρ'.mask ρ.mask) :
    PDT.depth (canonicalDT_CNF F ρ') ≤ PDT.depth (canonicalDT_CNF F ρ) := by
  -- Use `TraceBridge.canonicalDT_depth_monotone` with `fuel = ρ.freeCount`.
  -- Step 1: depth(aux F ρ'.freeCount ρ') ≤ depth(aux F ρ.freeCount ρ')
  have h_fuel_le : ρ'.freeCount ≤ ρ.freeCount := freeCount_le_of_subcubeRefines h_ref
  have h1 : PDT.depth (canonicalDT_CNF_aux F ρ'.freeCount ρ') ≤
            PDT.depth (canonicalDT_CNF_aux F ρ.freeCount ρ') :=
    canonicalDT_CNF_aux_depth_monotone_fuel F ρ' h_fuel_le
  -- Step 2: depth(aux F ρ.freeCount ρ') ≤ depth(aux F ρ.freeCount ρ)
  have h_ref_restr : Restriction.refines ρ' ρ := h_ref
  have h2 : PDT.depth (canonicalDT_CNF_aux F ρ.freeCount ρ') ≤
            PDT.depth (canonicalDT_CNF_aux F ρ.freeCount ρ) :=
    canonicalDT_depth_monotone F ρ.freeCount ρ' ρ h_ref_restr
  -- Combine
  unfold canonicalDT_CNF
  exact Nat.le_trans h1 h2

lemma depth_lt_t_of_good_one_refined
    {n w t : Nat} {F : Core.CNF n w} {ρ ρ' : Restriction n}
    (h_ref : subcubeRefines ρ'.mask ρ.mask)
    (hgood : ¬ BadCNF F t ρ) :
    PDT.depth (canonicalDT_CNF F ρ') < t := by
  have h1 := depth_lt_t_of_good_one hgood
  have h2 := canonicalDT_depth_monotone_global F ρ ρ' h_ref
  exact Nat.lt_of_le_of_lt h2 h1

def SmallDepthEverywhere
    {n w : Nat} (F : FormulaFamily n w) (t : Nat) (ρ : Restriction n) : Prop :=
  ∀ f ∈ F, ∀ (β : Subcube n), subcubeRefines β ρ.mask →
    PDT.depth (canonicalDT_CNF f ⟨β⟩) < t

lemma canonicalDT_CNF_aux_stable
    {n w : Nat} (F : Core.CNF n w) (ρ : Restriction n) (fuel : Nat)
    (hfuel : ρ.freeCount ≤ fuel) :
    canonicalDT_CNF_aux F fuel ρ = canonicalDT_CNF_aux F ρ.freeCount ρ := by
  induction h : ρ.freeCount generalizing ρ fuel with
  | zero =>
      cases fuel with
      | zero => rfl
      | succ fuel' =>
          unfold canonicalDT_CNF_aux
          have hnone : Restriction.firstPendingClause? ρ F.clauses = none := by
            cases hsel : Restriction.firstPendingClause? ρ F.clauses with
            | none => rfl
            | some selection =>
                let ℓ := chooseFreeLiteral (w := selection.witness)
                have hmem := chooseFreeLiteral_mem (w := selection.witness)
                have hfree := Restriction.ClausePendingWitness.literal_idx_mem_freeIndicesList
                  (ρ := ρ) (C := selection.clause) (w := selection.witness) (ℓ := ℓ) hmem
                have hpos : 0 < ρ.freeCount :=
                   Restriction.freeCount_pos_of_mem_freeIndicesList hfree
                rw [h] at hpos
                contradiction
          rw [hnone]
  | succ k ih =>
      cases fuel with
      | zero =>
          rw [h] at hfuel
          linarith
      | succ fuel' =>
          unfold canonicalDT_CNF_aux
          cases hsel : Restriction.firstPendingClause? ρ F.clauses with
          | none =>
              rfl
          | some selection =>
              let ℓ := chooseFreeLiteral (w := selection.witness)
              have hmem : ℓ ∈ selection.witness.free :=
                chooseFreeLiteral_mem (w := selection.witness)
              have hfree :
                  ℓ.idx ∈ ρ.freeIndicesList :=
                Restriction.ClausePendingWitness.literal_idx_mem_freeIndicesList
                  (ρ := ρ) (C := selection.clause) (w := selection.witness) (ℓ := ℓ) hmem
              have hcounts := @canonicalDT_CNF_aux_branch_freeCount n w F (Nat.succ fuel') ρ selection hsel
              have hcount0 : (Classical.choose (Restriction.assign_some_of_mem_freeIndicesList (ρ := ρ) (i := ℓ.idx) (b := false) hfree)).freeCount = k := by
                rw [hcounts.1, h, Nat.succ_sub_one]
              have hcount1 : (Classical.choose (Restriction.assign_some_of_mem_freeIndicesList (ρ := ρ) (i := ℓ.idx) (b := true) hfree)).freeCount = k := by
                rw [hcounts.2, h, Nat.succ_sub_one]

              rw [h] at hfuel
              dsimp only
              congr 1
              · apply ih (ρ := _) (fuel := fuel')
                · rw [hcount0]; exact Nat.le_of_succ_le_succ hfuel
                · exact hcount0
              · apply ih (ρ := _) (fuel := fuel')
                · rw [hcount1]; exact Nat.le_of_succ_le_succ hfuel
                · exact hcount1

lemma canonicalDT_depth_le_of_fuel_ge
    {n w : Nat} (f : Core.CNF n w) (fuel : Nat) (ρ : Restriction n)
    (hfuel : ρ.freeCount ≤ fuel) :
    PDT.depth (canonicalDT_CNF_aux f fuel ρ) = PDT.depth (canonicalDT_CNF f ρ) := by
  unfold canonicalDT_CNF
  rw [canonicalDT_CNF_aux_stable f ρ fuel hfuel]

lemma PDT.mem_leaves_refine_iff
    {n : Nat} {t : PDT n} {tails : ∀ β, β ∈ PDT.leaves t → PDT n}
    {β : Subcube n} :
    β ∈ PDT.leaves (PDT.refine t tails) ↔
      ∃ γ hγ, β ∈ PDT.leaves (tails γ hγ) := by
  induction t with
  | leaf γ =>
      simp [PDT.refine, PDT.leaves]
  | node i t0 t1 ih0 ih1 =>
      simp [PDT.refine, PDT.leaves]
      constructor
      · intro h
        -- Simplify mem (++ ...) to Or
        rcases h with h0 | h1
        · rw [ih0] at h0
          rcases h0 with ⟨γ, hγ, hmem⟩
          exact ⟨γ, Or.inl hγ, hmem⟩
        · rw [ih1] at h1
          rcases h1 with ⟨γ, hγ, hmem⟩
          exact ⟨γ, Or.inr hγ, hmem⟩
      · rintro ⟨γ, hγ, hmem⟩
        rcases hγ with hγ0 | hγ1
        · left
          rw [ih0]
          exact ⟨γ, hγ0, hmem⟩
        · right
          rw [ih1]
          exact ⟨γ, hγ1, hmem⟩

lemma assign_refines {ρ : Restriction n} (i : Fin n) {b : Bool}
    {ρ' : Restriction n} (h : ρ.assign i b = some ρ') :
    subcubeRefines ρ'.mask ρ.mask := by
  intro j val hj
  unfold Restriction.assign at h
  cases hsub : Subcube.assign ρ.mask i b with
  | none =>
    rw [hsub] at h
    contradiction
  | some β =>
    rw [hsub] at h
    injection h with h_eq
    subst h_eq
    unfold Subcube.assign at hsub
    cases hmask : ρ.mask i
    · rw [hmask] at hsub
      dsimp at hsub
      simp at hsub
      subst hsub
      dsimp
      by_cases hij : j = i
      · subst hij
        rw [hmask] at hj
        contradiction
      · simp [hij]; exact hj
    · rw [hmask] at hsub
      dsimp at hsub
      split_ifs at hsub <;> try { contradiction }
      simp at hsub; subst hsub; exact hj

lemma canonicalDT_CNF_aux_leaves_refine_rho
    {n w : Nat} (F : Core.CNF n w) (ρ : Restriction n) (fuel : Nat) :
    ∀ β ∈ PDT.leaves (canonicalDT_CNF_aux F fuel ρ), subcubeRefines β ρ.mask := by
  induction fuel generalizing ρ with
  | zero =>
      unfold canonicalDT_CNF_aux
      intro β hβ
      cases hβ
      · exact subcubeRefines_refl _
      · contradiction
  | succ fuel ih =>
      unfold canonicalDT_CNF_aux
      match hsel : Restriction.firstPendingClause? ρ F.clauses with
      | none =>
          simp only
          intro β hβ
          cases hβ
          · exact subcubeRefines_refl _
          · contradiction
      | some selection =>
          simp only
          intro β hβ
          simp only [PDT.leaves] at hβ
          rw [List.mem_append] at hβ
          rcases hβ with hβ | hβ
          · have href0 := ih _ β hβ
            let ℓ := chooseFreeLiteral (w := selection.witness)
            have hmem := chooseFreeLiteral_mem (w := selection.witness)
            have hfree := Restriction.ClausePendingWitness.literal_idx_mem_freeIndicesList
                  (ρ := ρ) (C := selection.clause) (w := selection.witness) (ℓ := ℓ) hmem
            let ρ0 := Classical.choose (Restriction.assign_some_of_mem_freeIndicesList (ρ := ρ) (i := ℓ.idx) (b := false) hfree)
            have hassign0 : ρ.assign ℓ.idx false = some ρ0 := Classical.choose_spec (Restriction.assign_some_of_mem_freeIndicesList (ρ := ρ) (i := ℓ.idx) (b := false) hfree)
            exact subcubeRefines_trans href0 (assign_refines ℓ.idx hassign0)
          · have href1 := ih _ β hβ
            let ℓ := chooseFreeLiteral (w := selection.witness)
            have hmem := chooseFreeLiteral_mem (w := selection.witness)
            have hfree := Restriction.ClausePendingWitness.literal_idx_mem_freeIndicesList
                  (ρ := ρ) (C := selection.clause) (w := selection.witness) (ℓ :=ℓ) hmem
            let ρ1 := Classical.choose (Restriction.assign_some_of_mem_freeIndicesList (ρ := ρ) (i := ℓ.idx) (b := true) hfree)
            have hassign1 : ρ.assign ℓ.idx true = some ρ1 := Classical.choose_spec (Restriction.assign_some_of_mem_freeIndicesList (ρ := ρ) (i := ℓ.idx) (b := true) hfree)
            exact subcubeRefines_trans href1 (assign_refines ℓ.idx hassign1)

lemma canonicalCCDT_CNF_aux_leaves_refine_rho
    {n w : Nat} (F : FormulaFamily n w) (ρ : Restriction n) (fuel : Nat) :
    ∀ β ∈ PDT.leaves (canonicalCCDT_CNF_aux F fuel ρ), subcubeRefines β ρ.mask := by
  induction F generalizing ρ with
  | nil =>
      unfold canonicalCCDT_CNF_aux
      intro β hβ
      simp [PDT.leaves] at hβ
      rw [hβ]
      apply subcubeRefines_refl
  | cons f rest ih =>
      unfold canonicalCCDT_CNF_aux
      intro β hβ
      rw [PDT.mem_leaves_refine_iff] at hβ
      rcases hβ with ⟨γ, hγ, hβ⟩
      -- β refines γ. γ refines ρ.
      have href_tail := ih (Restriction.mk γ) β hβ
      have href_trunk := canonicalDT_CNF_aux_leaves_refine_rho f ρ fuel γ hγ
      exact subcubeRefines_trans href_tail href_trunk

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
        have hrefines : subcubeRefines β ρ.mask := canonicalDT_CNF_aux_leaves_refine_rho f ρ fuel β hβ
        have hfuel' : (Restriction.mk β).freeCount ≤ fuel := by
           have hle := freeCount_le_of_subcubeRefines hrefines
           exact Nat.le_trans hle hfuel
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
    canonicalDT_depth_monotone_global f ρ ⟨β⟩ hβ
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

lemma clauseStatus_satisfied_iff {n : Nat} {ρ : Restriction n} {C : CnfClause n} :
    ρ.clauseStatus C = Restriction.ClauseStatus.satisfied ↔
      ∃ ℓ ∈ C.literals, ρ.literalStatus ℓ = LiteralStatus.satisfied := by
  unfold Restriction.clauseStatus
  by_cases h : ∃ ℓ ∈ C.literals, ρ.literalStatus ℓ = LiteralStatus.satisfied
  · rw [dif_pos h]
    rw [iff_true_intro h]
    simp
  · rw [dif_neg h]
    rw [iff_false_intro h]
    simp only [iff_false]
    intro H
    simp at H
    split_ifs at H

lemma evalCNF_const_of_firstPending_none
    {n w : Nat} (F : Core.CNF n w) (ρ : Restriction n)
    (h : Restriction.firstPendingClause? ρ F.clauses = none) :
    IsConstantOn (evalCNF F) ρ.mask := by
  intro x y hx hy
  have h_gen : ∀ clauses, Restriction.firstPendingClause? ρ clauses = none →
      IsConstantOn (fun z => clauses.all (fun C => C.eval z)) ρ.mask := by
    intro clauses h_none
    induction clauses with
    | nil =>
      intro x y _ _
      simp [List.all_nil]
    | cons C rest ih =>
      cases h_stat : ρ.clauseStatus C
      -- Case 1: satisfied
      · unfold Restriction.firstPendingClause? at h_none
        split at h_none
        · contradiction
        · split at h_none
          next h_rest =>
            have hrest := ih h_rest
            rw [clauseStatus_satisfied_iff] at h_stat
            rcases h_stat with ⟨ℓ, hℓ, hsat⟩
            have hC : ∀ z, mem ρ.mask z → C.eval z = true := by
              intro z hz
              apply CnfClause.holds_of_mem_eval_true hℓ
              rw [← Restriction.override_eq_of_mem hz]
              exact Restriction.literalStatus_eval_override_true hsat
            intro x y hx hy
            simp only [List.all_cons]
            rw [hC x hx, hC y hy]
            simp
            exact hrest x y hx hy
          · contradiction
        · unfold Restriction.clauseStatus at *; rw [h_stat] at *; contradiction
      -- Case 2: falsified
      · unfold Restriction.firstPendingClause? at h_none
        split at h_none
        · unfold Restriction.clauseStatus at *; rw [h_stat] at *; contradiction
        · unfold Restriction.clauseStatus at *; rw [h_stat] at *; contradiction
        · have hC : ∀ z, mem ρ.mask z → C.eval z = false := by
            intro z hz
            rw [CnfClause.eval_eq_false_iff]
            intro ℓ hℓ
            rw [← Restriction.override_eq_of_mem hz]
            apply Restriction.literalStatus_eval_override_false
            unfold Restriction.clauseStatus at h_stat
            by_cases hsat : ∃ ℓ ∈ C.literals, ρ.literalStatus ℓ = LiteralStatus.satisfied
            · rw [dif_pos hsat] at h_stat; contradiction
            · rw [dif_neg hsat] at h_stat
              by_cases hfree : ρ.freeLiterals C = []
              · rw [dif_pos hfree] at h_stat
                have h_not_sat : ρ.literalStatus ℓ ≠ LiteralStatus.satisfied := by
                    intro hs
                    apply hsat
                    exact ⟨ℓ, hℓ, hs⟩
                have h_not_un : ρ.literalStatus ℓ ≠ LiteralStatus.unassigned := by
                  intro hu
                  have : ℓ ∈ ρ.freeLiterals C := by
                     rw [Restriction.mem_freeLiterals]
                     exact ⟨hℓ, hu⟩
                  rw [hfree] at this
                  contradiction
                have h_status_cases := LiteralStatus.eq_satisfied_or_eq_falsified_or_eq_unassigned (ρ.literalStatus ℓ)
                cases h_status_cases with
                | inl h => contradiction
                | inr h =>
                  cases h with
                  | inl h => exact h
                  | inr h => contradiction
              · rw [dif_neg hfree] at h_stat; contradiction
          intro x y hx hy
          simp only [List.all_cons]
          rw [hC x hx, hC y hy]
          simp
      -- Case 3: pending
      · unfold Restriction.firstPendingClause? at h_none
        split at h_none
        · contradiction
        · unfold Restriction.clauseStatus at *; rw [h_stat] at *; contradiction
        · unfold Restriction.clauseStatus at *; rw [h_stat] at *; contradiction
  exact h_gen F.clauses h x y hx hy

lemma canonicalDT_CNF_aux_resolves
    {n w : Nat} (F : Core.CNF n w) (ρ : Restriction n) (fuel : Nat)
    (hfuel : ρ.freeCount ≤ fuel) :
    ∀ β ∈ PDT.leaves (canonicalDT_CNF_aux F fuel ρ),
      IsConstantOn (evalCNF F) β := by
  induction fuel generalizing ρ with
  | zero =>
      unfold canonicalDT_CNF_aux
      intro β hβ
      cases hβ
      · have hzero : ρ.freeCount = 0 := Nat.eq_zero_of_le_zero hfuel
        have hconst := Restriction.isConstantOn_of_freeCount_eq_zero ρ (evalCNF F) hzero
        rw [Restriction.isConstantOn_iff] at hconst
        intro x y hx hy
        have hx_eq : ρ.restrict (evalCNF F) x = evalCNF F x :=
          Restriction.restrict_agree_of_compatible ρ _ (Restriction.compatible_iff.mpr hx)
        have hy_eq : ρ.restrict (evalCNF F) y = evalCNF F y :=
          Restriction.restrict_agree_of_compatible ρ _ (Restriction.compatible_iff.mpr hy)
        rw [← hx_eq, ← hy_eq]
        exact hconst x y
      · contradiction
  | succ fuel ih =>
      unfold canonicalDT_CNF_aux
      match hsel : Restriction.firstPendingClause? ρ F.clauses with
      | none =>
          simp only
          intro β hβ
          cases hβ
          · exact evalCNF_const_of_firstPending_none F ρ hsel
          · contradiction
      | some selection =>
          simp only
          intro β hβ
          simp only [PDT.leaves] at hβ
          rw [List.mem_append] at hβ
          rcases hβ with hβ | hβ
          · apply ih (ρ := _)
            · have h := @canonicalDT_CNF_aux_branch_freeCount n w F (Nat.succ fuel) ρ selection hsel
              rw [h.1]
              exact Nat.pred_le_pred hfuel
            · exact hβ
          · apply ih (ρ := _)
            · have h := @canonicalDT_CNF_aux_branch_freeCount n w F (Nat.succ fuel) ρ selection hsel
              rw [h.2]
              exact Nat.pred_le_pred hfuel
            · exact hβ

lemma canonicalDT_resolves
    {n w : Nat} (F : Core.CNF n w) (ρ : Restriction n) :
    ∀ β ∈ PDT.leaves (canonicalDT_CNF F ρ),
      IsConstantOn (evalCNF F) β := by
  unfold canonicalDT_CNF
  exact canonicalDT_CNF_aux_resolves F ρ ρ.freeCount (Nat.le_refl _)

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
      rw [PDT.mem_leaves_refine_iff] at hβ
      rcases hβ with ⟨γ, hγ, hβ_tail⟩
      have href : subcubeRefines β γ := canonicalCCDT_CNF_aux_leaves_refine_rho rest ⟨γ⟩ fuel β hβ_tail
      cases hg with
      | head =>
          have htrunk_resolves : IsConstantOn (evalCNF f) γ :=
             canonicalDT_CNF_aux_resolves f ρ fuel hfuel γ hγ
          exact isConstantOn_of_refines htrunk_resolves href
      | tail _ hg' =>
          have hfuel' : (Restriction.mk γ).freeCount ≤ fuel := by
             have href_rho := canonicalDT_CNF_aux_leaves_refine_rho f ρ fuel γ hγ
             have hle : (Restriction.mk γ).freeCount ≤ ρ.freeCount :=
               freeCount_le_of_subcubeRefines href_rho
             exact Nat.le_trans hle hfuel
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

/-!
### Relaxing and Mapping Leaves for PartialCertificate
-/

def relax (ρ : Restriction n) (β : Subcube n) : Subcube n :=
  fun i => if ρ.mask i = none then β i else none

def PDT.mapLeaves {n : Nat} (f : Subcube n → Subcube n) : PDT n → PDT n
| .leaf β => .leaf (f β)
| .node i t0 t1 => .node i (mapLeaves f t0) (mapLeaves f t1)

lemma PDT.depth_mapLeaves {n : Nat} (f : Subcube n → Subcube n) (t : PDT n) :
    (mapLeaves f t).depth = t.depth := by
  induction t <;> simp [mapLeaves, PDT.depth, *]

lemma PDT.leaves_mapLeaves {n : Nat} (f : Subcube n → Subcube n) (t : PDT n) :
    (mapLeaves f t).leaves = t.leaves.map f := by
  induction t <;> simp [mapLeaves, PDT.leaves, *]

lemma mem_relax_iff_mem_override {n : Nat} {ρ : Restriction n} {β : Subcube n}
    (h_ref : subcubeRefines β ρ.mask) (x : Core.BitVec n) :
    mem (relax ρ β) x ↔ mem β (ρ.override x) := by
  rw [mem_iff, mem_iff]
  constructor
  · intro h i b hb
    by_cases hfree : ρ.mask i = none
    · have hβ_relax : relax ρ β i = β i := by simp [relax, hfree]
      rw [← hβ_relax] at hb
      have hval := h i b hb
      simp [Restriction.override, hfree]
      exact hval
    · obtain ⟨v, hv⟩ := Restriction.mask_eq_some_of_not_none hfree
      have hβ_fixed : β i = some v := h_ref i v hv
      rw [hβ_fixed] at hb
      injection hb with hvb
      subst hvb
      simp [Restriction.override, hv]
  · intro h i b hb
    have hfree : ρ.mask i = none := by
      by_contra hfixed
      have : relax ρ β i = none := by simp [relax, hfixed]
      rw [this] at hb; contradiction
    have hβ_relax : relax ρ β i = β i := by simp [relax, hfree]
    rw [hβ_relax] at hb
    have hval := h i b hb
    simp [Restriction.override, hfree] at hval
    exact hval

theorem partialCertificate_from_good_restriction
    {n k t : Nat} (F : FormulaFamily n k)
    (ρ : Restriction n) (hgood : GoodFamilyCNF (F := F) t ρ) :
    ∃ (ℓ : Nat) (C : PartialCertificate n ℓ ((evalFamily F).map (ρ.restrict))),
      ℓ = 0 ∧ C.depthBound = F.length * t ∧
        C.epsilon = (1 : Q) / (n + 2) := by
  classical
  let tree := PDT.mapLeaves (relax ρ) (canonicalCCDT F ρ)
  let leaves := PDT.leaves tree
  let selectors (g : Core.BitVec n → Bool) : List (Subcube n) :=
    leaves.filter (fun β => g (witnessOf β))

  -- Key Lemma: f is constant on relaxed leaves
  have hconst : ∀ β ∈ PDT.leaves (canonicalCCDT F ρ),
      ∀ f ∈ F, IsConstantOn (ρ.restrict (evalCNF f)) (relax ρ β) := by
    intro β hβ f hf
    intro x y hx hy
    -- x ∈ relax ρ β means ρ.override x ∈ β
    -- y ∈ relax ρ β means ρ.override y ∈ β
    -- f is constant on β. So f(override x) = f(override y)
    have href : subcubeRefines β ρ.mask :=
      canonicalCCDT_CNF_aux_leaves_refine_rho F ρ ρ.freeCount β hβ
    have hx' := (mem_relax_iff_mem_override href x).1 hx
    have hy' := (mem_relax_iff_mem_override href y).1 hy
    have hres := canonicalCCDT_resolves F ρ β hβ f hf
    exact hres _ _ hx' hy'

  have h_leaves_cover : ∀ x, covered leaves x := by
    -- We need to prove that relaxed leaves cover the universe.
    -- This follows from canonicalCCDT leaves covering ρ.
    have h_canonical_cover : ∀ z, mem ρ.mask z → covered (PDT.leaves (canonicalCCDT F ρ)) z := by
      -- This requires a lemma: canonicalCCDT leaves cover ρ.
      -- Proving this by induction on F.
      sorry -- Standard property of canonicalDT construction (partitioning)

    intro x
    have h_override : mem ρ.mask (ρ.override x) := Restriction.override_mem ρ x
    have h_cov := h_canonical_cover (ρ.override x) h_override
    rcases h_cov with ⟨β, hβ, hmem⟩
    -- Show x ∈ relax ρ β
    refine ⟨relax ρ β, ?_, ?_⟩
    · simp [leaves, tree]; rw [PDT.leaves_mapLeaves]; exact List.mem_map_of_mem _ hβ
    · -- mem (relax ρ β) x <-> mem β (override x)
      -- This holds if β is compatible with override x (which it is, hmem).
      -- Proof:
      rw [mem_iff]
      intro i b hb
      have hrelax_def : relax ρ β i = if ρ.mask i = none then β i else none := rfl
      rw [hrelax_def] at hb
      split_ifs at hb with hfree
      · -- ρ i = none. β i = some b.
        -- mem β (override x) -> override x i = b.
        have hval := (mem_iff β (ρ.override x)).1 hmem i b hb
        simp [Restriction.override, hfree] at hval
        exact hval
      · contradiction

  have herr : ∀ g ∈ (evalFamily F).map (ρ.restrict), errU g (selectors g) = 0 := by
    intro g hg
    rcases List.mem_map.mp hg with ⟨f, hf, rfl⟩
    apply errU_eq_zero_of_agree
    intro x
    simp [coveredB]
    -- g x = true <-> coveredB selectors x = true
    constructor
    · intro hgx
      -- Find leaf covering x
      obtain ⟨L, hL_mem, hL_cov⟩ := h_leaves_cover x
      -- L is relaxed leaf.
      -- g is constant on L (hconst).
      -- g x = true. So g (witnessOf L) = true.
      -- So L ∈ selectors g.
      refine ⟨L, ?_, hL_cov⟩
      simp [selectors]
      refine ⟨hL_mem, ?_⟩
      -- g(witnessOf L) = g(x) = true.
      -- L comes from mapLeaves.
      -- hconst says g constant on relax ρ β.
      -- L is some relax ρ β.
      rcases List.mem_map.1 ((PDT.leaves_mapLeaves _ _).symm ▸ hL_mem) with ⟨β, hβ, rfl⟩
      have hconst_val := hconst β hβ f hf
      rw [← hconst_val (witnessOf (relax ρ β)) x (mem_witnessOf _) hL_cov]
      exact hgx
    · intro hcov
      rcases hcov with ⟨L, hL, hL_mem⟩
      -- L ∈ selectors -> g(witnessOf L) = true.
      simp [selectors] at hL
      rcases hL with ⟨hL_leaves, hL_val⟩
      -- g constant on L.
      rcases List.mem_map.1 ((PDT.leaves_mapLeaves _ _).symm ▸ hL_leaves) with ⟨β, hβ, rfl⟩
      have hconst_val := hconst β hβ f hf
      rw [hconst_val x (witnessOf (relax ρ β)) hL_mem (mem_witnessOf _)]
      exact hL_val

  refine ⟨0, {
    witness := PartialDT.ofPDT tree
    depthBound := F.length * t
    epsilon := (1 : Q) / (n + 2)
    trunk_depth_le := by
      simp [PartialDT.ofPDT]
      rw [PDT.depth_mapLeaves]
      exact canonicalCCDT_depth_le_sum_t F ρ hgood
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
      S.F = (evalFamily F).map (ρ.restrict) ∧ S.t = F.length * t ∧
        S.ε = (1 : Q) / (n + 2) := by
  obtain ⟨ℓ, C, hℓ, hdepth, hε⟩ :=
    partialCertificate_from_good_restriction (F := F) (ρ := ρ) hgood
  let S := C.toShrinkage
  refine ⟨S, ?_, ?_, ?_⟩
  · simp [S]
  · simp [S, hdepth, hℓ]
  · simp [S, hε]

