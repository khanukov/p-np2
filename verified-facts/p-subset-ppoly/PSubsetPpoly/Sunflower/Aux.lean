/-
  Auxiliary lemmas for the development of the sunflower lemma.
  These are kept separate so that the main file `Sunflower.lean`
  remains lightweight during compilation.
-/

import PSubsetPpoly.Sunflower.Sunflower

-- Disable `unnecessarySimpa` warnings in this auxiliary file:
set_option linter.unnecessarySimpa false

open Classical Finset
open scoped BigOperators

namespace Sunflower

variable {α : Type} [DecidableEq α]

/--
  Sum of slice cardinalities over an arbitrary subset.
  This is a generalisation of `sum_card_slices_eq_w_mul_card` where we
  do not assume uniformity and restrict the sum to a set `U`.
-/
lemma sum_slice_inter (𝓢 : Finset (Finset α)) (U : Finset α) :
    ∑ x ∈ U, (slice 𝓢 x).card = ∑ A ∈ 𝓢, (A ∩ U).card := by
  classical
  -- As in `sum_card_slices_eq_w_mul_card`, expand each slice via indicators.
  have h1 :
      ∑ x ∈ U, (slice 𝓢 x).card
        = ∑ x ∈ U, ∑ A ∈ 𝓢, (if x ∈ A then (1 : ℕ) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    -- Cardinality of a filtered family expressed as a sum over `𝓢`.
    simpa [slice] using
      (Finset.card_filter (s := 𝓢) (p := fun A => x ∈ A))

  -- Swap the order of summation using a Cartesian-product reindexing.
  have h2 :
      ∑ x ∈ U, ∑ A ∈ 𝓢, (if x ∈ A then (1 : ℕ) else 0)
        = ∑ A ∈ 𝓢, ∑ x ∈ U, (if x ∈ A then (1 : ℕ) else 0) := by
    have hL :
        ∑ x ∈ U, ∑ A ∈ 𝓢, (if x ∈ A then (1 : ℕ) else 0)
          = ∑ p ∈ U.product 𝓢, (if p.1 ∈ p.2 then (1 : ℕ) else 0) := by
      simpa using
        (Finset.sum_product
          (s := U) (t := 𝓢)
          (f := fun p : α × Finset α =>
              (if p.1 ∈ p.2 then (1 : ℕ) else 0))).symm
    have hR :
        ∑ p ∈ U.product 𝓢, (if p.1 ∈ p.2 then (1 : ℕ) else 0)
          = ∑ A ∈ 𝓢, ∑ x ∈ U, (if x ∈ A then (1 : ℕ) else 0) := by
      simpa using
        (Finset.sum_product_right
          (s := U) (t := 𝓢)
          (f := fun p : α × Finset α =>
              (if p.1 ∈ p.2 then (1 : ℕ) else 0)))
    exact hL.trans hR

  -- The inner sum over `x` reduces to the size of `A ∩ U`.
  have h3 :
      ∀ {A}, A ∈ 𝓢 →
        ∑ x ∈ U, (if x ∈ A then (1 : ℕ) else 0) = (A ∩ U).card := by
    intro A hA
    have hsum :
        ∑ x ∈ U, (if x ∈ A then (1 : ℕ) else 0)
          = ∑ x ∈ U.filter (fun x => x ∈ A), (1 : ℕ) := by
      simpa [Finset.sum_filter] using
        (Finset.sum_filter
          (s := U) (p := fun x => x ∈ A)
          (f := fun _ : α => (1 : ℕ))).symm
    have hfilter :
        U.filter (fun x => x ∈ A) = A ∩ U := by
      apply Finset.ext; intro x; constructor
      · intro hx
        rcases Finset.mem_filter.mp hx with ⟨hxU, hxA⟩
        exact Finset.mem_inter.mpr ⟨hxA, hxU⟩
      · intro hx
        rcases Finset.mem_inter.mp hx with ⟨hxA, hxU⟩
        exact Finset.mem_filter.mpr ⟨hxU, hxA⟩
    calc
      ∑ x ∈ U, (if x ∈ A then (1 : ℕ) else 0)
          = ∑ x ∈ U.filter (fun x => x ∈ A), (1 : ℕ) := hsum
      _ = (U.filter (fun x => x ∈ A)).card := by
            simpa using
              (Finset.card_eq_sum_ones (s := U.filter (fun x => x ∈ A))).symm
      _ = (A ∩ U).card := by simpa [hfilter]

  -- Assemble the pieces.
  calc
    ∑ x ∈ U, (slice 𝓢 x).card
        = ∑ x ∈ U, ∑ A ∈ 𝓢, (if x ∈ A then (1 : ℕ) else 0) := h1
    _ = ∑ A ∈ 𝓢, ∑ x ∈ U, (if x ∈ A then (1 : ℕ) else 0) := h2
    _ = ∑ A ∈ 𝓢, (A ∩ U).card := by
          apply Finset.sum_congr rfl
          intro A hA
          exact h3 hA

/--
  Existence of a maximal pairwise-disjoint subfamily of `𝓢`.
  We obtain a subfamily `T` whose cardinality dominates all disjoint
  subfamilies of `𝓢`.  The construction uses `powerset.filter` together
  with `Finset.exists_max_image` applied to the cardinality function.
-/
lemma exists_max_pairwiseDisjoint_subset (𝓢 : Finset (Finset α)) :
    ∃ T ⊆ 𝓢, pairwiseDisjoint T ∧
      ∀ U ⊆ 𝓢, pairwiseDisjoint U → U.card ≤ T.card := by
  classical
  -- Consider the finite set of pairwise-disjoint subfamilies of `𝓢`.
  let 𝒟 :=
    𝓢.powerset.filter (fun T : Finset (Finset α) => pairwiseDisjoint T)
  have h𝒟_nonempty : 𝒟.Nonempty := by
    refine ⟨∅, ?_⟩
    have hsubset : (∅ : Finset (Finset α)) ⊆ 𝓢 := by intro A hA; cases hA
    have hdisj_empty : pairwiseDisjoint (∅ : Finset (Finset α)) := by
      intro A hA B hB hAB; cases hA
    exact Finset.mem_filter.mpr
      ⟨by simpa using Finset.mem_powerset.mpr hsubset, hdisj_empty⟩

  -- Choose a maximal element of `𝒟` with respect to cardinality.
  obtain ⟨T, hTmem, hTmax⟩ :=
    Finset.exists_max_image (s := 𝒟)
      (f := fun T : Finset (Finset α) => T.card) h𝒟_nonempty

  -- Unpack the membership information.
  have hTsub : T ⊆ 𝓢 :=
    by
      have h := (Finset.mem_filter.mp hTmem).1
      exact Finset.mem_powerset.mp h
  have hTdisj : pairwiseDisjoint T :=
    (Finset.mem_filter.mp hTmem).2

  -- Translate maximality into the desired statement.
  refine ⟨T, hTsub, hTdisj, ?_⟩
  intro U hUsub hUdisj
  have hUmem : U ∈ 𝒟 := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hUsub, hUdisj⟩
  exact hTmax U hUmem

/--
  A maximal pairwise-disjoint subfamily intersects every set in the
  ambient family.  Otherwise we could enlarge it by adding a disjoint
  set, contradicting maximality.  We assume here that all sets under
  consideration are nonempty; this hypothesis is satisfied in the
  sunflower application, where all petals have positive width.
-/
lemma maximal_disjoint_hits_union
    {𝓢 T : Finset (Finset α)}
    (hTsub : T ⊆ 𝓢)
    (hdisj : pairwiseDisjoint T)
    (hmax : ∀ U ⊆ 𝓢, pairwiseDisjoint U → U.card ≤ T.card)
    {A : Finset α} (hA : A ∈ 𝓢) (hAne : A.Nonempty) :
    (A ∩ T.unions).Nonempty := by
  classical
  -- Suppose for contradiction that `A` avoids the union of `T`.
  by_contra hEmpty
  -- The intersection must be empty, otherwise we contradict `hEmpty`.
  have hUnionEmpty : A ∩ T.unions = (∅ : Finset α) := by
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    exact hEmpty ⟨x, hx⟩

  -- In particular, `A` does not belong to `T`.
  have hA_notin : A ∉ T := by
    intro hAin
    rcases hAne with ⟨x, hx⟩
    have hxU : x ∈ T.unions :=
      Finset.mem_unions.mpr ⟨A, hAin, hx⟩
    have : (A ∩ T.unions).Nonempty :=
      ⟨x, Finset.mem_inter.mpr ⟨hx, hxU⟩⟩
    exact hEmpty this

  -- `A` is disjoint from every member of `T`.
  have hA_disj : ∀ B ∈ T, A ∩ B = (∅ : Finset α) := by
    intro B hB
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hxA, hxB⟩
    -- `x` lies in the union, contradicting `hUnionEmpty`.
    have hxU : x ∈ T.unions :=
      Finset.mem_unions.mpr ⟨B, hB, hxB⟩
    have hxAU : x ∈ A ∩ T.unions :=
      Finset.mem_inter.mpr ⟨hxA, hxU⟩
    have hFalse : False := by
      have : x ∈ (∅ : Finset α) := by simpa [hUnionEmpty] using hxAU
      exact Finset.notMem_empty _ this
    exact hFalse

  -- The enlarged family `insert A T` is still pairwise disjoint.
  have hdisj_insert : pairwiseDisjoint (insert A T) := by
    intro X hX Y hY hXY
    rcases Finset.mem_insert.mp hX with hXA | hXT
    · subst hXA
      rcases Finset.mem_insert.mp hY with hYA | hYT
      · subst hYA
        exact (hXY rfl).elim
      · exact hA_disj _ hYT
    · rcases Finset.mem_insert.mp hY with hYA | hYT
      · subst hYA
        have hAX := hA_disj X hXT
        simpa [Finset.inter_comm] using hAX
      · exact hdisj hXT hYT hXY

  -- It is a larger disjoint subfamily of `𝓢`, contradicting maximality.
  have hsub_insert : insert A T ⊆ 𝓢 := by
    intro B hB
    rcases Finset.mem_insert.mp hB with hBA | hBT
    · subst hBA; exact hA
    · exact hTsub hBT
  have hcard_le := hmax (insert A T) hsub_insert hdisj_insert
  have hcard_insert :
      (insert A T).card = T.card + 1 :=
    by simpa [Finset.card_insert_of_notMem hA_notin]
  have hcontr : T.card + 1 ≤ T.card := by
    simpa [hcard_insert, Nat.add_comm] using hcard_le
  have hlt : T.card < T.card :=
    lt_of_lt_of_le (Nat.lt_succ_self _) hcontr
  exact (Nat.lt_irrefl _ hlt)

end Sunflower

