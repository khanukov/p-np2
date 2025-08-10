--
--  Pnp2/Sunflower/Sunflower.lean
--
--  Classical sunflower lemma: axiomatized with the standard threshold
--  `(p - 1)^w * w!`.  We provide the basic definitions together with a
--  direct proof for the two-petal case; the general combinatorial lemma
--  is recorded as an axiom for now.
--
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Card
import Pnp2.Boolcube

open Classical Finset
open scoped BigOperators

set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

noncomputable section

/- Auxiliary namespace: we rebuild `Finset.unions` which is no longer
   present in `mathlib`.  It is defined as the supremum (union) of all
   members of a finite family.  We keep it outside of the `Sunflower`
   namespace so that it is available globally. -/
namespace Finset

variable {α : Type} [DecidableEq α]

/-- Union of all sets in a finite family. -/
def unions (𝓢 : Finset (Finset α)) : Finset α :=
  𝓢.sup id

@[simp] lemma mem_unions {𝓢 : Finset (Finset α)} {x : α} :
    x ∈ 𝓢.unions ↔ ∃ A ∈ 𝓢, x ∈ A := by
  unfold unions
  -- `mem_sup` characterises membership in the supremum
  simpa using (Finset.mem_sup (s := 𝓢) (f := id) (a := x))

end Finset

namespace Sunflower

variable {α : Type} [DecidableEq α]

/-- A `p`-sunflower inside a family `𝓢` consists of a subfamily `𝓣` of
cardinality `p` whose pairwise intersections all coincide with a set
`core`. -/
structure IsSunflower (p : ℕ) (𝓣 : Finset (Finset α)) (core : Finset α) : Prop where
  card_p : 𝓣.card = p
  pairwise_inter :
    ∀ ⦃A⦄, A ∈ 𝓣 → ∀ ⦃B⦄, B ∈ 𝓣 → A ≠ B → A ∩ B = core

/-- A family `𝓢` has a `p`-sunflower of width `w` if it contains a
subfamily with the sunflower property and all petals have size `w`. -/
def HasSunflower (𝓢 : Finset (Finset α)) (w p : ℕ) : Prop :=
  ∃ 𝓣 ⊆ 𝓢, ∃ core, IsSunflower (α := α) p 𝓣 core ∧ ∀ A ∈ 𝓣, A.card = w

/-! ### Slices and erase-by-element infrastructure -/

/-- `slice 𝓢 x` is the subfamily of sets from `𝓢` that contain `x`. -/
def slice (𝓢 : Finset (Finset α)) (x : α) : Finset (Finset α) :=
  𝓢.filter (fun A => x ∈ A)

lemma mem_slice {𝓢 : Finset (Finset α)} {x : α} {A : Finset α} :
    A ∈ slice 𝓢 x ↔ (A ∈ 𝓢 ∧ x ∈ A) := by
  simp [slice]

/-- `eraseSlice 𝓢 x` is obtained from `slice 𝓢 x` by removing `x` from each set. -/
def eraseSlice (𝓢 : Finset (Finset α)) (x : α) : Finset (Finset α) :=
  (slice 𝓢 x).image (fun A => A.erase x)

/-- If `x ∈ A` and `x ∈ B` and the erasures coincide, then the original
sets coincide as well. -/
lemma erase_inj_of_mem {x : α} {A B : Finset α}
    (hxA : x ∈ A) (hxB : x ∈ B) :
    A.erase x = B.erase x → A = B := by
  intro h
  have := congrArg (fun (S : Finset α) => insert x S) h
  simpa [insert_erase hxA, insert_erase hxB] using this

/-- On the slice `𝓢.filter (· ∋ x)` the map `erase x` is injective. -/
lemma erase_injective_on_slice (𝓢 : Finset (Finset α)) (x : α) :
    Set.InjOn (fun A : Finset α => A.erase x) {A | A ∈ slice 𝓢 x} := by
  intro A hA B hB h
  exact erase_inj_of_mem
    (by
      have := (mem_slice.mp hA).2
      simpa using this)
    (by
      have := (mem_slice.mp hB).2
      simpa using this) h

/-- The cardinalities of `slice 𝓢 x` and `eraseSlice 𝓢 x` agree. -/
lemma card_eraseSlice (𝓢 : Finset (Finset α)) (x : α) :
    (eraseSlice 𝓢 x).card = (slice 𝓢 x).card := by
  classical
  have hinj : Set.InjOn (fun A : Finset α => A.erase x) {A | A ∈ slice 𝓢 x} :=
    erase_injective_on_slice 𝓢 x
  simpa [eraseSlice] using
    Finset.card_image_of_injOn (s := slice 𝓢 x)
      (f := fun A : Finset α => A.erase x) hinj

/-- In a uniform family of positive width, removing a point lowers the
cardinality by one. -/
lemma card_erase_of_uniform
    {𝓢 : Finset (Finset α)} {w : ℕ}
    (hunif : ∀ A ∈ 𝓢, A.card = w) (hw : 0 < w)
    {x : α} {A : Finset α} (hA : A ∈ 𝓢) (hx : x ∈ A) :
    (A.erase x).card = w - 1 := by
  have := hunif A hA
  simpa [Finset.card_erase_of_mem hx, this]

/-! ### Double counting: sum of slice sizes -/

/-- In a `w`-uniform family the sum of the cardinalities of all slices
    equals `w` times the size of the family.  This is the key combinatorial
    fact behind the classical sunflower bound. -/
lemma sum_card_slices_eq_w_mul_card
    (𝓢 : Finset (Finset α)) (w : ℕ)
    (h_w : ∀ A ∈ 𝓢, A.card = w) :
    ∑ x ∈ 𝓢.unions, (slice 𝓢 x).card = w * 𝓢.card := by
  classical
  -- rewrite each slice cardinality via indicators over `𝓢`
  have h1 :
      ∑ x ∈ 𝓢.unions, (slice 𝓢 x).card
        = ∑ x ∈ 𝓢.unions, ∑ A ∈ 𝓢, (if x ∈ A then (1 : ℕ) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    -- `card (S.filter p) = ∑ A∈S, if p A then 1 else 0`
    simpa [slice] using
      (Finset.card_filter (s := 𝓢) (p := fun A => x ∈ A))

  -- swap the summations via a Cartesian-product reindexing
  have h2 :
      ∑ x ∈ 𝓢.unions, ∑ A ∈ 𝓢, (if x ∈ A then (1 : ℕ) else 0)
        = ∑ A ∈ 𝓢, ∑ x ∈ 𝓢.unions, (if x ∈ A then (1 : ℕ) else 0) := by
    classical
    -- Both nested sums can be expressed as a single sum over `𝓢.unions ×ˢ 𝓢`.
    have hL :
        ∑ x ∈ 𝓢.unions, ∑ A ∈ 𝓢, (if x ∈ A then (1 : ℕ) else 0)
          = ∑ p ∈ 𝓢.unions.product 𝓢,
              (if p.1 ∈ p.2 then (1 : ℕ) else 0) := by
      -- `sum_product` rewrites the nested sum to a sum over the product.
      simpa using
        (Finset.sum_product
          (s := 𝓢.unions) (t := 𝓢)
          (f := fun p : α × Finset α =>
              (if p.1 ∈ p.2 then (1 : ℕ) else 0))).symm
    have hR :
        ∑ p ∈ 𝓢.unions.product 𝓢,
            (if p.1 ∈ p.2 then (1 : ℕ) else 0)
          = ∑ A ∈ 𝓢, ∑ x ∈ 𝓢.unions,
              (if x ∈ A then (1 : ℕ) else 0) := by
      -- `sum_product_right` performs the reverse conversion.
      simpa using
        (Finset.sum_product_right
          (s := 𝓢.unions) (t := 𝓢)
          (f := fun p : α × Finset α =>
              (if p.1 ∈ p.2 then (1 : ℕ) else 0)))
    exact hL.trans hR

  -- inner sum over x reduces to the size of A
  have h3 :
      ∀ {A}, A ∈ 𝓢 →
        ∑ x ∈ 𝓢.unions, (if x ∈ A then (1 : ℕ) else 0) = A.card := by
    intro A hA
    -- restrict sum to elements of A
    have := (Finset.sum_filter
      (s := 𝓢.unions) (p := fun x => x ∈ A)
      (f := fun _ : α => (1 : ℕ))).symm
    have hfilter :
        (𝓢.unions.filter (fun x => x ∈ A)) = A := by
      -- since `A ⊆ 𝓢.unions`
      apply Finset.ext; intro x; constructor
      · intro hx; exact (Finset.mem_filter.mp hx).2
      · intro hxA
        have hxU : x ∈ 𝓢.unions := by
          exact Finset.mem_unions.mpr ⟨A, hA, hxA⟩
        exact Finset.mem_filter.mpr ⟨hxU, hxA⟩
    have : ∑ x ∈ 𝓢.unions, (if x ∈ A then (1 : ℕ) else 0)
            = ∑ x ∈ (𝓢.unions.filter (fun x => x ∈ A)), (1 : ℕ) := by
      simpa [Finset.sum_filter] using this
    simpa [hfilter] using this

  -- assemble the pieces
  calc
    ∑ x ∈ 𝓢.unions, (slice 𝓢 x).card
        = ∑ x ∈ 𝓢.unions, ∑ A ∈ 𝓢, (if x ∈ A then (1 : ℕ) else 0) := h1
    _ = ∑ A ∈ 𝓢, ∑ x ∈ 𝓢.unions, (if x ∈ A then (1 : ℕ) else 0) := h2
    _ = ∑ A ∈ 𝓢, A.card := by
          apply Finset.sum_congr rfl
          intro A hA; simp [h3 hA]
    _ = ∑ A ∈ 𝓢, w := by
          apply Finset.sum_congr rfl
          intro A hA; simp [h_w A hA]
    _ = w * 𝓢.card := by
          -- sum of a constant over `𝓢`
          simpa [Finset.sum_const, nsmul_eq_mul, Nat.mul_comm]

/-! ### Iterated element erasure -/

/-- `familyAfter 𝓢 xs` iteratively removes each element of the list `xs`
    from all members of the family `𝓢`.  The elements are removed in order,
    so `familyAfter 𝓢 [] = 𝓢` and `familyAfter 𝓢 (x :: xs)` first processes
    the tail `xs` and then erases `x` from every set. -/
def familyAfter : Finset (Finset α) → List α → Finset (Finset α)
  | 𝓢, []      => 𝓢
  | 𝓢, x :: xs => eraseSlice (familyAfter 𝓢 xs) x

/-- In a `w`-uniform family, iteratively erasing a list of elements of length
    `xs.length` lowers the size of each set precisely by that length. -/
lemma familyAfter_uniform
    {𝓢 : Finset (Finset α)} {w : ℕ}
    (hunif : ∀ A ∈ 𝓢, A.card = w)
    (xs : List α) :
    ∀ A ∈ familyAfter 𝓢 xs, A.card = w - xs.length := by
  classical
  -- Induction on the list of elements being erased
  induction xs with
  | nil =>
      -- No erasures: the family remains uniform of width `w`
      intro A hA; simpa using hunif A hA
  | cons x xs ih =>
      intro A hA
      -- Membership in `familyAfter` is membership in an erased slice
      -- of the family obtained after processing `xs`.
      have hA' : A ∈ eraseSlice (familyAfter 𝓢 xs) x := hA
      -- Unpack the membership in `eraseSlice` via the image description.
      rcases Finset.mem_image.mp hA' with ⟨B, hB, rfl⟩
      rcases mem_slice.mp hB with ⟨hB_in, hxB⟩
      -- Apply the inductive hypothesis to the preimage set `B`.
      have hBcard : B.card = w - xs.length := ih B hB_in
      -- Removing `x` lowers the cardinality by one.
      have := Finset.card_erase_of_mem hxB
      -- Rewrite the right-hand side using the inductive hypothesis.
      simpa [hBcard, Nat.sub_sub, List.length] using this

/-! ### Lifting a sunflower from a slice back to the original family -/

/-- If `eraseSlice 𝓢 x` contains a `p`-sunflower with core `C`, then the
original family `𝓢` contains a `p`-sunflower with core `insert x C`. -/
lemma lift_sunflower
    (𝓢 : Finset (Finset α)) {w p : ℕ} {x : α}
    (hunif : ∀ A ∈ 𝓢, A.card = w) (hw : 0 < w)
    {𝓣 : Finset (Finset α)} {C : Finset α}
    (hTsub : 𝓣 ⊆ eraseSlice 𝓢 x)
    (hSun : IsSunflower (α := α) p 𝓣 C) :
    ∃ 𝓣' ⊆ 𝓢, IsSunflower (α := α) p 𝓣' (insert x C) ∧
      (∀ A ∈ 𝓣', A.card = w) := by
  classical
  -- Image of `𝓣` under inserting `x` back.
  let 𝓣' := 𝓣.image (fun B => insert x B)
  have hT'sub : 𝓣' ⊆ 𝓢 := by
    intro X hX
    rcases Finset.mem_image.mp hX with ⟨B, hB, rfl⟩
    rcases Finset.mem_image.mp (by simpa [eraseSlice] using hTsub hB) with ⟨A, hAin, hAeq⟩
    rcases mem_slice.mp hAin with ⟨hA𝓢, hxA⟩
    have hXB : insert x B = A := by
      have := insert_erase hxA
      simpa [hAeq] using this
    simpa [hXB] using hA𝓢
  have hcards : ∀ A ∈ 𝓣', A.card = w := by
    intro A hA
    rcases Finset.mem_image.mp hA with ⟨B, hB, rfl⟩
    rcases Finset.mem_image.mp (by simpa [eraseSlice] using hTsub hB) with ⟨S, hSin, hSeq⟩
    rcases mem_slice.mp hSin with ⟨hS𝓢, hxS⟩
    have hXB : insert x B = S := by
      have := insert_erase hxS
      simpa [hSeq] using this
    simpa [hXB] using (hunif S hS𝓢)
  -- cardinalities of `𝓣` and `𝓣'` coincide
  have hcard : 𝓣'.card = 𝓣.card := by
    classical
    -- The map `B ↦ insert x B` is injective on `𝓣` since every `B` misses `x`.
    have hinj : Set.InjOn (fun B : Finset α => insert x B) {B | B ∈ 𝓣} := by
      intro B₁ hB₁ B₂ hB₂ hEq
      -- show `x ∉ B₁` and `x ∉ B₂`
      have hx₁ : x ∉ B₁ := by
        have := hTsub hB₁
        rcases Finset.mem_image.mp (by simpa [eraseSlice] using this) with ⟨S, hSin, hSeq⟩
        rcases mem_slice.mp hSin with ⟨_, hxS⟩
        have : x ∉ S.erase x := by simp
        simpa [hSeq] using this
      have hx₂ : x ∉ B₂ := by
        have := hTsub hB₂
        rcases Finset.mem_image.mp (by simpa [eraseSlice] using this) with ⟨S, hSin, hSeq⟩
        rcases mem_slice.mp hSin with ⟨_, hxS⟩
        have : x ∉ S.erase x := by simp
        simpa [hSeq] using this
      -- erasing `x` from both sides yields equality of the original sets
      have hEq' := congrArg (fun s => s.erase x) hEq
      simpa [Finset.erase_insert, hx₁, hx₂] using hEq'
    simpa [𝓣'] using
      Finset.card_image_of_injOn (s := 𝓣)
        (f := fun B : Finset α => insert x B) hinj
  have pairwise_lift :
      ∀ ⦃A⦄, A ∈ 𝓣' → ∀ ⦃B⦄, B ∈ 𝓣' → A ≠ B → A ∩ B = insert x C := by
    intro A hA B hB hAB
    rcases Finset.mem_image.mp hA with ⟨A', hA', rfl⟩
    rcases Finset.mem_image.mp hB with ⟨B', hB', rfl⟩
    -- `x` is not in `A'` or `B'` since they arise from erasures.
    have hxA' : x ∉ A' := by
      rcases Finset.mem_image.mp (by simpa [eraseSlice] using hTsub hA') with ⟨S, hSin, hSeq⟩
      rcases mem_slice.mp hSin with ⟨_, hxS⟩
      have : x ∉ S.erase x := by simp
      simpa [hSeq] using this
    have hxB' : x ∉ B' := by
      rcases Finset.mem_image.mp (by simpa [eraseSlice] using hTsub hB') with ⟨S, hSin, hSeq⟩
      rcases mem_slice.mp hSin with ⟨_, hxS⟩
      have : x ∉ S.erase x := by simp
      simpa [hSeq] using this
    -- Intersections of inserted sets.
    have inter_lift :
        (insert x A') ∩ (insert x B') = insert x (A' ∩ B') := by
      ext y; constructor <;> intro hy
      · rcases Finset.mem_inter.mp hy with ⟨hy1, hy2⟩
        by_cases hyx : y = x
        · subst hyx; simp
        ·
          have hyA' : y ∈ A' := by simpa [Finset.mem_insert, hyx] using hy1
          have hyB' : y ∈ B' := by simpa [Finset.mem_insert, hyx] using hy2
          have hmem : y ∈ A' ∩ B' := by
            exact Finset.mem_inter.mpr ⟨hyA', hyB'⟩
          simp [Finset.mem_insert, hyx, hmem]
      · rcases Finset.mem_insert.mp hy with hyx | hy'
        · subst hyx; simp
        · rcases Finset.mem_inter.mp hy' with ⟨hyA', hyB'⟩
          have hyA'' : y ∈ insert x A' := by
            have : y = x ∨ y ∈ A' := Or.inr hyA'
            simpa [Finset.mem_insert, hxA'] using this
          have hyB'' : y ∈ insert x B' := by
            have : y = x ∨ y ∈ B' := Or.inr hyB'
            simpa [Finset.mem_insert, hxB'] using this
          exact Finset.mem_inter.mpr ⟨hyA'', hyB''⟩
    have hAB' : A' ≠ B' := by
      intro h; exact hAB (by simpa [h])
    have hcore := hSun.pairwise_inter (A := A') hA' (B := B') hB' hAB'
    simpa [inter_lift, hcore]
  refine ⟨𝓣', hT'sub, ?_, hcards⟩
  refine ⟨?_, ?_⟩
  · -- cardinality of the lifted sunflower
    have : 𝓣.card = p := hSun.card_p
    simpa [hcard, this]
  · intro A hA B hB hAB; exact pairwise_lift hA hB hAB

/-! ### Two petals: explicit proof -/
/-- For two petals the sunflower lemma becomes completely elementary: any
family containing at least two sets already forms a `2`-sunflower.  We
record this special case with a direct proof so that small instances do
not depend on the general combinatorial argument. -/
lemma sunflower_exists_two
    (𝓢 : Finset (Finset α)) (w : ℕ) (hw : 0 < w)
    (h_large : 1 < 𝓢.card)
    (h_w : ∀ A ∈ 𝓢, A.card = w) :
    HasSunflower 𝓢 w 2 := by
  classical
  -- Choose two distinct members of the family.
  have hpos : 0 < 𝓢.card := lt_trans Nat.zero_lt_one h_large
  obtain ⟨A, hA⟩ := Finset.card_pos.mp hpos
  obtain ⟨B, hB, hAB⟩ := Finset.exists_ne_of_one_lt_card h_large A
  -- The petals of the sunflower are the two chosen sets.
  refine ⟨{A, B}, ?_, ?_⟩
  · intro X hX
    have hx : X = A ∨ X = B := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using hX
    cases hx with
    | inl hXA => simpa [hXA] using hA
    | inr hXB => simpa [hXB] using hB
  · refine ⟨A ∩ B, ?_, ?_⟩
    · -- Proof of the sunflower structure.
      have hA_notB : A ∉ ({B} : Finset (Finset α)) := by
        simpa [Finset.mem_singleton] using hAB.symm
      refine ⟨by
        simpa [Finset.card_singleton, hA_notB] using
          (Finset.card_insert_of_notMem hA_notB), ?_⟩
      -- The pairwise intersection property is immediate.
      intro X hX Y hY hXY
      have hX' : X = A ∨ X = B := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hX
      have hY' : Y = A ∨ Y = B := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hY
      cases hX' with
      | inl hx =>
          cases hY' with
          | inl hy => cases hXY (by simpa [hx, hy])
          | inr hy => simpa [hx, hy, Finset.inter_comm]
      | inr hx =>
          cases hY' with
          | inl hy => simpa [hx, hy, Finset.inter_comm]
          | inr hy => cases hXY (by simpa [hx, hy])
    · -- Finally each petal has cardinality `w`.
      intro X hX
      have hx : X = A ∨ X = B := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hX
      cases hx with
      | inl hx => simpa [hx] using h_w A hA
      | inr hx => simpa [hx] using h_w B hB

/-! ### Classical sunflower lemma (axiomatized) -/

/-- **Erdős–Rado sunflower lemma** (axiom).  If a finite family of
`w`-sets has more than `(p - 1)^w * w!` members, then it contains a
`p`-sunflower.  A complete combinatorial proof will be provided in a
future revision. -/
axiom sunflower_exists_classic
    (𝓢 : Finset (Finset α)) (w p : ℕ) (hw : 0 < w) (hp : 2 ≤ p)
    (h_size : (p - 1) ^ w * Nat.factorial w < 𝓢.card)
    (h_w : ∀ A ∈ 𝓢, A.card = w) :
    HasSunflower 𝓢 w p

/-- Convenient wrapper for the sunflower lemma when the family is
already known to consist of `w`-sets. -/
lemma sunflower_exists_of_fixedSize
    (𝓢 : Finset (Finset α)) (w p : ℕ) (hw : 0 < w) (hp : 2 ≤ p)
    (h_cards : ∀ A ∈ 𝓢, A.card = w)
    (h_big  : 𝓢.card > (p - 1) ^ w * Nat.factorial w) :
    HasSunflower 𝓢 w p :=
  sunflower_exists_classic 𝓢 w p hw hp
    (by simpa using h_big) h_cards

/-! ## Structures for the cover algorithm -/

open Boolcube

abbrev Petal (n : ℕ) := Finset (Fin n)

/-- Data of a sunflower family in the Boolean cube. -/
structure SunflowerFam (n t : ℕ) where
  petals : Finset (Petal n)
  tsize  : petals.card = t
  core   : Petal n
  sub_core : ∀ P ∈ petals, core ⊆ P
  pairwise_core :
    ∀ P₁ ∈ petals, ∀ P₂ ∈ petals, P₁ ≠ P₂ → P₁ ∩ P₂ = core

namespace SunflowerFam

variable {n w t : ℕ}

/-- From a sufficiently large family of `w`-subsets we can extract a
`t`-sunflower.  This is a thin wrapper around the classical lemma above
adapted to the `SunflowerFam` structure. -/
lemma exists_of_large_family_classic
    {F : Finset (Petal n)}
    (hw : 0 < w) (ht : 2 ≤ t)
    (hcard : ∀ S ∈ F, S.card = w)
    (hbig : F.card > (t - 1) ^ w * Nat.factorial w) :
    ∃ S : SunflowerFam n t, S.petals ⊆ F := by
  classical
  -- obtain the abstract sunflower using the axiom
  have hsun : HasSunflower (α := Fin n) F w t :=
    sunflower_exists_classic (𝓢 := F) (w := w) (p := t) hw ht hbig hcard
  rcases hsun with ⟨pet, hsub, core, hSun, hcards⟩
  rcases hSun with ⟨hsize, hpair⟩
  -- show the core is contained in every petal
  have hsub_core : ∀ P ∈ pet, core ⊆ P := by
    intro P hP
    have h_two : 1 < pet.card := by
      have : 2 ≤ pet.card := by simpa [hsize] using ht
      exact lt_of_lt_of_le (by decide : 1 < 2) this
    obtain ⟨Q, hQ, hne⟩ := Finset.exists_ne_of_one_lt_card h_two P
    have hPQ := hpair (A := P) hP (B := Q) hQ (Ne.symm hne)
    simpa [hPQ] using (Finset.inter_subset_left : P ∩ Q ⊆ P)
  refine ⟨⟨pet, hsize, core, hsub_core, ?_⟩, hsub⟩
  intro P₁ h₁ P₂ h₂ hne
  exact hpair (A := P₁) h₁ (B := P₂) h₂ hne

/-! ### Auxiliary facts about sunflower families -/

lemma petals_nonempty {S : SunflowerFam n t} (ht : 0 < t) :
    S.petals.Nonempty := by
  rw [← Finset.card_pos]
  rw [S.tsize]
  exact ht

/-- If a sunflower family contains two distinct petals of equal
cardinality, then the core is strictly smaller than each of those petals. -/
lemma core_card_lt_of_two_petals {S : SunflowerFam n t}
    {P₁ P₂ : Petal n} (h₁ : P₁ ∈ S.petals) (h₂ : P₂ ∈ S.petals)
    (hcard : P₂.card = P₁.card) (hne : P₁ ≠ P₂) :
    S.core.card < P₁.card := by
  classical
  have hsub : S.core ⊆ P₁ := S.sub_core _ h₁
  have hle : S.core.card ≤ P₁.card := Finset.card_le_card hsub
  have hneq : S.core.card ≠ P₁.card := by
    intro hEq
    have hcore_eq : S.core = P₁ :=
      Finset.eq_of_subset_of_card_le hsub (by simpa [hEq])
    have hsubset : P₁ ⊆ P₂ := by
      have htmp : P₁ ∩ P₂ = P₁ := by
        simpa [hcore_eq] using S.pairwise_core P₁ h₁ P₂ h₂ hne
      have hsubset_inter : P₁ ∩ P₂ ⊆ P₂ := Finset.inter_subset_right
      simpa [htmp] using hsubset_inter
    have hcardle : P₂.card ≤ P₁.card := by simpa [hcard]
    have : P₁ = P₂ := Finset.eq_of_subset_of_card_le hsubset hcardle
    exact hne this
  exact lt_of_le_of_ne hle hneq

/-- Reformulation of the previous lemma as a strict subset. -/
lemma core_ssubset_of_two_petals {S : SunflowerFam n t}
    {P₁ P₂ : Petal n} (h₁ : P₁ ∈ S.petals) (h₂ : P₂ ∈ S.petals)
    (hcard : P₂.card = P₁.card) (hne : P₁ ≠ P₂) :
    S.core ⊂ P₁ := by
  classical
  have hsub : S.core ⊆ P₁ := S.sub_core _ h₁
  have hneq : S.core ≠ P₁ := by
    intro hEq
    have hlt := core_card_lt_of_two_petals (S := S)
      (P₁ := P₁) (P₂ := P₂) h₁ h₂ hcard hne
    simpa [hEq] using hlt
  exact (Finset.ssubset_iff_subset_ne).2 ⟨hsub, hneq⟩

/-- If a sunflower family contains two distinct petals of equal
cardinality, there exists an element of one petal outside the core. -/
lemma exists_coord_not_core_of_two_petals {S : SunflowerFam n t}
    {P₁ P₂ : Petal n} (h₁ : P₁ ∈ S.petals) (h₂ : P₂ ∈ S.petals)
    (hcard : P₂.card = P₁.card) (hne : P₁ ≠ P₂) :
    ∃ i ∈ P₁, i ∉ S.core := by
  classical
  have hssub : S.core ⊂ P₁ :=
    core_ssubset_of_two_petals (S := S)
      (P₁ := P₁) (P₂ := P₂) h₁ h₂ hcard hne
  rcases Finset.exists_of_ssubset hssub with ⟨i, hiP₁, hiNot⟩
  exact ⟨i, hiP₁, hiNot⟩

end SunflowerFam

end Sunflower

end

