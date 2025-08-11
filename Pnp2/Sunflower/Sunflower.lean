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
import Mathlib.Data.Finset.Disjoint
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

@[simp] lemma unions_empty :
    (∅ : Finset (Finset α)).unions = (∅ : Finset α) := by
  simp [unions]

@[simp] lemma unions_insert (A : Finset α) (𝓣 : Finset (Finset α)) :
    (insert A 𝓣).unions = A ∪ 𝓣.unions := by
  classical
  ext x; constructor <;> intro hx
  · rcases Finset.mem_unions.mp hx with ⟨B, hB, hxB⟩
    rcases Finset.mem_insert.mp hB with hBA | hBT
    · subst hBA
      exact Finset.mem_union.mpr (Or.inl hxB)
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_unions.mpr ⟨B, hBT, hxB⟩))
  · rcases Finset.mem_union.mp hx with hxA | hxU
    · exact Finset.mem_unions.mpr
        ⟨A, Finset.mem_insert_self _ _, hxA⟩
    · rcases Finset.mem_unions.mp hxU with ⟨B, hB, hxB⟩
      exact Finset.mem_unions.mpr
        ⟨B, Finset.mem_insert.mpr (Or.inr hB), hxB⟩

end Finset

namespace Sunflower

variable {α : Type} [DecidableEq α]

/-- The standard cardinality bound `(t - 1)^w * w!` appearing in the
    sunflower lemma.  Having it as a named definition makes subsequent
    statements cleaner. -/
def threshold (w t : ℕ) : ℕ := (t - 1) ^ w * Nat.factorial w

/-- The threshold for width `0` is `1`, since there is exactly one empty
set. -/
lemma threshold_zero (p : ℕ) : threshold 0 p = 1 := by
  simp [threshold]

/-- A convenient recurrence for the sunflower threshold.  Increasing the
width by one multiplies the bound by `(p - 1)` (for the new element) and
`w + 1` (for the factorial). -/
lemma threshold_succ (w p : ℕ) :
    threshold (w + 1) p = (p - 1) * (w + 1) * threshold w p := by
  -- Expand both sides and simplify using `pow_succ` and
  -- `Nat.factorial_succ`.
  simp [threshold, Nat.factorial_succ, pow_succ, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc]

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

/-- The union of a `w`-uniform family has size at most `w * |𝓢|`.  Each
element of the union contributes at least one to the sum of slice
cardinalities, which equals `w * 𝓢.card` by
`sum_card_slices_eq_w_mul_card`. -/
lemma unions_card_le_w_mul
    (𝓢 : Finset (Finset α)) (w : ℕ)
    (h_w : ∀ A ∈ 𝓢, A.card = w) :
    (𝓢.unions).card ≤ w * 𝓢.card := by
  classical
  -- double counting provides the total number of incidences
  have hsum := sum_card_slices_eq_w_mul_card (𝓢 := 𝓢) (w := w) h_w
  -- every element of the union appears in at least one set
  have hpos :
      ∑ x ∈ 𝓢.unions, (1 : ℕ)
        ≤ ∑ x ∈ 𝓢.unions, (slice 𝓢 x).card := by
    refine Finset.sum_le_sum ?_
    intro x hx
    rcases Finset.mem_unions.mp hx with ⟨A, hA, hxA⟩
    have hx_nonempty : (slice 𝓢 x).Nonempty :=
      ⟨A, by simpa [slice] using And.intro hA hxA⟩
    have hx_pos : 0 < (slice 𝓢 x).card := Finset.card_pos.mpr hx_nonempty
    exact Nat.succ_le_of_lt hx_pos
  -- rewrite the left-hand side via the cardinality of the union
  have hcard : (𝓢.unions).card = ∑ x ∈ 𝓢.unions, (1 : ℕ) :=
    Finset.card_eq_sum_ones (s := 𝓢.unions)
  -- combine the inequalities
  have hleft : (𝓢.unions).card ≤ ∑ x ∈ 𝓢.unions, (1 : ℕ) :=
    le_of_eq hcard
  have h' := le_trans hleft hpos
  simpa [hsum] using h'

/-! ### Pairwise disjoint subfamilies -/

/-- `pairwiseDisjoint T` means that distinct members of `T` have
disjoint intersection.  This is the natural notion of a family of
pairwise disjoint sets. -/
def pairwiseDisjoint (T : Finset (Finset α)) : Prop :=
  ∀ ⦃A⦄, A ∈ T → ∀ ⦃B⦄, B ∈ T → A ≠ B →
    A ∩ B = (∅ : Finset α)

/-- For a pairwise-disjoint subfamily `T ⊆ 𝓢` of `w`-sets, the union of
`T` has cardinality exactly `w * T.card`. -/
lemma unions_card_of_disjoint
    {𝓢 T : Finset (Finset α)} {w : ℕ}
    (hTsub : T ⊆ 𝓢)
    (hdisj : pairwiseDisjoint T)
    (h_w : ∀ A ∈ 𝓢, A.card = w) :
    (T.unions).card = w * T.card := by
  classical
  revert hTsub hdisj
  refine Finset.induction_on T ?base ?step
  · intro _ _; simp
  · intro A T hA hIH hTsub hdisj
    -- T is a subfamily of 𝓢
    have hTsub' : T ⊆ 𝓢 := by
      intro B hB; exact hTsub (Finset.mem_insert.mpr (Or.inr hB))
    -- pairwise disjointness restricts to `T`
    have hdisj' : pairwiseDisjoint T := by
      intro B hB C hC hBC
      exact hdisj (Finset.mem_insert.mpr (Or.inr hB))
        (Finset.mem_insert.mpr (Or.inr hC)) hBC
    -- apply the inductive hypothesis to `T`
    have hIH' : (T.unions).card = w * T.card := hIH hTsub' hdisj'
    -- union of `insert A T` is `A ∪ T.unions`
    have hUnions : (insert A T).unions = A ∪ T.unions := by
      simpa [Finset.unions_insert]
    -- intersection of `A` with the union of `T` is empty
    have hA_disj : A ∩ T.unions = (∅ : Finset α) := by
      apply Finset.eq_empty_of_forall_not_mem
      intro x hx
      rcases Finset.mem_inter.mp hx with ⟨hxA, hxU⟩
      rcases Finset.mem_unions.mp hxU with ⟨B, hB, hxB⟩
      have hAB := hdisj (Finset.mem_insert.mpr (Or.inl rfl))
        (Finset.mem_insert.mpr (Or.inr hB)) ?_
      · have : x ∈ (∅ : Finset α) := by
          simpa [hAB] using (Finset.mem_inter.mpr ⟨hxA, hxB⟩)
        simpa using this
      · intro hBA; exact hA (by simpa [hBA] using hB)
    -- card of the union using disjointness
    have hCardUnion : ((insert A T).unions).card = A.card + (T.unions).card := by
      have hAdd := Finset.card_union_add_card_inter A T.unions
      have hInterZero : (A ∩ T.unions).card = 0 := by
        simpa [hA_disj]
      have hAdd' : (A ∪ T.unions).card = A.card + (T.unions).card := by
        have := hAdd
        -- rewrite using the vanishing intersection
        simpa [hInterZero, add_comm, add_left_comm, add_assoc] using this
      simpa [hUnions, add_comm] using hAdd'
    -- conclude by rewriting in terms of `w`
    have hAcard : A.card = w := h_w A (hTsub (Finset.mem_insert.mpr (Or.inl rfl)))
    calc
      ((insert A T).unions).card
          = A.card + (T.unions).card := hCardUnion
      _ = w + (T.unions).card := by simpa [hAcard]
      _ = w + w * T.card := by simpa [hIH']
      _ = w * T.card + w := by
            simpa [Nat.add_comm] using (Nat.add_comm w (w * T.card))
      _ = w * (T.card + 1) := (Nat.mul_succ w T.card).symm
      _ = w * (insert A T).card := by
            have hcard_insert : (insert A T).card = T.card + 1 :=
              Finset.card_insert_of_not_mem hA
            simpa [hcard_insert, Nat.add_comm]

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

/-! ### Factorial decomposition over iterated erasures -/

/-- **Factorial decomposition of iterated slices.**

    Let `𝓢` be a `w`-uniform family and `xs` a list of elements to be
    erased one by one.  As long as the remaining width `w - xs.length` is
    positive, the following identity holds:

    \[
      (w - |xs|)! \cdot |familyAfter 𝓢 xs|
        = \sum_{x \in (familyAfter 𝓢 xs).unions}
            (w - |xs| - 1)! \cdot |familyAfter 𝓢 (x :: xs)|.
    \]

    Intuitively, each set in `familyAfter 𝓢 xs` has `w - xs.length`
    elements.  Expanding the factorial of this width and applying the
    double-counting lemma `sum_card_slices_eq_w_mul_card` yields the
    stated equality. -/
lemma factorial_card_decomposition
    {𝓢 : Finset (Finset α)} {w : ℕ} {xs : List α}
    (hunif : ∀ A ∈ 𝓢, A.card = w)
    (hpos : xs.length < w) :
    Nat.factorial (w - xs.length) * (familyAfter 𝓢 xs).card
      = ∑ x ∈ (familyAfter 𝓢 xs).unions,
          Nat.factorial (w - xs.length - 1)
            * (familyAfter 𝓢 (x :: xs)).card := by
  classical
  -- Abbreviation for the intermediate family after erasing `xs`.
  let S' := familyAfter 𝓢 xs
  -- After erasing `xs` the family remains uniform of width `w - xs.length`.
  have h_unif : ∀ A ∈ S', A.card = w - xs.length :=
    familyAfter_uniform (hunif := hunif) xs
  -- Apply the double-counting lemma to `S'`.
  have hsum :
      ∑ x ∈ S'.unions, (slice S' x).card
        = (w - xs.length) * S'.card :=
    sum_card_slices_eq_w_mul_card
      (𝓢 := S') (w := w - xs.length) h_unif

  -- The remaining width after processing `xs` is positive by assumption.
  have hw' : 0 < w - xs.length := Nat.sub_pos_of_lt hpos

  -- Expand the factorial on the left: `n! = n * (n - 1)!` for positive `n`.
  have hfact :
      Nat.factorial (w - xs.length)
        = (w - xs.length) * Nat.factorial (w - xs.length - 1) := by
    -- From `0 < w - xs.length` we obtain `1 ≤ w - xs.length`.
    have hle : 1 ≤ w - xs.length := Nat.succ_le_of_lt hw'
    -- Therefore `w - xs.length - 1 + 1 = w - xs.length`.
    have hsucc : w - xs.length - 1 + 1 = w - xs.length := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using Nat.sub_add_cancel hle
    -- Apply the recursive formula for the factorial and simplify.
    have := Nat.factorial_succ (w - xs.length - 1)
    -- Replace occurrences of `w - xs.length - 1 + 1` using the identity above.
    simpa [hsucc]
      using this

  -- Start rewriting the desired equality.
  calc
    Nat.factorial (w - xs.length) * S'.card
        = ((w - xs.length) *
            Nat.factorial (w - xs.length - 1)) * S'.card := by
              -- replace factorial using the expansion above
              simpa [hfact]
    _ = Nat.factorial (w - xs.length - 1) *
            ((w - xs.length) * S'.card) := by
              -- just reshuffle the multiplication for better readability
              ac_rfl
    _ = Nat.factorial (w - xs.length - 1) *
            (∑ x ∈ S'.unions, (slice S' x).card) := by
              -- substitute the double-counting identity
              simpa [hsum]
    _ = ∑ x ∈ S'.unions,
            Nat.factorial (w - xs.length - 1) * (slice S' x).card := by
              -- pull the scalar multiplier inside the sum
              simpa [Finset.mul_sum]
    _ = ∑ x ∈ S'.unions,
            Nat.factorial (w - xs.length - 1) *
              (familyAfter 𝓢 (x :: xs)).card := by
              -- identifying each slice with the next step in `familyAfter`
              apply Finset.sum_congr rfl
              intro x hx
              -- `familyAfter 𝓢 (x :: xs)` equals `eraseSlice S' x`
              -- and `card_eraseSlice` replaces the cardinality of a slice.
              simpa [S', familyAfter, card_eraseSlice]

/-! ### Greedy choice of a large next slice -/

/-- **Greedy slice bound: existence of a large next-step family.**

Given a `w`-uniform family `𝓢` and a list `xs` of already erased elements,
assume the remaining width `w - xs.length` is positive and the current family
`familyAfter 𝓢 xs` is nonempty.  Then there exists an element `x` in the union
of the current family such that the next-step family `familyAfter 𝓢 (x :: xs)`
has cardinality at least the average value predicted by the factorial
decomposition.

The bound is written in a slightly algebraic form using `Nat.div`; it says
that the maximal slice is at least the average slice size. -/
lemma exists_x_with_large_next_family
    {𝓢 : Finset (Finset α)} {w : ℕ} {xs : List α}
    (hunif : ∀ A ∈ 𝓢, A.card = w)
    (hpos : xs.length < w)
    (hSnonempty : (familyAfter 𝓢 xs).Nonempty) :
    ∃ x ∈ (familyAfter 𝓢 xs).unions,
      (familyAfter 𝓢 (x :: xs)).card ≥
        Nat.div (Nat.factorial (w - xs.length) * (familyAfter 𝓢 xs).card)
                ((familyAfter 𝓢 xs).unions.card *
                  Nat.factorial (w - xs.length - 1)) := by
  classical
  -- Abbreviation for the intermediate family.
  let S' := familyAfter 𝓢 xs
  -- After erasing `xs` the family remains uniform of width `w - xs.length`.
  have h_unif : ∀ A ∈ S', A.card = w - xs.length :=
    familyAfter_uniform (hunif := hunif) xs
  -- The remaining width is positive.
  have hw' : 0 < w - xs.length := Nat.sub_pos_of_lt hpos
  -- The current family is nonempty by assumption, hence its union is also
  -- nonempty (each set has positive cardinality).
  have hU_nonempty : (S'.unions).Nonempty := by
    rcases hSnonempty with ⟨A, hA⟩
    have hAcard := h_unif A hA
    have hApos : 0 < A.card := by
      simpa [hAcard] using hw'
    rcases Finset.card_pos.mp hApos with ⟨x, hxA⟩
    exact ⟨x, Finset.mem_unions.mpr ⟨A, hA, hxA⟩⟩

  -- Apply the factorial decomposition to `S'`.
  have hsum :=
    factorial_card_decomposition (𝓢 := 𝓢) (w := w) (xs := xs) hunif hpos

  -- Some handy abbreviations for the forthcoming calculations.
  let F := Nat.factorial (w - xs.length) * S'.card
  let c := Nat.factorial (w - xs.length - 1)
  let f : α → ℕ := fun x => c * (familyAfter 𝓢 (x :: xs)).card

  -- Rewrite the factorial decomposition using the abbreviations.
  have hsum' : ∑ x ∈ S'.unions, f x = F := by
    simpa [F, c, f] using hsum.symm

  -- Choose an element `x` maximising `f` on the union.
  obtain ⟨x, hxU, hxmax⟩ :=
    Finset.exists_max_image (s := S'.unions) f hU_nonempty

  -- All summands are bounded by the maximal one, so the sum is bounded by
  -- `|S'.unions| * f x`.
  have hbound : F ≤ S'.unions.card * f x := by
    -- from the maximality statement
    have hle : ∀ y ∈ S'.unions, f y ≤ f x := hxmax
    -- apply the standard estimate on sums of bounded functions
    have := Finset.sum_le_card_nsmul (s := S'.unions) (f := f)
      (n := f x) hle
    -- substitute the sum with `F`
    simpa [hsum', Nat.mul_comm] using this

  -- Extract the average bound: `f x ≥ F / |S'.unions|`.
  have hxavg : F / S'.unions.card ≤ f x :=
    Nat.div_le_of_le_mul (by
      simpa [Nat.mul_comm] using hbound)

  -- Divide once more by the factorial constant to isolate the cardinality
  -- of the next family.
  have hxavg2 : (F / S'.unions.card) / c ≤
      (familyAfter 𝓢 (x :: xs)).card := by
    -- rewrite `hxavg` in terms of the cardinality and apply the division
    -- inequality once more
    have hineq : F / S'.unions.card ≤
        c * (familyAfter 𝓢 (x :: xs)).card := by
      simpa [f, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hxavg
    -- `Nat.div_le_of_le_mul` expects the product in the form `c * g`
    -- where `g` is the eventual bound; this matches `hineq`
    simpa using Nat.div_le_of_le_mul hineq

  -- Convert `(F / |U|) / c` into `F / (|U| * c)` and finish.
  have hxfinal :
      F / (S'.unions.card * c) ≤
        (familyAfter 𝓢 (x :: xs)).card := by
    simpa [F, c, Nat.div_div_eq_div_mul, Nat.mul_comm,
      Nat.mul_left_comm, Nat.mul_assoc] using hxavg2

  -- Present the result in the desired `Nat.div` form.
  refine ⟨x, hxU, ?_⟩
  simpa [F, c, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    using hxfinal

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

/-- Base case of the classical sunflower lemma: families of singletons.
If a family of singletons has more than `p - 1` members (which is exactly
`threshold 1 p`), then it contains a `p`-sunflower with empty core. -/
lemma sunflower_exists_w1
    (𝓢 : Finset (Finset α)) (p : ℕ) (hp : 2 ≤ p)
    (h_size : threshold 1 p < 𝓢.card)
    (h_w : ∀ A ∈ 𝓢, A.card = 1) :
    HasSunflower 𝓢 1 p := by
  classical
  -- From the size assumption we extract a subfamily of size `p`.
  have hcardp : p ≤ 𝓢.card := by
    -- `threshold 1 p = p - 1` by definition.
    have hsize' : (p - 1) < 𝓢.card := by
      simpa [threshold] using h_size
    -- Hence `(p - 1) + 1 = p` is bounded by `𝓢.card`.
    have hsize'' : (p - 1) + 1 ≤ 𝓢.card := Nat.succ_le_of_lt hsize'
    -- Using `p ≥ 1` we rewrite `(p - 1) + 1` to `p`.
    have hp1lt : 1 < p := lt_of_lt_of_le (by decide : 1 < 2) hp
    have hp1 : 1 ≤ p := Nat.le_of_lt hp1lt
    simpa [Nat.sub_add_cancel hp1] using hsize''
  -- Choose a subfamily of exactly `p` singletons.
  obtain ⟨𝓣, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq (s := 𝓢) (n := p) hcardp
  -- All members of this subfamily are still singletons.
  have hT_cards : ∀ A ∈ 𝓣, A.card = 1 := by
    intro A hA; exact h_w A (hTsub hA)
  -- Distinct singletons are disjoint, hence their intersection is empty.
  have hpair :
      ∀ ⦃A⦄, A ∈ 𝓣 → ∀ ⦃B⦄, B ∈ 𝓣 → A ≠ B →
        A ∩ B = (∅ : Finset α) := by
    intro A hA B hB hAB
    have hA1 : A.card = 1 := hT_cards A hA
    have hB1 : B.card = 1 := hT_cards B hB
    obtain ⟨a, haA⟩ := Finset.card_eq_one.mp hA1
    obtain ⟨b, hbB⟩ := Finset.card_eq_one.mp hB1
    have hneq : a ≠ b := by
      intro h
      apply hAB
      simpa [haA, hbB, h]
    have hdisj_single : Disjoint ({a} : Finset α) {b} :=
      (disjoint_singleton).2 hneq
    have hdisj : Disjoint A B := by
      simpa [haA, hbB] using hdisj_single
    simpa using
      (Finset.disjoint_iff_inter_eq_empty.mp hdisj)
  -- Assemble the sunflower structure with empty core.
  refine ⟨𝓣, hTsub, ∅, ?_, hT_cards⟩
  refine ⟨hTcard, ?_⟩
  intro A hA B hB hAB
  simpa using hpair hA hB hAB
/-! ### Classical sunflower lemma (axiomatized) -/

/-- **Erdős–Rado sunflower lemma** (axiom).  If a finite family of
`w`-sets has more than `(p - 1)^w * w!` members, then it contains a
`p`-sunflower.  A complete combinatorial proof will be provided in a
future revision. -/
axiom sunflower_exists_classic
    (𝓢 : Finset (Finset α)) (w p : ℕ) (hw : 0 < w) (hp : 2 ≤ p)
    (h_size : threshold w p < 𝓢.card)
    (h_w : ∀ A ∈ 𝓢, A.card = w) :
    HasSunflower 𝓢 w p

/-- Convenient wrapper for the sunflower lemma when the family is
already known to consist of `w`-sets. -/
lemma sunflower_exists_of_fixedSize
    (𝓢 : Finset (Finset α)) (w p : ℕ) (hw : 0 < w) (hp : 2 ≤ p)
    (h_cards : ∀ A ∈ 𝓢, A.card = w)
    (h_big  : 𝓢.card > threshold w p) :
    HasSunflower 𝓢 w p :=
  sunflower_exists_classic 𝓢 w p hw hp
    (by simpa [threshold] using h_big) h_cards

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
    (hbig : F.card > threshold w t) :
    ∃ S : SunflowerFam n t, S.petals ⊆ F := by
  classical
  -- obtain the abstract sunflower using the axiom
  have hsun : HasSunflower (α := Fin n) F w t :=
    sunflower_exists_classic (𝓢 := F) (w := w) (p := t) hw ht
      (by simpa [threshold] using hbig) hcard
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

namespace Sunflower

open Boolcube

variable {α : Type} [DecidableEq α]

/-! ### Очистка семейства после выделения ядра -/

/-- Удаляет из семейства `𝓢` те подмножества, которые содержат фиксированное `core`. -/
def removeSupersets (𝓢 : Finset (Finset α)) (core : Finset α) :
    Finset (Finset α) :=
  𝓢.filter (fun A => ¬ core ⊆ A)

/-- Характеризация членства в `removeSupersets`. -/
lemma mem_removeSupersets {𝓢 : Finset (Finset α)} {core A : Finset α} :
    A ∈ removeSupersets 𝓢 core ↔ (A ∈ 𝓢 ∧ ¬ core ⊆ A) := by
  simp [removeSupersets]

/-- Размер отфильтрованного семейства не превосходит исходный размер. -/
lemma card_removeSupersets_le (𝓢 : Finset (Finset α)) (core : Finset α) :
    (removeSupersets 𝓢 core).card ≤ 𝓢.card := by
  classical
  exact Finset.card_filter_le (s := 𝓢) (p := fun A => ¬ core ⊆ A)

/-- Отфильтрованное семейство является подсемейством исходного. -/
lemma removeSupersets_subset (𝓢 : Finset (Finset α)) (core : Finset α) :
    removeSupersets 𝓢 core ⊆ 𝓢 := by
  intro A hA
  exact (mem_removeSupersets.mp hA).1

namespace SunflowerFam

variable {n t : ℕ}

/-- Удаляем из семейства `F` те элементы, которые содержат ядро `S.core`. -/
def removeCovered {S : SunflowerFam n t} (F : Finset (Petal n)) :
    Finset (Petal n) :=
  removeSupersets F S.core

/-- Остаток после удаления покрытых является подсемейством `F`. -/
lemma removeCovered_subset {S : SunflowerFam n t} {F : Finset (Petal n)} :
    S.removeCovered F ⊆ F :=
  removeSupersets_subset F S.core

/-- Характеризация членства в `removeCovered`. -/
lemma mem_removeCovered {S : SunflowerFam n t} {F : Finset (Petal n)}
    {A : Petal n} :
    A ∈ S.removeCovered F ↔ (A ∈ F ∧ ¬ S.core ⊆ A) := by
  classical
  simpa [SunflowerFam.removeCovered, Sunflower.removeSupersets,
    Sunflower.mem_removeSupersets]

/-- Оценка на размер оставшегося семейства после удаления покрытых. -/
lemma card_removeCovered_le {S : SunflowerFam n t} {F : Finset (Petal n)} :
    (S.removeCovered F).card ≤ F.card := by
  classical
  simpa [removeCovered] using Sunflower.card_removeSupersets_le F S.core

/-- Один шаг “алгоритма покрытия”: если семейство достаточно велико, то можно
    извлечь подсолнечник и удалить покрытые элементы. -/
lemma cover_step_if_large
    {F : Finset (Petal n)} {w t : ℕ}
    (hw : 0 < w) (ht : 2 ≤ t)
    (hcard : ∀ A ∈ F, A.card = w)
    (hbig  : F.card > threshold w t) :
    ∃ S : SunflowerFam n t, S.petals ⊆ F ∧
      (S.removeCovered F).card ≤ F.card := by
  classical
  obtain ⟨S, hSsub⟩ := exists_of_large_family_classic
    (n := n) (w := w) (t := t) (F := F) hw ht hcard hbig
  refine ⟨S, hSsub, ?_⟩
  simpa using S.card_removeCovered_le (F := F)


/-- На одном шаге алгоритма покрытия: если `S.petals ⊆ F`, то после удаления покрытых элементов
    (всех `A ∈ F`, таких что `S.core ⊆ A`) остаётся по меньшей мере на `S.petals.card` меньше. -/
lemma card_removeCovered_le_sub_t
    {S : SunflowerFam n t} {F : Finset (Petal n)}
    (hSub : S.petals ⊆ F) :
    (S.removeCovered F).card ≤ F.card - S.petals.card := by
  classical
  -- Множество удалённых элементов: все `A ∈ F` с `S.core ⊆ A`.
  let R := F.filter (fun A => S.core ⊆ A)
  -- Остаток: не содержащие ядра
  let G := S.removeCovered F   -- = F.filter (fun A => ¬ S.core ⊆ A)
  have hdisj : Disjoint G R := by
    -- `G` и `R` — это два комплиментарных фильтра по предикату и его отрицанию.
    -- В таких случаях они пересекаются пусто.
    apply Finset.disjoint_left.mpr
    intro A hG hR
    -- `hG`: A ∈ G = F.filter (¬ core ⊆ A)
    -- `hR`: A ∈ R = F.filter (core ⊆ A)
    -- противоречие
    have hG' := (Finset.mem_filter.mp hG).2
    have hR' := (Finset.mem_filter.mp hR).2
    exact hG' (hR')
  have hunnion : G ∪ R ⊆ F := by
    -- обе части — подсемейства F
    intro A hA
    have : (A ∈ G) ∨ (A ∈ R) := Finset.mem_union.mp hA
    cases this with
    | inl hGA =>
      exact (Finset.mem_filter.mp hGA).1
    | inr hRA =>
      exact (Finset.mem_filter.mp hRA).1

  -- Теперь посмотрим на `F.filter (core ⊆ ·)`.
  have : ∀ P ∈ S.petals, P ∈ R := by
    intro P hP
    have hP_core : S.core ⊆ P := S.sub_core _ hP
    have hPF : P ∈ F := hSub hP
    exact Finset.mem_filter.mpr ⟨hPF, hP_core⟩

  -- Значит `S.petals ⊆ R`; получаем нижнюю оценку для `R.card`.
  have hRcard_lower : S.petals.card ≤ R.card :=
    Finset.card_le_card this

  -- `G` и `R` дизъюнктны и подмножетсва `F`. Кардинальность `F`
  -- как минимум сумма кардинальностей `G` и `R`.
  have hUnionCard : G.card + R.card ≤ F.card := by
    -- поскольку `G ⊆ F`, `R ⊆ F`, и они дизъюнктны, то
    -- `|G| + |R| = |G ∪ R| ≤ |F|`
    -- Сначала докажем: `G ∪ R ⊆ F`, `Disjoint G R`. Уже есть.
    have hUnion : (G ∪ R).card = G.card + R.card :=
      Finset.card_union_of_disjoint hdisj
    have h_le : (G ∪ R).card ≤ F.card :=
      Finset.card_le_card hunnion
    -- Итого: card G + card R = card (G ∪ R) ≤ F.card.
    simpa [hUnion, Nat.add_comm] using h_le

  -- Из `G.card + R.card ≤ F.card` следует `G.card ≤ F.card - R.card`
  have : G.card ≤ F.card - R.card := by
    -- вычитаем `R.card` из обеих частей неравенства `G.card + R.card ≤ F.card`
    have h := Nat.sub_le_sub_right hUnionCard R.card
    have h_cancel : (G.card + R.card) - R.card = G.card := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        Nat.add_sub_cancel G.card R.card
    simpa [h_cancel] using h

  -- Подставим нижнюю оценку на `R.card`: `R.card ≥ S.petals.card`.
  exact le_trans this (by
    -- здесь используем монотонность `Nat.sub` по правому аргументу
    -- `F.card - R.card ≤ F.card - S.petals.card` если `S.petals.card ≤ R.card`.
    exact Nat.sub_le_sub_left hRcard_lower F.card)

/-- Частный случай с разыменованием `S.tsize`. -/
lemma card_removeCovered_le_sub_t'
    {S : SunflowerFam n t} {F : Finset (Petal n)} :
    S.petals ⊆ F →
    (S.removeCovered F).card ≤ F.card - t := by
  classical
  intro hSub
  simpa [S.tsize] using card_removeCovered_le_sub_t (S := S) (F := F) hSub

/-- Равномерность семейства сохраняется при удалении покрытых точками ядра. -/
lemma uniform_of_removeCovered
    {S : SunflowerFam n t} {F : Finset (Petal n)} {w : ℕ}
    (hcardF : ∀ A ∈ F, A.card = w) :
    ∀ A ∈ S.removeCovered F, A.card = w := by
  classical
  intro A hA
  rcases S.mem_removeCovered.mp hA with ⟨hAF, _⟩
  simpa using hcardF A hAF

/-- Если `S.petals ⊆ F` и `0 < t`, то размер семейства строго убывает. -/
lemma card_removeCovered_lt
    {S : SunflowerFam n t} {F : Finset (Petal n)}
    (hSub : S.petals ⊆ F) (htpos : 0 < t) :
    (S.removeCovered F).card < F.card := by
  classical
  -- Используем оценку `≤ F.card - t`, доказанную выше
  have hle := S.card_removeCovered_le_sub_t (F := F) hSub
  have hle' : (S.removeCovered F).card ≤ F.card - t := by
    simpa [S.tsize] using hle
  -- Из `S.petals ⊆ F` и `t > 0` следует, что `F` непусто.
  have hFpos : 0 < F.card := by
    have hCardLe : S.petals.card ≤ F.card := Finset.card_le_card hSub
    have hPetPos : 0 < S.petals.card := by
      simpa [S.tsize] using htpos
    exact lt_of_lt_of_le hPetPos hCardLe
  -- Число элементов после удаления строго меньше исходного.
  have hlt : F.card - t < F.card := Nat.sub_lt hFpos htpos
  exact lt_of_le_of_lt hle' hlt

/-- Один строгий шаг алгоритма покрытия: из большого `w`-равномерного семейства
    мы выделяем подсолнечник и удаляем все множества, содержащие его ядро. -/
lemma exists_cover_step_strict
    {F : Finset (Petal n)} {w t : ℕ}
    (hw : 0 < w) (ht : 2 ≤ t)
    (hcardF : ∀ A ∈ F, A.card = w)
    (hbig  : F.card > threshold w t) :
    ∃ S : SunflowerFam n t,
      S.petals ⊆ F ∧
      (∀ A ∈ S.removeCovered F, A.card = w) ∧
      (S.removeCovered F).card < F.card := by
  classical
  -- Шаг 1: извлекаем подсолнечник из большого семейства
  obtain ⟨S, hSsub⟩ := exists_of_large_family_classic
    (n := n) (w := w) (t := t) (F := F) hw ht hcardF hbig
  -- Шаг 2: после удаления покрытых сохраняется `w`-равномерность
  have h_uniform : ∀ A ∈ S.removeCovered F, A.card = w :=
    S.uniform_of_removeCovered (F := F) (w := w) hcardF
  -- Из `t ≥ 2` получаем `t > 0`, нужное для строгой убываемости
  have htpos : 0 < t := lt_of_lt_of_le (by decide : 0 < 2) ht
  -- Шаг 3: количество элементов после удаления строго меньше
  have hlt : (S.removeCovered F).card < F.card :=
    S.card_removeCovered_lt (F := F) hSsub htpos
  exact ⟨S, hSsub, h_uniform, hlt⟩

/-- Итерация алгоритма покрытия: из `w`-равномерного семейства `F` мы удаляем
    покрытые ядрами найденных подсолнечников до тех пор, пока размер не
    станет `≤ (t - 1)^w * w!`.  На выходе получаем подсемейство `F' ⊆ F`,
    которое остаётся `w`-равномерным и имеет ограниченный размер. -/
lemma exists_cover_until_threshold
    {F : Finset (Petal n)} {w t : ℕ}
    (hw : 0 < w) (ht : 2 ≤ t)
    (hcardF : ∀ A ∈ F, A.card = w) :
    ∃ F' ⊆ F, (∀ A ∈ F', A.card = w) ∧
      F'.card ≤ threshold w t := by
  classical
  -- Обозначим порог для размера семейства.
  let B := threshold w t

  -- Индуктивное утверждение: для любого семейства `F'` размера `N`,
  -- которое `w`-равномерно, существует подсемейство размера `≤ B`.
  let P : ℕ → Prop := fun N =>
    ∀ F' : Finset (Petal n),
      F'.card = N →
      (∀ A ∈ F', A.card = w) →
      ∃ G ⊆ F', (∀ A ∈ G, A.card = w) ∧ G.card ≤ B

  -- Докажем `P F.card` по сильной индукции по `F.card`.
  have hMain : P F.card := by
    -- сильная индукция по размеру семейства
    refine Nat.strongRecOn F.card ?step
    intro N IH F' hcardF' hunifF'
    -- Проверяем, не достигнут ли уже порог.
    by_cases hsmall : F'.card ≤ B
    · -- Семейство уже достаточно маленькое, берём его целиком.
      exact ⟨F', by exact Subset.rfl, hunifF', hsmall⟩
    -- Иначе `F'.card > B`, делаем один строгий шаг алгоритма покрытия.
    · have hbig' : F'.card > B := Nat.lt_of_not_ge hsmall
      -- Выделяем подсолнечник и уменьшаем семейство.
      obtain ⟨S, hSsub, h_uniform_after, hlt⟩ :=
        exists_cover_step_strict (n := n) (F := F') (w := w) (t := t)
          hw ht hunifF' hbig'
      -- Определяем `F₁` как остаток.
      let F₁ := S.removeCovered F'
      -- После одного шага размер строго уменьшается.
      have hlt' : F₁.card < N := by
        simpa [hcardF'] using hlt
      -- Применяем IH к `F₁`.
      have hrec := IH F₁.card hlt' F₁ rfl h_uniform_after
      rcases hrec with ⟨G, hGsub, hGunif, hGle⟩
      -- Полученное `G` также является подсемейством исходного `F'`.
      exact ⟨G, hGsub.trans (S.removeCovered_subset (F := F')), hGunif, hGle⟩

  -- Применяем индуктивное утверждение к исходному `F`.
  exact hMain F rfl hcardF

end SunflowerFam

end Sunflower


