/-
cover.lean
===========

Top‑level **cover construction** for the Family Collision‑Entropy Lemma.
The next step in the formalization introduces real "uncovered input"
structures and an *optional* search for the first uncovered ⟨f, x⟩.
`buildCover` now recurses on these data.  The entropy-based branch is
implemented via `exists_coord_entropy_drop` and decreases `H₂` both in
the chosen branch and in its complement.  Only the sunflower branch and
the final numeric bound remain open.
-/

import Pnp2.BoolFunc
import Pnp2.entropy
import Pnp2.sunflower
import Pnp2.Agreement
import Pnp2.BoolFunc.Support   -- new helper lemmas
import Pnp2.Sunflower.RSpread   -- definition of scattered families
import Pnp2.low_sensitivity_cover
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Data.Fintype.Card

open Classical
open BoolFunc
open Finset
open Agreement

namespace Cover

/-! ## Numeric bound -/

@[simp] def mBound (n h : ℕ) : ℕ := n * (h + 2) * 2 ^ (10 * h)

lemma numeric_bound (n h : ℕ) : 2 * h + n ≤ mBound n h := by
  have : 1 ≤ 2 ^ (10 * h) := Nat.one_le_pow _ _ (by decide : 0 < (2 : ℕ))
  have : (2 * h + n : ℕ) ≤ n * (h + 2) * 2 ^ (10 * h) := by
    have : 2 * h + n ≤ n * (h + 2) := by
      have h0 : 0 ≤ (h : ℤ) := by exact_mod_cast Nat.zero_le _
      nlinarith
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      Nat.mul_le_mul_left (n * (h + 2)) (Nat.succ_le_iff.mpr this)
  simpa [mBound] using this

/-! ### Counting bound for arbitrary covers -/

@[simp] def size {n : ℕ} (Rset : Finset (Subcube n)) : ℕ := Rset.card

lemma cover_size_bound {n : ℕ} (Rset : Finset (Subcube n)) :
    size Rset ≤ Fintype.card (Subcube n) := by
  classical
  simpa [size] using (Finset.card_le_univ (s := Rset))

/-! ## Auxiliary predicates -/

variable {n h : ℕ} (F : Family n)

/-- `x` is **not yet covered** by `Rset`. -/
def NotCovered (Rset : Finset (Subcube n)) (x : Vector Bool n) : Prop :=
  ∀ R ∈ Rset, x ∉ₛ R

/-- The set of all uncovered 1-inputs (together with their functions). -/
@[simp]
def uncovered (F : Family n) (Rset : Finset (Subcube n)) : Set (Σ f : BoolFunc n, Vector Bool n) :=
  {⟨f, x⟩ | f ∈ F ∧ f x = true ∧ NotCovered Rset x}

/-- Optionally returns the *first* uncovered ⟨f, x⟩. -/
noncomputable
def firstUncovered (F : Family n) (Rset : Finset (Subcube n)) : Option (Σ f : BoolFunc n, Vector Bool n) :=
  (uncovered F Rset).choose?  -- `choose?` from Mathlib (classical choice on set)

@[simp]
lemma firstUncovered_none_iff (R : Finset (Subcube n)) :
    firstUncovered F R = none ↔ uncovered F R = ∅ := by
  classical
  simp [firstUncovered, Set.choose?_eq_none]

/-- **Sunflower extraction step.**  If the family of currently
uncovered functions is large, the classical sunflower lemma yields a
subcube covering a positive fraction of them.  The precise constants
are irrelevant here; we only record the existence of such a rectangle.
Formal details are deferred. -/
-- This lemma implements step A-3 of the `buildCover` algorithm,
-- extracting a subcube that simultaneously covers many functions.

lemma sunflower_step
    (p t : ℕ)
    (hp : 0 < p) (ht : 2 ≤ t)
    (h_big : (t - 1).factorial * p ^ t < (Family.supports F).card)
    (h_support : ∀ f ∈ F, (BoolFunc.support f).card = p) :
  ∃ (R : Subcube n),
    (F.filter fun f ↦ ∀ x, x ∈ₛ R → f x = true).card ≥ t ∧ 1 ≤ R.dimension := by
  classical
  -- Build the family of essential supports of functions in `F`.
  let 𝓢 : Finset (Finset (Fin n)) := Family.supports F
  have h_sizes : ∀ s ∈ 𝓢, s.card = p := by
    intro s hs
    rcases Family.mem_supports.mp hs with ⟨f, hf, rfl⟩
    exact h_support f hf
  -- Apply the sunflower lemma to obtain a sunflower inside `𝓢`.
  obtain ⟨𝓣, h𝓣sub, hSun, hcard⟩ :=
    Sunflower.sunflower_exists (𝓢 := 𝓢) (w := p) (p := t)
      hp ht h_big (by intro s hs; simpa [h_sizes s hs] using h_sizes s hs)
  -- Extract the core `K` from the sunflower description.
  obtain ⟨hT, K, h_core⟩ := hSun
  -- Freeze the coordinates in `K` according to a fixed point `x₀`.
  let x₀ : Point n := fun _ => false
  let R : Subcube n := Agreement.Subcube.fromPoint x₀ K
  refine ⟨R, ?_, ?_⟩
  ·
    -- Each `A ∈ 𝓣` is the support of some function `f_A ∈ F`.
    have exists_f : ∀ A ∈ 𝓣, ∃ f ∈ F, support f = A := by
      intro A hA
      have hA' := h𝓣sub hA
      simpa using (Family.mem_supports.mp hA')
    choose f hfF hfSupp using exists_f
    -- (a) main counting inequality
    have h_filter_ge : (F.filter fun f ↦ ∀ x, x ∈ₛ R → f x = true).card ≥ t := by
      -- the sets in `𝓣` have size `t` and are pairwise distinct, and for each
      -- `A ∈ 𝓣` we chose a unique function `f_A`.
      have h_inj :
          (Finset.image (fun A : Finset (Fin n) => f A (by
            have : A ∈ 𝓣 := by exact ‹A ∈ 𝓣›)
            ) 𝓣).card = t := by
        have h_inj_aux :
            Function.Injective (fun A : Finset (Fin n) =>
              f A (by exact ‹A ∈ 𝓣›)) := by
          intro A1 A2 h_eq
          have : support (f A1 _) = support (f A2 _) := by
            have h1 : support (f A1 _) = A1 := hfSupp _ (by exact ‹A1 ∈ 𝓣›)
            have h2 : support (f A2 _) = A2 := hfSupp _ (by exact ‹A2 ∈ 𝓣›)
            simpa [h1, h2] using congrArg support h_eq
          simpa [hfSupp _ (by exact ‹A1 ∈ 𝓣›), hfSupp _ (by exact ‹A2 ∈ 𝓣›)]
            using this
        simpa [Finset.card_image] using
          (Finset.card_image_of_injective _ h_inj_aux)
      -- now show that every chosen `f_A` passes the filter
      have h_sub :
          (Finset.image (fun A : Finset (Fin n) => f A _) 𝓣)
            ⊆ F.filter (fun f ↦ ∀ x, x ∈ₛ R → f x = true) := by
        intro g hg
        rcases Finset.mem_image.1 hg with ⟨A, hA, rfl⟩
        have hgF : f A _ ∈ F := hfF _ hA
        have htrue : ∀ x, x ∈ₛ R → (f A _) x = true := by
          intro x hx
          -- on the core `K` the values of `x` are fixed as in `x₀`, while
          -- outside the core the set `A` contains no coordinates of `x₀`.
          have : x.restrict (support (f A _)) = x₀.restrict := by
            ext i hi
            by_cases hKi : i ∈ K
            · simp [x₀, hKi] at hx
            · have : i ∈ A := by simpa [hfSupp _ hA] using hi
              simpa using rfl
          have : (f A _) x = (f A _) x₀ :=
            BoolFunc.eval_eq_of_agree_on_support (f := f A _) (x := x) (y := x₀)
              (by intro i hi; simpa using congrArg (fun t => t) (this i hi))
          have hx0 : (f A _) x₀ = true := by
            obtain ⟨y, hy⟩ := BoolFunc.exists_true_on_support
              (f := f A _) (by simpa [hfSupp _ hA])
            simpa using hy
          simpa [Agreement.Subcube.fromPoint, hx, this] using hx0
        have h_card_le := Finset.card_le_of_subset h_sub
        simpa using (le_of_eq_of_le h_inj).trans h_card_le
      exact h_filter_ge
  ·
    -- `R` has dimension `n - K.card`.  The sunflower lemma ensures `K` is a
    -- proper subset of each support in the sunflower, so `K.card < n` and the
    -- dimension is positive.
    have h_dim : 1 ≤ n - K.card := by
      have h_lt : K.card < n := by
        obtain ⟨A, hA𝓣, hKA⟩ := hT
        have hlt : K.card < A.card := Finset.card_lt_card hKA
        have hA_le : A.card ≤ n := by
          have : A ⊆ Finset.univ := by intro i hi; exact Finset.mem_univ _
          exact Finset.card_le_of_subset this
        exact hlt.trans_le hA_le
      have : 0 < n - K.card := Nat.sub_pos_of_lt h_lt
      exact Nat.succ_le_of_lt this
    simpa [R, Subcube.dimension_fromPoint] using h_dim

/-! ## Inductive construction of the cover -/
/-! ## Inductive construction of the cover (replaced) -/
noncomputable def buildCover (F : Family n) (h : ℕ) (hH : BoolFunc.H₂ F ≤ (h : ℝ)) : Finset (Subcube n) :=
  (Pnp.Boolcube.familyEntropyCover (F := F) (h := h) hH).rects



/-! ## Proof that buildCover indeed covers every 1‑input -/

/-- All 1‑inputs of `F` lie in some rectangle of `Rset`. -/
@[simp]
def AllOnesCovered (F : Family n) (Rset : Finset (Subcube n)) : Prop :=
  ∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R

lemma AllOnesCovered.superset {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    (h₁ : AllOnesCovered F R₁) (hsub : R₁ ⊆ R₂) :
    AllOnesCovered F R₂ := by
  intro f hf x hx
  rcases h₁ f hf x hx with ⟨R, hR, hxR⟩
  exact ⟨R, hsub hR, hxR⟩

lemma AllOnesCovered.union {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    (h₁ : AllOnesCovered F R₁) (h₂ : AllOnesCovered F R₂) :
    AllOnesCovered F (R₁ ∪ R₂) := by
  intro f hf x hx
  by_cases hx1 : ∃ R ∈ R₁, x ∈ₛ R
  · rcases hx1 with ⟨R, hR, hxR⟩
    exact ⟨R, by simpa [Finset.mem_union] using Or.inl hR, hxR⟩
  · rcases h₂ f hf x hx with ⟨R, hR, hxR⟩
    exact ⟨R, by simpa [Finset.mem_union, hx1] using Or.inr hR, hxR⟩

lemma buildCover_covers (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    AllOnesCovered F (buildCover F h hH) := by
  classical
  have hcov := (Pnp.Boolcube.familyEntropyCover (F := F) (h := h) hH).covers
  simpa [buildCover] using hcov

lemma buildCover_mono (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    ∀ R ∈ buildCover F h hH, Subcube.monochromaticForFamily R F := by
  classical
  have hmono := (Pnp.Boolcube.familyEntropyCover (F := F) (h := h) hH).mono
  simpa [buildCover] using hmono

lemma buildCover_card_bound (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (buildCover F h hH).card ≤ mBound n h := by
  classical
  have hbound := (Pnp.Boolcube.familyEntropyCover (F := F) (h := h) hH).bound
  simpa [buildCover] using hbound


/-! ## Main existence lemma -/

lemma cover_exists (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, Subcube.monochromaticForFamily R F) ∧
      AllOnesCovered F Rset ∧
      Rset.card ≤ mBound n h := by
  classical
  let Rset := buildCover F h hH
  refine ⟨Rset, ?_, ?_, ?_⟩
  · intro R hR
    simpa using buildCover_mono (F := F) (h := h) (hH := hH) R hR
  · simpa using buildCover_covers (F := F) (h := h) hH
  · simpa using buildCover_card_bound (F := F) (h := h) (hH := hH)

/-! ## Choice wrapper -/

noncomputable
def coverFamily (hH : BoolFunc.H₂ F ≤ (h : ℝ)) : Finset (Subcube n) :=
  Classical.choice (cover_exists (F := F) (h := h) hH)

lemma coverFamily_spec (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (∀ R ∈ coverFamily (F := F) (h := h) hH,
        Subcube.monochromaticForFamily R F) ∧
      AllOnesCovered F (coverFamily (F := F) (h := h) hH) ∧
      (coverFamily (F := F) (h := h) hH).card ≤ mBound n h := by
  classical
  simpa [coverFamily] using
    Classical.choose_spec (cover_exists (F := F) (h := h) hH)

lemma coverFamily_mono (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    ∀ R ∈ coverFamily (F := F) (h := h) hH,
      Subcube.monochromaticForFamily R F :=
  (coverFamily_spec (F := F) (h := h) hH).1

lemma coverFamily_spec_cover (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    AllOnesCovered F (coverFamily (F := F) (h := h) hH) :=
  (coverFamily_spec (F := F) (h := h) hH).2.1

lemma coverFamily_card_bound (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (coverFamily (F := F) (h := h) hH).card ≤ mBound n h :=
  (coverFamily_spec (F := F) (h := h) hH).2.2

end Cover
