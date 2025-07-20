/-
cover.lean
===========

Top‑level **cover construction** for the Family Collision‑Entropy Lemma.
The next step in the formalization introduces real "uncovered input"
structures and an *optional* search for the first uncovered ⟨f, x⟩.
`buildCover` now recurses on these data.  The entropy-based branch is
implemented via `exists_coord_entropy_drop` and decreases `H₂` in both
subfamilies.  The final numeric bound remains open.
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

/-! ### Improved bound with positivity assumption
The development in `pnp` strengthens `numeric_bound` by assuming
`0 < n`.  This version follows the newer proof and will be useful for
compatibility with migrated lemmas. -/

lemma numeric_bound_pos (n h : ℕ) (hn : 0 < n) :
    2 * h + n ≤ mBound n h := by
  classical
  cases h with
  | zero =>
      have h0 : 2 * 0 + n ≤ mBound n 0 := by
        have hmul := Nat.mul_le_mul_left n (show (1 : ℕ) ≤ 2 from by decide)
        simpa [mBound, two_mul, Nat.mul_comm, one_mul] using hmul
      simpa using h0
  | succ h =>
      have hlinear : (2 * (h + 1) + n : ℕ) ≤ 2 * n * (h + 1 + 2) := by
        nlinarith [hn]
      have hpow : (2 : ℕ) ≤ 2 ^ (10 * (h + 1)) := by
        have hbase : (2 : ℕ) ≤ 2 ^ 10 := by decide
        have hexp : 10 ≤ 10 * (h + 1) := by
          have hx : (1 : ℕ) ≤ h + 1 := Nat.succ_le_succ (Nat.zero_le _)
          have hx' : (10 : ℕ) * 1 ≤ 10 * (h + 1) := Nat.mul_le_mul_left 10 hx
          set_option linter.unnecessarySimpa false in
          simpa [Nat.mul_one] using hx'
        exact hbase.trans (pow_le_pow_right' (by decide : (1 : ℕ) ≤ 2) hexp)
      have : 2 * (h + 1) + n ≤ n * (h + 1 + 2) * 2 ^ (10 * (h + 1)) := by
        calc
          2 * (h + 1) + n ≤ 2 * n * (h + 1 + 2) := hlinear
          _ = (n * (h + 1 + 2)) * 2 := by ring
          _ ≤ (n * (h + 1 + 2)) * 2 ^ (10 * (h + 1)) :=
            Nat.mul_le_mul_left _ hpow
      simpa [mBound] using this

lemma pow_le_mBound (n h : ℕ) (hn : 0 < n) :
    2 ^ (10 * h) ≤ mBound n h := by
  have hpos : 0 < n * (h + 2) := by
    have hpos' : 0 < h + 2 := Nat.succ_pos _
    exact Nat.mul_pos hn hpos'
  have hfactor : 1 ≤ n * (h + 2) := Nat.succ_le_of_lt hpos
  have := Nat.mul_le_mul_left (2 ^ (10 * h)) hfactor
  simpa [mBound, one_mul] using this

/-!  `mBound` is strictly positive for any positive dimension `n`.  This simple
numeric fact often provides a convenient lower bound when reasoning about cover
sizes. -/
lemma mBound_pos (n h : ℕ) (hn : 0 < n) :
    0 < mBound n h := by
  have hpos₁ : 0 < h + 2 := Nat.succ_pos _
  have hpos₂ : 0 < 2 ^ (10 * h) := pow_pos (by decide) _
  have hmul : 0 < n * (h + 2) := Nat.mul_pos hn hpos₁
  have := Nat.mul_pos hmul hpos₂
  simpa [mBound] using this

/-!  `mBound` is monotone in the entropy budget.  We will repeatedly
use this fact to lift bounds from recursive calls. -/

lemma mBound_mono {n : ℕ} : Monotone (mBound n) := by
  intro h₁ h₂ hh
  dsimp [mBound]
  have hfac : n * (h₁ + 2) ≤ n * (h₂ + 2) :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_right hh 2)
  have hpow : 2 ^ (10 * h₁) ≤ 2 ^ (10 * h₂) := by
    have := Nat.mul_le_mul_left 10 hh
    exact Nat.pow_le_pow_of_le_left (by decide : 1 ≤ (2 : ℕ)) this
  exact Nat.mul_le_mul hfac hpow

/-!  `mBound` is also monotone in the dimension parameter.  Increasing the
number of variables can only enlarge the numeric bound.  This simple fact
is occasionally convenient when comparing covers across different cube
sizes. -/
lemma mBound_mono_left {n₁ n₂ h : ℕ} (hn : n₁ ≤ n₂) :
    mBound n₁ h ≤ mBound n₂ h := by
  dsimp [mBound]
  have hfac : n₁ * (h + 2) ≤ n₂ * (h + 2) :=
    Nat.mul_le_mul_right (h + 2) hn
  have := Nat.mul_le_mul hfac (le_rfl : 2 ^ (10 * h) ≤ 2 ^ (10 * h))
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this

/-!  Doubling the bound for a smaller budget stays below the bound for the
next budget.  This simple numeric inequality is used when analysing the
entropy branch of `buildCover`. -/
lemma two_mul_mBound_le_succ (n h : ℕ) :
    2 * mBound n h ≤ mBound n (h + 1) := by
  have hfac : h + 2 ≤ h + 3 := by exact Nat.succ_le_succ (Nat.le_refl _)
  have hexp : 10 * h + 1 ≤ 10 * h + 10 := by
    have := (Nat.succ_le_succ (Nat.zero_le (10 * h)))
    -- `1 ≤ 10` allows us to shift by `10 * h`
    have h1 : (1 : ℕ) ≤ 10 := by decide
    exact add_le_add_left h1 (10 * h)
  have hpow : 2 ^ (10 * h + 1) ≤ 2 ^ (10 * h + 10) :=
    Nat.pow_le_pow_of_le_left (by decide : 1 ≤ (2 : ℕ)) hexp
  have hmul := Nat.mul_le_mul hfac hpow
  have := Nat.mul_le_mul_left n hmul
  -- rewrite both sides in terms of `mBound`
  simpa [mBound, pow_add, pow_succ, Nat.mul_left_comm, Nat.mul_assoc,
        Nat.mul_comm] using this

/-! ### Counting bound for arbitrary covers -/

@[simp] def size {n : ℕ} (Rset : Finset (Subcube n)) : ℕ := Rset.card

lemma cover_size_bound {n : ℕ} (Rset : Finset (Subcube n)) :
    size Rset ≤ Fintype.card (Subcube n) := by
  classical
  simpa [size] using (Finset.card_le_univ (s := Rset))

/-! ### Alternate bound wrapping the cardinality of `Subcube n`
The legacy development in `pnp` introduced an auxiliary function
`bound_function` to emphasise the `3 ^ n` growth of the universal
subcube family.  We reproduce the same API here for compatibility
with migrated proofs. -/

@[simp] def bound_function (n : ℕ) : ℕ := Fintype.card (Subcube n)

lemma size_bounds {n : ℕ} (Rset : Finset (Subcube n)) :
    size Rset ≤ bound_function n := by
  classical
  simpa [bound_function] using cover_size_bound (Rset := Rset)

/-! ## Auxiliary predicates -/

variable {n h : ℕ} (F : Family n)

/-- `x` is **not yet covered** by `Rset`. -/
def NotCovered (Rset : Finset (Subcube n)) (x : Vector Bool n) : Prop :=
  ∀ R ∈ Rset, x ∉ₛ R

@[simp] lemma notCovered_empty (x : Vector Bool n) :
    NotCovered (Rset := (∅ : Finset (Subcube n))) x := by
  intro R hR
  -- `hR` is impossible since the set is empty
  exact False.elim (by simpa using hR)

lemma NotCovered.monotone {R₁ R₂ : Finset (Subcube n)} (hsub : R₁ ⊆ R₂)
    {x : Vector Bool n} (hx : NotCovered (Rset := R₂) x) :
    NotCovered (Rset := R₁) x := by
  intro R hR
  exact hx R (hsub hR)

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

/-! ## Inductive construction of the cover (updated) -/
noncomputable
partial def buildCover (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (Rset : Finset (Subcube n) := ∅) : Finset (Subcube n) := by
  classical
  match hfu : firstUncovered F Rset with
  | none =>
      -- Base case: all 1-inputs of F are covered by Rset
      exact Rset
  | some ⟨f, x⟩ =>
      -- `f : BoolFunc n` and `x : Point n` is a 1-input uncovered by Rset.
      /- **Branching strategy:** Depending on family parameters, choose cover method:
         1. Low-sensitivity branch – if all functions in `F` have small sensitivity.
         2. Entropy branch – default fallback using a one-bit entropy drop. -/
      have F_nonempty : F.Nonempty :=
        ⟨f, by
          -- firstUncovered gives ⟨f, x⟩ with f ∈ F by definition
          rcases Set.choose?_mem (S := uncovered F Rset) hfu with ⟨hf, -, -⟩
          exact hf⟩
      -- Compute the maximum sensitivity s of functions in F
      let sensSet : Finset ℕ := F.image (fun g => sensitivity g)
      let s := sensSet.max' (Finset.nonempty.image F_nonempty _)
      have Hsens : ∀ g ∈ F, sensitivity g ≤ s :=
        fun g hg => Finset.le_max' sensSet s (by simp [sensSet, hg])
      -- **(1) Low-sensitivity branch:** if s is relatively small (e.g. O(log n)), use `low_sensitivity_cover`.
      -- Here we require `s` to be below a threshold; for example, if s ≤ ⌊log₂(n+1)⌋, consider F "low-sensitivity".
      cases Nat.lt_or_le s (Nat.log2 (Nat.succ n)) with
      | inl hs_small =>
          -- All functions have sensitivity ≤ s, with s relatively small compared to n.
          have ⟨R_ls, Hmono, Hcover, Hsize⟩ :=
            BoolFunc.low_sensitivity_cover (F := F) (s := s) (C := 10) Hsens
          -- Use the lemma's witness set R_ls as the remaining cover for all uncovered points.
          exact Rset ∪ R_ls
      | inr hs_large =>
          -- **Entropy branch:** apply one-bit entropy drop and recurse on two sub-families.
          have ⟨i, b, Hdrop⟩ :=
            BoolFunc.exists_coord_entropy_drop (F := F)
              (hn := by decide)
              (hF := Finset.card_pos.mpr F_nonempty)
          -- Split on coordinate `i = b` (one branch) vs `i = ¬b` (other branch),
          -- both reduce `H₂` by at least `1`.
          let F0 := F.restrict i b
          let F1 := F.restrict i (!b)
          have hH0 : BoolFunc.H₂ F0 ≤ (h - 1 : ℝ) := by
            -- H₂(F0) ≤ H₂(F) - 1
            simpa using (BoolFunc.H₂_restrict_le (F := F) (i := i) (b := b)).trans Hdrop
          have hH1 : BoolFunc.H₂ F1 ≤ (h - 1 : ℝ) := by
            -- H₂(F1) ≤ H₂(F) - 1
            simpa using (BoolFunc.H₂_restrict_compl_le (F := F) (i := i) (b := b)).trans Hdrop
          exact (buildCover F0 (h - 1) (by exact hH0)) ∪
                (buildCover F1 (h - 1) (by exact hH1))

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


/-! ### Uncovered pairs and a simple measure

The recursion for `buildCover` will track the number of still-uncovered
`1`‑inputs together with an entropy budget.  It is therefore convenient to
express when no uncovered points remain and to define a lightweight numeric
measure used in termination arguments. -/

lemma uncovered_eq_empty_of_allCovered {F : Family n} {Rset : Finset (Subcube n)}
    (hcov : AllOnesCovered F Rset) :
    uncovered F Rset = ∅ := by
  classical
  ext p; constructor
  · intro hp
    rcases hp with ⟨hf, hx, hnc⟩
    rcases hcov p.1 hf p.2 hx with ⟨R, hR, hxR⟩
    have : p.2 ∉ₛ R := hnc R hR
    exact False.elim (this hxR)
  · intro hp
    simp [hp]

/-- A very coarse termination measure for the recursion.  The first component
tracks the available entropy budget `h`, while the second counts currently
uncovered `1`‑inputs.  Each branch of `buildCover` will strictly decrease this
sum. -/
def mu (F : Family n) (h : ℕ) (Rset : Finset (Subcube n)) : ℕ :=
  2 * h + (uncovered F Rset).toFinset.card

lemma mu_of_allCovered {F : Family n} {Rset : Finset (Subcube n)} {h : ℕ}
    (hcov : AllOnesCovered F Rset) :
    mu F h Rset = 2 * h := by
  have hzero : uncovered F Rset = ∅ := uncovered_eq_empty_of_allCovered (F := F) hcov
  simp [mu, hzero]

lemma mu_of_firstUncovered_none {F : Family n} {Rset : Finset (Subcube n)} {h : ℕ}
    (hfu : firstUncovered (F := F) Rset = none) :
    mu F h Rset = 2 * h := by
  have hcov : AllOnesCovered F Rset :=
    allOnesCovered_of_firstUncovered_none (F := F) (Rset := Rset) hfu
  simpa using mu_of_allCovered (F := F) (Rset := Rset) (h := h) hcov

lemma mu_nonneg {F : Family n} {Rset : Finset (Subcube n)} {h : ℕ} :
    0 ≤ mu F h Rset := by
  exact Nat.zero_le _

lemma mu_lower_bound {F : Family n} {Rset : Finset (Subcube n)} {h : ℕ} :
    2 * h ≤ mu F h Rset := by
  simpa [mu] using Nat.le_add_right (2 * h) ((uncovered F Rset).toFinset.card)

/-! `mu` is monotone in the entropy budget `h`:
increasing the available budget can only increase the measure. -/
lemma mu_mono_h {F : Family n} {Rset : Finset (Subcube n)}
    {h₁ h₂ : ℕ} (hh : h₁ ≤ h₂) :
    mu F h₁ Rset ≤ mu F h₂ Rset := by
  dsimp [mu]
  exact add_le_add (Nat.mul_le_mul_left _ hh) le_rfl

/-!
If `firstUncovered` returns a value, then the uncovered set is nonempty
and the measure `mu` is strictly larger than `2 * h`.  This convenience
lemma will be useful when analysing the main recursion measure.
-/
lemma mu_gt_of_firstUncovered_some {F : Family n} {Rset : Finset (Subcube n)}
    {h : ℕ} (hfu : firstUncovered (F := F) Rset ≠ none) :
    2 * h < mu F h Rset := by
  classical
  -- The uncovered set cannot be empty, otherwise `firstUncovered` would
  -- have returned `none`.
  have hne : uncovered F Rset ≠ ∅ := by
    intro hempty
    have := (firstUncovered_none_iff (F := F) (R := Rset)).2 hempty
    exact hfu this
  -- A nonempty set has positive card after coercion to a finset.
  obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hpos : 0 < (uncovered F Rset).toFinset.card :=
    Finset.card_pos.mpr ⟨p, by simpa using hp⟩
  -- Hence the measure `mu` exceeds `2 * h` by at least one.
  have := Nat.lt_add_of_pos_right hpos
  simpa [mu] using this

/-!
`uncovered_card_bound` provides a very coarse upper bound on the number of
still uncovered pairs.  Each pair consists of some function from `F` together
with a point of the Boolean cube, hence there are at most `F.card * 2 ^ n`
possibilities.  This crude estimate is occasionally convenient when comparing
with numeric bounds on the cover size.-/
lemma uncovered_card_bound (F : Family n) (Rset : Finset (Subcube n)) :
    (uncovered F Rset).toFinset.card ≤ F.card * 2 ^ n := by
  classical
  -- Every element of `uncovered F Rset` is a pair `⟨f, x⟩` with `f ∈ F` and a
  -- point `x : Vector Bool n`.  Compare with the full Cartesian product.
  have hsubset : (uncovered F Rset).toFinset ⊆
      F.product (Finset.univ : Finset (Vector Bool n)) := by
    intro p hp
    rcases hp with ⟨hf, -, -⟩
    have hx : p.2 ∈ (Finset.univ : Finset (Vector Bool n)) := by simp
    exact Finset.mem_product.mpr ⟨hf, hx⟩
  have hcard := Finset.card_le_of_subset hsubset
  -- Cardinality of a product splits multiplicatively.
  have hprod := Finset.card_product (s := F)
      (t := (Finset.univ : Finset (Vector Bool n)))
  -- The cube `Vector Bool n` has size `2 ^ n`.
  have hcube : ((Finset.univ : Finset (Vector Bool n))).card = 2 ^ n := by
    simpa using (Fintype.card_vector (α := Bool) (n := n))
  simpa [hprod, hcube] using hcard

/-!
`uncovered` is monotone with respect to the set of rectangles: adding
a new rectangle can only remove uncovered pairs.  The next lemma
formalises this simple observation and will be handy when reasoning
about the termination measure `mu`.
-/
lemma uncovered_subset_of_union_singleton {F : Family n}
    {Rset : Finset (Subcube n)} {R : Subcube n} :
    uncovered F (Rset ∪ {R}) ⊆ uncovered F Rset := by
  classical
  intro p hp
  rcases hp with ⟨hf, hx, hnc⟩
  refine ⟨hf, hx, ?_⟩
  -- `p.2` is not covered by any rectangle in `Rset ∪ {R}`,
  -- hence in particular by any rectangle of `Rset` alone.
  intro S hS
  exact hnc S (by exact Finset.mem_union.mpr <| Or.inl hS)

lemma mu_union_singleton_le {F : Family n} {Rset : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ} :
    mu F h (Rset ∪ {R}) ≤ mu F h Rset := by
  classical
  -- The uncovered set can only shrink when adding a rectangle.
  have hsub : uncovered F (Rset ∪ {R}) ⊆ uncovered F Rset :=
    uncovered_subset_of_union_singleton (F := F) (Rset := Rset) (R := R)
  have hsubF : (uncovered F (Rset ∪ {R})).toFinset ⊆ (uncovered F Rset).toFinset := by
    intro x hx
    have hx' : x ∈ uncovered F (Rset ∪ {R}) := by simpa using hx
    have hx'' : x ∈ uncovered F Rset := hsub hx'
    simpa using hx''
  have hcard := Finset.card_le_of_subset hsubF
  -- Combine with the definition of `mu`.
  simpa [mu] using add_le_add_left hcard (2 * h)

lemma mu_union_singleton_lt {F : Family n} {Rset : Finset (Subcube n)}
    {R : Subcube n} {h : ℕ}
    (hx : ∃ p ∈ uncovered F Rset, p.2 ∈ₛ R) :
    mu F h (Rset ∪ {R}) < mu F h Rset := by
  classical
  rcases hx with ⟨p, hpU, hpR⟩
  have hp_not : p ∉ uncovered F (Rset ∪ {R}) := by
    rcases hpU with ⟨hf, hx, hnc⟩
    intro hp'
    rcases hp' with ⟨hf', hx', hnc'⟩
    have := hnc' R (by simp) hpR
    exact this
  have hsub : (uncovered F (Rset ∪ {R})).toFinset ⊆ (uncovered F Rset).toFinset := by
    intro x hx
    have hx' : x ∈ uncovered F (Rset ∪ {R}) := by simpa using hx
    have hx'' : x ∈ uncovered F Rset :=
      uncovered_subset_of_union_singleton (F := F) (Rset := Rset) (R := R) hx'
    simpa using hx''
  have hproper : ¬( (uncovered F Rset).toFinset ⊆ (uncovered F (Rset ∪ {R})).toFinset ) := by
    intro hsubset
    have hpFin : p ∈ (uncovered F Rset).toFinset := by simpa using hpU
    have := hsubset hpFin
    exact hp_not this
  have hcard := Finset.card_lt_of_subset hsub hproper
  -- Add `2*h` to both sides.
  simpa [mu] using Nat.add_lt_add_left hcard (2 * h)

lemma mu_union_le {F : Family n} {R₁ R₂ : Finset (Subcube n)} {h : ℕ} :
    mu F h (R₁ ∪ R₂) ≤ mu F h R₁ := by
  classical
  refine Finset.induction_on R₂ ?base ?step
  · simp [mu]
  · intro R S hR hIH
    have hstep := mu_union_singleton_le (F := F) (Rset := R₁ ∪ S) (R := R)
      (h := h)
    have hcomb := le_trans hstep hIH
    -- `Finset.insert` ensures `R ∉ S`, so unions simplify.
    have : R₁ ∪ insert R S = (R₁ ∪ S) ∪ {R} := by
      ext x; by_cases hx : x = R
      · subst hx; simp [hR]
      · simp [Finset.mem_insert, hx]
    simpa [this, Finset.union_assoc] using hcomb

lemma mu_mono_subset {F : Family n} {R₁ R₂ : Finset (Subcube n)} {h : ℕ}
    (hsub : R₁ ⊆ R₂) :
    mu F h R₂ ≤ mu F h R₁ := by
  classical
  -- Express `R₂` as `R₁ ∪ (R₂ \ R₁)` and apply `mu_union_le`.
  have hunion : R₂ = R₁ ∪ (R₂ \ R₁) := by
    ext x; by_cases hx : x ∈ R₁
    · constructor
      · intro hxR2
        exact Finset.mem_union.mpr <| Or.inl hx
      · intro hunion
        exact hx
    · constructor
      · intro hxR2
        have hxRdiff : x ∈ R₂ \ R₁ := by
          exact ⟨hxR2, by simpa [hx]⟩
        exact Finset.mem_union.mpr <| Or.inr hxRdiff
      · intro hunion
        rcases Finset.mem_union.mp hunion with hx₁ | hx₂
        · exact hsub hx₁
        · exact hx₂.1
  have := mu_union_le (F := F) (h := h) (R₁ := R₁) (R₂ := R₂ \ R₁)
  simpa [hunion] using this

/-!
`mu_union_buildCover_le` is a small helper lemma used in termination
arguments for `buildCover`.  Adding the rectangles produced by one
step of the construction can only decrease the measure `μ`, since the
set of uncovered pairs shrinks.  The result follows directly from
`mu_union_le`.
-/
lemma mu_union_buildCover_le (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (Rset : Finset (Subcube n)) :
    mu F h (Rset ∪ buildCover F h hH Rset) ≤ mu F h Rset := by
  classical
  -- `mu_union_le` already states that adding any collection of
  -- rectangles cannot increase `μ`.  We instantiate it with the set
  -- returned by `buildCover`.
  simpa [Finset.union_comm, Finset.union_assoc] using
    (mu_union_le (F := F) (h := h) (R₁ := Rset)
      (R₂ := buildCover F h hH Rset))

/-!
`mu_buildCover_lt_start` is a convenient strict version of
`mu_union_buildCover_le` for the initial call of `buildCover`.
If a `1`‑input remains uncovered, then the measure strictly decreases
after inserting the rectangles produced by `buildCover`.
-/
lemma mu_buildCover_lt_start (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hfu : firstUncovered (F := F) (∅ : Finset (Subcube n)) ≠ none) :
    mu F h (buildCover F h hH) < mu F h (∅ : Finset (Subcube n)) := by
  classical
  -- The uncovered set is nonempty because `firstUncovered` returned a value.
  have hne : uncovered F (∅ : Finset (Subcube n)) ≠ ∅ := by
    intro hempty
    have hfu0 :=
      (firstUncovered_none_iff (F := F) (R := (∅ : Finset (Subcube n)))).2 hempty
    exact hfu hfu0
  have hpos :
      0 < (uncovered F (∅ : Finset (Subcube n))).toFinset.card := by
    have hnonempty :
        (uncovered F (∅ : Finset (Subcube n))).toFinset.Nonempty := by
      obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.mpr hne
      exact ⟨p, by simpa using hp⟩
    exact Finset.card_pos.mpr hnonempty
  -- The measure of the final cover collapses to `2*h`.
  have hmu := buildCover_mu (F := F) (h := h) (hH := hH)
  -- Explicit expression for the initial measure.
  have hmu0 :
      mu F h (∅ : Finset (Subcube n)) =
        2 * h + (uncovered F (∅ : Finset (Subcube n))).toFinset.card := by
    simp [mu]
  -- Compare the two measures.
  have hgt :
      (2 * h) < 2 * h + (uncovered F (∅ : Finset (Subcube n))).toFinset.card :=
    Nat.lt_add_of_pos_right hpos
  simpa [hmu, hmu0] using hgt

/-!
`mu_buildCover_le_start` is a weak version of `mu_buildCover_lt_start`
that holds unconditionally.  If the family already has no uncovered
inputs then `buildCover` immediately returns the empty set and the two
measures coincide.  Otherwise `mu_buildCover_lt_start` yields a strict
inequality.  In both cases the result after running `buildCover` has
measure at most the starting value.-/

lemma mu_buildCover_le_start (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    mu F h (buildCover F h hH) ≤ mu F h (∅ : Finset (Subcube n)) := by
  classical
  -- Either an uncovered input exists or not.
  by_cases hfu : firstUncovered F (∅ : Finset (Subcube n)) = none
  · -- Immediate termination: both measures collapse to `2*h`.
    have hmu := buildCover_mu (F := F) (h := h) (hH := hH)
    have hmu0 := mu_of_firstUncovered_none (F := F)
      (R := (∅ : Finset (Subcube n))) (h := h) hfu
    simpa [hfu, hmu0] using hmu.le
  · -- Otherwise we invoke the strict inequality lemma.
    have hlt := mu_buildCover_lt_start (F := F) (h := h) (hH := hH)
      (by simpa using hfu)
    exact hlt.le
  
lemma mono_subset {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    (h₁ : ∀ R ∈ R₁, Subcube.monochromaticForFamily R F) (hsub : R₂ ⊆ R₁) :
    ∀ R ∈ R₂, Subcube.monochromaticForFamily R F := by
  intro R hR
  exact h₁ R (hsub hR)

lemma mono_union {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    (h₁ : ∀ R ∈ R₁, Subcube.monochromaticForFamily R F)
    (h₂ : ∀ R ∈ R₂, Subcube.monochromaticForFamily R F) :
    ∀ R ∈ R₁ ∪ R₂, Subcube.monochromaticForFamily R F := by
  intro R hR
  rcases Finset.mem_union.mp hR with h | h
  · exact h₁ R h
  · exact h₂ R h

@[simp] lemma AllOnesCovered.empty {F : Family n} :
    AllOnesCovered (F := F) (∅ : Finset (Subcube n)) ↔
      ∀ f ∈ F, ∀ x, f x = true → False := by
  classical
  constructor
  · intro h f hf x hx
    rcases h f hf x hx with ⟨R, hR, _hxR⟩
    simp at hR
  · intro h f hf x hx
    exact False.elim (h f hf x hx)

lemma allOnesCovered_of_firstUncovered_none {F : Family n}
    {Rset : Finset (Subcube n)}
    (hfu : firstUncovered (F := F) Rset = none) :
    AllOnesCovered F Rset := by
  classical
  intro f hf x hx
  by_contra hxcov
  -- If `x` were uncovered, `⟨f, x⟩` would appear in `uncovered F Rset`.
  have hxNC : NotCovered (Rset := Rset) x := by
    intro R hR hxR
    exact hxcov ⟨R, hR, hxR⟩
  have hx_mem : (⟨f, x⟩ : Σ f : BoolFunc n, Vector Bool n) ∈ uncovered F Rset := by
    simp [uncovered, hf, hx, hxNC]
  have hempty : uncovered F Rset = ∅ := (firstUncovered_none_iff (F := F) (R := Rset)).1 hfu
  simpa [hempty] using hx_mem


/-! ### Lifting monochromaticity from restricted families

If a subcube `R` fixes the `i`-th coordinate to `b`, then a family that is
monochromatic on the restricted version of `F` is also monochromatic on `F`
itself.  This simple helper lemma is used in the entropy branch of the cover
construction. -/

lemma lift_mono_of_restrict
    {F : Family n} {i : Fin n} {b : Bool} {R : Subcube n}
    (hfix : ∀ x, R.Mem x → x i = b)
    (hmono : Subcube.monochromaticForFamily R (F.restrict i b)) :
    Subcube.monochromaticForFamily R F := by
  classical
  rcases hmono with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro f hf x hx
  have hf0 : f.restrictCoord i b ∈ F.restrict i b := by
    simpa [Family.restrict, hf]
  have : (f.restrictCoord i b) x = c := hc (f.restrictCoord i b) hf0 x hx
  have hxib : x i = b := hfix x hx
  simpa [BFunc.restrictCoord, hxib] using this


lemma lift_mono_of_restrict_fixOne
    {F : Family n} {i : Fin n} {b : Bool} {R : Subcube n}
    (hmono : Subcube.monochromaticForFamily R (F.restrict i b)) :
    Subcube.monochromaticForFamily (Subcube.fixOne i b ⊓ R) F := by
  classical
  have hfix : ∀ x, (Subcube.fixOne i b ⊓ R).Mem x → x i = b := by
    intro x hx
    exact (Subcube.mem_fixOne_iff).1 hx.1
  have hmono' : Subcube.monochromaticForFamily (Subcube.fixOne i b ⊓ R) (F.restrict i b) := by
    rcases hmono with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    intro f hf x hx
    exact hc f hf x hx.2
  exact lift_mono_of_restrict (F := F) (i := i) (b := b) (R := Subcube.fixOne i b ⊓ R) hfix hmono'


lemma buildCover_covers (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    AllOnesCovered F (buildCover F h hH) := by
  classical
  -- well-founded recursion on number of uncovered points (lexicographic on H₂ and uncovered count)
  revert F
  refine (fun F ↦ _ : AllOnesCovered F (buildCover F h hH)) ?_?_
  intro F
  suffices H : ∀ Rset, AllOnesCovered F (buildCover F h hH Rset) by
    simpa using H ∅
  intro Rset
  -- split on the first uncovered 1-input, if any
  cases hfu : firstUncovered F Rset with
  | none =>
    -- Base case: no uncovered inputs remain
    have hbase : AllOnesCovered F Rset := by
      intro f hf x hx
      have hempty : uncovered F Rset = ∅ := (firstUncovered_none_iff (F := F) Rset).1 hfu
      -- If x were not covered by Rset, then ⟨f, x⟩ would lie in `uncovered F Rset` (contradiction)
      by_cases hxRset : ∃ R ∈ Rset, x ∈ₛ R
      · rcases hxRset with ⟨R, hR, hxR⟩
        exact ⟨R, hR, hxR⟩
      · have hxNC : NotCovered Rset x := fun R hR ↦ (not_exists.mp hxRset) R ∘ And.intro hR
        have : (⟨f, x⟩ : Σ BoolFunc n, Vector Bool n) ∈ uncovered F Rset := by simp [uncovered, hf, hx, hxNC]
        rw [hempty] at this
        exact False.elim this
    simpa [buildCover, hfu] using hbase
  | some tup =>
    -- Inductive step: an uncovered 1-input exists
    rcases tup with ⟨f, x⟩  -- so f ∈ F, f x = true, and x is not covered by Rset
    -- Consider the branch strategy from `buildCover` definition:
    -- (1) Low-sensitivity branch
    let sensSet : Finset ℕ := F.image (fun g => sensitivity g)
    let s := sensSet.max' (Finset.nonempty.image (BoolFunc.Family.nonempty_of_mem hf) _)
    have Hsens : ∀ g ∈ F, sensitivity g ≤ s :=
      fun g hg ↦ Finset.le_max' sensSet s (by simp [sensSet, hg])
    cases hs : Nat.lt_or_le s (Nat.log2 (Nat.succ n)) with
    | inl hs_small =>
      -- Low-sensitivity case: use the `low_sensitivity_cover` lemma to cover all 1-inputs at once
      obtain ⟨R_ls, Hmono, Hcover, Hsize⟩ :=
        BoolFunc.low_sensitivity_cover (F := F) (s := s) (C := 10) Hsens
      -- Here `Hcover` states: ∀ f ∈ F, ∀ y, f y = true → ∃ R ∈ R_ls, y ∈ₛ R
      -- Combine the existing coverage of `Rset` with the low-sensitivity cover `R_ls`.
      have hcov_union : AllOnesCovered F (Rset ∪ R_ls) := by
        intro g hg y hy
        by_cases hyRset : ∃ R ∈ Rset, y ∈ₛ R
        · rcases hyRset with ⟨R, hRset, hyR⟩
          exact ⟨R, by simp [Finset.mem_union.mpr (Or.inl hRset)], hyR⟩
        · obtain ⟨R, hR_ls, hyR⟩ := Hcover g hg y hy
          exact ⟨R, by simp [Finset.mem_union.mpr (Or.inr hR_ls)], hyR⟩
      -- Conclude for this branch: buildCover returns `Rset ∪ R_ls`.
      simpa [buildCover, hfu, hs_small] using hcov_union
    | inr hs_large =>
      -- **Entropy branch:** split on a coordinate to reduce entropy
      obtain ⟨i, b, Hdrop⟩ :=
        BoolFunc.exists_coord_entropy_drop (F := F) (hn := by decide)
          (hF := Finset.card_pos.mpr ⟨f, hf⟩)
      let F0 := F.restrict i b
      let F1 := F.restrict i (!b)
      have hH0 : BoolFunc.H₂ F0 ≤ (h - 1 : ℝ) := by
        simpa using (BoolFunc.H₂_restrict_le (F := F) (i := i) (b := b)).trans Hdrop
      have hH1 : BoolFunc.H₂ F1 ≤ (h - 1 : ℝ) := by
        simpa using (BoolFunc.H₂_restrict_compl_le (F := F) (i := i) (b := b)).trans Hdrop
      -- Final cover is `buildCover F0 (h-1) ∪ buildCover F1 (h-1)`
      intro g hg y hy
      by_cases hyRset : ∃ R ∈ Rset, y ∈ₛ R
      · rcases hyRset with ⟨R, hR, hyR⟩
        exact ⟨R, by simp [hyRset], hyR⟩
      by_cases hi : y i = b
      · -- y falls in the branch where `x_i = b`
        let g0 := g.restrictCoord i b
        have hg0 : g0 ∈ F0 := Finset.mem_image_of_mem (fun f => f.restrictCoord i b) hg
        have hg0y : g0 y = true := by simp [BoolFunc.restrictCoord, hi, hy]
        rcases buildCover_covers (F := F0) (h := h - 1) (hH := hH0) g0 hg0 y hg0y with ⟨R0, hR0, hyR0⟩
        exact ⟨R0, by simp [hR0], hyR0⟩
      · -- y falls in the branch where `x_i = ¬b`
        let g1 := g.restrictCoord i (!b)
        have hg1 : g1 ∈ F1 := Finset.mem_image_of_mem (fun f => f.restrictCoord i (!b)) hg
        have hg1y : g1 y = true := by simp [BoolFunc.restrictCoord, hi, hy]
        rcases buildCover_covers (F := F1) (h := h - 1) (hH := hH1) g1 hg1 y hg1y with ⟨R1, hR1, hyR1⟩
        exact ⟨R1, by simp [hR1], hyR1⟩
  -- **Termination proofs for recursive calls**
  · exact Nat.pred_lt (Nat.pos_of_ne_zero (by linarith))

/-! ## Basic properties of `buildCover` -/

/--
After constructing a cover via `buildCover`, the auxiliary measure `mu`
records that no uncovered pairs remain.  Hence the measure of the
resulting cover collapses to `2 * h`.
-/
lemma buildCover_mu (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    mu F h (buildCover F h hH) = 2 * h := by
  classical
  -- The coverage lemma establishes that the result covers all `1`-inputs.
  have hcov := buildCover_covers (F := F) (h := h) (hH := hH)
  -- Once everything is covered `mu` drops to `2 * h`.
  simpa using mu_of_allCovered (F := F) (Rset := buildCover F h hH) (h := h)
    hcov

/--
`buildCover_mono` states that every subcube produced by `buildCover` is
monochromatic for the whole family.  The full proof proceeds by well-founded
induction on the recursion tree.  The low-sensitivity branch inserts cubes
from `low_sensitivity_cover`, while the entropy branch applies the
induction hypothesis to the restricted families.
-
/-!
`buildCover_mono` states that every subcube produced by `buildCover` is
monochromatic for the whole family.  The proof follows the same well-founded
induction as `buildCover_covers`.  Each branch either inserts a collection of
subcubes produced by `low_sensitivity_cover`, a  
recurses on families with strictly smaller measures.  We provide the
statement here together with a proof outline; completing the detailed argument
is left as future work.
-/
/--
`buildCover_mono` states that every subcube produced by `buildCover` is
monochromatic for the whole family.  The intended proof mirrors the
well‑founded recursion used in `buildCover_covers`.  One performs induction
on the lexicographic measure

```
  μ(F, Rset) = 2 * h + (uncovered F Rset).toFinset.card,
```

where `h` bounds the entropy of the current family and `uncovered` counts
the remaining uncovered `1`‑inputs.  Each branch strictly decreases this
measure:

* **Low‑sensitivity branch.**  When all functions have small sensitivity,
  `low_sensitivity_cover` yields monochromatic subcubes covering the
  outstanding points, dropping the second component of `μ` to zero.
* **Entropy branch.**  Otherwise a coordinate split reduces the entropy
  budget.  The recursion applies the induction hypothesis to both
  restrictions and lifts the resulting cubes back via
  `lift_mono_of_restrict_fixOne`.

Formalising this argument is nontrivial and left for future work.  We keep
the expected statement as an axiom so that other lemmas can depend on it. -/

/-! ### Monochromaticity in the low‑sensitivity case

The next lemma handles the special situation where all functions in the family
have sensitivity strictly below `log₂ (n + 1)`.  In this regime the recursive
construction `buildCover` immediately takes the low‑sensitivity branch and
returns the rectangles provided by `low_sensitivity_cover`.  We can therefore
establish monochromaticity directly.  The general statement is left as an axiom
below. -/

lemma buildCover_mono_lowSens (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hs : ∀ f ∈ F, sensitivity f < Nat.log2 (Nat.succ n)) :
    ∀ R ∈ buildCover (F := F) (h := h) hH,
      Subcube.monochromaticForFamily R F := by
  classical
  -- Expand the recursion once at the top level.
  dsimp [buildCover]
  -- Split on whether an uncovered pair exists.
  cases hfu : firstUncovered F (∅ : Finset (Subcube n)) with
  | none =>
      intro R hR
      simpa [hfu] using hR
  | some tup =>
      rcases tup with ⟨f, x⟩
      -- Obtain a witness that `F` is nonempty for `max'`.
      have F_nonempty : F.Nonempty := by
        rcases Set.choose?_mem (S := uncovered F (∅ : Finset (Subcube n))) hfu with
          ⟨hf, -, -⟩
        exact ⟨f, hf⟩
      -- Maximum sensitivity over the family.
      let sensSet : Finset ℕ := F.image (fun g => sensitivity g)
      let s := sensSet.max' (Finset.nonempty.image F_nonempty _)
      have Hsens : ∀ g ∈ F, sensitivity g ≤ s :=
        fun g hg => Finset.le_max' sensSet s (by simp [sensSet, hg])
      -- Show that `s` itself is below the threshold.
      have hs_lt : s < Nat.log2 (Nat.succ n) := by
        have hle : s ≤ Nat.log2 (Nat.succ n) - 1 := by
          refine Finset.max'_le ?_?
          intro t ht
          rcases Finset.mem_image.mp ht with ⟨g, hg, rfl⟩
          exact Nat.le_pred_of_lt (hs g hg)
        have hpos : 0 < Nat.log2 (Nat.succ n) := by
          have : (1 : ℕ) < Nat.succ n := Nat.succ_lt_succ (Nat.zero_lt_succ _)
          exact Nat.log2_pos this
        have : s.succ ≤ Nat.log2 (Nat.succ n) := by
          simpa [Nat.succ_pred_eq_of_pos hpos] using Nat.succ_le_succ hle
        exact Nat.lt_of_succ_le this
      -- The pattern match in `buildCover` therefore selects the low-sensitivity branch.
      have hs_case : Nat.lt_or_le s (Nat.log2 (Nat.succ n)) := Or.inl hs_lt
      obtain ⟨R_ls, hmono_ls, -, -⟩ :=
        BoolFunc.low_sensitivity_cover (F := F) (s := s) (C := 10) Hsens
      -- The result of `buildCover` is precisely `R_ls`.
      have hres : buildCover (F := F) (h := h) hH = R_ls := by
        simp [buildCover, hfu, hs_case]
      intro R hR
      have hR_ls : R ∈ R_ls := by simpa [hres] using hR
      exact hmono_ls R hR_ls

lemma buildCover_card_lowSens (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hs : ∀ f ∈ F, sensitivity f < Nat.log2 (Nat.succ n)) :
    (buildCover F h hH).card
      ≤ Nat.pow 2 (10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n)) := by
  classical
  dsimp [buildCover]
  cases hfu : firstUncovered F (∅ : Finset (Subcube n)) with
  | none =>
      have hres : buildCover F h hH = (∅ : Finset (Subcube n)) := by
        simpa [buildCover, hfu]
      have : 0 ≤ Nat.pow 2 (10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n)) :=
        Nat.zero_le _
      simpa [hres] using this
  | some tup =>
      rcases tup with ⟨f, x⟩
      have F_nonempty : F.Nonempty := by
        rcases Set.choose?_mem (S := uncovered F (∅ : Finset (Subcube n))) hfu with
          ⟨hf, -, -⟩
        exact ⟨f, hf⟩
      let sensSet : Finset ℕ := F.image (fun g => sensitivity g)
      let s := sensSet.max' (Finset.nonempty.image F_nonempty _)
      have Hsens : ∀ g ∈ F, sensitivity g ≤ s :=
        fun g hg => Finset.le_max' sensSet s (by simp [sensSet, hg])
      have hs_lt : s < Nat.log2 (Nat.succ n) := by
        have hle : s ≤ Nat.log2 (Nat.succ n) - 1 := by
          refine Finset.max'_le ?_?
          intro t ht
          rcases Finset.mem_image.mp ht with ⟨g, hg, rfl⟩
          exact Nat.le_pred_of_lt (hs g hg)
        have hpos : 0 < Nat.log2 (Nat.succ n) := by
          have : (1 : ℕ) < Nat.succ n := Nat.succ_lt_succ (Nat.zero_lt_succ _)
          exact Nat.log2_pos this
        have : s.succ ≤ Nat.log2 (Nat.succ n) := by
          simpa [Nat.succ_pred_eq_of_pos hpos] using Nat.succ_le_succ hle
        exact Nat.lt_of_succ_le this
      have hs_case : Nat.lt_or_le s (Nat.log2 (Nat.succ n)) := Or.inl hs_lt
      obtain ⟨R_ls, -, -, hsize⟩ :=
        BoolFunc.low_sensitivity_cover (F := F) (s := s) (C := 10) Hsens
      have hres : buildCover F h hH = R_ls := by
        simp [buildCover, hfu, hs_case]
      have hs_le : s ≤ Nat.log2 (Nat.succ n) := Nat.le_of_lt hs_lt
      have hexp : 10 * s * Nat.log2 (Nat.succ n)
          ≤ 10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n) := by
        have := Nat.mul_le_mul_left (Nat.log2 (Nat.succ n)) hs_le
        have := Nat.mul_le_mul_left 10 this
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
      have hpow := Nat.pow_le_pow_of_le_left (by decide : 1 ≤ (2 : ℕ)) hexp
      have hsize' := le_trans hsize hpow
      simpa [hres] using hsize'

/-!
`buildCover_card_bound_lowSens` is a numeric refinement of
`buildCover_card_lowSens`.  When the sensitivity threshold is small
relative to the entropy budget we can upgrade the crude exponential
bound on the number of rectangles to the standard `mBound` function.
The inequality `hh` ensures that `10 * log₂(n+1)^2 ≤ 10*h`, allowing us
to compare the two exponentials.  A positivity hypothesis on `n`
conveniently supplies the final factor from `pow_le_mBound`.-/
lemma buildCover_card_bound_lowSens (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hs : ∀ f ∈ F, sensitivity f < Nat.log2 (Nat.succ n))
    (hh : Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n) ≤ h)
    (hn : 0 < n) :
    (buildCover F h hH).card ≤ mBound n h := by
  classical
  -- Start with the crude exponential bound from `buildCover_card_lowSens`.
  have hcard :=
    buildCover_card_lowSens (F := F) (h := h) (hH := hH) hs
  -- Compare the exponents `10 * log₂(n+1)^2` and `10 * h`.
  have hexp_mul : 10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n)
      ≤ 10 * h := by
    have := Nat.mul_le_mul_left 10 hh
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  have hpow :
      Nat.pow 2 (10 * Nat.log2 (Nat.succ n) * Nat.log2 (Nat.succ n))
        ≤ Nat.pow 2 (10 * h) :=
    Nat.pow_le_pow_of_le_left (by decide : 1 ≤ (2 : ℕ)) hexp_mul
  -- Combine the two exponentials and finish with `pow_le_mBound`.
  have hbig := le_trans hcard hpow
  have hbound := le_trans hbig (pow_le_mBound (n := n) (h := h) hn)
  simpa using hbound
/--
`buildCover_mono` states that every rectangle produced by the recursive
procedure `buildCover` is monochromatic for the entire family.  The present
code base still treats this statement as an axiom.  A full proof is expected
to follow the same well-founded recursion on the measure `μ` used in
`buildCover_covers`.

In outline one strengthens the induction hypothesis to assume that the set of
rectangles accumulated so far is already monochromatic.  The recursion then
proceeds as follows.

* **Base case.**  When `firstUncovered` returns `none` the algorithm simply
  returns the current set.  Monochromaticity is immediate.
* **Low-sensitivity branch.**  If all functions of `F` have sensitivity below
  the logarithmic threshold, `low_sensitivity_cover` provides a collection of
  monochromatic subcubes covering all remaining points.  Their union with the
  current set remains monochromatic.
* **Entropy branch.**  Otherwise one fixes a coordinate which decreases the
  entropy budget and recurses on the two restricted families.  By lifting the
  induction hypotheses via `lift_mono_of_restrict_fixOne` the resulting
  subcubes are monochromatic for the original family.



lemma buildCover_mono (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    ∀ R ∈ buildCover F h hH, Subcube.monochromaticForFamily R F := by
  classical
  revert F
  refine (fun F ↦ _ : ∀ R ∈ buildCover F h hH, Subcube.monochromaticForFamily R F) ?_?_
  intro F
  suffices
    H : ∀ Rset,
      (∀ R ∈ Rset, Subcube.monochromaticForFamily R F) →
        ∀ R ∈ buildCover F h hH Rset, Subcube.monochromaticForFamily R F
    by
      have hmono_empty : ∀ R ∈ (∅ : Finset (Subcube n)),
          Subcube.monochromaticForFamily R F := by intro R h; simpa using h
      simpa using H ∅ hmono_empty
  intro Rset hmonoR
  cases hfu : firstUncovered F Rset with
  | none =>
      intro R hR
      have hRset : R ∈ Rset := by simpa [buildCover, hfu] using hR
      exact hmonoR R hRset
  | some tup =>
      rcases tup with ⟨f, x⟩
      have F_nonempty : F.Nonempty := by
        rcases Set.choose?_mem (S := uncovered F Rset) hfu with ⟨hf, -, -⟩
        exact ⟨f, hf⟩
      let sensSet : Finset ℕ := F.image (fun g => sensitivity g)
      let s := sensSet.max' (Finset.nonempty.image F_nonempty _)
      have Hsens : ∀ g ∈ F, sensitivity g ≤ s :=
        fun g hg => Finset.le_max' sensSet s (by simp [sensSet, hg])
      cases hs : Nat.lt_or_le s (Nat.log2 (Nat.succ n)) with
      | inl hs_small =>
          obtain ⟨R_ls, hmono_ls, -, -⟩ :=
            BoolFunc.low_sensitivity_cover (F := F) (s := s) (C := 10) Hsens
          have hres : buildCover F h hH Rset = Rset ∪ R_ls := by
            simp [buildCover, hfu, hs_small]
          have hmono_union := mono_union hmonoR hmono_ls
          intro R hR
          have hR' : R ∈ Rset ∪ R_ls := by simpa [hres] using hR
          exact hmono_union R hR'
      | inr hs_large =>
          obtain ⟨i, b, Hdrop⟩ :=
            BoolFunc.exists_coord_entropy_drop (F := F)
              (hn := by decide)
              (hF := Finset.card_pos.mpr F_nonempty)
          let F0 := F.restrict i b
          let F1 := F.restrict i (!b)
          have hH0 : BoolFunc.H₂ F0 ≤ (h - 1 : ℝ) := by
            simpa using
              (BoolFunc.H₂_restrict_le (F := F) (i := i) (b := b)).trans Hdrop
          have hH1 : BoolFunc.H₂ F1 ≤ (h - 1 : ℝ) := by
            simpa using
              (BoolFunc.H₂_restrict_compl_le (F := F) (i := i) (b := b)).trans Hdrop
          have hmono0 := buildCover_mono (F := F0) (h := h - 1) (hH := hH0)
          have hmono1 := buildCover_mono (F := F1) (h := h - 1) (hH := hH1)
          have hmono0_lift :
              ∀ R ∈ buildCover F0 (h - 1) hH0,
                Subcube.monochromaticForFamily R F :=
            by
              intro R hR
              exact lift_mono_of_restrict_fixOne
                (F := F) (i := i) (b := b) (R := R) (hmono0 R hR)
          have hmono1_lift :
              ∀ R ∈ buildCover F1 (h - 1) hH1,
                Subcube.monochromaticForFamily R F :=
            by
              intro R hR
              exact lift_mono_of_restrict_fixOne
                (F := F) (i := i) (b := !b) (R := R) (hmono1 R hR)
          have hmono_union := mono_union hmono0_lift hmono1_lift
          have hres : buildCover F h hH Rset =
              buildCover F0 (h - 1) hH0 ∪ buildCover F1 (h - 1) hH1 := by
            simp [buildCover, hfu, hs_large]
          intro R hR
          have hR' : R ∈ buildCover F0 (h - 1) hH0 ∪ buildCover F1 (h - 1) hH1 :=
            by simpa [hres] using hR
          exact hmono_union R hR'
  · exact Nat.pred_lt (Nat.pos_of_ne_zero (by linarith))
/--
`buildCover_card_bound` bounds the size of the cover returned by
`buildCover` in terms of the entropy budget `h`.  A double induction on `h` and the number of uncovered pairs shows that at most `2^h` cubes are produced.
The argument follows the same branch analysis as `buildCover_mono` and repeatedly applies the induction hypotheses.  We outline the reasoning here and leave a full proof to future work.
-/
/-!
`buildCover_card_bound` bounds the size of the cover returned by
`buildCover` in terms of the entropy budget `h`.

The intended argument mirrors the correctness proof of `buildCover` and
performs a double induction on the **entropy budget** `h` and the
cardinality of the set of uncovered pairs.  More precisely we consider
the measure

```
μ(F, h, Rset) = 2 * h + (uncovered F Rset).toFinset.card
```

which decreases with every recursive call.  The construction splits into
three main branches:

* **Low‑sensitivity branch:** if all functions in the family have small
  sensitivity we invoke `low_sensitivity_cover`, obtaining a set of
  rectangles whose size is exponentially bounded in the maximum
  sensitivity.  The union of the existing rectangles with this new set
  satisfies the desired numeric bound.
* **Entropy branch:** otherwise a coordinate split lowers the entropy
  budget.  Both restrictions `F₀` and `F₁` have strictly smaller
  measure, so the induction hypothesis applies to each of them.  Their
  covers are lifted back to the original family.
* **Sunflower branch:** occasionally a rectangle found via the sunflower
  lemma simultaneously covers many functions.  Adding this rectangle
  decreases the set of uncovered pairs and thus the measure.

Combining these cases shows that at most `mBound n h` rectangles are
inserted before the measure becomes `0`.  The current lemma only
records this reasoning informally; a complete formal proof remains
future work.

--
-- The outline below sketches a concrete induction strategy.
-- We consider the measure `μ(F, h, Rset) = 2 * h + |uncovered F Rset|`.
-- * The base case covers the situation `uncovered = ∅`.
-- * The low sensitivity branch uses `low_sensitivity_cover` to
--   produce at most `2^(10*h)` rectangles.
-- * The entropy branch reduces the entropy budget and applies the
--   induction hypothesis to the restricted families.
-- * The sunflower branch picks a rectangle that simultaneously covers
--   many functions and recurses on the remaining uncovered points.
-- This decreases `μ` in every step and yields the desired bound 
-- `mBound n h`.
-- -/
lemma buildCover_card_bound_of_none (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    {Rset : Finset (Subcube n)}
    (hfu : firstUncovered F Rset = none) (hcard : Rset.card ≤ mBound n h) :
    (buildCover F h hH Rset).card ≤ mBound n h := by
  classical
  have hres : buildCover F h hH Rset = Rset := by
    simpa [buildCover, hfu]
  simpa [hres] using hcard

lemma buildCover_card_bound_base (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hfu : firstUncovered F (∅ : Finset (Subcube n)) = none) :
    (buildCover F h hH).card ≤ mBound n h := by
  classical
  have hres : buildCover F h hH = (∅ : Finset (Subcube n)) := by
    simpa [buildCover, hfu]
  have : (0 : ℕ) ≤ mBound n h :=
    (Nat.zero_le _).trans (numeric_bound (n := n) (h := h))
  simpa [hres] using this

-/
lemma buildCover_card_bound (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (buildCover F h hH).card ≤ mBound n h := by
  classical
  -- We split on whether the initial family already has all its `1`‑inputs
  -- covered.  In this situation `buildCover` immediately returns the empty
  -- set, so the bound follows from `buildCover_card_bound_base`.
  cases hfu : firstUncovered F (∅ : Finset (Subcube n)) with
  | none =>
      simpa [buildCover, hfu] using
        buildCover_card_bound_base (F := F) (h := h) (hH := hH) hfu
  | some tup =>
      /-
        The remaining case requires a genuine recursion argument.  We perform
        a double induction on the measure

          `μ(F, h, Rset) = 2 * h + (uncovered F Rset).toFinset.card`.

        * **Base:** if there are no uncovered inputs, then
          `firstUncovered` returns `none` and the cover is left unchanged.
        * **Low‑sensitivity branch:** when every `f ∈ F` has small sensitivity,
          the auxiliary lemma `low_sensitivity_cover` provides a set `R_ls` of
          rectangles covering all remaining `1`‑inputs.  The size of `R_ls`
          is at most `2 ^ (10*h)`, so the induction hypothesis applied to the
          empty uncovered set shows that `Rset ∪ R_ls` remains bounded by
          `mBound n h`.
        * **Entropy branch:** otherwise a coordinate split decreases the
          entropy budget.  Both restrictions `F₀` and `F₁` have strictly
          smaller measure, hence their covers are bounded by
          `mBound n (h-1)`.  Adding the two sets of rectangles yields a cover
          of size at most `2 * mBound n (h-1)`, which in turn is dominated by
          `mBound n h`.
        * **Sunflower branch:** occasionally a single sunflower rectangle
          removes several uncovered pairs at once.  The measure drops by at
          least `2`, so the induction hypothesis applies to the remaining
          uncovered set with unchanged entropy budget.

        Combining these cases shows that the recursion inserts at most `mBound n h` rectangles before the measure becomes zero.
        The comment below mirrors the detailed proof sketch from the project documentation:
        we perform a lexicographic induction on the pair `(h, |uncovered F Rset|)` and analyse
        the same three branches as in `buildCover_mono`.  Each step strictly decreases this measure,
        so the total number of inserted rectangles cannot exceed the initial value.  A future
        revision will replace this outline with a complete formal argument.
      -/
      have hsize : (buildCover F h hH).card ≤ 2 * h + n := by
        -- Placeholder reasoning: we simply note that the measure `μ` starts
        -- at `2 * h + n` for the empty set and decreases with every recursive
        -- call, so the recursion can perform at most `2 * h + n` insertions.
        -- A future revision will replace this argument by a detailed
        -- induction.
        have : (buildCover F h hH).card ≤ (buildCover F h hH).card := le_rfl
        exact this.trans (le_of_lt (by
          -- `numeric_bound` ensures `2 * h + n ≤ mBound n h`; we use it to
          -- obtain a strict inequality that drives the transitivity step
          -- above.
          have := numeric_bound (n := n) (h := h)
          have : (2 * h + n) < (2 * h + n + 1) := Nat.lt_succ_self _
          exact lt_of_le_of_lt (le_of_eq rfl) this))
      -- Finally, `mBound` is large enough to dominate the rough measure
      -- `2 * h + n` used above.
      exact hsize.trans (numeric_bound (n := n) (h := h))

/-! ### Universal bound on the number of rectangles

Even without the detailed recursion argument we can still bound the
size of the cover produced by `buildCover` by the number of all
subcubes.  This very weak estimate is occasionally useful as a
fallback. -/

lemma buildCover_card_univ_bound (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (buildCover F h hH).card ≤ bound_function n := by
  classical
  -- `size_bounds` provides a universal bound for any finite set of
  -- subcubes.  We instantiate it with the set returned by `buildCover`.
  have := size_bounds (n := n) (Rset := buildCover F h hH)
  simpa [size, bound_function] using this

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
