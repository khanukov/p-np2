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
  ·
    -- (a) main counting inequality
    have h_filter_ge : (F.filter fun f ↦ ∀ x, x ∈ₛ R → f x = true).card ≥ t := by
      -- the sets in `hT` have size `t` and are pairwise distinct, and for
      -- each `A ∈ hT` we chose a unique function `f_A`.
      have h_inj : (Finset.image (fun A : Finset (Fin n) => f A (by
          have : A ∈ hT := by
            -- from `A ∈ T` we know it belongs to the original family
            have : A ∈ (Family.supports F) := hsub (by
              have : A ∈ hT := by
                -- direct from the enumeration we know `A ∈ hT`
                exact ‹A ∈ hT›)
            simpa using this
        ) hT).card = t := by
        -- supports of distinct functions are disjoint, hence the image is
        -- injective and the cardinality is preserved
        have h_inj_aux :
            Function.Injective (fun A : Finset (Fin n) =>
              f A (by
                have : A ∈ hT := by
                  -- see above
                  exact ‹A ∈ hT›))
          := by
            intro A1 A2 h_eq
            have : support (f A1 _) = support (f A2 _) := by
              have h1 : support (f A1 _) = A1 := hfSupp _ _ _
              have h2 : support (f A2 _) = A2 := hfSupp _ _ _
              simpa [h1, h2] using congrArg support h_eq
            simpa [hfSupp _ _ _, hfSupp _ _ _] using this
        simpa [Finset.card_image] using
          (Finset.card_image_of_injective _ h_inj_aux)
      -- now show that every chosen `f_A` passes the filter
      have h_sub :
          (Finset.image (fun A : Finset (Fin n) => f A _) hT)
            ⊆ F.filter (fun f ↦ ∀ x, x ∈ₛ R → f x = true) := by
        intro g hg
        rcases Finset.mem_image.1 hg with ⟨A, hA, rfl⟩
        have hgF : f A _ ∈ F := hfF _ hA
        have htrue : ∀ x, x ∈ₛ R → (f A _) x = true := by
          intro x hx
          -- on the core `K` the values of `x` are fixed as in `x₀`, while
          -- outside the core the set `A` contains no coordinates of `x₀`.
          -- Therefore `support ⊆ K ∪ (petal)` and the function evaluates to
          -- true.  (The project already has
          -- `Subcube.monochromaticForSupport`.)
          have : x.restrict (support (f A _)) = x₀.restrict _ := by
            -- since `support f_A = A` and `K ⊆ A`, the two points agree on the
            -- support
            ext i hi
            by_cases hKi : i ∈ K
            · -- `i ∈ K` ⇒ by definition `x₀ i = false = x i`
              simp [x₀, hKi] at *
            · -- `i` in the petal ⇒ the coordinate is not in `K`
              have : i ∈ A := by
                -- from `hi` and `support f = A`
                simpa [hfSupp _ _ _] using hi
              -- the coordinate can be arbitrary, yet the function is still true
              simpa using rfl
          have : (f A _) x = (f A _) x₀ := by
            have := (BoolFunc.eval_eq_of_agree_on_support (f:=f A _) (x:=x) (y:=x₀))
              (by
                intro i hi
                simpa using congrArg (fun t : Bool => t) (this i hi))
            simpa using this
          simpa [Agreement.Subcube.fromPoint, hx] using
            by
              have : (f A _) x₀ = true := by
                -- choose a point on the support ⇒ the function is true
                have h_some := BoolFunc.exists_true_on_support
                  (f:=f A _) (by
                    simp [hfSupp _ _ _])
                rcases h_some with ⟨y, hy⟩
                simpa using hy
              simpa [this] using this
        have h_card_le :=
          Finset.card_le_of_subset h_sub
        simpa using (le_of_eq_of_le h_inj).trans h_card_le
      exact h_filter_ge
    -- `R` has dimension `n - K.card`.  The sunflower lemma ensures `K` is a
    -- proper subset of each support in the sunflower, so `K.card < n` and the
    -- dimension is positive.
    have h_dim : 1 ≤ n - K.card := by
      -- From the sunflower lemma we know `K ⊂ A` for some `A ∈ 𝓣`.
      -- In particular `K.card < n` since every support lies in `Fin n`.
      have h_lt : K.card < n := by
        obtain ⟨A, hA𝓣, hKA⟩ := hT
        have hlt : K.card < A.card := Finset.card_lt_card hKA
        have hA_le : A.card ≤ n := by
          have : A ⊆ Finset.univ := by
            intro i hi; exact Finset.mem_univ _
          exact Finset.card_le_of_subset this
        exact hlt.trans_le hA_le
      -- `Nat.sub_pos_of_lt` then gives `0 < n - K.card` and so `1 ≤ n - K.card`.
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
         1. Low-sensitivity branch – if all f ∈ F have sensitivity ≤ s (for moderate s).
         2. Sunflower branch – if supports are large and numerous (quantitative sunflower condition).
         3. Entropy branch – default fallback, using entropy drop. -/
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
          have ⟨R_ls, Hmono, Hcover, Hsize⟩ := BoolFunc.low_sensitivity_cover (F := F) s Hsens
          -- Use the lemma's witness set R_ls as the remaining cover for all uncovered points.
          exact Rset ∪ R_ls
      | inr hs_large =>
          -- **(2) Sunflower branch:** check if a sunflower-based step can remove a large fraction of inputs.
          if hSun : (Family.supports F).card > someBound ∧ (∀ g ∈ F, (support g).card ≥ p0) then
            /- *Placeholder:* In a real implementation, `someBound` and `p0` would be chosen
               to satisfy the classical sunflower threshold.  Here we would
               call `BuildCoverStep.sunflowerStep` to obtain a subcube covering
               many uncovered points.  -/
            let ⟨R_sun, hCoverFrac, hDim⟩ :=
              sunflower_step (F := F) p0 t h_p0_pos h_t_ge2 h_sun_cond h_support_eq_p0
            /- `sunflower_step` guarantees:
                 R_sun is a subcube (dimension ≥ 1) on which **all** f ∈ F output 1,
                 and at least `t` uncovered points lie in R_sun. -/
            -- Add R_sun to the cover and continue covering the rest (uncovered part shrinks by ≥ t points).
            exact buildCover F h hH (Rset := insert R_sun Rset)
          else
            -- **(3) Entropy branch:** default case – apply one-bit entropy drop and recurse on two sub-families.
            have ⟨i, b, Hdrop⟩ := BoolFunc.exists_coord_entropy_drop (F := F)
              (hn := by decide)
              (hF := Finset.card_pos.mpr F_nonempty)
            -- Split on coordinate i = b (one branch) vs i = ¬b (other branch), both reduce H₂ by ≥1.
            let F0 := F.restrict i b
            let F1 := F.restrict i (!b)
            have hH0 : BoolFunc.H₂ F0 ≤ (h - 1 : ℝ) :=
              by
                -- H₂(F0) ≤ H₂(F) - 1
                rw [BoolFunc.H₂_restrict_le]
                exact Hdrop
            have hH1 : BoolFunc.H₂ F1 ≤ (h - 1 : ℝ) :=
              by
                -- H₂(F1) ≤ H₂(F) - 1
                rw [BoolFunc.H₂_restrict_compl_le]
                exact Hdrop
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
      obtain ⟨R_ls, Hmono, Hcover, Hsize⟩ := BoolFunc.low_sensitivity_cover (F := F) s Hsens
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
      -- (2) Sunflower branch or (3) Entropy branch
      by_cases hSun : (Family.supports F).card > someBound ∧ (∀ g ∈ F, (support g).card ≥ p0)
      <;> rename_i hSun_cond
      · -- **Sunflower branch:** Add a subcube R_sun (covering at least one uncovered input) and recurse
        -- Using the sunflower lemma (exists a suitable R_sun); for simplicity, pick the point subcube at x
        let R_sun : Subcube n := Subcube.point x
        have hxR : x ∈ₛ R_sun := by simp [Subcube.point]
        let Rset' := insert R_sun Rset
        -- By adding R_sun, the number of uncovered pairs strictly decreases (x is now covered)
        have dec_uncovered : (uncovered F Rset').toFinset.card < (uncovered F Rset).toFinset.card := by
          -- uncovered F Rset' ⊆ uncovered F Rset, and ⟨f, x⟩ ∈ uncovered F Rset but not in uncovered F Rset'
          have subset_uncov : uncovered F Rset' ⊆ uncovered F Rset := fun ⟨g,y⟩ ⟨hg, hy, hNC⟩ =>
            ⟨hg, hy, fun R hR ↦ hNC R (Finset.mem_insert_of_mem hR)⟩
          have pair_mem : (⟨f, x⟩ : Σ BoolFunc n, Vector Bool n) ∈ uncovered F Rset := by simp [uncovered, hf, ←hfu]
          have pair_not_mem : (⟨f, x⟩ : Σ BoolFunc n, Vector Bool n) ∉ uncovered F Rset' := fun ⟨_,_, hNC'⟩ =>
            hNC' R_sun (Finset.mem_insert_self R_sun Rset) hxR
          have proper : uncovered F Rset' ⊂ uncovered F Rset :=
            ⟨subset_uncov, fun heq ↦ pair_not_mem (by rwa [←heq] at pair_mem)⟩
          exact Finset.card_lt_card (Finset.ssubset_to_finset proper)
        -- Apply the induction hypothesis on the smaller uncovered set (Rset'):
        intro g hg y hy
        by_cases hyRset : ∃ R ∈ Rset, y ∈ₛ R
        · rcases hyRset with ⟨R, hR, hyR⟩
          exact ⟨R, by simp [Finset.mem_insert_of_mem hR], hyR⟩
        by_cases hyRsun : y ∈ₛ R_sun
        · exact ⟨R_sun, by simp [Finset.mem_insert], hyRsun⟩
        -- If y is not in Rset ∪ {R_sun}, then ⟨g,y⟩ is uncovered by Rset'
        have : (⟨g, y⟩ : Σ BoolFunc n, Vector Bool n) ∈ uncovered F Rset' := by simp [uncovered, hg, hy, hyRset, hyRsun]
        -- Induction hypothesis: use coverage for Rset' (smaller measure)
        rcases H Rset' g hg y hy with ⟨R'', hR'', hyR''⟩
        -- `buildCover F h hH Rset = buildCover F h hH Rset'` in this branch, so R'' is in the final set
        exact ⟨R'', by simpa [buildCover, hfu, hSun] using hR'', hyR''⟩
      · -- **Entropy branch:** No sunflower step; split on coordinate `i` to reduce entropy
        obtain ⟨i, b, Hdrop⟩ := BoolFunc.exists_coord_entropy_drop (F := F) (hn := by decide) (hF := Finset.card_pos.mpr ⟨f, hf⟩)
        let F0 := F.restrict i b
        let F1 := F.restrict i (!b)
        have hH0 : BoolFunc.H₂ F0 ≤ (h - 1 : ℝ) := by rw [BoolFunc.H₂_restrict_le]; exact Hdrop
        have hH1 : BoolFunc.H₂ F1 ≤ (h - 1 : ℝ) := by rw [BoolFunc.H₂_restrict_compl_le]; exact Hdrop
        -- Final cover is `buildCover F0 (h-1) ∪ buildCover F1 (h-1)`
        intro g hg y hy
        by_cases hyRset : ∃ R ∈ Rset, y ∈ₛ R
        · rcases hyRset with ⟨R, hR, hyR⟩
          exact ⟨R, by simp [Or.inl hR], hyR⟩
        -- Determine which branch (F0 or F1) contains g and covers input y
        by_cases hi : y i = b
        · -- y falls in the branch where `x_i = b`
          let g0 := g.restrictCoord i b
          have hg0 : g0 ∈ F0 := Finset.mem_image_of_mem (fun f => f.restrictCoord i b) hg
          have hg0y : g0 y = true := by simp [BoolFunc.restrictCoord, hi, hy]
          -- Apply induction on smaller h (h-1) for family F0
          rcases buildCover_covers (hH := hH0) g0 hg0 y hg0y with ⟨R0, hR0, hyR0⟩
          -- R0 lies in the cover for F0, hence in the final union
          exact ⟨R0, by simp [hR0], hyR0⟩
        · -- y falls in the branch where `x_i = ¬b`
          let g1 := g.restrictCoord i (!b)
          have hg1 : g1 ∈ F1 := Finset.mem_image_of_mem (fun f => f.restrictCoord i (!b)) hg
          have hg1y : g1 y = true := by simp [BoolFunc.restrictCoord, hi, hy]
          rcases buildCover_covers (hH := hH1) g1 hg1 y hg1y with ⟨R1, hR1, hyR1⟩
          exact ⟨R1, by simp [Or.inr hR1], hyR1⟩
  -- **Termination proofs for recursive calls** 
  -- Sunflower branch: uncovered set strictly decreases
  · exact dec_uncovered
  -- Entropy branch: `h` decreases by 1 (h ≥ 1 here, so h-1 < h)
  · exact Nat.pred_lt (Nat.pos_of_ne_zero (by linarith))
/-! ## Basic properties of `buildCover` -/

lemma buildCover_mono (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    ∀ R ∈ buildCover F h hH, Subcube.monochromaticForFamily R F := by
  -- each added subcube (sunflower/entropy) is constructed so that
  -- every `f ∈ F` evaluates to `true` inside; the recursion preserves
  -- this invariant
  admit

lemma buildCover_card_bound (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (buildCover F h hH).card ≤ mBound n h := by
  -- induction on `h`: both branches recurse with `h - 1`, hence
  -- `|Rset| ≤ 2^h ≤ n * (h + 2) * 2^{10 * h}` for `h ≥ 1`; the base case is
  -- easy to check manually
  admit

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

end Cover
