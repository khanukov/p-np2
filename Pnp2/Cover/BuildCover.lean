import Pnp2.Cover.Uncovered
import Pnp2.Cover.Measure
import Pnp2.Cover.Bounds
import Pnp2.Cover.SunflowerStep
import Pnp2.low_sensitivity_cover

/-!
This file supplies the recursive core of the covering construction.  The
original development used a trivial stub for `buildCover` that merely
performed a single call to `extendCover`.  Rewriting the function using a
well‑founded recursion on the measure `μ` avoids difficult termination issues
for the accompanying lemmas.

The actual correctness proofs are substantial and remain works in progress.
We nevertheless expose the intended API so that other parts of the repository
can already rely on the interface.  Lemmas that still await a complete proof
are currently stated as axioms.  They can be filled in once the missing
arguments have been formalised.
-/

open Classical
open Finset
open BoolFunc (Family BFunc)
open Boolcube (Point Subcube)

namespace Cover2

variable {n : ℕ}

/--  Auxiliary relation stating that one rectangle set has a smaller measure
than another.  This relation is well‑founded because the measure takes values
in the natural numbers. -/
def μRel (F : Family n) (h : ℕ) :
    Finset (Subcube n) → Finset (Subcube n) → Prop :=
  fun R₁ R₂ => mu (n := n) F h R₁ < mu (n := n) F h R₂

/--  `μRel` is a well‑founded relation, enabling recursion on the measure. -/
lemma μRel_wf (F : Family n) (h : ℕ) :
    WellFounded (μRel (n := n) (F := F) h) := by
  -- The relation `μRel` is the inverse image of `<` on `ℕ` under the measure
  -- `μ`.  Well‑foundedness therefore follows from the well‑foundedness of
  -- `<` on the natural numbers.
  simpa [μRel] using
    (InvImage.wf (f := fun Rset : Finset (Subcube n) => mu (n := n) F h Rset)
      Nat.lt_wfRel.wf)

/--  A rectangle set cannot have a strictly smaller measure than itself. -/
lemma μRel_irrefl (F : Family n) (h : ℕ) (Rset : Finset (Subcube n)) :
    ¬ μRel (n := n) (F := F) h Rset Rset := by
  intro hlt
  -- The measure `μ` takes values in `ℕ`, where `<` is irreflexive.
  exact lt_irrefl _ hlt

/-!
### Recursive cover construction

`buildCoverAux` implements the recursion directly via `WellFounded.fix`.
The function searches for an uncovered pair. If none exists we return the
current rectangle set. Otherwise, we choose one of three strategies:
1. Low-sensitivity: If all functions have low sensitivity, use a decision-tree cover.
2. Sunflower: If the family of supports is large, extract a sunflower.
3. Entropy-drop: As a fallback, split on a coordinate and recurse.
-/

noncomputable def buildCoverAux (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) [Fintype (Point n)] :
    (Rset : Finset (Subcube n)) → Finset (Subcube n) :=
  (μRel_wf (n := n) (F := F) h).fix
    (fun Rset rec =>
      -- If all 1-points are covered, we are done.
      if hfu : firstUncovered (n := n) F Rset = none then
        Rset
      else
        -- Low-sensitivity branch
        if h_sens : ∀ f ∈ F, BoolFunc.sensitivity f ≤ n.log2 then
          -- Use the low-sensitivity cover to handle all remaining points.
          let sens_cover_exists := low_sensitivity_cover F n.log2 h_sens
          let Rset_sens := Classical.choose sens_cover_exists
          let R' := Rset ∪ Rset_sens
          -- Prove that this step makes progress.
          have hdrop : μRel (n := n) (F := F) h R' Rset := by
            -- The low-sensitivity cover covers all 1-points.
            have h_sens_covers_all := (Classical.choose_spec sens_cover_exists).2.1
            -- Therefore, the union covers all 1-points.
            have h_all_covered_final: AllOnesCovered F R' := by
              intro f hf x hx_true
              by_cases h_old_covered: ∃ R_old ∈ Rset, x ∈ₛ R_old
              · rcases h_old_covered with ⟨R_old, hR_old_mem, hx_in_R_old⟩
                exact ⟨R_old, mem_union_left _ hR_old_mem, hx_in_R_old⟩
              · -- If not covered by the old set, it must be covered by the new one.
                rcases h_sens_covers_all f hf x hx_true with ⟨R_sens, h_sens_mem, hx_in_R_sens⟩
                exact ⟨R_sens, mem_union_right _ h_sens_mem, hx_in_R_sens⟩
            -- An all-covering set makes the measure `2*h`.
            have h_mu_new : mu F h R' = 2 * h := mu_of_allCovered h_all_covered_final
            -- The old measure was strictly greater than `2*h` because `hfu` was not `none`.
            have h_mu_old_gt : 2 * h < mu F h Rset := mu_gt_of_firstUncovered_some hfu
            -- Therefore, the new measure is smaller.
            rw [h_mu_new]
            exact h_mu_old_gt
          -- The recursion will terminate in the next step.
          rec R' hdrop
        -- Sunflower branch
        else if h_sun : ∃ p t, Sunflower.threshold p t < (Family.supports F).card then
          -- Extract p and t from the hypothesis
          let ⟨p, t, h_big⟩ := h_sun
          -- Call the sunflower_step lemma, admitting the missing hypotheses for now.
          have R_exists : ∃ (R : Subcube n), ((F.filter fun f => ∀ x, Subcube.Mem R x → f x = true).card ≥ t) ∧ 1 ≤ R.dim := by
            -- The actual implementation would need to find a uniform subfamily and prove agreement properties.
            -- For now, we admit the necessary conditions to proceed with the structure.
            have hp_pos : 0 < p := by admit
            have ht_ge_2 : 2 ≤ t := by admit
            have h_support_uniform : ∀ f ∈ F, (BoolFunc.support f).card = p := by admit
            have h_agree_axiom : ∀ (S : SunflowerFam n t), S.petals ⊆ Family.supports F → ∀ A ∈ S.petals, ∃ f ∈ F, BoolFunc.support f = A ∧ (∀ x y, (∀ i ∈ S.core, x i = y i) → f x = f y) := by admit
            have h_true_axiom : ∀ f ∈ F, f (fun _ => false) = true := by admit
            exact sunflower_step F p t hp_pos ht_ge_2 h_big h_support_uniform h_agree_axiom h_true_axiom
          let R_sun := Classical.choose R_exists
          let R' := Rset ∪ {R_sun}
          -- Prove that this step makes progress. This also requires assumptions about what the sunflower covers.
          have hdrop : μRel (n := n) (F := F) h R' Rset := by
            -- This proof is non-trivial and depends on showing that R_sun covers at least one point from the `uncovered` set.
            admit
          rec R' hdrop
        -- Entropy-drop branch
        else
          sorry
    )

/--  Top‑level wrapper starting the recursion from the empty set. -/
noncomputable def buildCover (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) : Finset (Subcube n) :=
  buildCoverAux (n := n) (F := F) (h := h) (hH := hH) ∅

-- The following are stubs and need to be proven for the new `buildCoverAux`
lemma buildCover_pointwiseMono (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    ∀ R ∈ buildCover (n := n) F h hH, ∀ g ∈ F,
      Boolcube.Subcube.monochromaticFor R g := by sorry

lemma buildCover_covers (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    AllOnesCovered (n := n) F (buildCover (n := n) F h hH) := by sorry

lemma buildCover_card_bound (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (buildCover (n := n) F h hH).card ≤ 2 ^ n := by sorry

lemma buildCover_card_le_mBound (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) (hn : 0 < n) (hlarge : n ≤ 5 * h) :
    (buildCover (n := n) F h hH).card ≤ mBound n h := by sorry

end Cover2