import Pnp4.Frontier.OneTapeMagnification.FiniteLayeredFamilySelectorUnambiguity
import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDOneRoundFoolingBound
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Component-first Fourier decomposition of a finite selector

The selector vertex decomposition is too fine for attacking the remaining
cardinality loss: it exposes a sum over every boundary/state slot before any
cross-component cancellation is used.  This module instead decomposes the
accepted **function** into its disjoint component indicators.

For an unambiguous family, the selector acceptance indicator is exactly the
sum of the component acceptance indicators.  Fourier projection and masked
uniform averaging commute with this sum.  The resulting second moment is
therefore exactly a double sum of component-pair correlations.

No pair bound is asserted.  The final identity is the insertion point for a
last-common-prefix/first-divergence charge or any other selector-specific
correlation estimate.  Pointwise disjointness of the original component
indicators alone does not control their projected cross terms.
-/

namespace FiniteLayeredQueryProgramFamily

open scoped BigOperators
open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open FiniteBooleanOneRoundFoolingBound
open FiniteUnambiguousFBDD

local instance familyIndexFintype {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) : Fintype family.Index :=
  family.indexFintype

/-- Rational indicator that one fixed family component accepts. -/
noncomputable def ratComponentAcceptanceIndicator {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) (index : family.Index)
    (input : Fin n → Bool) : ℚ := by
  classical
  exact if (family.program index).eval input = true then 1 else 0

/-- Unambiguity turns existential selector acceptance into an exact disjoint
sum of rational component indicators. -/
theorem selector_ratAcceptanceIndicator_eq_sum_components
    {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (hunambiguous : family.IsUnambiguous)
    (input : Fin n → Bool) :
    family.selectorFBDD.ratAcceptanceIndicator input =
      ∑ index : family.Index,
        family.ratComponentAcceptanceIndicator index input := by
  classical
  letI : Fintype family.Index := family.indexFintype
  by_cases haccepts : family.selectorFBDD.Accepts input
  · have heval : family.eval input = true :=
      (family.selectorFBDD_accepts_iff_eval_eq_true input).1 haccepts
    obtain ⟨chosen, hchosen⟩ := (family.eval_eq_true_iff input).1 heval
    unfold FiniteUnambiguousFBDD.ratAcceptanceIndicator
    rw [if_pos haccepts]
    symm
    calc
      (∑ index : family.Index,
          family.ratComponentAcceptanceIndicator index input) =
        family.ratComponentAcceptanceIndicator chosen input := by
          apply Finset.sum_eq_single chosen
          · intro index _ hne
            have hreject : (family.program index).eval input ≠ true := by
              intro hindex
              have heq := hunambiguous input index chosen hindex hchosen
              exact hne heq
            simp [ratComponentAcceptanceIndicator, hreject]
          · simp
      _ = 1 := by
        simp [ratComponentAcceptanceIndicator, hchosen]
  · have hreject (index : family.Index) :
        (family.program index).eval input ≠ true := by
      intro hindex
      exact haccepts
        (family.selectorFBDD_accepts_of_component_eval_true
          input index hindex)
    unfold FiniteUnambiguousFBDD.ratAcceptanceIndicator
    rw [if_neg haccepts]
    symm
    apply Finset.sum_eq_zero
    intro index _
    simp [ratComponentAcceptanceIndicator, hreject index]

/-! ## Fourier and restriction linearity -/

/-- The high-degree Fourier projection commutes with a sum over a finite
type. -/
theorem ratHighDegreeFourierTail_fintype_sum
    {n : Nat} {Index : Type} [Fintype Index]
    (f : Index → (Fin n → Bool) → ℚ) (k : Nat)
    (input : Fin n → Bool) :
    ratHighDegreeFourierTail
        (fun source => ∑ index : Index, f index source) k input =
      ∑ index : Index, ratHighDegreeFourierTail (f index) k input := by
  classical
  unfold ratHighDegreeFourierTail
  calc
    (∑ alpha : Finset (Fin n),
        if k < alpha.card then
          coefficient (fun source => ∑ index : Index, f index source) alpha *
            character alpha input
        else 0) =
      ∑ alpha : Finset (Fin n),
        if k < alpha.card then
          (∑ index : Index, coefficient (f index) alpha) *
            character alpha input
        else 0 := by
          apply Finset.sum_congr rfl
          intro alpha _
          by_cases hhigh : k < alpha.card
          · rw [if_pos hhigh, if_pos hhigh]
            rw [FiniteUnambiguousFBDD.coefficient_fintype_sum f alpha]
          · simp [hhigh]
    _ = ∑ alpha : Finset (Fin n), ∑ index : Index,
        if k < alpha.card then
          coefficient (f index) alpha * character alpha input
        else 0 := by
          apply Finset.sum_congr rfl
          intro alpha _
          by_cases hhigh : k < alpha.card
          · simp only [hhigh, if_true, Finset.sum_mul]
          · simp [hhigh]
    _ = ∑ index : Index, ∑ alpha : Finset (Fin n),
        if k < alpha.card then
          coefficient (f index) alpha * character alpha input
        else 0 := by
          rw [Finset.sum_comm]

/-- Component contribution to the signed masked uniform average of the
degree-`>k` Fourier tail. -/
noncomputable def componentHighTailAverage {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n)
    (index : family.Index) (k : Nat)
    (base mask : Fin n → Bool) : ℚ :=
  finiteAverage (fun uniform : Fin n → Bool =>
    ratHighDegreeFourierTail
      (family.ratComponentAcceptanceIndicator index) k
      (maskedInput base mask uniform))

/-- The masked high-tail average of the entire selector is exactly the sum
of the component-level high-tail averages. -/
theorem selector_highTailAverage_eq_sum_components
    {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (hunambiguous : family.IsUnambiguous)
    (k : Nat) (base mask : Fin n → Bool) :
    finiteAverage (fun uniform : Fin n → Bool =>
      ratHighDegreeFourierTail
        family.selectorFBDD.ratAcceptanceIndicator k
        (maskedInput base mask uniform)) =
      ∑ index : family.Index,
        family.componentHighTailAverage index k base mask := by
  classical
  letI : Fintype family.Index := family.indexFintype
  have hfunction : family.selectorFBDD.ratAcceptanceIndicator =
      fun input => ∑ index : family.Index,
        family.ratComponentAcceptanceIndicator index input := by
    funext input
    exact family.selector_ratAcceptanceIndicator_eq_sum_components
      hunambiguous input
  rw [hfunction]
  calc
    finiteAverage (fun uniform : Fin n → Bool =>
        ratHighDegreeFourierTail
          (fun input => ∑ index : family.Index,
            family.ratComponentAcceptanceIndicator index input) k
          (maskedInput base mask uniform)) =
      finiteAverage (fun uniform : Fin n → Bool =>
        ∑ index : family.Index,
          ratHighDegreeFourierTail
            (family.ratComponentAcceptanceIndicator index) k
            (maskedInput base mask uniform)) := by
        apply finiteAverage_congr
        intro uniform
        exact ratHighDegreeFourierTail_fintype_sum
          (fun index => family.ratComponentAcceptanceIndicator index)
          k (maskedInput base mask uniform)
    _ = ∑ index : family.Index,
        family.componentHighTailAverage index k base mask := by
      rw [finiteAverage_fintype_sum]
      rfl

/-! ## Exact pair-correlation insertion surface -/

/-- The second moment of a finite sum is the exact double sum of all ordered
pair correlations. -/
theorem finiteAverage_sq_fintype_sum_eq_sum_pair
    {Seed Index : Type*} [Fintype Seed] [Nonempty Seed] [Fintype Index]
    (value : Index → Seed → ℚ) :
    finiteAverage (fun seed : Seed =>
      (∑ index : Index, value index seed) ^ 2) =
      ∑ left : Index, ∑ right : Index,
        finiteAverage (fun seed : Seed =>
          value left seed * value right seed) := by
  calc
    finiteAverage (fun seed : Seed =>
        (∑ index : Index, value index seed) ^ 2) =
      finiteAverage (fun seed : Seed =>
        (∑ left : Index, value left seed) *
          (∑ right : Index, value right seed)) := by
            apply finiteAverage_congr
            intro seed
            rw [pow_two]
    _ = finiteAverage (fun seed : Seed =>
        ∑ left : Index, ∑ right : Index,
          value left seed * value right seed) := by
            apply finiteAverage_congr
            intro seed
            rw [Finset.sum_mul_sum]
    _ = ∑ left : Index, ∑ right : Index,
        finiteAverage (fun seed : Seed =>
          value left seed * value right seed) := by
      rw [finiteAverage_fintype_sum]
      apply Finset.sum_congr rfl
      intro left _
      rw [finiteAverage_fintype_sum]

/-- Exact component-pair expansion of the selector's masked high-tail second
moment.  Any future first-divergence theorem must bound the displayed ordered
pair sum; no vertex-cardinality inequality has yet been applied. -/
theorem selector_highTailAverage_secondMoment_eq_sum_componentPairs
    {n k : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (family : FiniteLayeredQueryProgramFamily n)
    (hunambiguous : family.IsUnambiguous)
    (D : DSeed → Fin n → Bool) (T : TSeed → Fin n → Bool) :
    finiteAverage (fun seed : DSeed × TSeed =>
      (finiteAverage (fun uniform : Fin n → Bool =>
        ratHighDegreeFourierTail
          family.selectorFBDD.ratAcceptanceIndicator k
          (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2) =
      ∑ left : family.Index, ∑ right : family.Index,
        finiteAverage (fun seed : DSeed × TSeed =>
          family.componentHighTailAverage left k
              (D seed.1) (T seed.2) *
            family.componentHighTailAverage right k
              (D seed.1) (T seed.2)) := by
  classical
  letI : Fintype family.Index := family.indexFintype
  calc
    finiteAverage (fun seed : DSeed × TSeed =>
        (finiteAverage (fun uniform : Fin n → Bool =>
          ratHighDegreeFourierTail
            family.selectorFBDD.ratAcceptanceIndicator k
            (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2) =
      finiteAverage (fun seed : DSeed × TSeed =>
        (∑ index : family.Index,
          family.componentHighTailAverage index k
            (D seed.1) (T seed.2)) ^ 2) := by
              apply finiteAverage_congr
              intro seed
              rw [family.selector_highTailAverage_eq_sum_components
                hunambiguous]
    _ = ∑ left : family.Index, ∑ right : family.Index,
        finiteAverage (fun seed : DSeed × TSeed =>
          family.componentHighTailAverage left k
              (D seed.1) (T seed.2) *
            family.componentHighTailAverage right k
              (D seed.1) (T seed.2)) := by
      exact finiteAverage_sq_fintype_sum_eq_sum_pair
        (Seed := DSeed × TSeed) (Index := family.Index)
        (fun index seed => family.componentHighTailAverage index k
          (D seed.1) (T seed.2))

end FiniteLayeredQueryProgramFamily
end OneTapeMagnification
end Frontier
end Pnp4
