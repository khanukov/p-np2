import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanRestrictionMoment

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Exact factorization after a Boolean mask

This file records the finite rational glue between coordinate locality and the
masked-input restriction used by the homogeneous moment argument.  For fixed
`base` and `mask`, substituting `maskedInput base mask uniform` preserves every
advertised dependency set.  Consequently functions on disjoint coordinate
sets remain independent under the uniform choice of `uniform`.

All averages are exact normalized sums over the finite Boolean cube.
-/

namespace FiniteBooleanMaskedProductFactorization

open scoped BigOperators

open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment

/-- Exact averaging over a heterogeneous finite product.  No `Nonempty`
assumption is needed: if one factor type is empty, both normalized sides
reduce to zero in `Rat`. -/
theorem finiteAverage_pi_dep_prod
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    {Factor : Index → Type*} [∀ index, Fintype (Factor index)]
    (weight : ∀ index, Factor index → Rat) :
    finiteAverage (fun sample : ∀ index, Factor index =>
      ∏ index, weight index (sample index)) =
    ∏ index, finiteAverage (weight index) := by
  unfold finiteAverage
  rw [← Fintype.prod_sum]
  rw [Fintype.card_pi]
  rw [Finset.prod_div_distrib]
  simp

/-- Substitution of a fixed base and mask preserves coordinate locality in the
remaining uniform input. -/
theorem dependsOnlyOn_maskedInput {n : Nat}
    {support : Finset (Fin n)} {f : (Fin n → Bool) → ℚ}
    (hf : DependsOnlyOn support f) (base mask : Fin n → Bool) :
    DependsOnlyOn support
      (fun uniform => f (maskedInput base mask uniform)) := by
  intro uniform uniform' hagrees
  apply hf
  intro queryIndex hqueryIndex
  simp only [maskedInput]
  rw [hagrees queryIndex hqueryIndex]

/-- The empty Walsh coefficient is exactly the uniform finite average. -/
theorem coefficient_empty_eq_finiteAverage {n : Nat}
    (f : (Fin n → Bool) → ℚ) :
    coefficient f ∅ = finiteAverage f := by
  simp [coefficient, finiteAverage]

/-- Functions with disjoint dependency sets factor exactly after applying any
fixed Boolean base and mask. -/
theorem finiteAverage_mul_maskedInput_eq_mul {n : Nat}
    {leftSupport rightSupport : Finset (Fin n)}
    {f g : (Fin n → Bool) → ℚ}
    (hf : DependsOnlyOn leftSupport f)
    (hg : DependsOnlyOn rightSupport g)
    (hdisjoint : Disjoint leftSupport rightSupport)
    (base mask : Fin n → Bool) :
    finiteAverage (fun uniform : Fin n → Bool =>
        f (maskedInput base mask uniform) *
          g (maskedInput base mask uniform)) =
      finiteAverage (fun uniform : Fin n → Bool =>
          f (maskedInput base mask uniform)) *
        finiteAverage (fun uniform : Fin n → Bool =>
          g (maskedInput base mask uniform)) := by
  let fMasked : (Fin n → Bool) → ℚ :=
    fun uniform => f (maskedInput base mask uniform)
  let gMasked : (Fin n → Bool) → ℚ :=
    fun uniform => g (maskedInput base mask uniform)
  have hfMasked : DependsOnlyOn leftSupport fMasked := by
    exact dependsOnlyOn_maskedInput hf base mask
  have hgMasked : DependsOnlyOn rightSupport gMasked := by
    exact dependsOnlyOn_maskedInput hg base mask
  have hfactor :=
    coefficient_mul_eq_mul_coefficient_of_disjoint
      (f := fMasked) (g := gMasked) (alpha := ∅)
      hfMasked hgMasked hdisjoint (by simp)
  simpa only [coefficient_empty_eq_finiteAverage, Finset.empty_inter,
    fMasked, gMasked] using hfactor

/-- If the masked average of the right local factor has absolute value at most
one, multiplying by it cannot increase the absolute masked average of the
left local factor. -/
theorem abs_finiteAverage_mul_maskedInput_le {n : Nat}
    {leftSupport rightSupport : Finset (Fin n)}
    {f g : (Fin n → Bool) → ℚ}
    (hf : DependsOnlyOn leftSupport f)
    (hg : DependsOnlyOn rightSupport g)
    (hdisjoint : Disjoint leftSupport rightSupport)
    (base mask : Fin n → Bool)
    (hgAverage :
      |finiteAverage (fun uniform : Fin n → Bool =>
        g (maskedInput base mask uniform))| ≤ 1) :
    |finiteAverage (fun uniform : Fin n → Bool =>
        f (maskedInput base mask uniform) *
          g (maskedInput base mask uniform))| ≤
      |finiteAverage (fun uniform : Fin n → Bool =>
        f (maskedInput base mask uniform))| := by
  rw [finiteAverage_mul_maskedInput_eq_mul hf hg hdisjoint base mask,
    abs_mul]
  simpa using
    (mul_le_mul_of_nonneg_left hgAverage
      (abs_nonneg (finiteAverage (fun uniform : Fin n → Bool =>
        f (maskedInput base mask uniform)))))

/-- A finite product of local functions depends only on the union of their
advertised supports.  Disjointness is not needed for this locality step. -/
theorem dependsOnlyOn_finset_prod
    {n : Nat} {Index : Type*} [DecidableEq Index]
    (indices : Finset Index) (support : Index → Finset (Fin n))
    (factor : Index → (Fin n → Bool) → Rat)
    (hlocal : ∀ index ∈ indices,
      DependsOnlyOn (support index) (factor index)) :
    DependsOnlyOn (indices.biUnion support)
      (fun input => ∏ index ∈ indices, factor index input) := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
      intro input input' _hagree
      simp
  | @insert index indices hnotMem ih =>
      have hhead : DependsOnlyOn (support index) (factor index) :=
        hlocal index (Finset.mem_insert_self index indices)
      have htail : DependsOnlyOn (indices.biUnion support)
          (fun input => ∏ other ∈ indices, factor other input) := by
        apply ih
        intro other hother
        exact hlocal other (Finset.mem_insert_of_mem hother)
      simpa [Finset.biUnion_insert, hnotMem] using
        (dependsOnlyOn_mul hhead htail)

/-- Exact fixed-mask correlation formula for an arbitrary finite tensor layer.
When the advertised supports are pairwise disjoint, the uniform conditional
average of the product is the product of the conditional averages. -/
theorem finiteAverage_finset_prod_maskedInput_eq_prod
    {n : Nat} {Index : Type*} [DecidableEq Index]
    (indices : Finset Index) (support : Index → Finset (Fin n))
    (factor : Index → (Fin n → Bool) → Rat)
    (hlocal : ∀ index ∈ indices,
      DependsOnlyOn (support index) (factor index))
    (hdisjoint : ∀ left ∈ indices, ∀ right ∈ indices, left ≠ right →
      Disjoint (support left) (support right))
    (base mask : Fin n → Bool) :
    finiteAverage (fun uniform : Fin n → Bool =>
        ∏ index ∈ indices,
          factor index (maskedInput base mask uniform)) =
      ∏ index ∈ indices,
        finiteAverage (fun uniform : Fin n → Bool =>
          factor index (maskedInput base mask uniform)) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp [finiteAverage]
  | @insert index indices hnotMem ih =>
      have hhead : DependsOnlyOn (support index) (factor index) :=
        hlocal index (Finset.mem_insert_self index indices)
      have htail : DependsOnlyOn (indices.biUnion support)
          (fun input => ∏ other ∈ indices, factor other input) := by
        exact dependsOnlyOn_finset_prod indices support factor (by
          intro other hother
          exact hlocal other (Finset.mem_insert_of_mem hother))
      have hheadTail : Disjoint (support index) (indices.biUnion support) := by
        rw [Finset.disjoint_left]
        intro coordinate hcoordinate htailCoordinate
        simp only [Finset.mem_biUnion] at htailCoordinate
        obtain ⟨other, hother, hcoordinateOther⟩ := htailCoordinate
        have hpair := hdisjoint index
          (Finset.mem_insert_self index indices) other
          (Finset.mem_insert_of_mem hother) (by
            intro heq
            subst other
            exact hnotMem hother)
        exact (Finset.disjoint_left.mp hpair hcoordinate) hcoordinateOther
      simp only [Finset.prod_insert hnotMem]
      rw [finiteAverage_mul_maskedInput_eq_mul
        hhead htail hheadTail base mask]
      rw [ih]
      · intro other hother
        exact hlocal other (Finset.mem_insert_of_mem hother)
      · intro left hleft right hright hne
        exact hdisjoint left (Finset.mem_insert_of_mem hleft)
          right (Finset.mem_insert_of_mem hright) hne

end FiniteBooleanMaskedProductFactorization
end OneTapeMagnification
end Frontier
end Pnp4
