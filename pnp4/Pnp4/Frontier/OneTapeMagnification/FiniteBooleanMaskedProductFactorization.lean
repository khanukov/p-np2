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

open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment

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

end FiniteBooleanMaskedProductFactorization
end OneTapeMagnification
end Frontier
end Pnp4
