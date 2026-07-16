import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanMaskedProductFactorization
import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDAffineRestrictionIteration

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Coordinate locality under iterated affine restrictions

Every affine restriction round used by the finite DPTW hybrid is
coordinatewise: it applies `maskedInput` with a fixed base and mask.  Thus
iterating such rounds cannot introduce a dependency on a new coordinate.
This small lemma is the prefix-stability bridge needed by the canonical
block-product Fourier factorization.
-/

open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment

namespace FiniteBooleanAffineRoundsLocality

/-- Iterated coordinatewise affine restrictions preserve the same advertised
dependency support.  In particular, functions on disjoint supports remain on
those same disjoint supports after every fixed affine prefix. -/
theorem dependsOnlyOn_applyAffineRestrictionRounds {n : Nat}
    {support : Finset (Fin n)} {f : (Fin n -> Bool) -> Rat}
    (hf : DependsOnlyOn support f)
    (rounds : List (AffineRestrictionRound n)) :
    DependsOnlyOn support
      (fun input => f (applyAffineRestrictionRounds rounds input)) := by
  induction rounds generalizing f with
  | nil =>
      simpa [applyAffineRestrictionRounds] using hf
  | cons round rounds ih =>
      let restricted : (Fin n -> Bool) -> Rat := fun input =>
        f (maskedInput round.base round.mask input)
      have hrestricted : DependsOnlyOn support restricted := by
        exact
          FiniteBooleanMaskedProductFactorization.dependsOnlyOn_maskedInput
            hf round.base round.mask
      simpa [applyAffineRestrictionRounds, restricted] using
        (ih (f := restricted) hrestricted)

end FiniteBooleanAffineRoundsLocality

end OneTapeMagnification
end Frontier
end Pnp4
