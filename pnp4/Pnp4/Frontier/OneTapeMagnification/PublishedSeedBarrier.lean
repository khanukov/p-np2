import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Published Viola/CHMY square-root parameter barrier

This module records only the exponent arithmetic in the published sufficient
seed/locality bound.  After specializing the bound to constant error, constant
query count, and no oracle-query bits, its power contribution is the square
root of the running time (with additional polylogarithmic factors).  Thus a
time exponent `101 / 100` contributes the exponent `101 / 200`.

The theorem below says that a target exponent strictly below `101 / 200`
cannot dominate that published power contribution.  Multiplicative
polylogarithmic factors only make the sufficient bound larger (once they are
at least one), so omitting them is the most favorable comparison for the
published construction.

This is a parameter obstruction for that published sufficient bound.  It is
not a lower bound on the seed length of arbitrary generators, and it makes no
PRG- or HSG-nonexistence claim.
-/

/-- Halving the time exponent `101 / 100` gives the exact square-root exponent
`101 / 200`. -/
theorem published_viola_chmy_square_root_time_exponent :
    ((101 : ℚ) / 100) / 2 = (101 : ℚ) / 200 := by
  norm_num

/--
Let the target exponent be `muNum / muDen`, with `muDen > 0`.  The natural
cross-multiplication hypothesis

`muNum * 200 < 101 * muDen`

is exactly the strict comparison `muNum / muDen < 101 / 200`.  Consequently
the target exponent cannot dominate the square-root exponent certified by the
published Viola/CHMY sufficient bound at running-time exponent `101 / 100`.

The conclusion intentionally concerns only the published exponent comparison;
it does not assert that a better generator cannot exist.
-/
theorem published_viola_chmy_parameters_do_not_certify_small_threshold
    (muNum muDen : Nat)
    (hMuDen : 0 < muDen)
    (hSmall : muNum * 200 < 101 * muDen) :
    ¬ (((101 : ℚ) / 100) / 2 ≤ (muNum : ℚ) / (muDen : ℚ)) := by
  have hMuDenQ : (0 : ℚ) < (muDen : ℚ) := by
    exact_mod_cast hMuDen
  have hSmallQ : (muNum : ℚ) * 200 < 101 * (muDen : ℚ) := by
    exact_mod_cast hSmall
  have hTargetSmall :
      (muNum : ℚ) / (muDen : ℚ) < (101 : ℚ) / 200 := by
    rw [div_lt_iff₀ hMuDenQ]
    linarith
  rw [published_viola_chmy_square_root_time_exponent]
  exact not_le_of_gt hTargetSmall

end OneTapeMagnification
end Frontier
end Pnp4
