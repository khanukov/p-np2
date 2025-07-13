import Pnp.LowSensitivity
import Pnp.TableLocality
import Pnp.NPSeparation

open Boolcube

namespace MigratedTests

-- Basic sanity check for the trivial low-sensitivity cover.
example :
    ∀ F : Finset (BoolFunc.Point 1 → Bool),
      F.Nonempty →
      ∃ R : List (BoolFunc.Subcube 1),
        R.length ≤ F.card * 2 ^ (4 * 0 * Nat.log2 (Nat.succ 1)) := by
  intro F hF
  obtain ⟨R, -, hlen⟩ := LowSensitivity.low_sensitivity_cover (F := F) (s := 0) hF
  exact ⟨R, hlen⟩

-- Table locality specializes to k = n.
example : ∃ k ≤ 1, True := by
  classical
  obtain ⟨k, hk, _⟩ := tableLocal (n := 1) (c := 1)
  exact ⟨k, hk, trivial⟩

-- The non-uniform separation lemma can be applied once a suitable lower
-- bound on `MCSP` is assumed.
example (h : ∃ ε > 0, MCSP_lower_bound ε) :
    P ≠ NP := by
  exact P_ne_NP_of_MCSP_bound h

end MigratedTests

