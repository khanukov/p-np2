import Pnp2.LowSensitivity
import Pnp2.TableLocality
import Pnp2.NPSeparation
import Pnp2.Entropy
import Pnp2.Collentropy

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

-- Restricting on a coordinate does not increase collision entropy.
example {n : ℕ} (F : BoolFunc.Family n) (i : Fin n) (b : Bool) :
    BoolFunc.H₂ (F.restrict i b) ≤ BoolFunc.H₂ F := by
  simpa using BoolFunc.H₂_restrict_le (F := F) (i := i) (b := b)

-- Collision probability is always positive.
example {n : ℕ} (f : BoolFunc.BFunc n) [Fintype (BoolFunc.Point n)] :
    0 < BoolFunc.collProbFun (n := n) f := by
  simpa using BoolFunc.collProbFun_pos (f := f)

-- Collision probability does not exceed 1.
example {n : ℕ} (f : BoolFunc.BFunc n) [Fintype (BoolFunc.Point n)] :
    BoolFunc.collProbFun (n := n) f ≤ 1 := by
  simpa using BoolFunc.collProbFun_le_one (f := f)

end MigratedTests

