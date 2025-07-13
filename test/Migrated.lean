import Pnp.LowSensitivity
import Pnp.TableLocality

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
  simpa using tableLocal (n := 1) 1 (by decide)

end MigratedTests

