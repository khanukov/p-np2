import Pnp.Boolcube

open Boolcube

namespace Boolcube

/-- Dummy locality predicate. -/
class Local (n k : ℕ) (f : Point n → Bool) : Prop where
  dummy : True

/-- Placeholder table locality statement. -/
theorem tableLocal {n : ℕ} (_c : ℕ) (_hpos : 0 < n) :
  ∃ k, k ≤ n ∧ True := by
  classical
  exact ⟨n, le_rfl, trivial⟩

end Boolcube
