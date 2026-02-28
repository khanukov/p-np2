import Complexity.Interfaces

namespace Pnp3.Tests

open Pnp3.ComplexityInterfaces

/--
Sanity witness: the imported lightweight `PpolyLite` interface is intentionally
too weak as a final non-uniform target (it accepts any language by construction).
-/
theorem ppolyLite_trivial : ∀ L : Language, PpolyLite L := by
  intro L
  exact ⟨{ circuits := fun n x => L n x }, trivial⟩

/--
As a direct corollary of `ppolyLite_trivial`, separation against `PpolyLite`
cannot hold in this interface.
-/
theorem not_NP_not_subset_PpolyLite : ¬ NP_not_subset_Ppoly := by
  intro hSep
  rcases hSep with ⟨L, _hNP, hNotPpoly⟩
  exact hNotPpoly (ppolyLite_trivial L)

end Pnp3.Tests
