import Pnp4.Frontier.SearchMCSPConcreteTargets
import Counting.CircuitCounting

namespace Pnp4
namespace Frontier
namespace Tests

open AlgorithmsToLowerBounds

/--
Finite-index witness width for circuits up to `threshold n`.

For L0 this is intentionally simple and explicit: we reserve one bit per
candidate in the overapproximation finset, plus one spare bit.  This is not yet
an efficient serialization; it is a capacity pin useful for subsequent codec
construction.
-/
def finiteIndexWitnessBits (threshold : Nat → Nat) (n : Nat) : Nat :=
  (Pnp3.Counting.circuitsOfSizeAtMost n (threshold n)).card + 1

/--
L0 helper: every bounded circuit is enumerated by the counting finset used for
finite-index coding.
-/
theorem mem_circuitsOfSizeAtMost_threshold
    (threshold : Nat → Nat)
    (n : Nat)
    (c : Pnp3.Models.Circuit n)
    (hc : Pnp3.Models.Circuit.size c ≤ threshold n) :
    c ∈ Pnp3.Counting.circuitsOfSizeAtMost n (threshold n) :=
  Pnp3.Counting.mem_circuitsOfSizeAtMost c (threshold n) hc

/--
L0 helper: the finite-index witness width is strictly positive.
-/
theorem finiteIndexWitnessBits_pos
    (threshold : Nat → Nat)
    (n : Nat) :
    0 < finiteIndexWitnessBits threshold n := by
  unfold finiteIndexWitnessBits
  omega

/--
L0 helper: `Fin (finiteIndexWitnessBits ...)` is inhabited, providing a canonical
index slot for future encode/decode experiments.
-/
def defaultFiniteIndex
    (threshold : Nat → Nat)
    (n : Nat) : Fin (finiteIndexWitnessBits threshold n) :=
  ⟨0, finiteIndexWitnessBits_pos threshold n⟩

end Tests
end Frontier
end Pnp4
