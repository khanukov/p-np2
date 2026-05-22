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

/--
If an element belongs to a finset, it appears at some finite list index in the
canonical `toList` enumeration.

This is the core indexing lemma needed by finite-index encoders.
-/
theorem exists_index_of_mem_finset
    {α : Type} [DecidableEq α]
    (S : Finset α)
    (a : α)
    (ha : a ∈ S) :
    ∃ i : Fin S.card, S.toList[i.1]? = some a := by
  have hmemList : a ∈ S.toList := by
    exact Finset.mem_toList.mpr ha
  let idx : Nat := S.toList.idxOf a
  have hlt : idx < S.card := by
    simpa [idx, Finset.length_toList] using List.idxOf_lt_length_iff.mpr hmemList
  refine ⟨⟨idx, hlt⟩, ?_⟩
  simpa [idx] using List.getElem?_idxOf (l := S.toList) hmemList

/--
One-hot vector on `k` active positions plus one spare bit.

The first `k` coordinates carry the one-hot payload; the final spare coordinate
is always `false` in this L1 staging encoding.
-/
def oneHot (k : Nat) (i : Fin k) : AlgorithmsToLowerBounds.BitVec (k + 1) :=
  fun j => if h : j.1 < k then (⟨j.1, h⟩ : Fin k) = i else false

/-- The selected index is marked `true` by `oneHot`. -/
theorem oneHot_at_index
    (k : Nat)
    (i : Fin k) :
    oneHot k i ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self k)⟩ = true := by
  simp [oneHot, i.2]

/-- Non-selected active coordinates are `false` in `oneHot`. -/
theorem oneHot_ne_at_index
    (k : Nat)
    (i : Fin k)
    (j : Fin k)
    (hji : j ≠ i) :
    oneHot k i ⟨j.1, Nat.lt_trans j.2 (Nat.lt_succ_self k)⟩ = false := by
  have : j.1 < k := j.2
  simp [oneHot, this, hji]

end Tests
end Frontier
end Pnp4
