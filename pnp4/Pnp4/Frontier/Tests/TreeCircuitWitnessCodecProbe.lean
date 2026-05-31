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


/-- The spare bit (index `k`) is always `false` in one-hot encoding. -/
theorem oneHot_spare_false
    (k : Nat)
    (i : Fin k) :
    oneHot k i ⟨k, Nat.lt_succ_self k⟩ = false := by
  simp [oneHot]

/-- Active-position characterization for one-hot vectors. -/
theorem oneHot_active_true_iff
    (k : Nat)
    (i j : Fin k) :
    oneHot k i ⟨j.1, Nat.lt_trans j.2 (Nat.lt_succ_self k)⟩ = true ↔ j = i := by
  have hj : j.1 < k := j.2
  simp [oneHot, hj]

/--
Decode a `(k+1)`-bit one-hot vector by choosing an active index in `Fin k`
when one exists; ignore the spare bit.
-/
noncomputable def decodeOneHotIndex (k : Nat)
    (w : AlgorithmsToLowerBounds.BitVec (k + 1)) :
    Option (Fin k) :=
  if h : ∃ i : Fin k, w ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self k)⟩ = true then
    some (Classical.choose h)
  else
    none

/-- One-hot encoding round-trips through `decodeOneHotIndex`. -/
theorem decodeOneHotIndex_oneHot
    (k : Nat)
    (i : Fin k) :
    decodeOneHotIndex k (oneHot k i) = some i := by
  unfold decodeOneHotIndex
  have hExists :
      ∃ j : Fin k,
        oneHot k i ⟨j.1, Nat.lt_trans j.2 (Nat.lt_succ_self k)⟩ = true := by
    exact ⟨i, oneHot_at_index k i⟩
  simp [hExists]
  apply (oneHot_active_true_iff k i (Classical.choose hExists)).1
  exact Classical.choose_spec hExists

/-- Finset used by the finite-index codec at length `n`. -/
def finiteIndexSupport (threshold : Nat → Nat) (n : Nat) : Finset (Pnp3.Models.Circuit n) :=
  Pnp3.Counting.circuitsOfSizeAtMost n (threshold n)

/--
Encode from an explicit support-membership proof using one-hot indexing.
-/
noncomputable def encodeFiniteIndexFromMembership
    (threshold : Nat → Nat)
    (n : Nat)
    (c : Pnp3.Models.Circuit n)
    (hmem : c ∈ finiteIndexSupport threshold n) :
    AlgorithmsToLowerBounds.BitVec (finiteIndexWitnessBits threshold n) :=
  let i : Fin (finiteIndexSupport threshold n).card := Classical.choose
    (exists_index_of_mem_finset (finiteIndexSupport threshold n) c hmem)
  oneHot (finiteIndexSupport threshold n).card i

/--
Finite-index encoder for circuits: one-hot at an index witnessing membership in
`circuitsOfSizeAtMost`; if no membership proof is supplied, use a default slot.
-/
noncomputable def encodeFiniteIndex
    (threshold : Nat → Nat)
    (n : Nat)
    (c : Pnp3.Models.Circuit n) :
    AlgorithmsToLowerBounds.BitVec (finiteIndexWitnessBits threshold n) :=
  if hmem : c ∈ finiteIndexSupport threshold n then
    encodeFiniteIndexFromMembership threshold n c hmem
  else
    fun _ => false

/--
Decode finite-index witness bits by decoding the one-hot index and looking up
the corresponding circuit in the canonical support list.
-/
noncomputable def decodeFiniteIndex
    (threshold : Nat → Nat)
    (n : Nat)
    (w : AlgorithmsToLowerBounds.BitVec (finiteIndexWitnessBits threshold n)) :
    Option (Pnp3.Models.Circuit n) := do
  let i ← decodeOneHotIndex (finiteIndexSupport threshold n).card w
  (finiteIndexSupport threshold n).toList[i.1]?

/-- Decoding a one-hot index and then list lookup returns the indexed circuit. -/
theorem decodeFiniteIndex_oneHot_index
    (threshold : Nat → Nat)
    (n : Nat)
    (i : Fin (finiteIndexSupport threshold n).card)
    (c : Pnp3.Models.Circuit n)
    (hi : (finiteIndexSupport threshold n).toList[i.1]? = some c) :
    decodeFiniteIndex threshold n
      (oneHot (finiteIndexSupport threshold n).card i) = some c := by
  unfold decodeFiniteIndex
  have hget : (finiteIndexSupport threshold n).toList[i.1] = c := by
    simpa using hi
  simp [decodeOneHotIndex_oneHot, hget]

/-- Round-trip for membership-based finite-index encoding. -/
theorem decode_encode_finiteIndexFromMembership
    (threshold : Nat → Nat)
    (n : Nat)
    (c : Pnp3.Models.Circuit n)
    (hmem : c ∈ finiteIndexSupport threshold n) :
    decodeFiniteIndex threshold n
      (encodeFiniteIndexFromMembership threshold n c hmem) = some c := by
  unfold encodeFiniteIndexFromMembership
  let hex := exists_index_of_mem_finset (finiteIndexSupport threshold n) c hmem
  let i : Fin (finiteIndexSupport threshold n).card := Classical.choose hex
  have hi : (finiteIndexSupport threshold n).toList[i.1]? = some c :=
    Classical.choose_spec hex
  simpa [i] using decodeFiniteIndex_oneHot_index threshold n i c hi

/-- Round-trip for bounded circuits through the finite-index codec staging API. -/
theorem decode_encode_finiteIndex
    (threshold : Nat → Nat)
    (n : Nat)
    (c : Pnp3.Models.Circuit n)
    (hc : Pnp3.Models.Circuit.size c ≤ threshold n) :
    decodeFiniteIndex threshold n
      (encodeFiniteIndex threshold n c) = some c := by
  have hmem : c ∈ finiteIndexSupport threshold n :=
    mem_circuitsOfSizeAtMost_threshold threshold n c hc
  unfold encodeFiniteIndex
  simp [decode_encode_finiteIndexFromMembership, hmem]

/-- Full finite-index `TreeCircuitWitnessCodec` staging object. -/
noncomputable def finiteIndexTreeCircuitWitnessCodec
    (threshold : Nat → Nat) :
    TreeCircuitWitnessCodec threshold where
  witnessBits := finiteIndexWitnessBits threshold
  encode := encodeFiniteIndex threshold
  decode := decodeFiniteIndex threshold
  decode_encode := decode_encode_finiteIndex threshold

/-- Optional convenience packaging into the generic search witness encoding surface. -/
noncomputable def finiteIndexTreeMCSPSearchWitnessEncoding
    (threshold : Nat → Nat) :
    TreeMCSPSearchWitnessEncoding threshold :=
  TreeMCSPSearchWitnessEncoding.ofCodec
    (finiteIndexTreeCircuitWitnessCodec threshold)

end Tests
end Frontier
end Pnp4
