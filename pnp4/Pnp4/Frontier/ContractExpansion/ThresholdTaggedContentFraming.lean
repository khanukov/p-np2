import Pnp4.Frontier.ContractExpansion.TreeCircuitContentWitnessRelation

/-!
# Tagged-pair framing ABI for the threshold content relation (Part A)

This module fixes the raw-word framing of the guarded content relation
`PartAEndpoint.thresholdContentWitnessRelation k` as one versioned V1 language.
A raw word is decoded by `Uniform.V1.PairEncoding.decodePair`; a canonical
interface query together with an interface certificate of the canonical length
`certificateLength n 1` is framed by `Uniform.V1.PairEncoding.encodePair`.

The public surface is deliberately small: one pointwise representation
conversion, the canonical framed pair, the framed language, and two Boolean
equations.  On a canonical framed pair the language answer is the authoritative
`contentSemanticAccepts` on the canonical interface concatenation
`concatBitstring x w`; every raw word that the pair decoder rejects has the
literal answer `false`.

**Scope.**  This is a framing module only.  It constructs no `UniformTM`, no
tape layout, no run and no clock, and it asserts no equality between words of
different types or lengths.  Both equations follow from
`encodedRelationLanguage_encodePair`, `encodedRelationLanguage_malformed` and
`contentWitnessRelation_at_certificateLength_concatBitstring` together with the
exact pointwise representation conversions.

**Progress classification:** Infrastructure.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

namespace PartAEndpoint

/-- Pointwise conversion from the canonical interface type to a V1 bitstring. -/
def interfaceToV1Bitstring {n : Nat}
    (x : Pnp3.ComplexityInterfaces.Bitstring n) :
    Pnp3.Complexity.Uniform.V1.Bitstring n :=
  fun i => x i

/-- Converting to the V1 view and back is the identity on interface bitstrings. -/
@[simp]
theorem v1ToInterfaceBitstring_interfaceToV1Bitstring {n : Nat}
    (x : Pnp3.ComplexityInterfaces.Bitstring n) :
    v1ToInterfaceBitstring (interfaceToV1Bitstring x) = x := rfl

/--
The canonical tagged framing of an interface query with an interface
certificate of the canonical length `certificateLength n 1`: both words are
converted pointwise to the V1 view and framed by `encodePair`.
-/
def canonicalTaggedContentPair {n : Nat}
    (x : Pnp3.ComplexityInterfaces.Bitstring n)
    (w : Pnp3.ComplexityInterfaces.Bitstring
      (Pnp3.ComplexityInterfaces.certificateLength n 1)) :
    Pnp3.Complexity.Uniform.V1.Bitstring
      (Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength n
        (Pnp3.ComplexityInterfaces.certificateLength n 1)) :=
  Pnp3.Complexity.Uniform.V1.PairEncoding.encodePair
    (interfaceToV1Bitstring x) (interfaceToV1Bitstring w)

/-- Closed form of the raw length index carried by every canonical tagged content pair. -/
theorem canonicalTaggedContentPair_pairLength (n : Nat) :
    Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength n
        (Pnp3.ComplexityInterfaces.certificateLength n 1) = 3 * n + 2 := by
  simp only [Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength,
    Pnp3.ComplexityInterfaces.certificateLength, Nat.pow_one]
  omega

/-- The total raw-word V1 language framed over the threshold content relation. -/
def thresholdTaggedContentLanguage (k : Nat) :
    Pnp3.Complexity.Uniform.V1.Language :=
  Pnp3.Complexity.Uniform.V1.encodedRelationLanguage
    (thresholdContentWitnessRelation k)

/--
**Canonical framing is exact.**  On a canonical tagged content pair the framed
language answers exactly the authoritative content-side semantic verifier on
the canonical interface concatenation `concatBitstring x w`.
-/
theorem encodedThresholdContentRelation_canonicalTaggedContentPair
    (k n : Nat)
    (x : Pnp3.ComplexityInterfaces.Bitstring n)
    (w : Pnp3.ComplexityInterfaces.Bitstring
      (Pnp3.ComplexityInterfaces.certificateLength n 1)) :
    thresholdTaggedContentLanguage k
        (Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength n
          (Pnp3.ComplexityInterfaces.certificateLength n 1))
        (canonicalTaggedContentPair x w) =
      contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k))
        (Pnp3.ComplexityInterfaces.concatBitstring x w) := by
  unfold thresholdTaggedContentLanguage canonicalTaggedContentPair
  rw [Pnp3.Complexity.Uniform.V1.encodedRelationLanguage_encodePair]
  unfold thresholdContentWitnessRelation
  rw [contentWitnessRelation_at_certificateLength_concatBitstring,
    v1ToInterfaceBitstring_interfaceToV1Bitstring,
    v1ToInterfaceBitstring_interfaceToV1Bitstring]
  rfl

/--
**Malformed words are rejected.**  A raw word that the V1 pair decoder rejects
has the literal Boolean answer `false` in the framed language.
-/
theorem thresholdTaggedContentLanguage_malformed (k : Nat) {N : Nat}
    (raw : Pnp3.Complexity.Uniform.V1.Bitstring N)
    (hdecode : Pnp3.Complexity.Uniform.V1.PairEncoding.decodePair raw = none) :
    thresholdTaggedContentLanguage k N raw = false :=
  Pnp3.Complexity.Uniform.V1.encodedRelationLanguage_malformed
    (thresholdContentWitnessRelation k) raw hdecode

end PartAEndpoint

end ContractExpansion
end Frontier
end Pnp4
