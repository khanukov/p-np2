import Complexity.Uniform.V1.Relation
import Pnp4.Frontier.ContractExpansion.ContentSemanticVerifier
import Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixSemanticVerifier
import Pnp4.Frontier.ContractExpansion.ConcreteTreeCodec
import Pnp4.Frontier.ContractExpansion.ThresholdGrowth

/-!
# Guarded V1 relations for tree-circuit content witnesses

This module packages the content and tree-prefix semantic checkers as two
separate length-indexed V1 witness relations.  The content relation uses the
computable, query-first concatenator defined here.  A proposition-level theorem
relates that concatenator extensionally to the canonical interface
concatenation.

This module constructs no verifier machine and proves no complexity-class or
resource-bound consequence.
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

namespace PartAEndpoint

/-- Pointwise conversion from a V1 bitstring to the canonical interface type. -/
def v1ToInterfaceBitstring {n : Nat}
    (x : Pnp3.Complexity.Uniform.V1.Bitstring n) :
    Pnp3.ComplexityInterfaces.Bitstring n :=
  fun i => x i

/-- Pointwise conversion from a V1 bitstring to a prefix bit-vector. -/
def v1ToPrefixBitVec {n : Nat}
    (x : Pnp3.Complexity.Uniform.V1.Bitstring n) : PrefixBitVec n :=
  fun i => x i

/-- Pointwise conversion from the canonical interface type to a prefix bit-vector. -/
def interfaceToPrefixBitVec {n : Nat}
    (x : Pnp3.ComplexityInterfaces.Bitstring n) : PrefixBitVec n :=
  fun i => x i

/--
Computable query-first concatenation at the V1-to-prefix boundary.  The right
branch uses the explicit offset `i.val - n`; its bound follows from the ambient
index bound and failure of the left-branch test.
-/
def concatV1ToPrefixBitVec {n m : Nat}
    (query : Pnp3.Complexity.Uniform.V1.Bitstring n)
    (cert : Pnp3.Complexity.Uniform.V1.Bitstring m) :
    PrefixBitVec (n + m) :=
  fun i =>
    if h : i.val < n then
      query ⟨i.val, h⟩
    else
      cert ⟨i.val - n, by
        have hi : i.val < n + m := i.isLt
        omega⟩

/--
The computable concatenator agrees extensionally with the canonical interface
concatenation after the explicit representation conversions.

This is a proposition-level compatibility theorem; executable definitions in
this module do not call the canonical concatenator.
-/
theorem concatV1ToPrefixBitVec_eq_concatBitstring
    {n m : Nat}
    (query : Pnp3.Complexity.Uniform.V1.Bitstring n)
    (cert : Pnp3.Complexity.Uniform.V1.Bitstring m) :
    concatV1ToPrefixBitVec query cert =
      interfaceToPrefixBitVec
        (Pnp3.ComplexityInterfaces.concatBitstring
          (v1ToInterfaceBitstring query)
          (v1ToInterfaceBitstring cert)) := by
  classical
  funext i
  by_cases h : i.val < n
  · simp only [concatV1ToPrefixBitVec, interfaceToPrefixBitVec,
      Pnp3.ComplexityInterfaces.concatBitstring, v1ToInterfaceBitstring,
      h, dif_pos]
  · simp only [concatV1ToPrefixBitVec, interfaceToPrefixBitVec,
      Pnp3.ComplexityInterfaces.concatBitstring, v1ToInterfaceBitstring,
      h]
    apply congrArg cert
    apply Fin.ext
    change i.val - n = Classical.choose
      (Nat.exists_eq_add_of_le (Nat.le_of_not_gt h))
    have ht :
        i.val = n + Classical.choose
          (Nat.exists_eq_add_of_le (Nat.le_of_not_gt h)) :=
      Classical.choose_spec
        (Nat.exists_eq_add_of_le (Nat.le_of_not_gt h))
    omega

/--
The content-side relation.  Only the exact certificate length is interpreted;
every other dependent index is mapped to `false`.  Its canonical branch calls
`contentSemanticAccepts` on the computable query-then-certificate view.
-/
def contentWitnessRelation
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) :
    Pnp3.Complexity.Uniform.V1.WitnessRelation :=
  fun n m query cert =>
    if h : m = Pnp3.ComplexityInterfaces.certificateLength n 1 then
      contentSemanticAccepts codec
        (concatV1ToPrefixBitVec query (h ▸ cert))
    else
      false

/--
The tree-prefix relation over the same V1 boundary and exact length guard.  It
is intentionally separate from `contentWitnessRelation`; no equality or
equivalence between the two relations is asserted.
-/
def treePrefixWitnessRelation
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) :
    Pnp3.Complexity.Uniform.V1.WitnessRelation :=
  fun n m query cert =>
    if h : m = Pnp3.ComplexityInterfaces.certificateLength n 1 then
      treePrefixSemanticAccepts codec n
        (v1ToPrefixBitVec query)
        (v1ToPrefixBitVec (h ▸ cert))
    else
      false

/-- Content-side relation at the requested fixed polynomial threshold. -/
def thresholdContentWitnessRelation (k : Nat) :
    Pnp3.Complexity.Uniform.V1.WitnessRelation :=
  contentWitnessRelation
    (treeCircuitWitnessCodec (thresholdPoly k))

/-- Tree-prefix-side relation at the same fixed polynomial threshold. -/
def thresholdTreePrefixWitnessRelation (k : Nat) :
    Pnp3.Complexity.Uniform.V1.WitnessRelation :=
  treePrefixWitnessRelation
    (treeCircuitWitnessCodec (thresholdPoly k))

/-- At the canonical certificate length, the content guard reduces exactly. -/
@[simp]
theorem contentWitnessRelation_at_certificateLength
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (query : Pnp3.Complexity.Uniform.V1.Bitstring n)
    (cert : Pnp3.Complexity.Uniform.V1.Bitstring
      (Pnp3.ComplexityInterfaces.certificateLength n 1)) :
    contentWitnessRelation codec n
        (Pnp3.ComplexityInterfaces.certificateLength n 1) query cert =
      contentSemanticAccepts codec
        (concatV1ToPrefixBitVec query cert) := by
  unfold contentWitnessRelation
  split <;> simp_all

/--
Canonical-length content reduction rewritten to the repository's canonical
interface concatenation.  This theorem changes only the bitstring view; it
constructs no machine or verifier object.
-/
theorem contentWitnessRelation_at_certificateLength_concatBitstring
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (query : Pnp3.Complexity.Uniform.V1.Bitstring n)
    (cert : Pnp3.Complexity.Uniform.V1.Bitstring
      (Pnp3.ComplexityInterfaces.certificateLength n 1)) :
    contentWitnessRelation codec n
        (Pnp3.ComplexityInterfaces.certificateLength n 1) query cert =
      contentSemanticAccepts codec
        (interfaceToPrefixBitVec
          (Pnp3.ComplexityInterfaces.concatBitstring
            (v1ToInterfaceBitstring query)
            (v1ToInterfaceBitstring cert))) := by
  rw [contentWitnessRelation_at_certificateLength,
    concatV1ToPrefixBitVec_eq_concatBitstring]

/-- Every noncanonical certificate length is rejected by the content relation. -/
@[simp]
theorem contentWitnessRelation_of_wrongLength
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    {n m : Nat}
    (query : Pnp3.Complexity.Uniform.V1.Bitstring n)
    (cert : Pnp3.Complexity.Uniform.V1.Bitstring m)
    (h : m ≠ Pnp3.ComplexityInterfaces.certificateLength n 1) :
    contentWitnessRelation codec n m query cert = false := by
  unfold contentWitnessRelation
  split <;> simp_all

/-- At the canonical certificate length, the tree-prefix guard reduces exactly. -/
@[simp]
theorem treePrefixWitnessRelation_at_certificateLength
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (query : Pnp3.Complexity.Uniform.V1.Bitstring n)
    (cert : Pnp3.Complexity.Uniform.V1.Bitstring
      (Pnp3.ComplexityInterfaces.certificateLength n 1)) :
    treePrefixWitnessRelation codec n
        (Pnp3.ComplexityInterfaces.certificateLength n 1) query cert =
      treePrefixSemanticAccepts codec n
        (v1ToPrefixBitVec query)
        (v1ToPrefixBitVec cert) := by
  unfold treePrefixWitnessRelation
  split <;> simp_all

/-- Every noncanonical certificate length is rejected by the tree-prefix relation. -/
@[simp]
theorem treePrefixWitnessRelation_of_wrongLength
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    {n m : Nat}
    (query : Pnp3.Complexity.Uniform.V1.Bitstring n)
    (cert : Pnp3.Complexity.Uniform.V1.Bitstring m)
    (h : m ≠ Pnp3.ComplexityInterfaces.certificateLength n 1) :
    treePrefixWitnessRelation codec n m query cert = false := by
  unfold treePrefixWitnessRelation
  split <;> simp_all

end PartAEndpoint

end ContractExpansion
end Frontier
end Pnp4
