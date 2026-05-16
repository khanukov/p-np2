import Pnp4.Frontier.ContractExpansion.PrefixExtensionLanguageNP

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/--
Ambient input length for the R1-B2a tree-MCSP prefix language.

The definition is deliberately small and arithmetic: any future concrete
serialization may choose its own overhead, witness-codec length, and padding
policy, but the truth-table component is always included explicitly.  This is
what lets a verifier that enumerates `2^n` assignments be measured against the
ambient encoded length `M(n)` rather than against the target parameter `n`.
-/
def treeMCSPPrefixAmbientLength
    (overhead witnessBits padBits : Nat → Nat)
    (n : Nat) : Nat :=
  Pnp3.Models.Partial.tableLen n + overhead n + witnessBits n + padBits n

/--
The truth-table component is part of the staged ambient length convention.

This is the first real R1-B2a arithmetic fact: it is not an NP-membership
claim, but it records the load-bearing inequality needed before truth-table
verification can be audited as polynomial in the ambient length.
-/
theorem tableLen_le_treeMCSPPrefixAmbientLength
    (overhead witnessBits padBits : Nat → Nat)
    (n : Nat) :
    Pnp3.Models.Partial.tableLen n ≤
      treeMCSPPrefixAmbientLength overhead witnessBits padBits n := by
  simp [treeMCSPPrefixAmbientLength, Nat.add_assoc]

/--
A family of natural numbers is polynomially bounded by the ambient length `M`.

R1-B2a uses this concrete arithmetic predicate for threshold and witness-length
bounds instead of a vacuous `True` placeholder.  Runtime claims below are still
staged as named `Prop` obligations because the repository does not yet expose a
uniform polynomial-time machine-cost formalism for these parser/codec routines.
-/
def PolynomiallyBoundedInAmbient
    (M f : Nat → Nat) : Prop :=
  ∃ c : Nat, ∀ n : Nat, f n ≤ M n ^ c + c

/-- The tree-circuit threshold is polynomially bounded in the ambient length. -/
def threshold_poly_in_M
    (threshold M : Nat → Nat) : Prop :=
  PolynomiallyBoundedInAmbient M threshold

/-- The codec witness length is polynomially bounded in the ambient length. -/
def witnessBits_poly_in_M
    {threshold : Nat → Nat}
    (M : Nat → Nat)
    (codec : TreeCircuitWitnessCodec threshold) : Prop :=
  PolynomiallyBoundedInAmbient M codec.witnessBits

/--
Runtime-aware refinement of `TreeCircuitWitnessCodec`.

The first and third fields are concrete arithmetic bounds.  The remaining
runtime fields are intentionally named obligations rather than default
inhabitants: R1-B2a exposes what an implementation must prove, while avoiding a
fake `PrefixExtensionLanguage_in_NP` theorem or any R1-C extraction step.
-/
structure RuntimeAwareTreeCircuitCodec
    (threshold M : Nat → Nat) where
  codec : TreeCircuitWitnessCodec threshold
  witnessBits_poly_in_M : witnessBits_poly_in_M M codec
  decode_polynomial_time_in_M : Prop
  threshold_poly_in_M : threshold_poly_in_M threshold M
  circuit_eval_polynomial_time_in_size : Prop
  truth_table_lookup_polynomial_time_in_M : Prop
  relation_polynomial_time_in_M : Prop

/--
Runtime-aware parser package for the prefix-extension language.

`parser_polynomial_time_in_M` remains a staged runtime obligation, but malformed
input and length-convention soundness are stated as precise parser facts.  In
particular, successful parsing must recover a target parameter whose ambient
string length is exactly `M input.n`.
-/
structure RuntimeAwarePrefixParser
    (problem : SearchMCSPCompressionProblem)
    (M : Nat → Nat) where
  parser : PrefixParser problem
  parser_polynomial_time_in_M : Prop
  malformed_inputs_rejected :
    ∀ {m : Nat}, ∀ y : PrefixBitVec m,
      parsePrefixInput parser y = none →
        PrefixExtensionLanguage parser m y = false
  length_convention_matches_M :
    ∀ {m : Nat}, ∀ y : PrefixBitVec m, ∀ input : PrefixInput problem m,
      parsePrefixInput parser y = some input → m = M input.n

/--
R1-B2a runtime-budget interface for tree-MCSP prefix verification.

This is not an NP theorem.  It only collects the local arithmetic and runtime
obligations that a future, separately authorised NP proof would need to audit.
The `tableLen_le_M`, threshold, and witness-size fields are concrete arithmetic
statements; the remaining runtime fields are named obligations because the
current repository still lacks a global polynomial-time formalism connecting
these local parser/codec facts to `ComplexityInterfaces.NP` / `NP_TM`.
-/
structure TreeMCSPPrefixRuntimeBudget
    (threshold M : Nat → Nat)
    (codec : TreeCircuitWitnessCodec threshold)
    (parser : PrefixParser (treeMCSPSearchProblem threshold
      (TreeMCSPSearchWitnessEncoding.ofCodec codec))) where
  tableLen_le_M : ∀ n : Nat, Pnp3.Models.Partial.tableLen n ≤ M n
  threshold_poly_in_M : threshold_poly_in_M threshold M
  witnessBits_poly_in_M : witnessBits_poly_in_M M codec
  decode_polynomial_time_in_M : Prop
  parser_polynomial_time_in_M : Prop
  circuit_eval_polynomial_time_in_size : Prop
  truth_table_lookup_polynomial_time_in_M : Prop
  relation_polynomial_time_in_M : Prop
  malformed_inputs_rejected :
    ∀ {m : Nat}, ∀ y : PrefixBitVec m,
      parsePrefixInput parser y = none →
        PrefixExtensionLanguage parser m y = false
  length_convention_matches_M :
    ∀ {m : Nat}, ∀ y : PrefixBitVec m,
      ∀ input : PrefixInput
        (treeMCSPSearchProblem threshold
          (TreeMCSPSearchWitnessEncoding.ofCodec codec)) m,
        parsePrefixInput parser y = some input → m = M input.n

/--
The canonical ambient-length convention immediately discharges the `tableLen`
part of the R1-B2a runtime budget.
-/
def treeMCSPPrefixRuntimeBudget_tableLen
    (threshold : Nat → Nat)
    (codec : TreeCircuitWitnessCodec threshold)
    (overhead padBits : Nat → Nat) :
    ∀ n : Nat,
      Pnp3.Models.Partial.tableLen n ≤
        treeMCSPPrefixAmbientLength overhead codec.witnessBits padBits n :=
  tableLen_le_treeMCSPPrefixAmbientLength overhead codec.witnessBits padBits

end ContractExpansion
end Frontier
end Pnp4
