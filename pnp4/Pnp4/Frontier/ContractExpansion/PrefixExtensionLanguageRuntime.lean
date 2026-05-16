import Pnp4.Frontier.ContractExpansion.PrefixExtensionLanguageNP

/-!
# R1-B2a runtime-aware prefix-extension budget

This module is intentionally a staging interface, not an NP-membership theorem.
R1-B2 showed that the expensive part of tree-MCSP witness checking is the
truth-table loop over `2^n` assignments: exponential in the target parameter
`n`, but potentially polynomial in the ambient encoded input length `M n` when
`M n` includes the full truth-table component.

The declarations below make that accounting explicit.  They provide:

* an ambient length convention that contains `tableLen n` by construction;
* a real arithmetic lemma `tableLen_le_treeMCSPPrefixAmbientLength`;
* named polynomial-boundedness obligations for the threshold and witness length;
* runtime-aware codec/parser budget records whose remaining runtime fields stay
  as explicit `Prop` obligations because this repository does not yet expose a
  canonical machine-time formalism for these local algorithms.

No declaration in this file proves `PrefixExtensionLanguage_in_NP`, extracts a
search solver from a circuit family, or opens R1-C.
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-- Local spelling for the tree-MCSP truth-table component length `2^n`. -/
abbrev treeMCSPTableLen (n : Nat) : Nat := Pnp3.Models.Partial.tableLen n

/--
Ambient length convention for an R1-B/R1-B1 tree-MCSP prefix instance.

The important point is the explicit `treeMCSPTableLen n` summand.  Extra pieces
are left parameterized because the repository has not yet fixed the bit-level
serialization of tags, naturals, prefixes, witnesses, or padding.  A later
parser can instantiate:

* `overhead n` for tags and encoded scalars such as `n` and `i`;
* `witnessBits n` for the target witness/prefix budget;
* `padBits n` for a chosen single-length convention.

This is deliberately only an ambient-length convention.  It does not define a
parser and it does not assert NP membership.
-/
def treeMCSPPrefixAmbientLength
    (overhead witnessBits padBits : Nat → Nat) (n : Nat) : Nat :=
  overhead n + treeMCSPTableLen n + witnessBits n + padBits n

/--
The tree-MCSP truth-table component is included in the staged ambient length.

This is the R1-B2a load-bearing arithmetic fact: the verifier loop over the
truth table may be charged against `M n` once the chosen ambient length contains
`tableLen n` as a summand.
-/
theorem tableLen_le_treeMCSPPrefixAmbientLength
    (overhead witnessBits padBits : Nat → Nat) (n : Nat) :
    treeMCSPTableLen n ≤
      treeMCSPPrefixAmbientLength overhead witnessBits padBits n := by
  unfold treeMCSPPrefixAmbientLength
  omega

/--
A reusable polynomial-boundedness obligation measured against an ambient length
function `M`, rather than against the target parameter `n`.

The existential exponent/constant shape is intentionally simple and auditably
first-order over `Nat`; it avoids pretending that this file has a full
Turing-machine runtime model.
-/
def PolynomiallyBoundedIn (f M : Nat → Nat) : Prop :=
  ∃ c : Nat, ∀ n : Nat, f n ≤ M n ^ c + c

/-- Threshold-size bound measured in the ambient input length `M n`. -/
def threshold_poly_in_M (threshold M : Nat → Nat) : Prop :=
  PolynomiallyBoundedIn threshold M

/-- Codec witness-length bound measured in the ambient input length `M n`. -/
def witnessBits_poly_in_M (witnessBits M : Nat → Nat) : Prop :=
  PolynomiallyBoundedIn witnessBits M

/--
Runtime-aware refinement of `TreeCircuitWitnessCodec`.

The codec itself remains the existing semantic codec.  R1-B2a adds explicit
ambient-length obligations around it.  The runtime fields are not filled with
`True`: each field is a named obligation that a future concrete serialization
and machine-time development must discharge.
-/
structure RuntimeAwareTreeCircuitCodec
    (threshold M : Nat → Nat) where
  codec : TreeCircuitWitnessCodec threshold
  witnessBits_poly_in_M : witnessBits_poly_in_M codec.witnessBits M
  decode_polynomial_time_in_M : Prop
  threshold_poly_in_M : threshold_poly_in_M threshold M
  circuit_eval_polynomial_time_in_size : Prop
  truth_table_lookup_polynomial_time_in_M : Prop
  relation_polynomial_time_in_M : Prop

/--
Runtime-aware parser wrapper for a prefix-extension parser.

The parser is still the R1-B parser.  This record names the extra local facts
needed before any honest NP-verifier theorem can be attempted: parser runtime,
malformed-input rejection, and agreement between successful parses and the
chosen ambient length convention.
-/
structure RuntimeAwarePrefixParser
    (problem : SearchMCSPCompressionProblem) (M : Nat → Nat) where
  parser : PrefixParser problem
  parser_polynomial_time_in_M : Prop
  malformed_inputs_rejected :
    ∀ {m : Nat} (y : PrefixBitVec m),
      parsePrefixInput parser y = none →
        PrefixExtensionLanguage parser m y = false
  length_convention_matches_M :
    ∀ {m : Nat} (y : PrefixBitVec m) (input : PrefixInput problem m),
      parsePrefixInput parser y = some input → m = M input.n

/--
Combined R1-B2a budget object for a tree-MCSP prefix verifier.

This is not an NP theorem.  It is a compact interface saying exactly what must
be true for the local verifier budget to be meaningful when measured in `M n`.
The first three fields are concrete arithmetic/size obligations; the remaining
fields are staged runtime obligations because no canonical polynomial-time
formalism for these local parser/codec computations is available here yet.
-/
structure TreeMCSPPrefixRuntimeBudget
    (threshold : Nat → Nat)
    (codec : TreeCircuitWitnessCodec threshold)
    (M : Nat → Nat) where
  tableLen_le_M : ∀ n : Nat, treeMCSPTableLen n ≤ M n
  threshold_poly_in_M : ∃ c : Nat, ∀ n : Nat, threshold n ≤ M n ^ c + c
  witnessBits_poly_in_M : ∃ c : Nat, ∀ n : Nat, codec.witnessBits n ≤ M n ^ c + c
  decode_polynomial_time_in_M : Prop
  parser_polynomial_time_in_M : Prop
  circuit_eval_polynomial_time_in_size : Prop
  truth_table_lookup_polynomial_time_in_M : Prop
  relation_polynomial_time_in_M : Prop

/--
The canonical ambient-length convention immediately supplies the `tableLen ≤ M`
field required by `TreeMCSPPrefixRuntimeBudget`.
-/
theorem tableLen_le_M_of_treeMCSPPrefixAmbientLength
    (overhead witnessBits padBits : Nat → Nat) :
    ∀ n : Nat,
      treeMCSPTableLen n ≤
        treeMCSPPrefixAmbientLength overhead witnessBits padBits n := by
  intro n
  exact tableLen_le_treeMCSPPrefixAmbientLength overhead witnessBits padBits n

end ContractExpansion
end Frontier
end Pnp4
