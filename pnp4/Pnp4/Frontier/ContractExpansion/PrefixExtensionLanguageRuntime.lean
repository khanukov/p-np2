import Pnp4.Frontier.ContractExpansion.PrefixExtensionLanguageNP

namespace Pnp4
namespace Frontier
namespace ContractExpansion

/--
A small arithmetic predicate for the R1-B2a runtime budget.

`FunctionPolynomiallyBoundedBy M f` means that the resource schedule `f` is
bounded by a polynomial in the ambient encoded input length `M`.  This is still
an arithmetic interface, not a machine-time theorem: R1-B2a deliberately keeps
TM-level polynomial-time claims as separate named obligations until the concrete
parser, decoder, and TM bridge exist.
-/
def FunctionPolynomiallyBoundedBy (M f : Nat → Nat) : Prop :=
  ∃ c : Nat, ∀ n : Nat, f n ≤ M n ^ c + c

/--
Ambient length convention for a tree-MCSP prefix instance.

The load-bearing component is the explicit `tableLen n` summand.  Since the
input contains the full truth table, an all-assignments check that is
exponential in the target parameter `n` can still be measured against the
ambient input length `M(n)` rather than against `n` alone.

The remaining summands are intentionally parametric:
* `overhead` covers tags and self-delimiting encodings of metadata such as `n`
  and the prefix length;
* `witnessBits` is the full witness/circuit-code length at target parameter
  `n`;
* `padBits` covers any padding used by the parser convention.
-/
def treeMCSPPrefixAmbientLength
    (overhead witnessBits padBits : Nat → Nat)
    (n : Nat) : Nat :=
  overhead n + Pnp3.Models.Partial.tableLen n + witnessBits n + padBits n

/--
The explicit truth-table payload is always bounded by the ambient length.

This is the concrete arithmetic fact R1-B2a needs before discussing verifier
runtime in `M(n)`: the `2^n` truth-table scan is at most linear in this ambient
length convention, ignoring the still-staged per-iteration costs.
-/
theorem tableLen_le_treeMCSPPrefixAmbientLength
    (overhead witnessBits padBits : Nat → Nat)
    (n : Nat) :
    Pnp3.Models.Partial.tableLen n ≤
      treeMCSPPrefixAmbientLength overhead witnessBits padBits n := by
  unfold treeMCSPPrefixAmbientLength
  omega

/-- Threshold growth bounded polynomially in the ambient length. -/
def threshold_poly_in_M (M threshold : Nat → Nat) : Prop :=
  FunctionPolynomiallyBoundedBy M threshold

/-- Witness-code length bounded polynomially in the ambient length. -/
def witnessBits_poly_in_M (M witnessBits : Nat → Nat) : Prop :=
  FunctionPolynomiallyBoundedBy M witnessBits

/--
Runtime-aware wrapper for the tree-circuit codec.

The fields are obligations, not placeholders.  The two size/growth fields use a
concrete arithmetic predicate; the runtime fields remain `Prop` because this
repository has not yet provided a reusable polynomial-time formalism for the
codec decoder, circuit evaluation implementation, truth-table lookup, or the
full relation checker.  In particular, no field is filled with `True` here and
this structure does not assert NP membership.
-/
structure RuntimeAwareTreeCircuitCodec
    (threshold : Nat → Nat) where
  codec : TreeCircuitWitnessCodec threshold
  overhead : Nat → Nat
  padBits : Nat → Nat
  witnessBits_poly_in_M :
    witnessBits_poly_in_M
      (treeMCSPPrefixAmbientLength overhead codec.witnessBits padBits)
      codec.witnessBits
  decode_polynomial_time_in_M : Prop
  threshold_poly_in_M :
    threshold_poly_in_M
      (treeMCSPPrefixAmbientLength overhead codec.witnessBits padBits)
      threshold
  circuit_eval_polynomial_time_in_size : Prop
  truth_table_lookup_polynomial_time_in_M : Prop
  relation_polynomial_time_in_M : Prop

namespace RuntimeAwareTreeCircuitCodec

/-- The ambient length induced by a runtime-aware codec package. -/
def M {threshold : Nat → Nat}
    (runtimeCodec : RuntimeAwareTreeCircuitCodec threshold) : Nat → Nat :=
  treeMCSPPrefixAmbientLength
    runtimeCodec.overhead
    runtimeCodec.codec.witnessBits
    runtimeCodec.padBits

/-- The table-length arithmetic lemma specialized to a runtime-aware codec. -/
theorem tableLen_le_M {threshold : Nat → Nat}
    (runtimeCodec : RuntimeAwareTreeCircuitCodec threshold)
    (n : Nat) :
    Pnp3.Models.Partial.tableLen n ≤ runtimeCodec.M n := by
  exact tableLen_le_treeMCSPPrefixAmbientLength
    runtimeCodec.overhead
    runtimeCodec.codec.witnessBits
    runtimeCodec.padBits
    n

end RuntimeAwareTreeCircuitCodec

/--
Runtime-aware parser package for the prefix-extension parser boundary.

This works for any `SearchMCSPCompressionProblem`; the tree-MCSP-specific
ambient budget is supplied by `TreeMCSPPrefixRuntimeBudget` below.  The parser
field is concrete data, while the runtime and soundness fields are explicit
obligations for a later serialization implementation.
-/
structure RuntimeAwarePrefixParser
    (problem : SearchMCSPCompressionProblem) where
  parser : PrefixParser problem
  parser_polynomial_time_in_M : Prop
  malformed_inputs_rejected : Prop
  length_convention_matches_M : Prop

/--
Combined R1-B2a runtime budget for the tree-MCSP prefix-extension language.

This object is intentionally not an NP theorem.  It records the arithmetic fact
that the truth-table component is included in the ambient length, polynomial
bounds for the threshold and witness-code length, and the remaining local
runtime obligations.  A future `PrefixExtensionLanguage_in_NP` theorem would
still need a concrete parser/decoder implementation and a bridge from these
local obligations to the repository's TM-based `NP_TM` definition.
-/
structure TreeMCSPPrefixRuntimeBudget
    (threshold : Nat → Nat)
    (codec : TreeCircuitWitnessCodec threshold)
    (overhead padBits : Nat → Nat)
    (parser : PrefixParser
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec))) where
  tableLen_le_M : ∀ n : Nat,
    Pnp3.Models.Partial.tableLen n ≤
      treeMCSPPrefixAmbientLength overhead codec.witnessBits padBits n
  threshold_poly_in_M :
    threshold_poly_in_M
      (treeMCSPPrefixAmbientLength overhead codec.witnessBits padBits)
      threshold
  witnessBits_poly_in_M :
    witnessBits_poly_in_M
      (treeMCSPPrefixAmbientLength overhead codec.witnessBits padBits)
      codec.witnessBits
  decode_polynomial_time_in_M : Prop
  parser_polynomial_time_in_M : Prop
  circuit_eval_polynomial_time_in_size : Prop
  truth_table_lookup_polynomial_time_in_M : Prop
  relation_polynomial_time_in_M : Prop
  malformed_inputs_rejected : Prop
  length_convention_matches_M : Prop

namespace TreeMCSPPrefixRuntimeBudget

/-- The ambient length associated with a tree-MCSP runtime budget. -/
def M
    {threshold : Nat → Nat}
    {codec : TreeCircuitWitnessCodec threshold}
    {overhead padBits : Nat → Nat}
    {parser : PrefixParser
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec))}
    (_budget : TreeMCSPPrefixRuntimeBudget threshold codec overhead padBits parser) :
    Nat → Nat :=
  treeMCSPPrefixAmbientLength overhead codec.witnessBits padBits

/-- Build the budget's required `tableLen` bound from the ambient convention. -/
theorem tableLen_le_M_from_ambient
    {threshold : Nat → Nat}
    {codec : TreeCircuitWitnessCodec threshold}
    {overhead padBits : Nat → Nat}
    {parser : PrefixParser
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec))}
    (_budget : TreeMCSPPrefixRuntimeBudget threshold codec overhead padBits parser)
    (n : Nat) :
    Pnp3.Models.Partial.tableLen n ≤
      treeMCSPPrefixAmbientLength overhead codec.witnessBits padBits n := by
  exact tableLen_le_treeMCSPPrefixAmbientLength overhead codec.witnessBits padBits n

end TreeMCSPPrefixRuntimeBudget

end ContractExpansion
end Frontier
end Pnp4
