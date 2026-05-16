import Pnp4.Frontier.ContractExpansion.PrefixExtensionLanguageNP

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/--
A local name for the tree-MCSP truth-table payload length.

The crucial R1-B2a accounting point is that this quantity is exponential in the
underlying target parameter `n`, but it is also literally a component of the
ambient prefix-language input length chosen below.  Therefore all later runtime
obligations in this module are stated relative to an ambient length `M n`, not
relative to `n` alone.
-/
abbrev treeMCSPTableLen (n : Nat) : Nat := Pnp3.Models.Partial.tableLen n

/--
Polynomial boundedness of a size schedule in the ambient input length `M`.

This is intentionally only an arithmetic growth obligation.  The repository does
not yet have a general TM-cost formalism for the concrete parser/codec routines
used by R1-B2a, so the genuinely operational fields below remain separate
`Prop` obligations rather than being replaced by vacuous placeholders.
-/
def PolynomiallyBoundedInM (f M : Nat → Nat) : Prop :=
  ∃ c : Nat, ∀ n : Nat, f n ≤ M n ^ c + c

/--
Runtime-staging propositions for the tree-circuit codec side of R1-B2a.

These names make explicit which arithmetic facts can already be stated as
polynomial-in-`M` inequalities and which facts still require a concrete machine
or cost model.  None of these fields proves NP membership by itself.
-/
structure RuntimeAwareTreeCircuitCodec
    (threshold : Nat → Nat)
    (M : Nat → Nat) where
  codec : TreeCircuitWitnessCodec threshold
  witnessBits_poly_in_M : PolynomiallyBoundedInM codec.witnessBits M
  decode_polynomial_time_in_M : Prop
  threshold_poly_in_M : PolynomiallyBoundedInM threshold M
  circuit_eval_polynomial_time_in_size : Prop
  truth_table_lookup_polynomial_time_in_M : Prop
  relation_polynomial_time_in_M : Prop

/--
Runtime-staging propositions for a prefix parser.

The `parser` field is the existing R1-B/R1-B1 parser interface.  The remaining
fields say what future serialization work must prove about that parser relative
to the chosen ambient length convention.  They are deliberately left as
non-vacuous propositions supplied by the worker who instantiates the record.
-/
structure RuntimeAwarePrefixParser
    (problem : SearchMCSPCompressionProblem)
    (M : Nat → Nat) where
  parser : PrefixParser problem
  parser_polynomial_time_in_M : Prop
  malformed_inputs_rejected : Prop
  length_convention_matches_M : Prop

/--
Ambient length convention for the tree-MCSP prefix language.

The exact byte-level serialization is still not fixed, but this convention makes
one load-bearing fact formal: the ambient length includes the full truth-table
component `tableLen n`.  The remaining schedules account for parser overhead,
witness/prefix storage budget, and padding.  Because the definition is a sum
with `tableLen n` as its first summand, the lemma below is real arithmetic rather
than a staged `Prop` field.
-/
def treeMCSPPrefixAmbientLength
    (overhead witnessBits padBits : Nat → Nat)
    (n : Nat) : Nat :=
  treeMCSPTableLen n + overhead n + witnessBits n + padBits n

/--
The truth-table payload is bounded by the ambient length convention.

This is the formal R1-B2a version of the key runtime distinction: an exhaustive
truth-table loop over `2^n` rows is not polynomial in `n`, but it can be charged
to `M n` once `M n` contains the `tableLen n` component.
-/
theorem tableLen_le_treeMCSPPrefixAmbientLength
    (overhead witnessBits padBits : Nat → Nat)
    (n : Nat) :
    treeMCSPTableLen n ≤
      treeMCSPPrefixAmbientLength overhead witnessBits padBits n := by
  unfold treeMCSPPrefixAmbientLength
  omega

/--
Combined R1-B2a runtime budget for the codec-induced tree-MCSP prefix language.

This record is an interface, not an NP theorem.  It packages the local arithmetic
and runtime obligations that a later `PrefixExtensionLanguage_in_NP` proof would
need to audit:

* `tableLen_le_M` is the ambient-length accounting fact;
* `threshold_poly_in_M` and `witnessBits_poly_in_M` are real polynomial-growth
  obligations;
* the remaining fields are operational runtime obligations that cannot yet be
  reduced to the repository's `NP_TM` definition without a concrete parser,
  codec serialization, and TM-cost bridge.
-/
structure TreeMCSPPrefixRuntimeBudget
    (threshold : Nat → Nat)
    (codec : TreeCircuitWitnessCodec threshold) where
  M : Nat → Nat
  tableLen_le_M : ∀ n : Nat, treeMCSPTableLen n ≤ M n
  threshold_poly_in_M : PolynomiallyBoundedInM threshold M
  witnessBits_poly_in_M : PolynomiallyBoundedInM codec.witnessBits M
  decode_polynomial_time_in_M : Prop
  parser_polynomial_time_in_M : Prop
  circuit_eval_polynomial_time_in_size : Prop
  truth_table_lookup_polynomial_time_in_M : Prop
  relation_polynomial_time_in_M : Prop

/--
Build the ambient-length accounting field for the canonical R1-B2a convention.

The caller must still supply all actual runtime and polynomial-growth evidence;
this helper only discharges the `tableLen_le_M` arithmetic obligation for the
specific `treeMCSPPrefixAmbientLength` schedule.
-/
def TreeMCSPPrefixRuntimeBudget.tableLen_le_ambient
    (threshold : Nat → Nat)
    (codec : TreeCircuitWitnessCodec threshold)
    (overhead padBits : Nat → Nat) :
    ∀ n : Nat,
      treeMCSPTableLen n ≤
        treeMCSPPrefixAmbientLength overhead codec.witnessBits padBits n :=
  tableLen_le_treeMCSPPrefixAmbientLength overhead codec.witnessBits padBits

/--
Extract the codec-side runtime-aware record from the combined budget.

This is only a projection/packaging helper: it does not turn the staged runtime
propositions into a verifier or an NP-membership theorem.
-/
def TreeMCSPPrefixRuntimeBudget.toRuntimeAwareCodec
    {threshold : Nat → Nat}
    {codec : TreeCircuitWitnessCodec threshold}
    (budget : TreeMCSPPrefixRuntimeBudget threshold codec) :
    RuntimeAwareTreeCircuitCodec threshold budget.M where
  codec := codec
  witnessBits_poly_in_M := budget.witnessBits_poly_in_M
  decode_polynomial_time_in_M := budget.decode_polynomial_time_in_M
  threshold_poly_in_M := budget.threshold_poly_in_M
  circuit_eval_polynomial_time_in_size := budget.circuit_eval_polynomial_time_in_size
  truth_table_lookup_polynomial_time_in_M := budget.truth_table_lookup_polynomial_time_in_M
  relation_polynomial_time_in_M := budget.relation_polynomial_time_in_M

end ContractExpansion
end Frontier
end Pnp4
