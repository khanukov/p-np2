import Pnp4.Frontier.ContractExpansion.PrefixExtensionLanguage

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/--
Parameterized parser constructor for the tree-MCSP prefix language.

R1-B1 deliberately keeps `threshold`, `encoding`, `M`, and `parse` explicit:
the current repository has not fixed a byte-level serialization for
`⟨tag,n,x,i,p,pad⟩`, so this constructor records the exact parser surface that a
future serialization proof must instantiate.  Supplying `parse` is not a
hardness assumption; it is only the staged decoding boundary already isolated by
`PrefixParser`.
-/
def treeMCSPPrefixParser
    (threshold : Nat → Nat)
    (encoding : TreeMCSPSearchWitnessEncoding threshold)
    (tag : Nat)
    (M : Nat → Nat)
    (parse : ∀ {m : Nat},
      PrefixBitVec m →
        Option (PrefixInput (treeMCSPSearchProblem threshold encoding) m)) :
    PrefixParser (treeMCSPSearchProblem threshold encoding) where
  tag := tag
  M := M
  parse := parse

/--
A named parser-data package for workers that want to audit parser obligations
before committing to a concrete serialization.

The fields are intentionally operational data, not lower-bound or endpoint
facts.  The accompanying propositions are obligations to be proved by a future
codec/serialization implementation; this module does not inhabit them with
`True` or any vacuous placeholder.
-/
structure TreeMCSPPrefixParserObligations
    (threshold : Nat → Nat)
    (encoding : TreeMCSPSearchWitnessEncoding threshold) where
  tag : Nat
  M : Nat → Nat
  parse : ∀ {m : Nat},
    PrefixBitVec m →
      Option (PrefixInput (treeMCSPSearchProblem threshold encoding) m)
  parser_polynomial_time : Prop
  malformed_inputs_rejected_by_parse : Prop
  length_convention_matches_M : Prop

/-- Build the staged `PrefixParser` exposed by a parser-obligation package. -/
def TreeMCSPPrefixParserObligations.parser
    {threshold : Nat → Nat}
    {encoding : TreeMCSPSearchWitnessEncoding threshold}
    (obligations : TreeMCSPPrefixParserObligations threshold encoding) :
    PrefixParser (treeMCSPSearchProblem threshold encoding) :=
  treeMCSPPrefixParser threshold encoding obligations.tag obligations.M obligations.parse

/--
Exact relation-decidability reduction for the tree-MCSP search target.

For an arbitrary `TreeMCSPSearchWitnessEncoding`, the verifier relation is the
field `encoding.verifies`; therefore R1-B1 can only obtain relation decidability
from an explicit decidability procedure for that field.  This definition lands
the non-vacuous interface reduction and pinpoints the remaining local/global
obligation for generic encodings.
-/
def treeMCSPSearchRelation_decidable_of_encoding
    {threshold : Nat → Nat}
    (encoding : TreeMCSPSearchWitnessEncoding threshold)
    (hdec : ∀ n : Nat,
      ∀ x : PrefixBitVec ((treeMCSPSearchProblem threshold encoding).instanceBits n),
      ∀ w : PrefixBitVec ((treeMCSPSearchProblem threshold encoding).witnessBits n),
        Decidable (encoding.verifies n x w))
    (n : Nat)
    (x : PrefixBitVec ((treeMCSPSearchProblem threshold encoding).instanceBits n))
    (w : PrefixBitVec ((treeMCSPSearchProblem threshold encoding).witnessBits n)) :
    Decidable ((treeMCSPSearchProblem threshold encoding).relation n x w) := by
  dsimp [treeMCSPSearchProblem]
  exact hdec n x w

/--
The codec-induced witness relation is decidable once the decoded circuit is
known, because the repository's tree-circuit model has decidable syntax and the
truth-table agreement check is a finite universal quantification over bit-vectors.

This is still not a polynomial-time theorem: it is only a decidability result.
The runtime and serialization budgets remain separate R1-B1 obligations.
-/
def TreeCircuitWitnessCodec.verifiesDecidable
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (tt : TruthTable n)
    (w : PrefixBitVec (codec.witnessBits n)) :
    Decidable (codec.verifies n tt w) := by
  unfold TreeCircuitWitnessCodec.verifies
  cases hdecode : codec.decode n w with
  | none =>
      exact isFalse (by
        intro h
        rcases h with ⟨c, hc, _hsize, _hcomp⟩
        cases hc)
  | some c =>
      let target : Prop :=
        Pnp3.Models.Circuit.size c ≤ threshold n ∧
          ComputesTruthTable treeCircuitClass c tt
      haveI hcompDecidable : Decidable (ComputesTruthTable treeCircuitClass c tt) := by
        unfold ComputesTruthTable
        exact Fintype.decidableForallFintype
      have targetDecidable : Decidable target := by
        unfold target
        infer_instance
      cases targetDecidable with
      | isTrue htarget =>
          exact isTrue ⟨c, rfl, htarget.1, htarget.2⟩
      | isFalse htarget =>
          exact isFalse (by
            intro h
            rcases h with ⟨c', hc', hsize, hcomp⟩
            cases hc'
            exact htarget ⟨hsize, hcomp⟩)

/-- Relation decidability for the concrete target induced by a tree-circuit codec. -/
def treeMCSPSearchRelation_decidable_of_codec
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (x : PrefixBitVec ((treeMCSPSearchProblem threshold
      (TreeMCSPSearchWitnessEncoding.ofCodec codec)).instanceBits n))
    (w : PrefixBitVec ((treeMCSPSearchProblem threshold
      (TreeMCSPSearchWitnessEncoding.ofCodec codec)).witnessBits n)) :
    Decidable ((treeMCSPSearchProblem threshold
      (TreeMCSPSearchWitnessEncoding.ofCodec codec)).relation n x w) := by
  dsimp [treeMCSPSearchProblem, TreeMCSPSearchWitnessEncoding.ofCodec]
  exact TreeCircuitWitnessCodec.verifiesDecidable codec n x w

/--
Named R1-B1 audit record for the four core budget fields.

Workers should use this record to report real progress without pretending that a
full `PrefixExtensionNPVerifierBudget` has been constructed.  In particular,
there are no default `True` fillers for the runtime fields that the current repo
has not formalized.
-/
structure TreeMCSPPrefixCoreBudgetProgress
    {threshold : Nat → Nat}
    {encoding : TreeMCSPSearchWitnessEncoding threshold}
    (parser : PrefixParser (treeMCSPSearchProblem threshold encoding)) where
  parser_polynomial_time : Prop
  relation_decidable :
    ∀ n : Nat,
      ∀ x : PrefixBitVec ((treeMCSPSearchProblem threshold encoding).instanceBits n),
      ∀ w : PrefixBitVec ((treeMCSPSearchProblem threshold encoding).witnessBits n),
        Decidable ((treeMCSPSearchProblem threshold encoding).relation n x w)
  relation_polynomial_time : Prop
  witness_length_polynomial : Prop
  remaining_runtime_or_codec_blockers : Prop

/--
Generic relation-decidability progress for a parser whose target encoding already
comes with a decidable verifier relation.
-/
def TreeMCSPPrefixCoreBudgetProgress.ofEncodingDecidable
    {threshold : Nat → Nat}
    {encoding : TreeMCSPSearchWitnessEncoding threshold}
    (parser : PrefixParser (treeMCSPSearchProblem threshold encoding))
    (parser_polynomial_time : Prop)
    (hdec : ∀ n : Nat,
      ∀ x : PrefixBitVec ((treeMCSPSearchProblem threshold encoding).instanceBits n),
      ∀ w : PrefixBitVec ((treeMCSPSearchProblem threshold encoding).witnessBits n),
        Decidable (encoding.verifies n x w))
    (relation_polynomial_time : Prop)
    (witness_length_polynomial : Prop)
    (remaining_runtime_or_codec_blockers : Prop) :
    TreeMCSPPrefixCoreBudgetProgress parser where
  parser_polynomial_time := parser_polynomial_time
  relation_decidable :=
    treeMCSPSearchRelation_decidable_of_encoding encoding hdec
  relation_polynomial_time := relation_polynomial_time
  witness_length_polynomial := witness_length_polynomial
  remaining_runtime_or_codec_blockers := remaining_runtime_or_codec_blockers

end ContractExpansion
end Frontier
end Pnp4
