import Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionCoincidence
import Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixSerializer
import Pnp4.Frontier.ContractExpansion.ConcreteTreeCodec
import Pnp4.Frontier.ContractExpansion.ThresholdGrowth

/-!
# Non-vacuity of `ContentAccepts` — GATE-0

This module closes GATE-0 of `VERIFIER_RETARGET_PLAN.md` §4.1: it exhibits words that the frozen
target predicate `ContentAccepts` actually accepts, and it does so *unconditionally* at the concrete
codec `treeCircuitWitnessCodec (thresholdPoly k)`.  Before this slice the only existential statement
about `ContentAccepts` was the conditional
`ContentAccepts_padWord_of_prefixExtendable` (`ContentPrefixExtensionPaddingTransport.lean`), whose
hypotheses `hparse` / `hn` / `hext` were nowhere discharged — so `L'` could, as far as the
development knew, have been the empty language.  That mattered because
`ContentPrefixExtensionTransfer.lean` pins even the *empty* `L'` outside `PpolyDAG`: an empty target
would have made the consolidated CT source `NP_not_subset_PpolyDAG_treePolyCT` worthless rather than
merely conditional, and would have made any verifier machine for `L'` a discharge of a vacuous
obligation.

The route is the one the plan specifies, and every ingredient is already in the directory:

* `zeroPrefixQueryValue_parses` (`TreeMCSPPrefixSerializer.lean`) supplies **both** hypotheses of
  `contentInput?_concat_of_parse` (`ContentPrefixExtensionCoincidence.lean`) — the successful strict
  parse `hparse` and the target agreement `hn : input.n = n` — because the parsed object is the
  canonical `toPrefixInput`, whose `n` field *is* the raw `n`.  No injectivity of
  `treeMCSPPrefixM codec` and no gamma canonicity is used.
* Prefix agreement is **vacuous**: `zeroPrefixFields` sets `i := 0`, `toPrefixInput` copies `i`
  verbatim, and `PrefixInput.prefixAgrees` quantifies over `Fin input.i`.
* The search relation comes from codec **completeness**
  (`TreeCircuitWitnessCodec.complete`, `SearchMCSPConcreteTargets.lean`), with the produced witness
  transported into the certificate's leading `witnessBits` block by `contentWitness_concat`
  (`ContentPrefixExtensionCoincidence.lean`).
* The concrete discharge takes the all-false truth table together with `Circuit.const false`, of
  size `1`, and the threshold arithmetic `1 ≤ thresholdPoly k n = n ^ k + k` (at `k = 0` the first
  summand is `n ^ 0 = 1`; at `k ≥ 1` the second summand already suffices).

Scope — non-vacuity only.  What is proved here is that specific words are accepted; nothing about
how hard acceptance is to *decide*:

* **no** verifier Turing machine, runtime bound, or `TM.accepts` bridge for `L'`;
* **no** `ContentPrefixExtensionNPWitness` instance and no `NP (ContentPrefixExtensionLanguage …)`;
* this module shows the re-decode gate does not fire on the *constructed* zero-prefix words below,
  via the parse round-trip; the separate I1 module `ContentPrefixExtensionGateClosure.lean` proves
  its convention-length equality unconditionally vacuous after any successful header decode and
  leaves exactly the tag, decoded-index, and inactive-padding read-value tests;
* **no** lower bound, no `NoPolynomialBoundedSearchSolver`, and no change to any
  `VerifiedNPDAGLowerBoundSource` or `SearchMCSPMagnificationContract`.

**Progress classification (AGENTS.md): Infrastructure.**  This is a satisfiability (non-emptiness)
witness for the content-verifier specification.  It builds no verifier machine, proves no
separation, and discharges no lower-bound obligation.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-! ## Carrying a full witness inside a certificate -/

/-- The certificate that stores a full search witness in its leading `codec.witnessBits n` block and
blanks the rest.  This is the shape the content witness window reads back. -/
private def witnessCertificate {threshold : Nat → Nat} (codec : TreeCircuitWitnessCodec threshold)
    (n m : Nat) (w : PrefixBitVec (codec.witnessBits n)) :
    Pnp3.ComplexityInterfaces.Bitstring (Pnp3.ComplexityInterfaces.certificateLength m 1) :=
  fun j => if h : j.1 < codec.witnessBits n then w ⟨j.1, h⟩ else false

/-- The content witness window of a concatenation reads `witnessCertificate` back exactly.  The
hypothesis `hgate` is the same "query sits at its own convention length" condition that
`contentWitness_concat` needs. -/
private theorem contentWitness_witnessCertificate {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {m n : Nat} (y : PrefixBitVec m)
    (w : PrefixBitVec (codec.witnessBits n)) (hgate : m = treeMCSPPrefixM codec n) :
    contentWitness codec
        (Pnp3.ComplexityInterfaces.concatBitstring y (witnessCertificate codec n m w)) n = w := by
  funext j
  rw [contentWitness_concat codec y (witnessCertificate codec n m w) hgate j]
  unfold witnessCertificate
  simp only [dif_pos (show (j : Nat) < codec.witnessBits n from j.2)]

/-- Prefix agreement is vacuous at active prefix length `0`: `PrefixInput.prefixAgrees` quantifies
over `Fin input.i`, so an empty active prefix imposes nothing on the witness. -/
private theorem prefixAgrees_of_i_eq_zero {problem : SearchMCSPCompressionProblem} {m : Nat}
    (input : PrefixInput problem m) (hi : input.i = 0)
    (w : PrefixBitVec (problem.witnessBits input.n)) :
    input.prefixAgrees w := by
  intro k
  have hk0 : (k : Nat) < 0 := lt_of_lt_of_eq k.isLt hi
  exact (Nat.not_lt_zero _ hk0).elim

/-! ## The generic non-vacuity theorem -/

/-- **GATE-0, generic form.**  A satisfied tree-MCSP promise at `n` makes the *zero-prefix* query
for that instance content-extendable: some certificate makes the concatenated word
`ContentAccepts`-accepted.

All three conjuncts of `ContentAccepts` are discharged by construction.  The content parse succeeds
because `zeroPrefixQueryValue_parses` gives the strict parse together with `input.n = n`, which is
exactly what `contentInput?_concat_of_parse` consumes.  Prefix agreement is vacuous (`i = 0`).  The
relation conjunct is codec completeness, read back through `contentWitness_witnessCertificate`. -/
theorem contentAccepts_zeroPrefixQuery_of_predicate
    {threshold : Nat → Nat} (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat) (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (hpred : treeMCSPPredicate n (threshold n) x) :
    ∃ w : Pnp3.ComplexityInterfaces.Bitstring
            (Pnp3.ComplexityInterfaces.certificateLength (treeMCSPPrefixM codec n) 1),
      ContentAccepts codec
        (Pnp3.ComplexityInterfaces.concatBitstring (zeroPrefixQueryValue codec n x) w) := by
  obtain ⟨wit, hverifies⟩ := codec.complete n x hpred
  refine ⟨witnessCertificate codec n (treeMCSPPrefixM codec n) wit, ?_⟩
  refine
    ⟨⟨n, CanonicalRawTreeMCSPPrefixFields.toPrefixInput codec (zeroPrefixFields codec n x)⟩,
      ?_, ?_, ?_⟩
  · exact contentInput?_concat_of_parse codec (zeroPrefixQueryValue codec n x)
      (CanonicalRawTreeMCSPPrefixFields.toPrefixInput codec (zeroPrefixFields codec n x))
      (parse_zeroPrefixQueryValue codec n x) rfl
      (witnessCertificate codec n (treeMCSPPrefixM codec n) wit)
  · exact prefixAgrees_of_i_eq_zero
      (CanonicalRawTreeMCSPPrefixFields.toPrefixInput codec (zeroPrefixFields codec n x)) rfl _
  · show (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec)).relation
      n x
      (contentWitness codec
        (Pnp3.ComplexityInterfaces.concatBitstring (zeroPrefixQueryValue codec n x)
          (witnessCertificate codec n (treeMCSPPrefixM codec n) wit)) n)
    rw [contentWitness_witnessCertificate codec (zeroPrefixQueryValue codec n x) wit rfl]
    exact hverifies

/-- **GATE-0, language form.**  Hence the zero-prefix query for a promised instance is a member of
the content-truthful language `L'` at its own convention length.  This is the first unconditional
membership statement for `L'` in the development. -/
theorem contentPrefixExtensionLanguage_zeroPrefixQuery
    {threshold : Nat → Nat} (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat) (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (hpred : treeMCSPPredicate n (threshold n) x) :
    ContentPrefixExtensionLanguage codec (treeMCSPPrefixM codec n)
      (zeroPrefixQueryValue codec n x) = true := by
  rw [ContentPrefixExtensionLanguage_accepts_iff]
  exact contentAccepts_zeroPrefixQuery_of_predicate codec n x hpred

/-! ## The concrete discharge at `treeCircuitWitnessCodec (thresholdPoly k)` -/

/-- The constant-false circuit computes the all-false truth table on `n` variables. -/
private theorem const_false_computes_allFalse (n : Nat) :
    ComputesTruthTable treeCircuitClass (Pnp3.Models.Circuit.const false)
      (fun _ : Fin (Pnp3.Models.Partial.tableLen n) => false) := by
  intro _
  rfl

/-- Every polynomial threshold admits at least one gate: `1 ≤ n ^ k + k`.  At `k = 0` the power
summand is `n ^ 0 = 1`; at `k ≥ 1` the additive summand already suffices. -/
private theorem one_le_thresholdPoly (k n : Nat) : 1 ≤ thresholdPoly k n := by
  unfold thresholdPoly
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp
  · omega

/-- The all-false truth table satisfies the tree-MCSP promise at every polynomial threshold,
witnessed by `Circuit.const false` of size `1`. -/
private theorem treeMCSPPredicate_allFalse_thresholdPoly (k n : Nat) :
    treeMCSPPredicate n (thresholdPoly k n)
      (fun _ : Fin (Pnp3.Models.Partial.tableLen n) => false) :=
  ⟨Pnp3.Models.Circuit.const false,
    by simpa [treeCircuitClass, Pnp3.Models.Circuit.size] using one_le_thresholdPoly k n,
    const_false_computes_allFalse n⟩

/-- **GATE-0 headline: `ContentAccepts` is non-vacuous at the concrete codec.**  For every exponent
`k` and every target `n` there is an accepted word, of exactly the query-plus-certificate length the
verifier interface evaluates at.  The binder `n` is load-bearing: it fixes the instance the witness
is built at, and hence the word's length.

The witness is the zero-prefix query for the all-false table on `n` variables, concatenated with the
certificate carrying `Circuit.const false`'s encoding.  So `L'` is not the empty language, and the
`NoPolynomialBoundedSearchSolver` hypothesis of the consolidated CT source is not refuted by
vacuity.  This says nothing about the *complexity* of `L'`: no machine, runtime bound, or
`TM.accepts` bridge is constructed here. -/
theorem contentAccepts_nonvacuous_treePoly (k n : Nat) :
    ∃ z : PrefixBitVec
            (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n
              + Pnp3.ComplexityInterfaces.certificateLength
                  (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n) 1),
      ContentAccepts (treeCircuitWitnessCodec (thresholdPoly k)) z := by
  obtain ⟨w, hw⟩ :=
    contentAccepts_zeroPrefixQuery_of_predicate (treeCircuitWitnessCodec (thresholdPoly k)) n
      (fun _ => false) (treeMCSPPredicate_allFalse_thresholdPoly k n)
  exact ⟨_, hw⟩

end ContractExpansion
end Frontier
end Pnp4
