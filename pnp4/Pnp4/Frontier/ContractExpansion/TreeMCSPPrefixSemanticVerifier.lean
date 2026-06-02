import Pnp4.Frontier.ContractExpansion.PrefixParserConvention
import Pnp4.Frontier.ContractExpansion.PrefixExtensionLanguageNP
import Pnp4.Frontier.ContractExpansion.ConcreteTreeCodec
import Pnp4.Frontier.ContractExpansion.ThresholdGrowth
import Complexity.Interfaces

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-!
# Semantic verifier for the tree-MCSP prefix-extension language

This module discharges the **mathematical core** of the NP-membership obligation
`PrefixExtensionNPWitness` (`PrefixExtensionNPWitness.lean`) — *without* yet building
a Turing machine or a runtime bound.

The canonical NP witness requires a `correct` field of the shape

```
PrefixExtensionLanguage parser n x = true ↔
  ∃ w : Bitstring (certificateLength n k), TM.accepts M (concatBitstring x w) = true
```

Here we build a **computable, `Bool`-valued** verifier `treePrefixSemanticAccepts` over an
explicit certificate and prove exactly that equivalence with `treePrefixSemanticAccepts`
standing in for `TM.accepts (concatBitstring x w)`, at the certificate exponent `k = 1`
(`certificateLength N 1 = N + 1`).  A later TM-construction track then only has to bridge
`TM.accepts (concatBitstring x w) = treePrefixSemanticAccepts …` and supply `M` / runtime,
after which `PrefixExtensionNPWitness.correct` is this theorem composed with that bridge.

## Certificate length

A certificate of length `certificateLength N 1 = N + 1` always suffices: a successful parse
forces `N = treeMCSPPrefixM codec input.n` (`parseTreeMCSPPrefixInput_length_convention`), and
`codec.witnessBits input.n ≤ treeMCSPPrefixM codec input.n` (`witnessBits_le_treeMCSPPrefixM`),
so the first `witnessBits input.n` certificate bits decode the witness prefix
(`extractWitness?` / `extractWitness_eq`, the central dependent-slice lemma).

## Axiom budget

All results stay within the standard axiom set `[propext, Classical.choice, Quot.sound]` (verified
in `AxiomsAudit.lean`).  The checks go through genuine `Decidable` instances
(`Fintype.decidableForallFintype`, `TreeCircuitWitnessCodec.verifiesDecidable`), never
`Classical.propDecidable`, so `treePrefixSemanticAccepts` is computable.

* `witnessBits_le_treeMCSPPrefixM`, `prefixAgreesBool_eq_true_iff`, `extractWitness_eq` are
  `Classical`-free (`[propext]` / `[propext, Quot.sound]`).
* `verifiesBool_eq_true_iff` — and hence `treePrefixSemanticAccepts` and every theorem mentioning
  it — inherits `Classical.choice` from the *existing* `TreeCircuitWitnessCodec.verifiesDecidable`
  (the `Classical.choice` lives only in the decidability proof terms, not the returned `Bool`).
* `treePrefixSemanticAccepts_correct` additionally relies on `Classical.choice` through the
  classical, noncomputable `PrefixExtensionLanguage` wrapper (`PrefixExtensionLanguage_accepts_iff`).

## Scope discipline

* **no** Turing machine, **no** `runTime`, **no** `concatBitstring`, **no** `NP_TM`;
* the certificate type is used only as a bit container — it is **not** routed through
  `PrefixExtensionNPWitness.correct` here;
* **no** lower bound, **no** `VerifiedNPDAGLowerBoundSource`, **no**
  `SearchMCSPMagnificationContract` change, **no** `P ≠ NP` endpoint.
-/

/-- The witness block is the final summand of the concrete length `treeMCSPPrefixM`. -/
theorem witnessBits_le_treeMCSPPrefixM
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat) :
    codec.witnessBits n ≤ treeMCSPPrefixM codec n := by
  unfold treeMCSPPrefixM
  omega

/-- Prefix agreement is decidable: it is a finite `∀` over `Fin input.i`.

`local` so that importing this verifier module does **not** alter project-wide typeclass search;
it is only needed to define `prefixAgreesBool` below via `decide`. -/
local instance instDecidablePrefixAgrees
    {problem : SearchMCSPCompressionProblem} {m : Nat}
    {input : PrefixInput problem m}
    {w : PrefixBitVec (problem.witnessBits input.n)} :
    Decidable (input.prefixAgrees w) := by
  unfold PrefixInput.prefixAgrees
  infer_instance

/-- `Bool`-valued prefix-agreement check. -/
def prefixAgreesBool
    {problem : SearchMCSPCompressionProblem} {m : Nat}
    (input : PrefixInput problem m)
    (w : PrefixBitVec (problem.witnessBits input.n)) : Bool :=
  decide (input.prefixAgrees w)

theorem prefixAgreesBool_eq_true_iff
    {problem : SearchMCSPCompressionProblem} {m : Nat}
    (input : PrefixInput problem m)
    (w : PrefixBitVec (problem.witnessBits input.n)) :
    prefixAgreesBool input w = true ↔ input.prefixAgrees w := by
  simp only [prefixAgreesBool, decide_eq_true_eq]

/-- Codec verification is decidable (reusing `verifiesDecidable`); registered as a
`local` instance so the `Bool` checker resolves it without exporting it to importers. -/
local instance instDecidableCodecVerifies
    {threshold : Nat → Nat} {codec : TreeCircuitWitnessCodec threshold}
    {n : Nat} {tt : TruthTable n} {w : PrefixBitVec (codec.witnessBits n)} :
    Decidable (codec.verifies n tt w) :=
  TreeCircuitWitnessCodec.verifiesDecidable codec n tt w

/-- `Bool`-valued codec-verification check. -/
def verifiesBool
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat) (tt : TruthTable n)
    (w : PrefixBitVec (codec.witnessBits n)) : Bool :=
  decide (codec.verifies n tt w)

theorem verifiesBool_eq_true_iff
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat) (tt : TruthTable n)
    (w : PrefixBitVec (codec.witnessBits n)) :
    verifiesBool codec n tt w = true ↔ codec.verifies n tt w := by
  simp only [verifiesBool, decide_eq_true_eq]

/-- Slicing the first `width` bits (offset `0`) of a long-enough vector recovers them. -/
theorem sliceBits?_zero
    {m width : Nat} (y : PrefixBitVec m) (h : width ≤ m) :
    sliceBits? y 0 width
      = some (fun j : Fin width => y ⟨j.1, Nat.lt_of_lt_of_le j.2 h⟩) := by
  unfold sliceBits?
  rw [dif_pos (show 0 + width ≤ m by omega)]
  apply congrArg some
  funext j
  exact congrArg y (Fin.ext (by simp))

/-- A length-`certificateLength N 1` certificate is long enough to hold the witness prefix. -/
theorem witnessBits_le_certificateLength
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (n N : Nat)
    (hM : N = treeMCSPPrefixM codec n) :
    codec.witnessBits n ≤ Pnp3.ComplexityInterfaces.certificateLength N 1 := by
  have h1 := witnessBits_le_treeMCSPPrefixM codec n
  have h2 : Pnp3.ComplexityInterfaces.certificateLength N 1 = N + 1 := by
    simp [Pnp3.ComplexityInterfaces.certificateLength]
  omega

/-- Decode the witness prefix from the leading bits of a certificate. -/
def extractWitness?
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (N : Nat)
    (cert : PrefixBitVec (Pnp3.ComplexityInterfaces.certificateLength N 1))
    {m : Nat}
    (input : PrefixInput
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec)) m) :
    Option (PrefixBitVec (codec.witnessBits input.n)) :=
  sliceBits? cert 0 (codec.witnessBits input.n)

/-- Under the length convention, extraction succeeds and returns the leading certificate bits. -/
theorem extractWitness_eq
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (N : Nat)
    (cert : PrefixBitVec (Pnp3.ComplexityInterfaces.certificateLength N 1))
    {m : Nat}
    (input : PrefixInput
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec)) m)
    (hM : N = treeMCSPPrefixM codec input.n) :
    extractWitness? codec N cert input
      = some (fun j : Fin (codec.witnessBits input.n) =>
          cert ⟨j.1, Nat.lt_of_lt_of_le j.2
            (witnessBits_le_certificateLength codec input.n N hM)⟩) := by
  unfold extractWitness?
  exact sliceBits?_zero cert (witnessBits_le_certificateLength codec input.n N hM)

/--
The semantic verifier: parse the query, slice the witness prefix out of the certificate,
and check prefix agreement together with codec verification.  Fully computable.
-/
def treePrefixSemanticAccepts
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (N : Nat)
    (query : PrefixBitVec N)
    (cert : PrefixBitVec (Pnp3.ComplexityInterfaces.certificateLength N 1)) : Bool :=
  match parseTreeMCSPPrefixInput threshold codec query with
  | none => false
  | some input =>
      match extractWitness? codec N cert input with
      | none => false
      | some w => prefixAgreesBool input w && verifiesBool codec input.n input.x w

/-- Reduction of the verifier when both the parse and the extraction succeed. -/
theorem treePrefixSemanticAccepts_eq_of_parse_extract
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (N : Nat) (query : PrefixBitVec N)
    (cert : PrefixBitVec (Pnp3.ComplexityInterfaces.certificateLength N 1))
    {input : PrefixInput
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec)) N}
    {w : PrefixBitVec (codec.witnessBits input.n)}
    (hp : parseTreeMCSPPrefixInput threshold codec query = some input)
    (hw : extractWitness? codec N cert input = some w) :
    treePrefixSemanticAccepts codec N query cert
      = (prefixAgreesBool input w && verifiesBool codec input.n input.x w) := by
  simp only [treePrefixSemanticAccepts, hp, hw]

/-- Reduction of the verifier when the parse succeeds but extraction fails. -/
theorem treePrefixSemanticAccepts_eq_false_of_extract_none
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (N : Nat) (query : PrefixBitVec N)
    (cert : PrefixBitVec (Pnp3.ComplexityInterfaces.certificateLength N 1))
    {input : PrefixInput
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec)) N}
    (hp : parseTreeMCSPPrefixInput threshold codec query = some input)
    (hw : extractWitness? codec N cert input = none) :
    treePrefixSemanticAccepts codec N query cert = false := by
  simp only [treePrefixSemanticAccepts, hp, hw]

/--
**Malformed queries are rejected.**  If the parser fails, the verifier rejects every
certificate.  Reusable for the later TM bridge.
-/
theorem treePrefixSemanticAccepts_rejects_malformed
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (N : Nat) (query : PrefixBitVec N)
    (hp : parseTreeMCSPPrefixInput threshold codec query = none)
    (cert : PrefixBitVec (Pnp3.ComplexityInterfaces.certificateLength N 1)) :
    treePrefixSemanticAccepts codec N query cert = false := by
  simp only [treePrefixSemanticAccepts, hp]

/--
**Semantic correctness (headline).**  The prefix-extension language accepts a query iff some
certificate makes the semantic verifier accept.  This is the mathematical core of the
`PrefixExtensionNPWitness.correct` obligation at `k = 1` (modulo the still-to-build
`TM.accepts (concatBitstring x w) = treePrefixSemanticAccepts …` bridge).
-/
theorem treePrefixSemanticAccepts_correct
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (N : Nat) (query : PrefixBitVec N) :
    PrefixExtensionLanguage (treeMCSPConcretePrefixParser threshold codec) N query = true
      ↔ ∃ cert : PrefixBitVec (Pnp3.ComplexityInterfaces.certificateLength N 1),
          treePrefixSemanticAccepts codec N query cert = true := by
  classical
  rw [PrefixExtensionLanguage_accepts_iff]
  constructor
  · -- forward: prefix-extendable ⇒ a certificate accepts
    rintro ⟨input, hparse, w, hagrees, hrel⟩
    have hp : parseTreeMCSPPrefixInput threshold codec query = some input := hparse
    have hM := parseTreeMCSPPrefixInput_length_convention threshold codec query input hp
    refine ⟨fun j => if hh : j.1 < codec.witnessBits input.n then w ⟨j.1, hh⟩ else false, ?_⟩
    have hextract :
        extractWitness? codec N
          (fun j => if hh : j.1 < codec.witnessBits input.n then w ⟨j.1, hh⟩ else false) input
          = some w := by
      rw [extractWitness_eq codec N _ input hM]
      apply congrArg some
      funext j
      simp only [j.2, dif_pos, Fin.eta]
    rw [treePrefixSemanticAccepts_eq_of_parse_extract codec N query _ hp hextract,
      Bool.and_eq_true]
    refine ⟨(prefixAgreesBool_eq_true_iff input w).mpr hagrees, ?_⟩
    refine (verifiesBool_eq_true_iff codec input.n input.x w).mpr ?_
    dsimp [treeMCSPSearchProblem, TreeMCSPSearchWitnessEncoding.ofCodec] at hrel
    exact hrel
  · -- backward: an accepting certificate ⇒ prefix-extendable
    rintro ⟨cert, hacc⟩
    cases hp : parseTreeMCSPPrefixInput threshold codec query with
    | none =>
        rw [treePrefixSemanticAccepts_rejects_malformed codec N query hp cert] at hacc
        simp at hacc
    | some input =>
        have hM := parseTreeMCSPPrefixInput_length_convention threshold codec query input hp
        cases hext : extractWitness? codec N cert input with
        | none =>
            rw [treePrefixSemanticAccepts_eq_false_of_extract_none codec N query cert hp hext]
              at hacc
            simp at hacc
        | some w =>
            rw [treePrefixSemanticAccepts_eq_of_parse_extract codec N query cert hp hext,
              Bool.and_eq_true] at hacc
            obtain ⟨hAg, hVer⟩ := hacc
            refine ⟨input, hp, w, (prefixAgreesBool_eq_true_iff input w).mp hAg, ?_⟩
            dsimp [treeMCSPSearchProblem, TreeMCSPSearchWitnessEncoding.ofCodec]
            exact (verifiesBool_eq_true_iff codec input.n input.x w).mp hVer

/-! ## Directed regression checks on the concrete `thresholdPoly 1` codec -/

section Regression

/-- Malformed (unparsable) queries are rejected for every certificate. -/
example (N : Nat) (query : PrefixBitVec N)
    (hp : parseTreeMCSPPrefixInput (thresholdPoly 1)
        (treeCircuitWitnessCodec (thresholdPoly 1)) query = none)
    (cert : PrefixBitVec (Pnp3.ComplexityInterfaces.certificateLength N 1)) :
    treePrefixSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly 1)) N query cert = false :=
  treePrefixSemanticAccepts_rejects_malformed _ N query hp cert

/-- A wrong version tag ⇒ the verifier rejects every certificate (end-to-end). -/
example (N : Nat) (query : PrefixBitVec N) {tag : Nat}
    (htag : readNatBE query 0 tagLen = some tag) (hbad : tag ≠ treePrefixTag)
    (cert : PrefixBitVec (Pnp3.ComplexityInterfaces.certificateLength N 1)) :
    treePrefixSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly 1)) N query cert = false :=
  treePrefixSemanticAccepts_rejects_malformed _ N query
    (parseTreeMCSPPrefixInput_bad_tag (thresholdPoly 1)
      (treeCircuitWitnessCodec (thresholdPoly 1)) query htag hbad) cert

/-- Accept path: a successful parse + extraction with both checks passing accepts. -/
example (N : Nat) (query : PrefixBitVec N)
    (cert : PrefixBitVec (Pnp3.ComplexityInterfaces.certificateLength N 1))
    {input : PrefixInput (treeMCSPSearchProblem (thresholdPoly 1)
      (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly 1)))) N}
    {w : PrefixBitVec ((treeCircuitWitnessCodec (thresholdPoly 1)).witnessBits input.n)}
    (hp : parseTreeMCSPPrefixInput (thresholdPoly 1)
        (treeCircuitWitnessCodec (thresholdPoly 1)) query = some input)
    (hw : extractWitness? (treeCircuitWitnessCodec (thresholdPoly 1)) N cert input = some w)
    (hAg : input.prefixAgrees w)
    (hVer : (treeCircuitWitnessCodec (thresholdPoly 1)).verifies input.n input.x w) :
    treePrefixSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly 1)) N query cert = true := by
  rw [treePrefixSemanticAccepts_eq_of_parse_extract _ N query cert hp hw, Bool.and_eq_true]
  exact ⟨(prefixAgreesBool_eq_true_iff input w).mpr hAg,
    (verifiesBool_eq_true_iff _ input.n input.x w).mpr hVer⟩

end Regression

end ContractExpansion
end Frontier
end Pnp4
