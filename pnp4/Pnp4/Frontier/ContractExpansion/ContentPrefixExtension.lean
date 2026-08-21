import Pnp4.Frontier.ContractExpansion.PrefixParserConvention

/-!
# The content-truthful prefix-extension language — the physical-length-gate repair, brick R1/R2

The obstruction this addresses (described in this directory's `README.md`): the ambient language
`PrefixExtensionLanguage` gates membership on the **physical** input length (the parser's
`m = treeMCSPPrefixM codec n` check), and the *planned* idle-sink verifier — a machine that reads
only the content `initialConfig` loaded into the tape and then idles — has no way to replicate that
gate.  This is a limitation of that planned construction, **not** of the `pnp3` TM model: the model
is *not* length-blind.  `Pnp3.Internal.PsubsetPpoly.TM` runs inputs of length `n` on a tape of
length `TM.tapeLength n = n + runTime n + 1` for exactly `runTime n` steps, and `runTime : ℕ → ℕ`
is an arbitrary structure field, so a word and its zero-extension are *different-length* inputs run
on different-length tapes for possibly different step counts; only the loaded tape *contents* agree
cell-by-cell where both tapes exist.  The whole argument is in any case a review of the
definitions, **not** a Lean refutation: nothing here formally proves
`PrefixExtensionNPWitness.correct` unprovable.

This module defines the **content-truthful** variant `L'`: membership at *any* physical length is
determined by the fields read **at offsets computed from the content itself** (the gamma header
decodes the target `n`; the query window is the first `treeMCSPPrefixM codec n` cells of the
blank-padded word; the witness window follows it).  What `L'` drops is the *explicit* gate on the
**original ambient length**: no test in `L'` compares the physical `N` against
`treeMCSPPrefixM codec n`.  The strict parser's own `m = treeMCSPPrefixM codec n` equality test is
**not** removed — `contentInput?` invokes that parser on the *computed* window
`padWord z (treeMCSPPrefixM codec n')`, where the test survives as a comparison of the computed
window's length against the parser's *re-decoded* target, and its intended vacuity is **unproved**
(see `contentInput?` below).  Syntactically, `L'` still mentions the physical length `N`:
`contentHeader?` decodes on the `2N+1`-padded word, so `N` fixes both that window's width and the
gamma decoder's fuel (`decodeGamma?` uses `m + 1`).  Closing that residual `N`-dependence is what a
padding-stability lemma has to do; no such lemma is proved **in this module** — it is discharged, for
`ContentAccepts` on *complete* words, in `ContentPrefixExtensionPadding.lean`
(`contentHeader?_padWord_of_le`, `ContentAccepts_padWord_of_le`,
`ContentAccepts_iff_of_padRead_eq`), which does not affect any statement below.  The scope of those
lemmas is exactly `ContentAccepts`: padding invariance of the language wrapper
`ContentPrefixExtensionLanguage` — whose membership at physical length `m` quantifies over
certificates of length `certificateLength m 1` concatenated at offset `m`, both of which move with
`m` — is **not** proved, and neither is any verifier TM, runtime bound, or `TM.accepts` bridge
for `L'`.

Definitions only (plus the immediate `accepts_iff` unwrapping and the NP-witness interface):

* `padRead` / `padWord` — total blank-padded reads of a finite bitstring, mirroring the TM tape
  (`initialConfig` loads the input and pads with `false`);
* `contentHeader?` — the gamma header read on the `2N+1`-padded word.  The margin is *intended* to
  keep every read of a successful strict decode in range, so that the spec matches a blank-reading
  machine; that intent is **not formalized here** — the padding-stability lemmas for the header and
  for `ContentAccepts` live in `ContentPrefixExtensionPadding.lean`;
* `contentInput?` — the parser re-run on the **computed-length** window `padWord z (M n')`.  The
  parser re-decodes the header from that *narrower* window and gates on `m = M n_dec` for the
  re-decoded `n_dec`.  `ContentPrefixExtensionGateClosure.lean` proves the required narrowing and
  `contentInput?_lengthGate_vacuous`: after a successful header decode this equality check compares
  `M n'` with itself.  The parser may still reject at its tag, decoded-index, or inactive-padding
  value tests;
* `contentWitness` — the witness window read just past the computed query window;
* `ContentAccepts` / `ContentPrefixExtendable` / `ContentPrefixExtensionLanguage` — the language;
* `ContentPrefixExtensionNPWitness` + `contentPrefixExtensionLanguage_in_NP_of_witness` — the
  NP-witness interface for `L'` (the new input (2) target), mirroring `PrefixExtensionNPWitness`.

The old length-gated language and its chain are **left intact**; the coincidence lemma (brick R3)
and the extraction transfer (brick R4) connect `L'` to the existing decision→search machinery.

**Progress classification (AGENTS.md): Infrastructure** — specification repair for the NP-verifier
track; defines a language and an interface, proves no separation.  Standard `[propext,
Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-! ### Blank-padded reads (the tape model of a finite input) -/

/-- Read bit `j` of a finite bitstring through the TM's blank padding: in-range cells give the
stored bit, everything past the support is the blank `false` — exactly `initialConfig`'s tape. -/
def padRead {N : Nat} (z : PrefixBitVec N) (j : Nat) : Bool :=
  if h : j < N then z ⟨j, h⟩ else false

/-- The blank-padded word, cut (or extended) to length `T`. -/
def padWord {N : Nat} (z : PrefixBitVec N) (T : Nat) : PrefixBitVec T :=
  fun j => padRead z j.1

@[simp] theorem padRead_lt {N : Nat} (z : PrefixBitVec N) {j : Nat} (h : j < N) :
    padRead z j = z ⟨j, h⟩ := by
  simp [padRead, h]

@[simp] theorem padRead_ge {N : Nat} (z : PrefixBitVec N) {j : Nat} (h : N ≤ j) :
    padRead z j = false := by
  simp [padRead, Nat.not_lt_of_ge h]

@[simp] theorem padWord_apply {N T : Nat} (z : PrefixBitVec N) (j : Fin T) :
    padWord z T j = padRead z j.1 := rfl

/-- Padding a vector to its own length is the identity. -/
theorem padWord_self {N : Nat} (z : PrefixBitVec N) : padWord z N = z := by
  funext j
  simp [padWord, padRead, j.2]

/-! ### The content-computed window -/

variable {threshold : Nat → Nat}

/-- The content-read gamma header: decode the Elias-gamma target length on the `2N+1`-padded word.
The `2N+1` margin is chosen so that a terminator inside the support has its whole payload inside the
padded window — the design intent being that the strict spec agree with what a blank-reading machine
computes.  No lemma **in this module** relates this decode across different physical lengths; the
padding-stability statement `contentHeader?_padWord_of_le` is proved in
`ContentPrefixExtensionPadding.lean`.  **Agreement with a machine is still not established**: no
verifier TM exists here, so the margin remains a definitional choice. -/
def contentHeader? {N : Nat} (z : PrefixBitVec N) : Option (Nat × Nat) :=
  decodeGamma? (padWord z (2 * N + 1)) tagLen

/-- The content-computed parse: decode the header `n'`, then run the **existing strict parser** on
the padded window of the *computed* convention length `treeMCSPPrefixM codec n'`.  The parser
re-decodes its own header from that narrower window and gates on `m = treeMCSPPrefixM codec n_dec`
for the re-decoded `n_dec`.  The separate I1 module
`ContentPrefixExtensionGateClosure.lean` proves that a successful wide (`2N+1`) decode re-succeeds
on this narrow window and that the convention-length equality gate is vacuous.  It does **not** say
that `contentInput?` always succeeds: the tag, decoded-index, and inactive-padding value tests remain
genuine rejection points. -/
def contentInput? (codec : TreeCircuitWitnessCodec threshold) {N : Nat} (z : PrefixBitVec N) :
    Option (Σ n' : Nat,
      PrefixInput (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec))
        (treeMCSPPrefixM codec n')) :=
  match contentHeader? z with
  | none => none
  | some (n', _) =>
      (parseTreeMCSPPrefixInput threshold codec (padWord z (treeMCSPPrefixM codec n'))).map
        (fun input => ⟨n', input⟩)

/-- The content-read witness window: `codec.witnessBits n` cells starting right after the computed
query window `treeMCSPPrefixM codec n`. -/
def contentWitness (codec : TreeCircuitWitnessCodec threshold) {N : Nat} (z : PrefixBitVec N)
    (n : Nat) : PrefixBitVec (codec.witnessBits n) :=
  fun j => padRead z (treeMCSPPrefixM codec n + j.1)

/-- **Content acceptance** of a full (query ++ certificate) word: the content-computed parse
succeeds and the witness window extends the decoded prefix through the search relation.  The query
and witness windows sit at content-computed offsets and are read through `padRead`, so no
*explicit* gate compares the ambient physical length `N` against a convention length.  The strict
parser's own `m = treeMCSPPrefixM codec n_dec` gate is still executed inside `contentInput?`, on the
*computed* window rather than on `N`; the separate I1 gate-closure theorem rules out rejection at
that equality gate after a successful header decode, while three value tests may still reject.
Syntactically the
definition still mentions the physical length `N`: `contentInput?` calls `contentHeader?`, which
decodes on `padWord z (2 * N + 1)`, so `N` fixes that window's width and the decoder's fuel.  That
the *value* does not move with `N` — invariance of `ContentAccepts` under blank padding, and under
equality of padded tapes — is **not proved here**; it is proved in
`ContentPrefixExtensionPadding.lean` (`ContentAccepts_padWord_of_le`,
`ContentAccepts_iff_of_padRead_eq`), for this predicate on complete words only, not for the language
wrapper below. -/
def ContentAccepts (codec : TreeCircuitWitnessCodec threshold) {N : Nat}
    (z : PrefixBitVec N) : Prop :=
  ∃ pr : (Σ n' : Nat,
      PrefixInput (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec))
        (treeMCSPPrefixM codec n')),
    contentInput? codec z = some pr
      ∧ pr.2.prefixAgrees (contentWitness codec z pr.2.n)
      ∧ (treeMCSPSearchProblem threshold
          (TreeMCSPSearchWitnessEncoding.ofCodec codec)).relation pr.2.n pr.2.x
            (contentWitness codec z pr.2.n)

/-- Content-truthful prefix extendability of an ambient input: some certificate makes the
concatenated word content-accepted. -/
def ContentPrefixExtendable (codec : TreeCircuitWitnessCodec threshold) {m : Nat}
    (y : PrefixBitVec m) : Prop :=
  ∃ w : Pnp3.ComplexityInterfaces.Bitstring (Pnp3.ComplexityInterfaces.certificateLength m 1),
    ContentAccepts codec (Pnp3.ComplexityInterfaces.concatBitstring y w)

/-- **The content-truthful prefix-extension language `L'`**: membership at any physical
length is the existence of a certificate whose concatenation is content-accepted. -/
noncomputable def ContentPrefixExtensionLanguage (codec : TreeCircuitWitnessCodec threshold) :
    Pnp3.ComplexityInterfaces.Language := by
  classical
  exact fun _m y => if ContentPrefixExtendable codec y then true else false

/-- The language accepts exactly the content-extendable inputs. -/
theorem ContentPrefixExtensionLanguage_accepts_iff (codec : TreeCircuitWitnessCodec threshold)
    {m : Nat} (y : PrefixBitVec m) :
    ContentPrefixExtensionLanguage codec m y = true ↔ ContentPrefixExtendable codec y := by
  classical
  by_cases h : ContentPrefixExtendable codec y
  · unfold ContentPrefixExtensionLanguage
    simp [h]
  · unfold ContentPrefixExtensionLanguage
    simp [h]

/-! ### The NP-witness interface for `L'` (the repaired input (2) target) -/

/-- **The content-truthful NP witness** — the repaired input (2): a verifier TM, polynomial
runtime, and certificate correctness **against `L'`**.  Mirrors `PrefixExtensionNPWitness`.  This is
an **interface / hypothesis**: no machine, runtime bound, or `TM.accepts` bridge for `L'` is
constructed in this directory.  The difference from the length-gated original is definitional and
narrow: `ContentAccepts` carries no *explicit* gate on the ambient physical length — it reads
through `padRead` at content-computed offsets, and never compares `N` against
`treeMCSPPrefixM codec n` — so the length-gate step of the obstruction has nothing to attach to.
The strict parser's own equality gate is not gone; `contentInput?` still runs it against the
*computed* window length, with vacuity unproved.
Three things are **not** claimed.  (i) That `L'` is independent of the physical length.  Padding
stability is proved only for `ContentAccepts` on *complete* words
(`ContentPrefixExtensionPadding.lean`: `ContentAccepts_padWord_of_le`,
`ContentAccepts_iff_of_padRead_eq`), while membership in `L'` at length `m` quantifies over
certificates of length `certificateLength m 1` concatenated at offset `m`, both of which move with
`m`; wrapper-level padding invariance is unproved, and the `runTime` field below is likewise
evaluated at the length-dependent point `n + certificateLength n 1`.  (ii) That those lemmas bring
the `correct` field below any closer to provable — they are specification-side only: no verifier
machine, runtime bound, or `TM.accepts` bridge for `L'` is constructed anywhere.  (iii) That a
polynomial-time verifier for `L'` exists — open.  Satisfiability of `ContentAccepts` is established
separately by `ContentPrefixExtensionNonVacuity.lean`, which constructs concrete accepted words but
does not supply the verifier machine, runtime theorem, or `TM.accepts` bridge required below. -/
structure ContentPrefixExtensionNPWitness (codec : TreeCircuitWitnessCodec threshold) where
  /-- The verifier Turing machine reading the concatenated input+certificate. -/
  M : Pnp3.Internal.PsubsetPpoly.TM.{0}
  /-- Runtime polynomial exponent. -/
  c : Nat
  /-- The verifier runs in polynomial time in the concatenated length. -/
  runTime_poly : ∀ n,
    M.runTime (n + Pnp3.ComplexityInterfaces.certificateLength n 1)
      ≤ (n + Pnp3.ComplexityInterfaces.certificateLength n 1) ^ c + c
  /-- Certificate correctness: membership in `L'` iff some certificate is accepted. -/
  correct : ∀ n (x : Pnp3.ComplexityInterfaces.Bitstring n),
    ContentPrefixExtensionLanguage codec n x = true ↔
      ∃ w : Pnp3.ComplexityInterfaces.Bitstring
              (Pnp3.ComplexityInterfaces.certificateLength n 1),
        Pnp3.Internal.PsubsetPpoly.TM.accepts
            (M := M)
            (n := n + Pnp3.ComplexityInterfaces.certificateLength n 1)
            (Pnp3.ComplexityInterfaces.concatBitstring x w) = true

/-- **NP-membership of `L'` from a content-truthful TM witness.** -/
theorem contentPrefixExtensionLanguage_in_NP_of_witness
    (codec : TreeCircuitWitnessCodec threshold)
    (W : ContentPrefixExtensionNPWitness codec) :
    Pnp3.ComplexityInterfaces.NP (ContentPrefixExtensionLanguage codec) :=
  ⟨W.M, W.c, 1, W.runTime_poly, W.correct⟩

end ContractExpansion
end Frontier
end Pnp4
