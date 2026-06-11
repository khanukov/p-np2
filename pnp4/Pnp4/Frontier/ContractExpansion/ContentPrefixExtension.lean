import Pnp4.Frontier.ContractExpansion.PrefixParserConvention

/-!
# The content-truthful prefix-extension language — the §13 repair, brick R1/R2

§13 of `TM_VERIFIER_STRATEGY.md` records a verified obstruction: the ambient language
`PrefixExtensionLanguage` gates membership on the **physical** input length (the parser's
`m = treeMCSPPrefixM codec n` check), which a length-blind idle-sink TM provably cannot replicate —
so the NP-witness bridge `(★)` is unprovable for the planned machine class.

This module defines the **content-truthful** variant `L'`: membership at *any* physical length is
determined by the fields read **at offsets computed from the content itself** (the gamma header
decodes the target `n`; the query window is the first `treeMCSPPrefixM codec n` cells of the
blank-padded word; the witness window follows it).  The physical length enters only through the
blank padding — exactly the information a length-blind machine actually has.

Definitions only (plus the immediate `accepts_iff` unwrapping and the NP-witness interface):

* `padRead` / `padWord` — total blank-padded reads of a finite bitstring, mirroring the TM tape
  (`initialConfig` loads the input and pads with `false`);
* `contentHeader?` — the gamma header read on the `2N+1`-padded word: with this margin every read
  the strict decoder performs is in range, so the strict spec behaves **exactly** like the machine
  reading blanks (no spurious out-of-range failures);
* `contentInput?` — the parser re-run on the **computed-length** window `padWord z (M n')`: the
  parser's physical-length gate `m = M n'` is then satisfied *by construction*, making it vacuous —
  the heart of the repair;
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
The margin guarantees that every cell the strict decoder touches on a *successful* machine-style
read is in range — a terminator within the support has its whole payload inside `2N+1` — so the
strict spec coincides with what a blank-reading machine computes.  (If the content has no
terminator, both the spec and the machine fail to decode: the spec by running out of word, the
machine by scanning blanks forever.) -/
def contentHeader? {N : Nat} (z : PrefixBitVec N) : Option (Nat × Nat) :=
  decodeGamma? (padWord z (2 * N + 1)) tagLen

/-- The content-computed parse: decode the header `n'`, then run the **existing strict parser** on
the padded window of the *computed* convention length `treeMCSPPrefixM codec n'`.  The parser's
physical-length gate `m = treeMCSPPrefixM codec n` is satisfied by construction. -/
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
succeeds and the witness window extends the decoded prefix through the search relation.  No
reference to the physical length anywhere — only padded reads at content-computed offsets. -/
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

/-- **The content-truthful prefix-extension language `L'`** (§13.3): membership at any physical
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

/-- **The content-truthful NP witness** — the §13-repaired input (2): a verifier TM, polynomial
runtime, and certificate correctness **against `L'`**.  Mirrors `PrefixExtensionNPWitness`; unlike
the length-gated original, this `correct` field is achievable by a length-blind idle-sink machine
(the language itself is a function of the padded content only). -/
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
