import Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionCoincidence

/-!
# Padding stability of `ContentAccepts` — the specification-side obligation

(Not padding stability of the *language* `ContentPrefixExtensionLanguage` — see the scope bullets
below.)

The review that motivated the content-truthful language `L'` (see this directory's `README.md`) is a
mismatch between two definitions: `PrefixExtensionLanguage` gates membership on the **physical**
input length (the parser's `m = treeMCSPPrefixM codec n` check), while `initialConfig` loads an input
of length `n` into the first `n` tape cells and blanks the rest — so a word and its zero-extension
induce tapes whose *contents* agree cell-by-cell wherever both are defined, and the planned idle-sink
verifier, which reads only that loaded content, has no way to replicate the gate.
`ContentPrefixExtension.lean` repairs the *definition*; this module discharges the specification-side
obligation that CT-B explicitly left open — **the padding-stability lemma for `ContentAccepts`** —
i.e. the statement that acceptance of a *complete* finite word (query ++ certificate) is a function
of that word's blank-padded tape only:

* `padRead_padWord_of_le` / `padWord_padWord_of_le` — blank padding past the support is idempotent;
* `readBit?_padWord_of_lt` / `readBit?_padWord_of_ge` / `readNatBE_padWord_transfer` — the strict
  readers on a padded word, and transfer of a successful fixed-width read to any padding whose
  width covers the read (**both** directions of widening: the shrinking direction is what the
  monotonicity lemmas of `ContentPrefixExtensionCoincidence.lean` cannot give);
* `decodeGammaAux?_padWord_support` — the **blank-tail lemma**: a successful gamma scan on a padded
  word has its terminator strictly inside the support, since every cell past the support reads
  blank.  This is what makes the shrinking direction sound at all;
* `decodeGammaAux?_padWord_canonical` — combining the two: a successful scan on *any* padding
  re-runs successfully on *any* padding of width `≥ 2N+1`, under the **explicit theorem hypothesis**
  `N + 1 ≤ fuel' + zeros` on the target fuel.  That initial bound is *assumed*, not proved; what the
  induction proves is that it is **preserved** by the scan step, and both callers in this module
  (`contentHeader?_padWord_of_le`, `contentHeader?_of_decodeGamma`) **discharge** it at their
  concrete fuel `2 * width + 2` with `zeros = 0`;
* `contentHeader?_padWord_of_le`, `contentInput?_padWord_of_le`, `contentWitness_padWord_of_le` —
  the three content-computed reads are padding-stable;
* **`ContentAccepts_padWord_of_le`** — the headline: acceptance of a word is unchanged by blank
  padding to any larger physical length;
* `ContentAccepts_iff_of_padRead_eq` — the fully general form: any two finite words with the *same*
  blank-padded tape are accepted alike (via `eq_padWord_of_padRead_eq`, which shows the padded form
  is the only shape such a pair can have).

Taken together, these close the residual `N`-dependence that `ContentPrefixExtension.lean` records:
`contentHeader?` still *syntactically* decodes on `padWord z (2 * N + 1)`, but
`contentHeader?_padWord_of_le` shows the result does not move with `N`, so the ambient physical
length of a complete word is no longer observable **in `ContentAccepts`**.  That is an invariance
property of one predicate of the specification, and of nothing else.  In particular:

* **it is not padding-invariance of the language `L'` (`ContentPrefixExtensionLanguage`).**  Every
  statement below is about `ContentAccepts` applied to a *complete* word.  Membership of a *query*
  `y` at physical length `m` unfolds (via `ContentPrefixExtendable`) to
  `∃ w : Bitstring (certificateLength m 1), ContentAccepts codec (concatBitstring y w)`, and **both**
  the certificate length and the offset at which `w` is concatenated are functions of `m`.  Padding
  `y` moves that boundary and changes the family of certificates quantified over, so nothing here
  relates `ContentPrefixExtensionLanguage codec m y` to
  `ContentPrefixExtensionLanguage codec m' (padWord y m')`: **wrapper-level padding invariance is not
  proved**, and the `L'` NP-witness interface is untouched;
* **it is not a statement that the `pnp3` TM model is length-blind — it is not.**
  `TM.tapeLength n = n + TM.runTime n + 1`, `runTime : ℕ → ℕ` is an arbitrary structure field, and
  `TM.accepts` is evaluated at exactly step `runTime n`, all of which move with the input length
  (`pnp3/Complexity/PsubsetPpolyInternal/TuringEncoding.lean`).  No machine is built or claimed
  here, and no impossibility result is formalised anywhere in this directory;
* **it does not prove that `contentInput?`'s surviving equality gate is vacuous.**  Stability says
  the two sides agree, *including on failure*.  `contentInput?` still runs the strict parser on the
  computed window `padWord z (treeMCSPPrefixM codec n')`, where the parser re-decodes its own header
  and gates on `m = treeMCSPPrefixM codec n_dec`; that this never fires needs `n_dec = n'` and is
  still **unproved**.

Two further lemmas are **conditional transport** statements, not existence statements:
`contentHeader?_of_decodeGamma` (an *already successful* strict decode also succeeds through the
`2N+1` margin) and `ContentAccepts_padWord_of_prefixExtendable` (an *already* prefix-extendable
query at its convention length yields a certificate whose concatenation is content-accepted, and
stays accepted at every larger physical length).  The second one's conclusion *is* an existential
over certificates, but only under its three undischarged hypotheses: **no unconditional existential
/ non-emptiness result is proved here**, so nothing in this module asserts that `ContentAccepts` is
satisfiable or that `L'` is non-empty.  Producing such a witness needs a truth table with a
threshold-respecting circuit plus the codec/parse round-trip, which is not done anywhere in this
directory.

Scope: no Turing machine, no runtime bound, no NP-witness achievability, no new source/contract
wrapper, no lower bound, no unconditional existence claim, no separation.  The `(★′)` bridge itself
(`TM.accepts … = ContentAccepts …`) is *not* claimed here; this module supplies one
specification-side ingredient that bridge would need.

**Progress classification (AGENTS.md): Infrastructure** — specification repair for the NP-verifier
track; proves no separation.  Verified axiom footprint (`#print axioms`, see
`Pnp4/Tests/AxiomsAudit.lean`): `readBit?_padWord_of_lt` is axiom-free, the other fourteen
padding-stability theorems are `[propext, Quot.sound]`, and only
`ContentAccepts_padWord_of_prefixExtendable` adds `Classical.choice` — via the noncomputable
`concatBitstring` and the classical language wrapper it routes through.
**No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

variable {threshold : Nat → Nat}

/-! ### Blank padding past the support is idempotent -/

/-- **Padding is idempotent for the tape read.**  Once a word has been padded to a width at least
its support, every padded read agrees with the original word's padded read — in range because the
cells were copied, out of range because both sides read the blank `false`. -/
theorem padRead_padWord_of_le {N T : Nat} (z : PrefixBitVec N) (hNT : N ≤ T) (j : Nat) :
    padRead (padWord z T) j = padRead z j := by
  by_cases hj : j < T
  · rw [padRead_lt (padWord z T) hj]
    rfl
  · rw [padRead_ge (padWord z T) (show T ≤ j by omega), padRead_ge z (show N ≤ j by omega)]

/-- Padding a padded word to any width is the same as padding the original word. -/
theorem padWord_padWord_of_le {N T : Nat} (z : PrefixBitVec N) (hNT : N ≤ T) (S : Nat) :
    padWord (padWord z T) S = padWord z S := by
  funext j
  simp only [padWord_apply, padRead_padWord_of_le z hNT]

/-- A word whose padded tape agrees with `z`'s **is** a padding of `z`: the only way to present the
same infinite tape at a larger physical length is to blank-pad. -/
theorem eq_padWord_of_padRead_eq {N N' : Nat} (z : PrefixBitVec N) (z' : PrefixBitVec N')
    (h : ∀ j, padRead z j = padRead z' j) :
    z' = padWord z N' := by
  funext j
  rw [padWord_apply, h j.1, padRead_lt z' j.2]

/-- Out-of-support reads are blank, so a `true` read pins the index inside the support. -/
theorem lt_of_padRead_eq_true {N : Nat} (z : PrefixBitVec N) {j : Nat}
    (h : padRead z j = true) : j < N := by
  by_contra hj
  rw [padRead_ge z (show N ≤ j by omega)] at h
  exact Bool.noConfusion h

/-! ### The strict readers on a padded word -/

/-- In-range strict bit read of a padded word: exactly the padded read. -/
theorem readBit?_padWord_of_lt {N : Nat} (z : PrefixBitVec N) {T j : Nat} (hj : j < T) :
    readBit? (padWord z T) j = some (padRead z j) := by
  rw [readBit?, dif_pos hj]
  rfl

/-- Past the padded width the strict reader fails (a machine, by contrast, would keep reading
blanks — which is why the padding width has to be chosen generously). -/
theorem readBit?_padWord_of_ge {N : Nat} (z : PrefixBitVec N) {T j : Nat} (hj : T ≤ j) :
    readBit? (padWord z T) j = none := by
  rw [readBit?, dif_neg (show ¬ j < T by omega)]

/-- **Fixed-width read transfer between paddings.**  A successful strict `readNatBE` on one padding
re-runs, with the same value, on any padding whose width covers the whole field.  Unlike
`readNatBE_mono` this does **not** require the target width to be larger: the bits are determined by
`z`, so shrinking is sound as soon as the field still fits. -/
theorem readNatBE_padWord_transfer {N : Nat} (z : PrefixBitVec N) {T T' : Nat} :
    ∀ {width offset v : Nat}, offset + width ≤ T' →
      readNatBE (padWord z T) offset width = some v →
      readNatBE (padWord z T') offset width = some v := by
  intro width
  induction width with
  | zero => intro offset v _ h; simpa [readNatBE] using h
  | succ k ih =>
      intro offset v hbound h
      rw [readNatBE] at h ⊢
      cases hbit : readBit? (padWord z T) offset with
      | none => rw [hbit] at h; cases h
      | some b =>
          rw [hbit] at h
          have hltT : offset < T := by
            by_contra hcon
            rw [readBit?_padWord_of_ge z (show T ≤ offset by omega)] at hbit
            cases hbit
          rw [readBit?_padWord_of_lt z hltT] at hbit
          have hbit' : readBit? (padWord z T') offset = some b := by
            rw [readBit?_padWord_of_lt z (show offset < T' by omega)]
            exact hbit
          rw [hbit']
          cases hrest : readNatBE (padWord z T) (offset + 1) k with
          | none => rw [hrest] at h; cases h
          | some rest =>
              rw [hrest] at h
              rw [ih (show offset + 1 + k ≤ T' by omega) hrest]
              exact h

/-! ### The blank-tail lemma for the gamma scan -/

/-- **Blank tail.**  A successful gamma scan on a padded word can only have found its unary
terminator *inside the support* of `z`: every cell past the support reads the blank `false`, which
the scan treats as "keep scanning".  Hence the current scan position is in support too. -/
theorem decodeGammaAux?_padWord_support {N : Nat} (z : PrefixBitVec N) {T offset : Nat} :
    ∀ {fuel zeros : Nat} {r : Nat × Nat},
      decodeGammaAux? (padWord z T) offset fuel zeros = some r → offset + zeros < N := by
  intro fuel
  induction fuel with
  | zero => intro zeros r h; cases h
  | succ f ih =>
      intro zeros r h
      rw [decodeGammaAux?] at h
      cases hbit : readBit? (padWord z T) (offset + zeros) with
      | none => rw [hbit] at h; cases h
      | some b =>
          rw [hbit] at h
          have hltT : offset + zeros < T := by
            by_contra hcon
            rw [readBit?_padWord_of_ge z (show T ≤ offset + zeros by omega)] at hbit
            cases hbit
          rw [readBit?_padWord_of_lt z hltT] at hbit
          cases b with
          | true =>
              exact lt_of_padRead_eq_true z (Option.some.inj hbit)
          | false =>
              have hstep : decodeGammaAux? (padWord z T) offset f (zeros + 1) = some r := h
              have hnext : offset + (zeros + 1) < N := ih hstep
              omega

/-- **Canonical re-run of a successful gamma scan.**  A scan that succeeds on *some* padding
succeeds, with the same result, on *any* padding of width at least `2N+1` provided the fuel still
covers the remaining scan.  Both side conditions are **explicit hypotheses** of the statement:

* width `2N+1` is enough because the terminator sits at an index `< N` (blank tail), so its
  `zeros`-bit payload ends before `2N`;
* the fuel bound `N + 1 ≤ fuel' + zeros` is *assumed* here, not proved.  What the induction proves
  is that it is **preserved** by the scan step (`zeros` grows by one as the fuel drops by one) and
  that, together with the blank-tail bound `zeros < N`, it keeps the target fuel positive.  The two
  callers below (`contentHeader?_padWord_of_le`, `contentHeader?_of_decodeGamma`) **discharge** it
  outright, since they enter at `zeros = 0` with fuel `2 * width + 2`. -/
theorem decodeGammaAux?_padWord_canonical {N : Nat} (z : PrefixBitVec N) {offset : Nat} :
    ∀ {T T' fuel fuel' zeros : Nat} {r : Nat × Nat},
      2 * N + 1 ≤ T' → N + 1 ≤ fuel' + zeros →
      decodeGammaAux? (padWord z T) offset fuel zeros = some r →
      decodeGammaAux? (padWord z T') offset fuel' zeros = some r := by
  intro T T' fuel
  induction fuel with
  | zero => intro fuel' zeros r _ _ h; cases h
  | succ f ih =>
      intro fuel' zeros r hT' hfuel h
      have hsupp : offset + zeros < N := decodeGammaAux?_padWord_support z h
      obtain ⟨g, rfl⟩ : ∃ g, fuel' = g + 1 := ⟨fuel' - 1, by omega⟩
      rw [decodeGammaAux?] at h ⊢
      cases hbit : readBit? (padWord z T) (offset + zeros) with
      | none => rw [hbit] at h; cases h
      | some b =>
          rw [hbit] at h
          have hltT : offset + zeros < T := by
            by_contra hcon
            rw [readBit?_padWord_of_ge z (show T ≤ offset + zeros by omega)] at hbit
            cases hbit
          rw [readBit?_padWord_of_lt z hltT] at hbit
          have hbit' : readBit? (padWord z T') (offset + zeros) = some b := by
            rw [readBit?_padWord_of_lt z (show offset + zeros < T' by omega)]
            exact hbit
          rw [hbit']
          cases b with
          | true =>
              cases hpayload : readNatBE (padWord z T) (offset + zeros + 1) zeros with
              | none => rw [hpayload] at h; cases h
              | some payload =>
                  rw [hpayload] at h
                  rw [readNatBE_padWord_transfer z
                    (show offset + zeros + 1 + zeros ≤ T' by omega) hpayload]
                  exact h
          | false =>
              exact ih hT' (by omega) h

/-! ### The content-computed reads are padding-stable -/

/-- Auxiliary: two `Option`s that transfer `some`-values to each other are equal. -/
private theorem option_eq_of_some_transfer {α : Type} {a b : Option α}
    (h₁ : ∀ x, a = some x → b = some x)
    (h₂ : ∀ x, b = some x → a = some x) : a = b := by
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some x => exact absurd (h₂ x rfl) (by simp)
  | some x => exact (h₁ x rfl).symm

/-- **The content header is padding-stable.**  Both margins (`2N+1` for `z`, `2T+1` for the padded
word) are canonical in the sense of `decodeGammaAux?_padWord_canonical`, so the two decodes agree —
including on failure.  This is what removes the residual `N`-dependence flagged in the
`contentHeader?` docstring: the definition still mentions `2 * N + 1`, but its *value* does not. -/
theorem contentHeader?_padWord_of_le {N T : Nat} (z : PrefixBitVec N) (hNT : N ≤ T) :
    contentHeader? (padWord z T) = contentHeader? z := by
  unfold contentHeader?
  rw [padWord_padWord_of_le z hNT]
  unfold decodeGamma?
  refine option_eq_of_some_transfer ?_ ?_
  · intro r hr
    exact decodeGammaAux?_padWord_canonical z (by omega) (by omega) hr
  · intro r hr
    exact decodeGammaAux?_padWord_canonical z (by omega) (by omega) hr

/-- The content-computed parse is padding-stable: the header is, and the query window is a padding
of the *same* word at the *same* content-computed width.  Stability is agreement, *including on
failure* — this does **not** say the strict parser's surviving `m = treeMCSPPrefixM codec n_dec`
gate never rejects. -/
theorem contentInput?_padWord_of_le (codec : TreeCircuitWitnessCodec threshold)
    {N T : Nat} (z : PrefixBitVec N) (hNT : N ≤ T) :
    contentInput? codec (padWord z T) = contentInput? codec z := by
  unfold contentInput?
  simp only [contentHeader?_padWord_of_le z hNT, padWord_padWord_of_le z hNT]

/-- The content witness window is padding-stable. -/
theorem contentWitness_padWord_of_le (codec : TreeCircuitWitnessCodec threshold)
    {N T : Nat} (z : PrefixBitVec N) (hNT : N ≤ T) (n : Nat) :
    contentWitness codec (padWord z T) n = contentWitness codec z n := by
  funext j
  unfold contentWitness
  exact padRead_padWord_of_le z hNT _

/-- **Padding stability of content acceptance (headline).**  Blank-padding a word to any larger
physical length changes nothing: the header, the query window and the witness window are all read at
content-computed offsets, and the padding only adds blanks past the support.  The length-gated
`PrefixExtensionLanguage` does **not** have this property, since its parser rejects every word whose
physical length differs from `treeMCSPPrefixM codec n` — that mismatch is the review of the
definitions recorded in this directory's `README.md`, argued against those definitions and **not**
formalised as a Lean refutation. -/
theorem ContentAccepts_padWord_of_le (codec : TreeCircuitWitnessCodec threshold)
    {N T : Nat} (z : PrefixBitVec N) (hNT : N ≤ T) :
    ContentAccepts codec (padWord z T) ↔ ContentAccepts codec z := by
  unfold ContentAccepts
  simp only [contentInput?_padWord_of_le codec z hNT, contentWitness_padWord_of_le codec z hNT]

/-- **Full padding-invariance of `ContentAccepts`.**  Any two *complete* finite words presenting the
same blank-padded tape are content-accepted alike, so no physical-length information about a complete
word is observable in `ContentAccepts`.  This is one ingredient the *planned idle-sink verifier*
would need on the specification side: the zero-extension pair of complete words that the
length-gated parser separates is not separated by `ContentAccepts`.

Two things it does **not** give.  It does not lift to the language wrapper: membership of a *query*
`y` in `ContentPrefixExtensionLanguage codec m` quantifies over certificates of length
`certificateLength m 1` concatenated at offset `m`, both of which move with `m`, so padding a query
is outside the scope of this lemma and wrapper-level invariance stays unproved.  And it says nothing
about the machine side: no verifier TM is built, the `pnp3` model is **not** length-blind (its tape
length and evaluation step both move with the input length), and the `(★′)` bridge
`TM.accepts … = ContentAccepts …` remains open. -/
theorem ContentAccepts_iff_of_padRead_eq (codec : TreeCircuitWitnessCodec threshold)
    {N N' : Nat} (z : PrefixBitVec N) (z' : PrefixBitVec N')
    (h : ∀ j, padRead z j = padRead z' j) :
    ContentAccepts codec z ↔ ContentAccepts codec z' := by
  rcases Nat.le_total N N' with hle | hle
  · rw [eq_padWord_of_padRead_eq z z' h]
    exact (ContentAccepts_padWord_of_le codec z hle).symm
  · rw [eq_padWord_of_padRead_eq z' z (fun j => (h j).symm)]
    exact ContentAccepts_padWord_of_le codec z' hle

/-! ### Conditional transport (no unconditional existence claim)

Both lemmas below take an already-successful decode / an already-extendable query as a hypothesis and
transport it.  The second one's conclusion is an existential over certificates, but it is available
only under undischarged hypotheses, so neither lemma witnesses — unconditionally — that
`ContentAccepts` is satisfiable. -/

/-- **The `2N+1` margin is harmless.**  Whatever the strict decoder reads off the word itself, the
content header reads too.  (The converse fails on purpose: a terminator inside the support whose
payload runs off the end is decoded by the padded reader — as a blank-reading machine would — and
rejected by the strict one.  That asymmetry is the point of the margin.) -/
theorem contentHeader?_of_decodeGamma {N : Nat} (z : PrefixBitVec N) {r : Nat × Nat}
    (h : decodeGamma? z tagLen = some r) : contentHeader? z = some r := by
  unfold contentHeader?
  unfold decodeGamma? at h ⊢
  rw [← padWord_self z] at h
  exact decodeGammaAux?_padWord_canonical z (by omega) (by omega) h

/-- **Conditional acceptance transport.**  *If* a query at its convention length parses and is
prefix-extendable, *then* some certificate makes the concatenation content-accepted, and — by padding
stability — it stays accepted at every larger physical length.  Both hypotheses of the coincidence
lemma (`hparse` and `hn : input.n = n`) are required, and neither they nor `hext` are discharged
anywhere.  The conclusion *is* an existential over certificates, but only under those hypotheses:
this does **not** show that such a query exists, so it is no unconditional existential /
non-emptiness result for `ContentAccepts` — nor for `L'`, whose membership it does not transport
across physical lengths. -/
theorem ContentAccepts_padWord_of_prefixExtendable
    (codec : TreeCircuitWitnessCodec threshold)
    {n : Nat} (y : PrefixBitVec (treeMCSPPrefixM codec n))
    (input : PrefixInput
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec))
      (treeMCSPPrefixM codec n))
    (hparse : parseTreeMCSPPrefixInput threshold codec y = some input)
    (hn : input.n = n)
    (hext : PrefixExtendable (treeMCSPConcretePrefixParser threshold codec) y)
    {T : Nat}
    (hT : treeMCSPPrefixM codec n
        + Pnp3.ComplexityInterfaces.certificateLength (treeMCSPPrefixM codec n) 1 ≤ T) :
    ∃ cert : Pnp3.ComplexityInterfaces.Bitstring
        (Pnp3.ComplexityInterfaces.certificateLength (treeMCSPPrefixM codec n) 1),
      ContentAccepts codec
        (padWord (Pnp3.ComplexityInterfaces.concatBitstring y cert) T) := by
  have hcontent : ContentPrefixExtendable codec y := by
    rw [← ContentPrefixExtensionLanguage_accepts_iff codec y,
      ContentPrefixExtensionLanguage_eq_of_parse codec y input hparse hn,
      PrefixExtensionLanguage_accepts_iff]
    exact hext
  obtain ⟨cert, hacc⟩ := hcontent
  exact ⟨cert, (ContentAccepts_padWord_of_le codec _ hT).mpr hacc⟩

end ContractExpansion
end Frontier
end Pnp4
