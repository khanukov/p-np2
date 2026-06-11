import Pnp4.Frontier.ContractExpansion.ContentPrefixExtension
import Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixVerifierLayout
import Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixSemanticVerifier

/-!
# Coincidence of `L'` with the length-gated language on parseable inputs — §13 repair, brick R3

The content-truthful language `L'` (`ContentPrefixExtension.lean`) drops the parser's physical-length
gate.  This module proves the **coincidence lemma**: on every input the strict parser accepts, the two
languages agree —

> `parseTreeMCSPPrefixInput y = some input  →  L' m y = L m y`.

This is the seam through which the existing decision→search extraction transfers to `L'` (brick R4):
the greedy machinery only ever evaluates deciders on *constructed, parseable* queries.

Mechanics: monotonicity of the strict field readers under ambient widening with cell agreement
(`readBit?` / `readNatBE` / `decodeGammaAux?` — the success trace only touches in-range cells), a
full parse inversion (the success cascade pins the internal gamma decode and the length gate), and
the two window computations on a concatenated word (`padWord` of the concat at the gate length *is*
`y`; the content witness window *is* the certificate prefix).

**Progress classification (AGENTS.md): Infrastructure** — specification repair for the NP-verifier
track; proves no separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.
**No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-! ### Reader monotonicity under ambient widening -/

section ReaderMono

variable {m₁ m₂ : Nat} {y₁ : PrefixBitVec m₁} {y₂ : PrefixBitVec m₂} {offset : Nat}

/-- A successful strict bit read survives widening the ambient vector (cells agreeing). -/
theorem readBit?_mono (hle : m₁ ≤ m₂)
    (hag : ∀ (j : Nat) (h : j < m₁), y₂ ⟨j, Nat.lt_of_lt_of_le h hle⟩ = y₁ ⟨j, h⟩)
    {j : Nat} {b : Bool} (h : readBit? y₁ j = some b) :
    readBit? y₂ j = some b := by
  by_cases hj : j < m₁
  · rw [readBit?, dif_pos hj] at h
    rw [readBit?, dif_pos (Nat.lt_of_lt_of_le hj hle), hag j hj]
    exact h
  · rw [readBit?, dif_neg hj] at h
    cases h

/-- A successful strict fixed-width read survives widening the ambient vector. -/
theorem readNatBE_mono (hle : m₁ ≤ m₂)
    (hag : ∀ (j : Nat) (h : j < m₁), y₂ ⟨j, Nat.lt_of_lt_of_le h hle⟩ = y₁ ⟨j, h⟩) :
    ∀ {width offset v : Nat}, readNatBE y₁ offset width = some v →
      readNatBE y₂ offset width = some v := by
  intro width
  induction width with
  | zero => intro offset v h; simpa [readNatBE] using h
  | succ k ih =>
      intro offset v h
      rw [readNatBE] at h ⊢
      cases hb : readBit? y₁ offset with
      | none => rw [hb] at h; cases h
      | some b =>
          rw [hb] at h
          rw [readBit?_mono hle hag hb]
          cases hr : readNatBE y₁ (offset + 1) k with
          | none => rw [hr] at h; cases h
          | some rest =>
              rw [hr] at h
              rw [ih hr]
              exact h

/-- A successful gamma scan survives widening the ambient vector **and** the fuel. -/
theorem decodeGammaAux?_mono (hle : m₁ ≤ m₂)
    (hag : ∀ (j : Nat) (h : j < m₁), y₂ ⟨j, Nat.lt_of_lt_of_le h hle⟩ = y₁ ⟨j, h⟩) :
    ∀ {fuel₁ fuel₂ zeros : Nat} {r : Nat × Nat}, fuel₁ ≤ fuel₂ →
      decodeGammaAux? y₁ offset fuel₁ zeros = some r →
      decodeGammaAux? y₂ offset fuel₂ zeros = some r := by
  intro fuel₁
  induction fuel₁ with
  | zero => intro fuel₂ zeros r _ h; cases h
  | succ f ih =>
      intro fuel₂ zeros r hfuel h
      obtain ⟨f₂, rfl⟩ : ∃ f₂, fuel₂ = f₂ + 1 :=
        ⟨fuel₂ - 1, by omega⟩
      rw [decodeGammaAux?] at h ⊢
      cases hb : readBit? y₁ (offset + zeros) with
      | none => rw [hb] at h; cases h
      | some b =>
          rw [hb] at h
          rw [readBit?_mono hle hag hb]
          cases b with
          | true =>
              cases hp : readNatBE y₁ (offset + zeros + 1) zeros with
              | none => rw [hp] at h; cases h
              | some payload =>
                  rw [hp] at h
                  rw [readNatBE_mono hle hag hp]
                  exact h
          | false =>
              exact ih (by omega) h

end ReaderMono

/-- A successful gamma decode transports to the blank-padded concatenated word (with the `2N+1`
margin used by `contentHeader?`). -/
theorem decodeGamma?_concat_pad {threshold : Nat → Nat}
    (_codec : TreeCircuitWitnessCodec threshold)
    {m : Nat} (y : PrefixBitVec m)
    (w : Pnp3.ComplexityInterfaces.Bitstring (Pnp3.ComplexityInterfaces.certificateLength m 1))
    {r : Nat × Nat} (h : decodeGamma? y tagLen = some r) :
    decodeGamma? (padWord (Pnp3.ComplexityInterfaces.concatBitstring y w)
        (2 * (m + Pnp3.ComplexityInterfaces.certificateLength m 1) + 1)) tagLen = some r := by
  set N := m + Pnp3.ComplexityInterfaces.certificateLength m 1 with hN
  have hle : m ≤ 2 * N + 1 := by omega
  have hag : ∀ (j : Nat) (h : j < m),
      (padWord (Pnp3.ComplexityInterfaces.concatBitstring y w) (2 * N + 1))
          ⟨j, Nat.lt_of_lt_of_le h hle⟩
        = y ⟨j, h⟩ := by
    intro j hj
    have hjN : j < N := by omega
    simp only [padWord_apply, padRead_lt _ hjN]
    exact concatBitstring_left y w ⟨j, hjN⟩ hj
  unfold decodeGamma? at h ⊢
  exact decodeGammaAux?_mono hle hag (by omega) h

/-! ### Parse inversion: the success cascade pins the gamma decode and the length gate -/

/-- **Parse inversion.**  A successful strict parse pins the internal gamma decode to the parsed
target (`decodeGamma? y tagLen = some (input.n, consumed)`) and the ambient length to the
convention (`m = treeMCSPPrefixM codec input.n`). -/
theorem parseTreeMCSPPrefixInput_inversion
    (threshold : Nat → Nat)
    (codec : TreeCircuitWitnessCodec threshold)
    {m : Nat}
    (y : PrefixBitVec m)
    (input : PrefixInput
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec)) m)
    (h : parseTreeMCSPPrefixInput threshold codec y = some input) :
    m = treeMCSPPrefixM codec input.n
      ∧ ∃ consumed, decodeGamma? y tagLen = some (input.n, consumed) := by
  unfold parseTreeMCSPPrefixInput at h
  cases htagRead : readNatBE y 0 tagLen with
  | none => simp [htagRead] at h
  | some tag =>
      simp [htagRead] at h
      by_cases htag : tag = treePrefixTag
      · simp [htag] at h
        cases hgamma : decodeGamma? y tagLen with
        | none => simp [hgamma] at h
        | some decoded =>
            obtain ⟨n', consumed⟩ := decoded
            simp [hgamma] at h
            by_cases hlen : m = treeMCSPPrefixM codec n'
            · simp [hlen] at h
              cases hx : sliceBits? y (tagLen + consumed) (Pnp3.Models.Partial.tableLen n') with
              | none => simp [hx] at h
              | some x =>
                  simp [hx] at h
                  cases hiRead : readNatBE y (tagLen + consumed + Pnp3.Models.Partial.tableLen n')
                      (idxWidth codec.witnessBits n') with
                  | none => simp [hiRead] at h
                  | some i =>
                      simp [hiRead] at h
                      by_cases hi : i ≤ codec.witnessBits n'
                      · simp [hi] at h
                        cases hp : sliceBits? y
                            (tagLen + consumed + Pnp3.Models.Partial.tableLen n' +
                              idxWidth codec.witnessBits n') i with
                        | none => simp [hp] at h
                        | some p =>
                            simp [hp] at h
                            cases hpad : sliceBits? y
                                (tagLen + consumed + Pnp3.Models.Partial.tableLen n' +
                                  idxWidth codec.witnessBits n' + i)
                                (codec.witnessBits n' - i) with
                            | none => simp [hpad] at h
                            | some pad =>
                                simp [hpad] at h
                                cases hzero : allZeroSlice? y
                                    (tagLen + consumed + Pnp3.Models.Partial.tableLen n' +
                                      idxWidth codec.witnessBits n' + i)
                                    (codec.witnessBits n' - i) with
                                | none => simp [hzero] at h
                                | some padZero =>
                                    simp [hzero] at h
                                    by_cases hz : padZero = true
                                    · simp [hz] at h
                                      cases h
                                      exact ⟨hlen, consumed, by simp⟩
                                    · simp [hz] at h
                      · simp [hi] at h
            · simp [hlen] at h
      · simp [htag] at h

/-! ### Window computations on a concatenated word -/

/-- The padded window of the concatenation at the query's own length is the query. -/
theorem padWord_concat_left {m : Nat} (y : PrefixBitVec m)
    (w : Pnp3.ComplexityInterfaces.Bitstring (Pnp3.ComplexityInterfaces.certificateLength m 1)) :
    padWord (Pnp3.ComplexityInterfaces.concatBitstring y w) m = y := by
  funext j
  have hjN : j.1 < m + Pnp3.ComplexityInterfaces.certificateLength m 1 := by
    have := j.2; omega
  simp only [padWord_apply, padRead_lt _ hjN]
  exact concatBitstring_left y w ⟨j.1, hjN⟩ j.2

/-- The content witness window of the concatenation (at the gate length) is the certificate's
leading `witnessBits` block. -/
theorem contentWitness_concat {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    {m : Nat} (y : PrefixBitVec m)
    (w : Pnp3.ComplexityInterfaces.Bitstring (Pnp3.ComplexityInterfaces.certificateLength m 1))
    {n : Nat} (hgate : m = treeMCSPPrefixM codec n) (j : Fin (codec.witnessBits n)) :
    contentWitness codec (Pnp3.ComplexityInterfaces.concatBitstring y w) n j
      = w ⟨j.1, by
          have hwb := witnessBits_le_certificateLength codec n m hgate
          omega⟩ := by
  have hwb : codec.witnessBits n ≤ Pnp3.ComplexityInterfaces.certificateLength m 1 :=
    witnessBits_le_certificateLength codec n m hgate
  have hjN : treeMCSPPrefixM codec n + j.1
      < m + Pnp3.ComplexityInterfaces.certificateLength m 1 := by
    have := j.2; omega
  unfold contentWitness
  simp only [padRead_lt _ hjN]
  have := concatBitstring_right y w ⟨treeMCSPPrefixM codec n + j.1, hjN⟩
    (by simp only [hgate]; omega)
  rw [this]
  congr 1
  apply Fin.ext
  simp only [hgate]
  omega

/-- The content-computed parse of a concatenation whose query parses (at the query's own
convention length): the same parsed input, under the content header. -/
theorem contentInput?_concat_of_parse {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    {n : Nat} (y : PrefixBitVec (treeMCSPPrefixM codec n))
    (input : PrefixInput
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec))
      (treeMCSPPrefixM codec n))
    (hparse : parseTreeMCSPPrefixInput threshold codec y = some input)
    (hn : input.n = n)
    (w : Pnp3.ComplexityInterfaces.Bitstring
      (Pnp3.ComplexityInterfaces.certificateLength (treeMCSPPrefixM codec n) 1)) :
    contentInput? codec (Pnp3.ComplexityInterfaces.concatBitstring y w) = some ⟨n, input⟩ := by
  obtain ⟨_, consumed, hgamma⟩ :=
    parseTreeMCSPPrefixInput_inversion threshold codec y input hparse
  rw [hn] at hgamma
  have hheader : contentHeader? (Pnp3.ComplexityInterfaces.concatBitstring y w)
      = some (n, consumed) := by
    unfold contentHeader?
    exact decodeGamma?_concat_pad codec y w hgamma
  unfold contentInput?
  rw [hheader]
  simp only [padWord_concat_left, hparse, Option.map_some]

/-! ### The coincidence theorem -/

/-- **Coincidence (brick R3).**  On a parseable query at its convention length, the
content-truthful language `L'` agrees with the length-gated language. -/
theorem ContentPrefixExtensionLanguage_eq_of_parse {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    {n : Nat} (y : PrefixBitVec (treeMCSPPrefixM codec n))
    (input : PrefixInput
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec))
      (treeMCSPPrefixM codec n))
    (hparse : parseTreeMCSPPrefixInput threshold codec y = some input)
    (hn : input.n = n) :
    ContentPrefixExtensionLanguage codec (treeMCSPPrefixM codec n) y
      = PrefixExtensionLanguage (treeMCSPConcretePrefixParser threshold codec)
          (treeMCSPPrefixM codec n) y := by
  have hwb : codec.witnessBits input.n
      ≤ Pnp3.ComplexityInterfaces.certificateLength (treeMCSPPrefixM codec n) 1 :=
    witnessBits_le_certificateLength codec input.n _ (by rw [hn])
  have hiff : ContentPrefixExtendable codec y
      ↔ PrefixExtendable (treeMCSPConcretePrefixParser threshold codec) y := by
    constructor
    · rintro ⟨w, pr, hci, hagree, hrel⟩
      rw [contentInput?_concat_of_parse codec y input hparse hn w] at hci
      obtain rfl : (⟨n, input⟩ : Σ n', PrefixInput
          (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec))
          (treeMCSPPrefixM codec n')) = pr := Option.some.inj hci
      exact ⟨input, hparse,
        ⟨contentWitness codec (Pnp3.ComplexityInterfaces.concatBitstring y w) input.n,
          hagree, hrel⟩⟩
    · rintro ⟨input', hparse', wfull, hagree, hrel⟩
      obtain rfl : input' = input := Option.some.inj (hparse'.symm.trans hparse)
      set wcert : Pnp3.ComplexityInterfaces.Bitstring
          (Pnp3.ComplexityInterfaces.certificateLength (treeMCSPPrefixM codec n) 1) :=
        fun j => if h : j.1 < codec.witnessBits input'.n then wfull ⟨j.1, h⟩ else false
        with hwcert
      have hcw : contentWitness codec
          (Pnp3.ComplexityInterfaces.concatBitstring y wcert) input'.n = wfull := by
        funext j
        rw [contentWitness_concat codec y wcert (by rw [hn]), hwcert]
        simp only [dif_pos (show (j : Nat) < codec.witnessBits input'.n from j.2)]
        exact congrArg wfull (Fin.ext rfl)
      refine ⟨wcert, ⟨n, input'⟩,
        contentInput?_concat_of_parse codec y input' hparse hn wcert, ?_, ?_⟩
      · show input'.prefixAgrees
          (contentWitness codec (Pnp3.ComplexityInterfaces.concatBitstring y wcert) input'.n)
        rw [hcw]
        exact hagree
      · show (treeMCSPSearchProblem threshold
            (TreeMCSPSearchWitnessEncoding.ofCodec codec)).relation input'.n input'.x
          (contentWitness codec (Pnp3.ComplexityInterfaces.concatBitstring y wcert) input'.n)
        rw [hcw]
        exact hrel
  rw [Bool.eq_iff_iff, ContentPrefixExtensionLanguage_accepts_iff,
    PrefixExtensionLanguage_accepts_iff]
  exact hiff

end ContractExpansion
end Frontier
end Pnp4
