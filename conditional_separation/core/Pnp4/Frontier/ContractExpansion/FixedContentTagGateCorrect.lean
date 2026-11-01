import Complexity.Uniform.V1.FixedContentTagGate
import Pnp4.Frontier.ContractExpansion.BoundedContentSemanticVerifier
import Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionGateClosure
namespace Pnp4.Frontier.ContractExpansion
open AlgorithmsToLowerBounds
open Pnp3.Complexity.Uniform.V1
private theorem fixedTag_constants : treePrefixTag = 178 ∧ tagLen = 8 ∧ ∀ j : Fin tagLen, FixedContentTagGate.expectedTagBit j = natBitBE treePrefixTag tagLen j := by
  refine ⟨rfl, rfl, ?_⟩
  intro j; fin_cases j <;> norm_num [FixedContentTagGate.expectedTagBit, natBitBE, treePrefixTag, tagLen]
theorem fixedTagMatches_iff {N : Nat} (z : PrefixBitVec N) : FixedContentTagGate.tagMatches z = true ↔ ∀ j : Fin tagLen, FixedContentTagGate.physicalSymbol z j.1 = some (natBitBE treePrefixTag tagLen j) := by
  rcases FixedContentTagGate.tag_contract z with ⟨_, _, _, _, _, _, _, _, hexact, _⟩
  constructor
  · intro hm j
    simpa [fixedTag_constants.2.2 j] using hexact.mp hm j
  · intro hall
    apply hexact.mpr
    intro j
    simpa [fixedTag_constants.2.2 j] using hall j
private theorem decodeGammaAux_none_of_no_true {M : Nat} (y : PrefixBitVec M) (offset fuel zeros : Nat) (hzero : ∀ j, offset ≤ j → readBit? y j ≠ some true) : decodeGammaAux? y offset fuel zeros = none := by
  induction fuel generalizing zeros with
  | zero => rfl
  | succ fuel ih =>
      rw [decodeGammaAux?]
      cases hread : readBit? y (offset + zeros) with
      | none => simp
      | some b =>
          cases b
          · simpa using ih (zeros + 1)
          · exact (hzero _ (by omega) hread).elim
private theorem short_header_none {N : Nat} (z : PrefixBitVec N) (hN : N ≤ tagLen) : contentHeader? z = none := by
  unfold contentHeader? decodeGamma?; apply decodeGammaAux_none_of_no_true
  intro j hj
  unfold readBit?
  split
  · rename_i hfit
    have hNj : N ≤ j := by simpa [tagLen] using le_trans hN hj
    simp [padWord, padRead, Nat.not_lt_of_ge hNj]
  · simp
private def sevenPrefix : PrefixBitVec 7 := fun j => FixedContentTagGate.expectedTagBit ⟨j.1, by omega⟩
theorem fixedTag_short_virtual_zero_contract : (∀ {N : Nat} (z : PrefixBitVec N), N ≤ tagLen → contentHeader? z = none) ∧ FixedContentTagGate.tagMatches sevenPrefix = false ∧ readNatBE (padWord sevenPrefix tagLen) 0 tagLen = some treePrefixTag ∧ contentHeader? sevenPrefix = none ∧ VirtualZeroTailReader.contentHeader? sevenPrefix = none := by
  refine ⟨fun z h => short_header_none z h, ?_, ?_, ?_, ?_⟩
  · rw [Bool.eq_false_iff]; intro h
    rcases FixedContentTagGate.tag_contract sevenPrefix with ⟨_, _, _, _, _, _, _, _, hexact, _⟩
    have hp := hexact.mp h ⟨7, by decide⟩
    simp [FixedContentTagGate.physicalSymbol] at hp
  · norm_num [readNatBE, readBit?, padWord, padRead, sevenPrefix, FixedContentTagGate.expectedTagBit, tagLen, treePrefixTag]
  · exact short_header_none sevenPrefix (by norm_num [tagLen])
  · simpa using short_header_none sevenPrefix (by norm_num [tagLen])
private theorem readNatBE_tag {T : Nat} (y : PrefixBitVec T) (hT : tagLen ≤ T) (h : readNatBE y 0 tagLen = some treePrefixTag) : ∀ j : Fin tagLen, y ⟨j.1, lt_of_lt_of_le j.2 hT⟩ = natBitBE treePrefixTag tagLen j := by
  have hs : (0 : Nat) < T ∧ 1 < T ∧ 2 < T ∧ 3 < T ∧ 4 < T ∧ 5 < T ∧ 6 < T ∧ 7 < T := by unfold tagLen at hT; omega
  rcases hs with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  simp [readNatBE, readBit?, h0, h1, h2, h3, h4, h5, h6, h7, treePrefixTag, tagLen] at h
  generalize hb0 : y ⟨0, h0⟩ = b0 at h; generalize hb1 : y ⟨1, h1⟩ = b1 at h
  generalize hb2 : y ⟨2, h2⟩ = b2 at h; generalize hb3 : y ⟨3, h3⟩ = b3 at h
  generalize hb4 : y ⟨4, h4⟩ = b4 at h; generalize hb5 : y ⟨5, h5⟩ = b5 at h
  generalize hb6 : y ⟨6, h6⟩ = b6 at h; generalize hb7 : y ⟨7, h7⟩ = b7 at h
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> norm_num at h
  intro j
  fin_cases j <;> simp_all [natBitBE, treePrefixTag, tagLen]
private theorem tagMatches_of_semantic_true {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {N : Nat} (z : PrefixBitVec N)
    (hsemantic : contentSemanticAccepts codec z = true) : FixedContentTagGate.tagMatches z = true := by
  by_cases hshort : N ≤ tagLen
  · have hnone := short_header_none z hshort
    have hinput : contentInput? codec z = none := by simp [contentInput?, hnone]
    simp [contentSemanticAccepts, hinput] at hsemantic
  · have hN : tagLen ≤ N := by omega
    cases hheader : contentHeader? z with
    | none =>
        have hinput : contentInput? codec z = none := by simp [contentInput?, hheader]
        simp [contentSemanticAccepts, hinput] at hsemantic
    | some nc =>
        rcases nc with ⟨n, consumed⟩
        have hsome : (contentInput? codec z).isSome := by
          cases hi : contentInput? codec z <;> simp [contentSemanticAccepts, hi] at hsemantic ⊢
        have hread := (contentInput?_isSome_iff_of_header codec z hheader).1 hsome |>.1
        have hwidth : tagLen ≤ treeMCSPPrefixM codec n := by unfold treeMCSPPrefixM; omega
        have hbits := readNatBE_tag (padWord z (treeMCSPPrefixM codec n)) hwidth hread
        rcases FixedContentTagGate.tag_contract z with ⟨_, _, _, _, _, _, _, _, hexact, _⟩
        apply hexact.mpr
        intro j
        have hj8 : j.1 < tagLen := by change j.1 < 8; exact j.2
        have hj : j.1 < N := lt_of_lt_of_le hj8 hN
        have hb := hbits ⟨j.1, hj8⟩
        rw [fixedTag_constants.2.2 j]
        simpa [FixedContentTagGate.physicalSymbol, hj, padWord, padRead] using hb
private theorem semantic_factor {threshold : Nat → Nat} (codec : TreeCircuitWitnessCodec threshold) {N : Nat} (z : PrefixBitVec N) : contentSemanticAccepts codec z = (FixedContentTagGate.tagMatches z && contentSemanticAccepts codec z) := by
  cases hs : contentSemanticAccepts codec z with
  | false => simp
  | true => simp [tagMatches_of_semantic_true codec z hs]
theorem fixedTag_semantic_factorization : (∀ {threshold : Nat → Nat} (codec : TreeCircuitWitnessCodec threshold)
      {N : Nat} (z : PrefixBitVec N), contentSemanticAccepts codec z = (FixedContentTagGate.tagMatches z && contentSemanticAccepts codec z)) ∧ (∀ k {N : Nat} (z : PrefixBitVec N), boundedContentSemanticAccepts k z = (FixedContentTagGate.tagMatches z && boundedContentSemanticAccepts k z) ∧ (FixedContentTagGate.tagMatches z = false → boundedContentSemanticAccepts k z = false)) := by
  constructor
  · intro threshold codec N z
    exact semantic_factor codec z
  · intro k N z
    rw [boundedContentSemanticAccepts_eq]
    refine ⟨semantic_factor (boundedContentCodec k) z, fun hbad => ?_⟩
    simpa [hbad] using semantic_factor (boundedContentCodec k) z
theorem fixedTag_machine_handoff {a m B : Nat} (x : PrefixBitVec a) (w : PrefixBitVec m) : let z := Fin.append x w
    ((FixedContentTagGate.machine.run
        (FixedContentTagGate.deadline a m) (FixedContentTagGate.startConfig B x w)).state = FixedContentTagGate.machine.accept ↔
      FixedContentTagGate.tagMatches z = true) ∧ ((FixedContentTagGate.machine.run
        (FixedContentTagGate.deadline a m) (FixedContentTagGate.startConfig B x w)).state = FixedContentTagGate.machine.reject ↔ FixedContentTagGate.tagMatches z = false) := by
  dsimp
  rw [FixedContentTagGate.run_deadline]
  change ((if FixedContentTagGate.tagMatches (Fin.append x w) then
      FixedContentTagGate.machine.accept else FixedContentTagGate.machine.reject) =
      FixedContentTagGate.machine.accept ↔ _) ∧
    ((if FixedContentTagGate.tagMatches (Fin.append x w) then
      FixedContentTagGate.machine.accept else FixedContentTagGate.machine.reject) =
      FixedContentTagGate.machine.reject ↔ _)
  by_cases htag : FixedContentTagGate.tagMatches (Fin.append x w) = true
  · simp [htag, FixedContentTagGate.machine.accept_ne_reject]
  · have hfalse := Bool.eq_false_of_not_eq_true htag
    simp [hfalse, Ne.symm FixedContentTagGate.machine.accept_ne_reject]
end Pnp4.Frontier.ContractExpansion
