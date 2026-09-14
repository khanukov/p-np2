import Complexity.Uniform.V1.FixedContentGammaTerminator
import Pnp4.Frontier.ContractExpansion.FixedContentTagGateCorrect
import Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionPadding

namespace Pnp4.Frontier.ContractExpansion

open AlgorithmsToLowerBounds
open Pnp3.Complexity.Uniform.V1

private theorem readNatBE_exists_of_fit {M : Nat} (y : PrefixBitVec M) :
    ∀ offset width, offset + width ≤ M → ∃ v, readNatBE y offset width = some v := by
  intro offset width
  induction width generalizing offset with
  | zero => intro _; exact ⟨0, rfl⟩
  | succ width ih =>
      intro hfit
      have hbit : offset < M := by omega
      rcases ih (offset + 1) (by omega) with ⟨v, hv⟩
      refine ⟨(if y ⟨offset, hbit⟩ then 1 else 0) * 2 ^ width + v, ?_⟩
      simp [readNatBE, readBit?, hbit, hv]

private theorem decode_of_zero_run {N : Nat} (z : PrefixBitVec N)
    (zeros : Nat) (hterm : FixedContentTagGate.physicalSymbol z (8 + zeros) = some true)
    (hzero : ∀ i, i < zeros →
      FixedContentTagGate.physicalSymbol z (8 + i) = some false) :
    ∃ n consumed, contentHeader? z = some (n, consumed) := by
  have htermN : 8 + zeros < N := by
    unfold FixedContentTagGate.physicalSymbol at hterm
    split at hterm
    · assumption
    · simp at hterm
  let T := 2 * N + 1
  have hfield : 8 + zeros + 1 + zeros ≤ T := by dsimp [T]; omega
  rcases readNatBE_exists_of_fit (padWord z T) (8 + zeros + 1) zeros hfield with
    ⟨payload, hpayload⟩
  have hdecode : ∀ k, k ≤ zeros →
      decodeGammaAux? (padWord z T) 8 (T + 1 - k) k =
        some (2 ^ zeros + payload - 1, 2 * zeros + 1) := by
    intro k hk
    induction hk using Nat.decreasingInduction with
    | self =>
        rw [show T + 1 - zeros = (T - zeros) + 1 by omega, decodeGammaAux?]
        have hr : readBit? (padWord z T) (8 + zeros) = some true := by
          rw [readBit?_padWord_of_lt z (by dsimp [T]; omega)]
          simpa [FixedContentTagGate.physicalSymbol, htermN, padRead] using hterm
        simp [hr, hpayload]
    | of_succ k hkzero ih =>
        rw [show T + 1 - k = (T - k) + 1 by omega, decodeGammaAux?]
        have hklt : k < zeros := by omega
        have hkN : 8 + k < N := by omega
        have hr : readBit? (padWord z T) (8 + k) = some false := by
          rw [readBit?_padWord_of_lt z (by dsimp [T]; omega)]
          simpa [FixedContentTagGate.physicalSymbol, hkN, padRead] using hzero k hklt
        simp only [hr]
        simpa [Nat.add_assoc] using ih
  refine ⟨2 ^ zeros + payload - 1, 2 * zeros + 1, ?_⟩
  simpa [contentHeader?, decodeGamma?, T] using hdecode 0 (Nat.zero_le _)

private theorem decode_success_has_physical_true {N : Nat} (z : PrefixBitVec N)
    {T offset fuel zeros n consumed : Nat}
    (h : decodeGammaAux? (padWord z T) offset fuel zeros = some (n, consumed)) :
    ∃ j, offset + zeros ≤ j ∧ j < N ∧
      FixedContentTagGate.physicalSymbol z j = some true := by
  induction fuel generalizing zeros with
  | zero => simp [decodeGammaAux?] at h
  | succ fuel ih =>
      have horig := h
      rw [decodeGammaAux?] at h
      cases hr : readBit? (padWord z T) (offset + zeros) with
      | none => simp [hr] at h
      | some b =>
        cases b with
        | false =>
          simp [hr] at h
          rcases ih h with ⟨j, hj, hjN, ht⟩
          exact ⟨j, by omega, hjN, ht⟩
        | true =>
          have hsupp : offset + zeros < N :=
            decodeGammaAux?_padWord_support z horig
          refine ⟨offset + zeros, le_rfl, hsupp, ?_⟩
          rw [readBit?_padWord_of_lt z (by
            have : offset + zeros < T := by
              by_contra hn
              rw [readBit?_padWord_of_ge z (by omega)] at hr
              cases hr
            exact this)] at hr
          simpa [FixedContentTagGate.physicalSymbol, hsupp, padRead] using hr

theorem fixedGamma_header_contract {N : Nat} (z : PrefixBitVec N) :
    (FixedContentGammaTerminator.gammaZeros? z).isSome ↔
      (contentHeader? z).isSome := by
  constructor
  · intro hg
    cases h : FixedContentGammaTerminator.gammaZeros? z with
    | none => simp [h] at hg
    | some zeros =>
        rcases (FixedContentGammaTerminator.gamma_contract z).1 zeros h with
          ⟨_, ht, hz⟩
        rcases decode_of_zero_run z zeros ht hz with ⟨n, consumed, hc⟩
        simp [hc]
  · intro hh
    cases hc : contentHeader? z with
    | none => simp [hc] at hh
    | some nc =>
        rcases nc with ⟨n, consumed⟩
        by_cases hN : 8 ≤ N
        · by_cases hg : FixedContentGammaTerminator.gammaZeros? z = none
          · have hz := (FixedContentGammaTerminator.gamma_contract z).2.1 hN hg
            unfold contentHeader? decodeGamma? at hc
            rcases decode_success_has_physical_true z hc with ⟨j, hj8, hjN, ht⟩
            have hindex : 8 + (j - 8) = j := by
              simp [tagLen] at hj8
              omega
            have hzj := hz (j - 8) (by omega)
            rw [hindex] at hzj
            rw [hzj] at ht
            cases ht
          · exact Option.isSome_iff_ne_none.mpr hg
        · have hnone := fixedTag_short_virtual_zero_contract.1 z (by
            simp [tagLen] at hN ⊢; omega)
          rw [hnone] at hc
          cases hc

private theorem semantic_false_of_no_header {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {N : Nat} (z : PrefixBitVec N)
    (h : contentHeader? z = none) : contentSemanticAccepts codec z = false := by
  apply contentSemanticAccepts_eq_false_of_contentInput_none
  simp [contentInput?, h]

private theorem semantic_factor {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {N : Nat} (z : PrefixBitVec N) :
    contentSemanticAccepts codec z =
      ((FixedContentGammaTerminator.gammaZeros? z).isSome &&
        contentSemanticAccepts codec z) := by
  cases hg : FixedContentGammaTerminator.gammaZeros? z with
  | some zeros => simp
  | none =>
    have hh : contentHeader? z = none := by
      cases hc : contentHeader? z with
      | none => rfl
      | some nc =>
        have hs : (FixedContentGammaTerminator.gammaZeros? z).isSome :=
          (fixedGamma_header_contract z).mpr (by simp [hc])
        simp [hg] at hs
    simp [semantic_false_of_no_header codec z hh]

theorem fixedGamma_semantic_factorization :
    (∀ {threshold : Nat → Nat} (codec : TreeCircuitWitnessCodec threshold)
      {N : Nat} (z : PrefixBitVec N),
      contentSemanticAccepts codec z =
        ((FixedContentGammaTerminator.gammaZeros? z).isSome &&
          contentSemanticAccepts codec z)) ∧
    (∀ k {N : Nat} (z : PrefixBitVec N),
      boundedContentSemanticAccepts k z =
        ((FixedContentGammaTerminator.gammaZeros? z).isSome &&
          boundedContentSemanticAccepts k z) ∧
      (FixedContentGammaTerminator.gammaZeros? z = none →
        boundedContentSemanticAccepts k z = false)) := by
  constructor
  · intro threshold codec N z
    exact semantic_factor codec z
  · intro k N z
    rw [boundedContentSemanticAccepts_eq]
    refine ⟨semantic_factor (boundedContentCodec k) z, ?_⟩
    intro hg
    have hf := semantic_factor (boundedContentCodec k) z
    simpa [hg] using hf

theorem fixedGamma_machine_handoff {a m B : Nat}
    (x : PrefixBitVec a) (w : PrefixBitVec m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    let z := Fin.append x w
    let c := FixedContentGammaTerminator.machine.run
      (FixedContentGammaTerminator.deadline a m)
      (FixedContentGammaTerminator.startConfig B x w)
    (c.state = FixedContentGammaTerminator.machine.accept ↔
      (contentHeader? z).isSome) ∧
    (c.state = FixedContentGammaTerminator.machine.reject ↔
      contentHeader? z = none) ∧
    c.tape = FixedPairContentMarkerErase.contentTape B x w := by
  dsimp
  have hrun := FixedContentGammaTerminator.run_deadline (B := B) x w htag
  have htape := (FixedContentGammaTerminator.phase_contract x w htag).2.2.1 B
  refine ⟨?_, ?_, htape⟩
  · rw [hrun]
    cases hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) with
    | some zeros =>
      have hh := (fixedGamma_header_contract (Fin.append x w)).mp (by simp [hg])
      simp [FixedContentGammaTerminator.finalConfig, hg, hh,
        FixedContentGammaTerminator.machine, FixedContentGammaTerminator.qAccept]
    | none =>
      have hh : ¬(contentHeader? (Fin.append x w)).isSome := by
        rw [← fixedGamma_header_contract]
        simp [hg]
      simp [FixedContentGammaTerminator.finalConfig, hg, hh,
        FixedContentGammaTerminator.machine, FixedContentGammaTerminator.qAccept,
        FixedContentGammaTerminator.qReject]
  · rw [hrun]
    cases hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) with
    | some zeros =>
      have hh := (fixedGamma_header_contract (Fin.append x w)).mp (by simp [hg])
      have hn : contentHeader? (Fin.append x w) ≠ none := by
        intro heq; simp [heq] at hh
      simp [FixedContentGammaTerminator.finalConfig, hg, hn,
        FixedContentGammaTerminator.machine,
        FixedContentGammaTerminator.qAccept,
        FixedContentGammaTerminator.qReject]
    | none =>
      have hh : contentHeader? (Fin.append x w) = none := by
        cases hc : contentHeader? (Fin.append x w) with
        | none => rfl
        | some nc =>
          have hs := (fixedGamma_header_contract (Fin.append x w)).mpr (by simp [hc])
          simp [hg] at hs
      simp [FixedContentGammaTerminator.finalConfig, hg, hh,
        FixedContentGammaTerminator.machine,
        FixedContentGammaTerminator.qAccept,
        FixedContentGammaTerminator.qReject]

end Pnp4.Frontier.ContractExpansion
