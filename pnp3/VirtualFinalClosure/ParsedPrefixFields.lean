import VirtualFinalClosure.GuardMeaning
namespace VirtualFinalClosure.ParsedPrefixFields
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion Pnp4.AlgorithmsToLowerBounds
set_option autoImplicit false
/-- Authoritative strict-parser inversion retaining the previously unexported
active-prefix slice. The unchanged immutable x-slice proof supplies the same
success cascade; this new conclusion also exposes the actual BE index and pad. -/
private theorem parsed_prefix_fields
    {threshold : Nat → Nat} (codec : TreeCircuitWitnessCodec threshold) {m : Nat}
    (y : PrefixBitVec m)
    (input : PrefixInput
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec)) m)
    (h : parseTreeMCSPPrefixInput threshold codec y = some input) :
    ∃ consumed : Nat,
      decodeGamma? y tagLen=some (input.n,consumed) ∧
      readNatBE y (tagLen+consumed+Pnp3.Models.Partial.tableLen input.n)
        (idxWidth codec.witnessBits input.n)=some input.i ∧
      sliceBits? y (tagLen+consumed+Pnp3.Models.Partial.tableLen input.n+
        idxWidth codec.witnessBits input.n) input.i=some input.p ∧
      allZeroSlice? y (tagLen+consumed+Pnp3.Models.Partial.tableLen input.n+
        idxWidth codec.witnessBits input.n+input.i) (codec.witnessBits input.n-input.i)=some true := by
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
                                      exact ⟨consumed, by simp, by simpa using hiRead, by simpa using hp, by simpa [hz] using hzero⟩
                                    · simp [hz] at h
                      · simp [hi] at h
            · simp [hlen] at h
      · simp [htag] at h

#print axioms parsed_prefix_fields
end VirtualFinalClosure.ParsedPrefixFields
