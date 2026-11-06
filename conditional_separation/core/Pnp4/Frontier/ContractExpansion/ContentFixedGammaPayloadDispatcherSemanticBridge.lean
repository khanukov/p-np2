import Complexity.Uniform.V1.FixedGammaPayloadDispatcherDeadline
import Pnp4.Frontier.ContractExpansion.ContentFixedGammaPayloadPendingSemanticBridge
import Pnp4.Frontier.ContractExpansion.FixedContentGammaTerminatorCorrect

/-!
# Total dispatcher endpoint semantics at the shared reader window

This infrastructure bridge identifies the three fixed dispatcher endpoints on
matching tags with strict-reader facts about the exact gamma payload window.
It includes the zero-width payload, whose empty all-zero scan is `some true`.

The results do not identify a decoded header value or a payload `readNatBE`, do
not interpret an endpoint as acceptance, and make no parser-correctness,
untagged-input, uniform-head, or cross-machine-clock claim.
-/

namespace Pnp4.Frontier.ContractExpansion

open AlgorithmsToLowerBounds
open Pnp3.Complexity.Uniform.V1

/-- A physical true is exactly a true blank-padded source read.  This also
covers out-of-range positions constructively: both sides are false there. -/
theorem physicalSymbol_true_iff_padRead_true {N j : Nat}
    (z : PrefixBitVec N) :
    FixedContentTagGate.physicalSymbol z j = some true ↔ padRead z j = true := by
  by_cases hj : j < N
  · simp [FixedContentTagGate.physicalSymbol, padRead, hj]
  · simp [FixedContentTagGate.physicalSymbol, padRead, hj]

/-- Gamma termination leaves enough room in the shared logical length for the
whole exact payload window, including width zero. -/
theorem gamma_payload_shared_window_fit {N zeros : Nat}
    (z : PrefixBitVec N)
    (hg : FixedContentGammaTerminator.gammaZeros? z = some zeros) :
    9 + zeros + zeros ≤ 2 * N + 1 := by
  have hgamma := (FixedContentGammaTerminator.gamma_contract z).1 zeros hg
  omega

/-- At the dispatcher deadline, `qAllZero` is exactly a successfully decoded
gamma width whose exact payload window is all zero at the shared length. -/
theorem dispatcher_qAllZero_iff_allZeroSlice_shared_window
    {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    let d := FixedGammaPayloadDispatcher.machine.run
      (FixedGammaPayloadDispatcherDeadline.deadline (a + m))
      (FixedGammaPayloadDispatcher.startConfig B x w)
    d.state = FixedGammaPayloadDispatcher.qAllZero ↔
      ∃ zeros,
        FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros ∧
        VirtualZeroTailReader.allZeroSlice? (Fin.append x w)
          (2 * (a + m) + 1) (9 + zeros) zeros = some true := by
  dsimp
  constructor
  · intro hstate
    cases hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) with
    | none =>
        have hrejected :=
          (FixedGammaPayloadDispatcherDeadline.qReject_iff (B := B) x w htag).2 hg
        exact False.elim ((show FixedGammaPayloadDispatcher.qAllZero ≠
          FixedGammaPayloadDispatcher.qReject by decide) (hstate.symm.trans hrejected))
    | some zeros =>
        refine ⟨zeros, rfl, ?_⟩
        rw [VirtualZeroTailReader.allZeroSlice?_eq_some_true_iff _
          (gamma_payload_shared_window_fit (Fin.append x w) hg)]
        have hnone :=
          (FixedGammaPayloadDispatcherDeadline.qAllZero_iff
            (B := B) x w htag hg).1 hstate
        intro t ht
        cases hp : padRead (Fin.append x w) (9 + zeros + t) with
        | false => rfl
        | true =>
            exact False.elim (hnone ⟨t, ht,
              (physicalSymbol_true_iff_padRead_true _).2 hp⟩)
  · rintro ⟨zeros, hg, hscan⟩
    apply (FixedGammaPayloadDispatcherDeadline.qAllZero_iff
      (B := B) x w htag hg).2
    intro hex
    obtain ⟨k, hk, hphysical⟩ := hex
    have hall := (VirtualZeroTailReader.allZeroSlice?_eq_some_true_iff _
      (gamma_payload_shared_window_fit (Fin.append x w) hg)).1 hscan
    have hpad := (physicalSymbol_true_iff_padRead_true _).1 hphysical
    rw [hall k hk] at hpad
    contradiction

/-- At the dispatcher deadline, `qHasOne` is exactly a successfully decoded
gamma width whose exact payload window contains a one at the shared length. -/
theorem dispatcher_qHasOne_iff_allZeroSlice_shared_window
    {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    let d := FixedGammaPayloadDispatcher.machine.run
      (FixedGammaPayloadDispatcherDeadline.deadline (a + m))
      (FixedGammaPayloadDispatcher.startConfig B x w)
    d.state = FixedGammaPayloadDispatcher.qHasOne ↔
      ∃ zeros,
        FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros ∧
        VirtualZeroTailReader.allZeroSlice? (Fin.append x w)
          (2 * (a + m) + 1) (9 + zeros) zeros = some false := by
  dsimp
  constructor
  · intro hstate
    cases hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) with
    | none =>
        have hrejected :=
          (FixedGammaPayloadDispatcherDeadline.qReject_iff (B := B) x w htag).2 hg
        exact False.elim ((show FixedGammaPayloadDispatcher.qHasOne ≠
          FixedGammaPayloadDispatcher.qReject by decide) (hstate.symm.trans hrejected))
    | some zeros =>
        refine ⟨zeros, rfl, ?_⟩
        rw [VirtualZeroTailReader.allZeroSlice?_eq_some_false_iff _
          (gamma_payload_shared_window_fit (Fin.append x w) hg)]
        obtain ⟨k, hk, hphysical⟩ :=
          (FixedGammaPayloadDispatcherDeadline.qHasOne_iff
            (B := B) x w htag hg).1 hstate
        exact ⟨k, hk, (physicalSymbol_true_iff_padRead_true _).1 hphysical⟩
  · rintro ⟨zeros, hg, hscan⟩
    apply (FixedGammaPayloadDispatcherDeadline.qHasOne_iff
      (B := B) x w htag hg).2
    obtain ⟨k, hk, hpad⟩ :=
      (VirtualZeroTailReader.allZeroSlice?_eq_some_false_iff _
        (gamma_payload_shared_window_fit (Fin.append x w) hg)).1 hscan
    exact ⟨k, hk, (physicalSymbol_true_iff_padRead_true _).2 hpad⟩

/-- The malformed dispatcher endpoint is exactly gamma-decoder failure. -/
theorem dispatcher_qReject_iff_gamma_none
    {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    let d := FixedGammaPayloadDispatcher.machine.run
      (FixedGammaPayloadDispatcherDeadline.deadline (a + m))
      (FixedGammaPayloadDispatcher.startConfig B x w)
    d.state = FixedGammaPayloadDispatcher.qReject ↔
      FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none := by
  dsimp
  exact FixedGammaPayloadDispatcherDeadline.qReject_iff (B := B) x w htag

/-- Gamma failure and content-header failure coincide as presence facts; no
claim is made about any decoded header value. -/
theorem dispatcher_qReject_iff_gamma_none_and_contentHeader_none
    {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    let d := FixedGammaPayloadDispatcher.machine.run
      (FixedGammaPayloadDispatcherDeadline.deadline (a + m))
      (FixedGammaPayloadDispatcher.startConfig B x w)
    d.state = FixedGammaPayloadDispatcher.qReject ↔
      FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none ∧
        contentHeader? (Fin.append x w) = none := by
  dsimp
  have hreject := dispatcher_qReject_iff_gamma_none (B := B) x w htag
  constructor
  · intro hstate
    have hg := hreject.mp hstate
    refine ⟨hg, ?_⟩
    cases hh : contentHeader? (Fin.append x w) with
    | none => rfl
    | some value =>
        have hisSome : (FixedContentGammaTerminator.gammaZeros?
            (Fin.append x w)).isSome :=
          (fixedGamma_header_contract (Fin.append x w)).mpr (by simp [hh])
        simp [hg] at hisSome
  · intro h
    exact hreject.mpr h.1

end Pnp4.Frontier.ContractExpansion
