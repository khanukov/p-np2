import Complexity.Uniform.V1.FixedGammaPayloadPendingCleanup
import Pnp4.Frontier.ContractExpansion.ContentFixedGammaPayloadZeroSemanticBridge

/-!
# Cleaned pending gamma-payload semantics

This infrastructure bridge records strict-reader consequences parallel to the
cleaned physical-true and first-virtual cleanup endpoints.  The payload window
is exactly `[9 + zeros, 9 + 2 * zeros)`.  No endpoint is interpreted as a
verdict and no parser, dispatcher, decoder, or cross-machine claim is made.
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds
open Pnp3.Complexity.Uniform.V1
open Pnp3.Complexity.Uniform.V1.PairEncoding

namespace VirtualZeroTailReader

/-- A positive-width strict scan fails exactly when its whole logical window
does not fit. -/
theorem allZeroSlice?_eq_none_iff
    {N T offset width : Nat} (z : PrefixBitVec N) (hwidth : 0 < width) :
    allZeroSlice? z T offset width = none ↔ T < offset + width := by
  induction width generalizing offset with
  | zero => omega
  | succ k ih =>
      rw [allZeroSlice?]
      by_cases hoffset : offset < T
      · rw [show readBit? z T offset = some (padRead z offset) by
          simp [readBit?, hoffset]]
        cases hrest : allZeroSlice? z T (offset + 1) k with
        | none =>
            simp
            cases k with
            | zero => simp [allZeroSlice?] at hrest
            | succ k =>
                have := (ih (offset := offset + 1) (by omega)).1 hrest
                omega
        | some rest =>
            simp
            by_contra hlt
            cases k with
            | zero => omega
            | succ k =>
                have hn := (ih (offset := offset + 1) (by omega)).2 (by omega)
                rw [hrest] at hn
                contradiction
      · simp [readBit?, hoffset]
        omega

/-- When the whole strict window fits, `some false` means that at least one
blank-padded read in that window is true. -/
theorem allZeroSlice?_eq_some_false_iff
    {N T offset width : Nat} (z : PrefixBitVec N)
    (hfit : offset + width ≤ T) :
    allZeroSlice? z T offset width = some false ↔
      ∃ t, t < width ∧ padRead z (offset + t) = true := by
  have htotal : ∃ b, allZeroSlice? z T offset width = some b := by
    cases hscan : allZeroSlice? z T offset width with
    | none =>
        exfalso
        by_cases hw : width = 0
        · subst width
          simp [allZeroSlice?] at hscan
        · have hfail := (allZeroSlice?_eq_none_iff z (Nat.pos_of_ne_zero hw)).1 hscan
          omega
    | some b => exact ⟨b, rfl⟩
  constructor
  · intro hfalse
    by_cases hexists : ∃ t : Fin width, padRead z (offset + t.val) = true
    · obtain ⟨t, ht⟩ := hexists
      exact ⟨t.val, t.isLt, ht⟩
    · have hall : ∀ t, t < width → padRead z (offset + t) = false := by
        intro t ht
        cases hread : padRead z (offset + t) with
        | false => rfl
        | true => exact False.elim (hexists ⟨⟨t, ht⟩, hread⟩)
      have htrue := (allZeroSlice?_eq_some_true_iff z hfit).2 hall
      rw [hfalse] at htrue
      contradiction
  · rintro ⟨t, ht, hread⟩
    obtain ⟨b, hb⟩ := htotal
    cases b with
    | false => exact hb
    | true =>
        have hall := (allZeroSlice?_eq_some_true_iff z hfit).1 hb
        rw [hall t ht] at hread
        contradiction

end VirtualZeroTailReader

/-- The physical-true cleanup endpoint and a logically fitting strict scan are
parallel one-way consequences. -/
theorem true_cleanup_endpoint_and_allZeroSlice
    {a m B zeros k T : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (htrue : FixedContentTagGate.physicalSymbol (Fin.append x w)
      (9 + zeros + k) = some true)
    (hfit : 9 + 2 * zeros ≤ T) :
    let d := FixedGammaPayloadPendingCleanup.machine.run
      (FixedGammaPayloadPendingCleanup.cleanupClock zeros k)
      (FixedGammaPayloadPendingCleanup.startConfig B x w zeros k)
    d.state = FixedGammaPayloadPendingCleanup.qOne ∧ d.head.val = 6 ∧
    d.tape = FixedPairContentMarkerErase.contentTape B x w ∧
    VirtualZeroTailReader.allZeroSlice?
      (Fin.append x w) T (9 + zeros) zeros = some false := by
  have hend := FixedGammaPayloadPendingCleanup.true_cleanup_endpoint
    (B := B) x w htag hg hk hkz hprefix htrue
  have hsemantic : VirtualZeroTailReader.allZeroSlice?
      (Fin.append x w) T (9 + zeros) zeros = some false := by
    rw [VirtualZeroTailReader.allZeroSlice?_eq_some_false_iff _ (by omega)]
    refine ⟨k, hkz, ?_⟩
    have hp : 9 + zeros + k < a + m := by
      unfold FixedContentTagGate.physicalSymbol at htrue
      split at htrue
      · assumption
      · contradiction
    simpa [FixedContentTagGate.physicalSymbol, padRead, hp] using htrue
  exact ⟨hend.1, hend.2.1, hend.2.2, hsemantic⟩

/-- The first-virtual cleanup endpoint and an all-false logically fitting scan
are parallel one-way consequences. -/
theorem virtual_cleanup_endpoint_and_allZeroSlice
    {a m B zeros k T : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (hvirtual : 9 + zeros + k = a + m)
    (hfit : 9 + 2 * zeros ≤ T) :
    let d := FixedGammaPayloadPendingCleanup.machine.run
      (FixedGammaPayloadPendingCleanup.cleanupClock zeros k)
      (FixedGammaPayloadPendingCleanup.startConfig B x w zeros k)
    d.state = FixedGammaPayloadPendingCleanup.qVirtual ∧ d.head.val = 6 ∧
    d.tape = FixedPairContentMarkerErase.contentTape B x w ∧
    VirtualZeroTailReader.allZeroSlice?
      (Fin.append x w) T (9 + zeros) zeros = some true := by
  have hend := FixedGammaPayloadPendingCleanup.virtual_cleanup_endpoint
    (B := B) x w htag hg hk hkz hprefix hvirtual
  have hsemantic : VirtualZeroTailReader.allZeroSlice?
      (Fin.append x w) T (9 + zeros) zeros = some true := by
    rw [VirtualZeroTailReader.allZeroSlice?_eq_some_true_iff _ (by omega)]
    intro t ht
    by_cases htk : t < k
    · have hp := hprefix (9 + zeros + t) (by omega) (by omega)
      have hj : 9 + zeros + t < a + m := by omega
      simpa [FixedContentTagGate.physicalSymbol, padRead, hj] using hp
    · have hj : ¬ 9 + zeros + t < a + m := by omega
      simp [padRead, hj]
  exact ⟨hend.1, hend.2.1, hend.2.2, hsemantic⟩

/-- At the physical boundary the first-virtual branch makes the positive-width
strict scan fail, even though every available or virtual payload bit is false. -/
theorem virtual_allZeroSlice_at_physical_length
    {a m zeros k : Nat} (x : Bitstring a) (w : Bitstring m)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hvirtual : 9 + zeros + k = a + m) :
    VirtualZeroTailReader.allZeroSlice? (Fin.append x w) (a + m)
      (9 + zeros) zeros = none := by
  rw [VirtualZeroTailReader.allZeroSlice?_eq_none_iff _ (by omega)]
  omega

/-- Physical-true specialization to the frozen shared logical window. -/
theorem true_cleanup_endpoint_and_allZeroSlice_shared_window
    {a m B zeros k : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (htrue : FixedContentTagGate.physicalSymbol (Fin.append x w)
      (9 + zeros + k) = some true) :
    let d := FixedGammaPayloadPendingCleanup.machine.run
      (FixedGammaPayloadPendingCleanup.cleanupClock zeros k)
      (FixedGammaPayloadPendingCleanup.startConfig B x w zeros k)
    d.state = FixedGammaPayloadPendingCleanup.qOne ∧ d.head.val = 6 ∧
    d.tape = FixedPairContentMarkerErase.contentTape B x w ∧
    VirtualZeroTailReader.allZeroSlice? (Fin.append x w)
      (2 * (a + m) + 1) (9 + zeros) zeros = some false :=
  true_cleanup_endpoint_and_allZeroSlice (B := B) (T := 2 * (a + m) + 1)
      x w htag hg hk hkz hprefix htrue
      (by
        have hgamma := (FixedContentGammaTerminator.gamma_contract
          (Fin.append x w)).1 zeros hg
        omega)

/-- First-virtual specialization to the frozen shared logical window. -/
theorem virtual_cleanup_endpoint_and_allZeroSlice_shared_window
    {a m B zeros k : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (hvirtual : 9 + zeros + k = a + m) :
    let d := FixedGammaPayloadPendingCleanup.machine.run
      (FixedGammaPayloadPendingCleanup.cleanupClock zeros k)
      (FixedGammaPayloadPendingCleanup.startConfig B x w zeros k)
    d.state = FixedGammaPayloadPendingCleanup.qVirtual ∧ d.head.val = 6 ∧
    d.tape = FixedPairContentMarkerErase.contentTape B x w ∧
    VirtualZeroTailReader.allZeroSlice? (Fin.append x w)
      (2 * (a + m) + 1) (9 + zeros) zeros = some true :=
  virtual_cleanup_endpoint_and_allZeroSlice (B := B) (T := 2 * (a + m) + 1)
      x w htag hg hk hkz hprefix hvirtual
      (by
        have hgamma := (FixedContentGammaTerminator.gamma_contract
          (Fin.append x w)).1 zeros hg
        omega)

/-- The zero-cleanup branch at the same frozen shared logical window. -/
theorem cleanup_endpoint_and_allZeroSlice_shared_window
    {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + 2 * zeros →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false) :
    let d := FixedGammaPayloadZeroCleanup.machine.run
      (FixedGammaPayloadZeroCleanup.cleanupClock zeros)
      (FixedGammaPayloadZeroCleanup.startConfig B x w zeros)
    d.state = FixedGammaPayloadZeroCleanup.qDone ∧ d.head.val = 6 ∧
    d.tape = FixedPairContentMarkerErase.contentTape B x w ∧
    VirtualZeroTailReader.allZeroSlice? (Fin.append x w)
      (2 * (a + m) + 1) (9 + zeros) zeros = some true := by
  have hend := FixedGammaPayloadZeroCleanup.cleanup_endpoint
    (B := B) x w htag hg hzero hprefix
  have hp := hprefix (8 + 2 * zeros) (by omega) (by omega)
  have hphysicalFit : 9 + 2 * zeros ≤ a + m := by
    unfold FixedContentTagGate.physicalSymbol at hp
    split at hp
    · omega
    · contradiction
  have hgamma := (FixedContentGammaTerminator.gamma_contract
    (Fin.append x w)).1 zeros hg
  have hsemantic := (full_false_gamma_payload_iff_allZeroSlice
    (T := 2 * (a + m) + 1) (Fin.append x w) hphysicalFit (by omega)).1 hprefix
  exact ⟨hend.1, hend.2.1, hend.2.2, hsemantic⟩

end ContractExpansion
end Frontier
end Pnp4
