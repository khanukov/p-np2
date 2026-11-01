import Complexity.Uniform.V1.FixedGammaPayloadZeroCleanup
import Pnp4.Frontier.ContractExpansion.ContentVirtualZeroTailReaderCore

/-!
# Fixed gamma-payload zero semantic bridge

This infrastructure module connects the physical all-false gamma-payload
hypothesis used by the fixed cleanup trace to the strict virtual-zero-tail
reader.  The payload window is exactly
`[9 + zeros, 9 + 2 * zeros)`.  The cleanup endpoint and the semantic fact are
parallel consequences of the same hypotheses; no machine-verdict or parser
correctness equivalence is asserted.
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds
open Pnp3.Complexity.Uniform.V1
open Pnp3.Complexity.Uniform.V1.PairEncoding

namespace VirtualZeroTailReader

private theorem allZeroSlice?_exists_of_fit
    {N T offset width : Nat}
    (z : PrefixBitVec N)
    (hfit : offset + width ≤ T) :
    ∃ b, VirtualZeroTailReader.allZeroSlice? z T offset width = some b := by
  induction width generalizing offset with
  | zero => exact ⟨true, rfl⟩
  | succ k ih =>
      have hoffset : offset < T := by omega
      obtain ⟨rest, hrest⟩ := ih (offset := offset + 1) (by omega)
      refine ⟨(!padRead z offset) && rest, ?_⟩
      rw [VirtualZeroTailReader.allZeroSlice?]
      rw [show VirtualZeroTailReader.readBit? z T offset = some (padRead z offset) by
        simp [VirtualZeroTailReader.readBit?, hoffset]]
      rw [hrest]
      rfl

/-- Under exact logical fit, a successful all-zero scan is equivalent to every
blank-padded read in the scanned window being false. -/
theorem allZeroSlice?_eq_some_true_iff
    {N T offset width : Nat}
    (z : PrefixBitVec N)
    (hfit : offset + width ≤ T) :
    VirtualZeroTailReader.allZeroSlice? z T offset width = some true ↔
      ∀ t, t < width → padRead z (offset + t) = false := by
  induction width generalizing offset with
  | zero => simp [VirtualZeroTailReader.allZeroSlice?]
  | succ k ih =>
      have hoffset : offset < T := by omega
      rw [VirtualZeroTailReader.allZeroSlice?]
      rw [show VirtualZeroTailReader.readBit? z T offset = some (padRead z offset) by
        simp [VirtualZeroTailReader.readBit?, hoffset]]
      obtain ⟨rest, hrest⟩ := allZeroSlice?_exists_of_fit (T := T) z
        (offset := offset + 1) (width := k) (by omega)
      rw [hrest]
      constructor
      · intro h t ht
        by_cases ht0 : t = 0
        · subst t
          cases hbit : padRead z offset <;> simp [hbit] at h
          exact hbit
        · have hhead : padRead z offset = false := by
            cases hbit : padRead z offset <;> simp [hbit] at h ⊢
          have hrestTrue : rest = true := by simpa [hhead] using h
          have htail : ∀ u, u < k → padRead z (offset + 1 + u) = false := by
            apply (ih (offset := offset + 1) (by omega)).1
            exact hrest.trans (congrArg some hrestTrue)
          obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            htail u (by omega)
      · intro h
        have hhead : padRead z offset = false := by simpa using h 0 (by omega)
        have htail : ∀ u, u < k → padRead z (offset + 1 + u) = false := by
          intro u hu
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            h (u + 1) (by omega)
        have hrestTrue : rest = true := by
          have := (ih (offset := offset + 1) (by omega)).2 htail
          exact Option.some.inj (hrest.symm.trans this)
        simp [hhead, hrestTrue]

end VirtualZeroTailReader

/-- With both physical and logical fit explicit, a physically present,
all-false gamma payload is exactly a successful semantic all-zero scan. -/
theorem full_false_gamma_payload_iff_allZeroSlice
    {L T zeros : Nat}
    (z : Fin L → Bool)
    (hphysicalFit : 9 + 2 * zeros ≤ L)
    (hlogicalFit : 9 + 2 * zeros ≤ T) :
    (∀ j, 9 + zeros ≤ j → j < 9 + 2 * zeros →
      FixedContentTagGate.physicalSymbol z j = some false) ↔
    VirtualZeroTailReader.allZeroSlice?
      z T (9 + zeros) zeros = some true := by
  rw [VirtualZeroTailReader.allZeroSlice?_eq_some_true_iff z (by omega)]
  constructor
  · intro h t ht
    have hjL : 9 + zeros + t < L := by omega
    have hp := h (9 + zeros + t) (by omega) (by omega)
    simpa [FixedContentTagGate.physicalSymbol, hjL, padRead] using hp
  · intro h j hj0 hj1
    have hjL : j < L := by omega
    obtain ⟨t, rfl⟩ : ∃ t, j = 9 + zeros + t :=
      ⟨j - (9 + zeros), by omega⟩
    have ht : t < zeros := by omega
    simpa [FixedContentTagGate.physicalSymbol, hjL, padRead] using h t ht

/-- The fixed cleanup endpoint and the all-zero semantic fact are one-way
consequences of the existing validated trace hypotheses. -/
theorem cleanup_endpoint_and_allZeroSlice
    {a m B zeros : Nat}
    (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + 2 * zeros →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false) :
    let d := FixedGammaPayloadZeroCleanup.machine.run
      (FixedGammaPayloadZeroCleanup.cleanupClock zeros)
      (FixedGammaPayloadZeroCleanup.startConfig B x w zeros)
    d.state = FixedGammaPayloadZeroCleanup.qDone ∧
    d.head.val = 6 ∧
    d.tape = FixedPairContentMarkerErase.contentTape B x w ∧
    VirtualZeroTailReader.allZeroSlice?
      (Fin.append x w) (a + m) (9 + zeros) zeros = some true := by
  have hend := FixedGammaPayloadZeroCleanup.cleanup_endpoint
    (B := B) x w htag hg hzero hprefix
  have hp := hprefix (8 + 2 * zeros) (by omega) (by omega)
  have hfit : 9 + 2 * zeros ≤ a + m := by
    unfold FixedContentTagGate.physicalSymbol at hp
    split at hp
    · omega
    · contradiction
  have hsemantic :=
    (full_false_gamma_payload_iff_allZeroSlice
      (T := a + m) (Fin.append x w) hfit hfit).1 hprefix
  exact ⟨hend.1, hend.2.1, hend.2.2, hsemantic⟩

end ContractExpansion
end Frontier
end Pnp4
