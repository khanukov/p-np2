import Complexity.Uniform.V1.FixedContentGammaAnchor
import Pnp4.Frontier.ContractExpansion.FixedContentGammaTerminatorCorrect

/-! Proof-level logical restoration and the operational G1 → G2a handoff.
This module does not claim an executable restoration step; physical restoration
is the G2b obligation. -/

namespace Pnp4.Frontier.ContractExpansion

open AlgorithmsToLowerBounds
open Pnp3.Complexity.Uniform.V1

/-- Proof-level logical restoration writes the literal erased tag bit rather
than reading that restored bit from the tape.  It copies all other cells and is
not a machine transition. -/
def logicalRestoreGammaAnchorCell7 {a m B : Nat}
    (t : Fin (tapeLength (PairEncoding.pairLength a m) B) → Option Bool) := fun i =>
  if i.val = 7 then some false else t i

theorem logicalRestore_markedTape {a m B : Nat} (x : PrefixBitVec a) (w : PrefixBitVec m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    logicalRestoreGammaAnchorCell7 (FixedContentGammaAnchor.markedTape B x w) =
      FixedPairContentMarkerErase.contentTape B x w := by
  have hL := (FixedContentTagGate.tag_contract (Fin.append x w)).2.2.2.2.2.2.2.2.2 htag
  funext i
  by_cases h : i.val = 7
  · have hi : i.val < a + m := by omega
    have hcell := (FixedContentTagGate.tag_contract (Fin.append x w)).2.2.2.2.2.2.2.2.1.mp htag
      ⟨7, by decide⟩
    simp [logicalRestoreGammaAnchorCell7, h, FixedPairContentMarkerErase.contentTape]
    simpa [FixedContentTagGate.expectedTagBit, FixedContentTagGate.physicalSymbol, hi]
      using hcell
  · simp [logicalRestoreGammaAnchorCell7, FixedContentGammaAnchor.markedTape, h]

theorem fixedGammaAnchor_header_contract {a m B : Nat}
    (x : PrefixBitVec a) (w : PrefixBitVec m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    let c := FixedContentGammaAnchor.machine.run (FixedContentGammaAnchor.deadline a m)
      (FixedContentGammaAnchor.startConfig B x w)
    (c.state = FixedContentGammaAnchor.machine.accept ↔
      (contentHeader? (Fin.append x w)).isSome) ∧
    (c.state = FixedContentGammaAnchor.machine.reject ↔
      contentHeader? (Fin.append x w) = none) := by
  rw [FixedContentGammaAnchor.run_deadline x w htag]
  have hh := fixedGamma_header_contract (Fin.append x w)
  cases hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) with
  | some zeros =>
      have : (contentHeader? (Fin.append x w)).isSome := hh.mp (by simp [hg])
      cases hc : contentHeader? (Fin.append x w) with
      | none => simp [hc] at this
      | some nc =>
          simp [FixedContentGammaAnchor.finalConfig, hg, FixedContentGammaAnchor.machine,
            FixedContentGammaAnchor.qAccept, FixedContentGammaAnchor.qReject]
  | none =>
      have hc : contentHeader? (Fin.append x w) = none := by
        cases h : contentHeader? (Fin.append x w) with
        | none => rfl
        | some nc => have := hh.mpr (by simp [h]); simp [hg] at this
      simp [FixedContentGammaAnchor.finalConfig, hg, hc, FixedContentGammaAnchor.machine,
        FixedContentGammaAnchor.qAccept, FixedContentGammaAnchor.qReject]

theorem fixedGammaAnchor_decode_and_restoration {a m B : Nat}
    (x : PrefixBitVec a) (w : PrefixBitVec m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hsuccess : (FixedContentGammaTerminator.gammaZeros? (Fin.append x w)).isSome) :
    (∃ n consumed, contentHeader? (Fin.append x w) = some (n, consumed)) ∧
    logicalRestoreGammaAnchorCell7
      (FixedContentGammaAnchor.machine.run (FixedContentGammaAnchor.deadline a m)
        (FixedContentGammaAnchor.startConfig B x w)).tape =
      FixedPairContentMarkerErase.contentTape B x w := by
  constructor
  · have hh := (fixedGamma_header_contract (Fin.append x w)).mp hsuccess
    cases hc : contentHeader? (Fin.append x w) with
    | none => simp [hc] at hh
    | some nc => rcases nc with ⟨n, consumed⟩; exact ⟨n, consumed, rfl⟩
  · rw [FixedContentGammaAnchor.run_deadline x w htag]
    cases hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) with
    | none => simp [hg] at hsuccess
    | some zeros => simpa [FixedContentGammaAnchor.finalConfig, hg] using
        logicalRestore_markedTape (B := B) x w htag

theorem fixedGammaAnchor_operational_handoff {a m B : Nat}
    (x : PrefixBitVec a) (w : PrefixBitVec m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    let g1 := FixedContentGammaTerminator.machine.run
      (FixedContentGammaTerminator.deadline a m) (FixedContentGammaTerminator.startConfig B x w)
    let g2 := FixedContentGammaAnchor.machine.run
      (FixedContentGammaAnchor.deadline a m) (FixedContentGammaAnchor.retag g1)
    g1 = FixedContentGammaTerminator.finalConfig B x w ∧
    g2 = FixedContentGammaAnchor.finalConfig B x w ∧
    (g2.state = FixedContentGammaAnchor.machine.accept ↔
      (contentHeader? (Fin.append x w)).isSome) ∧
    (g2.state = FixedContentGammaAnchor.machine.reject ↔
      contentHeader? (Fin.append x w) = none) ∧
    ((FixedContentGammaTerminator.gammaZeros? (Fin.append x w)).isSome →
      logicalRestoreGammaAnchorCell7 g2.tape = FixedPairContentMarkerErase.contentTape B x w) := by
  dsimp
  rw [FixedContentGammaTerminator.run_deadline x w htag]
  change _ ∧
    FixedContentGammaAnchor.machine.run (FixedContentGammaAnchor.deadline a m)
      (FixedContentGammaAnchor.startConfig B x w) = _ ∧ _
  rw [FixedContentGammaAnchor.run_deadline x w htag]
  refine ⟨rfl, rfl, ?_⟩
  rcases fixedGammaAnchor_header_contract (B := B) x w htag with ⟨ha, hr⟩
  exact ⟨ha, hr, fun hs => (fixedGammaAnchor_decode_and_restoration x w htag hs).2⟩

end Pnp4.Frontier.ContractExpansion
