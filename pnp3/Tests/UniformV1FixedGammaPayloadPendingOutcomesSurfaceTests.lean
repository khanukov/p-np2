import Complexity.Uniform.V1.FixedGammaPayloadPendingOutcomes

namespace Pnp3.Tests.UniformV1FixedGammaPayloadPendingOutcomesSurfaceTests

open Complexity.Uniform.V1
open Complexity.Uniform.V1.PairEncoding
open Complexity.Uniform.V1.FixedGammaPayloadRoundStep
open Complexity.Uniform.V1.FixedGammaPayloadRoundDriver
open Complexity.Uniform.V1.FixedGammaPayloadPendingOutcomes

def check_pendingTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m)
    (k : Nat) : Fin (tapeLength (pairLength a m) B) → Option Bool :=
  pendingTape B x w k

theorem check_pendingTape_footprint {a m B k : Nat} (x : Bitstring a) (w : Bitstring m)
    (i : Fin (tapeLength (pairLength a m) B)) (h7 : i.val ≠ 7)
    (hcounter : ¬ (8 ≤ i.val ∧ i.val < 9 + k)) :
    pendingTape B x w k i = FixedPairContentMarkerErase.contentTape B x w i :=
  pendingTape_footprint x w i h7 hcounter

def check_pendingClock : Nat → Nat → Nat := pendingClock

theorem check_pendingClock_eq {zeros k : Nat} (hk : 1 ≤ k) :
    pendingClock zeros k = boundaryClock zeros (k + 1) := pendingClock_eq hk

theorem check_pending_no_clamp_facts {a m B zeros k : Nat}
    (x : Bitstring a) (w : Bitstring m) (hk : 1 ≤ k)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false) :
    0 < 7 + k ∧ 9 + zeros + k < tapeLength (pairLength a m) B :=
  pending_no_clamp_facts x w hk hprefix

theorem check_pending_true_tail_exact {a m B zeros k : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (htrue : FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros + k) = some true)
    (c : Config stateCount (pairLength a m) B) (hc : RoundInvariant B x w zeros k c) :
    let d := machine.run (roundCost zeros) c
    d.state = qOnePending ∧ d.head.val = 9 + zeros + k ∧ d.tape = pendingTape B x w k :=
  pending_true_tail_exact x w hg hk hkz hprefix htrue c hc

theorem check_pending_virtual_tail_exact {a m B zeros k : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (hvirtual : 9 + zeros + k = a + m)
    (c : Config stateCount (pairLength a m) B) (hc : RoundInvariant B x w zeros k c) :
    let d := machine.run (roundCost zeros) c
    d.state = qVirtualPending ∧ d.head.val = 9 + zeros + k ∧ d.tape = pendingTape B x w k :=
  pending_virtual_tail_exact x w hg hk hkz hprefix hvirtual c hc

theorem check_pending_absorbing {N B : Nat} (c : Config stateCount N B)
    (hc : c.state = qOnePending ∨ c.state = qVirtualPending) (s : Nat) :
    machine.run s c = c := pending_absorbing c hc s

theorem check_pending_strict {a m B zeros k : Nat} (x : Bitstring a) (w : Bitstring m)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (c : Config stateCount (pairLength a m) B) (hc : RoundInvariant B x w zeros k c)
    (s : Nat) (hs : s < roundCost zeros) :
    (machine.run s c).state ≠ qOnePending ∧ (machine.run s c).state ≠ qVirtualPending :=
  pending_strict x w hg hk hkz hprefix c hc s hs

theorem check_pending_true_reachable {a m B zeros k : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (htrue : FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros + k) = some true) :
    let d := machine.run (pendingClock zeros k) (startConfig B x w zeros)
    d.state = qOnePending ∧ d.head.val = 9 + zeros + k ∧ d.tape = pendingTape B x w k :=
  pending_true_reachable x w htag hg hk hkz hprefix htrue

theorem check_pending_virtual_reachable {a m B zeros k : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (hvirtual : 9 + zeros + k = a + m) :
    let d := machine.run (pendingClock zeros k) (startConfig B x w zeros)
    d.state = qVirtualPending ∧ d.head.val = 9 + zeros + k ∧ d.tape = pendingTape B x w k :=
  pending_virtual_reachable x w htag hg hk hkz hprefix hvirtual

theorem check_pending_first_arrival {a m B zeros k : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (s : Nat) (hs : s < pendingClock zeros k) :
    (machine.run s (startConfig B x w zeros)).state ≠ qOnePending ∧
      (machine.run s (startConfig B x w zeros)).state ≠ qVirtualPending :=
  pending_first_arrival x w htag hg hk hkz hprefix s hs

end Pnp3.Tests.UniformV1FixedGammaPayloadPendingOutcomesSurfaceTests
