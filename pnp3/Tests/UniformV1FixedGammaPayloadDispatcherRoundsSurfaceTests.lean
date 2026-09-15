import Complexity.Uniform.V1.FixedGammaPayloadDispatcherRounds

namespace Pnp3.Tests.UniformV1FixedGammaPayloadDispatcherRoundsSurfaceTests

open Complexity.Uniform.V1
open Complexity.Uniform.V1.PairEncoding
open Complexity.Uniform.V1.FixedGammaPayloadDispatcher
open Complexity.Uniform.V1.FixedGammaPayloadDispatcherRounds

def check_roundStartClock : Nat → Nat := roundStartClock
def check_boundaryArrivalClock : Nat → Nat → Nat := boundaryArrivalClock
def check_pendingArrivalClock : Nat → Nat → Nat := pendingArrivalClock
def check_pendingEndClock : Nat → Nat → Nat := pendingEndClock
def check_exhaustedArrivalClock : Nat → Nat := exhaustedArrivalClock
def check_zeroEndClock : Nat → Nat := zeroEndClock

theorem check_roundStartClock_eq (zeros : Nat) :
    roundStartClock zeros = 2 * zeros + 4 := roundStartClock_eq zeros

theorem check_boundaryArrivalClock_eq {zeros k : Nat} (hk : 1 ≤ k) :
    boundaryArrivalClock zeros k = k * (2 * zeros + 4) :=
  boundaryArrivalClock_eq hk

theorem check_pendingArrivalClock_eq {zeros k : Nat} (hk : 1 ≤ k) :
    pendingArrivalClock zeros k = (k + 1) * (2 * zeros + 4) :=
  pendingArrivalClock_eq hk

theorem check_pendingEndClock_eq {zeros k : Nat} (hk : 1 ≤ k) :
    pendingEndClock zeros k = 2 * zeros * k + 3 * zeros + 5 * k + 8 :=
  pendingEndClock_eq hk

theorem check_exhaustedArrivalClock_eq {zeros : Nat} (hzero : 0 < zeros) :
    exhaustedArrivalClock zeros = 2 * zeros * zeros + 5 * zeros + 3 :=
  exhaustedArrivalClock_eq hzero

theorem check_zeroEndClock_eq {zeros : Nat} (hzero : 0 < zeros) :
    zeroEndClock zeros = 2 * zeros * zeros + 8 * zeros + 6 :=
  zeroEndClock_eq hzero

theorem check_round_start_exact {a m B zeros k : Nat} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k ≤ zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false) :
    let d := machine.run (roundStartClock zeros) (startConfig B x w)
    d.state = qRoundStart ∧ d.head.val = 9 + zeros ∧
      d.tape = FixedGammaPayloadRoundStep.roundTape B x w zeros 1 :=
  round_start_exact x w htag hg hk hkz hprefix

theorem check_boundary_exact {a m B zeros k : Nat} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k ≤ zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false) :
    let d := machine.run (boundaryArrivalClock zeros k) (startConfig B x w)
    d.state = qRoundStart ∧ d.head.val = 8 + zeros + k ∧
      d.tape = FixedGammaPayloadRoundStep.roundTape B x w zeros k :=
  boundary_exact x w htag hg hk hkz hprefix

theorem check_pending_true_start_exact {a m B zeros k : Nat} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (htrue : FixedContentTagGate.physicalSymbol (Fin.append x w)
      (9 + zeros + k) = some true) :
    let d := machine.run (pendingArrivalClock zeros k) (startConfig B x w)
    d.state = qPendingStart ∧ d.head.val = 9 + zeros + k ∧
      d.tape = FixedGammaPayloadPendingOutcomes.pendingTape B x w k :=
  pending_true_start_exact x w htag hg hk hkz hprefix htrue

theorem check_pending_virtual_start_exact {a m B zeros k : Nat} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (hvirtual : 9 + zeros + k = a + m) :
    let d := machine.run (pendingArrivalClock zeros k) (startConfig B x w)
    d.state = qPendingStart ∧ d.head.val = 9 + zeros + k ∧
      d.tape = FixedGammaPayloadPendingOutcomes.pendingTape B x w k :=
  pending_virtual_start_exact x w htag hg hk hkz hprefix hvirtual

theorem check_exhausted_start_exact {a m B zeros : Nat} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + 2 * zeros →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false) :
    let d := machine.run (exhaustedArrivalClock zeros) (startConfig B x w)
    d.state = qZeroScanRight ∧ d.head.val = 8 + zeros ∧
      d.tape = FixedGammaPayloadRoundStep.roundTape B x w zeros zeros :=
  exhausted_start_exact x w htag hg hzero hprefix

def check_TrueExecution :
    {a m : Nat} → (B : Nat) → Bitstring a → Bitstring m → Nat → Nat → Prop :=
  TrueExecution

def check_VirtualExecution :
    {a m : Nat} → (B : Nat) → Bitstring a → Bitstring m → Nat → Nat → Prop :=
  VirtualExecution

def check_ZeroExecution :
    {a m : Nat} → (B : Nat) → Bitstring a → Bitstring m → Nat → Prop :=
  ZeroExecution

theorem check_TrueExecution_expand {a m B zeros k : Nat} (x : Bitstring a)
    (w : Bitstring m) : TrueExecution B x w zeros k ↔
    let d := machine.run (pendingEndClock zeros k) (startConfig B x w)
    d.state = qHasOne ∧ d.head.val = 6 ∧
    d.tape = FixedPairContentMarkerErase.contentTape B x w ∧
    (∀ s, s < pendingEndClock zeros k →
      (machine.run s (startConfig B x w)).state ≠ qHasOne) ∧
    (∀ s, (machine.run s (startConfig B x w)).state ≠ qAllZero ∧
      (machine.run s (startConfig B x w)).state ≠ qReject) := by
  rfl

theorem check_VirtualExecution_expand {a m B zeros k : Nat} (x : Bitstring a)
    (w : Bitstring m) : VirtualExecution B x w zeros k ↔
    let d := machine.run (pendingEndClock zeros k) (startConfig B x w)
    d.state = qAllZero ∧ d.head.val = 6 ∧
    d.tape = FixedPairContentMarkerErase.contentTape B x w ∧
    (∀ s, s < pendingEndClock zeros k →
      (machine.run s (startConfig B x w)).state ≠ qAllZero) ∧
    (∀ s, (machine.run s (startConfig B x w)).state ≠ qHasOne ∧
      (machine.run s (startConfig B x w)).state ≠ qReject) := by
  rfl

theorem check_ZeroExecution_expand {a m B zeros : Nat} (x : Bitstring a)
    (w : Bitstring m) : ZeroExecution B x w zeros ↔
    let d := machine.run (zeroEndClock zeros) (startConfig B x w)
    d.state = qAllZero ∧ d.head.val = 6 ∧
    d.tape = FixedPairContentMarkerErase.contentTape B x w ∧
    (∀ s, s < zeroEndClock zeros →
      (machine.run s (startConfig B x w)).state ≠ qAllZero) ∧
    (∀ s, (machine.run s (startConfig B x w)).state ≠ qHasOne ∧
      (machine.run s (startConfig B x w)).state ≠ qReject) := by
  rfl

theorem check_true_exact {a m B zeros k : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (htrue : FixedContentTagGate.physicalSymbol (Fin.append x w)
      (9 + zeros + k) = some true) :
    let d := machine.run (pendingEndClock zeros k) (startConfig B x w)
    d.state = qHasOne ∧ d.head.val = 6 ∧
    d.tape = FixedPairContentMarkerErase.contentTape B x w ∧
    (∀ s, s < pendingEndClock zeros k →
      (machine.run s (startConfig B x w)).state ≠ qHasOne) ∧
    (∀ s, (machine.run s (startConfig B x w)).state ≠ qAllZero ∧
      (machine.run s (startConfig B x w)).state ≠ qReject) :=
  (check_TrueExecution_expand x w).mp
    (true_exact x w htag hg hk hkz hprefix htrue)

theorem check_virtual_exact {a m B zeros k : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (hvirtual : 9 + zeros + k = a + m) :
    let d := machine.run (pendingEndClock zeros k) (startConfig B x w)
    d.state = qAllZero ∧ d.head.val = 6 ∧
    d.tape = FixedPairContentMarkerErase.contentTape B x w ∧
    (∀ s, s < pendingEndClock zeros k →
      (machine.run s (startConfig B x w)).state ≠ qAllZero) ∧
    (∀ s, (machine.run s (startConfig B x w)).state ≠ qHasOne ∧
      (machine.run s (startConfig B x w)).state ≠ qReject) :=
  (check_VirtualExecution_expand x w).mp
    (virtual_exact x w htag hg hk hkz hprefix hvirtual)

theorem check_zero_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + 2 * zeros →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false) :
    let d := machine.run (zeroEndClock zeros) (startConfig B x w)
    d.state = qAllZero ∧ d.head.val = 6 ∧
    d.tape = FixedPairContentMarkerErase.contentTape B x w ∧
    (∀ s, s < zeroEndClock zeros →
      (machine.run s (startConfig B x w)).state ≠ qAllZero) ∧
    (∀ s, (machine.run s (startConfig B x w)).state ≠ qHasOne ∧
      (machine.run s (startConfig B x w)).state ≠ qReject) :=
  (check_ZeroExecution_expand x w).mp
    (zero_exact x w htag hg hzero hprefix)

end Pnp3.Tests.UniformV1FixedGammaPayloadDispatcherRoundsSurfaceTests
