import Complexity.Uniform.V1.FixedGammaPayloadDispatcherDeadline

namespace Pnp3.Tests.UniformV1FixedGammaPayloadDispatcherDeadlineSurfaceTests

open Complexity.Uniform.V1
open Complexity.Uniform.V1.PairEncoding
open Complexity.Uniform.V1.FixedGammaPayloadDispatcher
open Complexity.Uniform.V1.FixedGammaPayloadDispatcherDeadline

def check_deadline (N : Nat) : Nat := deadline N

theorem check_deadline_eq (N : Nat) : deadline N = 2 * N * N := deadline_eq N

theorem check_gamma_payload_first_index {L zeros : Nat} (z : Bitstring L)
    (hg : FixedContentGammaTerminator.gammaZeros? z = some zeros) :
    ∃ k, k ≤ zeros ∧
      (∀ t, t < k → FixedContentTagGate.physicalSymbol z (9 + zeros + t) = some false) ∧
      (k = zeros ∨
        (k < zeros ∧ FixedContentTagGate.physicalSymbol z (9 + zeros + k) = some true) ∨
        (k < zeros ∧ 9 + zeros + k = L)) :=
  gamma_payload_first_index z hg

theorem check_malformedClock_le_deadline {N : Nat} (hN : 8 ≤ N) :
    1 ≤ deadline N := malformedClock_le_deadline hN

theorem check_zeroWidthClock_le_deadline {N : Nat} (hN : 8 ≤ N) :
    2 ≤ deadline N := zeroWidthClock_le_deadline hN

theorem check_firstEndClock_le_deadline {N zeros : Nat} (hf : 9 + zeros ≤ N) :
    3 * zeros + 6 ≤ deadline N := firstEndClock_le_deadline hf

theorem check_pendingEndClock_le_deadline {N zeros k : Nat}
    (hf : 9 + zeros ≤ N) (hk : 1 ≤ k) (hkz : k < zeros) :
    FixedGammaPayloadDispatcherRounds.pendingEndClock zeros k ≤ deadline N :=
  pendingEndClock_le_deadline hf hk hkz

theorem check_zeroEndClock_le_deadline {N zeros : Nat}
    (hf : 9 + zeros ≤ N) (hz : 0 < zeros) :
    FixedGammaPayloadDispatcherRounds.zeroEndClock zeros ≤ deadline N :=
  zeroEndClock_le_deadline hf hz

theorem check_malformed_at_deadline {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none) :
    let d := machine.run (deadline (a + m)) (startConfig B x w)
    d.state = qReject ∧ d.head.val = a + m ∧
      d.tape = FixedPairContentMarkerErase.contentTape B x w :=
  malformed_at_deadline x w htag hg

theorem check_zero_width_at_deadline {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 0) :
    let d := machine.run (deadline (a + m)) (startConfig B x w)
    d.state = qAllZero ∧ d.head.val = 7 ∧
      d.tape = FixedPairContentMarkerErase.contentTape B x w :=
  zero_width_at_deadline x w htag hg

theorem check_true_at_deadline {a m B zeros k : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : k < zeros)
    (hp : ∀ t, t < k → FixedContentTagGate.physicalSymbol (Fin.append x w)
      (9 + zeros + t) = some false)
    (ht : FixedContentTagGate.physicalSymbol (Fin.append x w)
      (9 + zeros + k) = some true) :
    let d := machine.run (deadline (a + m)) (startConfig B x w)
    d.state = qHasOne ∧ d.head.val = 6 ∧
      d.tape = FixedPairContentMarkerErase.contentTape B x w :=
  true_at_deadline x w htag hg hk hp ht

theorem check_virtual_at_deadline {a m B zeros k : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : k < zeros)
    (hp : ∀ t, t < k → FixedContentTagGate.physicalSymbol (Fin.append x w)
      (9 + zeros + t) = some false) (hv : 9 + zeros + k = a + m) :
    let d := machine.run (deadline (a + m)) (startConfig B x w)
    d.state = qAllZero ∧ d.head.val = 6 ∧
      d.tape = FixedPairContentMarkerErase.contentTape B x w :=
  virtual_at_deadline x w htag hg hk hp hv

theorem check_exhausted_at_deadline {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hz : 0 < zeros)
    (hp : ∀ t, t < zeros → FixedContentTagGate.physicalSymbol (Fin.append x w)
      (9 + zeros + t) = some false) :
    let d := machine.run (deadline (a + m)) (startConfig B x w)
    d.state = qAllZero ∧ d.head.val = 6 ∧
      d.tape = FixedPairContentMarkerErase.contentTape B x w :=
  exhausted_at_deadline x w htag hg hz hp

theorem check_tagged_endpoint_classification {a m B : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    let d := machine.run (deadline (a + m)) (startConfig B x w)
    d.tape = FixedPairContentMarkerErase.contentTape B x w ∧
    ((d.state = qReject ∧ d.head.val = a + m ∧
        FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none) ∨
      (d.state = qAllZero ∧ d.head.val = 7 ∧
        FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 0) ∨
      (∃ zeros, FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros ∧
        0 < zeros ∧ d.head.val = 6 ∧
        ((d.state = qHasOne ∧ ∃ k, k < zeros ∧
            FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros + k) = some true) ∨
          (d.state = qAllZero ∧ ¬ ∃ k, k < zeros ∧
            FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros + k) = some true)))) :=
  tagged_endpoint_classification x w htag

theorem check_qHasOne_iff {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    (machine.run (deadline (a + m)) (startConfig B x w)).state = qHasOne ↔
      ∃ k, k < zeros ∧
        FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros + k) = some true :=
  qHasOne_iff x w htag hg

theorem check_qAllZero_iff {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    (machine.run (deadline (a + m)) (startConfig B x w)).state = qAllZero ↔
      ¬ ∃ k, k < zeros ∧
        FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros + k) = some true :=
  qAllZero_iff x w htag hg

theorem check_qReject_iff {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    (machine.run (deadline (a + m)) (startConfig B x w)).state = qReject ↔
      FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none :=
  qReject_iff x w htag

end Pnp3.Tests.UniformV1FixedGammaPayloadDispatcherDeadlineSurfaceTests
