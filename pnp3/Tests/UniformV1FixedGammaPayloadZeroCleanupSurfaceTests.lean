import Complexity.Uniform.V1.FixedGammaPayloadZeroCleanup

namespace Pnp3.Tests.UniformV1FixedGammaPayloadZeroCleanupSurfaceTests

open Complexity.Uniform.V1
open Complexity.Uniform.V1.PairEncoding
open Complexity.Uniform.V1.FixedGammaPayloadZeroCleanup

def check_stateCount : Nat := stateCount
def check_qScanRight : Fin stateCount := qScanRight
def check_qBackTerm : Fin stateCount := qBackTerm
def check_qFillCounter : Fin stateCount := qFillCounter
def check_qDone : Fin stateCount := qDone
def check_qReject : Fin stateCount := qReject
def check_machine : UniformTM := machine
def check_cleanupClock : Nat → Nat := cleanupClock

def check_retag {N B : Nat} :
    Config FixedGammaPayloadRoundStep.stateCount N B → Config stateCount N B := retag

def check_startConfig {a m : Nat} :
    (B : Nat) → Bitstring a → Bitstring m → Nat →
      Config stateCount (pairLength a m) B :=
  fun B x w => startConfig B x w

theorem check_table_and_resource_pins :
    (∀ s, machine.step qScanRight s = match s with
      | none => (qBackTerm, some false, .left)
      | some b => (qScanRight, some b, .right)) ∧
    (∀ s, machine.step qBackTerm s = match s with
      | none => (qFillCounter, some false, .left)
      | some b => (qBackTerm, some b, .left)) ∧
    (∀ s, machine.step qFillCounter s = match s with
      | none => (qFillCounter, some false, .left)
      | some true => (qDone, some true, .stay)
      | some false => (qReject, some false, .stay)) ∧
    (∀ s, machine.step qDone s = (qDone, s, .stay)) ∧
    (∀ s, machine.step qReject s = (qReject, s, .stay)) ∧
    machine.stateCount = 5 ∧ machine.start = qScanRight ∧
    machine.accept = qDone ∧ machine.reject = qReject ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 15 :=
  table_and_resource_pins

theorem check_handoff_from_exhausted_reachable {a m B zeros : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + 2 * zeros →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false) :
    let p := FixedGammaPayloadRoundStep.machine.run
      (FixedGammaPayloadExhausted.exhaustedClock zeros)
      (FixedGammaPayloadRoundStep.startConfig B x w zeros)
    let c := startConfig B x w zeros
    p.state = FixedGammaPayloadRoundStep.qExhausted ∧ p.head.val = 8 + zeros ∧
      p.tape = FixedGammaPayloadRoundStep.roundTape B x w zeros zeros ∧ c = retag p :=
  handoff_from_exhausted_reachable (B := B) x w htag hg hzero hprefix

theorem check_cleanup_arithmetic_bounds {a m B zeros : Nat}
    (hp : 8 + 2 * zeros < a + m) :
    0 < 6 ∧ 8 + 2 * zeros < tapeLength (pairLength a m) B :=
  cleanup_arithmetic_bounds (B := B) hp

theorem check_initial_footprint {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (i : Fin (tapeLength (pairLength a m) B)) (h7 : i.val ≠ 7)
    (hcounter : ¬ (8 ≤ i.val ∧ i.val < 8 + zeros))
    (hcursor : i.val ≠ 8 + 2 * zeros) :
    FixedGammaPayloadRoundStep.roundTape B x w zeros zeros i =
      FixedPairContentMarkerErase.contentTape B x w i :=
  initial_footprint x w i h7 hcounter hcursor

theorem check_cleanup_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + 2 * zeros →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false) :
    let c := startConfig B x w zeros
    machine.run (cleanupClock zeros) c =
      ⟨qDone, ⟨6, by
        rcases FixedContentTagGate.tag_contract (Fin.append x w) with
          ⟨_, _, _, _, _, _, _, _, _, hlenTag⟩
        have hL := hlenTag htag
        unfold tapeLength pairLength
        omega⟩,
        FixedPairContentMarkerErase.contentTape B x w⟩ ∧
    (∀ s, s < cleanupClock zeros → (machine.run s c).state ≠ qDone) :=
  cleanup_exact (B := B) x w htag hg hzero hprefix

theorem check_cleanup_endpoint {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + 2 * zeros →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false) :
    let d := machine.run (cleanupClock zeros) (startConfig B x w zeros)
    d.state = qDone ∧ d.head.val = 6 ∧
      d.tape = FixedPairContentMarkerErase.contentTape B x w :=
  cleanup_endpoint (B := B) x w htag hg hzero hprefix

theorem check_per_step_budget_independent : ∀ q s,
    machine.step q s = machine.rawStep q s :=
  per_step_budget_independent

end Pnp3.Tests.UniformV1FixedGammaPayloadZeroCleanupSurfaceTests
