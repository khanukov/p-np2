import Complexity.Uniform.V1.FixedGammaPayloadPendingCleanup

namespace Pnp3.Tests.UniformV1FixedGammaPayloadPendingCleanupSurfaceTests

open Complexity.Uniform.V1
open Complexity.Uniform.V1.PairEncoding
open Complexity.Uniform.V1.FixedGammaPayloadPendingCleanup

def check_stateCount : Nat := stateCount
def check_qStart : Fin stateCount := qStart
def check_qBackOne : Fin stateCount := qBackOne
def check_qBackVirtual : Fin stateCount := qBackVirtual
def check_qFillOne : Fin stateCount := qFillOne
def check_qFillVirtual : Fin stateCount := qFillVirtual
def check_qOne : Fin stateCount := qOne
def check_qVirtual : Fin stateCount := qVirtual
def check_qReject : Fin stateCount := qReject
def check_machine : UniformTM := machine
def check_cleanupClock : Nat → Nat → Nat := cleanupClock

def check_retag {N B : Nat} :
    Config FixedGammaPayloadRoundStep.stateCount N B → Config stateCount N B := retag

def check_startConfig {a m : Nat} :
    (B : Nat) → Bitstring a → Bitstring m → Nat → Nat →
      Config stateCount (pairLength a m) B :=
  fun B x w zeros k => startConfig B x w zeros k

theorem check_table_and_resource_pins :
    (machine.step qStart (some true) = (qBackOne, some true, .left)) ∧
    (machine.step qStart none = (qBackVirtual, none, .left)) ∧
    (machine.step qStart (some false) = (qReject, some false, .stay)) ∧
    (∀ s, machine.step qBackOne s = match s with
      | none => (qFillOne, some false, .left)
      | some b => (qBackOne, some b, .left)) ∧
    (∀ s, machine.step qBackVirtual s = match s with
      | none => (qFillVirtual, some false, .left)
      | some b => (qBackVirtual, some b, .left)) ∧
    (∀ s, machine.step qFillOne s = match s with
      | none => (qFillOne, some false, .left)
      | some true => (qOne, some true, .stay)
      | some false => (qReject, some false, .stay)) ∧
    (∀ s, machine.step qFillVirtual s = match s with
      | none => (qFillVirtual, some false, .left)
      | some true => (qVirtual, some true, .stay)
      | some false => (qReject, some false, .stay)) ∧
    (∀ s, machine.step qOne s = (qOne, s, .stay)) ∧
    (∀ s, machine.step qVirtual s = (qVirtual, s, .stay)) ∧
    (∀ s, machine.step qReject s = (qReject, s, .stay)) ∧
    machine.stateCount = 8 ∧ machine.start = qStart ∧ machine.accept = qOne ∧
    machine.reject = qReject ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 24 :=
  table_and_resource_pins

theorem check_cleanupClock_eq (zeros k : Nat) :
    cleanupClock zeros k = zeros + k + 4 := cleanupClock_eq zeros k

theorem check_handoff_from_pending_true_reachable {a m B zeros k : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (htrue : FixedContentTagGate.physicalSymbol (Fin.append x w)
      (9 + zeros + k) = some true) :
    let p := FixedGammaPayloadRoundStep.machine.run
      (FixedGammaPayloadPendingOutcomes.pendingClock zeros k)
      (FixedGammaPayloadRoundStep.startConfig B x w zeros)
    let c := startConfig B x w zeros k
    p.state = FixedGammaPayloadRoundStep.qOnePending ∧
      p.head.val = 9 + zeros + k ∧
      p.tape = FixedGammaPayloadPendingOutcomes.pendingTape B x w k ∧ c = retag p :=
  handoff_from_pending_true_reachable (B := B) x w htag hg hk hkz hprefix htrue

theorem check_handoff_from_pending_virtual_reachable {a m B zeros k : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (hvirtual : 9 + zeros + k = a + m) :
    let p := FixedGammaPayloadRoundStep.machine.run
      (FixedGammaPayloadPendingOutcomes.pendingClock zeros k)
      (FixedGammaPayloadRoundStep.startConfig B x w zeros)
    let c := startConfig B x w zeros k
    p.state = FixedGammaPayloadRoundStep.qVirtualPending ∧
      p.head.val = 9 + zeros + k ∧
      p.tape = FixedGammaPayloadPendingOutcomes.pendingTape B x w k ∧ c = retag p :=
  handoff_from_pending_virtual_reachable (B := B) x w htag hg hk hkz hprefix hvirtual

theorem check_cleanup_arithmetic_bounds {a m B zeros k : Nat}
    (hp : 8 + zeros + k < a + m) :
    0 < 7 ∧ 9 + zeros + k < tapeLength (pairLength a m) B :=
  cleanup_arithmetic_bounds (B := B) hp

theorem check_initial_footprint {a m B k : Nat} (x : Bitstring a) (w : Bitstring m)
    (i : Fin (tapeLength (pairLength a m) B)) (h7 : i.val ≠ 7)
    (hcounter : ¬ (8 ≤ i.val ∧ i.val < 9 + k)) :
    FixedGammaPayloadPendingOutcomes.pendingTape B x w k i =
      FixedPairContentMarkerErase.contentTape B x w i :=
  initial_footprint x w i h7 hcounter

theorem check_true_cleanup_exact {a m B zeros k : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (htrue : FixedContentTagGate.physicalSymbol (Fin.append x w)
      (9 + zeros + k) = some true) :
    let c := startConfig B x w zeros k
    machine.run (cleanupClock zeros k) c =
      ⟨qOne, ⟨6, by
        have hL := (FixedContentTagGate.tag_contract (Fin.append x w)).2.2.2.2.2.2.2.2.2 htag
        unfold tapeLength pairLength
        omega⟩, FixedPairContentMarkerErase.contentTape B x w⟩ ∧
    (∀ s, s < cleanupClock zeros k →
      (machine.run s c).state ≠ qOne ∧ (machine.run s c).state ≠ qVirtual) ∧
    (∀ s, (machine.run s c).state ≠ qVirtual) :=
  true_cleanup_exact (B := B) x w htag hg hk hkz hprefix htrue

theorem check_virtual_cleanup_exact {a m B zeros k : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (hvirtual : 9 + zeros + k = a + m) :
    let c := startConfig B x w zeros k
    machine.run (cleanupClock zeros k) c =
      ⟨qVirtual, ⟨6, by unfold tapeLength pairLength; omega⟩,
        FixedPairContentMarkerErase.contentTape B x w⟩ ∧
    (∀ s, s < cleanupClock zeros k →
      (machine.run s c).state ≠ qOne ∧ (machine.run s c).state ≠ qVirtual) ∧
    (∀ s, (machine.run s c).state ≠ qOne) :=
  virtual_cleanup_exact (B := B) x w htag hg hk hkz hprefix hvirtual

theorem check_true_cleanup_endpoint {a m B zeros k : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (htrue : FixedContentTagGate.physicalSymbol (Fin.append x w)
      (9 + zeros + k) = some true) :
    let d := machine.run (cleanupClock zeros k) (startConfig B x w zeros k)
    d.state = qOne ∧ d.head.val = 6 ∧
      d.tape = FixedPairContentMarkerErase.contentTape B x w :=
  true_cleanup_endpoint (B := B) x w htag hg hk hkz hprefix htrue

theorem check_virtual_cleanup_endpoint {a m B zeros k : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hk : 1 ≤ k) (hkz : k < zeros)
    (hprefix : ∀ j, 9 + zeros ≤ j → j < 9 + zeros + k →
      FixedContentTagGate.physicalSymbol (Fin.append x w) j = some false)
    (hvirtual : 9 + zeros + k = a + m) :
    let d := machine.run (cleanupClock zeros k) (startConfig B x w zeros k)
    d.state = qVirtual ∧ d.head.val = 6 ∧
      d.tape = FixedPairContentMarkerErase.contentTape B x w :=
  virtual_cleanup_endpoint (B := B) x w htag hg hk hkz hprefix hvirtual

theorem check_done_tags_distinct : qOne ≠ qVirtual := done_tags_distinct

theorem check_done_absorbing {N B : Nat} (c : Config stateCount N B)
    (hc : c.state = qOne ∨ c.state = qVirtual) (s : Nat) :
    machine.run s c = c := done_absorbing c hc s

theorem check_head_nonincreasing {N B : Nat} (c : Config stateCount N B) (s : Nat) :
    (machine.run s c).head.val ≤ c.head.val := head_nonincreasing c s

theorem check_tape_above_head_fixed {N B : Nat} (c : Config stateCount N B) (s : Nat)
    (i : Fin (tapeLength N B)) (hi : c.head.val < i.val) :
    (machine.run s c).tape i = c.tape i := tape_above_head_fixed c s i hi

theorem check_no_row_moves_right : ∀ q s,
    (machine.step q s).2.2 ≠ Move.right := no_row_moves_right

theorem check_per_step_budget_independent : ∀ q s,
    machine.step q s = machine.rawStep q s := per_step_budget_independent

end Pnp3.Tests.UniformV1FixedGammaPayloadPendingCleanupSurfaceTests
