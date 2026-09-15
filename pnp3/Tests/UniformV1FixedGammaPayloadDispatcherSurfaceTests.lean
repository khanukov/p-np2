import Complexity.Uniform.V1.FixedGammaPayloadDispatcher

namespace Pnp3.Tests.UniformV1FixedGammaPayloadDispatcherSurfaceTests

open Complexity.Uniform.V1
open Complexity.Uniform.V1.PairEncoding
open Complexity.Uniform.V1.FixedGammaPayloadDispatcher

def check_stateCount : Nat := stateCount
def check_qCursorStart : Fin stateCount := qCursorStart
def check_qCursorBackFirst : Fin stateCount := qCursorBackFirst
def check_qCursorBackSeen : Fin stateCount := qCursorBackSeen
def check_qCursorSpend : Fin stateCount := qCursorSpend
def check_qCursorSeekTerm : Fin stateCount := qCursorSeekTerm
def check_qCursorRead : Fin stateCount := qCursorRead
def check_qCursorRestoreOne : Fin stateCount := qCursorRestoreOne
def check_qCursorRestoreVirtual : Fin stateCount := qCursorRestoreVirtual
def check_qCursorFillOne : Fin stateCount := qCursorFillOne
def check_qCursorFillVirtual : Fin stateCount := qCursorFillVirtual
def check_qRoundStart : Fin stateCount := qRoundStart
def check_qRoundBackPayload : Fin stateCount := qRoundBackPayload
def check_qRoundBackCounter : Fin stateCount := qRoundBackCounter
def check_qRoundSpend : Fin stateCount := qRoundSpend
def check_qRoundSeekTerm : Fin stateCount := qRoundSeekTerm
def check_qRoundSeekHole : Fin stateCount := qRoundSeekHole
def check_qRoundRead : Fin stateCount := qRoundRead
def check_qZeroScanRight : Fin stateCount := qZeroScanRight
def check_qZeroBackTerm : Fin stateCount := qZeroBackTerm
def check_qZeroFillCounter : Fin stateCount := qZeroFillCounter
def check_qPendingStart : Fin stateCount := qPendingStart
def check_qPendingBackOne : Fin stateCount := qPendingBackOne
def check_qPendingBackVirtual : Fin stateCount := qPendingBackVirtual
def check_qPendingFillOne : Fin stateCount := qPendingFillOne
def check_qPendingFillVirtual : Fin stateCount := qPendingFillVirtual
def check_qAllZero : Fin stateCount := qAllZero
def check_qHasOne : Fin stateCount := qHasOne
def check_qReject : Fin stateCount := qReject
def check_raw :
    Fin stateCount → Option Bool → Fin stateCount × Option Bool × Move := raw
def check_machine : UniformTM := machine
def check_retagG2a {N B : Nat} :
    Config FixedContentGammaAnchor.stateCount N B → Config stateCount N B := retagG2a
def check_startConfig {a m : Nat} :
    (B : Nat) → Bitstring a → Bitstring m → Config stateCount (pairLength a m) B := startConfig

theorem check_table_and_resource_pins :
    (∀ s, machine.step qCursorStart s = match s with
      | some true => (qCursorBackFirst, some true, .left) | s => (qReject, s, .stay)) ∧
    (∀ s, machine.step qCursorBackFirst s = match s with
      | some false => (qCursorBackSeen, some false, .left)
      | none => (qAllZero, some false, .stay) | s => (qReject, s, .stay)) ∧
    (∀ s, machine.step qCursorBackSeen s = match s with
      | some false => (qCursorBackSeen, some false, .left)
      | none => (qCursorSpend, none, .right) | s => (qReject, s, .stay)) ∧
    (∀ s, machine.step qCursorSpend s = match s with
      | some false => (qCursorSeekTerm, none, .right) | s => (qReject, s, .stay)) ∧
    (∀ s, machine.step qCursorSeekTerm s = match s with
      | some false => (qCursorSeekTerm, some false, .right)
      | some true => (qCursorRead, some true, .right) | none => (qReject, none, .stay)) ∧
    (∀ s, machine.step qCursorRead s = match s with
      | some false => (qRoundStart, none, .stay)
      | some true => (qCursorRestoreOne, some true, .left)
      | none => (qCursorRestoreVirtual, none, .left)) ∧
    (∀ s, machine.step qCursorRestoreOne s = match s with
      | none => (qCursorFillOne, some false, .left) | s => (qCursorRestoreOne, s, .left)) ∧
    (∀ s, machine.step qCursorRestoreVirtual s = match s with
      | none => (qCursorFillVirtual, some false, .left) | s => (qCursorRestoreVirtual, s, .left)) ∧
    (∀ s, machine.step qCursorFillOne s = match s with
      | none => (qHasOne, some false, .left) | s => (qReject, s, .stay)) ∧
    (∀ s, machine.step qCursorFillVirtual s = match s with
      | none => (qAllZero, some false, .left) | s => (qReject, s, .stay)) ∧
    (∀ s, machine.step qRoundStart s = match s with
      | none => (qRoundBackPayload, none, .left) | s => (qReject, s, .stay)) ∧
    (∀ s, machine.step qRoundBackPayload s = match s with
      | some false => (qRoundBackPayload, some false, .left)
      | some true => (qRoundBackCounter, some true, .left) | none => (qReject, none, .stay)) ∧
    (∀ s, machine.step qRoundBackCounter s = match s with
      | some false => (qRoundBackCounter, some false, .left)
      | none => (qRoundSpend, none, .right) | some true => (qReject, some true, .stay)) ∧
    (∀ s, machine.step qRoundSpend s = match s with
      | some false => (qRoundSeekTerm, none, .right)
      | some true => (qZeroScanRight, some true, .stay) | none => (qReject, none, .stay)) ∧
    (∀ s, machine.step qRoundSeekTerm s = match s with
      | some false => (qRoundSeekTerm, some false, .right)
      | some true => (qRoundSeekHole, some true, .right) | none => (qReject, none, .stay)) ∧
    (∀ s, machine.step qRoundSeekHole s = match s with
      | some false => (qRoundSeekHole, some false, .right)
      | none => (qRoundRead, some false, .right) | some true => (qReject, some true, .stay)) ∧
    (∀ s, machine.step qRoundRead s = match s with
      | some false => (qRoundStart, none, .stay)
      | some true => (qPendingStart, some true, .stay) | none => (qPendingStart, none, .stay)) ∧
    (∀ s, machine.step qZeroScanRight s = match s with
      | none => (qZeroBackTerm, some false, .left) | some b => (qZeroScanRight, some b, .right)) ∧
    (∀ s, machine.step qZeroBackTerm s = match s with
      | none => (qZeroFillCounter, some false, .left) | some b => (qZeroBackTerm, some b, .left)) ∧
    (∀ s, machine.step qZeroFillCounter s = match s with
      | none => (qZeroFillCounter, some false, .left)
      | some true => (qAllZero, some true, .stay) | some false => (qReject, some false, .stay)) ∧
    (∀ s, machine.step qPendingStart s = match s with
      | some true => (qPendingBackOne, some true, .left)
      | none => (qPendingBackVirtual, none, .left) | some false => (qReject, some false, .stay)) ∧
    (∀ s, machine.step qPendingBackOne s = match s with
      | none => (qPendingFillOne, some false, .left) | some b => (qPendingBackOne, some b, .left)) ∧
    (∀ s, machine.step qPendingBackVirtual s = match s with
      | none => (qPendingFillVirtual, some false, .left) | some b => (qPendingBackVirtual, some b, .left)) ∧
    (∀ s, machine.step qPendingFillOne s = match s with
      | none => (qPendingFillOne, some false, .left)
      | some true => (qHasOne, some true, .stay) | some false => (qReject, some false, .stay)) ∧
    (∀ s, machine.step qPendingFillVirtual s = match s with
      | none => (qPendingFillVirtual, some false, .left)
      | some true => (qAllZero, some true, .stay) | some false => (qReject, some false, .stay)) ∧
    (∀ s, machine.step qAllZero s = (qAllZero, s, .stay)) ∧
    (∀ s, machine.step qHasOne s = (qHasOne, s, .stay)) ∧
    (∀ s, machine.step qReject s = (qReject, s, .stay)) ∧
    machine.stateCount = 28 ∧ machine.start = qCursorStart ∧
    machine.accept = qAllZero ∧ machine.reject = qReject ∧
    qCursorStart.val = 0 ∧ qCursorBackFirst.val = 1 ∧ qCursorBackSeen.val = 2 ∧
    qCursorSpend.val = 3 ∧ qCursorSeekTerm.val = 4 ∧ qCursorRead.val = 5 ∧
    qCursorRestoreOne.val = 6 ∧ qCursorRestoreVirtual.val = 7 ∧
    qCursorFillOne.val = 8 ∧ qCursorFillVirtual.val = 9 ∧ qRoundStart.val = 10 ∧
    qRoundBackPayload.val = 11 ∧ qRoundBackCounter.val = 12 ∧ qRoundSpend.val = 13 ∧
    qRoundSeekTerm.val = 14 ∧ qRoundSeekHole.val = 15 ∧ qRoundRead.val = 16 ∧
    qZeroScanRight.val = 17 ∧ qZeroBackTerm.val = 18 ∧ qZeroFillCounter.val = 19 ∧
    qPendingStart.val = 20 ∧ qPendingBackOne.val = 21 ∧ qPendingBackVirtual.val = 22 ∧
    qPendingFillOne.val = 23 ∧ qPendingFillVirtual.val = 24 ∧
    qAllZero.val = 25 ∧ qHasOne.val = 26 ∧ qReject.val = 27 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 84 :=
  table_and_resource_pins

theorem check_handoff_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let p := FixedContentGammaAnchor.machine.run (FixedContentGammaAnchor.deadline a m)
      (FixedContentGammaAnchor.startConfig B x w)
    let c := startConfig B x w
    c = retagG2a p ∧ c.state = machine.start ∧ c.head = p.head ∧ c.tape = p.tape :=
  handoff_exact x w

theorem check_malformed_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none) :
    let d := machine.run 1 (startConfig B x w)
    d.state = qReject ∧ d.head.val = a + m ∧
      d.tape = FixedPairContentMarkerErase.contentTape B x w :=
  malformed_exact x w htag hg

theorem check_zero_width_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 0) :
    machine.run 2 (startConfig B x w) =
      ⟨qAllZero, ⟨7, by
        have hs := ((FixedContentGammaTerminator.gamma_contract _).1 0 hg).1
        unfold tapeLength pairLength
        omega⟩, FixedPairContentMarkerErase.contentTape B x w⟩ :=
  zero_width_exact x w htag hg

theorem check_first_true_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros) (hp : 9 + zeros < a + m)
    (htrue : (Fin.append x w) ⟨9 + zeros, hp⟩ = true) :
    machine.run (3 * zeros + 6) (startConfig B x w) =
      ⟨qHasOne, ⟨6, by unfold tapeLength pairLength; omega⟩,
        FixedPairContentMarkerErase.contentTape B x w⟩ :=
  first_true_exact x w htag hg hzero hp htrue

theorem check_first_virtual_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzero : 0 < zeros) (hvirtual : 9 + zeros = a + m) :
    machine.run (3 * zeros + 6) (startConfig B x w) =
      ⟨qAllZero, ⟨6, by unfold tapeLength pairLength; omega⟩,
        FixedPairContentMarkerErase.contentTape B x w⟩ :=
  first_virtual_exact x w htag hg hzero hvirtual

theorem check_endpoints_absorb {N B : Nat} (c : Config stateCount N B) :
    (c.state = qAllZero → ∀ n, machine.run n c = c) ∧
    (c.state = qHasOne → ∀ n, machine.run n c = c) ∧
    (c.state = qReject → ∀ n, machine.run n c = c) :=
  endpoints_absorb c

theorem check_per_step_budget_independent : ∀ q s, machine.step q s = machine.rawStep q s :=
  per_step_budget_independent

end Pnp3.Tests.UniformV1FixedGammaPayloadDispatcherSurfaceTests
