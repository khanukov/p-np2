import Complexity.Uniform.V1.FixedGammaTargetFirstPayload

namespace Pnp3.Tests.UniformV1FixedGammaTargetFirstPayloadSurfaceTests

open Complexity.Uniform.V1
open Complexity.Uniform.V1.PairEncoding
open Complexity.Uniform.V1.FixedGammaTargetFirstPayload

def check_stateCount : Nat := stateCount
def check_states : List (Fin stateCount) :=
  [qStart, qBack, qMarkSeven, qInspectEight, qSeekTerm, qReadPayload, qScanRight0, qScanRight1,
    qCrossScratch0, qCrossScratch1, qWrite0, qWrite1, qBackScratch, qCrossBoundary, qScanLeft,
    qSeekAnchor, qDone, qReject]
def check_raw :
    Fin stateCount → Option Bool → Fin stateCount × Option Bool × Move := raw
def check_machine : UniformTM := machine
def check_retagBootstrap {N B : Nat} :
    Config FixedGammaTerminatorScratchBootstrap.stateCount N B → Config stateCount N B :=
  retagBootstrap
def check_startConfig {a m : Nat} :
    (B : Nat) → Bitstring a → Bitstring m → Config stateCount (pairLength a m) B :=
  startConfig
def check_deadline (N : Nat) : Nat := deadline N
def check_firstPayloadTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m)
    (b : Bool) : Fin (tapeLength (pairLength a m) B) → Option Bool :=
  firstPayloadTape B x w b

theorem check_deadline_eq (N : Nat) : deadline N = 3 * N := rfl

theorem check_table_and_resource_pins :
    machine.step qStart none = (qReject, none, .stay) ∧
    machine.step qStart (some false) = (qReject, some false, .stay) ∧
    machine.step qStart (some true) = (qBack, none, .left) ∧
    machine.step qBack none = (qReject, none, .stay) ∧
    machine.step qBack (some false) = (qBack, some false, .left) ∧
    machine.step qBack (some true) = (qMarkSeven, some true, .right) ∧
    machine.step qMarkSeven none = (qReject, none, .stay) ∧
    machine.step qMarkSeven (some false) = (qInspectEight, none, .right) ∧
    machine.step qMarkSeven (some true) = (qReject, some true, .stay) ∧
    machine.step qInspectEight none = (qSeekAnchor, some true, .left) ∧
    machine.step qInspectEight (some false) = (qSeekTerm, some false, .right) ∧
    machine.step qInspectEight (some true) = (qReject, some true, .stay) ∧
    machine.step qSeekTerm none = (qReadPayload, none, .right) ∧
    machine.step qSeekTerm (some false) = (qSeekTerm, some false, .right) ∧
    machine.step qSeekTerm (some true) = (qReject, some true, .stay) ∧
    machine.step qReadPayload none = (qCrossScratch0, none, .right) ∧
    machine.step qReadPayload (some false) = (qScanRight0, some false, .right) ∧
    machine.step qReadPayload (some true) = (qScanRight1, some true, .right) ∧
    machine.step qScanRight0 none = (qCrossScratch0, none, .right) ∧
    machine.step qScanRight0 (some false) = (qScanRight0, some false, .right) ∧
    machine.step qScanRight0 (some true) = (qScanRight0, some true, .right) ∧
    machine.step qScanRight1 none = (qCrossScratch1, none, .right) ∧
    machine.step qScanRight1 (some false) = (qScanRight1, some false, .right) ∧
    machine.step qScanRight1 (some true) = (qScanRight1, some true, .right) ∧
    machine.step qCrossScratch0 none = (qReject, none, .stay) ∧
    machine.step qCrossScratch0 (some false) = (qReject, some false, .stay) ∧
    machine.step qCrossScratch0 (some true) = (qWrite0, some true, .right) ∧
    machine.step qCrossScratch1 none = (qReject, none, .stay) ∧
    machine.step qCrossScratch1 (some false) = (qReject, some false, .stay) ∧
    machine.step qCrossScratch1 (some true) = (qWrite1, some true, .right) ∧
    machine.step qWrite0 none = (qBackScratch, some false, .left) ∧
    machine.step qWrite0 (some false) = (qReject, some false, .stay) ∧
    machine.step qWrite0 (some true) = (qReject, some true, .stay) ∧
    machine.step qWrite1 none = (qBackScratch, some true, .left) ∧
    machine.step qWrite1 (some false) = (qReject, some false, .stay) ∧
    machine.step qWrite1 (some true) = (qReject, some true, .stay) ∧
    machine.step qBackScratch none = (qReject, none, .stay) ∧
    machine.step qBackScratch (some false) = (qReject, some false, .stay) ∧
    machine.step qBackScratch (some true) = (qCrossBoundary, some true, .left) ∧
    machine.step qCrossBoundary none = (qScanLeft, none, .left) ∧
    machine.step qCrossBoundary (some false) = (qReject, some false, .stay) ∧
    machine.step qCrossBoundary (some true) = (qReject, some true, .stay) ∧
    machine.step qScanLeft none = (qSeekAnchor, some true, .left) ∧
    machine.step qScanLeft (some false) = (qScanLeft, some false, .left) ∧
    machine.step qScanLeft (some true) = (qScanLeft, some true, .left) ∧
    machine.step qSeekAnchor none = (qDone, some false, .stay) ∧
    machine.step qSeekAnchor (some false) = (qSeekAnchor, some false, .left) ∧
    machine.step qSeekAnchor (some true) = (qReject, some true, .stay) ∧
    machine.step qDone none = (qDone, none, .stay) ∧
    machine.step qDone (some false) = (qDone, some false, .stay) ∧
    machine.step qDone (some true) = (qDone, some true, .stay) ∧
    machine.step qReject none = (qReject, none, .stay) ∧
    machine.step qReject (some false) = (qReject, some false, .stay) ∧
    machine.step qReject (some true) = (qReject, some true, .stay) ∧
    machine.stateCount = 18 ∧ machine.start = qStart ∧
    machine.accept = qDone ∧ machine.reject = qReject ∧
    qStart.val = 0 ∧ qBack.val = 1 ∧ qMarkSeven.val = 2 ∧ qInspectEight.val = 3 ∧
    qSeekTerm.val = 4 ∧ qReadPayload.val = 5 ∧ qScanRight0.val = 6 ∧
    qScanRight1.val = 7 ∧ qCrossScratch0.val = 8 ∧ qCrossScratch1.val = 9 ∧
    qWrite0.val = 10 ∧ qWrite1.val = 11 ∧ qBackScratch.val = 12 ∧
    qCrossBoundary.val = 13 ∧ qScanLeft.val = 14 ∧ qSeekAnchor.val = 15 ∧
    qDone.val = 16 ∧ qReject.val = 17 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 54 :=
  table_and_resource_pins

theorem check_per_step_budget_independent :
    ∀ q s, machine.step q s = machine.rawStep q s :=
  per_step_budget_independent

theorem check_endpoints_absorb {N B : Nat} (c : Config stateCount N B) :
    (c.state = qDone → ∀ n, machine.run n c = c) ∧
    (c.state = qReject → ∀ n, machine.run n c = c) :=
  endpoints_absorb c

theorem check_handoff_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let p := FixedGammaTerminatorScratchBootstrap.machine.run
      (FixedGammaTerminatorScratchBootstrap.deadline (a + m))
      (FixedGammaTerminatorScratchBootstrap.startConfig B x w)
    let c := startConfig B x w
    c = retagBootstrap p ∧ c.state = machine.start ∧ c.head = p.head ∧
      c.tape = p.tape :=
  handoff_exact x w

theorem check_firstPayloadTape_layout {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (b : Bool) (hroom : a + m + 2 < tapeLength (pairLength a m) B) :
    (∀ j : Fin (a + m), firstPayloadTape B x w b
      ⟨j.val, by unfold tapeLength pairLength; omega⟩ = some (Fin.append x w j)) ∧
    firstPayloadTape B x w b ⟨a + m, by unfold tapeLength pairLength; omega⟩ = none ∧
    firstPayloadTape B x w b ⟨a + m + 1, by unfold tapeLength pairLength; omega⟩ =
      some true ∧
    firstPayloadTape B x w b ⟨a + m + 2, hroom⟩ = some b ∧
    ∀ i : Fin (tapeLength (pairLength a m) B), a + m + 2 < i.val →
      firstPayloadTape B x w b i = none :=
  firstPayloadTape_layout x w b hroom

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
    d.state = qDone ∧ d.head.val = 7 ∧
      d.tape = FixedGammaTerminatorScratchBootstrap.scratchTape B x w :=
  zero_width_at_deadline x w htag hg

theorem check_first_payload_at_deadline {a m B zeros : Nat} (x : Bitstring a)
    (w : Bitstring m) (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 0 < zeros) (hroom : a + m + 2 < tapeLength (pairLength a m) B) :
    let d := machine.run (deadline (a + m)) (startConfig B x w)
    d.state = qDone ∧ d.head.val = 7 ∧
      d.tape = firstPayloadTape B x w
        ((FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros)).getD false) :=
  first_payload_at_deadline x w htag hg hzeros hroom

theorem check_first_physical_at_deadline {a m B zeros : Nat} (x : Bitstring a)
    (w : Bitstring m) (b : Bool)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 0 < zeros)
    (hread : FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros) = some b)
    (hroom : a + m + 2 < tapeLength (pairLength a m) B) :
    let d := machine.run (deadline (a + m)) (startConfig B x w)
    d.state = qDone ∧ d.head.val = 7 ∧ d.tape = firstPayloadTape B x w b :=
  first_physical_at_deadline x w b htag hg hzeros hread hroom

theorem check_first_virtual_at_deadline {a m B zeros : Nat} (x : Bitstring a)
    (w : Bitstring m) (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 0 < zeros) (hvirtual : 9 + zeros = a + m)
    (hroom : a + m + 2 < tapeLength (pairLength a m) B) :
    let d := machine.run (deadline (a + m)) (startConfig B x w)
    d.state = qDone ∧ d.head.val = 7 ∧ d.tape = firstPayloadTape B x w false :=
  first_virtual_at_deadline x w htag hg hzeros hvirtual hroom

theorem check_no_boundary_clamp {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hroom : ∀ zeros, FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros →
      0 < zeros → a + m + 2 < tapeLength (pairLength a m) B) (s : Nat) :
    let c := machine.run s (startConfig B x w)
    let move := (machine.step c.state (c.tape c.head)).2.2
    (move = .right → c.head.val + 1 < tapeLength (pairLength a m) B) ∧
    (move = .left → 0 < c.head.val) :=
  no_boundary_clamp x w htag hroom s

theorem check_footprint {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hroom : 0 < zeros → a + m + 2 < tapeLength (pairLength a m) B) (s : Nat) :
    let d := machine.run s (startConfig B x w)
    6 ≤ d.head.val ∧ d.head.val ≤ (if zeros = 0 then 8 else a + m + 2) ∧
      ∀ i : Fin (tapeLength (pairLength a m) B), i.val ≠ 7 → i.val ≠ 8 + zeros →
        i.val ≠ a + m + 1 → i.val ≠ a + m + 2 →
          d.tape i = FixedPairContentMarkerErase.contentTape B x w i :=
  footprint x w htag hg hroom s

theorem check_budget_independence {a m : Nat} (B B' : Nat) (x : Bitstring a)
    (w : Bitstring m) (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hroom : ∀ zeros, FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros →
      0 < zeros → a + m + 2 < tapeLength (pairLength a m) B ∧
        a + m + 2 < tapeLength (pairLength a m) B') (s : Nat) :
    (machine.run s (startConfig B x w)).state =
        (machine.run s (startConfig B' x w)).state ∧
    (machine.run s (startConfig B x w)).head.val =
        (machine.run s (startConfig B' x w)).head.val ∧
    ∀ (i : Fin (tapeLength (pairLength a m) B))
        (i' : Fin (tapeLength (pairLength a m) B')),
      i.val = i'.val →
      (machine.run s (startConfig B x w)).tape i =
        (machine.run s (startConfig B' x w)).tape i' :=
  budget_independence B B' x w htag hroom s

/-! Concrete regressions after the tag `10110010`, derived for every budget from the
public theorems; `decide` evaluates only the tag, gamma, and physical-cell facts.
The words are malformed, width zero, width one with physical payload bit `1`,
width one with physical payload bit `0`, and width two whose payload cell is the
boundary `N = 11` (virtual zero).  With `a = 8` every budget allocates the target
cell `N + 2`. -/

private def tag : Bitstring 8 := ![true, false, true, true, false, false, true, false]
private def malformed : Bitstring 3 := ![false, false, false]
private def widthZero : Bitstring 1 := ![true]
private def physicalOne : Bitstring 3 := ![false, true, true]
private def physicalZero : Bitstring 3 := ![false, true, false]
private def virtualZero : Bitstring 3 := ![false, false, true]

example (B : Nat) :
    (machine.run (deadline (8 + 3)) (startConfig B tag malformed)).state = qReject := by
  have h := malformed_at_deadline (B := B) tag malformed (by decide) (by decide)
  exact h.1

example (B : Nat) :
    let d := machine.run (deadline (8 + 1)) (startConfig B tag widthZero)
    d.state = qDone ∧ d.head.val = 7 ∧
      d.tape = FixedGammaTerminatorScratchBootstrap.scratchTape B tag widthZero := by
  have h := zero_width_at_deadline (B := B) tag widthZero (by decide) (by decide)
  exact h

example (B : Nat) :
    let d := machine.run (deadline (8 + 3)) (startConfig B tag physicalOne)
    d.state = qDone ∧ d.head.val = 7 ∧ d.tape = firstPayloadTape B tag physicalOne true := by
  have h := first_physical_at_deadline (B := B) (zeros := 1) tag physicalOne true
    (by decide) (by decide) (by decide) (by decide) (by unfold tapeLength pairLength; omega)
  exact h

example (B : Nat) :
    let d := machine.run (deadline (8 + 3)) (startConfig B tag physicalZero)
    d.state = qDone ∧ d.head.val = 7 ∧ d.tape = firstPayloadTape B tag physicalZero false := by
  have h := first_physical_at_deadline (B := B) (zeros := 1) tag physicalZero false
    (by decide) (by decide) (by decide) (by decide) (by unfold tapeLength pairLength; omega)
  exact h

example (B : Nat) :
    let d := machine.run (deadline (8 + 3)) (startConfig B tag virtualZero)
    d.state = qDone ∧ d.head.val = 7 ∧ d.tape = firstPayloadTape B tag virtualZero false := by
  have h := first_virtual_at_deadline (B := B) (zeros := 2) tag virtualZero
    (by decide) (by decide) (by decide) rfl (by unfold tapeLength pairLength; omega)
  exact h

end Pnp3.Tests.UniformV1FixedGammaTargetFirstPayloadSurfaceTests
