import Complexity.Uniform.V1.FixedGammaTargetFirstPayload
import Complexity.Uniform.V1.SequentialComposition

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
def check_exactClock (N zeros : Nat) : Nat := exactClock N zeros
def check_malformedExactClock : Nat := malformedExactClock
def check_firstPayloadTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m)
    (b : Bool) : Fin (tapeLength (pairLength a m) B) → Option Bool :=
  firstPayloadTape B x w b

theorem check_deadline_eq (N : Nat) : deadline N = 3 * N := rfl

theorem check_exactClock_eq (N zeros : Nat) :
    exactClock N zeros = if zeros = 0 then 6 else 2 * N + zeros - 6 := rfl

theorem check_malformedExactClock_eq : malformedExactClock = 1 := rfl

theorem check_exactClock_pins :
    (∀ N, exactClock N 0 = 6) ∧
      (∀ N zeros, 0 < zeros → exactClock N zeros = 2 * N + zeros - 6) ∧
      malformedExactClock = 1 :=
  exactClock_pins

theorem check_exactClock_add {N zeros : Nat} (hN : 9 + zeros ≤ N) (hz : 0 < zeros) :
    exactClock N zeros + 6 = 2 * N + zeros :=
  exactClock_add hN hz

theorem check_exactClock_le_deadline {N zeros : Nat} (hN : 9 + zeros ≤ N) :
    exactClock N zeros ≤ deadline N :=
  exactClock_le_deadline hN

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

theorem check_malformed_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none)
    (s : Nat) (hs : malformedExactClock ≤ s) :
    let d := machine.run s (startConfig B x w)
    d.state = qReject ∧ d.head.val = a + m ∧
      d.tape = FixedPairContentMarkerErase.contentTape B x w :=
  malformed_exact x w htag hg s hs

theorem check_malformed_strict {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none)
    (s : Nat) (hs : s < malformedExactClock) :
    let d := machine.run s (startConfig B x w)
    d.state ≠ qDone ∧ d.state ≠ qReject :=
  malformed_strict x w htag hg s hs

theorem check_zero_width_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 0)
    (s : Nat) (hs : exactClock (a + m) 0 ≤ s) :
    let d := machine.run s (startConfig B x w)
    d.state = qDone ∧ d.head.val = 7 ∧
      d.tape = FixedGammaTerminatorScratchBootstrap.scratchTape B x w :=
  zero_width_exact x w htag hg s hs

theorem check_zero_width_strict {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some 0)
    (s : Nat) (hs : s < exactClock (a + m) 0) :
    let d := machine.run s (startConfig B x w)
    d.state ≠ qDone ∧ d.state ≠ qReject :=
  zero_width_strict x w htag hg s hs

theorem check_first_payload_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 0 < zeros) (hroom : a + m + 2 < tapeLength (pairLength a m) B)
    (s : Nat) (hs : exactClock (a + m) zeros ≤ s) :
    let d := machine.run s (startConfig B x w)
    d.state = qDone ∧ d.head.val = 7 ∧
      d.tape = firstPayloadTape B x w
        ((FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros)).getD false) :=
  first_payload_exact x w htag hg hzeros hroom s hs

theorem check_first_payload_strict {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 0 < zeros) (hroom : a + m + 2 < tapeLength (pairLength a m) B)
    (s : Nat) (hs : s < exactClock (a + m) zeros) :
    let d := machine.run s (startConfig B x w)
    d.state ≠ qDone ∧ d.state ≠ qReject :=
  first_payload_strict x w htag hg hzeros hroom s hs

theorem check_first_physical_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (b : Bool) (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 0 < zeros)
    (hread : FixedContentTagGate.physicalSymbol (Fin.append x w) (9 + zeros) = some b)
    (hroom : a + m + 2 < tapeLength (pairLength a m) B)
    (s : Nat) (hs : exactClock (a + m) zeros ≤ s) :
    let d := machine.run s (startConfig B x w)
    d.state = qDone ∧ d.head.val = 7 ∧ d.tape = firstPayloadTape B x w b :=
  first_physical_exact x w b htag hg hzeros hread hroom s hs

theorem check_first_virtual_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hzeros : 0 < zeros) (hvirtual : 9 + zeros = a + m)
    (hroom : a + m + 2 < tapeLength (pairLength a m) B)
    (s : Nat) (hs : exactClock (a + m) zeros ≤ s) :
    let d := machine.run s (startConfig B x w)
    d.state = qDone ∧ d.head.val = 7 ∧ d.tape = firstPayloadTape B x w false :=
  first_virtual_exact x w htag hg hzeros hvirtual hroom s hs

theorem check_strict_first_terminal {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (hroom : 0 < zeros → a + m + 2 < tapeLength (pairLength a m) B) :
    (∀ s, s < exactClock (a + m) zeros →
        (machine.run s (startConfig B x w)).state ≠ machine.accept ∧
        (machine.run s (startConfig B x w)).state ≠ machine.reject) ∧
      (machine.run (exactClock (a + m) zeros) (startConfig B x w)).state = machine.accept ∧
      exactClock (a + m) zeros ≤ deadline (a + m) ∧
      machine.run (exactClock (a + m) zeros) (startConfig B x w) =
        machine.run (deadline (a + m)) (startConfig B x w) :=
  strict_first_terminal x w htag hg hroom

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
boundary `N = 11` (virtual zero); the probe section below adds a width-three word
with a physical payload cell.  With `a = 8` every budget allocates the target
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

/-! ### Independent reduction probes at the exact first arrival

Everything above is a restatement: it executes nothing.  The probes below do.
Each one first identifies the *actual* `startConfig B tag ·` — which is the
retagged G2p-a bootstrap endpoint, not a hand-written configuration — with an
explicit configuration for every budget, using only G2p-a's landed
`run_deadline` / `malformed_at_deadline`, themselves free of any execution here;
it then reduces this phase's own run at `B = 0` by kernel computation, at the
exact clock and one step before it.  No probe appeals to the clock theorems it
is checking, so each is an independent witness that `exactClock` and
`malformedExactClock` are the *first* terminal times and not merely upper
bounds.

The reachable shapes of a decoded width are covered: a positive width whose
payload cell `9 + zeros` is physical, with each bit value and with `zeros = 1`
and `zeros = 3`; a positive width whose payload cell is the blank boundary
(`9 + zeros = a + m`, the largest width a run of this length can decode); width
zero, at its own extreme `9 = a + m`; and a malformed gamma.  A positive width
with `9 + zeros > a + m` is not reachable: the gamma contract forces
`9 + zeros ≤ a + m`. -/

private def wideWord : Bitstring 5 := ![false, false, false, true, true]

/-- Rebuild a configuration from its projections, over a configuration
*variable*, so that identifying the phase-local start configuration never has to
reduce the G2p-a run term inside it. -/
private theorem config_of_parts {K n B : Nat} {c : Config K n B} {q : Fin K} {k : Nat}
    {hk : k < tapeLength n B} {T : Fin (tapeLength n B) → Option Bool}
    (hq : c.state = q) (hh : c.head.val = k) (ht : c.tape = T) : c = ⟨q, ⟨k, hk⟩, T⟩ :=
  Config.ext_parts hq (Fin.ext hh) ht

private theorem physicalOne_start (B : Nat) :
    startConfig B tag physicalOne =
      ⟨qStart, ⟨8 + 1, by unfold tapeLength pairLength; omega⟩,
        FixedGammaTerminatorScratchBootstrap.scratchTape B tag physicalOne⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTerminatorScratchBootstrap.run_deadline
    (B := B) (zeros := 1) tag physicalOne (by decide) (by decide)
  config_of_parts rfl hh ht

private theorem physicalZero_start (B : Nat) :
    startConfig B tag physicalZero =
      ⟨qStart, ⟨8 + 1, by unfold tapeLength pairLength; omega⟩,
        FixedGammaTerminatorScratchBootstrap.scratchTape B tag physicalZero⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTerminatorScratchBootstrap.run_deadline
    (B := B) (zeros := 1) tag physicalZero (by decide) (by decide)
  config_of_parts rfl hh ht

private theorem virtualZero_start (B : Nat) :
    startConfig B tag virtualZero =
      ⟨qStart, ⟨8 + 2, by unfold tapeLength pairLength; omega⟩,
        FixedGammaTerminatorScratchBootstrap.scratchTape B tag virtualZero⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTerminatorScratchBootstrap.run_deadline
    (B := B) (zeros := 2) tag virtualZero (by decide) (by decide)
  config_of_parts rfl hh ht

private theorem wideWord_start (B : Nat) :
    startConfig B tag wideWord =
      ⟨qStart, ⟨8 + 3, by unfold tapeLength pairLength; omega⟩,
        FixedGammaTerminatorScratchBootstrap.scratchTape B tag wideWord⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTerminatorScratchBootstrap.run_deadline
    (B := B) (zeros := 3) tag wideWord (by decide) (by decide)
  config_of_parts rfl hh ht

private theorem widthZero_start (B : Nat) :
    startConfig B tag widthZero =
      ⟨qStart, ⟨8 + 0, by unfold tapeLength pairLength; omega⟩,
        FixedGammaTerminatorScratchBootstrap.scratchTape B tag widthZero⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTerminatorScratchBootstrap.run_deadline
    (B := B) (zeros := 0) tag widthZero (by decide) (by decide)
  config_of_parts rfl hh ht

private theorem malformed_start (B : Nat) :
    startConfig B tag malformed =
      ⟨qStart, ⟨8 + 3, by unfold tapeLength pairLength; omega⟩,
        FixedPairContentMarkerErase.contentTape B tag malformed⟩ :=
  let ⟨_, hh, ht⟩ := FixedGammaTerminatorScratchBootstrap.malformed_at_deadline
    (B := B) tag malformed (by decide) (by decide)
  config_of_parts rfl hh ht

set_option maxRecDepth 100000 in
/-- **Width one with a physical payload bit `1`, reduced.**  `N = 11`,
`zeros = 1`, source cell `9 + 1 = 10 < 11`, target cell `N + 2 = 13`, and
`exactClock 11 1 = 2 * 11 + 1 - 6 = 17`.  At step `16` the control is
`qSeekAnchor` (index `15`) at head `7` on the still-blanked anchor, which is
neither verdict; at step `17` it is `qDone` at head `7`, with the copied `true`
at `13`, the bootstrap register `true` still at `12`, the anchor restored to
`some false` at `7` and the terminator restored to `some true` at `9`.  Those
last two cells are the ones this run blanks in flight; the endpoint theorem says
the same thing about every cell at once. -/
theorem check_arrival_probe_physical_one :
    exactClock (8 + 3) 1 = 17 ∧
    (machine.run 16 (startConfig 0 tag physicalOne)).state.val = 15 ∧
    (machine.run 16 (startConfig 0 tag physicalOne)).head.val = 7 ∧
    (machine.run 16 (startConfig 0 tag physicalOne)).tape ⟨7, by decide⟩ = none ∧
    (machine.run 16 (startConfig 0 tag physicalOne)).state ≠ qDone ∧
    (machine.run 16 (startConfig 0 tag physicalOne)).state ≠ qReject ∧
    (machine.run 17 (startConfig 0 tag physicalOne)).state = qDone ∧
    (machine.run 17 (startConfig 0 tag physicalOne)).head.val = 7 ∧
    (machine.run 17 (startConfig 0 tag physicalOne)).tape ⟨13, by decide⟩ = some true ∧
    (machine.run 17 (startConfig 0 tag physicalOne)).tape ⟨12, by decide⟩ = some true ∧
    (machine.run 17 (startConfig 0 tag physicalOne)).tape ⟨7, by decide⟩ = some false ∧
    (machine.run 17 (startConfig 0 tag physicalOne)).tape ⟨9, by decide⟩ = some true := by
  rw [physicalOne_start 0]
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 100000 in
/-- **The same width with a physical payload bit `0`, reduced.**  The same word
length and width as the probe above, so the same clock `17` and the same head
`7`, but `false` at the target cell `13`: across the two probes the carried value
tracks the source cell rather than being a constant. -/
theorem check_arrival_probe_physical_zero :
    (machine.run 16 (startConfig 0 tag physicalZero)).state ≠ qDone ∧
    (machine.run 16 (startConfig 0 tag physicalZero)).state ≠ qReject ∧
    (machine.run 17 (startConfig 0 tag physicalZero)).state = qDone ∧
    (machine.run 17 (startConfig 0 tag physicalZero)).head.val = 7 ∧
    (machine.run 17 (startConfig 0 tag physicalZero)).tape ⟨13, by decide⟩ = some false ∧
    (machine.run 17 (startConfig 0 tag physicalZero)).tape ⟨12, by decide⟩ = some true := by
  rw [physicalZero_start 0]
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 100000 in
/-- **The virtual source shape, reduced.**  `N = 11`, `zeros = 2`, so the source
address `9 + 2` *is* the blank boundary `11` and the clock is
`exactClock 11 2 = 18`, one step later than the width-one probe above at the same
length.  At step `17` the control is in neither verdict; at step `18` it is
`qDone` at head `7` with the virtual `false` at the target cell `13`, while the
register `true` at `12` — the last cell the head crosses before the target — is
still `some true`, so it was not consumed as the source, and the terminator is
back at `10`. -/
theorem check_arrival_probe_virtual :
    exactClock (8 + 3) 2 = 18 ∧
    (machine.run 17 (startConfig 0 tag virtualZero)).state ≠ qDone ∧
    (machine.run 17 (startConfig 0 tag virtualZero)).state ≠ qReject ∧
    (machine.run 18 (startConfig 0 tag virtualZero)).state = qDone ∧
    (machine.run 18 (startConfig 0 tag virtualZero)).head.val = 7 ∧
    (machine.run 18 (startConfig 0 tag virtualZero)).tape ⟨13, by decide⟩ = some false ∧
    (machine.run 18 (startConfig 0 tag virtualZero)).tape ⟨12, by decide⟩ = some true ∧
    (machine.run 18 (startConfig 0 tag virtualZero)).tape ⟨10, by decide⟩ = some true := by
  rw [virtualZero_start 0]
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 100000 in
/-- **A wider gamma block, reduced.**  `N = 13`, `zeros = 3`: the source cell is
`9 + 3 = 12 < 13`, the target cell is `15`, the terminator is at `8 + 3 = 11`,
and `exactClock 13 3 = 2 * 13 + 3 - 6 = 23`.  The three probed positive widths
now read `17` at `(11, 1)`, `18` at `(11, 2)` and `23` at `(13, 3)`: the first
pair moves the width alone, and this probe moves the length as well, so neither
term of the clock is idle. -/
theorem check_arrival_probe_wide :
    exactClock (8 + 5) 3 = 23 ∧
    (machine.run 22 (startConfig 0 tag wideWord)).state ≠ qDone ∧
    (machine.run 22 (startConfig 0 tag wideWord)).state ≠ qReject ∧
    (machine.run 23 (startConfig 0 tag wideWord)).state = qDone ∧
    (machine.run 23 (startConfig 0 tag wideWord)).head.val = 7 ∧
    (machine.run 23 (startConfig 0 tag wideWord)).tape ⟨15, by decide⟩ = some true ∧
    (machine.run 23 (startConfig 0 tag wideWord)).tape ⟨14, by decide⟩ = some true ∧
    (machine.run 23 (startConfig 0 tag wideWord)).tape ⟨11, by decide⟩ = some true ∧
    (machine.run 23 (startConfig 0 tag wideWord)).tape ⟨7, by decide⟩ = some false := by
  rw [wideWord_start 0]
  repeat' apply And.intro
  all_goals decide

set_option maxRecDepth 100000 in
/-- **The two shapes outside the positive-width branch, reduced.**  Width zero
(`N = 9`, its own extreme `9 + 0 = a + m`) is in neither verdict at step `5` and
halts at `exactClock 9 0 = 6` at head `7`, leaving the target cell `11` blank —
the cell a positive width would have written — with the bootstrap register
`true` it was handed still at `10`.  A malformed gamma is in neither verdict at
step `0`, the handed-over configuration itself, is in `qReject` at
`malformedExactClock = 1` at the boundary head `11`, and is still there at step
`5`. -/
theorem check_arrival_probe_degenerate :
    exactClock (8 + 1) 0 = 6 ∧ malformedExactClock = 1 ∧
    (machine.run 5 (startConfig 0 tag widthZero)).state ≠ qDone ∧
    (machine.run 5 (startConfig 0 tag widthZero)).state ≠ qReject ∧
    (machine.run 6 (startConfig 0 tag widthZero)).state = qDone ∧
    (machine.run 6 (startConfig 0 tag widthZero)).head.val = 7 ∧
    (machine.run 6 (startConfig 0 tag widthZero)).tape ⟨11, by decide⟩ = none ∧
    (machine.run 6 (startConfig 0 tag widthZero)).tape ⟨10, by decide⟩ = some true ∧
    (machine.run 0 (startConfig 0 tag malformed)).state ≠ qDone ∧
    (machine.run 0 (startConfig 0 tag malformed)).state ≠ qReject ∧
    (machine.run 1 (startConfig 0 tag malformed)).state = qReject ∧
    (machine.run 1 (startConfig 0 tag malformed)).head.val = 11 ∧
    (machine.run 5 (startConfig 0 tag malformed)).state = qReject := by
  rw [widthZero_start 0, malformed_start 0]
  repeat' apply And.intro
  all_goals decide

end Pnp3.Tests.UniformV1FixedGammaTargetFirstPayloadSurfaceTests
