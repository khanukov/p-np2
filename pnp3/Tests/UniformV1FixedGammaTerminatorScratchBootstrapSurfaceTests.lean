import Complexity.Uniform.V1.FixedGammaTerminatorScratchBootstrap

namespace Pnp3.Tests.UniformV1FixedGammaTerminatorScratchBootstrapSurfaceTests

open Complexity.Uniform.V1
open Complexity.Uniform.V1.PairEncoding
open Complexity.Uniform.V1.FixedGammaTerminatorScratchBootstrap

def check_stateCount : Nat := stateCount
def check_qStart : Fin stateCount := qStart
def check_qNormalize : Fin stateCount := qNormalize
def check_qSeekTerm : Fin stateCount := qSeekTerm
def check_qScanRight : Fin stateCount := qScanRight
def check_qWriteScratch : Fin stateCount := qWriteScratch
def check_qCrossBoundary : Fin stateCount := qCrossBoundary
def check_qScanLeft : Fin stateCount := qScanLeft
def check_qTerm : Fin stateCount := qTerm
def check_qReject : Fin stateCount := qReject
def check_raw :
    Fin stateCount → Option Bool → Fin stateCount × Option Bool × Move := raw
def check_machine : UniformTM := machine
def check_retagDispatcher {N B : Nat} :
    Config FixedGammaPayloadDispatcher.stateCount N B → Config stateCount N B :=
  retagDispatcher
def check_startConfig {a m : Nat} :
    (B : Nat) → Bitstring a → Bitstring m → Config stateCount (pairLength a m) B :=
  startConfig
def check_exactClock (N zeros : Nat) : Nat := exactClock N zeros
def check_deadline (N : Nat) : Nat := deadline N
def check_markedTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m)
    (zeros : Nat) : Fin (tapeLength (pairLength a m) B) → Option Bool :=
  markedTape B x w zeros
def check_scratchMarkedTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m)
    (zeros : Nat) : Fin (tapeLength (pairLength a m) B) → Option Bool :=
  scratchMarkedTape B x w zeros
def check_scratchTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Fin (tapeLength (pairLength a m) B) → Option Bool :=
  scratchTape B x w
def check_traceState (N zeros s : Nat) : Fin stateCount := traceState N zeros s
def check_traceHead (N zeros s : Nat) : Nat := traceHead N zeros s
def check_traceTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m)
    (zeros s : Nat) : Fin (tapeLength (pairLength a m) B) → Option Bool :=
  traceTape B x w zeros s

theorem check_table_and_resource_pins :
    machine.step qStart none = (qReject, none, .stay) ∧
    machine.step qStart (some false) = (qNormalize, some false, .stay) ∧
    machine.step qStart (some true) = (qNormalize, some true, .right) ∧
    machine.step qNormalize none = (qReject, none, .stay) ∧
    machine.step qNormalize (some false) = (qSeekTerm, some false, .right) ∧
    machine.step qNormalize (some true) = (qReject, some true, .stay) ∧
    machine.step qSeekTerm none = (qReject, none, .stay) ∧
    machine.step qSeekTerm (some false) = (qSeekTerm, some false, .right) ∧
    machine.step qSeekTerm (some true) = (qScanRight, none, .right) ∧
    machine.step qScanRight none = (qWriteScratch, none, .right) ∧
    machine.step qScanRight (some false) = (qScanRight, some false, .right) ∧
    machine.step qScanRight (some true) = (qScanRight, some true, .right) ∧
    machine.step qWriteScratch none = (qCrossBoundary, some true, .left) ∧
    machine.step qWriteScratch (some false) = (qReject, some false, .stay) ∧
    machine.step qWriteScratch (some true) = (qReject, some true, .stay) ∧
    machine.step qCrossBoundary none = (qScanLeft, none, .left) ∧
    machine.step qCrossBoundary (some false) = (qReject, some false, .stay) ∧
    machine.step qCrossBoundary (some true) = (qReject, some true, .stay) ∧
    machine.step qScanLeft none = (qTerm, some true, .stay) ∧
    machine.step qScanLeft (some false) = (qScanLeft, some false, .left) ∧
    machine.step qScanLeft (some true) = (qScanLeft, some true, .left) ∧
    machine.step qTerm none = (qTerm, none, .stay) ∧
    machine.step qTerm (some false) = (qTerm, some false, .stay) ∧
    machine.step qTerm (some true) = (qTerm, some true, .stay) ∧
    machine.step qReject none = (qReject, none, .stay) ∧
    machine.step qReject (some false) = (qReject, some false, .stay) ∧
    machine.step qReject (some true) = (qReject, some true, .stay) ∧
    machine.stateCount = 9 ∧ machine.start = qStart ∧
    machine.accept = qTerm ∧ machine.reject = qReject ∧
    qStart.val = 0 ∧ qNormalize.val = 1 ∧ qSeekTerm.val = 2 ∧ qScanRight.val = 3 ∧
    qWriteScratch.val = 4 ∧ qCrossBoundary.val = 5 ∧ qScanLeft.val = 6 ∧
    qTerm.val = 7 ∧ qReject.val = 8 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 27 :=
  table_and_resource_pins

theorem check_per_step_budget_independent :
    ∀ q s, machine.step q s = machine.rawStep q s :=
  per_step_budget_independent

theorem check_endpoints_absorb {N B : Nat} (c : Config stateCount N B) :
    (c.state = qTerm → ∀ n, machine.run n c = c) ∧
    (c.state = qReject → ∀ n, machine.run n c = c) :=
  endpoints_absorb c

theorem check_handoff_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    let p := FixedGammaPayloadDispatcher.machine.run
      (FixedGammaPayloadDispatcherDeadline.deadline (a + m))
      (FixedGammaPayloadDispatcher.startConfig B x w)
    let c := startConfig B x w
    c = retagDispatcher p ∧ c.state = machine.start ∧ c.head = p.head ∧
      c.tape = p.tape :=
  handoff_exact x w

theorem check_exactClock_add {N zeros : Nat} (hN : 9 + zeros ≤ N) :
    exactClock N zeros + zeros + 11 = 2 * N :=
  exactClock_add hN

theorem check_exactClock_le_deadline (N zeros : Nat) :
    exactClock N zeros ≤ deadline N :=
  exactClock_le_deadline N zeros

theorem check_marker_unique {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (i : Fin (tapeLength (pairLength a m) B)) :
    markedTape B x w zeros i = none ↔ i.val = 8 + zeros ∨ a + m ≤ i.val :=
  marker_unique x w i

theorem check_scratchTape_layout {a m B : Nat} (x : Bitstring a) (w : Bitstring m) :
    (∀ j : Fin (a + m), scratchTape B x w
      ⟨j.val, by unfold tapeLength pairLength; omega⟩ = some (Fin.append x w j)) ∧
    scratchTape B x w ⟨a + m, by unfold tapeLength pairLength; omega⟩ = none ∧
    scratchTape B x w ⟨a + m + 1, by unfold tapeLength pairLength; omega⟩ = some true ∧
    ∀ i : Fin (tapeLength (pairLength a m) B), a + m + 1 < i.val →
      scratchTape B x w i = none :=
  scratchTape_layout x w

theorem check_run_trace {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (s : Nat) :
    let d := machine.run s (startConfig B x w)
    d.state = traceState (a + m) zeros s ∧ d.head.val = traceHead (a + m) zeros s ∧
      d.tape = traceTape B x w zeros s :=
  run_trace x w htag hg s

theorem check_post_clock_absorption {a m B zeros : Nat} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (s : Nat) (hs : exactClock (a + m) zeros ≤ s) :
    let d := machine.run s (startConfig B x w)
    d.state = qTerm ∧ d.head.val = 8 + zeros ∧ d.tape = scratchTape B x w :=
  post_clock_absorption x w htag hg s hs

theorem check_run_exact {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    let d := machine.run (exactClock (a + m) zeros) (startConfig B x w)
    d.state = qTerm ∧ d.head.val = 8 + zeros ∧ d.tape = scratchTape B x w :=
  run_exact x w htag hg

theorem check_run_deadline {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    let d := machine.run (deadline (a + m)) (startConfig B x w)
    d.state = qTerm ∧ d.head.val = 8 + zeros ∧ d.tape = scratchTape B x w :=
  run_deadline x w htag hg

theorem check_strict_first_terminal {a m B zeros : Nat} (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    (∀ s, s < exactClock (a + m) zeros →
      (machine.run s (startConfig B x w)).state ≠ qTerm ∧
      (machine.run s (startConfig B x w)).state ≠ qReject) ∧
    (machine.run (exactClock (a + m) zeros) (startConfig B x w)).state = qTerm :=
  strict_first_terminal x w htag hg

theorem check_no_boundary_clamp {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) (s : Nat) :
    let c := machine.run s (startConfig B x w)
    let move := (machine.step c.state (c.tape c.head)).2.2
    (move = .right → c.head.val + 1 < tapeLength (pairLength a m) B) ∧
    (move = .left → 0 < c.head.val) :=
  no_boundary_clamp x w htag s

theorem check_footprint {a m B zeros : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros)
    (s : Nat) :
    let d := machine.run s (startConfig B x w)
    6 ≤ d.head.val ∧ d.head.val ≤ a + m + 1 ∧
      ∀ i : Fin (tapeLength (pairLength a m) B), i.val ≠ 8 + zeros →
        i.val ≠ a + m + 1 → d.tape i = FixedPairContentMarkerErase.contentTape B x w i :=
  footprint x w htag hg s

theorem check_budget_independence {a m : Nat} (B B' : Nat) (x : Bitstring a)
    (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) (s : Nat) :
    (machine.run s (startConfig B x w)).state =
        (machine.run s (startConfig B' x w)).state ∧
    (machine.run s (startConfig B x w)).head.val =
        (machine.run s (startConfig B' x w)).head.val ∧
    ∀ (i : Fin (tapeLength (pairLength a m) B))
        (i' : Fin (tapeLength (pairLength a m) B')),
      i.val = i'.val →
      (machine.run s (startConfig B x w)).tape i =
        (machine.run s (startConfig B' x w)).tape i' :=
  budget_independence B B' x w htag s

theorem check_malformed_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none)
    (s : Nat) (hs : 1 ≤ s) :
    let d := machine.run s (startConfig B x w)
    d.state = qReject ∧ d.head.val = a + m ∧
      d.tape = FixedPairContentMarkerErase.contentTape B x w :=
  malformed_exact x w htag hg s hs

theorem check_malformed_at_deadline {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none) :
    let d := machine.run (deadline (a + m)) (startConfig B x w)
    d.state = qReject ∧ d.head.val = a + m ∧
      d.tape = FixedPairContentMarkerErase.contentTape B x w :=
  malformed_at_deadline x w htag hg

/-! Concrete schedule regressions.  With `N = 10` and one gamma zero the clock
is `8`; with `N = 9` and zero width it is `7`, the shortest successful run. -/

example : exactClock 10 1 = 8 ∧ deadline 10 = 20 ∧ exactClock 9 0 = 7 := ⟨rfl, rfl, rfl⟩

example :
    (List.range 9).map (traceState 10 1) =
      [qStart, qNormalize, qSeekTerm, qSeekTerm, qScanRight, qWriteScratch,
        qCrossBoundary, qScanLeft, qTerm] := by decide

example : (List.range 9).map (traceHead 10 1) = [6, 7, 8, 9, 10, 11, 10, 9, 9] := by
  decide

example :
    (List.range 8).map (traceState 9 0) =
      [qStart, qNormalize, qSeekTerm, qScanRight, qWriteScratch, qCrossBoundary,
        qScanLeft, qTerm] := by decide

example : (List.range 8).map (traceHead 9 0) = [7, 7, 8, 9, 10, 9, 8, 8] := by decide

end Pnp3.Tests.UniformV1FixedGammaTerminatorScratchBootstrapSurfaceTests
