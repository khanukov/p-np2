import Complexity.Uniform.V1.FixedContentGammaTerminator

namespace Pnp3.Tests.UniformV1FixedContentGammaTerminatorSurfaceTests
open Pnp3.Complexity.Uniform.V1
open PairEncoding
open FixedContentGammaTerminator

def check_stateCount : Nat := stateCount
def check_qScan : Fin stateCount := qScan
def check_qAccept : Fin stateCount := qAccept
def check_qReject : Fin stateCount := qReject
def check_machine : UniformTM := machine
def check_gammaZeros? {L : Nat} : Bitstring L → Option Nat := gammaZeros?
def check_terminalIndex {L : Nat} : Bitstring L → Nat := terminalIndex
def check_retag {N B : Nat} : Config FixedContentTagGate.stateCount N B → Config stateCount N B := retag
def check_startConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config stateCount (pairLength a m) B := startConfig B x w
def check_deadline : Nat → Nat → Nat := deadline
def check_finalConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config stateCount (pairLength a m) B := finalConfig B x w

theorem check_table_and_resource_pins :
    (∀ s, machine.rawStep qScan s = match s with
      | some false => (qScan, some false, .right)
      | some true => (qAccept, some true, .stay)
      | none => (qReject, none, .stay)) ∧ machine.stateCount = 3 ∧
    machine.start = qScan ∧ machine.accept = qAccept ∧ machine.reject = qReject ∧
    qScan.val = 0 ∧ qAccept.val = 1 ∧ qReject.val = 2 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 9 := by
  exact FixedContentGammaTerminator.table_and_resource_pins

theorem check_gamma_contract {L : Nat} (z : Bitstring L) :
    (∀ zeros, gammaZeros? z = some zeros → 8 + zeros < L ∧
      FixedContentTagGate.physicalSymbol z (8 + zeros) = some true ∧
      ∀ i, i < zeros → FixedContentTagGate.physicalSymbol z (8 + i) = some false) ∧
    (8 ≤ L → gammaZeros? z = none → ∀ i, i < L - 8 →
      FixedContentTagGate.physicalSymbol z (8 + i) = some false) ∧
    terminalIndex z ≤ L := by
  exact FixedContentGammaTerminator.gamma_contract z

theorem check_handoff_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    let p := FixedContentTagGate.machine.run (FixedContentTagGate.deadline a m)
      (FixedContentTagGate.startConfig B x w)
    let c := startConfig B x w
    p = FixedContentTagGate.finalConfig B x w ∧ p.state = FixedContentTagGate.machine.accept ∧
    p.head.val = 8 ∧ p.tape = FixedPairContentMarkerErase.contentTape B x w ∧
    c = retag p ∧ c.state = machine.start ∧ c.head = p.head ∧ c.tape = p.tape := by
  exact FixedContentGammaTerminator.handoff_exact x w htag

theorem check_run_deadline {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    machine.run (deadline a m) (startConfig B x w) = finalConfig B x w := by
  exact FixedContentGammaTerminator.run_deadline x w htag

theorem check_deadline_exact (a m : Nat) :
    8 ≤ a + m → deadline a m = (a + m - 8) + 1 := by
  exact FixedContentGammaTerminator.deadline_exact a m

theorem check_exact_terminal_contract {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    (∀ zeros, gammaZeros? (Fin.append x w) = some zeros →
      (∀ s < zeros + 1, (machine.run s (startConfig B x w)).state ≠ machine.accept ∧
        (machine.run s (startConfig B x w)).state ≠ machine.reject) ∧
      machine.run (zeros + 1) (startConfig B x w) = finalConfig B x w ∧
      zeros + 1 ≤ deadline a m) ∧
    (gammaZeros? (Fin.append x w) = none →
      (∀ s < deadline a m, (machine.run s (startConfig B x w)).state ≠ machine.accept ∧
        (machine.run s (startConfig B x w)).state ≠ machine.reject) ∧
      machine.run (deadline a m) (startConfig B x w) = finalConfig B x w) := by
  exact FixedContentGammaTerminator.exact_terminal_contract x w htag

theorem check_phase_contract {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    (∀ B s, s ≤ deadline a m →
      (machine.run s (startConfig B x w)).head.val ≤ a + m) ∧
    (∀ B s, s < deadline a m →
      let c := machine.run s (startConfig B x w)
      let move := (machine.step c.state (c.tape c.head)).2.2
      move ≠ .left ∧
      (move = .right → c.head.val + 1 < tapeLength (pairLength a m) B)) ∧
    (∀ B, (machine.run (deadline a m) (startConfig B x w)).tape =
      FixedPairContentMarkerErase.contentTape B x w) ∧
    (∀ B (i : Fin (tapeLength (pairLength a m) B)), a + m ≤ i.val →
      (machine.run (deadline a m) (startConfig B x w)).tape i = none) ∧
    (∀ B extra, machine.run (deadline a m + extra) (startConfig B x w) = finalConfig B x w) ∧
    (∀ B B' s, s ≤ deadline a m →
      let c := machine.run s (startConfig B x w)
      let c' := machine.run s (startConfig B' x w)
      c.state = c'.state ∧ c.head.val = c'.head.val ∧
      ∀ (i : Fin (tapeLength (pairLength a m) B)) (i' : Fin (tapeLength (pairLength a m) B')),
        i.val = i'.val →
        c.tape i = c'.tape i') := by
  exact FixedContentGammaTerminator.phase_contract x w htag

end Pnp3.Tests.UniformV1FixedContentGammaTerminatorSurfaceTests
