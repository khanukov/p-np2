import Complexity.Uniform.V1.FixedContentGammaAnchor

namespace Pnp3.Tests.UniformV1FixedContentGammaAnchorSurfaceTests

open Pnp3.Complexity.Uniform.V1
open PairEncoding FixedContentGammaAnchor

def check_stateCount : Nat := stateCount
def check_qStart : Fin stateCount := qStart
def check_qLeft : Fin stateCount := qLeft
def check_qErase : Fin stateCount := qErase
def check_qReturn : Fin stateCount := qReturn
def check_qAccept : Fin stateCount := qAccept
def check_qReject : Fin stateCount := qReject
def check_machine : UniformTM := machine
def check_retag {N B : Nat} :
    Config FixedContentGammaTerminator.stateCount N B → Config stateCount N B := retag
def check_startConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config stateCount (pairLength a m) B := startConfig B x w
def check_successTime : Nat → Nat := successTime
def check_deadline : Nat → Nat → Nat := deadline
def check_markedTape {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Fin (tapeLength (pairLength a m) B) → Option Bool := markedTape B x w
def check_finalConfig {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) :
    Config stateCount (pairLength a m) B := finalConfig B x w

theorem check_table_and_resource_pins :
    (∀ s, machine.step qStart s = match s with
      | some true => (qLeft, some true, .left) | some false => (qReject, some false, .stay)
      | none => (qReject, none, .stay)) ∧
    (∀ s, machine.step qLeft s = match s with
      | some false => (qLeft, some false, .left) | some true => (qErase, some true, .right)
      | none => (qReject, none, .stay)) ∧
    (∀ s, machine.step qErase s = match s with
      | some false => (qReturn, none, .right) | some true => (qReject, some true, .stay)
      | none => (qReject, none, .stay)) ∧
    (∀ s, machine.step qReturn s = match s with
      | some false => (qReturn, some false, .right) | some true => (qAccept, some true, .stay)
      | none => (qReject, none, .stay)) ∧
    (∀ s, machine.step qAccept s = (qAccept, s, .stay)) ∧
    (∀ s, machine.step qReject s = (qReject, s, .stay)) ∧
    machine.stateCount = 6 ∧ machine.start = qStart ∧ machine.accept = qAccept ∧
    machine.reject = qReject ∧ qStart.val = 0 ∧ qLeft.val = 1 ∧ qErase.val = 2 ∧
    qReturn.val = 3 ∧ qAccept.val = 4 ∧ qReject.val = 5 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 18 :=
  FixedContentGammaAnchor.table_and_resource_pins

theorem check_handoff_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    let p := FixedContentGammaTerminator.machine.run (FixedContentGammaTerminator.deadline a m)
      (FixedContentGammaTerminator.startConfig B x w)
    let c := startConfig B x w
    p = FixedContentGammaTerminator.finalConfig B x w ∧ c = retag p ∧
    c.state = machine.start ∧ c.head = p.head ∧ c.tape = p.tape :=
  FixedContentGammaAnchor.handoff_exact x w htag

theorem check_run_success_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) {zeros : Nat}
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    machine.run (successTime zeros) (startConfig B x w) = finalConfig B x w :=
  FixedContentGammaAnchor.run_success_exact x w htag hg

theorem check_run_reject_exact {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none) :
    machine.run 1 (startConfig B x w) = finalConfig B x w :=
  FixedContentGammaAnchor.run_reject_exact x w hg

theorem check_successTime_le_deadline {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    {zeros : Nat} (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros) :
    successTime zeros ≤ deadline a m := FixedContentGammaAnchor.successTime_le_deadline x w hg

theorem check_run_deadline {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    machine.run (deadline a m) (startConfig B x w) = finalConfig B x w :=
  FixedContentGammaAnchor.run_deadline x w htag

theorem check_exact_terminal_contract {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    (∀ zeros, FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some zeros →
      (∀ s < successTime zeros, (machine.run s (startConfig B x w)).state ≠ machine.accept ∧
        (machine.run s (startConfig B x w)).state ≠ machine.reject) ∧
      machine.run (successTime zeros) (startConfig B x w) = finalConfig B x w ∧
      successTime zeros ≤ deadline a m) ∧
    (FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = none →
      (∀ s < 1, (machine.run s (startConfig B x w)).state ≠ machine.accept ∧
        (machine.run s (startConfig B x w)).state ≠ machine.reject) ∧
      machine.run 1 (startConfig B x w) = finalConfig B x w) :=
  FixedContentGammaAnchor.exact_terminal_contract x w htag

theorem check_final_tape_contract {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    let c := machine.run (deadline a m) (startConfig B x w)
    (FixedContentGammaTerminator.gammaZeros? (Fin.append x w)).isSome →
      c.tape = markedTape B x w ∧
      (∀ i, i.val ≠ 7 → c.tape i = FixedPairContentMarkerErase.contentTape B x w i) ∧
      (∀ i, i.val = 7 → c.tape i = none) ∧
      (∀ i, a + m ≤ i.val → c.tape i = none) :=
  FixedContentGammaAnchor.final_tape_contract x w htag

theorem check_execution_safety {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    (∀ B s, s ≤ deadline a m → let c := machine.run s (startConfig B x w)
      6 ≤ c.head.val ∧ c.head.val ≤ a + m ∧
      (∀ i, i.val ≠ 7 → c.tape i = FixedPairContentMarkerErase.contentTape B x w i) ∧
      (∀ i, a + m ≤ i.val → c.tape i = none)) ∧
    (∀ B s, s < deadline a m → let c := machine.run s (startConfig B x w)
      let move := (machine.step c.state (c.tape c.head)).2.2
      (move = .left → 0 < c.head.val) ∧
      (move = .right → c.head.val + 1 < tapeLength (pairLength a m) B)) :=
  FixedContentGammaAnchor.execution_safety x w htag

theorem check_budget_independence_through_deadline {a m : Nat}
    (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    ∀ B B' s, s ≤ deadline a m → let c := machine.run s (startConfig B x w)
      let c' := machine.run s (startConfig B' x w)
      c.state = c'.state ∧ c.head.val = c'.head.val ∧
      ∀ (i : Fin (tapeLength (pairLength a m) B))
        (i' : Fin (tapeLength (pairLength a m) B')), i.val = i'.val → c.tape i = c'.tape i' :=
  FixedContentGammaAnchor.budget_independence_through_deadline x w htag

theorem check_phase_contract {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    (∀ B, machine.run (deadline a m) (startConfig B x w) = finalConfig B x w) ∧
    (∀ B, (machine.run (deadline a m) (startConfig B x w)).head.val ≤ a + m) ∧
    (∀ B extra, machine.run (deadline a m + extra) (startConfig B x w) = finalConfig B x w) ∧
    (∀ B B', (machine.run (deadline a m) (startConfig B x w)).state =
        (machine.run (deadline a m) (startConfig B' x w)).state ∧
      (machine.run (deadline a m) (startConfig B x w)).head.val =
        (machine.run (deadline a m) (startConfig B' x w)).head.val) ∧
    (∀ B s, s ≤ deadline a m → let c := machine.run s (startConfig B x w)
      6 ≤ c.head.val ∧ c.head.val ≤ a + m ∧
      (∀ i, i.val ≠ 7 → c.tape i = FixedPairContentMarkerErase.contentTape B x w i) ∧
      (∀ i, a + m ≤ i.val → c.tape i = none)) ∧
    (∀ B B' s, s ≤ deadline a m → let c := machine.run s (startConfig B x w)
      let c' := machine.run s (startConfig B' x w)
      c.state = c'.state ∧ c.head.val = c'.head.val ∧
      ∀ (i : Fin (tapeLength (pairLength a m) B))
        (i' : Fin (tapeLength (pairLength a m) B')), i.val = i'.val → c.tape i = c'.tape i') :=
  FixedContentGammaAnchor.phase_contract x w htag

end Pnp3.Tests.UniformV1FixedContentGammaAnchorSurfaceTests
