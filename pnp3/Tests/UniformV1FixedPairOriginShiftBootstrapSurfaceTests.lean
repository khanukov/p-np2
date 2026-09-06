import Complexity.Uniform.V1.FixedPairOriginShiftBootstrap

namespace Pnp3.Tests.UniformV1FixedPairOriginShiftBootstrapSurfaceTests

open Pnp3.Complexity.Uniform.V1
open Pnp3.Complexity.Uniform.V1.PairEncoding
open Pnp3.Complexity.Uniform.V1.FixedPairOriginShiftBootstrap

abbrev check_shiftStateCount : Nat :=
  shiftStateCount

def check_qStart : Fin shiftStateCount :=
  qStart

def check_qAccept : Fin shiftStateCount :=
  qAccept

def check_qReject : Fin shiftStateCount :=
  qReject

def check_machine : UniformTM :=
  machine

def check_retag {N B : Nat}
    (c : Config FixedPairTagRemoval.removalStateCount N B) :
    Config shiftStateCount N B :=
  retag c

def check_startConfig {n m : Nat} (B : Nat)
    (x : Bitstring n) (w : Bitstring m) :
    Config shiftStateCount (pairLength n m) B :=
  startConfig B x w

def check_clock (n m : Nat) : Nat :=
  clock n m

def check_shiftedTape {n m : Nat} (B : Nat)
    (x : Bitstring n) (w : Bitstring m) :
    Fin (tapeLength (pairLength n m) B) → Option Bool :=
  shiftedTape B x w

def check_finalConfig {n m : Nat} (B : Nat)
    (x : Bitstring n) (w : Bitstring m) :
    Config shiftStateCount (pairLength n m) B :=
  finalConfig B x w

theorem check_raw_table :
    (∀ s, machine.rawStep qStart s = match s with
      | none => (qStart, none, .right)
      | some false => (⟨1, by decide⟩, none, .left)
      | some true => (⟨2, by decide⟩, none, .left)) ∧
    (∀ s, machine.rawStep ⟨1, by decide⟩ s = match s with
      | none => (⟨3, by decide⟩, some false, .right)
      | some b => (qReject, some b, .stay)) ∧
    (∀ s, machine.rawStep ⟨2, by decide⟩ s = match s with
      | none => (⟨3, by decide⟩, some true, .right)
      | some b => (qReject, some b, .stay)) ∧
    (∀ s, machine.rawStep ⟨3, by decide⟩ s = match s with
      | none => (⟨4, by decide⟩, none, .right)
      | some b => (qReject, some b, .stay)) ∧
    (∀ s, machine.rawStep ⟨4, by decide⟩ s = match s with
      | none => (qAccept, none, .stay)
      | some false => (⟨1, by decide⟩, none, .left)
      | some true => (⟨2, by decide⟩, none, .left)) ∧
    (∀ s, machine.rawStep qAccept s = (qAccept, s, .stay)) ∧
    (∀ s, machine.rawStep qReject s = (qReject, s, .stay)) :=
  raw_table

theorem check_resource_pins :
    machine.stateCount = 7 ∧ machine.start = qStart ∧
    machine.accept = qAccept ∧ machine.reject = qReject ∧
    qStart.val = 0 ∧ qAccept.val = 5 ∧ qReject.val = 6 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 21 :=
  resource_pins

theorem check_handoff_exact {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    let p := FixedPairTagRemoval.machine.run (FixedPairTagRemoval.clock n)
      (FixedPairTagRemoval.startConfig B x w)
    p = FixedPairTagRemoval.finalConfig B x w ∧
    p.state = FixedPairTagRemoval.qAccept ∧
    (startConfig B x w).state = qStart ∧
    (startConfig B x w).head = p.head ∧
    (startConfig B x w).tape = p.tape :=
  handoff_exact x w

theorem check_clock_exact (n m : Nat) :
    clock n m = (n + 1) + 3 * (n + m + 1) + 1 ∧
    clock 0 0 = 5 ∧ clock n m ≤ 4 * (n + m + 1) + 1 :=
  clock_exact n m

theorem check_run_exact {n m : Nat} (B : Nat)
    (x : Bitstring n) (w : Bitstring m) :
    machine.run (clock n m) (startConfig B x w) = finalConfig B x w :=
  run_exact B x w

theorem check_final_fields {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    (machine.run (clock n m) (startConfig B x w)).state = qAccept ∧
    (machine.run (clock n m) (startConfig B x w)).state = machine.accept ∧
    (machine.run (clock n m) (startConfig B x w)).head.val =
      pairLength n m + Nat.min B 1 ∧
    (machine.run (clock n m) (startConfig B x w)).tape = shiftedTape B x w :=
  final_fields x w

theorem check_noEarlyTerminal {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m)
    (s : Nat) (hs : s < clock n m) :
    (machine.run s (startConfig B x w)).state ≠ qAccept ∧
    (machine.run s (startConfig B x w)).state ≠ qReject :=
  noEarlyTerminal x w s hs

theorem check_run_after {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) (extra : Nat) :
    machine.run (clock n m + extra) (startConfig B x w) = finalConfig B x w :=
  run_after x w extra

theorem check_footprint {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    (∀ s, s ≤ clock n m →
      (machine.run s (startConfig B x w)).head.val ≤ pairLength n m + 1) ∧
    (B = 0 → ∀ s, s ≤ clock n m →
      (machine.run s (startConfig B x w)).head.val ≤ pairLength n m) ∧
    (machine.run (clock n m - 1) (startConfig B x w)).head.val =
      pairLength n m + Nat.min B 1 ∧
    (∀ s, s ≤ clock n m → ∀ i : Fin (tapeLength (pairLength n m) B),
      pairLength n m < i.val →
      (machine.run s (startConfig B x w)).tape i = none) :=
  footprint x w

theorem check_clamps {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    (∀ s, s < clock n m →
      let c := machine.run s (startConfig B x w)
      (machine.step c.state (c.tape c.head)).2.2 = .left → 0 < c.head.val) ∧
    (∀ s, s < clock n m → s ≠ clock n m - 2 →
      let c := machine.run s (startConfig B x w)
      (machine.step c.state (c.tape c.head)).2.2 = .right →
        c.head.val + 1 < tapeLength (pairLength n m) B) ∧
    (machine.run (clock n m - 2) (startConfig B x w)).head.val =
        pairLength n m ∧
    (machine.step
        (machine.run (clock n m - 2) (startConfig B x w)).state
        ((machine.run (clock n m - 2) (startConfig B x w)).tape
          (machine.run (clock n m - 2) (startConfig B x w)).head)).2.2 =
      .right ∧
    (moveHead (machine.run (clock n m - 2) (startConfig B x w)).head
        .right = (machine.run (clock n m - 2) (startConfig B x w)).head ↔
      B = 0) :=
  clamps x w

theorem check_budget_accounting {n m : Nat}
    (B B' : Nat) (x : Bitstring n) (w : Bitstring m)
    (hscope : B = 0 ↔ B' = 0) (s : Nat) (hs : s ≤ clock n m) :
    (machine.run s (startConfig B x w)).state =
      (machine.run s (startConfig B' x w)).state ∧
    (machine.run s (startConfig B x w)).head.val =
      (machine.run s (startConfig B' x w)).head.val ∧
    (∀ (i : Fin (tapeLength (pairLength n m) B))
        (i' : Fin (tapeLength (pairLength n m) B')), i.val = i'.val →
      (machine.run s (startConfig B x w)).tape i =
        (machine.run s (startConfig B' x w)).tape i') :=
  budget_accounting B B' x w hscope s hs

theorem check_final_layout {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    let c := machine.run (clock n m) (startConfig B x w)
    (∀ i : Fin (tapeLength (pairLength n m) B), i.val < n → c.tape i = none) ∧
    (∀ j : Fin n, c.tape ⟨n + j.val, by unfold tapeLength pairLength; omega⟩ =
      some (x j)) ∧
    (∀ j : Fin m, c.tape ⟨2 * n + j.val, by unfold tapeLength pairLength; omega⟩ =
      some (w j)) ∧
    c.tape ⟨2 * n + m, by unfold tapeLength pairLength; omega⟩ = some true ∧
    (∀ i : Fin (tapeLength (pairLength n m) B),
      pairLength n m ≤ i.val → c.tape i = none) :=
  final_layout x w

theorem check_recovery {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    (∀ i : Fin (tapeLength (pairLength n m) B),
      FixedPairTagRemoval.compactTape B x w i =
        if i.val = 0 then none else shiftedTape B x w
          ⟨i.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le i.val 1) i.isLt⟩) ∧
    (∀ (x' : Bitstring n) (w' : Bitstring m),
      shiftedTape B x w = shiftedTape B x' w' →
      FixedPairTagRemoval.compactTape B x w =
        FixedPairTagRemoval.compactTape B x' w') :=
  recovery x w

theorem check_phase_contract {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    let c0 := startConfig B x w
    c0.head = (FixedPairTagRemoval.finalConfig B x w).head ∧
    c0.tape = (FixedPairTagRemoval.finalConfig B x w).tape ∧
    machine.run (clock n m) c0 = finalConfig B x w ∧
    (∀ s, s < clock n m →
      (machine.run s c0).state ≠ qAccept ∧ (machine.run s c0).state ≠ qReject) ∧
    (∀ s, s ≤ clock n m →
      (machine.run s c0).head.val ≤ pairLength n m + 1) ∧
    (machine.run (clock n m) c0).head.val = pairLength n m + Nat.min B 1 ∧
    (∀ j : Fin (n + m), (machine.run (clock n m) c0).tape
      ⟨n + j.val, by unfold tapeLength pairLength; omega⟩ =
        some (Fin.append x w j)) ∧
    (machine.run (clock n m) c0).tape
      ⟨2 * n + m, by unfold tapeLength pairLength; omega⟩ = some true ∧
    FixedPairTagRemoval.compactTape B x w = fun i =>
      if i.val = 0 then none else shiftedTape B x w
        ⟨i.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le i.val 1) i.isLt⟩ :=
  phase_contract x w

end Pnp3.Tests.UniformV1FixedPairOriginShiftBootstrapSurfaceTests
