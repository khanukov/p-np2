import Complexity.Uniform.V1.FixedPairTagRemoval

namespace Pnp3.Tests.UniformV1FixedPairTagRemovalSurfaceTests

open Pnp3.Complexity.Uniform.V1
open Pnp3.Complexity.Uniform.V1.PairEncoding
open Pnp3.Complexity.Uniform.V1.FixedPairTagRemoval

def check_removalStateCount : Nat :=
  removalStateCount

def check_qStart : Fin removalStateCount :=
  qStart

def check_qAccept : Fin removalStateCount :=
  qAccept

def check_qReject : Fin removalStateCount :=
  qReject

def check_machine : UniformTM :=
  machine

def check_startConfig {n m : Nat} (B : Nat)
    (x : Bitstring n) (w : Bitstring m) :
    Config removalStateCount (pairLength n m) B :=
  startConfig B x w

def check_clock (n : Nat) : Nat :=
  clock n

def check_compactTape {n m : Nat} (B : Nat)
    (x : Bitstring n) (w : Bitstring m) :
    Fin (tapeLength (pairLength n m) B) → Option Bool :=
  compactTape B x w

def check_finalConfig {n m : Nat} (B : Nat)
    (x : Bitstring n) (w : Bitstring m) :
    Config removalStateCount (pairLength n m) B :=
  finalConfig B x w

theorem check_removalRawStep_table :
    (∀ s, machine.rawStep qStart s =
      match s with
      | none => (⟨1, by decide⟩, none, .left)
      | some b => (qReject, some b, .stay)) ∧
    (∀ s, machine.rawStep ⟨1, by decide⟩ s =
      match s with
      | none => (qAccept, none, .stay)
      | some false => (⟨2, by decide⟩, none, .right)
      | some true => (⟨3, by decide⟩, none, .right)) ∧
    (∀ s, machine.rawStep ⟨2, by decide⟩ s =
      match s with
      | none => (⟨2, by decide⟩, none, .right)
      | some b => (⟨4, by decide⟩, some b, .left)) ∧
    (∀ s, machine.rawStep ⟨3, by decide⟩ s =
      match s with
      | none => (⟨3, by decide⟩, none, .right)
      | some b => (⟨5, by decide⟩, some b, .left)) ∧
    (∀ s, machine.rawStep ⟨4, by decide⟩ s =
      match s with
      | none => (⟨6, by decide⟩, some false, .left)
      | some b => (qReject, some b, .stay)) ∧
    (∀ s, machine.rawStep ⟨5, by decide⟩ s =
      match s with
      | none => (⟨6, by decide⟩, some true, .left)
      | some b => (qReject, some b, .stay)) ∧
    (∀ s, machine.rawStep ⟨6, by decide⟩ s =
      match s with
      | none => (⟨6, by decide⟩, none, .left)
      | some false => (⟨1, by decide⟩, none, .left)
      | some true => (qReject, some true, .stay)) ∧
    (∀ s, machine.rawStep qAccept s = (qAccept, s, .stay)) ∧
    (∀ s, machine.rawStep qReject s = (qReject, s, .stay)) :=
  removalRawStep_table

theorem check_machine_resource_pins :
    machine.stateCount = 9 ∧ machine.start = qStart ∧
    machine.accept = qAccept ∧ machine.reject = qReject ∧
    qStart.val = 0 ∧ qAccept.val = 7 ∧ qReject.val = 8 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 27 :=
  machine_resource_pins

theorem check_startConfig_of_hole_run {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    let holeFinal := FixedPairSeparatorHole.machine.run
      FixedPairSeparatorHole.clock (FixedPairSeparatorHole.startConfig B x w)
    holeFinal.state = FixedPairSeparatorHole.qAccept ∧
    (startConfig B x w).state = qStart ∧
    (startConfig B x w).head = holeFinal.head ∧
    (startConfig B x w).tape = holeFinal.tape ∧
    (startConfig B x w).head.val = 2 * n ∧
    (startConfig B x w).tape (startConfig B x w).head = none :=
  startConfig_of_hole_run x w

theorem check_clock_structural (n : Nat) :
    clock n = n * n + 5 * n + 2 ∧ clock 0 = 2 ∧
    clock (n + 1) = clock n + (2 * n + 6) :=
  clock_structural n

theorem check_run_encoded_exact {n m : Nat} (B : Nat)
    (x : Bitstring n) (w : Bitstring m) :
    machine.run (clock n) (startConfig B x w) = finalConfig B x w :=
  run_encoded_exact B x w

theorem check_final_literal_fields {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    (machine.run (clock n) (startConfig B x w)).state = qAccept ∧
    (machine.run (clock n) (startConfig B x w)).state = machine.accept ∧
    (machine.run (clock n) (startConfig B x w)).head.val = 0 ∧
    (machine.run (clock n) (startConfig B x w)).tape = compactTape B x w :=
  final_literal_fields x w

theorem check_run_after_clock {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) (extra : Nat) :
    machine.run (clock n + extra) (startConfig B x w) = finalConfig B x w :=
  run_after_clock x w extra

theorem check_noEarlyTerminal {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m)
    (s : Nat) (hs : s < clock n) :
    (machine.run s (startConfig B x w)).state ≠ qAccept ∧
    (machine.run s (startConfig B x w)).state ≠ qReject :=
  noEarlyTerminal x w s hs

theorem check_footprint_through_clock {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    (∀ s, s ≤ clock n →
      (machine.run s (startConfig B x w)).head.val ≤ 2 * n + 1) ∧
    (0 < n → (machine.run 3 (startConfig B x w)).head.val = 2 * n + 1) ∧
    (∀ s, s ≤ clock n → ∀ i : Fin (tapeLength (pairLength n m) B),
      2 * n < i.val →
      (machine.run s (startConfig B x w)).tape i =
        FixedPairConcatSentinel.sentinelTape B (encodePair x w) i) :=
  footprint_through_clock x w

theorem check_boundary_clamps {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    (∀ s, s < clock n →
      let c := machine.run s (startConfig B x w)
    (machine.step c.state (c.tape c.head)).2.2 = .right →
        c.head.val ≤ 2 * n ∧ c.head.val + 1 < tapeLength (pairLength n m) B) ∧
    (∀ s, s < clock n → s ≠ clock n - 2 →
      let c := machine.run s (startConfig B x w)
      (machine.step c.state (c.tape c.head)).2.2 = .left → 0 < c.head.val) ∧
    (let c := machine.run (clock n - 2) (startConfig B x w)
     c.head.val = 0 ∧ (machine.step c.state (c.tape c.head)).2.2 = .left) :=
  boundary_clamps x w

theorem check_run_budget_independent {n m : Nat}
    (B B' : Nat) (x : Bitstring n) (w : Bitstring m)
    (s : Nat) (hs : s ≤ clock n) :
    (machine.run s (startConfig B x w)).state =
      (machine.run s (startConfig B' x w)).state ∧
    (machine.run s (startConfig B x w)).head.val =
      (machine.run s (startConfig B' x w)).head.val ∧
    (∀ (i : Fin (tapeLength (pairLength n m) B))
        (i' : Fin (tapeLength (pairLength n m) B')),
      i.val = i'.val →
      (machine.run s (startConfig B x w)).tape i =
        (machine.run s (startConfig B' x w)).tape i') :=
  run_budget_independent B B' x w s hs

theorem check_final_tape_behavior {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    let cF := machine.run (clock n) (startConfig B x w)
    (∀ i : Fin (tapeLength (pairLength n m) B), i.val ≤ n → cF.tape i = none) ∧
    (∀ j : Fin n,
      cF.tape ⟨n + 1 + j.val, by unfold tapeLength pairLength; omega⟩ =
        some (x j)) ∧
    (∀ j : Fin m,
      cF.tape ⟨2 * n + 1 + j.val, by unfold tapeLength pairLength; omega⟩ =
        some (w j)) ∧
    cF.tape ⟨pairLength n m, by unfold tapeLength; omega⟩ = some true ∧
    (∀ i : Fin (tapeLength (pairLength n m) B),
      pairLength n m < i.val → cF.tape i = none) :=
  final_tape_behavior x w

theorem check_final_content_contiguous {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) (j : Fin (n + m)) :
    (machine.run (clock n) (startConfig B x w)).tape
      ⟨n + 1 + j.val, by unfold tapeLength pairLength; omega⟩ =
        some (Fin.append x w j) :=
  final_content_contiguous x w j

theorem check_zero_cases {n m : Nat} (B : Nat) :
    (∀ (x : Bitstring 0) (w : Bitstring m),
      clock 0 = 2 ∧
      machine.run (clock 0) (startConfig B x w) = finalConfig B x w ∧
      (machine.run (clock 0) (startConfig B x w)).head.val = 0 ∧
      (machine.run (clock 0) (startConfig B x w)).tape =
        (startConfig B x w).tape) ∧
    (∀ (x : Bitstring n) (w : Bitstring 0),
      pairLength n 0 = 2 * n + 1 ∧
      machine.run (clock n) (startConfig B x w) = finalConfig B x w ∧
      (machine.run (clock n) (startConfig B x w)).tape
        ⟨2 * n + 1, by unfold tapeLength pairLength; omega⟩ = some true) ∧
    (∀ (x : Bitstring n) (w : Bitstring m),
      tapeLength (pairLength n m) 0 = pairLength n m + 1 ∧
      machine.run (clock n) (startConfig 0 x w) = finalConfig 0 x w) :=
  zero_cases B

theorem check_phase_contract {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    let c₀ := startConfig B x w
    c₀.head = (FixedPairSeparatorHole.finalConfig B x w).head ∧
    c₀.tape = (FixedPairSeparatorHole.finalConfig B x w).tape ∧
    machine.run (clock n) c₀ = finalConfig B x w ∧
    (∀ s, s < clock n →
      (machine.run s c₀).state ≠ qAccept ∧ (machine.run s c₀).state ≠ qReject) ∧
    (∀ s, s ≤ clock n → (machine.run s c₀).head.val ≤ 2 * n + 1) ∧
    (∀ s, s ≤ clock n → ∀ i : Fin (tapeLength (pairLength n m) B),
      2 * n < i.val →
      (machine.run s c₀).tape i =
        FixedPairConcatSentinel.sentinelTape B (encodePair x w) i) ∧
    (machine.run (clock n) c₀).state = qAccept ∧
    (machine.run (clock n) c₀).head.val = 0 ∧
    (∀ i : Fin (tapeLength (pairLength n m) B), i.val ≤ n →
      (machine.run (clock n) c₀).tape i = none) ∧
    (∀ j : Fin (n + m),
      (machine.run (clock n) c₀).tape
        ⟨n + 1 + j.val, by unfold tapeLength pairLength; omega⟩ =
          some (Fin.append x w j)) :=
  phase_contract x w

end Pnp3.Tests.UniformV1FixedPairTagRemovalSurfaceTests
