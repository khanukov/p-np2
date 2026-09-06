import Complexity.Uniform.V1.FixedPairSeparatorHole

namespace Pnp3.Tests.UniformV1FixedPairSeparatorHoleSurfaceTests

open Pnp3.Complexity.Uniform.V1
open Pnp3.Complexity.Uniform.V1.PairEncoding
open Pnp3.Complexity.Uniform.V1.FixedPairSeparatorHole

def check_holeStateCount : Nat :=
  holeStateCount

def check_qStart : Fin holeStateCount :=
  qStart

def check_qAccept : Fin holeStateCount :=
  qAccept

def check_qReject : Fin holeStateCount :=
  qReject

def check_machine : UniformTM :=
  machine

def check_retag {N B : Nat}
    (c : Config FixedPairSeparatorCursor.cursorStateCount N B) :
    Config holeStateCount N B :=
  retag c

def check_startConfig {n m : Nat} (B : Nat)
    (x : Bitstring n) (w : Bitstring m) :
    Config holeStateCount (pairLength n m) B :=
  startConfig B x w

def check_clock : Nat :=
  clock

def check_holeTape {n m : Nat} (B : Nat)
    (x : Bitstring n) (w : Bitstring m) :
    Fin (tapeLength (pairLength n m) B) → Option Bool :=
  holeTape B x w

def check_finalConfig {n m : Nat} (B : Nat)
    (x : Bitstring n) (w : Bitstring m) :
    Config holeStateCount (pairLength n m) B :=
  finalConfig B x w

def check_natView {L : Nat} (t : Fin L → Option Bool) (i : Nat) :
    Option Bool :=
  natView t i

theorem check_holeRawStep_table :
    (∀ scanned : Option Bool,
      machine.rawStep qStart scanned =
        match scanned with
        | none => (qReject, none, .stay)
        | some false => (qReject, some false, .stay)
        | some true => (qAccept, none, .stay)) ∧
    (∀ scanned : Option Bool,
      machine.rawStep qAccept scanned = (qAccept, scanned, .stay)) ∧
    (∀ scanned : Option Bool,
      machine.rawStep qReject scanned = (qReject, scanned, .stay)) :=
  holeRawStep_table

theorem check_machine_resource_pins :
    machine.stateCount = 3 ∧
    machine.start = qStart ∧
    machine.accept = qAccept ∧
    machine.reject = qReject ∧
    qStart.val = 0 ∧
    qAccept.val = 1 ∧
    qReject.val = 2 ∧
    Fintype.card (Fin machine.stateCount) = 3 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 9 :=
  machine_resource_pins

theorem check_retag_fields {N B : Nat}
    (c : Config FixedPairSeparatorCursor.cursorStateCount N B) :
    (retag c).state = qStart ∧
    (retag c).head = c.head ∧
    (retag c).tape = c.tape :=
  retag_fields c

theorem check_startConfig_of_cursor_run {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    let cursorFinal := FixedPairSeparatorCursor.machine.run
      (FixedPairSeparatorCursor.clock n)
      (FixedPairSeparatorCursor.startConfig B (encodePair x w))
    startConfig B x w = retag cursorFinal ∧
    cursorFinal.state = FixedPairSeparatorCursor.qAccept ∧
    (startConfig B x w).state = qStart ∧
    (startConfig B x w).head = cursorFinal.head ∧
    (startConfig B x w).tape = cursorFinal.tape :=
  startConfig_of_cursor_run x w

theorem check_clock_eq : clock = 1 :=
  clock_eq

theorem check_stepConfig_start_separator {N B : Nat}
    (c : Config holeStateCount N B)
    (hstate : c.state = qStart) (hread : c.tape c.head = some true) :
    machine.stepConfig c =
      ({ state := qAccept
         head := c.head
         tape := fun i => if i = c.head then none else c.tape i } :
        Config holeStateCount N B) :=
  stepConfig_start_separator c hstate hread

theorem check_stepConfig_start_non_separator {N B : Nat}
    (c : Config holeStateCount N B)
    (hstate : c.state = qStart) (hread : c.tape c.head ≠ some true) :
    machine.stepConfig c =
      ({ state := qReject
         head := c.head
         tape := c.tape } : Config holeStateCount N B) :=
  stepConfig_start_non_separator c hstate hread

theorem check_run_preterminal_exact {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    machine.run 0 (startConfig B x w) = startConfig B x w ∧
    (startConfig B x w).state = qStart ∧
    (startConfig B x w).head.val = 2 * n ∧
    (startConfig B x w).tape =
      FixedPairConcatSentinel.sentinelTape B (encodePair x w) ∧
    (startConfig B x w).tape (startConfig B x w).head = some true :=
  run_preterminal_exact x w

theorem check_run_encoded_exact {n m : Nat} (B : Nat)
    (x : Bitstring n) (w : Bitstring m) :
    machine.run clock (startConfig B x w) = finalConfig B x w :=
  run_encoded_exact B x w

theorem check_final_literal_fields {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    (machine.run clock (startConfig B x w)).state = qAccept ∧
    (machine.run clock (startConfig B x w)).state = machine.accept ∧
    (machine.run clock (startConfig B x w)).head.val = 2 * n ∧
    (machine.run clock (startConfig B x w)).head.val / 2 = n :=
  final_literal_fields x w

theorem check_final_tape_eq_holeTape {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    (machine.run clock (startConfig B x w)).tape = holeTape B x w :=
  final_tape_eq_holeTape x w

theorem check_final_tape_eq_update {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    (machine.run clock (startConfig B x w)).tape =
      Function.update
        (FixedPairConcatSentinel.sentinelTape B (encodePair x w))
        ⟨2 * n, by unfold tapeLength pairLength; omega⟩ none :=
  final_tape_eq_update x w

theorem check_final_tape_behavior {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    let cF := machine.run clock (startConfig B x w)
    cF.tape ⟨2 * n, by unfold tapeLength pairLength; omega⟩ = none ∧
    (∀ i : Fin n,
      cF.tape ⟨2 * i.val, by unfold tapeLength pairLength; omega⟩ =
        some false) ∧
    (∀ i : Fin n,
      cF.tape ⟨2 * i.val + 1, by unfold tapeLength pairLength; omega⟩ =
        some (x i)) ∧
    (∀ j : Fin m,
      cF.tape ⟨2 * n + 1 + j.val, by unfold tapeLength pairLength; omega⟩ =
        some (w j)) ∧
    cF.tape ⟨pairLength n m, by unfold tapeLength; omega⟩ = some true ∧
    (∀ i : Fin (tapeLength (pairLength n m) B),
      pairLength n m < i.val → cF.tape i = none) :=
  final_tape_behavior x w

theorem check_final_blank_iff {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m)
    (i : Fin (tapeLength (pairLength n m) B)) :
    (machine.run clock (startConfig B x w)).tape i = none ↔
      (i.val = 2 * n ∨ pairLength n m < i.val) :=
  final_blank_iff x w i

theorem check_hole_interior {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    let cF := machine.run clock (startConfig B x w)
    2 * n < pairLength n m ∧
    (∀ hm : 0 < m,
      cF.tape ⟨2 * n + 1, by unfold tapeLength pairLength; omega⟩ =
        some (w ⟨0, hm⟩)) ∧
    (m = 0 →
      cF.tape ⟨2 * n + 1, by unfold tapeLength pairLength; omega⟩ =
        some true) ∧
    (∀ hn : 0 < n,
      cF.tape ⟨2 * n - 1, by unfold tapeLength pairLength; omega⟩ =
        some (x ⟨n - 1, by omega⟩)) :=
  hole_interior x w

theorem check_holeTape_natView_injective {n m n' m' : Nat} (B B' : Nat)
    (x : Bitstring n) (w : Bitstring m)
    (x' : Bitstring n') (w' : Bitstring m')
    (h : natView (holeTape B x w) = natView (holeTape B' x' w')) :
    ((⟨n, x⟩, ⟨m, w⟩) : DecodedPair) =
      ((⟨n', x'⟩, ⟨m', w'⟩) : DecodedPair) :=
  holeTape_natView_injective B B' x w x' w' h

theorem check_final_tape_determines_pair {n m n' m' : Nat} (B B' : Nat)
    (x : Bitstring n) (w : Bitstring m)
    (x' : Bitstring n') (w' : Bitstring m')
    (h : natView (machine.run clock (startConfig B x w)).tape =
      natView (machine.run clock (startConfig B' x' w')).tape) :
    ((⟨n, x⟩, ⟨m, w⟩) : DecodedPair) =
      ((⟨n', x'⟩, ⟨m', w'⟩) : DecodedPair) :=
  final_tape_determines_pair B B' x w x' w' h

theorem check_finalConfig_injective {n m B : Nat}
    (x x' : Bitstring n) (w w' : Bitstring m)
    (h : finalConfig B x w = finalConfig B x' w') :
    x = x' ∧ w = w' :=
  finalConfig_injective x x' w w' h

theorem check_head_fixed_through_clock {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m)
    (s : Nat) (hs : s ≤ clock) :
    (machine.run s (startConfig B x w)).head = (startConfig B x w).head ∧
    (machine.run s (startConfig B x w)).head.val = 2 * n :=
  head_fixed_through_clock x w s hs

theorem check_tape_off_hole_through_clock {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m)
    (s : Nat) (hs : s ≤ clock)
    (i : Fin (tapeLength (pairLength n m) B)) (hi : i.val ≠ 2 * n) :
    (machine.run s (startConfig B x w)).tape i =
      FixedPairConcatSentinel.sentinelTape B (encodePair x w) i :=
  tape_off_hole_through_clock x w s hs i hi

theorem check_hole_cell_trace {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    (machine.run 0 (startConfig B x w)).tape
      ⟨2 * n, by unfold tapeLength pairLength; omega⟩ = some true ∧
    (machine.run clock (startConfig B x w)).tape
      ⟨2 * n, by unfold tapeLength pairLength; omega⟩ = none :=
  hole_cell_trace x w

theorem check_run_budget_independent {n m : Nat}
    (B B' : Nat) (x : Bitstring n) (w : Bitstring m)
    (s : Nat) (hs : s ≤ clock) :
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

theorem check_no_boundary_clamp_before_clock {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m)
    (s : Nat) (hs : s < clock) :
    let c := machine.run s (startConfig B x w)
    let move := (machine.step c.state (c.tape c.head)).2.2
    move = .stay ∧
    (move = .right → c.head.val + 1 < tapeLength (pairLength n m) B) ∧
    (move = .left → 0 < c.head.val) :=
  no_boundary_clamp_before_clock x w s hs

theorem check_noEarlyTerminal {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m)
    (s : Nat) (hs : s < clock) :
    (machine.run s (startConfig B x w)).state ≠ qAccept ∧
    (machine.run s (startConfig B x w)).state ≠ qReject :=
  noEarlyTerminal x w s hs

theorem check_run_after_clock {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) (extra : Nat) :
    machine.run (clock + extra) (startConfig B x w) = finalConfig B x w :=
  run_after_clock x w extra

theorem check_run_zero_query_exact {m : Nat} (B : Nat)
    (x : Bitstring 0) (w : Bitstring m) :
    machine.run clock (startConfig B x w) = finalConfig B x w ∧
    (machine.run clock (startConfig B x w)).head.val = 0 ∧
    (machine.run clock (startConfig B x w)).tape
      ⟨0, by unfold tapeLength; omega⟩ = none :=
  run_zero_query_exact B x w

theorem check_run_empty_witness_exact {n : Nat} (B : Nat)
    (x : Bitstring n) (w : Bitstring 0) :
    machine.run clock (startConfig B x w) = finalConfig B x w ∧
    pairLength n 0 = 2 * n + 1 ∧
    (machine.run clock (startConfig B x w)).tape
      ⟨2 * n + 1, by unfold tapeLength pairLength; omega⟩ = some true :=
  run_empty_witness_exact B x w

theorem check_run_zero_budget_exact {n m : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    tapeLength (pairLength n m) 0 = pairLength n m + 1 ∧
    machine.run clock (startConfig 0 x w) = finalConfig 0 x w :=
  run_zero_budget_exact x w

theorem check_run_minimal_literal :
    let x : Bitstring 0 := fun i => Fin.elim0 i
    let w : Bitstring 0 := fun i => Fin.elim0 i
    List.ofFn (startConfig 0 x w).tape = [some true, some true] ∧
    List.ofFn (machine.run clock (startConfig 0 x w)).tape =
      [none, some true] :=
  run_minimal_literal

theorem check_phase_contract {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    let c₀ := startConfig B x w
    c₀ = retag (FixedPairSeparatorCursor.finalConfig B x w) ∧
    machine.run clock c₀ = finalConfig B x w ∧
    (∀ s, s < clock →
      (machine.run s c₀).state ≠ qAccept ∧
      (machine.run s c₀).state ≠ qReject) ∧
    (∀ s, s ≤ clock → (machine.run s c₀).head.val = 2 * n) ∧
    (∀ s, s ≤ clock → ∀ i : Fin (tapeLength (pairLength n m) B),
      i.val ≠ 2 * n →
      (machine.run s c₀).tape i =
        FixedPairConcatSentinel.sentinelTape B (encodePair x w) i) ∧
    (machine.run clock c₀).state = qAccept ∧
    (machine.run clock c₀).head.val = 2 * n ∧
    (∀ i : Fin (tapeLength (pairLength n m) B),
      (machine.run clock c₀).tape i = none ↔
        (i.val = 2 * n ∨ pairLength n m < i.val)) :=
  phase_contract x w

end Pnp3.Tests.UniformV1FixedPairSeparatorHoleSurfaceTests
