import Complexity.Uniform.V1.FixedPairSeparatorCursor

namespace Pnp3.Tests.UniformV1FixedPairSeparatorCursorSurfaceTests

open Pnp3.Complexity.Uniform.V1
open Pnp3.Complexity.Uniform.V1.PairEncoding
open Pnp3.Complexity.Uniform.V1.FixedPairSeparatorCursor

def check_cursorStateCount : Nat :=
  cursorStateCount

def check_qTag : Fin cursorStateCount :=
  qTag

def check_qData : Fin cursorStateCount :=
  qData

def check_qPeek : Fin cursorStateCount :=
  qPeek

def check_qAccept : Fin cursorStateCount :=
  qAccept

def check_qReject : Fin cursorStateCount :=
  qReject

def check_machine : UniformTM :=
  machine

def check_startConfig {N : Nat} (B : Nat) (raw : Bitstring N) :
    Config cursorStateCount N B :=
  startConfig B raw

def check_clock : Nat → Nat :=
  clock

def check_finalConfig {n m : Nat} (B : Nat)
    (x : Bitstring n) (w : Bitstring m) :
    Config cursorStateCount (pairLength n m) B :=
  finalConfig B x w

theorem check_cursorRawStep_table :
    (∀ scanned : Option Bool,
      machine.rawStep qTag scanned =
        match scanned with
        | none => (qReject, none, .stay)
        | some false => (qData, some false, .right)
        | some true => (qPeek, some true, .right)) ∧
    (∀ scanned : Option Bool,
      machine.rawStep qData scanned =
        match scanned with
        | none => (qReject, none, .stay)
        | some b => (qTag, some b, .right)) ∧
    (∀ scanned : Option Bool,
      machine.rawStep qPeek scanned =
        match scanned with
        | none => (qReject, none, .stay)
        | some b => (qAccept, some b, .left)) ∧
    (∀ scanned : Option Bool,
      machine.rawStep qAccept scanned = (qAccept, scanned, .stay)) ∧
    (∀ scanned : Option Bool,
      machine.rawStep qReject scanned = (qReject, scanned, .stay)) :=
  cursorRawStep_table

theorem check_machine_resource_pins :
    machine.stateCount = 5 ∧
    machine.start = qTag ∧
    machine.accept = qAccept ∧
    machine.reject = qReject ∧
    qTag.val = 0 ∧
    qData.val = 1 ∧
    qPeek.val = 2 ∧
    qAccept.val = 3 ∧
    qReject.val = 4 ∧
    Fintype.card (Fin machine.stateCount) = 5 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 15 :=
  machine_resource_pins

theorem check_startConfig_of_sentinel_run {N B : Nat} (raw : Bitstring N) :
    (startConfig B raw).state = qTag ∧
    (startConfig B raw).head =
      (FixedPairConcatSentinel.machine.run
        (FixedPairConcatSentinel.clock N)
        (initialConfig FixedPairConcatSentinel.machine B raw)).head ∧
    (startConfig B raw).tape =
      (FixedPairConcatSentinel.machine.run
        (FixedPairConcatSentinel.clock N)
        (initialConfig FixedPairConcatSentinel.machine B raw)).tape :=
  startConfig_of_sentinel_run raw

theorem check_run_preterminal_exact {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    (machine.run (2 * n + 1) (startConfig B (encodePair x w))).state = qPeek ∧
    (machine.run (2 * n + 1) (startConfig B (encodePair x w))).head.val =
      2 * n + 1 ∧
    (machine.run (2 * n + 1) (startConfig B (encodePair x w))).tape =
      FixedPairConcatSentinel.sentinelTape B (encodePair x w) :=
  run_preterminal_exact x w

theorem check_run_encoded_exact {n m : Nat} (B : Nat)
    (x : Bitstring n) (w : Bitstring m) :
    machine.run (clock n) (startConfig B (encodePair x w)) =
      finalConfig B x w :=
  run_encoded_exact B x w

theorem check_final_tape_unchanged {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    (machine.run (clock n) (startConfig B (encodePair x w))).tape =
      FixedPairConcatSentinel.sentinelTape B (encodePair x w) :=
  final_tape_unchanged x w

theorem check_final_literal_fields {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    (machine.run (clock n) (startConfig B (encodePair x w))).state = qAccept ∧
    (machine.run (clock n) (startConfig B (encodePair x w))).head.val = 2 * n :=
  final_literal_fields x w

theorem check_head_le_separator_successor_through_clock {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m)
    (s : Nat) (hs : s ≤ clock n) :
    (machine.run s (startConfig B (encodePair x w))).head.val ≤ 2 * n + 1 :=
  head_le_separator_successor_through_clock x w s hs

theorem check_reaches_separator_successor {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    (machine.run (2 * n + 1)
      (startConfig B (encodePair x w))).head.val = 2 * n + 1 :=
  reaches_separator_successor x w

theorem check_run_budget_independent {n m : Nat}
    (B B' : Nat) (x : Bitstring n) (w : Bitstring m)
    (s : Nat) (hs : s ≤ clock n) :
    (machine.run s (startConfig B (encodePair x w))).state =
      (machine.run s (startConfig B' (encodePair x w))).state ∧
    (machine.run s (startConfig B (encodePair x w))).head.val =
      (machine.run s (startConfig B' (encodePair x w))).head.val ∧
    (∀ (i : Fin (tapeLength (pairLength n m) B))
        (i' : Fin (tapeLength (pairLength n m) B')),
      i.val = i'.val →
      (machine.run s (startConfig B (encodePair x w))).tape i =
        (machine.run s (startConfig B' (encodePair x w))).tape i') :=
  run_budget_independent B B' x w s hs

theorem check_no_boundary_clamp_before_clock {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m)
    (s : Nat) (hs : s < clock n) :
    let c := machine.run s (startConfig B (encodePair x w))
    let move := (machine.step c.state (c.tape c.head)).2.2
    (move = .right → c.head.val + 1 < tapeLength (pairLength n m) B) ∧
    (move = .left → 0 < c.head.val) :=
  no_boundary_clamp_before_clock x w s hs

theorem check_noEarlyTerminal {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m)
    (s : Nat) (hs : s < clock n) :
    (machine.run s (startConfig B (encodePair x w))).state ≠ qAccept ∧
    (machine.run s (startConfig B (encodePair x w))).state ≠ qReject :=
  noEarlyTerminal x w s hs

theorem check_run_after_clock {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) (extra : Nat) :
    machine.run (clock n + extra) (startConfig B (encodePair x w)) =
      finalConfig B x w :=
  run_after_clock x w extra

theorem check_malformed_literal_fields {N B : Nat}
    (raw : Bitstring N) (hdecode : decodePair raw = none)
    (hB : 0 < B) :
    (machine.run (N + 2) (startConfig B raw)).state = qReject ∧
    (machine.run (N + 2) (startConfig B raw)).head.val = N + 1 ∧
    (machine.run (N + 2) (startConfig B raw)).tape =
      FixedPairConcatSentinel.sentinelTape B raw :=
  malformed_literal_fields raw hdecode hB

theorem check_phase_contract {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    let c₀ := startConfig B (encodePair x w)
    machine.run (clock n) c₀ = finalConfig B x w ∧
    (∀ s, s < clock n →
      (machine.run s c₀).state ≠ qAccept ∧
      (machine.run s c₀).state ≠ qReject) ∧
    (∀ s, s ≤ clock n →
      (machine.run s c₀).head.val ≤ 2 * n + 1) ∧
    (machine.run (2 * n + 1) c₀).head.val = 2 * n + 1 ∧
    (∀ s, s ≤ clock n →
      (machine.run s c₀).tape =
        FixedPairConcatSentinel.sentinelTape B (encodePair x w)) ∧
    (machine.run (clock n) c₀).state = qAccept ∧
    (machine.run (clock n) c₀).head.val = 2 * n :=
  phase_contract x w

end Pnp3.Tests.UniformV1FixedPairSeparatorCursorSurfaceTests
