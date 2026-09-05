import Complexity.Uniform.V1.FixedPairConcatSentinel

namespace Pnp3.Tests.UniformV1FixedPairConcatSentinelSurfaceTests

open Pnp3.Complexity.Uniform.V1
open Pnp3.Complexity.Uniform.V1.FixedPairConcatSentinel

def check_sentinelStateCount : Nat :=
  sentinelStateCount

def check_qStart : Fin sentinelStateCount :=
  qStart

def check_qScanF : Fin sentinelStateCount :=
  qScanF

def check_qScanT : Fin sentinelStateCount :=
  qScanT

def check_qBackF : Fin sentinelStateCount :=
  qBackF

def check_qBackT : Fin sentinelStateCount :=
  qBackT

def check_qAccept : Fin sentinelStateCount :=
  qAccept

def check_qReject : Fin sentinelStateCount :=
  qReject

def check_machine : UniformTM :=
  machine

def check_clock : Nat → Nat :=
  clock

def check_sentinelTape {N : Nat} (B : Nat) (x : Bitstring N) :
    Fin (tapeLength N B) → Option Bool :=
  sentinelTape B x

def check_sentinelConfig {N : Nat} (B : Nat) (x : Bitstring N) :
    Config sentinelStateCount N B :=
  sentinelConfig B x

theorem check_machine_rawStep_table :
    (∀ scanned : Option Bool,
      machine.rawStep qStart scanned =
        match scanned with
        | none => (qAccept, some true, .stay)
        | some false => (qScanF, none, .right)
        | some true => (qScanT, none, .right)) ∧
    (∀ scanned : Option Bool,
      machine.rawStep qScanF scanned =
        match scanned with
        | none => (qBackF, some true, .left)
        | some b => (qScanF, some b, .right)) ∧
    (∀ scanned : Option Bool,
      machine.rawStep qScanT scanned =
        match scanned with
        | none => (qBackT, some true, .left)
        | some b => (qScanT, some b, .right)) ∧
    (∀ scanned : Option Bool,
      machine.rawStep qBackF scanned =
        match scanned with
        | none => (qAccept, some false, .stay)
        | some b => (qBackF, some b, .left)) ∧
    (∀ scanned : Option Bool,
      machine.rawStep qBackT scanned =
        match scanned with
        | none => (qAccept, some true, .stay)
        | some b => (qBackT, some b, .left)) ∧
    (∀ scanned : Option Bool,
      machine.rawStep qAccept scanned = (qAccept, scanned, .stay)) ∧
    (∀ scanned : Option Bool,
      machine.rawStep qReject scanned = (qReject, scanned, .stay)) :=
  machine_rawStep_table

theorem check_clock_eq (N : Nat) : clock N = 2 * N + 1 :=
  clock_eq N

theorem check_machine_resource_pins :
    machine.stateCount = 7 ∧
    machine.start = qStart ∧
    machine.accept = qAccept ∧
    machine.reject = qReject ∧
    qStart.val = 0 ∧
    qScanF.val = 1 ∧
    qScanT.val = 2 ∧
    qBackF.val = 3 ∧
    qBackT.val = 4 ∧
    qAccept.val = 5 ∧
    qReject.val = 6 ∧
    (∀ N, clock N = 2 * N + 1) ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 21 :=
  machine_resource_pins

theorem check_run_initialConfig_exact {N : Nat} (B : Nat)
    (x : Bitstring N) :
    machine.run (clock N) (initialConfig machine B x) =
      sentinelConfig B x :=
  run_initialConfig_exact B x

theorem check_final_tape_behavior {N B : Nat} (x : Bitstring N) :
    let cF := machine.run (clock N) (initialConfig machine B x)
    (∀ i : Fin N,
      cF.tape
        ⟨i.val, Nat.lt_of_lt_of_le i.isLt
          (Nat.le_add_right N (B + 1))⟩ = some (x i)) ∧
    cF.tape ⟨N, by unfold tapeLength; omega⟩ = some true ∧
    (∀ j : Fin (tapeLength N B), N < j.val → cF.tape j = none) :=
  final_tape_behavior x

theorem check_blank_after_marker {N B : Nat}
    (x : Bitstring N) (hB : 0 < B) :
    let cF := machine.run (clock N) (initialConfig machine B x)
    cF.tape ⟨N + 1, by unfold tapeLength; omega⟩ = none :=
  blank_after_marker x hB

theorem check_head_le_input_through_clock {N B : Nat}
    (x : Bitstring N) (s : Nat) (hs : s ≤ clock N) :
    (machine.run s (initialConfig machine B x)).head.val ≤ N :=
  head_le_input_through_clock x s hs

theorem check_beyond_input_blank_through_clock {N B : Nat}
    (x : Bitstring N) (s : Nat) (hs : s ≤ clock N)
    (j : Fin (tapeLength N B)) (hj : N < j.val) :
    (machine.run s (initialConfig machine B x)).tape j = none :=
  beyond_input_blank_through_clock x s hs j hj

theorem check_run_budget_independent {N : Nat} (B B' : Nat)
    (x : Bitstring N) (s : Nat) (hs : s ≤ clock N) :
    (machine.run s (initialConfig machine B x)).state =
      (machine.run s (initialConfig machine B' x)).state ∧
    (machine.run s (initialConfig machine B x)).head.val =
      (machine.run s (initialConfig machine B' x)).head.val ∧
    (∀ (i : Fin (tapeLength N B)) (i' : Fin (tapeLength N B')),
      i.val = i'.val →
        (machine.run s (initialConfig machine B x)).tape i =
          (machine.run s (initialConfig machine B' x)).tape i') :=
  run_budget_independent B B' x s hs

theorem check_no_boundary_clamp_before_clock {N B : Nat}
    (x : Bitstring N) (s : Nat) (hs : s < clock N) :
    let c := machine.run s (initialConfig machine B x)
    let move := (machine.step c.state (c.tape c.head)).2.2
    (move = .right → c.head.val + 1 < tapeLength N B) ∧
    (move = .left → 0 < c.head.val) :=
  no_boundary_clamp_before_clock x s hs

theorem check_work_state_before_clock {N B : Nat} (x : Bitstring N)
    (s : Nat) (hs : s < clock N) :
    (machine.run s (initialConfig machine B x)).state.val < 5 :=
  work_state_before_clock x s hs

theorem check_noEarlyTerminal_initialConfig {N B : Nat}
    (x : Bitstring N) (s : Nat) (hs : s < clock N) :
    (machine.run s (initialConfig machine B x)).state ≠ machine.accept ∧
      (machine.run s (initialConfig machine B x)).state ≠ machine.reject :=
  noEarlyTerminal_initialConfig x s hs

theorem check_acceptsAt_clock {N : Nat} (B : Nat) (x : Bitstring N) :
    AcceptsAt machine B (clock N) x :=
  acceptsAt_clock B x

theorem check_not_rejectsAt {N B : Nat} (x : Bitstring N) (s : Nat) :
    ¬ RejectsAt machine B s x :=
  not_rejectsAt x s

theorem check_decidesWithin {N B : Nat} (x : Bitstring N)
    (hB : clock N ≤ B) :
    DecidesWithin machine B x true :=
  decidesWithin x hB

theorem check_clock_le_polyClock_two (N : Nat) :
    clock N ≤ polyClock 2 N :=
  clock_le_polyClock_two N

theorem check_decidesWithin_polyClock {N : Nat} (x : Bitstring N) :
    DecidesWithin machine (polyClock 2 N) x true :=
  decidesWithin_polyClock x

theorem check_sentinel_phase_contract {N : Nat} (B : Nat)
    (x : Bitstring N) :
    let c₀ := initialConfig machine B x
    machine.run (clock N) c₀ = sentinelConfig B x ∧
    (∀ s, s < clock N → (machine.run s c₀).state.val < 5) ∧
    (∀ s, s < clock N →
      (machine.run s c₀).state ≠ machine.accept ∧
        (machine.run s c₀).state ≠ machine.reject) ∧
    (∀ s, s ≤ clock N → (machine.run s c₀).head.val ≤ N) ∧
    (∀ s, s ≤ clock N → ∀ j : Fin (tapeLength N B), N < j.val →
      (machine.run s c₀).tape j = none) ∧
    AcceptsAt machine B (clock N) x ∧
    (∀ s, ¬ RejectsAt machine B s x) ∧
    (clock N ≤ B → DecidesWithin machine B x true) :=
  sentinel_phase_contract B x

end Pnp3.Tests.UniformV1FixedPairConcatSentinelSurfaceTests
