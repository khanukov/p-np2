import Complexity.Uniform.V1.FixedPairParserCore

/-!
# Public surface pins for the fixed Uniform V1 pair-parser core

The two finite capstone wrappers are intentionally first: in the vertical TDD
sequence this file is added and run before the core module, where its missing
import/declarations are the expected RED result.  After the core is added,
every source theorem below has exactly one namespaced wrapper restating its
full proposition.
-/

namespace Pnp3.Tests.UniformV1FixedPairParserCore

open Pnp3.Complexity.Uniform.V1
open Pnp3.Complexity.Uniform.V1.PairEncoding
open Pnp3.Complexity.Uniform.V1.FixedPairParser

/-! ## Capstone-first vertical surface -/

theorem check_finite_exact_run_capstone :
    decodePairList [] = none ∧
    RejectsAt machine 1 1 (rawBitstring []) ∧
    decodePairList [false] = none ∧
    RejectsAt machine 3 3 (rawBitstring [false]) ∧
    decodePairList [false, true] = none ∧
    RejectsAt machine 5 5 (rawBitstring [false, true]) ∧
    decodePairList [true] = some ([], []) ∧
    AcceptsAt machine 3 3 (rawBitstring [true]) ∧
    decodePairList [false, true, true] = some ([true], []) ∧
    AcceptsAt machine 7 7 (rawBitstring [false, true, true]) ∧
    decodePairList [true, false] = some ([], [false]) ∧
    AcceptsAt machine 5 5 (rawBitstring [true, false]) :=
  finite_exact_run_capstone

theorem check_finite_restoration_capstone :
    (clockConfig [true, false]).state = qAccept ∧
    (clockConfig [true, false]).head.val = 0 ∧
    (clockConfig [true, false]).tape =
      (initialConfig machine 5
        (rawBitstring [true, false])).tape ∧
    (clockConfig [false, true]).state = qReject ∧
    (clockConfig [false, true]).head.val = 0 ∧
    (clockConfig [false, true]).tape =
      (initialConfig machine 5
        (rawBitstring [false, true])).tape :=
  finite_restoration_capstone

/-! ## Typed public-definition pins -/

#check (parserStateCount : Nat)
#check (qStart : Fin parserStateCount)
#check (qDataF : Fin parserStateCount)
#check (qTagF : Fin parserStateCount)
#check (qWitnessF : Fin parserStateCount)
#check (qWitnessT : Fin parserStateCount)
#check (qBackAcceptF : Fin parserStateCount)
#check (qBackAcceptT : Fin parserStateCount)
#check (qBackRejectF : Fin parserStateCount)
#check (qAccept : Fin parserStateCount)
#check (qReject : Fin parserStateCount)
#check (parserRawStep :
  Fin parserStateCount → Option Bool →
    Fin parserStateCount × Option Bool × Move)
#check (machine : UniformTM)
#check (clock : Nat → Nat)
#check (rawBitstring :
  (raw : List Bool) → Bitstring raw.length)
#check (clockConfig :
  (raw : List Bool) →
    Config parserStateCount raw.length (clock raw.length))

/-! ## Exact structural theorem wrappers -/

theorem check_machine_rawStep
    (q : Fin parserStateCount)
    (scanned : Option Bool) :
    machine.rawStep q scanned = parserRawStep q scanned :=
  machine_rawStep q scanned

theorem check_parserRawStep_table :
    (∀ scanned,
      parserRawStep qStart scanned =
        match scanned with
        | none => (qReject, none, .stay)
        | some false => (qDataF, none, .right)
        | some true => (qWitnessT, none, .right)) ∧
    (∀ scanned,
      parserRawStep qDataF scanned =
        match scanned with
        | none => (qBackRejectF, none, .left)
        | some b => (qTagF, some b, .right)) ∧
    (∀ scanned,
      parserRawStep qTagF scanned =
        match scanned with
        | none => (qBackRejectF, none, .left)
        | some false => (qDataF, some false, .right)
        | some true => (qWitnessF, some true, .right)) ∧
    (∀ scanned,
      parserRawStep qWitnessF scanned =
        match scanned with
        | none => (qBackAcceptF, none, .left)
        | some b => (qWitnessF, some b, .right)) ∧
    (∀ scanned,
      parserRawStep qWitnessT scanned =
        match scanned with
        | none => (qBackAcceptT, none, .left)
        | some b => (qWitnessT, some b, .right)) ∧
    (∀ scanned,
      parserRawStep qBackAcceptF scanned =
        match scanned with
        | none => (qAccept, some false, .stay)
        | some b => (qBackAcceptF, some b, .left)) ∧
    (∀ scanned,
      parserRawStep qBackAcceptT scanned =
        match scanned with
        | none => (qAccept, some true, .stay)
        | some b => (qBackAcceptT, some b, .left)) ∧
    (∀ scanned,
      parserRawStep qBackRejectF scanned =
        match scanned with
        | none => (qReject, some false, .stay)
        | some b => (qBackRejectF, some b, .left)) ∧
    (∀ scanned,
      parserRawStep qAccept scanned = (qAccept, scanned, .stay)) ∧
    (∀ scanned,
      parserRawStep qReject scanned = (qReject, scanned, .stay)) :=
  parserRawStep_table

theorem check_machine_public_step_pins :
    (∀ (q : Fin parserStateCount) (scanned : Option Bool),
      q ≠ qAccept → q ≠ qReject →
        machine.step q scanned = parserRawStep q scanned) ∧
    (∀ scanned,
      machine.step qAccept scanned = (qAccept, scanned, .stay)) ∧
    (∀ scanned,
      machine.step qReject scanned = (qReject, scanned, .stay)) :=
  machine_public_step_pins

theorem check_machine_resource_pins :
    machine.stateCount = 10 ∧
    machine.start = qStart ∧
    machine.accept = qAccept ∧
    machine.reject = qReject ∧
    qStart.val = 0 ∧
    qDataF.val = 1 ∧
    qTagF.val = 2 ∧
    qWitnessF.val = 3 ∧
    qWitnessT.val = 4 ∧
    qBackAcceptF.val = 5 ∧
    qBackAcceptT.val = 6 ∧
    qBackRejectF.val = 7 ∧
    qAccept.val = 8 ∧
    qReject.val = 9 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 30 :=
  machine_resource_pins

theorem check_clock_tape_pins (N : Nat) :
    clock N = 2 * N + 1 ∧
    tapeLength N (clock N) = 3 * N + 2 :=
  clock_tape_pins N

end Pnp3.Tests.UniformV1FixedPairParserCore
