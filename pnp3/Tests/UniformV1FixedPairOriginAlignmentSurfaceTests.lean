import Complexity.Uniform.V1.FixedPairOriginAlignment

namespace Pnp3.Tests.UniformV1FixedPairOriginAlignmentSurfaceTests

open Pnp3.Complexity.Uniform.V1
open Pnp3.Complexity.Uniform.V1.PairEncoding
open Pnp3.Complexity.Uniform.V1.FixedPairOriginAlignment

abbrev check_alignmentStateCount : Nat := alignmentStateCount

def check_qStart : Fin alignmentStateCount := qStart

def check_qAccept : Fin alignmentStateCount := qAccept

def check_qReject : Fin alignmentStateCount := qReject

def check_machine : UniformTM := machine

def check_retag {N B : Nat}
    (c : Config FixedPairOriginShiftBootstrap.shiftStateCount N B) :
    Config alignmentStateCount N B :=
  retag c

def check_startConfig {n m : Nat} (B : Nat) (x : Bitstring n) (w : Bitstring m) :
    Config alignmentStateCount (pairLength n m) B :=
  startConfig B x w

def check_clock (n m : Nat) : Nat := clock n m

def check_alignedTape {n m : Nat} (B : Nat) (x : Bitstring n) (w : Bitstring m) :
    Fin (tapeLength (pairLength n m) B) → Option Bool :=
  alignedTape B x w

def check_finalConfig {n m : Nat} (B : Nat) (x : Bitstring n) (w : Bitstring m) :
    Config alignmentStateCount (pairLength n m) B :=
  finalConfig B x w

theorem check_raw_table (q : Fin alignmentStateCount) (s : Option Bool) :
    machine.rawStep q s =
      match q.val with
      | 0 => match s with
        | none => (⟨1, by decide⟩, none, .left)
        | some b => (qReject, some b, .stay)
      | 1 => match s with
        | none => (⟨2, by decide⟩, none, .left)
        | some b => (⟨2, by decide⟩, some b, .right)
      | 2 => (⟨3, by decide⟩, s, .right)
      | 3 => match s with
        | none => (⟨4, by decide⟩, none, .left)
        | some false => (⟨5, by decide⟩, none, .left)
        | some true => (⟨6, by decide⟩, none, .left)
      | 4 => match s with
        | none => (qReject, none, .stay)
        | some b => (⟨7, by decide⟩, some b, .left)
      | 5 => match s with
        | none => (qReject, none, .stay)
        | some b => (⟨8, by decide⟩, some b, .left)
      | 6 => match s with
        | none => (qReject, none, .stay)
        | some b => (⟨9, by decide⟩, some b, .left)
      | 7 => (⟨10, by decide⟩, s, .right)
      | 8 => (⟨11, by decide⟩, s, .right)
      | 9 => (⟨12, by decide⟩, s, .right)
      | 10 => match s with
        | none => (qAccept, none, .left)
        | some b => (⟨13, by decide⟩, some b, .right)
      | 11 => match s with
        | none => (qAccept, some false, .left)
        | some b => (⟨14, by decide⟩, some b, .right)
      | 12 => match s with
        | none => (qAccept, some true, .left)
        | some b => (⟨15, by decide⟩, some b, .right)
      | 13 => match s with
        | none => (⟨16, by decide⟩, none, .left)
        | some b => (qReject, some b, .stay)
      | 14 => match s with
        | none => (⟨16, by decide⟩, some false, .left)
        | some b => (qReject, some b, .stay)
      | 15 => match s with
        | none => (⟨16, by decide⟩, some true, .left)
        | some b => (qReject, some b, .stay)
      | 16 => match s with
        | none => (qReject, none, .stay)
        | some b => (⟨17, by decide⟩, some b, .left)
      | 17 => match s with
        | none => (⟨18, by decide⟩, none, .right)
        | some b => (⟨3, by decide⟩, some b, .right)
      | 18 => match s with
        | none => (qReject, none, .stay)
        | some false => (⟨19, by decide⟩, none, .left)
        | some true => (⟨20, by decide⟩, none, .left)
      | 19 => match s with
        | none => (⟨21, by decide⟩, some false, .right)
        | some b => (qReject, some b, .stay)
      | 20 => match s with
        | none => (⟨21, by decide⟩, some true, .right)
        | some b => (qReject, some b, .stay)
      | 21 => match s with
        | none => (⟨22, by decide⟩, none, .right)
        | some b => (qReject, some b, .stay)
      | 22 => match s with
        | none => (⟨23, by decide⟩, none, .left)
        | some false => (⟨19, by decide⟩, none, .left)
        | some true => (⟨20, by decide⟩, none, .left)
      | 23 => match s with
        | none => (⟨2, by decide⟩, none, .left)
        | some b => (qReject, some b, .stay)
      | 24 => (qAccept, s, .stay)
      | _ => (qReject, s, .stay) :=
  raw_table q s

theorem check_resource_pins :
    machine.stateCount = 26 ∧ machine.start = qStart ∧
    machine.accept = qAccept ∧ machine.reject = qReject ∧
    qStart.val = 0 ∧ qAccept.val = 24 ∧ qReject.val = 25 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 78 :=
  resource_pins

theorem check_handoff_exact {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    let p := FixedPairOriginShiftBootstrap.machine.run
      (FixedPairOriginShiftBootstrap.clock n m)
      (FixedPairOriginShiftBootstrap.startConfig B x w)
    p = FixedPairOriginShiftBootstrap.finalConfig B x w ∧
    p.state = FixedPairOriginShiftBootstrap.qAccept ∧
    (startConfig B x w).state = qStart ∧
    (startConfig B x w).head = p.head ∧
    (startConfig B x w).tape = p.tape :=
  handoff_exact x w

theorem check_clock_exact (n m : Nat) :
    clock n m = 2 + n * (10 * (n + m + 1) + 3) +
        (7 * ((n + m + 1) - 1) + 5) ∧
    clock n m = 10 * n * n + 10 * n * m + 20 * n + 7 * m + 7 ∧
    clock 0 0 = 7 ∧
    clock n m ≤ (10 * (n + m + 1) + 7) * (n + m + 1) +
      3 * (n + m + 1) :=
  clock_exact n m

theorem check_run_exact {n m : Nat} (B : Nat) (x : Bitstring n) (w : Bitstring m) :
    machine.run (clock n m) (startConfig B x w) = finalConfig B x w :=
  run_exact B x w

end Pnp3.Tests.UniformV1FixedPairOriginAlignmentSurfaceTests
