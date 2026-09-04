import Complexity.Uniform.V1.PairEncoding
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FinCases

/-!
# Fixed ten-state pair parser: executable finite core

This P2-3a module exposes one concrete parser, its exact raw transition table,
the bridge to the installed machine table, exact clock/resource pins, and
closed executable regressions.  It intentionally makes no claim about all
input lengths, arbitrary ambient budgets, parser/verifier composition,
relation verification, complexity-class inclusion, or circuit gates.
-/

namespace Pnp3.Complexity.Uniform.V1

namespace FixedPairParser

open PairEncoding

/-- Eight working controls followed by two public verdict controls. -/
abbrev parserStateCount : Nat := 10

def qStart : Fin parserStateCount :=
  ⟨0, by decide⟩

def qDataF : Fin parserStateCount :=
  ⟨1, by decide⟩

def qTagF : Fin parserStateCount :=
  ⟨2, by decide⟩

def qWitnessF : Fin parserStateCount :=
  ⟨3, by decide⟩

def qWitnessT : Fin parserStateCount :=
  ⟨4, by decide⟩

def qBackAcceptF : Fin parserStateCount :=
  ⟨5, by decide⟩

def qBackAcceptT : Fin parserStateCount :=
  ⟨6, by decide⟩

def qBackRejectF : Fin parserStateCount :=
  ⟨7, by decide⟩

def qAccept : Fin parserStateCount :=
  ⟨8, by decide⟩

def qReject : Fin parserStateCount :=
  ⟨9, by decide⟩

/-!
The first nonblank transition saves the first bit in finite control and writes
`none` at cell zero.  Forward and rewind transitions otherwise preserve the
scanned symbol.  The final rewind transition restores the saved marker.
-/
def parserRawStep
    (q : Fin parserStateCount)
    (scanned : Option Bool) :
    Fin parserStateCount × Option Bool × Move :=
  match q.val with
  | 0 =>
      match scanned with
      | none =>
          (qReject, none, .stay)
      | some false =>
          (qDataF, none, .right)
      | some true =>
          (qWitnessT, none, .right)
  | 1 =>
      match scanned with
      | none =>
          (qBackRejectF, none, .left)
      | some b =>
          (qTagF, some b, .right)
  | 2 =>
      match scanned with
      | none =>
          (qBackRejectF, none, .left)
      | some false =>
          (qDataF, some false, .right)
      | some true =>
          (qWitnessF, some true, .right)
  | 3 =>
      match scanned with
      | none =>
          (qBackAcceptF, none, .left)
      | some b =>
          (qWitnessF, some b, .right)
  | 4 =>
      match scanned with
      | none =>
          (qBackAcceptT, none, .left)
      | some b =>
          (qWitnessT, some b, .right)
  | 5 =>
      match scanned with
      | none =>
          (qAccept, some false, .stay)
      | some b =>
          (qBackAcceptF, some b, .left)
  | 6 =>
      match scanned with
      | none =>
          (qAccept, some true, .stay)
      | some b =>
          (qBackAcceptT, some b, .left)
  | 7 =>
      match scanned with
      | none =>
          (qReject, some false, .stay)
      | some b =>
          (qBackRejectF, some b, .left)
  | 8 =>
      (qAccept, scanned, .stay)
  | _ =>
      (qReject, scanned, .stay)

/-- The fixed ten-state standalone parser. -/
def machine : UniformTM where
  stateCount := parserStateCount
  start := qStart
  accept := qAccept
  reject := qReject
  accept_ne_reject := by decide
  rawStep := parserRawStep

/-- The displayed raw table is exactly the table installed in `machine`. -/
@[simp] theorem machine_rawStep
    (q : Fin parserStateCount)
    (scanned : Option Bool) :
    machine.rawStep q scanned = parserRawStep q scanned :=
  rfl

/-- One theorem pins every row of the displayed raw transition table. -/
theorem parserRawStep_table :
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
      parserRawStep qReject scanned = (qReject, scanned, .stay)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro scanned
    cases scanned with
    | none => rfl
    | some b => cases b <;> rfl
  · intro scanned
    cases scanned <;> rfl
  · intro scanned
    cases scanned with
    | none => rfl
    | some b => cases b <;> rfl
  · intro scanned
    cases scanned <;> rfl
  · intro scanned
    cases scanned <;> rfl
  · intro scanned
    cases scanned <;> rfl
  · intro scanned
    cases scanned <;> rfl
  · intro scanned
    cases scanned <;> rfl
  · intro scanned
    rfl
  · intro scanned
    rfl

/-- Public execution uses the raw table off terminals and absorbs both
terminals while preserving the exact scanned symbol. -/
theorem machine_public_step_pins :
    (∀ (q : Fin parserStateCount) (scanned : Option Bool),
      q ≠ qAccept → q ≠ qReject →
        machine.step q scanned = parserRawStep q scanned) ∧
    (∀ scanned,
      machine.step qAccept scanned = (qAccept, scanned, .stay)) ∧
    (∀ scanned,
      machine.step qReject scanned = (qReject, scanned, .stay)) := by
  constructor
  · intro q scanned hAccept hReject
    simp [UniformTM.step, machine, hAccept, hReject]
  constructor
  · intro scanned
    rfl
  · intro scanned
    rfl

/-- Exact proposed parser deadline in the actual raw input length. -/
def clock (N : Nat) : Nat :=
  2 * N + 1

/-- Closed finite-control and raw-table resource pins. -/
theorem machine_resource_pins :
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
    Fintype.card (Fin machine.stateCount × Option Bool) = 30 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, ?_⟩
  change Fintype.card (Fin 10 × Option Bool) = 30
  decide

/-- Exact clock and physical allocation when the clock is the tape budget. -/
theorem clock_tape_pins (N : Nat) :
    clock N = 2 * N + 1 ∧
    tapeLength N (clock N) = 3 * N + 2 := by
  constructor
  · rfl
  · unfold tapeLength clock
    omega

/-! ## Literal-list execution used only by the closed regressions -/

/-- Convert a literal list to the indexed raw-input API. -/
def rawBitstring (raw : List Bool) : Bitstring raw.length :=
  fun i => raw.get i

/-- Exact-deadline configuration at the exact parser clock. -/
def clockConfig
    (raw : List Bool) :
    Config parserStateCount raw.length (clock raw.length) :=
  machine.run (clock raw.length)
    (initialConfig machine (clock raw.length) (rawBitstring raw))

/-! ## Closed finite exact-run and restoration capstones -/

/-- Exact grammar classifications and literal verdicts for the required
finite malformed and valid words only. -/
theorem finite_exact_run_capstone :
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
    AcceptsAt machine 5 5 (rawBitstring [true, false]) := by
  refine ⟨rfl, ?_, rfl, ?_, rfl, ?_, rfl, ?_, rfl, ?_, rfl, ?_⟩
  · unfold RejectsAt
    decide
  · unfold RejectsAt
    decide
  · unfold RejectsAt
    decide
  · unfold AcceptsAt
    decide
  · unfold AcceptsAt
    decide
  · unfold AcceptsAt
    decide

/-- Closed valid and malformed samples both finish at head zero with the
entire allocated tape equal to their own exact-budget initial tape. -/
theorem finite_restoration_capstone :
    (clockConfig [true, false]).state = qAccept ∧
    (clockConfig [true, false]).head.val = 0 ∧
    (clockConfig [true, false]).tape =
      (initialConfig machine 5
        (rawBitstring [true, false])).tape ∧
    (clockConfig [false, true]).state = qReject ∧
    (clockConfig [false, true]).head.val = 0 ∧
    (clockConfig [false, true]).tape =
      (initialConfig machine 5
        (rawBitstring [false, true])).tape := by
  constructor
  · decide
  constructor
  · decide
  constructor
  · funext i
    fin_cases i <;> decide
  constructor
  · decide
  constructor
  · decide
  · funext i
    fin_cases i <;> decide

end FixedPairParser

end Pnp3.Complexity.Uniform.V1
