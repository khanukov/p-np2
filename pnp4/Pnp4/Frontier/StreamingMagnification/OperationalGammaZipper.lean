import Pnp4.Frontier.StreamingMagnification.OperationalUniformity
import Mathlib.Tactic.DeriveFintype

/-!
# A fixed-control value-preserving gamma zipper kernel

This file isolates the executable finite control for the sentinel format

```text
1 0^k 1 b_1 ... b_k suffix
^       ^
S       D
```

The leading `1` is an explicit left sentinel.  During cycle `j`, the current
payload bit is held in the finite control and its old cell is a temporary
`1` marker `C`.  Already visited bits use the alternating right code
`EncR(b) = b,0`.  A backward pass changes every `b,0` pair to `0,b`, moves
`D` one cell left, and a forward pass bubbles the held bit through those
pairs and restores the right code.  Thus payload data is never used as a
marker.

The transition table below is independent of `k` and of the input length.
This module deliberately exposes the executable kernel and the exact local
cycle layouts.  `OperationalGammaZipperGlobal` now supplies their complete
arbitrary-list induction and exact quadratic endpoint.
In particular, a zero payload bit beyond the finite input remains
indistinguishable from a blank tape cell in the repository's `Bool`-tape
model.

For a request stream, the last tag bit can serve as the sentinel of the first
gamma word.  On the final cycle the kernel deliberately leaves `C = 1` and
moves right.  That cell terminates the last alternating pair and is also the
sentinel immediately to the left of the next gamma word.  A surrounding
parser must hand control to its next scan phase at that point; this standalone
program instead enters its absorbing `done` state.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace OperationalGammaZipper

open Pnp3.Internal.PsubsetPpoly
open OperationalUniformity

/-! ## Fixed finite control -/

/--
Finite phases of the zipper.  Boolean constructor fields are genuine finite
control bits: `x` is the mobile payload bit, `b` is one temporarily carried
encoded bit, and `last` records whether the left probe saw the sentinel.
-/
inductive ZipperState where
  | sentinel
  | scanFirst
  | scanZeros
  | initRead
  | backStart (x : Bool)
  | backEnd (x : Bool)
  | backRead (x : Bool)
  | backWrite (x b : Bool)
  | backLeft (x : Bool)
  | placeDelimiter
  | probeBoundary
  | crossNewD (last : Bool)
  | loadMobile (last : Bool)
  | forwardBlockStart (last x : Bool)
  | forwardReadB (last x : Bool)
  | forwardBackZero (last x b : Bool)
  | forwardWriteOld (last x b : Bool)
  | forwardCrossZero (last x : Bool)
  | forwardCrossMobile (last x : Bool)
  | readNext
  | done
  | reject
  deriving DecidableEq, Fintype

/--
The value-preserving alternating-pair zipper.

Unexpected symbols in phases whose symbol is forced by the zipper invariant
enter the absorbing `reject` state.  Data-reading phases branch on either
Boolean value and store it only in the finite control.
-/
def gammaZipper : OperationalTM where
  state := ZipperState
  stateFintype := inferInstance
  stateDecEq := inferInstance
  start := .sentinel
  step := fun state scanned =>
    match state with
    | .sentinel =>
        if scanned then (.scanFirst, true, Move.right)
        else (.reject, false, Move.stay)
    | .scanFirst =>
        if scanned then (.done, true, Move.right)
        else (.scanZeros, false, Move.right)
    | .scanZeros =>
        if scanned then (.initRead, true, Move.right)
        else (.scanZeros, false, Move.right)
    | .initRead => (.backStart scanned, true, Move.stay)
    | .backStart x =>
        if scanned then (.backEnd x, true, Move.left)
        else (.reject, false, Move.stay)
    | .backEnd x =>
        if scanned then (.placeDelimiter, x, Move.left)
        else (.backRead x, false, Move.left)
    | .backRead x => (.backWrite x scanned, false, Move.right)
    | .backWrite x b =>
        if scanned then (.reject, true, Move.stay)
        else (.backLeft x, b, Move.left)
    | .backLeft x =>
        if scanned then (.reject, true, Move.stay)
        else (.backEnd x, false, Move.left)
    | .placeDelimiter =>
        if scanned then (.reject, true, Move.stay)
        else (.probeBoundary, true, Move.left)
    | .probeBoundary =>
        (.crossNewD scanned, scanned, Move.right)
    | .crossNewD last =>
        if scanned then (.loadMobile last, true, Move.right)
        else (.reject, false, Move.stay)
    | .loadMobile last =>
        (.forwardBlockStart last scanned, scanned, Move.right)
    | .forwardBlockStart last x =>
        if scanned then
          if last then (.done, true, Move.right)
          else (.readNext, false, Move.right)
        else
          (.forwardReadB last x, false, Move.right)
    | .forwardReadB last x =>
        (.forwardBackZero last x scanned, x, Move.left)
    | .forwardBackZero last x b =>
        if scanned then (.reject, true, Move.stay)
        else (.forwardWriteOld last x b, false, Move.left)
    | .forwardWriteOld last x b =>
        if scanned == x then (.forwardCrossZero last x, b, Move.right)
        else (.reject, scanned, Move.stay)
    | .forwardCrossZero last x =>
        if scanned then (.reject, true, Move.stay)
        else (.forwardCrossMobile last x, false, Move.right)
    | .forwardCrossMobile last x =>
        if scanned == x then (.forwardBlockStart last x, x, Move.right)
        else (.reject, scanned, Move.stay)
    | .readNext => (.backStart scanned, true, Move.stay)
    | .done => (.done, scanned, Move.stay)
    | .reject => (.reject, scanned, Move.stay)
  exponent := 3
  output := fun state => state == .done

/-- The program has one fixed 57-state control, independently of all data. -/
@[simp] theorem gammaZipper_state_card :
    Fintype.card gammaZipper.state = 57 := by
  decide

/-- The chosen cubic canonical clock.  `OperationalGammaZipperGlobal` proves
the exact useful quadratic trace, and `OperationalGammaZipperActual` proves
that the absorbing endpoint persists to this longer repository clock. -/
@[simp] theorem gammaZipper_clock (inputLength : Nat) :
    gammaZipper.executionTM.runTime inputLength = inputLength ^ 3 + 3 :=
  rfl

/-! ## Proof-friendly natural-coordinate execution -/

/-- A single-cell write on an unbounded natural-coordinate tape. -/
def writeNat (tape : Nat -> Bool) (position : Nat) (bit : Bool) :
    Nat -> Bool :=
  fun query => if query = position then bit else tape query

@[simp] theorem writeNat_same (tape : Nat -> Bool) (position : Nat)
    (bit : Bool) :
    writeNat tape position bit position = bit := by
  simp [writeNat]

@[simp] theorem writeNat_other (tape : Nat -> Bool) (position query : Nat)
    (bit : Bool) (hne : query ≠ position) :
    writeNat tape position bit query = tape query := by
  simp [writeNat, hne]

@[simp] theorem writeNat_eq_self_of_eq {tape : Nat -> Bool} {position : Nat}
    {bit : Bool} (hbit : tape position = bit) :
    writeNat tape position bit = tape := by
  funext query
  by_cases hquery : query = position
  · subst query
    simp [writeNat, hbit]
  · simp [writeNat, hquery]

@[simp] theorem writeNat_current (tape : Nat -> Bool) (position : Nat) :
    writeNat tape position (tape position) = tape :=
  writeNat_eq_self_of_eq rfl

@[simp] theorem writeNat_write_same (tape : Nat -> Bool) (position : Nat)
    (first second : Bool) :
    writeNat (writeNat tape position first) position second =
      writeNat tape position second := by
  funext query
  by_cases hquery : query = position <;> simp [writeNat, hquery]

theorem writeNat_write_comm (tape : Nat -> Bool) (left right : Nat)
    (leftBit rightBit : Bool) (hne : left ≠ right) :
    writeNat (writeNat tape left leftBit) right rightBit =
      writeNat (writeNat tape right rightBit) left leftBit := by
  funext query
  by_cases hleft : query = left
  · subst query
    simp [writeNat, hne]
  · by_cases hright : query = right
    · subst query
      simp [writeNat, hleft]
    · simp [writeNat, hleft, hright]

/-- Natural-coordinate movement with the repository's reflecting left edge. -/
def moveNat (position : Nat) : Move -> Nat
  | .left => position - 1
  | .stay => position
  | .right => position + 1

/-- A proof facade carrying exactly the data visible to the operational step. -/
structure NatConfig where
  state : ZipperState
  head : Nat
  tape : Nat -> Bool

/-- One natural-coordinate execution of the same fixed transition table. -/
def natStep (config : NatConfig) : NatConfig :=
  let result := gammaZipper.step config.state (config.tape config.head)
  { state := result.1
    head := moveNat config.head result.2.2
    tape := writeNat config.tape config.head result.2.1 }

/-- Iterate the exact fixed control on natural coordinates. -/
def natRun (config : NatConfig) (steps : Nat) : NatConfig :=
  Nat.iterate natStep steps config

@[simp] theorem natRun_zero (config : NatConfig) : natRun config 0 = config :=
  rfl

theorem natRun_succ (config : NatConfig) (steps : Nat) :
    natRun config (steps + 1) = natStep (natRun config steps) := by
  unfold natRun
  exact Function.iterate_succ_apply' natStep steps config

theorem natRun_add (config : NatConfig) (first second : Nat) :
    natRun config (first + second) = natRun (natRun config first) second := by
  unfold natRun
  rw [Nat.add_comm, Function.iterate_add_apply]

/-! Exact successful one-step rules.  These are the executable obligations
used by the local multi-step zipper proofs below. -/

@[simp] theorem natStep_sentinel_one (head : Nat) (tape : Nat -> Bool)
    (hbit : tape head = true) :
    natStep ⟨.sentinel, head, tape⟩ =
      ⟨.scanFirst, head + 1, tape⟩ := by
  simp [natStep, gammaZipper, hbit, moveNat]

@[simp] theorem natStep_scanFirst_one (head : Nat) (tape : Nat -> Bool)
    (hbit : tape head = true) :
    natStep ⟨.scanFirst, head, tape⟩ =
      ⟨.done, head + 1, tape⟩ := by
  simp [natStep, gammaZipper, hbit, moveNat]

@[simp] theorem natStep_scanFirst_zero (head : Nat) (tape : Nat -> Bool)
    (hbit : tape head = false) :
    natStep ⟨.scanFirst, head, tape⟩ =
      ⟨.scanZeros, head + 1, tape⟩ := by
  simp [natStep, gammaZipper, hbit, moveNat]

@[simp] theorem natStep_scanZeros_zero (head : Nat) (tape : Nat -> Bool)
    (hbit : tape head = false) :
    natStep ⟨.scanZeros, head, tape⟩ =
      ⟨.scanZeros, head + 1, tape⟩ := by
  simp [natStep, gammaZipper, hbit, moveNat]

@[simp] theorem natStep_scanZeros_one (head : Nat) (tape : Nat -> Bool)
    (hbit : tape head = true) :
    natStep ⟨.scanZeros, head, tape⟩ =
      ⟨.initRead, head + 1, tape⟩ := by
  simp [natStep, gammaZipper, hbit, moveNat]

@[simp] theorem natStep_initRead (head : Nat) (tape : Nat -> Bool) :
    natStep ⟨.initRead, head, tape⟩ =
      ⟨.backStart (tape head), head, writeNat tape head true⟩ := by
  simp [natStep, gammaZipper, moveNat]

@[simp] theorem natStep_backStart_one (x : Bool) (head : Nat)
    (tape : Nat -> Bool) (hbit : tape head = true) :
    natStep ⟨.backStart x, head, tape⟩ =
      ⟨.backEnd x, head - 1, tape⟩ := by
  simp [natStep, gammaZipper, hbit, moveNat]

@[simp] theorem natStep_backEnd_zero (x : Bool) (head : Nat)
    (tape : Nat -> Bool) (hbit : tape head = false) :
    natStep ⟨.backEnd x, head, tape⟩ =
      ⟨.backRead x, head - 1, tape⟩ := by
  simp [natStep, gammaZipper, hbit, moveNat]

@[simp] theorem natStep_backEnd_one (x : Bool) (head : Nat)
    (tape : Nat -> Bool) (hbit : tape head = true) :
    natStep ⟨.backEnd x, head, tape⟩ =
      ⟨.placeDelimiter, head - 1, writeNat tape head x⟩ := by
  simp [natStep, gammaZipper, hbit, moveNat]

@[simp] theorem natStep_backRead (x : Bool) (head : Nat)
    (tape : Nat -> Bool) :
    natStep ⟨.backRead x, head, tape⟩ =
      ⟨.backWrite x (tape head), head + 1,
        writeNat tape head false⟩ := by
  simp [natStep, gammaZipper, moveNat]

@[simp] theorem natStep_backWrite_zero (x b : Bool) (head : Nat)
    (tape : Nat -> Bool) (hbit : tape head = false) :
    natStep ⟨.backWrite x b, head, tape⟩ =
      ⟨.backLeft x, head - 1, writeNat tape head b⟩ := by
  simp [natStep, gammaZipper, hbit, moveNat]

@[simp] theorem natStep_backLeft_zero (x : Bool) (head : Nat)
    (tape : Nat -> Bool) (hbit : tape head = false) :
    natStep ⟨.backLeft x, head, tape⟩ =
      ⟨.backEnd x, head - 1, tape⟩ := by
  simp [natStep, gammaZipper, hbit, moveNat]

@[simp] theorem natStep_placeDelimiter_zero (head : Nat)
    (tape : Nat -> Bool) (hbit : tape head = false) :
    natStep ⟨.placeDelimiter, head, tape⟩ =
      ⟨.probeBoundary, head - 1, writeNat tape head true⟩ := by
  simp [natStep, gammaZipper, hbit, moveNat]

@[simp] theorem natStep_probeBoundary (head : Nat) (tape : Nat -> Bool) :
    natStep ⟨.probeBoundary, head, tape⟩ =
      ⟨.crossNewD (tape head), head + 1, tape⟩ := by
  simp [natStep, gammaZipper, moveNat]

@[simp] theorem natStep_crossNewD_one (last : Bool) (head : Nat)
    (tape : Nat -> Bool) (hbit : tape head = true) :
    natStep ⟨.crossNewD last, head, tape⟩ =
      ⟨.loadMobile last, head + 1, tape⟩ := by
  simp [natStep, gammaZipper, hbit, moveNat]

@[simp] theorem natStep_loadMobile (last : Bool) (head : Nat)
    (tape : Nat -> Bool) :
    natStep ⟨.loadMobile last, head, tape⟩ =
      ⟨.forwardBlockStart last (tape head), head + 1, tape⟩ := by
  simp [natStep, gammaZipper, moveNat]

@[simp] theorem natStep_forwardBlockStart_zero (last x : Bool)
    (head : Nat) (tape : Nat -> Bool) (hbit : tape head = false) :
    natStep ⟨.forwardBlockStart last x, head, tape⟩ =
      ⟨.forwardReadB last x, head + 1, tape⟩ := by
  simp [natStep, gammaZipper, hbit, moveNat]

@[simp] theorem natStep_forwardBlockStart_moreC (x : Bool)
    (head : Nat) (tape : Nat -> Bool) (hbit : tape head = true) :
    natStep ⟨.forwardBlockStart false x, head, tape⟩ =
      ⟨.readNext, head + 1, writeNat tape head false⟩ := by
  simp [natStep, gammaZipper, hbit, moveNat]

@[simp] theorem natStep_forwardBlockStart_lastC (x : Bool)
    (head : Nat) (tape : Nat -> Bool) (hbit : tape head = true) :
    natStep ⟨.forwardBlockStart true x, head, tape⟩ =
      ⟨.done, head + 1, tape⟩ := by
  simp [natStep, gammaZipper, hbit, moveNat]

@[simp] theorem natStep_forwardReadB (last x : Bool) (head : Nat)
    (tape : Nat -> Bool) :
    natStep ⟨.forwardReadB last x, head, tape⟩ =
      ⟨.forwardBackZero last x (tape head), head - 1,
        writeNat tape head x⟩ := by
  simp [natStep, gammaZipper, moveNat]

@[simp] theorem natStep_forwardBackZero_zero (last x b : Bool)
    (head : Nat) (tape : Nat -> Bool) (hbit : tape head = false) :
    natStep ⟨.forwardBackZero last x b, head, tape⟩ =
      ⟨.forwardWriteOld last x b, head - 1, tape⟩ := by
  simp [natStep, gammaZipper, hbit, moveNat]

@[simp] theorem natStep_forwardWriteOld (last x b : Bool)
    (head : Nat) (tape : Nat -> Bool) (hbit : tape head = x) :
    natStep ⟨.forwardWriteOld last x b, head, tape⟩ =
      ⟨.forwardCrossZero last x, head + 1, writeNat tape head b⟩ := by
  simp [natStep, gammaZipper, hbit, moveNat]

@[simp] theorem natStep_forwardCrossZero_zero (last x : Bool)
    (head : Nat) (tape : Nat -> Bool) (hbit : tape head = false) :
    natStep ⟨.forwardCrossZero last x, head, tape⟩ =
      ⟨.forwardCrossMobile last x, head + 1, tape⟩ := by
  simp [natStep, gammaZipper, hbit, moveNat]

@[simp] theorem natStep_forwardCrossMobile (last x : Bool)
    (head : Nat) (tape : Nat -> Bool) (hbit : tape head = x) :
    natStep ⟨.forwardCrossMobile last x, head, tape⟩ =
      ⟨.forwardBlockStart last x, head + 1, tape⟩ := by
  simp [natStep, gammaZipper, hbit, moveNat]

@[simp] theorem natStep_readNext (head : Nat) (tape : Nat -> Bool) :
    natStep ⟨.readNext, head, tape⟩ =
      ⟨.backStart (tape head), head, writeNat tape head true⟩ := by
  simp [natStep, gammaZipper, moveNat]

@[simp] theorem natStep_done (head : Nat) (tape : Nat -> Bool) :
    natStep ⟨.done, head, tape⟩ = ⟨.done, head, tape⟩ := by
  simp [natStep, gammaZipper, moveNat]

/-! ## Exact boundary layouts -/

/-- Alternating right-oriented encoding: every data bit is followed by `0`. -/
def encR : List Bool -> List Bool
  | [] => []
  | bit :: bits => bit :: false :: encR bits

@[simp] theorem encR_nil : encR [] = [] := rfl

@[simp] theorem encR_cons (bit : Bool) (bits : List Bool) :
    encR (bit :: bits) = bit :: false :: encR bits := rfl

@[simp] theorem encR_length (bits : List Bool) :
    (encR bits).length = 2 * bits.length := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp [encR, ih, Nat.mul_succ]

/-- Put a finite frame in front of an arbitrary untouched suffix. -/
def framedTape (frame : List Bool) (suffix : Nat -> Bool) : Nat -> Bool :=
  fun position =>
    match frame[position]? with
    | some bit => bit
    | none => suffix (position - frame.length)

/-- Inside the finite frame, `framedTape` is exactly list lookup. -/
theorem framedTape_prefix (frame : List Bool) (suffix : Nat -> Bool)
    (position : Nat) (hposition : position < frame.length) :
    framedTape frame suffix position = frame[position] := by
  unfold framedTape
  rw [List.getElem?_eq_getElem hposition]

/-- At and beyond the frame boundary, the supplied suffix is untouched. -/
theorem framedTape_suffix (frame : List Bool) (suffix : Nat -> Bool)
    (offset : Nat) :
    framedTape frame suffix (frame.length + offset) = suffix offset := by
  simp [framedTape]

/-- Input frame for the explicit-sentinel convention. -/
def initialFrame (k : Nat) (payload : List Bool) : List Bool :=
  true :: List.replicate k false ++ true :: payload

@[simp] theorem initialFrame_length (k : Nat) (payload : List Bool) :
    (initialFrame k payload).length = k + payload.length + 2 := by
  simp [initialFrame]
  omega

/--
Cycle-boundary frame.  `processed` is already pair-coded, `current` lives in
the control while its tape cell contains `C = 1`, and `unprocessed` is still
raw.  The equation `remaining + processed.length = k` is the unary-count
conservation law.
-/
def cycleFrame (remaining : Nat) (processed unprocessed : List Bool) :
    List Bool :=
  true :: List.replicate remaining false ++
    true :: encR processed ++ true :: unprocessed

@[simp] theorem cycleFrame_length (remaining : Nat)
    (processed unprocessed : List Bool) :
    (cycleFrame remaining processed unprocessed).length =
      remaining + 2 * processed.length + unprocessed.length + 3 := by
  simp [cycleFrame, encR_length]
  omega

@[simp] theorem cycleFrame_getElem?_sentinel (remaining : Nat)
    (processed unprocessed : List Bool) :
    (cycleFrame remaining processed unprocessed)[0]? = some true := by
  simp [cycleFrame]

@[simp] theorem cycleFrame_getElem?_delimiter (remaining : Nat)
    (processed unprocessed : List Bool) :
    (cycleFrame remaining processed unprocessed)[remaining + 1]? =
      some true := by
  simp [cycleFrame]

@[simp] theorem framedCycle_sentinel (remaining : Nat)
    (processed unprocessed : List Bool) (suffix : Nat -> Bool) :
    framedTape (cycleFrame remaining processed unprocessed) suffix 0 = true := by
  unfold framedTape
  rw [cycleFrame_getElem?_sentinel]

@[simp] theorem framedCycle_delimiter (remaining : Nat)
    (processed unprocessed : List Bool) (suffix : Nat -> Bool) :
    framedTape (cycleFrame remaining processed unprocessed) suffix
      (remaining + 1) = true := by
  unfold framedTape
  rw [cycleFrame_getElem?_delimiter]

/-- Exact semantic invariant at the entry to a backward pass. -/
def GammaZipperInvariant (k : Nat) (payload : List Bool)
    (state : ZipperState) (head : Nat) (tape : Nat -> Bool)
    (suffix : Nat -> Bool) (remaining : Nat) (processed : List Bool)
    (current : Bool) (unprocessed : List Bool) : Prop :=
  payload.length = k /\
    payload = processed ++ current :: unprocessed /\
    remaining + processed.length = k /\
    state = .backStart current /\
    head = 1 + remaining + 1 + (encR processed).length /\
    tape = framedTape (cycleFrame remaining processed unprocessed) suffix

/-- The three semantic equations in the invariant force exact frame length. -/
theorem cycleFrame_length_eq_total {k : Nat} {payload processed unprocessed : List Bool}
    {remaining : Nat} {current : Bool}
    (hlength : payload.length = k)
    (hsplit : payload = processed ++ current :: unprocessed)
    (hcount : remaining + processed.length = k) :
    (cycleFrame remaining processed unprocessed).length = 2 * k + 2 := by
  have hpayload : processed.length + 1 + unprocessed.length = k := by
    calc
      processed.length + 1 + unprocessed.length = payload.length := by
        rw [hsplit]
        simp
        omega
      _ = k := hlength
  rw [cycleFrame_length]
  omega

/-- Invariant-specialized form of exact footprint conservation. -/
theorem GammaZipperInvariant.frame_length {k : Nat} {payload : List Bool}
    {state : ZipperState} {head : Nat} {tape suffix : Nat -> Bool}
    {remaining : Nat} {processed : List Bool} {current : Bool}
    {unprocessed : List Bool}
    (hinvariant : GammaZipperInvariant k payload state head tape suffix
      remaining processed current unprocessed) :
    (cycleFrame remaining processed unprocessed).length = 2 * k + 2 := by
  exact cycleFrame_length_eq_total hinvariant.1 hinvariant.2.1
    hinvariant.2.2.1

/-- The left probe sees the sentinel exactly on the last payload cycle. -/
theorem remaining_eq_one_iff_unprocessed_nil {k : Nat}
    {payload processed unprocessed : List Bool} {remaining : Nat}
    {current : Bool}
    (hlength : payload.length = k)
    (hsplit : payload = processed ++ current :: unprocessed)
    (hcount : remaining + processed.length = k) :
    remaining = 1 <-> unprocessed = [] := by
  have hpayload : processed.length + 1 + unprocessed.length = k := by
    calc
      processed.length + 1 + unprocessed.length = payload.length := by
        rw [hsplit]
        simp
        omega
      _ = k := hlength
  constructor
  · intro hremaining
    apply List.eq_nil_of_length_eq_zero
    omega
  · intro hunprocessed
    subst unprocessed
    simp at hpayload
    omega

/--
Final value encoding.  All but the last payload bit use `b,0`; the final bit
uses `b,1`, so its second cell is also the sentinel for a following gamma
word.  The empty payload needs no additional cells.
-/
def encFinal : List Bool -> List Bool
  | [] => []
  | [bit] => [bit, true]
  | bit :: next :: bits => bit :: false :: encFinal (next :: bits)

@[simp] theorem encFinal_length (payload : List Bool) :
    (encFinal payload).length = 2 * payload.length := by
  induction payload with
  | nil => rfl
  | cons bit tail ih =>
      cases tail with
      | nil => rfl
      | cons next bits =>
          simp [encFinal, ih, Nat.mul_add,
            Nat.add_comm, Nat.add_left_comm]
          omega

/-- A decoded gamma field's delimiter, value encoding, and trailing sentinel. -/
def encChain (payload : List Bool) : List Bool :=
  true :: encFinal payload

/--
Successful standalone frame.  The first cell is the original sentinel;
`encChain` starts with the moved delimiter and ends at the next sentinel.
For `k = 0`, the delimiter itself is already that trailing sentinel.
-/
def finalFrame (payload : List Bool) : List Bool :=
  true :: encChain payload

/-- Exact expected endpoint, with the head at the first untouched suffix cell. -/
def ExpectedFinalLayout (payload : List Bool) (state : ZipperState)
    (head : Nat) (tape : Nat -> Bool) (suffix : Nat -> Bool) : Prop :=
  state = .done /\
    head = (finalFrame payload).length /\
    tape = framedTape (finalFrame payload) suffix

@[simp] theorem finalFrame_length (payload : List Bool) :
    (finalFrame payload).length = 2 * payload.length + 2 := by
  simp [finalFrame, encChain]

/-- Every valid initial frame has the same `2*k+2` footprint. -/
theorem initialFrame_length_eq_total {k : Nat} {payload : List Bool}
    (hlength : payload.length = k) :
    (initialFrame k payload).length = 2 * k + 2 := by
  rw [initialFrame_length, hlength]
  omega

/-! ## Spatial predicates for composing the local kernels -/

/-- A consecutive block of right-oriented pairs `b,0` beginning at `start`. -/
def RightPairsAt (tape : Nat -> Bool) (start : Nat) : List Bool -> Prop
  | [] => True
  | bit :: bits =>
      tape start = bit /\
      tape (start + 1) = false /\
      RightPairsAt tape (start + 2) bits

/-- A consecutive block of backward-oriented pairs `0,b` beginning at `start`. -/
def LeftPairsAt (tape : Nat -> Bool) (start : Nat) : List Bool -> Prop
  | [] => True
  | bit :: bits =>
      tape start = false /\
      tape (start + 1) = bit /\
      LeftPairsAt tape (start + 2) bits

/-- Two tapes agree away from the half-open interval `[start, finish)`. -/
def EqOutside (after before : Nat -> Bool) (start finish : Nat) : Prop :=
  forall position, position < start \/ finish <= position ->
    after position = before position

@[simp] theorem rightPairsAt_nil (tape : Nat -> Bool) (start : Nat) :
    RightPairsAt tape start [] := by
  trivial

@[simp] theorem rightPairsAt_cons (tape : Nat -> Bool) (start : Nat)
    (bit : Bool) (bits : List Bool) :
    RightPairsAt tape start (bit :: bits) <->
      tape start = bit /\ tape (start + 1) = false /\
        RightPairsAt tape (start + 2) bits := by
  rfl

@[simp] theorem leftPairsAt_nil (tape : Nat -> Bool) (start : Nat) :
    LeftPairsAt tape start [] := by
  trivial

@[simp] theorem leftPairsAt_cons (tape : Nat -> Bool) (start : Nat)
    (bit : Bool) (bits : List Bool) :
    LeftPairsAt tape start (bit :: bits) <->
      tape start = false /\ tape (start + 1) = bit /\
        LeftPairsAt tape (start + 2) bits := by
  rfl

theorem rightPairsAt_append (tape : Nat -> Bool) (start : Nat)
    (left right : List Bool) :
    RightPairsAt tape start (left ++ right) <->
      RightPairsAt tape start left /\
        RightPairsAt tape (start + 2 * left.length) right := by
  induction left generalizing start with
  | nil => simp
  | cons bit bits ih =>
      simp only [List.cons_append, rightPairsAt_cons, List.length_cons]
      rw [ih]
      constructor
      · rintro ⟨hbit, hzero, hbits, hright⟩
        refine ⟨⟨hbit, hzero, hbits⟩, ?_⟩
        convert hright using 1 <;> simp [Nat.mul_succ] <;> omega
      · rintro ⟨⟨hbit, hzero, hbits⟩, hright⟩
        refine ⟨hbit, hzero, hbits, ?_⟩
        convert hright using 1 <;> simp [Nat.mul_succ] <;> omega

theorem leftPairsAt_append (tape : Nat -> Bool) (start : Nat)
    (left right : List Bool) :
    LeftPairsAt tape start (left ++ right) <->
      LeftPairsAt tape start left /\
        LeftPairsAt tape (start + 2 * left.length) right := by
  induction left generalizing start with
  | nil => simp
  | cons bit bits ih =>
      simp only [List.cons_append, leftPairsAt_cons, List.length_cons]
      rw [ih]
      constructor
      · rintro ⟨hzero, hbit, hbits, hright⟩
        refine ⟨⟨hzero, hbit, hbits⟩, ?_⟩
        convert hright using 1 <;> simp [Nat.mul_succ] <;> omega
      · rintro ⟨⟨hzero, hbit, hbits⟩, hright⟩
        refine ⟨hzero, hbit, hbits, ?_⟩
        convert hright using 1 <;> simp [Nat.mul_succ] <;> omega

@[simp] theorem eqOutside_refl (tape : Nat -> Bool) (start finish : Nat) :
    EqOutside tape tape start finish := by
  intro position hposition
  rfl

theorem rightPairsAt_congr {before after : Nat -> Bool} {start : Nat}
    {bits : List Bool}
    (hagrees : forall position, start <= position ->
      position < start + 2 * bits.length -> after position = before position)
    (hpairs : RightPairsAt before start bits) :
    RightPairsAt after start bits := by
  induction bits generalizing start with
  | nil => trivial
  | cons bit bits ih =>
      rcases hpairs with ⟨hbit, hzero, hpairs⟩
      refine ⟨?_, ?_, ih ?_ hpairs⟩
      · exact (hagrees start (by omega) (by simp)).trans hbit
      · exact (hagrees (start + 1) (by omega) (by simp; omega)).trans hzero
      · intro position hstart hfinish
        apply hagrees position (by omega)
        simp at hfinish ⊢
        omega

theorem leftPairsAt_congr {before after : Nat -> Bool} {start : Nat}
    {bits : List Bool}
    (hagrees : forall position, start <= position ->
      position < start + 2 * bits.length -> after position = before position)
    (hpairs : LeftPairsAt before start bits) :
    LeftPairsAt after start bits := by
  induction bits generalizing start with
  | nil => trivial
  | cons bit bits ih =>
      rcases hpairs with ⟨hzero, hbit, hpairs⟩
      refine ⟨?_, ?_, ih ?_ hpairs⟩
      · exact (hagrees start (by omega) (by simp)).trans hzero
      · exact (hagrees (start + 1) (by omega) (by simp; omega)).trans hbit
      · intro position hstart hfinish
        apply hagrees position (by omega)
        simp at hfinish ⊢
        omega

/-! ## Exact local zipper transformations -/

/--
Four real machine steps convert one backward-facing right pair `b,0` into
`0,b`, move to the preceding pair end, and retain the mobile bit `x` solely
in finite control.
-/
theorem natRun_backwardPair (x b : Bool) (left : Nat)
    (tape : Nat -> Bool) (hleft : tape left = b)
    (hend : tape (left + 1) = false) :
    natRun ⟨.backEnd x, left + 1, tape⟩ 4 =
      ⟨.backEnd x, left - 1,
        writeNat (writeNat tape left false) (left + 1) b⟩ := by
  simp [natRun, Function.iterate_succ_apply', natStep, gammaZipper,
    moveNat, writeNat, hleft, hend]

/--
Five real steps overwrite the old delimiter with `x`, install the delimiter
one cell to its left, inspect the cell before it (sentinel iff `last`), cross
the new delimiter, reload `x`, and arrive at the first forward block.
-/
theorem natRun_shiftDelimiter (x last : Bool) (delimiter : Nat)
    (tape : Nat -> Bool) (hdelimiter : 2 <= delimiter)
    (hD : tape delimiter = true)
    (hnew : tape (delimiter - 1) = false)
    (hprobe : tape (delimiter - 2) = last) :
    natRun ⟨.backEnd x, delimiter, tape⟩ 5 =
      ⟨.forwardBlockStart last x, delimiter + 1,
        writeNat (writeNat tape delimiter x) (delimiter - 1) true⟩ := by
  have hDnew : delimiter ≠ delimiter - 1 := by omega
  have hnewD : delimiter - 1 ≠ delimiter := by omega
  have hprobeD : delimiter - 2 ≠ delimiter := by omega
  have hprobeNew : delimiter - 2 ≠ delimiter - 1 := by omega
  have hsub : delimiter - 1 - 1 = delimiter - 2 := by omega
  have hadd : delimiter - 1 + 1 = delimiter := by omega
  have hprobeAdd : delimiter - 2 + 1 = delimiter - 1 := by omega
  simp [natRun, Function.iterate_succ_apply', natStep, gammaZipper,
    moveNat, writeNat, hD, hnew, hprobe, hDnew, hnewD, hprobeD,
    hprobeNew, hsub, hadd, hprobeAdd]

/--
Six real steps implement the forward bubble

```text
x 0 b  ->  b 0 x
```

and place the head at the next block start.  Both payload bits are preserved.
-/
theorem natRun_forwardBubble (last x b : Bool) (mobile : Nat)
    (tape : Nat -> Bool) (hmobile : tape mobile = x)
    (hzero : tape (mobile + 1) = false)
    (hbit : tape (mobile + 2) = b) :
    natRun ⟨.forwardBlockStart last x, mobile + 1, tape⟩ 6 =
      ⟨.forwardBlockStart last x, mobile + 3,
        writeNat (writeNat tape (mobile + 2) x) mobile b⟩ := by
  have h20 : mobile + 2 ≠ mobile := by omega
  simp [natRun, Function.iterate_succ_apply', natStep, gammaZipper,
    moveNat, writeNat, hmobile, hzero, hbit, h20]

/-- On a nonfinal `C`, one step writes the regular zero pair separator. -/
theorem natRun_nonfinalC (x : Bool) (marker : Nat) (tape : Nat -> Bool)
    (hmarker : tape marker = true) :
    natRun ⟨.forwardBlockStart false x, marker, tape⟩ 1 =
      ⟨.readNext, marker + 1, writeNat tape marker false⟩ := by
  simpa [natRun] using
    natStep_forwardBlockStart_moreC x marker tape hmarker

/--
On the final `C`, one step preserves the `1`, enters `done`, and moves to the
first suffix cell.  The preserved `1` is the sentinel for a subsequent field.
-/
theorem natRun_finalC (x : Bool) (marker : Nat) (tape : Nat -> Bool)
    (hmarker : tape marker = true) :
    natRun ⟨.forwardBlockStart true x, marker, tape⟩ 1 =
      ⟨.done, marker + 1, tape⟩ := by
  simpa [natRun] using
    natStep_forwardBlockStart_lastC x marker tape hmarker

/-! ## Arbitrary-list composition of the zipper kernels -/

/--
Compose `natRun_backwardPair` over an arbitrary right-oriented pair block.
The theorem records both the complete left-oriented output block and the
fact that no cell outside that block changes.
 -/
theorem natRun_backwardPairs (x : Bool) (delimiter : Nat)
    (bits : List Bool) (tape : Nat -> Bool)
    (hpairs : RightPairsAt tape (delimiter + 1) bits) :
    exists resultTape,
      natRun ⟨.backEnd x, delimiter + 2 * bits.length, tape⟩
          (4 * bits.length) =
        ⟨.backEnd x, delimiter, resultTape⟩ /\
      LeftPairsAt resultTape (delimiter + 1) bits /\
      EqOutside resultTape tape (delimiter + 1)
        (delimiter + 1 + 2 * bits.length) := by
  induction bits using List.reverseRecOn generalizing tape with
  | nil =>
      refine ⟨tape, ?_, by trivial, eqOutside_refl _ _ _⟩
      simp [natRun]
  | append_singleton prior bit ih =>
      have hsplit :=
        (rightPairsAt_append tape (delimiter + 1) prior [bit]).mp hpairs
      have hprior : RightPairsAt tape (delimiter + 1) prior := hsplit.1
      have hlast :
          tape (delimiter + 1 + 2 * prior.length) = bit /\
          tape (delimiter + 1 + 2 * prior.length + 1) = false := by
        simpa using hsplit.2
      let pairTape :=
        writeNat
          (writeNat tape (delimiter + 1 + 2 * prior.length) false)
          (delimiter + 1 + 2 * prior.length + 1) bit
      have hpair :
          natRun
              ⟨.backEnd x,
                delimiter + 2 * (prior ++ [bit]).length, tape⟩ 4 =
            ⟨.backEnd x, delimiter + 2 * prior.length, pairTape⟩ := by
        have hlocal := natRun_backwardPair x bit
          (delimiter + 1 + 2 * prior.length) tape hlast.1 hlast.2
        convert hlocal using 1
        · congr 2
          simp
          omega
        · simp [pairTape]
      have hprior' :
          RightPairsAt pairTape (delimiter + 1) prior := by
        apply rightPairsAt_congr (before := tape)
          (after := pairTape) (start := delimiter + 1)
        · intro position hstart hfinish
          have hneLeft :
              position ≠ delimiter + 1 + 2 * prior.length := by omega
          have hneRight :
              position ≠ delimiter + 1 + 2 * prior.length + 1 := by omega
          simp [pairTape, writeNat, hneLeft, hneRight]

        · exact hprior
      obtain ⟨resultTape, hrun, hleft, houtside⟩ :=
        ih pairTape hprior'
      refine ⟨resultTape, ?_, ?_, ?_⟩
      · rw [show 4 * (prior ++ [bit]).length =
            4 + 4 * prior.length by simp; omega]
        rw [natRun_add, hpair, hrun]
      · apply (leftPairsAt_append resultTape (delimiter + 1)
          prior [bit]).mpr
        refine ⟨hleft, ?_⟩
        have hleftCell := houtside
          (delimiter + 1 + 2 * prior.length) (by right; omega)
        have hrightCell := houtside
          (delimiter + 1 + 2 * prior.length + 1) (by right; omega)
        simp only [leftPairsAt_cons, leftPairsAt_nil, and_true]
        constructor
        · rw [hleftCell]
          simp [pairTape, writeNat]
        · rw [hrightCell]
          simp [pairTape, writeNat]
      · intro position hposition
        have hthrough : resultTape position = pairTape position := by
          apply houtside position
          rcases hposition with hbefore | hafter
          · exact Or.inl hbefore
          · exact Or.inr (by
              simp at hafter ⊢
              omega)
        rw [hthrough]
        rcases hposition with hbefore | hafter
        · have hneLeft :
              position ≠ delimiter + 1 + 2 * prior.length := by omega
          have hneRight :
              position ≠ delimiter + 1 + 2 * prior.length + 1 := by omega
          simp [pairTape, writeNat, hneLeft, hneRight]
        · have hneLeft :
              position ≠ delimiter + 1 + 2 * prior.length := by
                simp at hafter
                omega
          have hneRight :
              position ≠ delimiter + 1 + 2 * prior.length + 1 := by
                simp at hafter
                omega
          simp [pairTape, writeNat, hneLeft, hneRight]

/--
Compose `natRun_forwardBubble` over an arbitrary left-oriented pair block.
The mobile bit `x` is transported to the cell immediately after the restored
right-oriented block, and the complete closed work interval is audited.
 -/
theorem natRun_forwardPairs (last x : Bool) (mobile : Nat)
    (bits : List Bool) (tape : Nat -> Bool)
    (hmobile : tape mobile = x)
    (hpairs : LeftPairsAt tape (mobile + 1) bits) :
    exists resultTape,
      natRun ⟨.forwardBlockStart last x, mobile + 1, tape⟩
          (6 * bits.length) =
        ⟨.forwardBlockStart last x,
          mobile + 2 * bits.length + 1, resultTape⟩ /\
      RightPairsAt resultTape mobile bits /\
      resultTape (mobile + 2 * bits.length) = x /\
      EqOutside resultTape tape mobile
        (mobile + 2 * bits.length + 1) := by
  induction bits generalizing mobile tape with
  | nil =>
      refine ⟨tape, ?_, by trivial, ?_, eqOutside_refl _ _ _⟩
      · simp [natRun]
      · simpa using hmobile
  | cons bit bits ih =>
      rcases hpairs with ⟨hzero, hbit, htail⟩
      let bubbleTape :=
        writeNat (writeNat tape (mobile + 2) x) mobile bit
      have hbubble :
          natRun ⟨.forwardBlockStart last x, mobile + 1, tape⟩ 6 =
            ⟨.forwardBlockStart last x, mobile + 2 + 1,
              bubbleTape⟩ := by
        simpa [bubbleTape, Nat.add_assoc] using
          natRun_forwardBubble last x bit mobile tape hmobile hzero hbit
      have hmobile' : bubbleTape (mobile + 2) = x := by
        have hne : mobile + 2 ≠ mobile := by omega
        simp [bubbleTape, writeNat, hne]
      have htail' : LeftPairsAt bubbleTape (mobile + 2 + 1) bits := by
        apply leftPairsAt_congr (before := tape) (after := bubbleTape)
          (start := mobile + 2 + 1)
        · intro position hstart hfinish
          have hneMobile : position ≠ mobile := by omega
          have hneNext : position ≠ mobile + 2 := by omega
          simp [bubbleTape, writeNat, hneMobile, hneNext]
        · convert htail using 1 <;> omega
      obtain ⟨resultTape, hrun, hright, hfinalMobile, houtside⟩ :=
        ih (mobile + 2) bubbleTape hmobile' htail'
      refine ⟨resultTape, ?_, ?_, ?_, ?_⟩
      · rw [show 6 * (bit :: bits).length =
            6 + 6 * bits.length by simp; omega]
        rw [natRun_add, hbubble]
        convert hrun using 1 <;> simp <;> omega
      · refine ⟨?_, ?_, ?_⟩
        · rw [houtside mobile (by left; omega)]
          simp [bubbleTape, writeNat]
        · rw [houtside (mobile + 1) (by left; omega)]
          have hne : mobile + 1 ≠ mobile := by omega
          simp [bubbleTape, writeNat, hne, hzero]
        · convert hright using 1 <;> omega
      · rw [show mobile + 2 * (bit :: bits).length =
            (mobile + 2) + 2 * bits.length by simp; omega]
        exact hfinalMobile
      · intro position hposition
        have hthrough : resultTape position = bubbleTape position := by
          apply houtside position
          rcases hposition with hbefore | hafter
          · exact Or.inl (by omega)
          · exact Or.inr (by
              simp at hafter ⊢
              omega)
        rw [hthrough]
        rcases hposition with hbefore | hafter
        · have hneMobile : position ≠ mobile := by omega
          have hneNext : position ≠ mobile + 2 := by omega
          simp [bubbleTape, writeNat, hneMobile, hneNext]
        · have hneMobile : position ≠ mobile := by
            simp at hafter
            omega
          have hneNext : position ≠ mobile + 2 := by
            simp at hafter
            omega
          simp [bubbleTape, writeNat, hneMobile, hneNext]

/--
One complete arbitrary-list zipper cycle, stopped immediately before handling
the old `C` marker.  This composes the real one-step entry, the complete
backward pass, delimiter shift, and complete forward pass.  The exact cost is
`1 + 4*p + 5 + 6*p = 10*p + 6` for `p = processed.length`.
 -/
theorem natRun_cycleToMarker (last x : Bool) (delimiter : Nat)
    (processed : List Bool) (tape : Nat -> Bool)
    (hdelimiter : 2 <= delimiter)
    (hD : tape delimiter = true)
    (hnew : tape (delimiter - 1) = false)
    (hprobe : tape (delimiter - 2) = last)
    (hpairs : RightPairsAt tape (delimiter + 1) processed)
    (hmarker : tape (delimiter + 1 + 2 * processed.length) = true) :
    exists resultTape,
      natRun
          ⟨.backStart x,
            delimiter + 1 + 2 * processed.length, tape⟩
          (10 * processed.length + 6) =
        ⟨.forwardBlockStart last x,
          delimiter + 2 * processed.length + 1, resultTape⟩ /\
      resultTape (delimiter - 1) = true /\
      RightPairsAt resultTape delimiter processed /\
      resultTape (delimiter + 2 * processed.length) = x /\
      resultTape (delimiter + 2 * processed.length + 1) = true /\
      EqOutside resultTape tape (delimiter - 1)
        (delimiter + 2 * processed.length + 1) := by
  have hfirst :
      natRun
          ⟨.backStart x,
            delimiter + 1 + 2 * processed.length, tape⟩ 1 =
        ⟨.backEnd x, delimiter + 2 * processed.length, tape⟩ := by
    have hlocal := natStep_backStart_one x
      (delimiter + 1 + 2 * processed.length) tape hmarker
    change natStep
      ⟨.backStart x, delimiter + 1 + 2 * processed.length, tape⟩ = _
    have hhead :
        delimiter + 1 + 2 * processed.length - 1 =
          delimiter + 2 * processed.length := by
      rw [show delimiter + 1 + 2 * processed.length =
        (delimiter + 2 * processed.length) + 1 by omega]
      simp
    simpa only [hhead] using hlocal
  obtain ⟨backTape, hback, hleft, hbackOutside⟩ :=
    natRun_backwardPairs x delimiter processed tape hpairs
  have hbackD : backTape delimiter = true := by
    exact (hbackOutside delimiter (by left; omega)).trans hD
  have hbackNew : backTape (delimiter - 1) = false := by
    exact (hbackOutside (delimiter - 1) (by left; omega)).trans hnew
  have hbackProbe : backTape (delimiter - 2) = last := by
    exact (hbackOutside (delimiter - 2) (by left; omega)).trans hprobe
  let shiftedTape :=
    writeNat (writeNat backTape delimiter x) (delimiter - 1) true
  have hshift :
      natRun ⟨.backEnd x, delimiter, backTape⟩ 5 =
        ⟨.forwardBlockStart last x, delimiter + 1, shiftedTape⟩ := by
    simpa [shiftedTape] using natRun_shiftDelimiter x last delimiter backTape
      hdelimiter hbackD hbackNew hbackProbe
  have hshiftMobile : shiftedTape delimiter = x := by
    have hne : delimiter ≠ delimiter - 1 := by omega
    simp [shiftedTape, writeNat, hne]
  have hshiftLeft :
      LeftPairsAt shiftedTape (delimiter + 1) processed := by
    apply leftPairsAt_congr (before := backTape) (after := shiftedTape)
      (start := delimiter + 1)
    · intro position hstart hfinish
      have hneD : position ≠ delimiter := by omega
      have hneNew : position ≠ delimiter - 1 := by omega
      simp [shiftedTape, writeNat, hneD, hneNew]
    · exact hleft
  obtain ⟨resultTape, hforward, hright, hmobile, hforwardOutside⟩ :=
    natRun_forwardPairs last x delimiter processed shiftedTape
      hshiftMobile hshiftLeft
  have hresultDelimiter : resultTape (delimiter - 1) = true := by
    rw [hforwardOutside (delimiter - 1) (by left; omega)]
    simp [shiftedTape, writeNat]
  have hbackMarker :
      backTape (delimiter + 2 * processed.length + 1) = true := by
    rw [hbackOutside (delimiter + 2 * processed.length + 1)
      (by right; omega)]
    rw [show delimiter + 2 * processed.length + 1 =
      delimiter + 1 + 2 * processed.length by omega]
    exact hmarker
  have hshiftMarker :
      shiftedTape (delimiter + 2 * processed.length + 1) = true := by
    have hneD : delimiter + 2 * processed.length + 1 ≠ delimiter := by omega
    have hneNew :
        delimiter + 2 * processed.length + 1 ≠ delimiter - 1 := by omega
    simp [shiftedTape, writeNat, hneD, hneNew, hbackMarker]
  have hresultMarker :
      resultTape (delimiter + 2 * processed.length + 1) = true := by
    exact (hforwardOutside
      (delimiter + 2 * processed.length + 1) (by right; omega)).trans
        hshiftMarker
  refine ⟨resultTape, ?_, hresultDelimiter, hright, hmobile,
    hresultMarker, ?_⟩
  · rw [show 10 * processed.length + 6 =
        1 + (4 * processed.length + (5 + 6 * processed.length)) by omega]
    rw [natRun_add, hfirst, natRun_add, hback, natRun_add, hshift]
    convert hforward using 1 <;> omega
  · intro position hposition
    have hthroughForward : resultTape position = shiftedTape position := by
      apply hforwardOutside position
      rcases hposition with hbefore | hafter
      · exact Or.inl (by omega)
      · exact Or.inr hafter
    rw [hthroughForward]
    have hneD : position ≠ delimiter := by
      rcases hposition with hbefore | hafter <;> omega
    have hneNew : position ≠ delimiter - 1 := by
      rcases hposition with hbefore | hafter <;> omega
    rw [show shiftedTape position = backTape position by
      simp [shiftedTape, writeNat, hneD, hneNew]]
    apply hbackOutside position
    rcases hposition with hbefore | hafter
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

/-- The last zipper cycle, including the single final-`C` transition. -/
theorem natRun_finalCycle (x : Bool) (delimiter : Nat)
    (processed : List Bool) (tape : Nat -> Bool)
    (hdelimiter : 2 <= delimiter)
    (hD : tape delimiter = true)
    (hnew : tape (delimiter - 1) = false)
    (hprobe : tape (delimiter - 2) = true)
    (hpairs : RightPairsAt tape (delimiter + 1) processed)
    (hmarker : tape (delimiter + 1 + 2 * processed.length) = true) :
    exists resultTape,
      natRun
          ⟨.backStart x,
            delimiter + 1 + 2 * processed.length, tape⟩
          (10 * processed.length + 7) =
        ⟨.done, delimiter + 2 * processed.length + 2, resultTape⟩ /\
      resultTape (delimiter - 1) = true /\
      RightPairsAt resultTape delimiter processed /\
      resultTape (delimiter + 2 * processed.length) = x /\
      resultTape (delimiter + 2 * processed.length + 1) = true /\
      EqOutside resultTape tape (delimiter - 1)
        (delimiter + 2 * processed.length + 1) := by
  obtain ⟨resultTape, hcycle, hnewD, hpairsOut, hmobile,
      hfinalMarker, houtside⟩ :=
    natRun_cycleToMarker true x delimiter processed tape hdelimiter hD hnew
      hprobe hpairs hmarker
  have hfinal := natRun_finalC x
    (delimiter + 2 * processed.length + 1) resultTape hfinalMarker
  refine ⟨resultTape, ?_, hnewD, hpairsOut, hmobile,
    hfinalMarker, houtside⟩
  rw [show 10 * processed.length + 7 =
    (10 * processed.length + 6) + 1 by omega]
  rw [natRun_add, hcycle, hfinal]

/--
A nonfinal cycle including the `C` rewrite and the following `readNext` step.
The output facts are exactly the local input facts required by the next cycle:
the delimiter moved one cell left, `processed ++ [x]` is right-oriented, and
the next payload bit has been loaded into control while its cell is `C = 1`.
 -/
theorem natRun_nonfinalCycle (x next : Bool) (delimiter : Nat)
    (processed : List Bool) (tape : Nat -> Bool)
    (hdelimiter : 2 <= delimiter)
    (hD : tape delimiter = true)
    (hnew : tape (delimiter - 1) = false)
    (hprobe : tape (delimiter - 2) = false)
    (hpairs : RightPairsAt tape (delimiter + 1) processed)
    (hmarker : tape (delimiter + 1 + 2 * processed.length) = true)
    (hnext : tape (delimiter + 2 * processed.length + 2) = next) :
    exists resultTape,
      natRun
          ⟨.backStart x,
            delimiter + 1 + 2 * processed.length, tape⟩
          (10 * processed.length + 8) =
        ⟨.backStart next,
          delimiter + 2 * processed.length + 2, resultTape⟩ /\
      resultTape (delimiter - 1) = true /\
      resultTape (delimiter - 2) = false /\
      RightPairsAt resultTape delimiter (processed ++ [x]) /\
      resultTape (delimiter + 2 * processed.length + 2) = true /\
      EqOutside resultTape tape (delimiter - 1)
        (delimiter + 2 * processed.length + 3) := by
  obtain ⟨cycleTape, hcycle, hnewD, hpairsOut, hmobile,
      hCmarker, hcycleOutside⟩ :=
    natRun_cycleToMarker false x delimiter processed tape hdelimiter hD hnew
      hprobe hpairs hmarker
  let marker := delimiter + 2 * processed.length + 1
  let nextPosition := delimiter + 2 * processed.length + 2
  let afterC := writeNat cycleTape marker false
  let nextTape := writeNat afterC nextPosition true
  have hnonfinal :
      natRun ⟨.forwardBlockStart false x, marker, cycleTape⟩ 1 =
        ⟨.readNext, nextPosition, afterC⟩ := by
    have hlocal := natRun_nonfinalC x marker cycleTape (by
      simpa [marker] using hCmarker)
    simpa [marker, nextPosition, afterC] using hlocal
  have hcycleNext : cycleTape nextPosition = next := by
    rw [hcycleOutside nextPosition (by right; simp [nextPosition])]
    simpa [nextPosition] using hnext
  have hafterNext : afterC nextPosition = next := by
    have hne : nextPosition ≠ marker := by
      simp [nextPosition, marker]
    simp [afterC, writeNat, hne, hcycleNext]
  have hread :
      natRun ⟨.readNext, nextPosition, afterC⟩ 1 =
        ⟨.backStart next, nextPosition, nextTape⟩ := by
    simpa [natRun, nextTape, hafterNext] using
      natStep_readNext nextPosition afterC
  have hresultD : nextTape (delimiter - 1) = true := by
    have hneMarker : delimiter - 1 ≠ marker := by
      simp [marker]
      omega
    have hneNext : delimiter - 1 ≠ nextPosition := by
      simp [nextPosition]
      omega
    simp [nextTape, afterC, writeNat, hneMarker, hneNext, hnewD]
  have hcycleProbe : cycleTape (delimiter - 2) = false := by
    exact (hcycleOutside (delimiter - 2) (by left; omega)).trans hprobe
  have hresultProbe : nextTape (delimiter - 2) = false := by
    have hneMarker : delimiter - 2 ≠ marker := by
      simp [marker]
      omega
    have hneNext : delimiter - 2 ≠ nextPosition := by
      simp [nextPosition]
      omega
    simp [nextTape, afterC, writeNat, hneMarker, hneNext, hcycleProbe]
  have hpairsPreserved : RightPairsAt nextTape delimiter processed := by
    apply rightPairsAt_congr (before := cycleTape) (after := nextTape)
      (start := delimiter)
    · intro position hstart hfinish
      have hneMarker : position ≠ marker := by
        simp [marker]
        omega
      have hneNext : position ≠ nextPosition := by
        simp [nextPosition]
        omega
      simp [nextTape, afterC, writeNat, hneMarker, hneNext]
    · exact hpairsOut
  have hresultMobile :
      nextTape (delimiter + 2 * processed.length) = x := by
    have hneMarker :
        delimiter + 2 * processed.length ≠ marker := by simp [marker]
    have hneNext :
        delimiter + 2 * processed.length ≠ nextPosition := by
      simp [nextPosition]
    simp [nextTape, afterC, writeNat, hneMarker, hneNext, hmobile]
  have hresultOldMarker :
      nextTape (delimiter + 2 * processed.length + 1) = false := by
    have hneNext : marker ≠ nextPosition := by
      simp [marker, nextPosition]
    rw [show delimiter + 2 * processed.length + 1 = marker by rfl]
    simp [nextTape, afterC, writeNat, hneNext]
  have hpairsNext :
      RightPairsAt nextTape delimiter (processed ++ [x]) := by
    apply (rightPairsAt_append nextTape delimiter processed [x]).mpr
    refine ⟨hpairsPreserved, ?_⟩
    simp only [rightPairsAt_cons, rightPairsAt_nil, and_true]
    constructor
    · convert hresultMobile using 1 <;> omega
    · convert hresultOldMarker using 1 <;> omega
  have hresultMarker : nextTape nextPosition = true := by
    simp [nextTape]
  refine ⟨nextTape, ?_, hresultD, hresultProbe, hpairsNext, ?_, ?_⟩
  · rw [show 10 * processed.length + 8 =
      (10 * processed.length + 6) + (1 + 1) by omega]
    rw [natRun_add, hcycle, natRun_add, hnonfinal, hread]
  · simpa [nextPosition] using hresultMarker
  · intro position hposition
    have hneMarker : position ≠ marker := by
      rcases hposition with hbefore | hafter
      · simp [marker]
        omega
      · simp [marker] at hafter ⊢
        omega
    have hneNext : position ≠ nextPosition := by
      rcases hposition with hbefore | hafter
      · simp [nextPosition]
        omega
      · simp [nextPosition] at hafter ⊢
        omega
    rw [show nextTape position = cycleTape position by
      simp [nextTape, afterC, writeNat, hneMarker, hneNext]]
    apply hcycleOutside position
    rcases hposition with hbefore | hafter
    · exact Or.inl hbefore
    · exact Or.inr (by omega)

end OperationalGammaZipper
end StreamingMagnification
end Frontier
end Pnp4

#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper.gammaZipper_state_card
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper.encR_length
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper.cycleFrame_length_eq_total
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper.remaining_eq_one_iff_unprocessed_nil
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper.natRun_backwardPair
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper.natRun_shiftDelimiter
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper.natRun_forwardBubble
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper.natRun_finalC
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper.natRun_backwardPairs
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper.natRun_forwardPairs
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper.natRun_cycleToMarker
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper.natRun_finalCycle
#print axioms Pnp4.Frontier.StreamingMagnification.OperationalGammaZipper.natRun_nonfinalCycle
