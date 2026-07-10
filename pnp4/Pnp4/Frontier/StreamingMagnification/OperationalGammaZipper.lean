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
This module deliberately exposes the executable kernel and the exact cycle
and final layouts before claiming the still-missing global run induction.
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

/-- The chosen cubic canonical clock.  The intended quadratic bound for the
fully composed zipper trace remains part of the global induction obligation. -/
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
