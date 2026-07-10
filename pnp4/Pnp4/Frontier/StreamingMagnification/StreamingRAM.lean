import Mathlib.Tactic

/-!
# An operational uniform one-pass bit-RAM

This file fixes a concrete convention for the streaming machine used by the
MMW route.  A `Program` contains one finite control graph and one finite bank
of address registers, independent of the input length.  Its code is assembled
from the fixed instruction palette below; it is not an arbitrary Lean
function of the whole input or work memory.

The physical input is immutable and advances only through `requestInput`.
The input length is available on a separate read-only, least-significant-bit
first binary interface, as is standard for a length-aware streaming
algorithm.  Reading or moving that interface costs one instruction, and its
binary width is charged to space.

An address register is a bit zipper.  Its only data operations read or write
the current bit; its head moves by one position at a time.  There are no
unit-cost whole-word clear, copy, increment, comparison, or arithmetic
instructions.  Indirect `readWork` and `writeWork` use a register word solely
as the standard RAM address selector and touch exactly one Boolean work cell.
The program can branch only on that one cell, one current address bit, one
length bit, EOF, or one newly requested input bit.

Reporting is explicit: `beginReport` is legal only after the whole input has
been consumed, `emit` writes one output bit, and `finishReport` is the only
successful halt.  The accounting closes every otherwise-free boundary:

* the first update gap starts at step zero;
* consecutive gaps use successful-read completion times;
* `beginReport` closes the tail after the last read (or from step zero for an
  empty input);
* report time includes `beginReport`, all report computation and emissions,
  and `finishReport`.

Read-only stream bits and write-only output bits are excluded from work
space.  Every distinct addressed work bit, every allocated address-register
bit, and the read-only binary length interface are included.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace StreamingRAM

/-- An immutable finite bit input. -/
abbrev Input (length : Nat) := Fin length -> Bool

/-- Live update, explicit reporting, successful halt, or terminal fault. -/
inductive Phase where
  | update
  | report
  | halted
  | faulted
  deriving DecidableEq, Repr

/-! ## Bit-local address registers -/

/-- A finite allocated address word with a movable head.  `lowerRev` stores
less-significant bits nearest-first; `upper` stores more-significant bits
nearest-first.  At least the current bit is always allocated. -/
structure AddressRegister where
  lowerRev : List Bool
  current : Bool
  upper : List Bool
  deriving DecidableEq, Repr

namespace AddressRegister

/-- The zero word, with its head at the least significant bit. -/
def zero : AddressRegister :=
  { lowerRev := [], current := false, upper := [] }

/-- Allocated storage bits. -/
def allocatedBits (register : AddressRegister) : Nat :=
  register.lowerRev.length + 1 + register.upper.length

/-- Little-endian list of the allocated word. -/
def bits (register : AddressRegister) : List Bool :=
  register.lowerRev.reverse ++ register.current :: register.upper

/-- Decode a little-endian Boolean list.  This is used only by the standard
indirect-address selector, never as a branch predicate or a whole-word data
operation. -/
def littleEndianValue : List Bool -> Nat
  | [] => 0
  | bit :: rest => (if bit then 1 else 0) + 2 * littleEndianValue rest

/-- Natural address selected by the allocated word. -/
def value (register : AddressRegister) : Nat :=
  littleEndianValue register.bits

/-- Write exactly the current register bit. -/
def writeCurrent (register : AddressRegister) (bit : Bool) : AddressRegister :=
  { register with current := bit }

/-- Move the physical register head one bit toward more-significant bits.
Crossing the allocated boundary allocates one fresh zero bit. -/
def moveRight (register : AddressRegister) : AddressRegister :=
  match register.upper with
  | [] =>
      { lowerRev := register.current :: register.lowerRev
        current := false
        upper := [] }
  | bit :: rest =>
      { lowerRev := register.current :: register.lowerRev
        current := bit
        upper := rest }

/-- Move the physical register head one bit toward less-significant bits.
The least-significant boundary is sticky. -/
def moveLeft (register : AddressRegister) : AddressRegister :=
  match register.lowerRev with
  | [] => register
  | bit :: rest =>
      { lowerRev := rest
        current := bit
        upper := register.current :: register.upper }

@[simp] theorem allocatedBits_zero : zero.allocatedBits = 1 :=
  rfl

@[simp] theorem allocatedBits_writeCurrent
    (register : AddressRegister) (bit : Bool) :
    (register.writeCurrent bit).allocatedBits = register.allocatedBits := by
  simp [writeCurrent, allocatedBits]

theorem allocatedBits_moveRight_le_succ (register : AddressRegister) :
    register.moveRight.allocatedBits <= register.allocatedBits + 1 := by
  cases register with
  | mk lowerRev current upper =>
      cases upper with
      | nil => simp [moveRight, allocatedBits]
      | cons bit rest =>
          simp [moveRight, allocatedBits]
          omega

theorem allocatedBits_moveLeft_eq (register : AddressRegister) :
    register.moveLeft.allocatedBits = register.allocatedBits := by
  cases register with
  | mk lowerRev current upper =>
      cases lowerRev with
      | nil => simp [moveLeft, allocatedBits]
      | cons bit rest =>
          simp [moveLeft, allocatedBits]
          omega

end AddressRegister

/-! ## Uniform program and instruction palette -/

/-- Every constructor is one unit-cost instruction in the fixed palette.
`readWork`/`writeWork` touch one addressed work bit.  The address-register
constructors touch at most the current bit and one neighbouring head cell. -/
inductive Instruction (stateCount addressRegisterCount : Nat) where
  | jump (next : Fin stateCount)
  | requestInput (onEnd onFalse onTrue : Fin stateCount)
  | readLengthBit (onEnd onFalse onTrue : Fin stateCount)
  | moveLengthLeft (next : Fin stateCount)
  | moveLengthRight (next : Fin stateCount)
  | readAddressBit
      (register : Fin addressRegisterCount)
      (onFalse onTrue : Fin stateCount)
  | writeAddressBit
      (register : Fin addressRegisterCount)
      (value : Bool) (next : Fin stateCount)
  | moveAddressLeft
      (register : Fin addressRegisterCount)
      (next : Fin stateCount)
  | moveAddressRight
      (register : Fin addressRegisterCount)
      (next : Fin stateCount)
  | readWork
      (addressRegister : Fin addressRegisterCount)
      (onFalse onTrue : Fin stateCount)
  | writeWork
      (addressRegister : Fin addressRegisterCount)
      (value : Bool) (next : Fin stateCount)
  | beginReport (next : Fin stateCount)
  | emit (value : Bool) (next : Fin stateCount)
  | finishReport
  deriving DecidableEq, Repr

/-- One finite program, fixed before the input length and table. -/
structure Program where
  stateCount : Nat
  addressRegisterCount : Nat
  startState : Fin stateCount
  instruction : Fin stateCount ->
    Instruction stateCount addressRegisterCount

/-- Binary width charged for the read-only length parameter. -/
def lengthBitWidth (length : Nat) : Nat :=
  if length = 0 then 1 else Nat.log2 length + 1

/-- Read one bit of the read-only little-endian binary length interface. -/
def lengthBit (length position : Nat) : Bool :=
  Nat.testBit length position

/-- Total allocated storage in the fixed finite address bank.  The recursion
over `Fin` avoids introducing a classical enumeration of the bank. -/
def addressRegisterSpace : {count : Nat} ->
    (Fin count -> AddressRegister) -> Nat
  | 0, _ => 0
  | _count + 1, registers =>
      (registers 0).allocatedBits +
        addressRegisterSpace (fun register => registers register.succ)

/-- Allocate one random-access work cell if it has not been touched before.
The list is inaccessible bookkeeping, and this operation preserves its
no-duplicate invariant when started from the initial empty list. -/
def touchWorkAddress (address : Nat) (touched : List Nat) : List Nat :=
  if address ∈ touched then touched else address :: touched

/-! ## Operational configurations and accounting -/

/-- The operational configuration.  `workTouched` is accounting metadata for
the finite set of allocated random-access Boolean cells; it is not visible to
the program.  Output is reversed so one `emit` is a cons operation.

`lastReadStep` stores the completion time of the latest successful read.
`reportStartStep` stores the instruction-start time of `beginReport`. -/
structure Config (program : Program) (inputLength : Nat) where
  input : Input inputLength
  state : Fin program.stateCount
  phase : Phase
  cursor : Nat
  lengthHead : Nat
  work : Nat -> Bool
  workTouched : List Nat
  address : Fin program.addressRegisterCount -> AddressRegister
  outputRev : List Bool
  stepCount : Nat
  spaceHighWater : Nat
  lastReadStep : Option Nat
  maxUpdateGap : Nat
  reportStartStep : Option Nat

namespace Config

/-- Output in chronological order. -/
def output {program : Program} {inputLength : Nat}
    (config : Config program inputLength) : List Bool :=
  config.outputRev.reverse

/-- Currently allocated charged storage. -/
def instantaneousSpace {program : Program} {inputLength : Nat}
    (config : Config program inputLength) : Nat :=
  config.workTouched.length + addressRegisterSpace config.address +
    lengthBitWidth inputLength

end Config

/-- Elapsed update time from step zero or the preceding read completion. -/
def elapsedUpdateGap (previousRead : Option Nat) (now : Nat) : Nat :=
  now - previousRead.getD 0

/-- Incorporate one newly closed update interval into the worst-case gap. -/
def extendUpdateMaximum
    (currentMaximum : Nat) (previousRead : Option Nat) (now : Nat) : Nat :=
  max currentMaximum (elapsedUpdateGap previousRead now)

@[simp] theorem elapsedUpdateGap_from_start (now : Nat) :
    elapsedUpdateGap none now = now := by
  simp [elapsedUpdateGap]

@[simp] theorem elapsedUpdateGap_from_read (previous now : Nat) :
    elapsedUpdateGap (some previous) now = now - previous := by
  simp [elapsedUpdateGap]

/-- An immediate first read still costs its one read transition. -/
@[simp] theorem firstReadBoundaryGap :
    elapsedUpdateGap none 1 = 1 :=
  rfl

/-- Adjacent successful read completions are one elapsed step apart. -/
@[simp] theorem consecutiveReadBoundaryGap (previous : Nat) :
    elapsedUpdateGap (some previous) (previous + 1) = 1 := by
  simp [elapsedUpdateGap]

/-- Beginning the report immediately after a read adds no hidden update
operation; any delay makes this tail positive and is incorporated below. -/
@[simp] theorem immediateReportBoundaryGap (previous : Nat) :
    elapsedUpdateGap (some previous) previous = 0 := by
  simp [elapsedUpdateGap]

theorem closedGap_le_extendedMaximum
    (currentMaximum : Nat) (previousRead : Option Nat) (now : Nat) :
    elapsedUpdateGap previousRead now <=
      extendUpdateMaximum currentMaximum previousRead now := by
  simp [extendUpdateMaximum]

/-- Initial configuration.  The address bank starts at zero. -/
def initialConfig (program : Program) {inputLength : Nat}
    (input : Input inputLength) : Config program inputLength :=
  let addresses : Fin program.addressRegisterCount -> AddressRegister :=
    fun _ => AddressRegister.zero
  let initialSpace :=
    addressRegisterSpace addresses + lengthBitWidth inputLength
  { input := input
    state := program.startState
    phase := .update
    cursor := 0
    lengthHead := 0
    work := fun _ => false
    workTouched := []
    address := addresses
    outputRev := []
    stepCount := 0
    spaceHighWater := initialSpace
    lastReadStep := none
    maxUpdateGap := 0
    reportStartStep := none }

/-- Close one live instruction and update the monotone space summary. -/
private def finishStep {program : Program} {inputLength : Nat}
    (before after : Config program inputLength) :
    Config program inputLength :=
  { after with
    stepCount := before.stepCount + 1
    spaceHighWater :=
      max before.spaceHighWater after.instantaneousSpace }

/-- Illegal phase/instruction combinations fault in one step. -/
private def fault {program : Program} {inputLength : Nat}
    (config : Config program inputLength) : Config program inputLength :=
  finishStep config { config with phase := .faulted }

/-- Record a successful input read at its completion time.  This charges the
initial-to-first boundary as well as every consecutive-read boundary. -/
private def recordRead {program : Program} {inputLength : Nat}
    (before after : Config program inputLength) :
    Config program inputLength :=
  let completion := before.stepCount + 1
  { after with
    lastReadStep := some completion
    maxUpdateGap :=
      extendUpdateMaximum before.maxUpdateGap before.lastReadStep completion }

/-- Close the final update tail at the start of explicit reporting. -/
private def recordReportStart {program : Program} {inputLength : Nat}
    (config : Config program inputLength) : Config program inputLength :=
  { config with
    maxUpdateGap :=
      extendUpdateMaximum config.maxUpdateGap
        config.lastReadStep config.stepCount
    reportStartStep := some config.stepCount }

/-- Execute one fixed-palette instruction.  Terminal configurations stutter
without accruing steps. -/
def step (program : Program) {inputLength : Nat}
    (config : Config program inputLength) : Config program inputLength :=
  match config.phase with
  | .halted => config
  | .faulted => config
  | livePhase =>
      match program.instruction config.state with
      | .jump next =>
          finishStep config { config with state := next }
      | .requestInput onEnd onFalse onTrue =>
          if livePhase = .update then
            if hCursor : config.cursor < inputLength then
              let bit := config.input ⟨config.cursor, hCursor⟩
              let next := if bit then onTrue else onFalse
              recordRead config <|
                finishStep config
                  { config with
                    state := next
                    cursor := config.cursor + 1 }
            else
              finishStep config { config with state := onEnd }
          else
            fault config
      | .readLengthBit onEnd onFalse onTrue =>
          if config.lengthHead < lengthBitWidth inputLength then
            let bit := lengthBit inputLength config.lengthHead
            let next := if bit then onTrue else onFalse
            finishStep config { config with state := next }
          else
            finishStep config { config with state := onEnd }
      | .moveLengthLeft next =>
          finishStep config
            { config with
              state := next
              lengthHead := config.lengthHead - 1 }
      | .moveLengthRight next =>
          finishStep config
            { config with
              state := next
              lengthHead :=
                min (config.lengthHead + 1) (lengthBitWidth inputLength) }
      | .readAddressBit register onFalse onTrue =>
          let bit := (config.address register).current
          let next := if bit then onTrue else onFalse
          finishStep config { config with state := next }
      | .writeAddressBit register value next =>
          finishStep config
            { config with
              state := next
              address := Function.update config.address register
                ((config.address register).writeCurrent value) }
      | .moveAddressLeft register next =>
          finishStep config
            { config with
              state := next
              address := Function.update config.address register
                (config.address register).moveLeft }
      | .moveAddressRight register next =>
          finishStep config
            { config with
              state := next
              address := Function.update config.address register
                (config.address register).moveRight }
      | .readWork addressRegister onFalse onTrue =>
          let address := (config.address addressRegister).value
          let bit := config.work address
          let next := if bit then onTrue else onFalse
          finishStep config
            { config with
              state := next
              workTouched := touchWorkAddress address config.workTouched }
      | .writeWork addressRegister value next =>
          let address := (config.address addressRegister).value
          finishStep config
            { config with
              state := next
              work := Function.update config.work address value
              workTouched := touchWorkAddress address config.workTouched }
      | .beginReport next =>
          if livePhase = .update ∧ config.cursor = inputLength then
            let accounted := recordReportStart config
            finishStep config
              { accounted with state := next, phase := .report }
          else
            fault config
      | .emit value next =>
          if livePhase = .report then
            finishStep config
              { config with
                state := next
                outputRev := value :: config.outputRev }
          else
            fault config
      | .finishReport =>
          if livePhase = .report then
            finishStep config { config with phase := .halted }
          else
            fault config

/-- Configuration after exactly the requested number of attempted steps.
After either terminal phase, further attempts stutter. -/
def run (program : Program) {inputLength : Nat}
    (input : Input inputLength) : Nat -> Config program inputLength
  | 0 => initialConfig program input
  | steps + 1 => step program (run program input steps)

/-- Evidence of explicit successful completion.  It contains no correctness,
solver, lower-bound, contract, or provider field. -/
structure CompletedRun (program : Program) {inputLength : Nat}
    (input : Input inputLength) where
  steps : Nat
  halted : (run program input steps).phase = .halted

namespace CompletedRun

/-- Final operational configuration. -/
def finalConfig {program : Program} {inputLength : Nat}
    {input : Input inputLength} (completed : CompletedRun program input) :
    Config program inputLength :=
  run program input completed.steps

/-- Maximum charged storage over the whole run. -/
def spaceUsed {program : Program} {inputLength : Nat}
    {input : Input inputLength} (completed : CompletedRun program input) : Nat :=
  completed.finalConfig.spaceHighWater

/-- Maximum of the initial, inter-read, and final update gaps. -/
def maxUpdateGap {program : Program} {inputLength : Nat}
    {input : Input inputLength} (completed : CompletedRun program input) : Nat :=
  completed.finalConfig.maxUpdateGap

/-- Instructions starting with `beginReport` and ending with
`finishReport`, inclusive. -/
def reportTime {program : Program} {inputLength : Nat}
    {input : Input inputLength} (completed : CompletedRun program input) : Nat :=
  match completed.finalConfig.reportStartStep with
  | none => 0
  | some start => completed.finalConfig.stepCount - start

/-- Emitted output in chronological order. -/
def output {program : Program} {inputLength : Nat}
    {input : Input inputLength} (completed : CompletedRun program input) :
    List Bool :=
  completed.finalConfig.output

/-- Number of physical stream bits consumed. -/
def bitsRead {program : Program} {inputLength : Nat}
    {input : Input inputLength} (completed : CompletedRun program input) : Nat :=
  completed.finalConfig.cursor

end CompletedRun

/-! ## Operational audit lemmas -/

@[simp] theorem initialConfig_phase (program : Program)
    {inputLength : Nat} (input : Input inputLength) :
    (initialConfig program input).phase = .update :=
  rfl

@[simp] theorem initialConfig_cursor (program : Program)
    {inputLength : Nat} (input : Input inputLength) :
    (initialConfig program input).cursor = 0 :=
  rfl

@[simp] theorem initialConfig_lengthHead (program : Program)
    {inputLength : Nat} (input : Input inputLength) :
    (initialConfig program input).lengthHead = 0 :=
  rfl

@[simp] theorem step_preserves_input (program : Program)
    {inputLength : Nat} (config : Config program inputLength) :
    (step program config).input = config.input := by
  cases hPhase : config.phase <;>
    cases hInstruction : program.instruction config.state <;>
    simp only [step, hPhase, hInstruction] <;>
    dsimp [finishStep, fault, recordRead, recordReportStart] <;>
    split_ifs <;> rfl

/-- No instruction rewinds the one-way physical input cursor. -/
theorem cursor_mono_step (program : Program)
    {inputLength : Nat} (config : Config program inputLength) :
    config.cursor <= (step program config).cursor := by
  cases hPhase : config.phase <;>
    cases hInstruction : program.instruction config.state <;>
    simp only [step, hPhase, hInstruction] <;>
    (try dsimp [finishStep, fault, recordRead, recordReportStart]) <;>
    (try split_ifs) <;> simp_all

/-- One instruction consumes at most one physical input bit. -/
theorem cursor_step_le_succ (program : Program)
    {inputLength : Nat} (config : Config program inputLength) :
    (step program config).cursor <= config.cursor + 1 := by
  cases hPhase : config.phase <;>
    cases hInstruction : program.instruction config.state <;>
    simp only [step, hPhase, hInstruction] <;>
    (try dsimp [finishStep, fault, recordRead, recordReportStart]) <;>
    (try split_ifs) <;> simp_all

/-- The read-only length head remains within the finite binary interface. -/
theorem lengthHead_step_le_width (program : Program)
    {inputLength : Nat} (config : Config program inputLength)
    (hHead : config.lengthHead <= lengthBitWidth inputLength) :
    (step program config).lengthHead <= lengthBitWidth inputLength := by
  cases hPhase : config.phase <;>
    cases hInstruction : program.instruction config.state <;>
    simp only [step, hPhase, hInstruction] <;>
    (try dsimp [finishStep, fault, recordRead, recordReportStart]) <;>
    (try split_ifs) <;> (try simp_all) <;> omega

end StreamingRAM
end StreamingMagnification
end Frontier
end Pnp4
