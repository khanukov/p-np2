import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram
import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekEncoding
import Mathlib.Tactic.DeriveFintype

/-!
# T1 fixed-control true uniform seek: finite control

This module holds the **complete** zero-parameter T1 finite control: the
read-only grammar pass and rewind of T1a, the destructive cursor/index
mutation modes of T1b, and the terminal output/repair/dispatch modes of T1c.
T1c-1 closes the table: the T1c transitions — restoring the consumed index
field, writing the output frame, and entering `accept` — are present, and
`successStart`/`oobStart`, the last two idle states, are active.
"Complete" here is a statement about the **table only**.  It is not a claim
that the traces those transitions generate have been proved; see the scope
paragraph at the end of this docstring.

There is still exactly one program declaration (`t1CS`), no machine
arguments, no `Nat` in `T1State`, no compiled offsets, and the public clock
`t1Clock` is unchanged: the only state added beyond T1a is a single Boolean
latch, which carries the data value under the cursor during T1b and is
re-used as the accept/reject tag during T1c's repair pass.

The thirty-three modes fall into seven groups.

* Read-only validation (T1a): `validateBof`, `validateIndex`, `validateData`,
  `validateFinish`, `validateBlank`, then `rewindStart` and `rewind`.
* Cursor installation: `startMutation` walks off the `bof` frame,
  `seekSeparator` scans the index field, `probeData` reads the frame right of
  the current position, `turnInstall` turns around, and `writeCursor`
  overwrites that frame with the `cursor` marker.
* Index consumption: `seekIndexBack` scans right-to-left for the rightmost
  unconsumed `index` frame and `markSpent` rewrites it to `spent` — the
  on-tape decrement.
* Cursor motion: `seekCursorFwd` scans left-to-right for the `cursor` marker,
  `backupCursor` turns around onto it, and `writeData` restores it to the
  latched data frame.
* Boundaries: `successStart` (all index units consumed) and `oobStart` (the
  data field ran out) are the two terminal entry points.  Both are now
  **active**: `successStart` dispatches into the output arm keeping the latch,
  `oobStart` dispatches straight into the repair pass with the latch cleared
  to the reject tag.  `accept` and `reject` remain the only stable sinks.
* Success arm (T1c): `outWalk` walks off the `bof` anchor, `outSeekCursor`
  scans left to right for the `cursor` marker, `outBackup` turns around onto
  it, `outWriteData` restores it to the latched data frame, `outSeekOutput`
  scans on to the `output` frame, `outTurn` turns around onto it, and
  `outWriteOut` overwrites it with `output latch` — then sets the latch to
  `true`, the accept tag.
* Shared repair and dispatch (T1c): `repairSeek` scans right to left,
  `repairWrite` rewrites each `spent` marker back to `index`, `repairBack`
  and `repairHop` return the head to the preceding frame, and `repairDone`
  fires at the `bof` anchor, entering `t1AcceptState` or `t1RejectState`
  according to the latch tag.

Four of the mutation and terminal modes (`seekSeparator`, `seekCursorFwd`,
`outSeekCursor`, `outSeekOutput`) read frames left to right exactly like the
T1a validation modes, so they are folded into the shared
`t1Advance`/`t1Complete` table and inherit T1a's macrostep machinery.
`seekIndexBack` and `repairSeek` read frames right to left and have their own
`t1SeekBackAdvance` and `t1RepairBackAdvance` tables.

**Transition-table lemmas.**  Every lemma in the *Standalone
transition-table lemmas* section below is a plain tuple equation about
`t1Transition`, discharged by `rfl` after at most one case split — on
`T1FramePosition`, through `T1ForwardMode.cases`, or on the decoded frame —
possibly preceded by rewriting with the lemma's own decoded-frame hypothesis.
The clock `t1Clock`, the program `t1CS` and its two projections also sit
below `t1Transition`; they are definitions and projections, not table lemmas.
Downstream `TM.stepConfig` proofs consume only the table lemmas through the
generic `ConstStatePhasedStepBridge` corollaries and never unfold
`t1Transition` itself.  That is what keeps the enlarged thirty-three-mode
control table out of every execution proof.

This module makes no addressing claim, and it proves no *end-to-end*
restoration or acceptance theorem: it fixes the terminal control only.  The
exact repair/output traces and the acceptance semantics are T1c-2.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

inductive T1Mode
  | validateBof | validateIndex | validateData | validateFinish | validateBlank
  | rewindStart | rewind | startMutation
  | seekSeparator | probeData | turnInstall | writeCursor
  | seekIndexBack | markSpent | seekCursorFwd | backupCursor | writeData
  | successStart | oobStart
  | outWalk | outSeekCursor | outBackup | outWriteData
  | outSeekOutput | outTurn | outWriteOut
  | repairSeek | repairWrite | repairBack | repairHop | repairDone
  | accept | reject
  deriving Fintype, DecidableEq, Repr

inductive T1FramePosition | p0 | p1 | p2 | p3
  deriving Fintype, DecidableEq, Repr

/-- The complete T1 control state: a mode, a frame position, a three-bit
frame buffer, and the single Boolean latch — the cursor value during T1b, the
accept/reject tag during T1c's repair pass.  T1c-1 adds no field: no `Nat`,
width, offset, or length occurs here. -/
structure T1State where
  mode : T1Mode
  position : T1FramePosition
  b0 : Bool
  b1 : Bool
  b2 : Bool
  latch : Bool
  deriving Fintype, DecidableEq, Repr

def t1State (mode : T1Mode) (position : T1FramePosition)
    (b0 := false) (b1 := false) (b2 := false) (latch := false) : T1State :=
  ⟨mode, position, b0, b1, b2, latch⟩

def t1AcceptState : T1State := t1State .accept .p0
def t1RejectState : T1State := t1State .reject .p0

/-- The success boundary state, carrying the latched data value that T1c will
write into the output frame. -/
def t1SuccessState (latch : Bool) : T1State :=
  t1State .successStart .p0 false false false latch

/-- The out-of-bounds boundary state. -/
def t1OobState (latch : Bool) : T1State :=
  t1State .oobStart .p0 false false false latch

/-- Left-to-right frame table, shared by the read-only validation modes and
by the two forward mutation scans. -/
def t1Advance : T1Mode → T1Frame → T1Mode
  | .validateBof, .bof => .validateIndex
  | .validateIndex, .index => .validateIndex
  | .validateIndex, .separator => .validateData
  | .validateData, .data _ => .validateData
  | .validateData, .output false => .validateFinish
  | .validateFinish, .finish => .validateBlank
  | .validateBlank, .blank => .rewindStart
  | .seekSeparator, .index => .seekSeparator
  | .seekSeparator, .separator => .probeData
  | .seekCursorFwd, .spent => .seekCursorFwd
  | .seekCursorFwd, .separator => .seekCursorFwd
  | .seekCursorFwd, .data _ => .seekCursorFwd
  | .seekCursorFwd, .cursor => .backupCursor
  | .outSeekCursor, .spent => .outSeekCursor
  | .outSeekCursor, .separator => .outSeekCursor
  | .outSeekCursor, .data _ => .outSeekCursor
  | .outSeekCursor, .cursor => .outBackup
  | .outSeekOutput, .data _ => .outSeekOutput
  | .outSeekOutput, .output false => .outTurn
  | _, _ => .reject

def t1Complete (mode : T1Mode) (b0 b1 b2 b3 : Bool) : T1Mode :=
  match decodeT1Frame? [b0, b1, b2, b3] with
  | some frame => t1Advance mode frame
  | none => .reject

/-- Right-to-left frame table for `seekIndexBack`: skip the data prefix, the
separator and the already-`spent` markers; stop on the rightmost `index`
frame; report success at the `bof` anchor. -/
def t1SeekBackAdvance : T1Frame → T1Mode
  | .index => .markSpent
  | .spent => .seekIndexBack
  | .separator => .seekIndexBack
  | .data _ => .seekIndexBack
  | .bof => .successStart
  | _ => .reject

def t1SeekBackComplete (b0 b1 b2 b3 : Bool) : T1Mode :=
  match decodeT1Frame? [b0, b1, b2, b3] with
  | some frame => t1SeekBackAdvance frame
  | none => .reject

/-- Right-to-left frame table for the shared `spent ↦ index` repair scan.
Everything to the right of the index field is skipped; each `spent` marker is
rewritten; the `bof` anchor ends the pass. -/
def t1RepairBackAdvance : T1Frame → T1Mode
  | .spent => .repairWrite
  | .bof => .repairDone
  | .index => .repairSeek
  | .separator => .repairSeek
  | .data _ => .repairSeek
  | .output _ => .repairSeek
  | .finish => .repairSeek
  | _ => .reject

def t1RepairBackComplete (b0 b1 b2 b3 : Bool) : T1Mode :=
  match decodeT1Frame? [b0, b1, b2, b3] with
  | some frame => t1RepairBackAdvance frame
  | none => .reject

/-- Modes in which the T1 control reads one frame from left to right through
the shared `t1Advance` table. -/
def T1ForwardMode : T1Mode → Prop
  | .validateBof | .validateIndex | .validateData | .validateFinish
  | .validateBlank | .seekSeparator | .seekCursorFwd
  | .outSeekCursor | .outSeekOutput => True
  | _ => False

/-- The forward modes, enumerated.  Case-splitting through this lemma keeps
the table lemmas below at nine cheap `rfl`s instead of thirty-three. -/
theorem T1ForwardMode.cases {mode : T1Mode} (hmode : T1ForwardMode mode) :
    mode = .validateBof ∨ mode = .validateIndex ∨ mode = .validateData ∨
      mode = .validateFinish ∨ mode = .validateBlank ∨
      mode = .seekSeparator ∨ mode = .seekCursorFwd ∨
      mode = .outSeekCursor ∨ mode = .outSeekOutput := by
  cases mode <;> simp_all [T1ForwardMode]

theorem T1ForwardMode.outSeekCursor : T1ForwardMode .outSeekCursor := trivial

theorem T1ForwardMode.outSeekOutput : T1ForwardMode .outSeekOutput := trivial

def t1Transition (_phase : Fin 1) (s : T1State) (scan : Bool) :
    Fin 1 × T1State × Bool × Move :=
  match s.mode with
  | .accept => (0, t1AcceptState, scan, .stay)
  | .reject => (0, t1RejectState, scan, .stay)
  | .successStart => (0, t1State .outWalk .p0 false false false s.latch, scan, .stay)
  | .oobStart => (0, t1State .repairSeek .p3 false false false false, scan, .stay)
  | .outWalk =>
      match s.position with
      | .p0 => (0, t1State .outWalk .p1 false false false s.latch, scan, .right)
      | .p1 => (0, t1State .outWalk .p2 false false false s.latch, scan, .right)
      | .p2 => (0, t1State .outWalk .p3 false false false s.latch, scan, .right)
      | .p3 => (0, t1State .outSeekCursor .p0 false false false s.latch, scan, .right)
  | .outBackup =>
      match s.position with
      | .p0 => (0, t1State .outBackup .p1 false false false s.latch, scan, .left)
      | .p1 => (0, t1State .outBackup .p2 false false false s.latch, scan, .left)
      | .p2 => (0, t1State .outBackup .p3 false false false s.latch, scan, .left)
      | .p3 => (0, t1State .outWriteData .p0 false false false s.latch, scan, .left)
  | .outWriteData =>
      match s.position with
      | .p0 => (0, t1State .outWriteData .p1 false false false s.latch, false, .right)
      | .p1 => (0, t1State .outWriteData .p2 false false false s.latch, true, .right)
      | .p2 => (0, t1State .outWriteData .p3 false false false s.latch, s.latch, .right)
      | .p3 => (0, t1State .outSeekOutput .p0 false false false s.latch, !s.latch, .right)
  | .outTurn => (0, t1State .outWriteOut .p3 false false false s.latch, scan, .left)
  | .outWriteOut =>
      match s.position with
      | .p3 => (0, t1State .outWriteOut .p2 false false false s.latch, s.latch, .left)
      | .p2 => (0, t1State .outWriteOut .p1 false false false s.latch, false, .left)
      | .p1 => (0, t1State .outWriteOut .p0 false false false s.latch, false, .left)
      | .p0 => (0, t1State .repairSeek .p3 false false false true, true, .left)
  | .repairSeek =>
      match s.position with
      | .p3 => (0, t1State .repairSeek .p2 false false scan s.latch, scan, .left)
      | .p2 => (0, t1State .repairSeek .p1 false scan s.b2 s.latch, scan, .left)
      | .p1 => (0, t1State .repairSeek .p0 scan s.b1 s.b2 s.latch, scan, .left)
      | .p0 =>
          match t1RepairBackComplete scan s.b0 s.b1 s.b2 with
          | .repairWrite =>
              (0, t1State .repairWrite .p0 false false false s.latch, scan, .stay)
          | .repairSeek =>
              (0, t1State .repairSeek .p3 false false false s.latch, scan, .left)
          | .repairDone =>
              (0, t1State .repairDone .p0 false false false s.latch, scan, .stay)
          | _ => (0, t1RejectState, scan, .stay)
  | .repairWrite =>
      match s.position with
      | .p0 => (0, t1State .repairWrite .p1 false false false s.latch, false, .right)
      | .p1 => (0, t1State .repairWrite .p2 false false false s.latch, false, .right)
      | .p2 => (0, t1State .repairWrite .p3 false false false s.latch, true, .right)
      | .p3 => (0, t1State .repairBack .p0 false false false s.latch, false, .right)
  | .repairBack =>
      match s.position with
      | .p0 => (0, t1State .repairBack .p1 false false false s.latch, scan, .left)
      | .p1 => (0, t1State .repairBack .p2 false false false s.latch, scan, .left)
      | .p2 => (0, t1State .repairBack .p3 false false false s.latch, scan, .left)
      | .p3 => (0, t1State .repairHop .p0 false false false s.latch, scan, .left)
  | .repairHop => (0, t1State .repairSeek .p3 false false false s.latch, scan, .left)
  | .repairDone =>
      (0, bif s.latch then t1AcceptState else t1RejectState, scan, .stay)
  | .startMutation =>
      match s.position with
      | .p0 => (0, t1State .startMutation .p1 false false false s.latch, scan, .right)
      | .p1 => (0, t1State .startMutation .p2 false false false s.latch, scan, .right)
      | .p2 => (0, t1State .startMutation .p3 false false false s.latch, scan, .right)
      | .p3 => (0, t1State .seekSeparator .p0 false false false s.latch, scan, .right)
  | .rewindStart => (0, t1State .rewind .p3 false false false s.latch, scan, .left)
  | .rewind =>
      match s.position with
      | .p3 => (0, t1State .rewind .p2 false false scan s.latch, scan, .left)
      | .p2 => (0, t1State .rewind .p1 false scan s.b2 s.latch, scan, .left)
      | .p1 => (0, t1State .rewind .p0 scan s.b1 s.b2 s.latch, scan, .left)
      | .p0 =>
          if decodeT1Frame? [scan, s.b0, s.b1, s.b2] = some .bof then
            (0, t1State .startMutation .p0 false false false s.latch, scan, .stay)
          else (0, t1State .rewind .p3 false false false s.latch, scan, .left)
  | .probeData =>
      match s.position with
      | .p0 => (0, t1State .probeData .p1 scan false false s.latch, scan, .right)
      | .p1 => (0, t1State .probeData .p2 s.b0 scan false s.latch, scan, .right)
      | .p2 => (0, t1State .probeData .p3 s.b0 s.b1 scan s.latch, scan, .right)
      | .p3 =>
          match decodeT1Frame? [s.b0, s.b1, s.b2, scan] with
          | some (.data value) =>
              (0, t1State .turnInstall .p0 false false false value, scan, .right)
          | some (.output false) => (0, t1OobState s.latch, scan, .stay)
          | _ => (0, t1RejectState, scan, .stay)
  | .turnInstall => (0, t1State .writeCursor .p3 false false false s.latch, scan, .left)
  | .writeCursor =>
      match s.position with
      | .p3 => (0, t1State .writeCursor .p2 false false false s.latch, true, .left)
      | .p2 => (0, t1State .writeCursor .p1 false false false s.latch, true, .left)
      | .p1 => (0, t1State .writeCursor .p0 false false false s.latch, true, .left)
      | .p0 => (0, t1State .seekIndexBack .p3 false false false s.latch, false, .left)
  | .seekIndexBack =>
      match s.position with
      | .p3 => (0, t1State .seekIndexBack .p2 false false scan s.latch, scan, .left)
      | .p2 => (0, t1State .seekIndexBack .p1 false scan s.b2 s.latch, scan, .left)
      | .p1 => (0, t1State .seekIndexBack .p0 scan s.b1 s.b2 s.latch, scan, .left)
      | .p0 =>
          match t1SeekBackComplete scan s.b0 s.b1 s.b2 with
          | .markSpent =>
              (0, t1State .markSpent .p0 false false false s.latch, scan, .stay)
          | .seekIndexBack =>
              (0, t1State .seekIndexBack .p3 false false false s.latch, scan, .left)
          | .successStart => (0, t1SuccessState s.latch, scan, .stay)
          | _ => (0, t1RejectState, scan, .stay)
  | .markSpent =>
      match s.position with
      | .p0 => (0, t1State .markSpent .p1 false false false s.latch, false, .right)
      | .p1 => (0, t1State .markSpent .p2 false false false s.latch, false, .right)
      | .p2 => (0, t1State .markSpent .p3 false false false s.latch, true, .right)
      | .p3 => (0, t1State .seekCursorFwd .p0 false false false s.latch, true, .right)
  | .backupCursor =>
      match s.position with
      | .p0 => (0, t1State .backupCursor .p1 false false false s.latch, scan, .left)
      | .p1 => (0, t1State .backupCursor .p2 false false false s.latch, scan, .left)
      | .p2 => (0, t1State .backupCursor .p3 false false false s.latch, scan, .left)
      | .p3 => (0, t1State .writeData .p0 false false false s.latch, scan, .left)
  | .writeData =>
      match s.position with
      | .p0 => (0, t1State .writeData .p1 false false false s.latch, false, .right)
      | .p1 => (0, t1State .writeData .p2 false false false s.latch, true, .right)
      | .p2 => (0, t1State .writeData .p3 false false false s.latch, s.latch, .right)
      | .p3 => (0, t1State .probeData .p0 false false false s.latch, !s.latch, .right)
  | mode =>
      match s.position with
      | .p0 => (0, t1State mode .p1 scan false false s.latch, scan, .right)
      | .p1 => (0, t1State mode .p2 s.b0 scan false s.latch, scan, .right)
      | .p2 => (0, t1State mode .p3 s.b0 s.b1 scan s.latch, scan, .right)
      | .p3 =>
          let next := t1Complete mode s.b0 s.b1 s.b2 scan
          if next = .reject then (0, t1RejectState, scan, .stay)
          else (0, t1State next .p0 false false false s.latch, scan, .right)

def t1Clock (N : Nat) : Nat := 128 * (N + 1) ^ 2 + 128

/-- The only T1 program declaration: closed finite control and no parameters. -/
def t1CS : ConstStatePhasedProgram T1State where
  numPhases := 1
  startPhase := 0
  startState := t1State .validateBof .p0
  acceptPhase := 0
  acceptState := t1AcceptState
  transition := t1Transition
  timeBound := t1Clock

@[simp] theorem t1CS_numPhases : t1CS.numPhases = 1 := rfl

/-- The public T1 clock in arithmetic normal form.  This theorem is kept out
of the simp set because the generic `toTM_runTime` and `toPhased_timeBound`
simps already reduce the same left-hand side to `t1CS.timeBound N`; callers use
this named theorem to take the additional program-specific step to the expanded
polynomial `t1Clock N` without adding a competing default rewrite. -/
theorem t1CS_runTime (N : Nat) :
    t1CS.toPhased.toTM.runTime N = 128 * (N + 1) ^ 2 + 128 := rfl

/-! ## Standalone transition-table lemmas

Each lemma below is a plain tuple equation about `t1Transition`.  They are the
*only* place the control table is ever reduced; the phase argument is
universally quantified so that callers can instantiate it at whatever
`Fin`-encoded phase their configuration happens to carry. -/

/-! ### Terminal sinks and boundary states -/

@[simp] theorem t1Transition_accept_sink (phase : Fin 1) (scan : Bool) :
    t1Transition phase t1AcceptState scan = (0, t1AcceptState, scan, .stay) := rfl

@[simp] theorem t1Transition_reject_sink (phase : Fin 1) (scan : Bool) :
    t1Transition phase t1RejectState scan = (0, t1RejectState, scan, .stay) := rfl

/-- **The success boundary is active.**  It hands the latched data value to
the output-writing arm without moving the head, which still sits on the first
cell of the `bof` anchor. -/
theorem t1Transition_successStart_active
    (phase : Fin 1) (position : T1FramePosition) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .successStart position b0 b1 b2 latch) scan =
      (0, t1State .outWalk .p0 false false false latch, scan, .stay) := rfl

/-- **The out-of-bounds boundary is active.**  The head already sits on the
last cell of the output frame, which is exactly the entry shape of the
backward repair scan; the latch is cleared to `false`, the reject tag that
`repairDone` will dispatch on. -/
theorem t1Transition_oobStart_active
    (phase : Fin 1) (position : T1FramePosition) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .oobStart position b0 b1 b2 latch) scan =
      (0, t1State .repairSeek .p3 false false false false, scan, .stay) := rfl

/-! ### Cursor installation -/

/-- **The replacement for T1a's idle mutation handoff.**  `startMutation` is
now an active four-step walk off the `bof` anchor into the index scan; the
latch is threaded through unchanged. -/
theorem t1Transition_startMutation_active
    (phase : Fin 1) (position : T1FramePosition) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .startMutation position b0 b1 b2 latch) scan =
      (0, match position with
          | .p0 => t1State .startMutation .p1 false false false latch
          | .p1 => t1State .startMutation .p2 false false false latch
          | .p2 => t1State .startMutation .p3 false false false latch
          | .p3 => t1State .seekSeparator .p0 false false false latch,
        scan, .right) := by
  cases position <;> rfl

theorem t1Transition_probeData_p0
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .probeData .p0 b0 b1 b2 latch) scan =
      (0, t1State .probeData .p1 scan false false latch, scan, .right) := rfl

theorem t1Transition_probeData_p1
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .probeData .p1 b0 b1 b2 latch) scan =
      (0, t1State .probeData .p2 b0 scan false latch, scan, .right) := rfl

theorem t1Transition_probeData_p2
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .probeData .p2 b0 b1 b2 latch) scan =
      (0, t1State .probeData .p3 b0 b1 scan latch, scan, .right) := rfl

private theorem t1Transition_probeData_p3_raw
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .probeData .p3 b0 b1 b2 latch) scan =
      (match decodeT1Frame? [b0, b1, b2, scan] with
       | some (.data value) =>
           (0, t1State .turnInstall .p0 false false false value, scan, .right)
       | some (.output false) => (0, t1OobState latch, scan, .stay)
       | _ => (0, t1RejectState, scan, .stay)) := rfl

/-- Probing a genuine data frame latches its value and turns around. -/
theorem t1Transition_probeData_p3_data
    (phase : Fin 1) (b0 b1 b2 latch scan value : Bool)
    (h : decodeT1Frame? [b0, b1, b2, scan] = some (.data value)) :
    t1Transition phase (t1State .probeData .p3 b0 b1 b2 latch) scan =
      (0, t1State .turnInstall .p0 false false false value, scan, .right) := by
  rw [t1Transition_probeData_p3_raw, h]

/-- Probing the output frame instead means the data field is exhausted: this
is the out-of-bounds boundary. -/
theorem t1Transition_probeData_p3_oob
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool)
    (h : decodeT1Frame? [b0, b1, b2, scan] = some (.output false)) :
    t1Transition phase (t1State .probeData .p3 b0 b1 b2 latch) scan =
      (0, t1OobState latch, scan, .stay) := by
  rw [t1Transition_probeData_p3_raw, h]

theorem t1Transition_turnInstall
    (phase : Fin 1) (position : T1FramePosition) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .turnInstall position b0 b1 b2 latch) scan =
      (0, t1State .writeCursor .p3 false false false latch, scan, .left) := rfl

theorem t1Transition_writeCursor
    (phase : Fin 1) (position : T1FramePosition) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .writeCursor position b0 b1 b2 latch) scan =
      (0, match position with
          | .p3 => t1State .writeCursor .p2 false false false latch
          | .p2 => t1State .writeCursor .p1 false false false latch
          | .p1 => t1State .writeCursor .p0 false false false latch
          | .p0 => t1State .seekIndexBack .p3 false false false latch,
        match position with
        | .p0 => false
        | _ => true,
        .left) := by
  cases position <;> rfl

/-! ### Index consumption -/

theorem t1Transition_seekIndexBack_p3
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .seekIndexBack .p3 b0 b1 b2 latch) scan =
      (0, t1State .seekIndexBack .p2 false false scan latch, scan, .left) := rfl

theorem t1Transition_seekIndexBack_p2
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .seekIndexBack .p2 b0 b1 b2 latch) scan =
      (0, t1State .seekIndexBack .p1 false scan b2 latch, scan, .left) := rfl

theorem t1Transition_seekIndexBack_p1
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .seekIndexBack .p1 b0 b1 b2 latch) scan =
      (0, t1State .seekIndexBack .p0 scan b1 b2 latch, scan, .left) := rfl

private theorem t1Transition_seekIndexBack_p0_raw
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .seekIndexBack .p0 b0 b1 b2 latch) scan =
      (match t1SeekBackComplete scan b0 b1 b2 with
       | .markSpent => (0, t1State .markSpent .p0 false false false latch, scan, .stay)
       | .seekIndexBack =>
           (0, t1State .seekIndexBack .p3 false false false latch, scan, .left)
       | .successStart => (0, t1SuccessState latch, scan, .stay)
       | _ => (0, t1RejectState, scan, .stay)) := rfl

/-- The rightmost unconsumed `index` frame has been located: hand over to the
on-tape decrement without moving. -/
theorem t1Transition_seekIndexBack_p0_mark
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool)
    (h : decodeT1Frame? [scan, b0, b1, b2] = some .index) :
    t1Transition phase (t1State .seekIndexBack .p0 b0 b1 b2 latch) scan =
      (0, t1State .markSpent .p0 false false false latch, scan, .stay) := by
  rw [t1Transition_seekIndexBack_p0_raw]
  simp [t1SeekBackComplete, h, t1SeekBackAdvance]

/-- A frame the backward scan skips over (`spent`, `separator` or a data
frame): keep going left. -/
theorem t1Transition_seekIndexBack_p0_skip
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool) (frame : T1Frame)
    (h : decodeT1Frame? [scan, b0, b1, b2] = some frame)
    (hframe : frame = .spent ∨ frame = .separator ∨ ∃ v, frame = .data v) :
    t1Transition phase (t1State .seekIndexBack .p0 b0 b1 b2 latch) scan =
      (0, t1State .seekIndexBack .p3 false false false latch, scan, .left) := by
  rw [t1Transition_seekIndexBack_p0_raw]
  rcases hframe with rfl | rfl | ⟨v, rfl⟩ <;>
    simp [t1SeekBackComplete, h, t1SeekBackAdvance]

/-- The backward scan reached the `bof` anchor: every index unit has been
consumed, so this is the success boundary. -/
theorem t1Transition_seekIndexBack_p0_success
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool)
    (h : decodeT1Frame? [scan, b0, b1, b2] = some .bof) :
    t1Transition phase (t1State .seekIndexBack .p0 b0 b1 b2 latch) scan =
      (0, t1SuccessState latch, scan, .stay) := by
  rw [t1Transition_seekIndexBack_p0_raw]
  simp [t1SeekBackComplete, h, t1SeekBackAdvance]

theorem t1Transition_markSpent
    (phase : Fin 1) (position : T1FramePosition) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .markSpent position b0 b1 b2 latch) scan =
      (0, match position with
          | .p0 => t1State .markSpent .p1 false false false latch
          | .p1 => t1State .markSpent .p2 false false false latch
          | .p2 => t1State .markSpent .p3 false false false latch
          | .p3 => t1State .seekCursorFwd .p0 false false false latch,
        match position with
        | .p0 => false
        | .p1 => false
        | .p2 => true
        | .p3 => true,
        .right) := by
  cases position <;> rfl

/-! ### Cursor motion -/

theorem t1Transition_backupCursor
    (phase : Fin 1) (position : T1FramePosition) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .backupCursor position b0 b1 b2 latch) scan =
      (0, match position with
          | .p0 => t1State .backupCursor .p1 false false false latch
          | .p1 => t1State .backupCursor .p2 false false false latch
          | .p2 => t1State .backupCursor .p3 false false false latch
          | .p3 => t1State .writeData .p0 false false false latch,
        scan, .left) := by
  cases position <;> rfl

theorem t1Transition_writeData
    (phase : Fin 1) (position : T1FramePosition) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .writeData position b0 b1 b2 latch) scan =
      (0, match position with
          | .p0 => t1State .writeData .p1 false false false latch
          | .p1 => t1State .writeData .p2 false false false latch
          | .p2 => t1State .writeData .p3 false false false latch
          | .p3 => t1State .probeData .p0 false false false latch,
        match position with
        | .p0 => false
        | .p1 => true
        | .p2 => latch
        | .p3 => !latch,
        .right) := by
  cases position <;> rfl

/-! ### The success arm: output traversal and output write -/

theorem t1Transition_outWalk
    (phase : Fin 1) (position : T1FramePosition) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .outWalk position b0 b1 b2 latch) scan =
      (0, match position with
          | .p0 => t1State .outWalk .p1 false false false latch
          | .p1 => t1State .outWalk .p2 false false false latch
          | .p2 => t1State .outWalk .p3 false false false latch
          | .p3 => t1State .outSeekCursor .p0 false false false latch,
        scan, .right) := by
  cases position <;> rfl

theorem t1Transition_outBackup
    (phase : Fin 1) (position : T1FramePosition) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .outBackup position b0 b1 b2 latch) scan =
      (0, match position with
          | .p0 => t1State .outBackup .p1 false false false latch
          | .p1 => t1State .outBackup .p2 false false false latch
          | .p2 => t1State .outBackup .p3 false false false latch
          | .p3 => t1State .outWriteData .p0 false false false latch,
        scan, .left) := by
  cases position <;> rfl

/-- The cursor restore on the success arm: the same four ascending writes as
`writeData`, but handing over to the output-frame search instead of the next
probe. -/
theorem t1Transition_outWriteData
    (phase : Fin 1) (position : T1FramePosition) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .outWriteData position b0 b1 b2 latch) scan =
      (0, match position with
          | .p0 => t1State .outWriteData .p1 false false false latch
          | .p1 => t1State .outWriteData .p2 false false false latch
          | .p2 => t1State .outWriteData .p3 false false false latch
          | .p3 => t1State .outSeekOutput .p0 false false false latch,
        match position with
        | .p0 => false
        | .p1 => true
        | .p2 => latch
        | .p3 => !latch,
        .right) := by
  cases position <;> rfl

theorem t1Transition_outTurn
    (phase : Fin 1) (position : T1FramePosition) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .outTurn position b0 b1 b2 latch) scan =
      (0, t1State .outWriteOut .p3 false false false latch, scan, .left) := rfl

/-- **The output write.**  Four descending writes turn `output false` into
`output latch`; only the last cell of the frame can change value.  The latch
is then re-used as the *accept tag* for the shared repair pass. -/
theorem t1Transition_outWriteOut
    (phase : Fin 1) (position : T1FramePosition) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .outWriteOut position b0 b1 b2 latch) scan =
      (0, match position with
          | .p3 => t1State .outWriteOut .p2 false false false latch
          | .p2 => t1State .outWriteOut .p1 false false false latch
          | .p1 => t1State .outWriteOut .p0 false false false latch
          | .p0 => t1State .repairSeek .p3 false false false true,
        match position with
        | .p3 => latch
        | .p2 => false
        | .p1 => false
        | .p0 => true,
        .left) := by
  cases position <;> rfl

/-! ### The shared right-to-left `spent ↦ index` repair -/

theorem t1Transition_repairSeek_p3
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .repairSeek .p3 b0 b1 b2 latch) scan =
      (0, t1State .repairSeek .p2 false false scan latch, scan, .left) := rfl

theorem t1Transition_repairSeek_p2
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .repairSeek .p2 b0 b1 b2 latch) scan =
      (0, t1State .repairSeek .p1 false scan b2 latch, scan, .left) := rfl

theorem t1Transition_repairSeek_p1
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .repairSeek .p1 b0 b1 b2 latch) scan =
      (0, t1State .repairSeek .p0 scan b1 b2 latch, scan, .left) := rfl

private theorem t1Transition_repairSeek_p0_raw
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .repairSeek .p0 b0 b1 b2 latch) scan =
      (match t1RepairBackComplete scan b0 b1 b2 with
       | .repairWrite =>
           (0, t1State .repairWrite .p0 false false false latch, scan, .stay)
       | .repairSeek =>
           (0, t1State .repairSeek .p3 false false false latch, scan, .left)
       | .repairDone =>
           (0, t1State .repairDone .p0 false false false latch, scan, .stay)
       | _ => (0, t1RejectState, scan, .stay)) := rfl

/-- A `spent` marker: rewrite it back to `index` without moving. -/
theorem t1Transition_repairSeek_p0_write
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool)
    (h : decodeT1Frame? [scan, b0, b1, b2] = some .spent) :
    t1Transition phase (t1State .repairSeek .p0 b0 b1 b2 latch) scan =
      (0, t1State .repairWrite .p0 false false false latch, scan, .stay) := by
  rw [t1Transition_repairSeek_p0_raw]
  simp [t1RepairBackComplete, h, t1RepairBackAdvance]

/-- A frame the repair scan skips: keep going left. -/
theorem t1Transition_repairSeek_p0_skip
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool) (frame : T1Frame)
    (h : decodeT1Frame? [scan, b0, b1, b2] = some frame)
    (hframe : frame = .index ∨ frame = .separator ∨ frame = .finish ∨
      (∃ v, frame = .data v) ∨ ∃ v, frame = .output v) :
    t1Transition phase (t1State .repairSeek .p0 b0 b1 b2 latch) scan =
      (0, t1State .repairSeek .p3 false false false latch, scan, .left) := by
  rw [t1Transition_repairSeek_p0_raw]
  rcases hframe with rfl | rfl | rfl | ⟨v, rfl⟩ | ⟨v, rfl⟩ <;>
    simp [t1RepairBackComplete, h, t1RepairBackAdvance]

/-- The `bof` anchor: the index field is fully repaired, dispatch. -/
theorem t1Transition_repairSeek_p0_done
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool)
    (h : decodeT1Frame? [scan, b0, b1, b2] = some .bof) :
    t1Transition phase (t1State .repairSeek .p0 b0 b1 b2 latch) scan =
      (0, t1State .repairDone .p0 false false false latch, scan, .stay) := by
  rw [t1Transition_repairSeek_p0_raw]
  simp [t1RepairBackComplete, h, t1RepairBackAdvance]

/-- The inverse of `markSpent`: four ascending writes of `T1Frame.index`. -/
theorem t1Transition_repairWrite
    (phase : Fin 1) (position : T1FramePosition) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .repairWrite position b0 b1 b2 latch) scan =
      (0, match position with
          | .p0 => t1State .repairWrite .p1 false false false latch
          | .p1 => t1State .repairWrite .p2 false false false latch
          | .p2 => t1State .repairWrite .p3 false false false latch
          | .p3 => t1State .repairBack .p0 false false false latch,
        match position with
        | .p0 => false
        | .p1 => false
        | .p2 => true
        | .p3 => false,
        .right) := by
  cases position <;> rfl

theorem t1Transition_repairBack
    (phase : Fin 1) (position : T1FramePosition) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .repairBack position b0 b1 b2 latch) scan =
      (0, match position with
          | .p0 => t1State .repairBack .p1 false false false latch
          | .p1 => t1State .repairBack .p2 false false false latch
          | .p2 => t1State .repairBack .p3 false false false latch
          | .p3 => t1State .repairHop .p0 false false false latch,
        scan, .left) := by
  cases position <;> rfl

/-- One more left step off the repaired frame, back onto the last cell of its
predecessor: the repair scan's entry shape. -/
theorem t1Transition_repairHop
    (phase : Fin 1) (position : T1FramePosition) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .repairHop position b0 b1 b2 latch) scan =
      (0, t1State .repairSeek .p3 false false false latch, scan, .left) := rfl

/-! ### Final dispatch

`repairDone` is the only mode that enters a sink.  Both branches enter
*literally* `t1AcceptState` / `t1RejectState`: every scratch bit and the latch
are cleared, which is what makes `TM.accepts` — a comparison of the full
`Sigma` state against `t1CS.acceptState` — able to fire at all. -/

theorem t1Transition_repairDone_accept
    (phase : Fin 1) (position : T1FramePosition) (b0 b1 b2 scan : Bool) :
    t1Transition phase (t1State .repairDone position b0 b1 b2 true) scan =
      (0, t1AcceptState, scan, .stay) := rfl

theorem t1Transition_repairDone_reject
    (phase : Fin 1) (position : T1FramePosition) (b0 b1 b2 scan : Bool) :
    t1Transition phase (t1State .repairDone position b0 b1 b2 false) scan =
      (0, t1RejectState, scan, .stay) := rfl

/-- The dispatch target is the program's own accept state, with no residual
latch or buffer content. -/
theorem t1Transition_repairDone_acceptState :
    t1AcceptState = t1CS.acceptState := rfl

/-! ### The read-only rewind (T1a) -/

theorem t1Transition_rewindStart
    (phase : Fin 1) (position : T1FramePosition) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .rewindStart position b0 b1 b2 latch) scan =
      (0, t1State .rewind .p3 false false false latch, scan, .left) := rfl

theorem t1Transition_rewind_p3
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .rewind .p3 b0 b1 b2 latch) scan =
      (0, t1State .rewind .p2 false false scan latch, scan, .left) := rfl

theorem t1Transition_rewind_p2
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .rewind .p2 b0 b1 b2 latch) scan =
      (0, t1State .rewind .p1 false scan b2 latch, scan, .left) := rfl

theorem t1Transition_rewind_p1
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State .rewind .p1 b0 b1 b2 latch) scan =
      (0, t1State .rewind .p0 scan b1 b2 latch, scan, .left) := rfl

theorem t1Transition_rewind_p0_bof
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool)
    (h : decodeT1Frame? [scan, b0, b1, b2] = some .bof) :
    t1Transition phase (t1State .rewind .p0 b0 b1 b2 latch) scan =
      (0, t1State .startMutation .p0 false false false latch, scan, .stay) := by
  show (if decodeT1Frame? [scan, b0, b1, b2] = some .bof then _ else _) = _
  rw [if_pos h]
  rfl

theorem t1Transition_rewind_p0_other
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool)
    (h : decodeT1Frame? [scan, b0, b1, b2] ≠ some .bof) :
    t1Transition phase (t1State .rewind .p0 b0 b1 b2 latch) scan =
      (0, t1State .rewind .p3 false false false latch, scan, .left) := by
  show (if decodeT1Frame? [scan, b0, b1, b2] = some .bof then _ else _) = _
  rw [if_neg h]
  rfl

/-! ### The shared forward frame reader

These four lemmas cover every mode satisfying `T1ForwardMode`, which is the
five T1a validation modes together with `seekSeparator` and `seekCursorFwd`.
Each is discharged by seven `rfl`s through `T1ForwardMode.cases`. -/

theorem t1Transition_forward_p0 {mode : T1Mode} (hmode : T1ForwardMode mode)
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State mode .p0 b0 b1 b2 latch) scan =
      (0, t1State mode .p1 scan false false latch, scan, .right) := by
  rcases hmode.cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem t1Transition_forward_p1 {mode : T1Mode} (hmode : T1ForwardMode mode)
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State mode .p1 b0 b1 b2 latch) scan =
      (0, t1State mode .p2 b0 scan false latch, scan, .right) := by
  rcases hmode.cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem t1Transition_forward_p2 {mode : T1Mode} (hmode : T1ForwardMode mode)
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State mode .p2 b0 b1 b2 latch) scan =
      (0, t1State mode .p3 b0 b1 scan latch, scan, .right) := by
  rcases hmode.cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem t1Transition_forward_p3_raw {mode : T1Mode}
    (hmode : T1ForwardMode mode)
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool) :
    t1Transition phase (t1State mode .p3 b0 b1 b2 latch) scan =
      (if t1Complete mode b0 b1 b2 scan = .reject then
        (0, t1RejectState, scan, .stay)
      else
        (0, t1State (t1Complete mode b0 b1 b2 scan) .p0 false false false latch,
          scan, .right)) := by
  rcases hmode.cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Completing a grammar-valid frame: enter the next mode one cell to the
right, carrying the latch. -/
theorem t1Transition_forward_p3_advance {mode : T1Mode}
    (hmode : T1ForwardMode mode)
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool)
    (hne : t1Complete mode b0 b1 b2 scan ≠ .reject) :
    t1Transition phase (t1State mode .p3 b0 b1 b2 latch) scan =
      (0, t1State (t1Complete mode b0 b1 b2 scan) .p0 false false false latch,
        scan, .right) := by
  rw [t1Transition_forward_p3_raw hmode, if_neg hne]

/-- Completing an invalid frame: stable reject, tape and head unchanged. -/
theorem t1Transition_forward_p3_reject {mode : T1Mode}
    (hmode : T1ForwardMode mode)
    (phase : Fin 1) (b0 b1 b2 latch scan : Bool)
    (heq : t1Complete mode b0 b1 b2 scan = .reject) :
    t1Transition phase (t1State mode .p3 b0 b1 b2 latch) scan =
      (0, t1RejectState, scan, .stay) := by
  rw [t1Transition_forward_p3_raw hmode, if_pos heq]

end Pnp3.Internal.PsubsetPpoly.TM
