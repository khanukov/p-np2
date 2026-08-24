import Complexity.TMVerifier.TuringToolkit.FrameScannerKernel
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Sigma

/-!
# A non-T1 instance of the frame-scanner kernel (genericity probe)

This module exists to witness that `FrameScannerKernel` is genuinely generic
and not a T1 wrapper.  It defines, from scratch and with **no T1 import**:

* `ProbeFrame` — a different frame alphabet with different codewords,
  including the `1011` separator code that the planned `G1` gate ABI reserves
  for `argSep`;
* `probeFrameCodec` — its fixed-width codec, with the round trip proved;
* `ProbeMode`/`ProbeState`/`probeCS` — a different mode set, a different
  control-state record (its carried context is a *pair* of Booleans, not T1's
  single latch), and a different `ConstStatePhasedProgram` with its own clock;
* `probeFrameScanner` — the instance, whose five obligations are discharged by
  small standalone table lemmas exactly as T1's are.

It then applies the kernel unchanged: `probeCS_frame_macrostep` is the
four-step macrostep, `probeCS_scan_frames` the arbitrary-context list scan,
and `probeCS_scan_probeWord` a fully concrete six-frame,
twenty-four-step run of a `tag · argSep · datum · argSep · datum · stop`
word — a word shaped like a `G1` gate request, scanned by a machine that has
never heard of `T1Frame`.

Nothing downstream depends on this module; it is an audit surface.
-/

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace TM

namespace FrameScan

/-! ## A different four-bit alphabet -/

/-- A gate-request-shaped alphabet: an argument separator, a unary tag, data
frames and a terminator.  The codewords deliberately differ from `T1Frame`'s,
and `pargSep` uses the `1011` code reserved for `G1`'s `argSep`. -/
inductive ProbeFrame
  | pblank | ptag | pargSep | pdatum (value : Bool) | pstop
  deriving DecidableEq, Repr

def ProbeFrame.bits : ProbeFrame → List Bool
  | .pblank       => [false, false, false, false]
  | .ptag         => [true,  true,  false, false]
  | .pargSep      => [true,  false, true,  true ]
  | .pdatum false => [false, true,  false, true ]
  | .pdatum true  => [false, true,  true,  false]
  | .pstop        => [true,  true,  true,  true ]

def decodeProbeFrame? : List Bool → Option ProbeFrame
  | [false, false, false, false] => some .pblank
  | [true,  true,  false, false] => some .ptag
  | [true,  false, true,  true ] => some .pargSep
  | [false, true,  false, true ] => some (.pdatum false)
  | [false, true,  true,  false] => some (.pdatum true)
  | [true,  true,  true,  true ] => some .pstop
  | _ => none

/-- The probe alphabet as a fixed-width codec. -/
def probeFrameCodec : FrameCodec ProbeFrame where
  bits := ProbeFrame.bits
  decode? := decodeProbeFrame?
  bits_length := by
    intro f
    cases f with
    | pdatum b => cases b <;> rfl
    | pblank | ptag | pargSep | pstop => rfl
  decode_bits := by
    intro f
    cases f with
    | pdatum b => cases b <;> rfl
    | pblank | ptag | pargSep | pstop => rfl

/-! ## A different control table -/

/-- Probe modes: scan the unary tag, then the argument list, then the data
region, then stop.  `bad` is the grammar-violation mode. -/
inductive ProbeMode
  | scanTag | scanArgs | scanData | done | bad
  deriving Fintype, DecidableEq, Repr

inductive ProbePos | q0 | q1 | q2 | q3
  deriving Fintype, DecidableEq, Repr

set_option synthInstance.maxSize 512 in
/-- The probe's control state.  Note the carried context is *two* Booleans
(the `pass`/`crossed` pair `G1` needs), instantiating the kernel's `Aux` at
`Bool × Bool` rather than T1's `Bool`.

The `synthInstance.maxSize` bump is only for the derived `Fintype`: the
`ProxyType` sigma tower of a six-field record with a product field exceeds the
default search size. -/
structure ProbeState where
  mode : ProbeMode
  position : ProbePos
  b0 : Bool
  b1 : Bool
  b2 : Bool
  ctx : Bool × Bool
  deriving Fintype, DecidableEq, Repr

def probeState (mode : ProbeMode) (position : ProbePos)
    (b0 := false) (b1 := false) (b2 := false)
    (ctx : Bool × Bool := (false, false)) : ProbeState :=
  ⟨mode, position, b0, b1, b2, ctx⟩

def probeRejectState : ProbeState := probeState .bad .q0

def probeAdvance : ProbeMode → ProbeFrame → ProbeMode
  | .scanTag, .ptag => .scanTag
  | .scanTag, .pargSep => .scanArgs
  | .scanArgs, .pdatum _ => .scanArgs
  | .scanArgs, .pargSep => .scanData
  | .scanData, .pdatum _ => .scanData
  | .scanData, .pstop => .done
  | _, _ => .bad

def probeComplete (mode : ProbeMode) (b0 b1 b2 b3 : Bool) : ProbeMode :=
  match decodeProbeFrame? [b0, b1, b2, b3] with
  | some frame => probeAdvance mode frame
  | none => .bad

def ProbeForwardMode : ProbeMode → Prop
  | .scanTag | .scanArgs | .scanData => True
  | _ => False

theorem ProbeForwardMode.cases {mode : ProbeMode} (h : ProbeForwardMode mode) :
    mode = .scanTag ∨ mode = .scanArgs ∨ mode = .scanData := by
  cases mode <;> simp_all [ProbeForwardMode]

def probeTransition (_phase : Fin 1) (s : ProbeState) (scan : Bool) :
    Fin 1 × ProbeState × Bool × Move :=
  match s.mode with
  | .done => (0, probeState .done .q0 false false false s.ctx,
      scan, .stay)
  | .bad => (0, probeRejectState, scan, .stay)
  | mode =>
      match s.position with
      | .q0 => (0, probeState mode .q1 scan false false s.ctx,
          scan, .right)
      | .q1 => (0, probeState mode .q2 s.b0 scan false s.ctx,
          scan, .right)
      | .q2 => (0, probeState mode .q3 s.b0 s.b1 scan s.ctx,
          scan, .right)
      | .q3 =>
          let next := probeComplete mode s.b0 s.b1 s.b2 scan
          if next = .bad then (0, probeRejectState, scan, .stay)
          else (0, probeState next .q0 false false false s.ctx,
            scan, .right)

def probeClock (N : Nat) : Nat := 16 * (N + 1)

/-- The probe program: zero parameters, one phase, its own clock. -/
def probeCS : ConstStatePhasedProgram ProbeState where
  numPhases := 1
  startPhase := 0
  startState := probeState .scanTag .q0
  acceptPhase := 0
  acceptState := probeState .done .q0
  transition := probeTransition
  timeBound := probeClock

/-! ### Standalone table lemmas (the only place `probeTransition` reduces) -/

theorem probeTransition_p0 {mode : ProbeMode} (hm : ProbeForwardMode mode)
    (phase : Fin 1) (b0 b1 b2 scan : Bool) (ctx : Bool × Bool) :
    probeTransition phase (probeState mode .q0 b0 b1 b2 ctx) scan =
      (0, probeState mode .q1 scan false false ctx, scan, .right) := by
  rcases hm.cases with rfl | rfl | rfl <;> rfl

theorem probeTransition_p1 {mode : ProbeMode} (hm : ProbeForwardMode mode)
    (phase : Fin 1) (b0 b1 b2 scan : Bool) (ctx : Bool × Bool) :
    probeTransition phase (probeState mode .q1 b0 b1 b2 ctx) scan =
      (0, probeState mode .q2 b0 scan false ctx, scan, .right) := by
  rcases hm.cases with rfl | rfl | rfl <;> rfl

theorem probeTransition_p2 {mode : ProbeMode} (hm : ProbeForwardMode mode)
    (phase : Fin 1) (b0 b1 b2 scan : Bool) (ctx : Bool × Bool) :
    probeTransition phase (probeState mode .q2 b0 b1 b2 ctx) scan =
      (0, probeState mode .q3 b0 b1 scan ctx, scan, .right) := by
  rcases hm.cases with rfl | rfl | rfl <;> rfl

private theorem probeTransition_p3_raw {mode : ProbeMode}
    (hm : ProbeForwardMode mode)
    (phase : Fin 1) (b0 b1 b2 scan : Bool) (ctx : Bool × Bool) :
    probeTransition phase (probeState mode .q3 b0 b1 b2 ctx) scan =
      (if probeComplete mode b0 b1 b2 scan = .bad then
          (0, probeRejectState, scan, .stay)
        else
          (0, probeState (probeComplete mode b0 b1 b2 scan) .q0 false false
            false ctx, scan, .right)) := by
  rcases hm.cases with rfl | rfl | rfl <;> rfl

theorem probeTransition_p3 {mode : ProbeMode} (hm : ProbeForwardMode mode)
    (phase : Fin 1) (b0 b1 b2 scan : Bool) (ctx : Bool × Bool)
    (hne : probeComplete mode b0 b1 b2 scan ≠ .bad) :
    probeTransition phase (probeState mode .q3 b0 b1 b2 ctx) scan =
      (0, probeState (probeComplete mode b0 b1 b2 scan) .q0 false false false
        ctx, scan, .right) := by
  rw [probeTransition_p3_raw hm, if_neg hne]

/-! ## The instance -/

/-- **A second, non-T1 instance of the kernel.**  Different alphabet,
different modes, different program, different context type. -/
def probeFrameScanner : FrameScanner ProbeState ProbeFrame ProbeMode
    (Bool × Bool) where
  program := probeCS
  phase := probeCS.startPhase
  codec := probeFrameCodec
  rejectMode := .bad
  advance := probeAdvance
  complete := probeComplete
  Forward := ProbeForwardMode
  st0 := fun mode a => probeState mode .q0 false false false a
  st1 := fun mode a b0 => probeState mode .q1 b0 false false a
  st2 := fun mode a b0 b1 => probeState mode .q2 b0 b1 false a
  st3 := fun mode a b0 b1 b2 => probeState mode .q3 b0 b1 b2 a
  complete_decode := fun m b0 b1 b2 b3 => by
    cases h : decodeProbeFrame? [b0, b1, b2, b3] <;>
      simp [probeComplete, probeFrameCodec, h]
  step_p0 := fun hm a scan =>
    probeTransition_p0 hm probeCS.startPhase false false false scan a
  step_p1 := fun hm a b0 scan =>
    probeTransition_p1 hm probeCS.startPhase b0 false false scan a
  step_p2 := fun hm a b0 b1 scan =>
    probeTransition_p2 hm probeCS.startPhase b0 b1 false scan a
  step_p3 := fun hm a b0 b1 b2 scan hne =>
    probeTransition_p3 hm probeCS.startPhase b0 b1 b2 scan a hne

/-! ## The kernel, applied to the probe

These are named instantiations, not re-proofs: the right-hand sides are the
generic theorems of `FrameScannerKernel`. -/

/-- The generic four-step macrostep, at the probe machine. -/
theorem probeCS_frame_macrostep (n h : Nat)
    (hsafe : h + 4 < probeFrameScanner.machine.tapeLength n)
    (tape : Fin (probeFrameScanner.machine.tapeLength n) → Bool)
    (mode : ProbeMode) (frame : ProbeFrame) (a : Bool × Bool)
    (hm : ProbeForwardMode mode) (hnext : probeAdvance mode frame ≠ .bad)
    (hbits : physicalBitsAt hsafe tape = frame.bits) :
    TM.runConfig (M := probeFrameScanner.machine)
        (probeFrameScanner.alignedFrame n h (by omega) tape mode a) 4 =
      probeFrameScanner.alignedFrame n (h + 4) hsafe tape
        (probeAdvance mode frame) a :=
  probeFrameScanner.frameMacrostep n h hsafe tape mode frame a hm hnext hbits

/-- The generic list scan, at the probe machine: exactly four steps per frame
over an arbitrary surrounding tape. -/
theorem probeCS_scan_frames (n : Nat)
    (pre frames suffix : List ProbeFrame) (mode : ProbeMode) (a : Bool × Bool)
    (hpath : probeFrameScanner.ValidPath mode frames)
    (hsafe : 4 * (pre.length + frames.length) <
      probeFrameScanner.machine.tapeLength n) :
    TM.runConfig (M := probeFrameScanner.machine)
        (probeFrameScanner.alignedFrame n (4 * pre.length) (by omega)
          (frameListTape ((pre ++ frames ++ suffix).flatMap ProbeFrame.bits))
          mode a)
        (4 * frames.length) =
      probeFrameScanner.alignedFrame n (4 * (pre.length + frames.length)) hsafe
        (frameListTape ((pre ++ frames ++ suffix).flatMap ProbeFrame.bits))
        (probeFrameScanner.advanceList mode frames) a :=
  probeFrameScanner.scanFrames n pre frames suffix mode a hpath hsafe

/-! ### A concrete gate-request-shaped word -/

/-- `tag · argSep · datum true · argSep · datum false · stop`: six frames
shaped like a two-operand `G1` request. -/
def probeWord : List ProbeFrame :=
  [.ptag, .pargSep, .pdatum true, .pargSep, .pdatum false, .pstop]

theorem probeWord_validPath :
    probeFrameScanner.ValidPath .scanTag probeWord := by
  refine ⟨trivial, by decide, trivial, by decide, trivial, by decide,
    trivial, by decide, trivial, by decide, trivial, by decide, trivial⟩

theorem probeWord_advanceList :
    probeFrameScanner.advanceList .scanTag probeWord = .done := rfl

/-- **Concrete non-T1 scan.**  Twenty-four genuine TM steps take the probe
machine across the whole six-frame word, from `scanTag` to `done`, with the
tape and the two-Boolean context untouched. -/
theorem probeCS_scan_probeWord (n : Nat)
    (hsafe : 24 < probeFrameScanner.machine.tapeLength n) (a : Bool × Bool) :
    TM.runConfig (M := probeFrameScanner.machine)
        (probeFrameScanner.alignedFrame n 0 (by omega)
          (frameListTape (probeWord.flatMap ProbeFrame.bits)) .scanTag a) 24 =
      probeFrameScanner.alignedFrame n 24 hsafe
        (frameListTape (probeWord.flatMap ProbeFrame.bits)) .done a := by
  have h := probeFrameScanner.scanFrames n [] probeWord [] .scanTag a
    probeWord_validPath (by simpa [probeWord] using hsafe)
  simpa [probeWord, probeWord_advanceList] using h

end FrameScan

end TM
end PsubsetPpoly
end Internal
end Pnp3
