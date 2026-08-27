import Complexity.TMVerifier.TuringToolkit.FrameScannerKernel
import Complexity.TMVerifier.TuringToolkit.GateOneControl

/-!
# G1 as an instance of the generic frame-scanner kernel

**Progress classification: Infrastructure.**

`g1FrameCodec` presents the G1 alphabet as a `FrameCodec`; `g1FrameScanner`
presents the G1 control as a `FrameScanner`: the program `g1CS`, its single
phase, the shared table `g1Advance`/`g1Complete`, the predicate
`G1ForwardMode`, and the four aligned states of `G1State`, whose carried
context (`Aux`) is the three-Boolean `G1Ctx`.

**No T1 proof stack is duplicated.**  All five obligations are discharged by
the standalone tuple lemmas of `GateOneControl`; nothing here unfolds
`g1Transition`, and the multi-frame validation scan of `GateOneValidation` is
the *generic* `FrameScanner.scanFrames` instantiated here, not a re-proof.
Semantic content is carried by theorems, never by a structure field.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

/-- The concrete G1 machine. -/
abbrev G1M := g1CS.toPhased.toTM

/-- **G1 is an instance of the generic kernel.**  It reuses the pure-layer
`g1FrameCodec`; the carried context is the three-Boolean `G1Ctx`, threaded
through every frame unchanged. -/
def g1FrameScanner : FrameScanner G1State G1Frame G1Mode G1Ctx where
  program := g1CS
  phase := g1CS.startPhase
  codec := g1FrameCodec
  rejectMode := .reject
  advance := g1Advance
  complete := g1Complete
  Forward := G1ForwardMode
  st0 := fun mode ctx => g1State mode .p0 false false false ctx
  st1 := fun mode ctx b0 => g1State mode .p1 b0 false false ctx
  st2 := fun mode ctx b0 b1 => g1State mode .p2 b0 b1 false ctx
  st3 := fun mode ctx b0 b1 b2 => g1State mode .p3 b0 b1 b2 ctx
  complete_decode := fun m b0 b1 b2 b3 => by
    cases h : decodeG1Frame? [b0, b1, b2, b3] <;>
      simp [g1Complete, g1FrameCodec, h]
  step_p0 := fun hmode ctx scan =>
    g1Transition_forward_p0 hmode g1CS.startPhase false false false scan ctx
  step_p1 := fun hmode ctx b0 scan =>
    g1Transition_forward_p1 hmode g1CS.startPhase b0 false false scan ctx
  step_p2 := fun hmode ctx b0 b1 scan =>
    g1Transition_forward_p2 hmode g1CS.startPhase b0 b1 false scan ctx
  step_p3 := fun hmode ctx b0 b1 b2 scan hne =>
    g1Transition_forward_p3_advance hmode g1CS.startPhase b0 b1 b2 scan ctx hne

@[simp] theorem g1FrameScanner_program : g1FrameScanner.program = g1CS := rfl

@[simp] theorem g1FrameScanner_machine : g1FrameScanner.machine = G1M := rfl

@[simp] theorem g1FrameScanner_phase :
    g1FrameScanner.phase = g1CS.toPhased.startPhase := rfl

@[simp] theorem g1FrameScanner_advance :
    g1FrameScanner.advance = g1Advance := rfl

@[simp] theorem g1FrameScanner_st0 (mode : G1Mode) (ctx : G1Ctx) :
    g1FrameScanner.st0 mode ctx = g1State mode .p0 false false false ctx := rfl

/-! ## The kernel's frame language is the control's frame language

`GateOneControl` proves the whole canonical-grammar correspondence about the
local fold `g1AdvanceList` and the local path predicate `G1ValidPath`.  These
two bridges say the generic kernel's `advanceList`/`ValidPath` at this instance
*are* those, so every grammar theorem of `GateOneControl` — in particular
`g1Automaton_accepts_iff_decode` — applies verbatim to the executable scan. -/

@[simp] theorem g1FrameScanner_advanceList (mode : G1Mode) (fs : List G1Frame) :
    g1FrameScanner.advanceList mode fs = g1AdvanceList mode fs := by
  induction fs generalizing mode with
  | nil => rfl
  | cons frame rest ih => simpa using ih (g1Advance mode frame)

@[simp] theorem g1FrameScanner_validPath (mode : G1Mode) (fs : List G1Frame) :
    g1FrameScanner.ValidPath mode fs ↔ G1ValidPath mode fs := by
  induction fs generalizing mode with
  | nil => exact Iff.rfl
  | cons frame rest ih =>
      show (G1ForwardMode mode ∧ g1Advance mode frame ≠ .reject ∧
        g1FrameScanner.ValidPath (g1Advance mode frame) rest) ↔ _
      rw [ih (g1Advance mode frame)]
      exact Iff.rfl

/-- **The executable scan validates exactly the canonical grammar.**  The
kernel-level forward run of a frame word closed by the explicit end-of-input
frame reaches `rewindStart` precisely when the pure parser decodes it. -/
theorem g1FrameScanner_accepts_iff_decode (fs : List G1Frame) :
    g1FrameScanner.advanceList .vBof (fs ++ [.blank]) = .rewindStart ↔
      ∃ r : G1Request, decodeG1FrameList? fs = some r := by
  rw [g1FrameScanner_advanceList]
  exact g1Automaton_accepts_iff_decode fs

/-- The generic four-step macrostep, at the G1 machine. -/
theorem g1FrameScanner_frameMacrostep (n h : Nat)
    (hsafe : h + 4 < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (mode : G1Mode) (frame : G1Frame)
    (ctx : G1Ctx) (hmode : G1ForwardMode mode)
    (hnext : g1Advance mode frame ≠ .reject)
    (hbits : physicalBitsAt hsafe tape = frame.bits) :
    TM.runConfig (M := G1M)
        (g1FrameScanner.alignedFrame n h
          (by show h < G1M.tapeLength n; omega) tape mode ctx) 4 =
      g1FrameScanner.alignedFrame n (h + 4) hsafe tape
        (g1Advance mode frame) ctx :=
  g1FrameScanner.frameMacrostep n h hsafe tape mode frame ctx hmode hnext hbits

/-- The generic exact list-scan induction, at the G1 machine. -/
theorem g1FrameScanner_scanFrames (n : Nat)
    (pre frames suffix : List G1Frame) (mode : G1Mode) (ctx : G1Ctx)
    (hpath : g1FrameScanner.ValidPath mode frames)
    (hsafe : 4 * (pre.length + frames.length) < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1FrameScanner.alignedFrame n (4 * pre.length)
          (by show 4 * pre.length < G1M.tapeLength n; omega)
          (frameListTape ((pre ++ frames ++ suffix).flatMap G1Frame.bits))
          mode ctx)
        (4 * frames.length) =
      g1FrameScanner.alignedFrame n (4 * (pre.length + frames.length)) hsafe
        (frameListTape ((pre ++ frames ++ suffix).flatMap G1Frame.bits))
        (g1FrameScanner.advanceList mode frames) ctx :=
  g1FrameScanner.scanFrames n pre frames suffix mode ctx hpath hsafe

end Pnp3.Internal.PsubsetPpoly.TM
