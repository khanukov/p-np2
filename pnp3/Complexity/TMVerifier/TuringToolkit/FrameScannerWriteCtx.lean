import Complexity.TMVerifier.TuringToolkit.FrameScannerWrite

/-!
# Context-dependent rightward frame writer

The fixed `FrameWriter` installs one constant frame.  A shuttle must instead
restore the source held in finite auxiliary control, so its rightward target
depends on that control.  `FrameWriterCtx` is the genuine machine-level
variant: four transition tuples write `target a`, and the exact four-step and
arbitrary-list theorems are derived through the phased step bridge.
-/
namespace Pnp3.Internal.PsubsetPpoly.TM.FrameScan

universe v

open Pnp3.Internal.PsubsetPpoly.TM

/-- A four-cell left-to-right writer whose target is computed from `Aux`.
There is no semantic run/provider field: execution follows from the codec law
and the four concrete transition rows. -/
structure FrameWriterCtx (S : Type v) [Fintype S] [DecidableEq S]
    (F Aux : Type v) where
  program : ConstStatePhasedProgram S
  phase : Fin program.numPhases
  codec : FrameCodec F
  target : Aux → F
  w0 : Aux → Bool
  w1 : Aux → Bool
  w2 : Aux → Bool
  w3 : Aux → Bool
  wst0 : Aux → S
  wst1 : Aux → S
  wst2 : Aux → S
  wst3 : Aux → S
  exitState : Aux → S
  target_bits : ∀ a, codec.bits (target a) = [w0 a, w1 a, w2 a, w3 a]
  wstep_p0 : ∀ a scan,
    program.transition phase (wst0 a) scan =
      (phase, wst1 a, w0 a, Move.right)
  wstep_p1 : ∀ a scan,
    program.transition phase (wst1 a) scan =
      (phase, wst2 a, w1 a, Move.right)
  wstep_p2 : ∀ a scan,
    program.transition phase (wst2 a) scan =
      (phase, wst3 a, w2 a, Move.right)
  wstep_p3 : ∀ a scan,
    program.transition phase (wst3 a) scan =
      (phase, exitState a, w3 a, Move.right)

namespace FrameWriterCtx

variable {S : Type v} [Fintype S] [DecidableEq S] {F Aux : Type v}

abbrev machine (W : FrameWriterCtx S F Aux) : TM.{v} :=
  Phased.machine W.program

abbrev alignedConfigQ (W : FrameWriterCtx S F Aux) (n h : Nat)
    (hh : h < W.machine.tapeLength n)
    (tape : Fin (W.machine.tapeLength n) → Bool) (q : S) :
    Configuration (M := W.machine) n :=
  Phased.alignedAt W.program W.phase n h hh tape q

/-- Exact four-step context writer: all program, phase and codec data are the
writer's own, the head advances by four, and the target is `target a`. -/
theorem writeMacrostep (W : FrameWriterCtx S F Aux) (n base : Nat)
    (hsafe : base + 4 < W.machine.tapeLength n)
    (tape : Fin (W.machine.tapeLength n) → Bool) (a : Aux) :
    TM.runConfig (M := W.machine)
        (W.alignedConfigQ n base (by omega) tape (W.wst0 a)) 4 =
      W.alignedConfigQ n (base + 4) hsafe
        (writeFrame4 base (W.w0 a) (W.w1 a) (W.w2 a) (W.w3 a) tape)
        (W.exitState a) := by
  have h0 : base < W.machine.tapeLength n := by omega
  have h1 : base + 1 < W.machine.tapeLength n := by omega
  have h2 : base + 2 < W.machine.tapeLength n := by omega
  have h3 : base + 3 < W.machine.tapeLength n := by omega
  show TM.runConfig (M := W.machine)
      (W.alignedConfigQ n base h0 tape (W.wst0 a)) (1 + 1 + 1 + 1) = _
  rw [runConfig_add, runConfig_add, runConfig_add]
  simp only [runConfig_one]
  rw [Phased.stepRight W.program W.phase n base h0 h1 tape
    (W.wst0 a) (W.wst1 a) (W.w0 a) (W.wstep_p0 a _)]
  rw [Phased.stepRight W.program W.phase n (base + 1) h1 h2 _
    (W.wst1 a) (W.wst2 a) (W.w1 a) (W.wstep_p1 a _)]
  rw [Phased.stepRight W.program W.phase n (base + 2) h2 h3 _
    (W.wst2 a) (W.wst3 a) (W.w2 a) (W.wstep_p2 a _)]
  rw [Phased.stepRight W.program W.phase n (base + 3) h3 hsafe _
    (W.wst3 a) (W.exitState a) (W.w3 a) (W.wstep_p3 a _)]
  rfl

/-- Exact four-step replacement on an arbitrary list-backed tape. -/
theorem writeFrameOnList (W : FrameWriterCtx S F Aux) (n : Nat)
    (pre suffix : List F) (old : F) (a : Aux)
    (hsafe : 4 * pre.length + 4 < W.machine.tapeLength n) :
    TM.runConfig (M := W.machine)
        (W.alignedConfigQ n (4 * pre.length) (by omega)
          (frameListTape ((pre ++ old :: suffix).flatMap W.codec.bits))
          (W.wst0 a)) 4 =
      W.alignedConfigQ n (4 * pre.length + 4) hsafe
        (frameListTape ((pre ++ W.target a :: suffix).flatMap W.codec.bits))
        (W.exitState a) := by
  rw [W.writeMacrostep n (4 * pre.length) hsafe _ a,
    writeFrame4_frameListTape W.codec pre suffix old (W.target a)
      (W.target_bits a)]

end FrameWriterCtx

end Pnp3.Internal.PsubsetPpoly.TM.FrameScan
