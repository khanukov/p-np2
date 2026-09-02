import Complexity.TMVerifier.TuringToolkit.FrameShuttleProbe

/-!
# GN-E2-1a generic frame-shuttle surface

Definition pins plus explicit theorem propositions for the context writer,
shared-program shuttle, exact schedule/capstone, and fresh positive/negative
probes.  Infrastructure only; no GNM activation or instance.
-/
namespace Pnp3.Tests.TMFrameShuttleSurface

open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

#check @FrameWriterCtx
#check @FrameShuttle
#check @FrameShuttle.reverseScanner
#check @FrameShuttle.markWriter
#check @FrameShuttle.destinationWriter
#check @FrameShuttle.restoreWriter
#check @FrameShuttle.shuttleSegments
#check @FrameShuttle.shuttleSteps
#check @FrameShuttle.shuttleFootprint
#check @shuttleProbe
#check @shuttleProbeCS

universe v

variable {S : Type v} [Fintype S] [DecidableEq S]
variable {F Mode Aux : Type v}

theorem check_frameListTape_append_blank (C : FrameCodec F) {L : Nat}
    (frames : List F) (blank : F)
    (hblank : C.bits blank = [false, false, false, false]) :
    frameListTape (L := L) (frames.flatMap C.bits) =
      frameListTape ((frames ++ [blank]).flatMap C.bits) :=
  frameListTape_append_blank C frames blank hblank

theorem check_FrameWriterCtx_writeMacrostep
    (W : FrameWriterCtx S F Aux) (n base : Nat)
    (hsafe : base + 4 < W.machine.tapeLength n)
    (tape : Fin (W.machine.tapeLength n) → Bool) (a : Aux) :
    W.machine.runConfig
        (W.alignedConfigQ n base (by omega) tape (W.wst0 a)) 4 =
      W.alignedConfigQ n (base + 4) hsafe
        (writeFrame4 base (W.w0 a) (W.w1 a) (W.w2 a) (W.w3 a) tape)
        (W.exitState a) :=
  W.writeMacrostep n base hsafe tape a

theorem check_FrameWriterCtx_writeFrameOnList
    (W : FrameWriterCtx S F Aux) (n : Nat)
    (pre suffix : List F) (old : F) (a : Aux)
    (hsafe : 4 * pre.length + 4 < W.machine.tapeLength n) :
    W.machine.runConfig
        (W.alignedConfigQ n (4 * pre.length) (by omega)
          (frameListTape ((pre ++ old :: suffix).flatMap W.codec.bits))
          (W.wst0 a)) 4 =
      W.alignedConfigQ n (4 * pre.length + 4) hsafe
        (frameListTape ((pre ++ W.target a :: suffix).flatMap W.codec.bits))
        (W.exitState a) :=
  W.writeFrameOnList n pre suffix old a hsafe

variable [Fintype Mode] [Fintype Aux]

theorem check_FrameShuttle_shuttleSteps_provenance (d : Nat) :
    FrameShuttle.shuttleSteps d =
        4 + (4 + (4 + (4 * (d + 1) +
          (1 + (4 + ((4 * d + 4) + 4)))))) ∧
      FrameShuttle.shuttleSteps d = 8 * d + 29 :=
  FrameShuttle.shuttleSteps_provenance d

theorem check_FrameShuttle_marker_breaks_forwardPath
    (K : FrameShuttle S F Mode Aux) :
    ¬ K.core.ValidPath K.seekMode [K.marker] :=
  K.marker_breaks_forwardPath

theorem check_FrameShuttle_shuttleOnList
    (K : FrameShuttle S F Mode Aux) (n : Nat)
    (pre : List F) (f : F) (middle rest : List F) (a : Aux)
    (hmid : ∀ g ∈ middle, g ≠ K.blank ∧ g ≠ K.marker)
    (hsafe : 4 * (pre.length + middle.length + 2) < K.machine.tapeLength n) :
    K.machine.runConfig
        (K.cfg n (4 * pre.length) (by omega)
          (frameListTape
            ((pre ++ f :: middle ++ K.blank :: rest).flatMap K.core.codec.bits))
          (K.pst0 a)) (FrameShuttle.shuttleSteps middle.length) =
      K.cfg n (4 * pre.length + 4) (by omega)
        (frameListTape
          ((pre ++ f :: middle ++ K.image f :: rest).flatMap K.core.codec.bits))
        (K.exitState (K.latch a f)) :=
  K.shuttleOnList n pre f middle rest a hmid hsafe

theorem check_FrameShuttle_shuttleOnList_nextBlank
    (K : FrameShuttle S F Mode Aux) (n : Nat)
    (pre : List F) (f : F) (middle rest : List F) (a : Aux)
    (hmid : ∀ g ∈ middle, g ≠ K.blank ∧ g ≠ K.marker)
    (hsafe : 4 * (pre.length + middle.length + 2) < K.machine.tapeLength n) :
    K.machine.runConfig
        (K.cfg n (4 * pre.length) (by omega)
          (frameListTape
            ((pre ++ f :: middle ++ K.blank :: K.blank :: rest).flatMap
              K.core.codec.bits)) (K.pst0 a))
        (FrameShuttle.shuttleSteps middle.length) =
      K.cfg n (4 * pre.length + 4) (by omega)
        (frameListTape
          ((pre ++ f :: middle ++ K.image f :: K.blank :: rest).flatMap
            K.core.codec.bits)) (K.exitState (K.latch a f)) :=
  K.shuttleOnList_nextBlank n pre f middle rest a hmid hsafe

theorem check_shuttleProbe_run45 (n : Nat) :
    shuttleProbe.machine.runConfig
        (shuttleProbe.cfg n 0 (by
          change 0 < n + shuttleProbeClock n + 1
          rw [shuttleProbeClock]
          omega)
          (frameListTape (shuttleProbeInput.flatMap ShuttleProbeFrame.bits))
          (shuttleProbeState .probe .q0 false false false ⟨false, .blank⟩)) 45 =
      shuttleProbe.cfg n 4 (by
        change 4 < n + shuttleProbeClock n + 1
        rw [shuttleProbeClock]
        omega)
        (frameListTape (shuttleProbeOutput.flatMap ShuttleProbeFrame.bits))
        (shuttleProbeState .exit .q0 false false false
          ⟨false, .source true⟩) :=
  shuttleProbe_run45 n

theorem check_shuttleProbe_marker_middle_rejected :
    ¬ shuttleProbe.core.ValidPath shuttleProbe.seekMode
      [ShuttleProbeFrame.marker] :=
  shuttleProbe_marker_middle_rejected

end Pnp3.Tests.TMFrameShuttleSurface
