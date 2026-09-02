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
#check @FrameShuttle.reverseScanner_shared
#check @FrameShuttle.markWriter_shared
#check @FrameShuttle.destinationWriter_shared
#check @FrameShuttle.restoreWriter_shared
#check @FrameShuttle.markWriter_glue
#check @FrameShuttle.destinationWriter_glue
#check @FrameShuttle.restoreWriter_glue
#check @FrameShuttle.shuttleSegments
#check @FrameShuttle.shuttleSteps
#check @FrameShuttle.shuttleFootprint
#check @shuttleProbe
#check @shuttleProbeCS

universe v

variable {S : Type v} [Fintype S] [DecidableEq S]
variable {F Mode Aux : Type v}

theorem check_writerCtx_onList (W : FrameWriterCtx S F Aux) (n : Nat)
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

theorem check_shuttle_steps (d : Nat) :
    FrameShuttle.shuttleSteps d = 8 * d + 29 :=
  (FrameShuttle.shuttleSteps_provenance d).2

theorem check_shuttle_capstone (K : FrameShuttle S F Mode Aux) (n : Nat)
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

theorem check_shuttle_next_blank (K : FrameShuttle S F Mode Aux) (n : Nat)
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

theorem check_probe_run45 (n : Nat) :
    shuttleProbe.machine.runConfig
        (shuttleProbe.cfg n 0 (shuttleProbe_lt_tapeLength (by omega))
          (frameListTape (shuttleProbeInput.flatMap ShuttleProbeFrame.bits))
          (shuttleProbeState .probe .q0 false false false ⟨false, .blank⟩)) 45 =
      shuttleProbe.cfg n 4 (shuttleProbe_lt_tapeLength (by omega))
        (frameListTape (shuttleProbeOutput.flatMap ShuttleProbeFrame.bits))
        (shuttleProbeState .exit .q0 false false false
          ⟨false, .source true⟩) :=
  shuttleProbe_run45 n

theorem check_probe_marker_middle :
    ¬ shuttleProbe.core.ValidPath shuttleProbe.seekMode
      [ShuttleProbeFrame.marker] :=
  shuttleProbe_marker_middle_rejected

end Pnp3.Tests.TMFrameShuttleSurface
