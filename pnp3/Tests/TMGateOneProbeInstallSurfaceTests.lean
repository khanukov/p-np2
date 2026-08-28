import Complexity.TMVerifier.TuringToolkit.GateOneProbeInstallExamples

/-!
# G1 probe / latch / cursor install: surface tests

Import-side contracts for the successor of the merged installation-scan
endpoint: the leftward cursor-writer instance, the three exact atomic macros on
arbitrary frame-list contexts, and their literal encoded-frame probes.

**Every statement below takes the caller's configuration.**  None starts from
`G1M.initialConfig`: the only real-initial-configuration endpoint on this branch
is the installation scan, pinned unchanged in `TMGateOneReadBSurfaceTests`.
The install exits at `bSeek .p3`, head on the preceding frame's last cell.
`bSeek` has no successful frame row; a complete-frame attempt rejects and no
theorem executes it.  Its reverse-read rows are PR2b.  Deliberately absent: any
walk invariant, installation driver, seek/mark/turn/restore/exhaustion macro,
iteration or loop clock, addressing, `TM.accepts`, gate-semantics, full-clock or
padded-tape surface.

This is an audit surface: it pins public signatures and proves nothing new.
-/

namespace Pnp3.Tests.TMGateOneProbeInstallSurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

#check @g1CursorWriter
#check @g1CursorWriter_machine
#check @g1Advance_bProbe2_data
#check @G1ProbeInstallExamples.g1WalkFramesCursor0

/-! ## The atomic macros, pinned exactly

Each wrapper restates its macro verbatim, so a later slice cannot silently drop
the tape equation, move the head or specialise the surrounding frame list. -/

/-- **Probe and latch.**  The tape is unchanged and the *only* state change is
`vB := v`; the head ends on that frame's last cell in `bIns .p3`. -/
theorem check_g1CS_walk_probe_latch (n : Nat) (pre suffix : List G1Frame)
    (v : Bool) (ctx : G1Ctx)
    (hsafe : 4 * pre.length + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape ((pre ++ G1Frame.data v :: suffix).flatMap G1Frame.bits))
        .bProbe2 .p0 false false false ctx) 5 =
      g1AlignedConfig n (4 * pre.length + 3) (by omega)
        (g1ListTape ((pre ++ G1Frame.data v :: suffix).flatMap G1Frame.bits))
        .bIns .p3 false false false (ctx.withVB v) :=
  g1CS_walk_probe_latch n pre suffix v ctx hsafe

/-- **The out-of-range probe** enters the stable boundary, not the reject
sink. -/
theorem check_g1CS_walk_probe_oob (n : Nat) (pre suffix : List G1Frame)
    (ctx : G1Ctx) (hsafe : 4 * pre.length + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape
          ((pre ++ G1Frame.output false :: suffix).flatMap G1Frame.bits))
        .bProbe2 .p0 false false false ctx) 4 =
      g1AlignedConfig n (4 * pre.length + 4) hsafe
        (g1ListTape
          ((pre ++ G1Frame.output false :: suffix).flatMap G1Frame.bits))
        .bOOB .p0 false false false ctx :=
  g1CS_walk_probe_oob n pre suffix ctx hsafe

/-- **The cursor install** replaces one arbitrary frame by `cursor`, walking
left, and stops in the endpoint `bSeek`. -/
theorem check_g1CS_walk_install_cursor (n : Nat) (pre suffix : List G1Frame)
    (old : G1Frame) (ctx : G1Ctx) (hpre : 0 < pre.length)
    (hsafe : 4 * pre.length + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length + 3) (by omega)
        (g1ListTape ((pre ++ old :: suffix).flatMap G1Frame.bits))
        .bIns .p3 false false false ctx) 4 =
      g1AlignedConfig n (4 * pre.length - 1) (by omega)
        (g1ListTape ((pre ++ G1Frame.cursor :: suffix).flatMap G1Frame.bits))
        .bSeek .p3 false false false ctx :=
  g1CS_walk_install_cursor n pre suffix old ctx hpre hsafe

/-! ## The literal probes, pinned exactly -/

open G1InstallScanExamples G1ProbeInstallExamples in
/-- Head `40 → 43` in `5` steps on the reused sixteen-frame word: `vB := false`,
tape untouched. -/
theorem check_probe_latch_false (n : Nat) (hsafe : 44 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n 40 (by omega)
        (g1ListTape (g1WalkInitFrames.flatMap G1Frame.bits))
        .bProbe2 .p0 false false false g1Ctx0) 5 =
      g1AlignedConfig n 43 (by omega)
        (g1ListTape (g1WalkInitFrames.flatMap G1Frame.bits))
        .bIns .p3 false false false (g1Ctx0.withVB false) :=
  probe_latch_false n hsafe

open G1InstallScanExamples G1ProbeInstallExamples in
/-- Head `44 → 47` in `5` steps: `vB := true`. -/
theorem check_probe_latch_true (n : Nat) (hsafe : 48 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n 44 (by omega)
        (g1ListTape (g1WalkInitFrames.flatMap G1Frame.bits))
        .bProbe2 .p0 false false false g1Ctx0) 5 =
      g1AlignedConfig n 47 (by omega)
        (g1ListTape (g1WalkInitFrames.flatMap G1Frame.bits))
        .bIns .p3 false false false (g1Ctx0.withVB true) :=
  probe_latch_true n hsafe

open G1InstallScanExamples G1ProbeInstallExamples in
/-- Head `52 → 56` in `4` steps on the `output` destination frame: `bOOB`. -/
theorem check_probe_oob (n : Nat) (hsafe : 56 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n 52 (by omega)
        (g1ListTape (g1WalkInitFrames.flatMap G1Frame.bits))
        .bProbe2 .p0 false false false g1Ctx0) 4 =
      g1AlignedConfig n 56 (by omega)
        (g1ListTape (g1WalkInitFrames.flatMap G1Frame.bits))
        .bOOB .p0 false false false g1Ctx0 :=
  probe_oob n hsafe

open G1InstallScanExamples G1ProbeInstallExamples in
/-- Head `43 → 39` in `4` steps: ordinal `10` becomes `cursor`, nothing else
changes, and the run stops in the local endpoint `bSeek`. -/
theorem check_install_cursor (n : Nat) (hsafe : 44 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n 43 (by omega)
        (g1ListTape (g1WalkInitFrames.flatMap G1Frame.bits))
        .bIns .p3 false false false (g1Ctx0.withVB false)) 4 =
      g1AlignedConfig n 39 (by omega)
        (g1ListTape (g1WalkFramesCursor0.flatMap G1Frame.bits))
        .bSeek .p3 false false false (g1Ctx0.withVB false) :=
  install_cursor n hsafe

end Pnp3.Tests.TMGateOneProbeInstallSurface
