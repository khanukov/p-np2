import Complexity.TMVerifier.TuringToolkit.GateOneProbeInstall
import Complexity.TMVerifier.TuringToolkit.GateOneInstallScanExamples

/-!
# G1 probe / latch / cursor install: concrete encoded-frame probes

**Progress classification: Infrastructure.**  One literal probe per macro of
`GateOneProbeInstall`, on the **reused** encoded frame word of
`G1InstallScanExamples.g1WalkExample = ⟨and, 0, 2, [false, true, true]⟩`:
**fifteen** encoded frames and `60` input cells; the list-backed layout
`g1WalkInitFrames` appends one `blank`, the frame the machine's own tape
supplies past the input, so it has **sixteen** frames and `64` bits.  The prefix
`bof · tag⁴ · argSep · argSep` lies at ordinals `0 … 6`, the operand-2 field at
ordinals `7 … 8` and the data region from ordinal `10`.  Only one new layout is
introduced: `g1WalkInitFrames` with the cursor installed over ordinal `10`.

The request, its canonicity and length, `g1WalkInitFrames`, the initial-tape
equation and the `169`-step installation-scan capstones are reused verbatim from
`GateOneInstallScanExamples`.

Every head position and step count is a literal, and every probe is an exact
`G1M` configuration equality — but each takes the tape length `n` and one
numeric safety bound from the **caller**.  Nothing composes the macros with the
`169`-step capstone or with each other: no round is chained, no invariant is
stated, no run here starts from `G1M.initialConfig`, no index is addressed.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

namespace G1ProbeInstallExamples

open G1InstallScanExamples

/-- `g1WalkInitFrames` with `data vals[0]` at ordinal `10` replaced by the
installed `cursor`: the layout the cursor writer produces. -/
def g1WalkFramesCursor0 : List G1Frame :=
  [.bof, .tag, .tag, .tag, .tag, .argSep, .argSep, .index, .index, .separator,
    .cursor, .data true, .data true, .output false, .finish, .blank]

/-- **Probe and latch, `false`.**  Five steps read `data vals[0] = data false`
at ordinal `10`, store `false` in `G1Ctx.vB` and leave the head on cell `43`.
The tape does not change. -/
theorem probe_latch_false (n : Nat) (hsafe : 44 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n 40 (by omega)
        (g1ListTape (g1WalkInitFrames.flatMap G1Frame.bits))
        .bProbe2 .p0 false false false g1Ctx0) 5 =
      g1AlignedConfig n 43 (by omega)
        (g1ListTape (g1WalkInitFrames.flatMap G1Frame.bits))
        .bIns .p3 false false false (g1Ctx0.withVB false) := by
  have h := g1CS_walk_probe_latch n
    [.bof, .tag, .tag, .tag, .tag, .argSep, .argSep, .index, .index, .separator]
    [.data true, .data true, .output false, .finish, .blank] false g1Ctx0
    (by simpa using hsafe)
  simpa [g1WalkInitFrames] using h

/-- **Probe and latch, `true`.**  The same five steps one frame further right:
`data vals[1] = data true` at ordinal `11`, head `44 → 47`, `vB := true`. -/
theorem probe_latch_true (n : Nat) (hsafe : 48 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n 44 (by omega)
        (g1ListTape (g1WalkInitFrames.flatMap G1Frame.bits))
        .bProbe2 .p0 false false false g1Ctx0) 5 =
      g1AlignedConfig n 47 (by omega)
        (g1ListTape (g1WalkInitFrames.flatMap G1Frame.bits))
        .bIns .p3 false false false (g1Ctx0.withVB true) := by
  have h := g1CS_walk_probe_latch n
    [.bof, .tag, .tag, .tag, .tag, .argSep, .argSep, .index, .index, .separator,
      .data false]
    [.data true, .output false, .finish, .blank] true g1Ctx0
    (by simpa using hsafe)
  simpa [g1WalkInitFrames] using h

/-- **The out-of-range probe.**  Ordinal `13` is the `output` destination frame:
four steps from cell `52` enter the stable `bOOB` boundary on cell `56`, tape
untouched. -/
theorem probe_oob (n : Nat) (hsafe : 56 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n 52 (by omega)
        (g1ListTape (g1WalkInitFrames.flatMap G1Frame.bits))
        .bProbe2 .p0 false false false g1Ctx0) 4 =
      g1AlignedConfig n 56 (by omega)
        (g1ListTape (g1WalkInitFrames.flatMap G1Frame.bits))
        .bOOB .p0 false false false g1Ctx0 := by
  have h := g1CS_walk_probe_oob n
    [.bof, .tag, .tag, .tag, .tag, .argSep, .argSep, .index, .index, .separator,
      .data false, .data true, .data true]
    [.finish, .blank] g1Ctx0 (by simpa using hsafe)
  simpa [g1WalkInitFrames] using h

/-- **The cursor install.**  Four leftward steps turn ordinal `10` — the frame
just latched — into `cursor`, head on cell `39`, control in the local endpoint
`bSeek`.  The latched `vB = false` rides through unchanged. -/
theorem install_cursor (n : Nat) (hsafe : 44 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n 43 (by omega)
        (g1ListTape (g1WalkInitFrames.flatMap G1Frame.bits))
        .bIns .p3 false false false (g1Ctx0.withVB false)) 4 =
      g1AlignedConfig n 39 (by omega)
        (g1ListTape (g1WalkFramesCursor0.flatMap G1Frame.bits))
        .bSeek .p3 false false false (g1Ctx0.withVB false) := by
  have h := g1CS_walk_install_cursor n
    [.bof, .tag, .tag, .tag, .tag, .argSep, .argSep, .index, .index, .separator]
    [.data true, .data true, .output false, .finish, .blank] (.data false)
    (g1Ctx0.withVB false) (by simp) (by simpa using hsafe)
  simpa [g1WalkInitFrames, g1WalkFramesCursor0] using h

end G1ProbeInstallExamples

end Pnp3.Internal.PsubsetPpoly.TM
