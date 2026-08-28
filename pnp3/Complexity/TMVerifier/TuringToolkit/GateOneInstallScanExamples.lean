import Complexity.TMVerifier.TuringToolkit.GateOneInstallScan

/-!
# G1: the concrete installation-scan probe

**Progress classification: Infrastructure.**  One literal instance of
`GateOneInstallScan.g1CS_readB_install_scan_exact`, on the single literal
request `g1WalkExample = ⟨and, 0, 2, [false, true, true]⟩` — **fifteen** encoded
frames and `60` input cells; the explicit list-backed layout below appends one
`blank`, the frame the machine's own tape supplies past the input, so it
contains **sixteen** frames and `64` bits.  The prefix
`bof · tag⁴ · argSep · argSep` lies at ordinals `0 … 6`, the operand-2 field at
ordinals `7 … 8` and the data region from ordinal `10`.

Every number below is a literal: exactly `169 = 2 * 60 + 9 + 4 * 10` genuine
steps of the one fixed zero-parameter machine `G1M` run from its **real**
initial configuration to head `40` — the first cell of `data vals[0]` — in
`bProbe2`, with the tape bit-for-bit the initial tape and the context still
`g1Ctx0`.

`bProbe2` is the live-route boundary: nothing here latches a value, installs a
cursor, runs a round or states an invariant.  The literal probes of those steps
are `GateOneProbeInstallExamples`, and they start from caller-supplied
configurations.  This module is an audit surface, and that one reuses its
request, its literal frame word and these `169`-step capstones verbatim.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

namespace G1InstallScanExamples

/-- `and` with an empty operand-1 field, `arg2 = 2` and a three-bit data
region. -/
def g1WalkExample : G1Request := ⟨.and, 0, 2, [false, true, true]⟩

theorem g1WalkExample_canonical : g1WalkExample.Canonical := by decide

theorem g1WalkExample_length : (encodeG1 g1WalkExample).length = 60 := by
  rw [encodeG1_length]; rfl

/-- The canonical word plus the blank frame the tape supplies past the input:
sixteen frames, `64` bits. -/
def g1WalkInitFrames : List G1Frame :=
  [.bof, .tag, .tag, .tag, .tag, .argSep, .argSep, .index, .index, .separator,
    .data false, .data true, .data true, .output false, .finish, .blank]

/-- **The initial tape, as that literal sixteen-frame word.** -/
theorem g1WalkExample_initial_tape :
    (G1M.initialConfig (g1Point (encodeG1 g1WalkExample))).tape =
      g1ListTape (n := (encodeG1 g1WalkExample).length)
        (g1WalkInitFrames.flatMap G1Frame.bits) := by
  rw [← g1ListTape_validation_eq_initial g1WalkExample]
  rfl

/-- `2 * 60 + 9` T2a steps plus `4 * 10` rescan steps. -/
theorem walk_install_scan_steps :
    g1InstallScanSteps g1WalkExample = 169 := by
  simp only [g1InstallScanSteps, g1ReadBHandoffSteps, g1WalkExample_length]
  rfl

/-- **The re-pointed positive-index route.**  Exactly `169` genuine steps from
the **real** initial configuration reach `bProbe2` at cell `40` — the first cell
of `data vals[0]` — with the tape bit-for-bit the initial tape. -/
theorem walk_install_scan :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1WalkExample))) 169 =
      g1AlignedConfig (encodeG1 g1WalkExample).length 40
        (g1_route_lt_tapeLength g1WalkExample 10 (by decide))
        (G1M.initialConfig (g1Point (encodeG1 g1WalkExample))).tape
        .bProbe2 .p0 false false false g1Ctx0 := by
  have h := g1CS_readB_install_scan_exact g1WalkExample g1WalkExample_canonical
    (Or.inl rfl) 1 rfl
  rw [walk_install_scan_steps] at h
  exact h

/-- The concrete endpoint head. -/
theorem walk_install_scan_head :
    ((TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1WalkExample))) 169).head : Nat) =
      40 := by
  rw [walk_install_scan]; rfl

/-- The concrete endpoint state: the boundary `bProbe2`, context untouched. -/
theorem walk_install_scan_state :
    (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1WalkExample))) 169).state.snd =
      g1Probe2State g1Ctx0 := by
  rw [walk_install_scan]; rfl

/-- **The concrete scan changes nothing**: after `169` steps the tape is still
the literal sixteen-frame word of `g1WalkExample_initial_tape`. -/
theorem walk_install_scan_tape :
    (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1WalkExample))) 169).tape =
      g1ListTape (n := (encodeG1 g1WalkExample).length)
        (g1WalkInitFrames.flatMap G1Frame.bits) := by
  rw [walk_install_scan, ← g1WalkExample_initial_tape]
  rfl

/-- The concrete step count is inside the unchanged public clock. -/
theorem walk_install_scan_clock :
    169 ≤ g1Clock (encodeG1 g1WalkExample).length := by
  rw [← walk_install_scan_steps]
  exact g1InstallScanSteps_le_clock g1WalkExample

end G1InstallScanExamples

end Pnp3.Internal.PsubsetPpoly.TM
