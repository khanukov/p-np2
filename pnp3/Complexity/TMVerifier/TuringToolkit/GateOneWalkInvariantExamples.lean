import Complexity.TMVerifier.TuringToolkit.GateOneWalkInvariant
import Complexity.TMVerifier.TuringToolkit.GateOneProbeInstallExamples

/-!
# G1 cursor walk: concrete probes of `Σ(0)` and its installation

**Progress classification: Infrastructure.**  All-literal probes of the PR3a
capstones, on two literal requests:

| request | probe | steps | head |
|---------|-------|-------|------|
| `⟨and, 0, 2, [false, true, true]⟩` | install into `Σ(0)` | `178` | `→ 39` |
| `⟨and, 0, 2, []⟩` | empty-data install OOB | `149` | `→ 44` |

The first request, its canonicity and its `169`-step installation scan are the
merged `G1InstallScanExamples.g1WalkExample`: **fifteen** encoded frames and
`60` input cells; the list-backed layouts append one `blank`, the frame the
machine's own tape supplies past the input, so each has **sixteen** frames.  The
prefix `bof · tag⁴ · argSep · argSep` lies at ordinals `0 … 6`, the operand-2
field at ordinals `7 … 8`, the data region from ordinal `10`, and the cursor of
`Σ(j)` at ordinal `j + 10`.

`Σ(0)`'s frame word is literally the layout the merged cursor-install probe
produces, `G1ProbeInstallExamples.g1WalkFramesCursor0`, so no second copy of it
is introduced here.

Nothing here executes a round, iterates, sums a loop clock, reaches a terminal
or reads an arbitrary operand-2 index; `Σ(1)` and `Σ(2)` are not probed, because
no theorem of this slice reaches them.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

namespace G1WalkInvariantExamples

open G1InstallScanExamples (g1WalkExample g1WalkExample_canonical
  walk_install_scan_steps)

/-! ## `⟨and, 0, 2, [false, true, true]⟩`: the invariant at `j = 0` -/

/-- `Σ(0)`'s frame word — `bof · tag⁴ · argSep · argSep · index² · separator ·
cursor · data true · data true · output false · finish · blank`: the operand-2
field untouched, the cursor at ordinal `10` hiding `vals[0] = false`.  It is the
merged post-install layout `g1WalkFramesCursor0`, named again for its new
role. -/
def g1WalkFramesRound0 : List G1Frame :=
  G1ProbeInstallExamples.g1WalkFramesCursor0

theorem walkFrames_zero : g1WalkFrames g1WalkExample 0 = g1WalkFramesRound0 :=
  rfl

theorem walkCursor_zero : g1WalkCursor g1WalkExample 0 = 10 := rfl

/-- The invariant word has exactly the length of the real tape word: sixteen
frames. -/
theorem walkFrames_zero_length : (g1WalkFrames g1WalkExample 0).length = 16 :=
  rfl

/-- The cursor is unique. -/
theorem walkFrames_zero_count_cursor :
    (g1WalkFrames g1WalkExample 0).count G1Frame.cursor = 1 := by decide

/-- At `j = 0` no operand-2 unit is spent yet: `index²`, `spent⁰`. -/
theorem walkFrames_zero_count_index :
    (g1WalkFrames g1WalkExample 0).count G1Frame.index = 2 := by decide

theorem walkFrames_zero_count_spent :
    (g1WalkFrames g1WalkExample 0).count G1Frame.spent = 0 := by decide

/-! ## The installation, from the real initial configuration -/

/-- `169` installation-scan steps plus `5` probe/latch steps plus `4` cursor
install steps. -/
theorem walk_install_steps : g1WalkInstallSteps g1WalkExample = 178 := by
  rw [g1WalkInstallSteps, walk_install_scan_steps]

/-- **Exactly `178` genuine steps from the real initial configuration reach
`Σ(0)`**: head `4 * 10 - 1 = 39`, control `bSeek .p3`, `vB = vals[0] = false`,
tape `g1WalkFramesRound0` — the initial word with data slot `0` overwritten by
the single `cursor` frame.  The run stops there; no round follows. -/
theorem walk_install :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1WalkExample))) 178 =
      g1WalkConfig g1WalkExample 0 (by decide) (by decide) false (by decide) := by
  have h := g1CS_walk_install_exact g1WalkExample g1WalkExample_canonical
    (Or.inl rfl) 1 rfl false (by decide)
  rw [walk_install_steps] at h
  exact h

theorem walk_install_head :
    ((TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1WalkExample))) 178).head : Nat) =
      39 := by
  rw [walk_install]; rfl

theorem walk_install_clock : 178 ≤ g1Clock (encodeG1 g1WalkExample).length := by
  rw [← walk_install_steps]
  exact g1WalkInstallSteps_le_clock g1WalkExample

/-! ## The empty-data installation out-of-range branch

`⟨and, 0, 2, []⟩`: a positive operand-2 index against an **empty** data region.
The installation scan is read-only and its probe meets the `output false`
destination frame. -/

def g1EmptyExample : G1Request := ⟨.and, 0, 2, []⟩

theorem g1EmptyExample_canonical : g1EmptyExample.Canonical := by decide

theorem g1EmptyExample_length : (encodeG1 g1EmptyExample).length = 48 := by
  rw [encodeG1_length]; rfl

theorem walk_empty_oob_steps : g1WalkEmptyOOBSteps g1EmptyExample = 149 := by
  simp only [g1WalkEmptyOOBSteps, g1InstallScanSteps, g1ReadBHandoffSteps,
    g1EmptyExample_length]
  rfl

/-- **Exactly `149` genuine steps from the real initial configuration end in the
stable `bOOB` boundary**, head `4 * 11 = 44`, tape **bit-for-bit the initial
tape**: no `spent` marker and no `cursor` is written anywhere on the empty-data
branch. -/
theorem walk_empty_oob :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1EmptyExample))) 149 =
      g1AlignedConfig (encodeG1 g1EmptyExample).length 44
        (g1_route_lt_tapeLength g1EmptyExample 11 (by decide))
        (G1M.initialConfig (g1Point (encodeG1 g1EmptyExample))).tape
        .bOOB .p0 false false false g1Ctx0 := by
  have h := g1CS_walk_install_oob_exact g1EmptyExample g1EmptyExample_canonical
    (Or.inl rfl) 1 rfl rfl
  rw [walk_empty_oob_steps] at h
  exact h

theorem walk_empty_oob_tape :
    (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1EmptyExample))) 149).tape =
      (G1M.initialConfig (g1Point (encodeG1 g1EmptyExample))).tape := by
  rw [walk_empty_oob]; rfl

theorem walk_empty_oob_clock :
    149 ≤ g1Clock (encodeG1 g1EmptyExample).length := by
  rw [← walk_empty_oob_steps]
  exact g1WalkEmptyOOBSteps_le_clock g1EmptyExample

end G1WalkInvariantExamples

end Pnp3.Internal.PsubsetPpoly.TM
