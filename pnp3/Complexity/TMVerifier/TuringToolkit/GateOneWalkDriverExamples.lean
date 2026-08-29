import Complexity.TMVerifier.TuringToolkit.GateOneWalkDriver
import Complexity.TMVerifier.TuringToolkit.GateOneWalkInvariantExamples

/-!
# G1 cursor walk: concrete positive-index reads and out-of-range branches

**Progress classification: Infrastructure.**  Four all-literal probes of the
PR3c capstones — two successful positive-index operand-2 reads and both
aggregated out-of-range branches:

| request | probe | steps | head |
|---------|-------|-------|------|
| `⟨and, 0, 1, [false, true]⟩` | read `vals[1] = true` | `239` | `44` |
| `⟨and, 0, 2, [false, true, true]⟩` | read `vals[2] = true` | `328` | `52` |
| `⟨and, 0, 2, []⟩` | aggregated OOB, `m = 0` | `149` | `44` |
| `⟨and, 0, 2, [false, true]⟩` | aggregated OOB, `m = 2` | `255` | `52` |

Every step count, head position and frame word is a literal, and each probe is
an exact `G1M` configuration equality from the **real** initial configuration.
Three of the four requests are the merged literals of
`GateOneInstallScanExamples` and `GateOneWalkInvariantExamples`; the `arg2 = 2`
read ends on `G1WalkExamples.g1WalkFramesFinal` and the `m = 2` boundary on
`G1WalkInvariantExamples.g1OOBFramesRestored1` — the literal words those
modules' probes already produced.  Nothing here repairs the operand-2 field,
reads operand 1, combines, writes the output frame or mentions `TM.accepts`.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

namespace G1WalkDriverExamples

open G1InstallScanExamples (g1WalkExample g1WalkExample_canonical
  walk_install_scan_steps)
open G1WalkExamples (g1WalkFramesFinal)
open G1WalkInvariantExamples (g1OOBExample g1OOBExample_canonical
  g1OOBFramesRestored1 g1EmptyExample g1EmptyExample_canonical
  g1EmptyExample_length)

/-! ## The loop clock on literals -/

theorem loopSteps_zero : g1BLoopSteps 0 = 0 := rfl
theorem loopSteps_one : g1BLoopSteps 1 = 37 := rfl
theorem loopSteps_two : g1BLoopSteps 2 = 90 := rfl
theorem loopSteps_three : g1BLoopSteps 3 = 159 := rfl

/-- The recurrence on literals: the second round costs `16 * 1 + 37 = 53`. -/
theorem loopSteps_two_eq : g1BLoopSteps 2 = g1BLoopSteps 1 + 53 := rfl

/-! ## `⟨and, 0, 1, [false, true]⟩`: reading operand-2 index `1` -/

/-- `and`, empty operand-1 field, `arg2 = 1`, two-bit data region. -/
def g1BReadExample : G1Request := ⟨.and, 0, 1, [false, true]⟩

theorem g1BReadExample_canonical : g1BReadExample.Canonical := by decide

theorem g1BReadExample_length : (encodeG1 g1BReadExample).length = 52 := by
  rw [encodeG1_length]; rfl

/-- The tape the read ends on: the single operand-2 unit consumed, data region
exactly `vals`, **no cursor**. -/
def g1BReadFramesFinal : List G1Frame :=
  [.bof, .tag, .tag, .tag, .tag, .argSep, .argSep, .spent, .separator,
    .data false, .data true, .output false, .finish, .blank]

theorem readFramesFinal_eq :
    g1BSpentFrames g1BReadExample g1BReadExample.arg2 = g1BReadFramesFinal :=
  rfl

theorem readFramesFinal_count_cursor :
    g1BReadFramesFinal.count G1Frame.cursor = 0 := by decide

theorem readFramesFinal_count_spent :
    g1BReadFramesFinal.count G1Frame.spent = 1 := by decide

theorem readFramesFinal_count_index :
    g1BReadFramesFinal.count G1Frame.index = 0 := by decide

theorem readFramesFinal_length : g1BReadFramesFinal.length = 14 := rfl

/-- `2 * 52 + 9` pass-B steps plus `4 * 9` rescan steps. -/
theorem readExample_install_scan_steps :
    g1InstallScanSteps g1BReadExample = 149 := by
  simp only [g1InstallScanSteps, g1ReadBHandoffSteps, g1BReadExample_length]
  rfl

/-- `149` scan steps plus `8 * 1² + 45 * 1 + 37 = 90`: the installation's nine
extra steps, one full round (`37`) and the terminal (`16 * 1 + 28 = 44`). -/
theorem readExample_steps : g1BReadSteps g1BReadExample = 239 := by
  rw [g1BReadSteps, readExample_install_scan_steps]; rfl

theorem readExample_steps_split :
    g1BReadSteps g1BReadExample = 158 + 37 + 44 := by
  rw [readExample_steps]

/-- **Exactly `239` genuine steps read `vals[1] = true`.**  Head `4 * 11 = 44`,
control the pass-A reset handoff `readAResetStart`, `G1Ctx.vB = true`, tape
`g1BReadFramesFinal`: data region back to `[false, true]`, no cursor, the single
operand-2 unit left `spent`. -/
theorem read_positive :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1BReadExample))) 239 =
      g1AlignedConfig (encodeG1 g1BReadExample).length 44
        (g1_route_lt_tapeLength g1BReadExample 11 (by decide))
        (g1ListTape (g1BReadFramesFinal.flatMap G1Frame.bits))
        .readAResetStart .p0 false false false (g1Ctx0.withVB true) := by
  have h := g1CS_readB_positive_exact g1BReadExample g1BReadExample_canonical
    (Or.inl rfl) (by decide) true (by decide)
  rw [readExample_steps, readFramesFinal_eq] at h
  exact h

theorem read_positive_vB :
    (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1BReadExample)))
        239).state.snd.ctx.vB = true := by
  rw [read_positive]; rfl

theorem read_positive_head :
    ((TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1BReadExample)))
        239).head : Nat) = 44 := by
  rw [read_positive]; rfl

/-- The unchanged public clock for this request is `512 * 53² + 512`. -/
theorem readExample_clock_value :
    g1Clock (encodeG1 g1BReadExample).length = 1438720 := by
  rw [g1BReadExample_length]; rfl

theorem read_positive_clock :
    239 ≤ g1Clock (encodeG1 g1BReadExample).length := by
  rw [← readExample_steps]
  exact g1BReadSteps_le_clock g1BReadExample

/-! ## `⟨and, 0, 2, [false, true, true]⟩`: reading operand-2 index `2` -/

/-- The `arg2 = 2` read ends on the literal word `GateOneWalkExamples` already
produced. -/
theorem walkExample_framesFinal :
    g1BSpentFrames g1WalkExample g1WalkExample.arg2 = g1WalkFramesFinal := rfl

/-- `169` scan steps plus `8 * 2² + 45 * 2 + 37 = 159`: nine installation
steps, two rounds (`37 + 53 = 90`) and the terminal (`16 * 2 + 28 = 60`). -/
theorem walkExample_steps : g1BReadSteps g1WalkExample = 328 := by
  rw [g1BReadSteps, walk_install_scan_steps]; rfl

theorem walkExample_steps_split :
    g1BReadSteps g1WalkExample = 178 + (37 + 53) + 60 := by
  rw [walkExample_steps]

/-- **Exactly `328` genuine steps read `vals[2] = true`.**  Head `4 * 13 = 52`,
control `readAResetStart`, `G1Ctx.vB = true`, tape `g1WalkFramesFinal`: data
region back to `[false, true, true]`, no cursor, operand-2 field `spent²`. -/
theorem read_positive_two :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1WalkExample))) 328 =
      g1AlignedConfig (encodeG1 g1WalkExample).length 52
        (g1_route_lt_tapeLength g1WalkExample 13 (by decide))
        (g1ListTape (g1WalkFramesFinal.flatMap G1Frame.bits))
        .readAResetStart .p0 false false false (g1Ctx0.withVB true) := by
  have h := g1CS_readB_positive_exact g1WalkExample g1WalkExample_canonical
    (Or.inl rfl) (by decide) true (by decide)
  rw [walkExample_steps, walkExample_framesFinal] at h
  exact h

theorem read_positive_two_vB :
    (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1WalkExample)))
        328).state.snd.ctx.vB = true := by
  rw [read_positive_two]; rfl

theorem read_positive_two_clock :
    328 ≤ g1Clock (encodeG1 g1WalkExample).length := by
  rw [← walkExample_steps]
  exact g1BReadSteps_le_clock g1WalkExample

/-! ## The aggregated out-of-range branch at `m = 0`: `⟨and, 0, 2, []⟩`, the
empty-data branch, read-only from start to finish -/

theorem emptyExample_oob_steps : g1BOOBSteps g1EmptyExample = 149 := by
  simp only [g1BOOBSteps, g1InstallScanSteps, g1ReadBHandoffSteps,
    g1EmptyExample_length]
  rfl

/-- At `m = 0` the aggregated layout is literally the initial word. -/
theorem emptyExample_frames :
    g1BSpentFrames g1EmptyExample g1EmptyExample.vals.length =
      encodeG1Frames g1EmptyExample ++ [G1Frame.blank] :=
  g1BSpentFrames_empty g1EmptyExample rfl

/-- **Exactly `149` genuine steps end in the stable `bOOB` boundary**, head
`4 * 11 = 44`, context `g1Ctx0` — nothing was latched — and the tape is
bit-for-bit the initial word at the endpoint. -/
theorem oob_empty :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1EmptyExample))) 149 =
      g1AlignedConfig (encodeG1 g1EmptyExample).length 44
        (g1_route_lt_tapeLength g1EmptyExample 11 (by decide))
        (g1ListTape
          ((g1BSpentFrames g1EmptyExample 0).flatMap G1Frame.bits))
        .bOOB .p0 false false false g1Ctx0 := by
  have h := g1CS_readB_positive_oob_exact g1EmptyExample
    g1EmptyExample_canonical (Or.inl rfl) (by decide) (by decide)
  rw [emptyExample_oob_steps] at h
  exact h

theorem oob_empty_clock :
    149 ≤ g1Clock (encodeG1 g1EmptyExample).length := by
  rw [← emptyExample_oob_steps]
  exact g1BOOBSteps_le_clock g1EmptyExample

/-! ## The aggregated out-of-range branch at `0 < m ≤ arg2`

`⟨and, 0, 2, [false, true]⟩`: the walk installs, runs one full round and aborts
in the second round's probe. -/

/-- `161` scan steps plus `8 * 2² + 29 * 2 + 4 = 94`: nine installation steps,
one round (`37`) and the out-of-range round (`48`). -/
theorem oobExample_oob_steps : g1BOOBSteps g1OOBExample = 255 := by
  simp only [g1BOOBSteps, g1InstallScanSteps, g1ReadBHandoffSteps,
    show (encodeG1 g1OOBExample).length = 56 from by rw [encodeG1_length]; rfl]
  rfl

theorem oobExample_oob_steps_split :
    g1BOOBSteps g1OOBExample = 170 + 37 + 48 := by
  rw [oobExample_oob_steps]

/-- The aggregated layout at `m = 2` is the merged one-round out-of-range
literal. -/
theorem oobExample_frames :
    g1BSpentFrames g1OOBExample g1OOBExample.vals.length =
      g1OOBFramesRestored1 := rfl

/-- **Exactly `255` genuine steps end in the stable `bOOB` boundary**, head
`4 * 13 = 52`, context `g1Ctx0.withVB vals[1]`, tape `g1OOBFramesRestored1`:
data region back to `[false, true]`, no cursor, operand-2 field consumed to
`spent²` — unrepaired. -/
theorem oob_nonempty :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1OOBExample))) 255 =
      g1AlignedConfig (encodeG1 g1OOBExample).length 52
        (g1_route_lt_tapeLength g1OOBExample 13 (by decide))
        (g1ListTape (g1OOBFramesRestored1.flatMap G1Frame.bits))
        .bOOB .p0 false false false (g1Ctx0.withVB true) := by
  have h := g1CS_readB_positive_oob_exact g1OOBExample g1OOBExample_canonical
    (Or.inl rfl) (by decide) (by decide)
  rw [oobExample_oob_steps, oobExample_frames] at h
  exact h

theorem oob_nonempty_head :
    ((TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1OOBExample)))
        255).head : Nat) = 52 := by
  rw [oob_nonempty]; rfl

theorem oob_nonempty_clock :
    255 ≤ g1Clock (encodeG1 g1OOBExample).length := by
  rw [← oobExample_oob_steps]
  exact g1BOOBSteps_le_clock g1OOBExample

end G1WalkDriverExamples

end Pnp3.Internal.PsubsetPpoly.TM
