import Complexity.TMVerifier.TuringToolkit.GateOneRepairDriver
import Complexity.TMVerifier.TuringToolkit.GateOneWalkDriverExamples
import Complexity.TMVerifier.TuringToolkit.GateOneRepairKernelExamples

/-!
# G1 operand-2 repair sweep: concrete repaired reads from `G1M.initialConfig`

**Progress classification: Infrastructure.**  The Repair-2b slice: three
all-literal probes of the Repair-2a capstones, one per operand-2 index.

| request | index | read | sweep | total |
|---------|-------|------|-------|-------|
| `⟨and, 0, 0, [true]⟩` | `0` | `134` | `38` | `172` |
| `⟨and, 0, 1, [false, true]⟩` | `1` | `239` | `55` | `294` |
| `⟨and, 0, 2, [false, true, true]⟩` | `2` | `328` | `72` | `400` |

Every step count, head position and frame word is a literal, and each probe is
an exact configuration equality of `G1M` **from the real `G1M.initialConfig`** —
exactly what Repair-1b's caller-supplied kernel probes could not say.  All three
endpoint tapes are bit-for-bit the initial tape: the canonical encoded word plus
the trailing `blank` frame, with **no** consumed unit and **no** cursor.

**Three different lengths, kept apart** (`probe_extents`), and nothing below
conflates them: the **encoded input length** `(encodeG1 r).length` (`44`, `52`,
`60` cells, four per encoded frame); the explicit **validation frame-word
extent** (`48`, `56`, `64` — the encoded word plus the four cells of the
trailing all-false `blank` frame); and the
**physical tape capacity** `G1M.tapeLength (encodeG1 r).length`, a separately
derived number (`1037357` for the zero probe) far larger than either.  The
physical tape is not the input and its length is not the input length, and
`zero_safe`/`one_safe`/`two_safe` *derive* each head-safety bound from the
encoded length.

**Reuse, not duplication.**  The `arg2 = 1` request/read count comes from
`GateOneWalkDriverExamples`; the `arg2 = 2` request is
`GateOneInstallScanExamples.g1WalkExample`.  Its endpoint words and counts are
`GateOneRepairKernelExamples`' `probeSpentFrames`/`probeIndexFrames` verbatim.
Repair-1b's caller-supplied pass used a six-frame middle and `79` steps; this
slice's real run uses a four-frame middle and `72` repair steps.  Only the words
coincide.  No caller-supplied kernel probe is restated.

**Explicitly deferred.**  Nothing here reads operand 1, activates `readAStart`,
combines, writes the output frame or mentions `TM.accepts`: the three
`readA_idle_after_*` theorems show the endpoint is a stationary handoff for the
whole remaining budget.  Also absent and claimed nowhere: a full-clock theorem,
gate-semantics correctness, the acceptance gate, multi-gate composition, the
specification-level bridge, and any literal probe of the unrepaired
out-of-range boundary or of a non-canonical word.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

namespace G1RepairExamples

open G1InstallScanExamples (g1WalkExample g1WalkExample_canonical
  g1WalkExample_length)
open G1WalkDriverExamples (g1BReadExample g1BReadExample_canonical
  g1BReadExample_length g1BReadFramesFinal readExample_steps walkExample_steps
  read_positive read_positive_two)
open G1RepairKernelExamples (probeSpentFrames probeIndexFrames
  probeIndex_eq_encoded probe_counts)


/-- `and` with both operand fields empty and a one-bit data region: the
zero-index probe.  The two positive-index requests are the merged literals
`g1BReadExample = ⟨and, 0, 1, [false, true]⟩` and
`g1WalkExample = ⟨and, 0, 2, [false, true, true]⟩`. -/
def g1ZeroExample : G1Request := ⟨.and, 0, 0, [true]⟩

theorem g1ZeroExample_canonical : g1ZeroExample.Canonical := by decide

/-- The **encoded input length**: eleven encoded frames, four cells each. -/
theorem g1ZeroExample_length : (encodeG1 g1ZeroExample).length = 44 := by
  rw [encodeG1_length]; rfl

/-- Every cell the zero probe touches is far inside the physical tape, and the
bound is derived from the encoded length rather than assumed. -/
theorem zero_safe {k : Nat} (hk : k ≤ 48) :
    k < G1M.tapeLength (encodeG1 g1ZeroExample).length :=
  g1_lt_tapeLength (by rw [g1ZeroExample_length]; omega)

theorem one_safe {k : Nat} (hk : k ≤ 56) :
    k < G1M.tapeLength (encodeG1 g1BReadExample).length :=
  g1_lt_tapeLength (by rw [g1BReadExample_length]; omega)

theorem two_safe {k : Nat} (hk : k ≤ 64) :
    k < G1M.tapeLength (encodeG1 g1WalkExample).length :=
  g1_lt_tapeLength (by rw [g1WalkExample_length]; omega)


/-- The zero probe's endpoint word: the canonical eleven-frame encoding plus the
trailing `blank` frame.  No `spent`, no `cursor`, no operand-2 unit at all. -/
def g1ZeroFrames : List G1Frame :=
  [.bof, .tag, .tag, .tag, .tag, .argSep, .argSep, .separator, .data true,
    .output false, .finish, .blank]

theorem zeroFrames_eq :
    encodeG1Frames g1ZeroExample ++ [G1Frame.blank] = g1ZeroFrames := rfl

/-- **At `arg2 = 0` the sweep has no repair frame to rewrite.**  The entry
layout is already canonical and its `spent → index` block has length `13 * 0`. -/
theorem zeroFrames_layout : g1BSpentFrames g1ZeroExample 0 = g1ZeroFrames := rfl

theorem zeroFrames_counts :
    g1ZeroFrames.count G1Frame.spent = 0 ∧
      g1ZeroFrames.count G1Frame.cursor = 0 ∧
      g1ZeroFrames.count G1Frame.index = 0 ∧
      g1ZeroFrames.length = 12 := by decide

/-- The word the `arg2 = 1` sweep restores: the single `spent` unit of
`g1BReadFramesFinal` is back to `index`. -/
def g1OneRepairedFrames : List G1Frame :=
  [.bof, .tag, .tag, .tag, .tag, .argSep, .argSep, .index, .separator,
    .data false, .data true, .output false, .finish, .blank]

theorem oneRepairedFrames_eq :
    encodeG1Frames g1BReadExample ++ [G1Frame.blank] = g1OneRepairedFrames := rfl

/-- **The consumed unit really comes back.**  The read's terminal word carries
one `spent` and no `index`; the repaired word carries no `spent`, no `cursor`
and the unit as `index` again. -/
theorem oneRepairedFrames_counts :
    g1BReadFramesFinal.count G1Frame.spent = 1 ∧
      g1BReadFramesFinal.count G1Frame.index = 0 ∧
      g1OneRepairedFrames.count G1Frame.spent = 0 ∧
      g1OneRepairedFrames.count G1Frame.cursor = 0 ∧
      g1OneRepairedFrames.count G1Frame.index = 1 ∧
      g1OneRepairedFrames.length = 14 := by decide

/-- **The `arg2 = 2` probe reuses the Repair-1b words verbatim.**  The read's
terminal word is exactly `probeSpentFrames`, the repaired word exactly
`probeIndexFrames`. -/
theorem twoFrames_eq :
    g1BSpentFrames g1WalkExample g1WalkExample.arg2 = probeSpentFrames ∧
      encodeG1Frames g1WalkExample ++ [G1Frame.blank] = probeIndexFrames :=
  ⟨rfl, probeIndex_eq_encoded.symm⟩

/-- The `spent`/`index` counts are Repair-1b's own results, reused; only the
absent `cursor` is new here. -/
theorem twoRepaired_counts :
    probeSpentFrames.count G1Frame.spent = 2 ∧
      probeIndexFrames.count G1Frame.spent = 0 ∧
      probeIndexFrames.count G1Frame.index = 2 ∧
      probeIndexFrames.count G1Frame.cursor = 0 :=
  ⟨probe_counts.1, probe_counts.2.2.1, probe_counts.2.2.2.2.1, by decide⟩

/-- Three different numbers per probe: `4` cells per encoded frame; four cells
more in the explicit validation word for the all-false trailing `blank`; and a
separately derived capacity, `44 + g1Clock 44 + 1` for the zero probe. -/
theorem probe_extents :
    ((encodeG1 g1ZeroExample).length = 44 ∧
        (g1ZeroFrames.flatMap G1Frame.bits).length = 48 ∧
        48 < G1M.tapeLength (encodeG1 g1ZeroExample).length) ∧
      ((encodeG1 g1BReadExample).length = 52 ∧
        (g1OneRepairedFrames.flatMap G1Frame.bits).length = 56 ∧
        56 < G1M.tapeLength (encodeG1 g1BReadExample).length) ∧
      ((encodeG1 g1WalkExample).length = 60 ∧
        (probeIndexFrames.flatMap G1Frame.bits).length = 64 ∧
        64 < G1M.tapeLength (encodeG1 g1WalkExample).length) ∧
      G1M.tapeLength (encodeG1 g1ZeroExample).length = 1037357 :=
  ⟨⟨g1ZeroExample_length, by decide, zero_safe (by omega)⟩,
    ⟨g1BReadExample_length, by decide, one_safe (by omega)⟩,
    ⟨g1WalkExample_length, by decide, two_safe (by omega)⟩,
    by rw [g1ZeroExample_length]; rfl⟩

/-- `1 + 8 + 0 + 24 + 5`: at `s = 0` the sweep is a pure rewind. -/
theorem repairSteps_zero : g1RepairSteps g1ZeroExample 0 = 38 := rfl

/-- `1 + 12 + 13 + 24 + 5`: one consumed unit repaired. -/
theorem repairSteps_one : g1RepairSteps g1BReadExample 1 = 55 := rfl

/-- `1 + 16 + 26 + 24 + 5`: two consumed units repaired. -/
theorem repairSteps_two : g1RepairSteps g1WalkExample 2 = 72 := rfl

/-- The same three literals through the driver's own decomposition
`1 + g1RepairPassSteps (left) s (mid)` at the real layout lengths: the left run
is `6` frames in all three, the middle run grows `2, 3, 4` with the index, and
the `13 * s` write block is empty at `s = 0`. -/
theorem repairSteps_splits :
    g1RepairSteps g1ZeroExample 0 = 1 + g1RepairPassSteps 6 0 2 ∧
      g1RepairSteps g1BReadExample 1 = 1 + g1RepairPassSteps 6 1 3 ∧
      g1RepairSteps g1WalkExample 2 = 1 + g1RepairPassSteps 6 2 4 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [g1RepairSteps_eq g1ZeroExample 0 (by decide) (by decide)]; rfl
  · rw [g1RepairSteps_eq g1BReadExample 1 (by decide) (by decide)]; rfl
  · rw [g1RepairSteps_eq g1WalkExample 2 (by decide) (by decide)]; rfl


/-- The read `2 * 44 + 9 + 4 * 9 + 1`, the total, and its split. -/
theorem zeroExample_steps :
    g1ReadBSteps g1ZeroExample = 134 ∧ g1ZPassASteps g1ZeroExample = 172 ∧
      g1ZPassASteps g1ZeroExample = 134 + 38 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [g1ZPassASteps, g1ReadBSteps, g1ReadBHandoffSteps,
      g1ZeroExample_length] <;> rfl

/-- **Exactly `172` genuine steps read `vals[0] = true` and return the head to
`0` in `readAStart`.**  The `38`-step sweep has an empty rewrite block and
walks back: it crosses the `separator` and the single data frame, finds no
consumed unit, crosses the tag run and both `argSep`s and dispatches. -/
theorem zero_repaired :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1ZeroExample))) 172 =
      g1ReadAConfig g1ZeroExample true := by
  have h := g1CS_readB_zero_repaired_exact g1ZeroExample g1ZeroExample_canonical
    (Or.inl rfl) rfl true (by decide)
  rw [zeroExample_steps.2.1] at h
  exact h

/-- Head `0`, control `readAStart` with an empty frame buffer, and the
**actual** `vals[0]` latched in `G1Ctx.vB`. -/
theorem zero_repaired_projections :
    ((TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1ZeroExample)))
          172).head : Nat) = 0 ∧
      (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1ZeroExample)))
          172).state.snd = g1ReadAState (g1Ctx0.withVB true) ∧
      (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1ZeroExample)))
          172).state.snd.ctx.vB = true := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [zero_repaired] <;> rfl

/-- The latched bit is the request's own `vals[arg2]`, resolved physically. -/
theorem zero_selected :
    g1ZeroExample.vals[g1ZeroExample.arg2]? = some true ∧
      g1ZeroExample.vals = [true] := by decide

theorem zero_repaired_tape :
    (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1ZeroExample))) 172).tape =
      g1ListTape (g1ZeroFrames.flatMap G1Frame.bits) := by
  rw [zero_repaired, g1ReadAConfig_tape, zeroFrames_eq]

/-- **The zero branch has no net tape change.**  Its endpoint tape is literally
the initial tape, the entry layout is already canonical, and the sweep's
`spent → index` rewrite block has length `13 * 0`. -/
theorem zero_repaired_no_net_change :
    (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1ZeroExample))) 172).tape =
        (G1M.initialConfig (g1Point (encodeG1 g1ZeroExample))).tape ∧
      g1BSpentFrames g1ZeroExample 0 = g1ZeroFrames ∧
      g1ZeroFrames.count G1Frame.spent = 0 :=
  ⟨by rw [zero_repaired]; rfl, zeroFrames_layout, zeroFrames_counts.1⟩

/-- The **unchanged** public clock of this request is `512 * 45 ^ 2 + 512`, and
the total fits inside it. -/
theorem zero_repaired_clock :
    g1Clock (encodeG1 g1ZeroExample).length = 1037312 ∧
      172 ≤ g1Clock (encodeG1 g1ZeroExample).length := by
  refine ⟨by rw [g1ZeroExample_length]; rfl, ?_⟩
  rw [← zeroExample_steps.2.1]
  exact g1ZPassASteps_le_clock g1ZeroExample

/-- The endpoint is a **handoff**, not a continuation: it holds its state, head
and tape for the whole remaining budget.  Operand 1 is not read. -/
theorem readA_idle_after_zero (k : Nat) :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1ZeroExample))) (172 + k) =
      g1ReadAConfig g1ZeroExample true := by
  rw [runConfig_add, zero_repaired]
  exact g1CS_runConfig_readA_idle _ _ _ _ _ k


/-- The cumulative total, and its split into the merged `239`-step read and the
`55`-step sweep. -/
theorem oneExample_steps :
    g1BPassASteps g1BReadExample = 294 ∧
      g1BPassASteps g1BReadExample = 239 + 55 := by
  refine ⟨?_, ?_⟩ <;> rw [g1BPassASteps, readExample_steps] <;> rfl

/-- **Exactly `294` genuine steps read `vals[1] = true` and repair the tape.**
`239` are the cursor-walk read, ending at head `44` with the single operand-2
unit `spent`; the remaining `55` are the sweep, which turns that unit back into
`index` and returns the head to `0` with `vB = true` still latched. -/
theorem one_repaired :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1BReadExample))) 294 =
      g1ReadAConfig g1BReadExample true := by
  have h := g1CS_readB_positive_repaired_exact g1BReadExample
    g1BReadExample_canonical (Or.inl rfl) (by decide) true (by decide)
  rw [oneExample_steps.1] at h
  exact h

theorem one_repaired_projections :
    ((TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1BReadExample)))
          294).head : Nat) = 0 ∧
      (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1BReadExample)))
          294).state.snd = g1ReadAState (g1Ctx0.withVB true) ∧
      (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1BReadExample)))
          294).state.snd.ctx.vB = true := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [one_repaired] <;> rfl

/-- **The latched bit is the actual selected element, not `vals[0]`:** this
request's data region is `[false, true]`, the read returns `vals[1] = true`, and
`vals[0]` is `false`. -/
theorem one_selected :
    g1BReadExample.vals[g1BReadExample.arg2]? = some true ∧
      g1BReadExample.vals[0]? = some false ∧
      g1BReadExample.vals = [false, true] := by decide

/-- The endpoint word is the canonical encoding plus the trailing `blank`, and
that word is bit-for-bit the machine's initial tape. -/
theorem one_repaired_tape :
    (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1BReadExample))) 294).tape =
        g1ListTape (g1OneRepairedFrames.flatMap G1Frame.bits) ∧
      (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1BReadExample))) 294).tape =
        (G1M.initialConfig (g1Point (encodeG1 g1BReadExample))).tape := by
  refine ⟨?_, by rw [one_repaired]; rfl⟩
  rw [one_repaired, g1ReadAConfig_tape, oneRepairedFrames_eq]

/-- **The sweep genuinely writes on this branch.**  Physical cell `28` — the
first cell of frame `7`, the single operand-2 unit — is `true` on the read's
terminal tape (`spent` spells `[true, true, false, false]`) and `false` at the
repaired endpoint (`index` spells `[false, false, true, true]`), so the `55`
sweep steps cannot be a no-op. -/
theorem one_repaired_cell28 :
    (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1BReadExample))) 239).tape
        ⟨28, one_safe (by omega)⟩ = true ∧
      (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1BReadExample))) 294).tape
        ⟨28, one_safe (by omega)⟩ = false := by
  refine ⟨by rw [read_positive]; rfl, ?_⟩
  rw [one_repaired_tape.1]; rfl

theorem one_repaired_clock :
    294 ≤ g1Clock (encodeG1 g1BReadExample).length := by
  rw [← oneExample_steps.1]
  exact g1BPassASteps_le_clock g1BReadExample

theorem readA_idle_after_one (k : Nat) :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1BReadExample))) (294 + k) =
      g1ReadAConfig g1BReadExample true := by
  rw [runConfig_add, one_repaired]
  exact g1CS_runConfig_readA_idle _ _ _ _ _ k


theorem twoExample_steps :
    g1BPassASteps g1WalkExample = 400 ∧
      g1BPassASteps g1WalkExample = 328 + 72 := by
  refine ⟨?_, ?_⟩ <;> rw [g1BPassASteps, walkExample_steps] <;> rfl

/-- **Exactly `400` genuine steps read `vals[2] = true` and repair the tape.**
`328` for the two-round cursor walk, `72` for the sweep, whose `26` write steps
are two thirteen-step `spent ↦ index` cycles. -/
theorem two_repaired :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1WalkExample))) 400 =
      g1ReadAConfig g1WalkExample true := by
  have h := g1CS_readB_positive_repaired_exact g1WalkExample
    g1WalkExample_canonical (Or.inl rfl) (by decide) true (by decide)
  rw [twoExample_steps.1] at h
  exact h

theorem two_repaired_projections :
    ((TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1WalkExample)))
          400).head : Nat) = 0 ∧
      (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1WalkExample)))
          400).state.snd = g1ReadAState (g1Ctx0.withVB true) ∧
      (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1WalkExample)))
          400).state.snd.ctx.vB = true := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [two_repaired] <;> rfl

theorem two_selected :
    g1WalkExample.vals[g1WalkExample.arg2]? = some true ∧
      g1WalkExample.vals[0]? = some false ∧
      g1WalkExample.vals = [false, true, true] := by decide

/-- The endpoint word is Repair-1b's `probeIndexFrames`, and that word is
bit-for-bit the machine's initial tape. -/
theorem two_repaired_tape :
    (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1WalkExample))) 400).tape =
        g1ListTape (probeIndexFrames.flatMap G1Frame.bits) ∧
      (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1WalkExample))) 400).tape =
        (G1M.initialConfig (g1Point (encodeG1 g1WalkExample))).tape := by
  refine ⟨?_, by rw [two_repaired]; rfl⟩
  rw [two_repaired, g1ReadAConfig_tape, ← probeIndex_eq_encoded]

/-- **The machine reaches the two Repair-1b words from `G1M.initialConfig`.**
Here the executed sweep is the `72`-step instance with a four-frame scanned
middle; Repair-1b's `79`-step caller-supplied pass used a six-frame middle.  The
words coincide, not the pass instances. -/
theorem two_repaired_kernel_words :
    (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1WalkExample))) 328).tape =
        g1ListTape (probeSpentFrames.flatMap G1Frame.bits) ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1WalkExample))) 400).tape =
        g1ListTape (probeIndexFrames.flatMap G1Frame.bits) := by
  refine ⟨?_, two_repaired_tape.1⟩
  rw [read_positive_two]; rfl

/-- **The executed sweep genuinely writes here too.**  Physical cell `32` — the
first cell of frame `8`, the rightmost operand-2 unit — is `true` after the read
and `false` after the sweep. -/
theorem two_repaired_cell32 :
    (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1WalkExample))) 328).tape
        ⟨32, two_safe (by omega)⟩ = true ∧
      (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1WalkExample))) 400).tape
        ⟨32, two_safe (by omega)⟩ = false := by
  refine ⟨?_, ?_⟩
  · rw [two_repaired_kernel_words.1]; rfl
  · rw [two_repaired_kernel_words.2]; rfl

theorem two_repaired_clock :
    400 ≤ g1Clock (encodeG1 g1WalkExample).length := by
  rw [← twoExample_steps.1]
  exact g1BPassASteps_le_clock g1WalkExample

theorem readA_idle_after_two (k : Nat) :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1WalkExample))) (400 + k) =
      g1ReadAConfig g1WalkExample true := by
  rw [runConfig_add, two_repaired]
  exact g1CS_runConfig_readA_idle _ _ _ _ _ k


/-- The zero-index literal takes the `g1ZPassASteps` arm, the two others the
`g1BPassASteps` arm. -/
theorem common_arms_distinct :
    g1ZeroExample.arg2 = 0 ∧ g1BReadExample.arg2 ≠ 0 ∧
      g1WalkExample.arg2 ≠ 0 := by decide

/-- The branch is not vacuous: at the zero-index request the other arm would be
`204`, not `172`. -/
theorem common_branch_literals :
    (if g1ZeroExample.arg2 = 0 then g1ZPassASteps g1ZeroExample
        else g1BPassASteps g1ZeroExample) = 172 ∧
      (if g1BReadExample.arg2 = 0 then g1ZPassASteps g1BReadExample
        else g1BPassASteps g1BReadExample) = 294 ∧
      (if g1WalkExample.arg2 = 0 then g1ZPassASteps g1WalkExample
        else g1BPassASteps g1WalkExample) = 400 ∧
      g1BPassASteps g1ZeroExample = 204 := by
  refine ⟨zeroExample_steps.2.1, oneExample_steps.1, twoExample_steps.1, ?_⟩
  simp only [g1BPassASteps, g1BReadSteps, g1InstallScanSteps,
    g1ReadBHandoffSteps, g1ZeroExample_length]
  rfl

/-- **The zero arm of the common capstone, on a literal.** -/
theorem common_zero_arm :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1ZeroExample)))
        (if g1ZeroExample.arg2 = 0 then g1ZPassASteps g1ZeroExample
          else g1BPassASteps g1ZeroExample) =
      g1ReadAConfig g1ZeroExample true :=
  g1CS_readB_repaired_common g1ZeroExample g1ZeroExample_canonical (Or.inl rfl)
    true (by decide)

/-- **The positive arm of the common capstone, on a literal.** -/
theorem common_positive_arm :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1WalkExample)))
        (if g1WalkExample.arg2 = 0 then g1ZPassASteps g1WalkExample
          else g1BPassASteps g1WalkExample) =
      g1ReadAConfig g1WalkExample true :=
  g1CS_readB_repaired_common g1WalkExample g1WalkExample_canonical (Or.inl rfl)
    true (by decide)

/-- Both literal totals fit the **unchanged** public clock. -/
theorem common_branch_clock :
    (if g1ZeroExample.arg2 = 0 then g1ZPassASteps g1ZeroExample
        else g1BPassASteps g1ZeroExample) ≤
        g1Clock (encodeG1 g1ZeroExample).length ∧
      (if g1WalkExample.arg2 = 0 then g1ZPassASteps g1WalkExample
        else g1BPassASteps g1WalkExample) ≤
        g1Clock (encodeG1 g1WalkExample).length :=
  ⟨g1CS_readB_repaired_common_le_clock g1ZeroExample,
    g1CS_readB_repaired_common_le_clock g1WalkExample⟩

end G1RepairExamples

end Pnp3.Internal.PsubsetPpoly.TM
