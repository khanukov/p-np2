import Complexity.TMVerifier.TuringToolkit.GateOneWalkInvariant
import Complexity.TMVerifier.TuringToolkit.GateOneProbeInstallExamples
import Complexity.TMVerifier.TuringToolkit.GateOneWalkExamples

/-!
# G1 cursor walk: concrete probes of `Σ(j)`, its installation and one round

**Progress classification: Infrastructure.**  All-literal probes of the PR3a
and PR3b capstones, on three literal requests:

| request | probe | steps | heads |
|---------|-------|-------|-------|
| `⟨and, 0, 2, [false, true, true]⟩` | install into `Σ(0)` | `178` | `→ 39` |
| `⟨and, 0, 2, [false, true, true]⟩` | `Σ(0) → Σ(1)` | `37` | `39 → 43` |
| `⟨and, 0, 2, [false, true, true]⟩` | `Σ(1) → Σ(2)` | `53` | `43 → 47` |
| `⟨and, 0, 2, [false, true]⟩` | non-empty OOB round at `j = 1` | `48` | `43 → 52` |
| `⟨and, 0, 2, []⟩` | empty-data install OOB | `149` | `→ 44` |

The first request, its canonicity and its `169`-step installation scan are the
merged `G1InstallScanExamples.g1WalkExample`: **fifteen** encoded frames and
`60` input cells; the list-backed layouts append one `blank`, the frame the
machine's own tape supplies past the input, so each has **sixteen** frames.  The
prefix `bof · tag⁴ · argSep · argSep` lies at ordinals `0 … 6`, the operand-2
field at ordinals `7 … 8`, the data region from ordinal `10`, and the cursor of
`Σ(j)` at ordinal `j + 10`.

No frame word is copied twice.  `Σ(0)` is literally the layout the merged
cursor-install probe produces, `G1ProbeInstallExamples.g1WalkFramesCursor0`, and
`Σ(1)`, `Σ(2)` and the round's restored layout are literally the merged
`G1WalkExamples.g1WalkFramesRound1`, `g1WalkFramesTerminal` and
`g1WalkFramesRestored1`: the words the atomic probes were stated on really are
the invariant at those `j`.  Only the out-of-range request, whose data region is
shorter, needs its own two literals.

Each round probe below is **one** round.  Nothing here iterates, chains
`walk_install` to `walk_round_zero`, sums a loop clock, reaches a successful
terminal or reads an arbitrary operand-2 index, and the out-of-range probe
claims no verdict: its tape is an intermediate, unrepaired one.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

namespace G1WalkInvariantExamples

open G1InstallScanExamples (g1WalkExample g1WalkExample_canonical
  walk_install_scan_steps)

open G1WalkExamples (g1WalkFramesRound1 g1WalkFramesRestored1
  g1WalkFramesTerminal)

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

/-- `Σ(1)` is literally the layout `GateOneWalkExamples` states its atomic
probes on: `index` at ordinal `7`, `spent` at ordinal `8`, the cursor at ordinal
`11` hiding `vals[1] = true`. -/
theorem walkFrames_one : g1WalkFrames g1WalkExample 1 = g1WalkFramesRound1 :=
  rfl

/-- `Σ(2)` is the terminal layout of `GateOneWalkExamples`: operand 2 entirely
`spent`, the cursor at ordinal `12`. -/
theorem walkFrames_two : g1WalkFrames g1WalkExample 2 = g1WalkFramesTerminal :=
  rfl

/-- The layout the round at `j = 1` passes through after its cursor restore:
the data region is exactly `vals` again and carries no cursor. -/
theorem walkFramesRestored_one :
    g1WalkFramesRestored g1WalkExample 1 = g1WalkFramesRestored1 := rfl

theorem walkCursor_one : g1WalkCursor g1WalkExample 1 = 11 := rfl

theorem walkCursor_two : g1WalkCursor g1WalkExample 2 = 12 := rfl

/-- `Σ(1)` has the same sixteen frames as `Σ(0)`: a round invents no frame and
loses none. -/
theorem walkFrames_one_length : (g1WalkFrames g1WalkExample 1).length = 16 :=
  rfl

/-- The cursor is still unique after one round. -/
theorem walkFrames_one_count_cursor :
    (g1WalkFrames g1WalkExample 1).count G1Frame.cursor = 1 := by decide

/-- One on-tape decrement: at `j = 1` exactly one operand-2 unit is spent and
one is left. -/
theorem walkFrames_one_count_index :
    (g1WalkFrames g1WalkExample 1).count G1Frame.index = 1 := by decide

theorem walkFrames_one_count_spent :
    (g1WalkFrames g1WalkExample 1).count G1Frame.spent = 1 := by decide

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

/-! ## Two single rounds of the walk

Each is **one** application of `g1CS_walk_iteration_exact` on a configuration
written out in full; neither is chained to `walk_install` above or to the other,
and no clock bound is claimed for either. -/

/-- **`Σ(0) → Σ(1)` in exactly `16 * 0 + 37 = 37` genuine steps.**  Head
`39 → 43`; the `index` at ordinal `7` becomes `spent`, the unique cursor moves
from ordinal `10` to ordinal `11`, data slot `0` is restored to `data false` —
the bit `Σ(0)` recorded as hidden — and `vB` becomes `vals[1] = true`, which is
`Σ(1)`'s own hidden bit. -/
theorem walk_round_zero :
    TM.runConfig (M := G1M)
        (g1WalkConfig g1WalkExample 0 (by decide) (by decide) false
          (by decide)) 37 =
      g1WalkConfig g1WalkExample 1 (by decide) (by decide) true (by decide) :=
  g1CS_walk_iteration_exact g1WalkExample 0 (by decide) (by decide) false true
    (by decide) (by decide)

/-- **`Σ(1) → Σ(2)` in exactly `16 * 1 + 37 = 53` genuine steps.**  Head
`43 → 47`; the last remaining `index`, at ordinal `8`, becomes `spent`, the
cursor moves from ordinal `11` to ordinal `12`, slot `1` is restored to
`data true`, and `vB` becomes `vals[2] = true`. -/
theorem walk_round_one :
    TM.runConfig (M := G1M)
        (g1WalkConfig g1WalkExample 1 (by decide) (by decide) true
          (by decide)) 53 =
      g1WalkConfig g1WalkExample 2 (by decide) (by decide) true (by decide) :=
  g1CS_walk_iteration_exact g1WalkExample 1 (by decide) (by decide) true true
    (by decide) (by decide)

theorem walk_round_zero_head :
    ((g1WalkConfig g1WalkExample 0 (by decide) (by decide) false
      (by decide)).head : Nat) = 39 := rfl

theorem walk_round_one_head :
    ((g1WalkConfig g1WalkExample 1 (by decide) (by decide) true
      (by decide)).head : Nat) = 43 := rfl

theorem walk_round_two_head :
    ((g1WalkConfig g1WalkExample 2 (by decide) (by decide) true
      (by decide)).head : Nat) = 47 := rfl

/-! ## The non-empty out-of-range round

`⟨and, 0, 2, [false, true]⟩`: an operand-2 index of `2` against a two-element
data region.  At `j = 1` the cursor sits on the *last* data frame while one
operand-2 unit is still unspent, so the round aborts at its probe. -/

def g1OOBExample : G1Request := ⟨.and, 0, 2, [false, true]⟩

theorem g1OOBExample_canonical : g1OOBExample.Canonical := by decide

/-- `Σ(1)` for `g1OOBExample`: one unspent `index` at ordinal `7`, one `spent`
at ordinal `8`, the cursor at ordinal `11` hiding the last data bit
`vals[1] = true`.  This request's data region is one frame shorter than
`g1WalkExample`'s, so its layouts are not the merged ones. -/
def g1OOBFramesRound1 : List G1Frame :=
  [.bof, .tag, .tag, .tag, .tag, .argSep, .argSep, .index, .spent, .separator,
    .data false, .cursor, .output false, .finish, .blank]

/-- The layout the out-of-range boundary is reached on: the data region is
exactly `vals` and carries **no cursor**, while the operand-2 field is
*partially spent and unrepaired* — `spent²`, no `index` left. -/
def g1OOBFramesRestored1 : List G1Frame :=
  [.bof, .tag, .tag, .tag, .tag, .argSep, .argSep, .spent, .spent, .separator,
    .data false, .data true, .output false, .finish, .blank]

theorem oobFrames_one : g1WalkFrames g1OOBExample 1 = g1OOBFramesRound1 := rfl

theorem oobFrames_one_length : g1OOBFramesRound1.length = 15 := rfl

theorem oobFrames_one_count_cursor :
    g1OOBFramesRound1.count G1Frame.cursor = 1 := by decide

theorem oobFramesRestored_one :
    g1WalkFramesRestored g1OOBExample 1 = g1OOBFramesRestored1 := rfl

theorem oobFramesRestored_one_length : g1OOBFramesRestored1.length = 15 := rfl

/-- The final tape of the out-of-range round is **cursor-free**. -/
theorem oobFramesRestored_one_count_cursor :
    g1OOBFramesRestored1.count G1Frame.cursor = 0 := by decide

/-- …and operand 2 is **still spent**, not repaired. -/
theorem oobFramesRestored_one_count_spent :
    g1OOBFramesRestored1.count G1Frame.spent = 2 := by decide

theorem oobFramesRestored_one_count_index :
    g1OOBFramesRestored1.count G1Frame.index = 0 := by decide

/-- **The non-empty out-of-range round, exactly `16 * 1 + 32 = 48` steps.**
Head `43 → 52`: the old cursor at ordinal `11` is restored to `data true`, no
cursor is left anywhere, the operand-2 field ends up `spent²`, and the machine
stops in the stable `bOOB` boundary with `vB` still `vals[1] = true`.  The tape
is intermediate and unrepaired, and **no verdict is claimed**. -/
theorem walk_oob_round :
    TM.runConfig (M := G1M)
        (g1WalkConfig g1OOBExample 1 (by decide) (by decide) true
          (by decide)) 48 =
      g1AlignedConfig (encodeG1 g1OOBExample).length 52
        (g1WalkCursor_safe g1OOBExample 1 (by decide) (by decide))
        (g1ListTape (g1OOBFramesRestored1.flatMap G1Frame.bits))
        .bOOB .p0 false false false (g1Ctx0.withVB true) := by
  have h := g1CS_walk_oob_exact g1OOBExample 1 (by decide) (by decide) true
    (by decide)
  rw [oobFramesRestored_one] at h
  exact h

theorem walk_oob_round_head :
    ((g1WalkConfig g1OOBExample 1 (by decide) (by decide) true
      (by decide)).head : Nat) = 43 := rfl

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
