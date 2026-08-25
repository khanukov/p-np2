import Complexity.TMVerifier.TuringToolkit.FrameRewriteCycleInstances
import Complexity.TMVerifier.TuringToolkit.GateOneReadB

/-!
# G1 exact execution: one destructive operand-2 index round

**Progress classification: Infrastructure.**

The executable capstone of the T2b-2 slice.  `GateOneReadB` stops the `arg2 > 0`
branch at `bRoundStart`; this module runs it.  The four modes
`bWalk`/`bMark`/`bBack`/`bHop` of `g1Transition` are an instance of the generic
thirteen-step rewrite cycle (`FrameRewriteCycleInstances.g1IndexCycle`), so the
work here is exactly the composition:

```text
initialConfig
  --(2*|w|+9)-->            readBStart at head 0          (T2a, unchanged)
  --(4*(units+arg1+3))-->   bScan at the operand-2 field  (T2b-1, unchanged)
  --(4)-->                  bRoundStart, head 4*(units+arg1+4)
  --(1)-->                  bWalk, head 4*(units+arg1+3)+3   (the bridge)
  --(13)-->                 bWalk, head 4*(units+arg1+3)-1   (the round)
```

and the tape after the round is the canonical word with the **first** `index`
frame of the operand-2 field replaced by `spent`; every other cell is
bit-for-bit the initial tape.  `g1CS_round_from_bridge` is the fourteen-step
bridge-plus-round on an *arbitrary* frame list, `g1CS_index_first_round` the
composition from the real initial configuration, and `g1CS_round_example_*` a
concrete `and` request with `arg2 = 1` where every number is a literal.

**Scope.**  This is **one** round.  Nothing here iterates the round, addresses a
runtime index, terminates the reverse walk, restores the data region, or
resolves the operand-2 value for `arg2 > 0`: after the round the control sits on
the last cell of the frame *preceding* the rewritten one in `bWalk`, and no
theorem of this development runs it further.  In particular the endpoint of
`g1CS_index_first_round` is *not* an operand read: it is the `argSep` boundary of
the operand-2 field with one unit spent, and what the walk does next — including
whether it meets another `index` at all — is unclaimed.  There is no
`TM.accepts`, no output write, no combine step, no pass-A read and no
`spec`-correctness claim.  As everywhere else in T1/T2, each execution statement
is scoped to the exact tape `encodeG1 r`.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

/-! ## The route to the bridge

One more frame than the binary field route: the first `index` unit of the
operand-2 field, whose completion enters `bRoundStart`. -/

/-- The rest of the canonical word after the existing exact
`g1RoundRouteFrames` routing prefix, for an operand-2 field of length `k + 1`. -/
def g1RoundRouteRest (r : G1Request) (k : Nat) : List G1Frame :=
  List.replicate k .index ++ .separator ::
    (r.vals.map .data ++ [.output false, .finish, .blank])

/-! ## Step counts -/

/-- Steps from `initialConfig` to the bridge boundary of the first operand-2
index unit. -/
def g1RoundBoundarySteps (r : G1Request) : Nat :=
  g1ReadBHandoffSteps r + 4 * (r.tag.units + r.arg1 + 4)

/-- Steps from `initialConfig` to the endpoint of the first destructive round:
the bridge boundary plus `1 + 13`. -/
def g1IndexRoundSteps (r : G1Request) : Nat := g1RoundBoundarySteps r + 14

theorem g1RoundBoundarySteps_eq (r : G1Request) :
    g1RoundBoundarySteps r = g1FieldRouteSteps r + 4 := by
  unfold g1RoundBoundarySteps g1FieldRouteSteps
  omega

theorem g1IndexRoundSteps_eq (r : G1Request) :
    g1IndexRoundSteps r = g1FieldRouteSteps r + 18 := by
  rw [g1IndexRoundSteps, g1RoundBoundarySteps_eq]

/-- **The whole round fits the unchanged public clock.**  `g1Clock` is not
widened: the existing quadratic bound already dominates the bridge and the
thirteen round steps with room to spare. -/
theorem g1IndexRoundSteps_le_clock (r : G1Request) :
    g1IndexRoundSteps r ≤ g1Clock (encodeG1 r).length := by
  have hle := g1_route_le r (r.tag.units + r.arg1 + 4) (by omega)
  have hsq : (encodeG1 r).length + 1 ≤ ((encodeG1 r).length + 1) ^ 2 := by
    have h2 : ((encodeG1 r).length + 1) ^ 2 =
        ((encodeG1 r).length + 1) * ((encodeG1 r).length + 1) := by
      simp [Nat.pow_succ]
    rw [h2]
    exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have hmul : 512 * ((encodeG1 r).length + 1) ≤
      512 * ((encodeG1 r).length + 1) ^ 2 := Nat.mul_le_mul_left _ hsq
  simp only [g1IndexRoundSteps, g1RoundBoundarySteps, g1ReadBHandoffSteps,
    g1Clock]
  omega

/-! ## The bridge boundary, from the real initial configuration -/

/-- **The `arg2 > 0` branch reaches the bridge, exactly.**  For a canonical
`and`/`or` request whose operand-2 field is non-empty, exactly
`g1RoundBoundarySteps r` genuine steps validate the word, rewind, physically
rescan the tag, skip the operand-1 field and read the **first** `index` unit of
the operand-2 field, landing in `bRoundStart` with the head on the first cell of
the following frame, the context still `g1Ctx0`, and the tape bit-for-bit the
initial tape. -/
theorem g1CS_readB_round_boundary (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1RoundBoundarySteps r) =
      g1AlignedConfig (encodeG1 r).length (4 * (r.tag.units + r.arg1 + 4))
        (g1_route_lt_tapeLength r _ (by omega))
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        .bRoundStart .p0 false false false g1Ctx0 := by
  have hsafe : 4 * (g1RoundRouteFrames r).length <
      G1M.tapeLength (encodeG1 r).length := by
    rw [g1RoundRouteFrames_length]
    exact g1_route_lt_tapeLength r _ (by omega)
  have h := g1CS_readB_scan r hc (g1RoundRouteFrames r) (g1RoundRouteRest r k)
    (g1RoundRoute_split r k h2) (g1RoundRoute_validPath r ht) hsafe
  rw [g1RoundRoute_advance r ht] at h
  simpa [g1RoundBoundarySteps] using h

/-! ## The composed round

`g1CS_step_round_bridge` (one step) plus `g1CS_index_round_onList` (thirteen
steps).  The bridge is what makes the two compose: it is the only row that turns
the forward `bScan` alignment into the reverse `bWalk` alignment. -/

/-- **Fourteen genuine steps from the bridge boundary.**  On a tape backed by an
arbitrary frame list `pre ++ index :: suffix`, with the head on the first cell of
the frame *after* the `index` and the control in `bRoundStart`, the bridge and
the thirteen-step round replace that `index` by `spent` — nothing else on the
tape changes — and leave the head on the last cell of the frame *before* it, in
the reverse-read entry shape `bWalk .p3`, with the whole `G1Ctx` preserved. -/
theorem g1CS_round_from_bridge (n : Nat) (pre suffix : List G1Frame)
    (ctx : G1Ctx) (hpre : 0 < pre.length)
    (hsafe : 4 * pre.length + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * pre.length + 4) hsafe
          (g1ListTape ((pre ++ G1Frame.index :: suffix).flatMap G1Frame.bits))
          .bRoundStart .p0 false false false ctx) 14 =
      g1AlignedConfig n (4 * pre.length - 1) (by omega)
        (g1ListTape ((pre ++ G1Frame.spent :: suffix).flatMap G1Frame.bits))
        .bWalk .p3 false false false ctx := by
  have hb := g1CS_step_round_bridge n (4 * pre.length + 4) hsafe (by omega)
    (g1ListTape (n := n)
      ((pre ++ G1Frame.index :: suffix).flatMap G1Frame.bits)) ctx
  have hc := g1CS_index_round_onList n pre suffix ctx hpre hsafe
  show TM.runConfig (M := G1M) _ (1 + 13) = _
  rw [runConfig_add, hb]
  simpa [show 4 * pre.length + 4 - 1 = 4 * pre.length + 3 from by omega] using hc

/-- **One destructive index round, from the real initial configuration.**  For a
canonical `and`/`or` request with `arg2 = k + 1`, exactly `g1IndexRoundSteps r`
genuine steps of the one fixed zero-parameter machine turn the initial tape into
the canonical word with the **first** `index` unit of the operand-2 field
replaced by `spent`, leaving the head on the last cell of the `argSep` that
opens that field and the control in the reverse-read entry shape.

This is one round of the destructive walk, executed.  It is *not* an addressing
claim: nothing here says how many rounds the walk needs, that it terminates, or
which data frame the operand finally selects. -/
theorem g1CS_index_first_round (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1IndexRoundSteps r) =
      g1AlignedConfig (encodeG1 r).length (4 * (r.tag.units + r.arg1 + 3) - 1)
        (Nat.lt_of_le_of_lt (Nat.sub_le _ _)
          (g1_route_lt_tapeLength r _ (by omega)))
        (g1ListTape ((g1FieldRouteFrames r ++
          G1Frame.spent :: g1RoundRouteRest r k).flatMap G1Frame.bits))
        .bWalk .p3 false false false g1Ctx0 := by
  have hpre : 0 < (g1FieldRouteFrames r).length := by
    rw [g1FieldRouteFrames_length]; omega
  have hsafe : 4 * (g1FieldRouteFrames r).length + 4 <
      G1M.tapeLength (encodeG1 r).length := by
    have h := g1_route_lt_tapeLength r (r.tag.units + r.arg1 + 4) (by omega)
    rw [g1FieldRouteFrames_length]
    omega
  have hword : g1FieldRouteFrames r ++
      G1Frame.index :: g1RoundRouteRest r k = g1ValidationFrames r := by
    rw [g1ValidationFrames, ← g1RoundRoute_split r k h2, g1RoundRouteFrames]
    simp [g1RoundRouteRest, List.append_assoc]
  have htape : g1ListTape (n := (encodeG1 r).length)
      ((g1FieldRouteFrames r ++
        G1Frame.index :: g1RoundRouteRest r k).flatMap G1Frame.bits) =
      (G1M.initialConfig (g1Point (encodeG1 r))).tape := by
    rw [hword]; exact g1ListTape_validation_eq_initial r
  have hround := g1CS_round_from_bridge (encodeG1 r).length
    (g1FieldRouteFrames r) (g1RoundRouteRest r k) g1Ctx0 hpre hsafe
  rw [htape] at hround
  simp only [g1FieldRouteFrames_length,
    show 4 * (r.tag.units + r.arg1 + 3) + 4 = 4 * (r.tag.units + r.arg1 + 4)
      from by omega] at hround
  rw [g1IndexRoundSteps, runConfig_add,
    g1CS_readB_round_boundary r hc ht k h2, hround]

/-! ## A concrete request

`and` with an empty operand-1 field, one operand-2 index unit and a one-bit data
region.  Every number below is a literal: the encoded word is twelve frames
(`48` cells) and the blank frame the machine's own tape supplies past the input
makes thirteen. -/

/-- The concrete request: `and`, `arg1 = 0`, `arg2 = 1`, one data bit. -/
def g1RoundExample : G1Request := ⟨.and, 0, 1, [true]⟩

/-- The frame word of `g1RoundExample` on the machine's **initial** tape: the
canonical word plus the blank frame the tape supplies past the input. -/
def g1RoundExampleInitFrames : List G1Frame :=
  [.bof, .tag, .tag, .tag, .tag, .argSep, .argSep, .index, .separator,
    .data true, .output false, .finish, .blank]

/-- The frame word of `g1RoundExample` after the first destructive round: the
single `index` unit of the operand-2 field has become `spent`, and nothing else
differs from `g1RoundExampleInitFrames`. -/
def g1RoundExampleFrames : List G1Frame :=
  [.bof, .tag, .tag, .tag, .tag, .argSep, .argSep, .spent, .separator,
    .data true, .output false, .finish, .blank]

theorem g1RoundExample_canonical : g1RoundExample.Canonical := by decide

/-- **The initial tape, as the same thirteen-frame word.**  Together with
`g1CS_round_example_tape` this makes "the round changes exactly the four cells
`28 … 31`" a comparison of two literal frame lists. -/
theorem g1RoundExample_initial_tape :
    (G1M.initialConfig (g1Point (encodeG1 g1RoundExample))).tape =
      g1ListTape (n := (encodeG1 g1RoundExample).length)
        (g1RoundExampleInitFrames.flatMap G1Frame.bits) := by
  rw [← g1ListTape_validation_eq_initial g1RoundExample]
  rfl

private theorem g1RoundExample_length :
    (encodeG1 g1RoundExample).length = 48 := by
  rw [encodeG1_length]; rfl

private theorem g1RoundExample_steps :
    g1IndexRoundSteps g1RoundExample = 151 := by
  simp only [g1IndexRoundSteps, g1RoundBoundarySteps, g1ReadBHandoffSteps,
    g1RoundExample_length]
  rfl

private theorem g1RoundExample_run :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1RoundExample))) 151 =
      g1AlignedConfig (encodeG1 g1RoundExample).length
        (4 * (g1RoundExample.tag.units + g1RoundExample.arg1 + 3) - 1)
        (Nat.lt_of_le_of_lt (Nat.sub_le _ _)
          (g1_route_lt_tapeLength g1RoundExample _ (by omega)))
        (g1ListTape ((g1FieldRouteFrames g1RoundExample ++
          G1Frame.spent :: g1RoundRouteRest g1RoundExample 0).flatMap
          G1Frame.bits))
        .bWalk .p3 false false false g1Ctx0 := by
  rw [← g1RoundExample_steps]
  exact g1CS_index_first_round g1RoundExample g1RoundExample_canonical
    (Or.inl rfl) 0 rfl

/-- **The concrete round: exact head.**  After exactly 151 genuine steps the
head is on cell `27`, the last cell of the `argSep` that opens the operand-2
field. -/
theorem g1CS_round_example_head :
    ((TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1RoundExample)))
        151).head : Nat) = 27 := by
  rw [g1RoundExample_run]; rfl

/-- **The concrete round: exact control state.**  The reverse-read entry shape,
with the whole context still at its initial value. -/
theorem g1CS_round_example_state :
    (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1RoundExample)))
        151).state.snd = g1WalkState g1Ctx0 := by
  rw [g1RoundExample_run]; rfl

/-- **The concrete round: the first operand-2 `index` really became `spent`.**
The whole tape after 151 steps is the thirteen-frame word
`bof · tag⁴ · argSep · argSep · spent · separator · data true · output false ·
finish · blank`; by `g1RoundExample_initial_tape` the initial tape is the same
word with `index` in that seventh frame, so exactly the four cells `28 … 31`
changed. -/
theorem g1CS_round_example_tape :
    (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1RoundExample)))
        151).tape =
      g1ListTape (n := (encodeG1 g1RoundExample).length)
        (g1RoundExampleFrames.flatMap G1Frame.bits) := by
  rw [g1RoundExample_run]
  rfl

/-- The concrete step count is inside the unchanged public clock. -/
theorem g1CS_round_example_clock :
    151 ≤ g1Clock (encodeG1 g1RoundExample).length := by
  rw [← g1RoundExample_steps]
  exact g1IndexRoundSteps_le_clock g1RoundExample

end Pnp3.Internal.PsubsetPpoly.TM
