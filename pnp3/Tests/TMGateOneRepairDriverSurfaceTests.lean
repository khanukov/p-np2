import Complexity.TMVerifier.TuringToolkit.GateOneRepairDriver

/-!
# G1 operand-2 repair driver: surface tests

Theorem-style exact wrappers for **every** public statement of
`GateOneRepairDriver`, the Repair-2a slice: the layout split, the
request-specific sweep and the two composed `initialConfig` capstones.

**What this surface pins.**  The real layout split
`g1BSpentFrames r s = [bof] ++ left ++ spent^s ++ mid ++ tail`, the lengths of
its three runs, the fact that `g1BSpentFrames r 0` is the canonical word plus the
trailing blank, and the repaired word `g1RepairFrames_repaired` — the endpoint is
**literally** the initial word, not merely a word of the same length.  The two
scanned runs are pinned against the **narrowed** `G1RepairSkip` in both
directions (`check_repair_runs_skip`, `check_repair_runs_clean`), and
`check_g1RepairTail_unread` pins that the tail's `blank` is not crossable, that
the scanned region is exactly `g1WalkCursor r arg2 + 1` frames, and that every
tail cell lies strictly right of the sweep's entry cell.  Then the sweep itself
(`4u + 4a1 + 8a + 9s + 22` steps, head to `0`, control `readAStart`, tape the
canonical word, context untouched), the common handoff `g1ReadAConfig r b` with
its four projections, the two cumulative totals inside the **unchanged**
`g1Clock`, both composed `initialConfig` capstones with head/state/`vB`/tape
projections, and the common conditional theorem.

`check_g1CS_readB_positive_oob_unrepaired` pins that the out-of-range boundary is
left exactly as it was: stable for every extra budget, still carrying
`m = vals.length` consumed units, and in a state that is **not** the pass-A
handoff.  No repair and no rejection is claimed for it.

**Absent from this surface**: any pass-A execution, operand-1 read, combine step,
output write, and any `TM.accepts`, verdict, full-clock, gate-semantics,
acceptance-gate, multi-gate, specification-bridge or padded-tape surface.  The
**all-literal** repaired runs from `G1M.initialConfig` are deferred in full to
Repair-2b, so no probe wrapper appears here either.  This is an audit surface:
it pins public signatures and proves nothing new.
-/

namespace Pnp3.Tests.TMGateOneRepairDriverSurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM

/-! ## The real layout, split for the sweep -/

/-- The three runs, and their lengths. -/
theorem check_repair_run_lengths (r : G1Request) (s : Nat)
    (hm : r.arg2 < r.vals.length) :
    (g1RepairLeft r s).length = r.tag.units + r.arg1 + (r.arg2 - s) + 2 ∧
      (g1RepairMid r).length = r.arg2 + 2 ∧
      (g1RepairTail r).length = r.vals.length - (r.arg2 + 1) + 3 :=
  ⟨g1RepairLeft_length r s, g1RepairMid_length r hm, g1RepairTail_length r⟩

/-- **The read's terminal tape, split for the sweep**, and its `s = 0` value:
the canonical encoded word plus the trailing blank frame. -/
theorem check_g1BSpentFrames_repair_split (r : G1Request) (s : Nat) :
    g1BSpentFrames r s =
        [G1Frame.bof] ++ g1RepairLeft r s ++ List.replicate s G1Frame.spent ++
          g1RepairMid r ++ g1RepairTail r ∧
      g1BSpentFrames r 0 = encodeG1Frames r ++ [G1Frame.blank] :=
  ⟨g1BSpentFrames_repair_split r s, g1BSpentFrames_zero r⟩

/-- **Both scanned runs satisfy the narrowed `G1RepairSkip`.**  These are the
hypotheses `g1CS_repair_pass_exact` consumes. -/
theorem check_repair_runs_skip (r : G1Request) (s : Nat) :
    (∀ f ∈ g1RepairLeft r s, G1RepairSkip f) ∧
      (∀ f ∈ g1RepairMid r, G1RepairSkip f) :=
  ⟨g1RepairLeft_skip r s, g1RepairMid_skip r⟩

/-- **The rejection outcome is respected, not dodged.**  `blank`, `cursor`,
`bof` and `spent` are not crossable, and neither scanned run contains a `blank`
or a leftover `cursor`. -/
theorem check_repair_runs_clean (r : G1Request) (s : Nat) :
    (¬ G1RepairSkip G1Frame.blank ∧ ¬ G1RepairSkip G1Frame.cursor ∧
        ¬ G1RepairSkip G1Frame.bof ∧ ¬ G1RepairSkip G1Frame.spent) ∧
      (G1Frame.blank ∉ g1RepairLeft r s ∧
        G1Frame.cursor ∉ g1RepairLeft r s) ∧
      (G1Frame.blank ∉ g1RepairMid r ∧ G1Frame.cursor ∉ g1RepairMid r) :=
  ⟨g1Repair_not_skip, g1RepairLeft_clean r s, g1RepairMid_clean r⟩

/-- **The tail contains a `blank`, and is never scanned.**  The scanned region is
exactly `g1WalkCursor r arg2 + 1` frames, the sweep enters on its last cell, and
every tail cell lies strictly to the right. -/
theorem check_g1RepairTail_unread (r : G1Request) (s : Nat) (hs : s ≤ r.arg2)
    (hm : r.arg2 < r.vals.length) :
    G1Frame.blank ∈ g1RepairTail r ∧ ¬ G1RepairSkip G1Frame.blank ∧
      1 + (g1RepairLeft r s).length + s + (g1RepairMid r).length =
        g1WalkCursor r r.arg2 + 1 ∧
      ∀ i, i < 4 * (g1RepairTail r).length →
        4 * (g1WalkCursor r r.arg2 + 1) - 1 <
          4 * (g1WalkCursor r r.arg2 + 1) + i :=
  g1RepairTail_unread r s hs hm

/-- **Repairing the units restores the field, and the repaired word is the
canonical one.**  Not one consumed unit remains. -/
theorem check_g1RepairFrames_repaired (r : G1Request) (s : Nat)
    (hs : s ≤ r.arg2) :
    g1RepairLeft r s ++ List.replicate s G1Frame.index = g1RepairLeft r 0 ∧
      [G1Frame.bof] ++ g1RepairLeft r s ++ List.replicate s G1Frame.index ++
          g1RepairMid r ++ g1RepairTail r =
        encodeG1Frames r ++ [G1Frame.blank] :=
  ⟨g1RepairLeft_append r s hs, g1RepairFrames_repaired r s hs⟩

/-! ## The sweep at the real layout -/

/-- The closed sweep cost and its decomposition into the bridge and the generic
repair pass: every summand is provenance, not padding. -/
theorem check_g1RepairSteps_eq (r : G1Request) (s : Nat) (hs : s ≤ r.arg2)
    (hm : r.arg2 < r.vals.length) :
    g1RepairSteps r s =
        4 * r.tag.units + 4 * r.arg1 + 8 * r.arg2 + 9 * s + 22 ∧
      g1RepairSteps r s =
        1 + g1RepairPassSteps (g1RepairLeft r s).length s
          (g1RepairMid r).length :=
  ⟨rfl, g1RepairSteps_eq r s hs hm⟩

/-- **The operand-2 repair pass at the real layout.**  From the post-read
`readAResetStart` boundary at its exact head, `4u + 4a1 + 8a + 9s + 22` genuine
steps repair all `s` consumed units, finish on head `0` in `readAStart`, leave
the tape exactly `encodeG1Frames r ++ [blank]` and leave the carried context
untouched. -/
theorem check_g1CS_repair_sweep_exact (r : G1Request) (s : Nat)
    (hs : s ≤ r.arg2) (hm : r.arg2 < r.vals.length) (ctx : G1Ctx) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig (encodeG1 r).length (4 * (g1WalkCursor r r.arg2 + 1))
          (by have := g1WalkCursor_safe r r.arg2 (Nat.le_refl _) hm; omega)
          (g1ListTape ((g1BSpentFrames r s).flatMap G1Frame.bits))
          .readAResetStart .p0 false false false ctx)
        (g1RepairSteps r s) =
      g1AlignedConfig (encodeG1 r).length 0
        (by have := g1WalkCursor_safe r r.arg2 (Nat.le_refl _) hm; omega)
        (g1ListTape ((encodeG1Frames r ++ [G1Frame.blank]).flatMap G1Frame.bits))
        .readAStart .p0 false false false ctx :=
  g1CS_repair_sweep_exact r s hs hm ctx

/-! ## The common pass-A handoff -/

/-- The four projections of the canonical handoff: head `0`, control
`readAStart`, `vB = b`, tape the canonical word plus the trailing blank frame. -/
theorem check_g1ReadAConfig (r : G1Request) (b : Bool) :
    ((g1ReadAConfig r b).head : Nat) = 0 ∧
      (g1ReadAConfig r b).state.snd = g1ReadAState (g1Ctx0.withVB b) ∧
      (g1ReadAConfig r b).state.snd.ctx.vB = b ∧
      (g1ReadAConfig r b).tape =
        g1ListTape ((encodeG1Frames r ++ [G1Frame.blank]).flatMap
          G1Frame.bits) :=
  ⟨g1ReadAConfig_head r b, g1ReadAConfig_state r b, g1ReadAConfig_vB r b,
    g1ReadAConfig_tape r b⟩

/-- **The handoff's tape is literally the machine's initial tape.** -/
theorem check_g1ReadAConfig_tape_initial (r : G1Request) (b : Bool) :
    (g1ReadAConfig r b).tape =
      (G1M.initialConfig (g1Point (encodeG1 r))).tape := rfl

/-- The repaired endpoint of the sweep **is** the canonical pass-A handoff. -/
theorem check_g1CS_repair_sweep_readAConfig (r : G1Request) (s : Nat)
    (hs : s ≤ r.arg2) (hm : r.arg2 < r.vals.length) (b : Bool) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig (encodeG1 r).length (4 * (g1WalkCursor r r.arg2 + 1))
          (by have := g1WalkCursor_safe r r.arg2 (Nat.le_refl _) hm; omega)
          (g1ListTape ((g1BSpentFrames r s).flatMap G1Frame.bits))
          .readAResetStart .p0 false false false (g1Ctx0.withVB b))
        (g1RepairSteps r s) = g1ReadAConfig r b :=
  g1CS_repair_sweep_readAConfig r s hs hm b

/-! ## The two cumulative totals, inside the unchanged clock -/

theorem check_passASteps_eq (r : G1Request) :
    g1BPassASteps r = g1BReadSteps r + g1RepairSteps r r.arg2 ∧
      g1ZPassASteps r = g1ReadBSteps r + g1RepairSteps r 0 ∧
      g1BPassASteps r =
        g1InstallScanSteps r +
          (8 * r.arg2 ^ 2 + 62 * r.arg2 + 4 * r.tag.units + 4 * r.arg1 + 59) :=
  ⟨rfl, rfl, g1BPassASteps_eq r⟩

theorem check_zPassASteps_eq (r : G1Request) (h2 : r.arg2 = 0) :
    g1ZPassASteps r =
      g1ReadBHandoffSteps r + (8 * r.tag.units + 8 * r.arg1 + 43) :=
  g1ZPassASteps_eq r h2

/-- **Both totals fit the unchanged public clock**, unconditionally: no
hypothesis on the request at all, and `g1Clock` is not widened. -/
theorem check_passASteps_le_clock (r : G1Request) :
    g1BPassASteps r ≤ g1Clock (encodeG1 r).length ∧
      g1ZPassASteps r ≤ g1Clock (encodeG1 r).length ∧
      (if r.arg2 = 0 then g1ZPassASteps r else g1BPassASteps r) ≤
        g1Clock (encodeG1 r).length :=
  ⟨g1BPassASteps_le_clock r, g1ZPassASteps_le_clock r,
    g1CS_readB_repaired_common_le_clock r⟩

/-! ## The two composed capstones from the real initial configuration -/

/-- **The positive-index read, repaired.**  The bit `b` is the pure selector
`r.vals[r.arg2]`, resolved physically; the endpoint is the canonical handoff. -/
theorem check_g1CS_readB_positive_repaired_exact (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .and ∨ r.tag = .or) (h2 : 0 < r.arg2)
    (b : Bool) (hb : r.vals[r.arg2]? = some b) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BPassASteps r) = g1ReadAConfig r b :=
  g1CS_readB_positive_repaired_exact r hc ht h2 b hb

/-- Head `0`, control `readAStart`, `vB` the actual `vals[arg2]`, and the tape
back to the canonical word — bit-for-bit the initial tape. -/
theorem check_g1CS_readB_positive_repaired_projections (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .and ∨ r.tag = .or) (h2 : 0 < r.arg2)
    (b : Bool) (hb : r.vals[r.arg2]? = some b) :
    ((TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1BPassASteps r)).head : Nat) = 0 ∧
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1BPassASteps r)).state.snd = g1ReadAState (g1Ctx0.withVB b) ∧
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1BPassASteps r)).state.snd.ctx.vB = b ∧
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1BPassASteps r)).tape =
        g1ListTape ((encodeG1Frames r ++ [G1Frame.blank]).flatMap
          G1Frame.bits) ∧
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1BPassASteps r)).tape =
        (G1M.initialConfig (g1Point (encodeG1 r))).tape :=
  ⟨g1CS_readB_positive_repaired_head r hc ht h2 b hb,
    g1CS_readB_positive_repaired_state r hc ht h2 b hb,
    g1CS_readB_positive_repaired_vB r hc ht h2 b hb,
    g1CS_readB_positive_repaired_tape r hc ht h2 b hb,
    g1CS_readB_positive_repaired_tape_initial r hc ht h2 b hb⟩

/-- **The zero-index read, repaired.**  At `arg2 = 0` nothing was consumed, so
the sweep writes nothing: it is a pure rewind to the same canonical handoff. -/
theorem check_g1CS_readB_zero_repaired_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : r.arg2 = 0) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ZPassASteps r) = g1ReadAConfig r b :=
  g1CS_readB_zero_repaired_exact r hc ht h2 b hb

theorem check_g1CS_readB_zero_repaired_projections (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .and ∨ r.tag = .or) (h2 : r.arg2 = 0)
    (b : Bool) (hb : r.vals[r.arg2]? = some b) :
    ((TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1ZPassASteps r)).head : Nat) = 0 ∧
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1ZPassASteps r)).state.snd = g1ReadAState (g1Ctx0.withVB b) ∧
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1ZPassASteps r)).state.snd.ctx.vB = b ∧
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1ZPassASteps r)).tape =
        (G1M.initialConfig (g1Point (encodeG1 r))).tape :=
  ⟨g1CS_readB_zero_repaired_head r hc ht h2 b hb,
    g1CS_readB_zero_repaired_state r hc ht h2 b hb,
    g1CS_readB_zero_repaired_vB r hc ht h2 b hb,
    g1CS_readB_zero_repaired_tape r hc ht h2 b hb⟩

/-- **The two branches meet.**  One conditional count, one endpoint; the
condition is on the request, not on the machine. -/
theorem check_g1CS_readB_repaired_common (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (if r.arg2 = 0 then g1ZPassASteps r else g1BPassASteps r) =
      g1ReadAConfig r b :=
  g1CS_readB_repaired_common r hc ht b hb

/-! ## The out-of-range boundary is untouched -/

/-- **`bOOB` is still stable, still unrepaired, and still not the handoff.**  No
repair and no rejection is claimed for it anywhere in this slice. -/
theorem check_g1CS_readB_positive_oob_unrepaired (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .and ∨ r.tag = .or) (h2 : 0 < r.arg2)
    (hm : r.vals.length ≤ r.arg2) (k : Nat) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1BOOBSteps r + k) =
        g1AlignedConfig (encodeG1 r).length
          (4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 5))
          (g1_route_lt_tapeLength r _ (by omega))
          (g1ListTape ((g1BSpentFrames r r.vals.length).flatMap G1Frame.bits))
          .bOOB .p0 false false false (g1BOOBCtx r) ∧
      (g1BSpentFrames r r.vals.length).count G1Frame.spent = r.vals.length ∧
      ∀ ctx : G1Ctx, g1ReadAState ctx ≠ g1OOBState (g1BOOBCtx r) :=
  g1CS_readB_positive_oob_unrepaired r hc ht h2 hm k

theorem check_g1ReadAState_ne_oob (ctx ctx' : G1Ctx) :
    g1ReadAState ctx ≠ g1OOBState ctx' :=
  g1ReadAState_ne_oob ctx ctx'

end Pnp3.Tests.TMGateOneRepairDriverSurface
