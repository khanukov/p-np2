import Complexity.TMVerifier.TuringToolkit.GateOneRepairKernel

/-!
# G1 operand-2 repair sweep: the real layout, and the common pass-A handoff

**Progress classification: Infrastructure.**

The Repair-2a slice.  `GateOneRepairKernel` proves the `spent ↦ index` pass on an
**arbitrary** frame list; this module instantiates it at the **real** operand-2
layout `g1BSpentFrames r s` and composes it behind both successful operand-2
reads, so that the two of them meet in **one** canonical pass-A handoff.

Throughout, `u = r.tag.units`, `a1 = r.arg1`, `a = r.arg2`, `m = r.vals.length`.

## The layout, split for the sweep

`g1BSpentFrames_repair_split` writes the read's terminal tape as
`[bof] ++ g1RepairLeft r s ++ spent^s ++ g1RepairMid r ++ g1RepairTail r`, with
`g1RepairLeft r s = tag^u · argSep · index^a1 · argSep · index^(a-s)` the run
between the anchor and the consumed units, `g1RepairMid r = separator ·
data^(a+1)` the run the scan crosses on its way in, and `g1RepairTail r` the
rest.

**The two scanned runs are clean under the narrowed predicate.**  Repair-1
narrowed `G1RepairSkip` so that `blank`, `bof`, `cursor` and `spent` are *not*
crossable.  `g1RepairLeft_skip`/`g1RepairMid_skip` discharge the kernel's
`hleft`/`hmid` against that narrowing, and `g1RepairLeft_clean`/
`g1RepairMid_clean` record the same fact in the contrapositive form: neither run
contains a `blank` or a leftover `cursor`.  `g1RepairTail` **does** contain a
`blank` — the trailing frame the machine's own tape supplies past the input —
and `g1RepairTail_unread` shows why that is harmless: the tail begins exactly at
the sweep's entry cell `4 * (g1WalkCursor r a + 1)`, one cell to the right of the
first cell the scan reads, so it is passed as the kernel's **unconstrained**
`tail`, never read, and reproduced bit-for-bit.

## The sweep at the real layout

`g1CS_repair_sweep_exact` is the repair-pass theorem: from the post-B
`readAResetStart` boundary **at its exact head** `4 * (g1WalkCursor r a + 1)` on
`g1BSpentFrames r s` with `s ≤ a` and `a < m`, exactly
`g1RepairSteps r s = 4u + 4a1 + 8a + 9s + 22` genuine steps repair all `s`
consumed units and finish on head `0` in `readAStart`, with the tape **exactly**
`encodeG1Frames r ++ [blank]` — the canonical encoded word plus the trailing
blank frame, which is bit-for-bit the machine's initial tape — and the carried
`G1Ctx` unchanged, so the latched operand-2 value survives.  The decomposition
is `1 + g1RepairPassSteps (u + a1 + (a-s) + 2) s (a + 2)`: the bridge, `4` per
skipped frame, `13` per consumed unit, and the anchor read plus dispatch.  Every
summand is a concrete polynomial in the request's own fields — no pad, no
advice, no free budget parameter.

## The two composed capstones

`g1CS_readB_positive_repaired_exact` is `g1CS_readB_positive_exact` (at `s = a`)
plus the sweep, in `g1BPassASteps r = g1BReadSteps r + g1RepairSteps r a` steps;
`g1CS_readB_zero_repaired_exact` is `g1CS_readB_zero_exact` (at `s = 0`, where
the sweep is a pure rewind: nothing was consumed, so **nothing is written**) plus
the sweep, in `g1ZPassASteps r = g1ReadBSteps r + g1RepairSteps r 0` steps.  Both
end in the **same** `g1ReadAConfig r b`, whose tape is literally
`(G1M.initialConfig (g1Point (encodeG1 r))).tape`, and both totals fit the
**unchanged** `g1Clock`.  `g1CS_readB_repaired_common` states the meeting point
once.  The value `b` is the **actual** `r.vals[r.arg2]`, resolved physically out
of the unannotated data region.

## Explicit deferrals

`readAStart` is still idle (`g1CS_runConfig_readA_idle`): **operand 1 is not
read**, and nothing here claims it is.  Also absent and claimed nowhere: the
combine step, the output write, `TM.accepts`, a full-clock theorem, the
gate-semantics correctness statement, the acceptance gate, multi-gate
composition and the specification-level bridge.  The out-of-range boundary
`bOOB` is left exactly as `GateOneWalkDriver` leaves it — stable, unrepaired
and **not** a rejection theorem; `g1CS_readB_positive_oob_unrepaired` below only
records that it is still unrepaired and is a different state from the pass-A
handoff.  Every execution statement is scoped to the exact tape `encodeG1 r`.

The **all-literal** repaired runs — concrete requests, concrete step counts,
concrete endpoint words — are deferred in full to **Repair-2b**: this slice
ships no example module, and every statement below is quantified over the
caller's request.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

/-! ## The layout, split for the sweep -/

/-- The run between the anchor and the consumed units: the tag run, both
`argSep`s, the operand-1 field and the operand-2 units not yet consumed. -/
def g1RepairLeft (r : G1Request) (s : Nat) : List G1Frame :=
  List.replicate r.tag.units G1Frame.tag ++ G1Frame.argSep ::
    (List.replicate r.arg1 G1Frame.index ++ G1Frame.argSep ::
      List.replicate (r.arg2 - s) G1Frame.index)

/-- The run the repair scan crosses on its way in: the `separator` and the
`arg2 + 1` data frames the cursor walk has already restored. -/
def g1RepairMid (r : G1Request) : List G1Frame :=
  G1Frame.separator :: (r.vals.map G1Frame.data).take (r.arg2 + 1)

/-- Everything to the right of the sweep's entry head: the rest of the data
region, the `output` destination, the terminator and the trailing `blank`. -/
def g1RepairTail (r : G1Request) : List G1Frame :=
  (r.vals.map G1Frame.data).drop (r.arg2 + 1) ++
    [G1Frame.output false, G1Frame.finish, G1Frame.blank]

@[simp] theorem g1RepairLeft_length (r : G1Request) (s : Nat) :
    (g1RepairLeft r s).length = r.tag.units + r.arg1 + (r.arg2 - s) + 2 := by
  simp only [g1RepairLeft, List.length_append, List.length_cons,
    List.length_replicate]
  omega

theorem g1RepairMid_length (r : G1Request) (hm : r.arg2 < r.vals.length) :
    (g1RepairMid r).length = r.arg2 + 2 := by
  simp only [g1RepairMid, List.length_cons, List.length_take, List.length_map]
  omega

theorem g1RepairTail_length (r : G1Request) :
    (g1RepairTail r).length = r.vals.length - (r.arg2 + 1) + 3 := by
  simp only [g1RepairTail, List.length_append, List.length_drop,
    List.length_map, List.length_cons, List.length_nil]

/-- **At `s = 0` the layout family is the initial word.**  `g1BSpentFrames r 0`
is literally `encodeG1Frames r ++ [blank]`: nothing has been written.  This
generalises `g1BSpentFrames_empty`, which needs an empty data region. -/
theorem g1BSpentFrames_zero (r : G1Request) :
    g1BSpentFrames r 0 = encodeG1Frames r ++ [G1Frame.blank] := by
  simp only [g1BSpentFrames, encodeG1Frames, g1FieldRouteFrames, Nat.sub_zero,
    List.replicate_zero, List.append_nil]
  simp [List.append_assoc]

/-- **The read's terminal tape, split for the sweep.** -/
theorem g1BSpentFrames_repair_split (r : G1Request) (s : Nat) :
    g1BSpentFrames r s =
      [G1Frame.bof] ++ g1RepairLeft r s ++ List.replicate s G1Frame.spent ++
        g1RepairMid r ++ g1RepairTail r := by
  have hd : r.vals.map G1Frame.data ++
        [G1Frame.output false, G1Frame.finish, G1Frame.blank] =
      (r.vals.map G1Frame.data).take (r.arg2 + 1) ++
        ((r.vals.map G1Frame.data).drop (r.arg2 + 1) ++
          [G1Frame.output false, G1Frame.finish, G1Frame.blank]) := by
    rw [← List.append_assoc, List.take_append_drop]
  simp only [g1BSpentFrames, g1FieldRouteFrames, g1RepairLeft, g1RepairMid,
    g1RepairTail, List.append_assoc, List.cons_append, List.nil_append, hd]

/-- Every frame of the left run is crossable by the repair scan, under the
**narrowed** `G1RepairSkip`. -/
theorem g1RepairLeft_skip (r : G1Request) (s : Nat) :
    ∀ f ∈ g1RepairLeft r s, G1RepairSkip f := by
  intro f hf
  simp only [g1RepairLeft, List.mem_append, List.mem_cons, List.mem_replicate]
    at hf
  rcases hf with ⟨-, rfl⟩ | rfl | ⟨-, rfl⟩ | rfl | ⟨-, rfl⟩ <;> trivial

/-- Every frame of the middle run is crossable by the repair scan. -/
theorem g1RepairMid_skip (r : G1Request) :
    ∀ f ∈ g1RepairMid r, G1RepairSkip f := by
  intro f hf
  rcases List.mem_cons.1 hf with rfl | hf'
  · trivial
  · obtain ⟨v, -, hv⟩ := List.mem_map.1 (List.mem_of_mem_take hf')
    rw [← hv]; trivial

/-- **The four non-crossable frame kinds.**  `blank`, `bof`, `cursor` and
`spent` are not `G1RepairSkip`, so a scanned run that contained one of them
could not discharge the kernel's hypotheses. -/
theorem g1Repair_not_skip :
    ¬ G1RepairSkip G1Frame.blank ∧ ¬ G1RepairSkip G1Frame.cursor ∧
      ¬ G1RepairSkip G1Frame.bof ∧ ¬ G1RepairSkip G1Frame.spent := by decide

/-- **The left run is clean**: no `blank`, no leftover `cursor`.  The
contrapositive reading of `g1RepairLeft_skip`. -/
theorem g1RepairLeft_clean (r : G1Request) (s : Nat) :
    G1Frame.blank ∉ g1RepairLeft r s ∧ G1Frame.cursor ∉ g1RepairLeft r s :=
  ⟨fun h => g1Repair_not_skip.1 (g1RepairLeft_skip r s _ h),
    fun h => g1Repair_not_skip.2.1 (g1RepairLeft_skip r s _ h)⟩

/-- **The middle run is clean**: no `blank`, no leftover `cursor`. -/
theorem g1RepairMid_clean (r : G1Request) :
    G1Frame.blank ∉ g1RepairMid r ∧ G1Frame.cursor ∉ g1RepairMid r :=
  ⟨fun h => g1Repair_not_skip.1 (g1RepairMid_skip r _ h),
    fun h => g1Repair_not_skip.2.1 (g1RepairMid_skip r _ h)⟩

/-- **The tail does contain a `blank`, and is never scanned.**  The trailing
frame is not crossable, so if the sweep read it the pass would reject; it does
not.  The scanned region is exactly the `g1WalkCursor r arg2 + 1` frames
`[bof] ++ left ++ spent^s ++ mid`, the sweep enters on that region's **last**
cell `4 * (g1WalkCursor r arg2 + 1) - 1`, and every tail cell
`4 * (g1WalkCursor r arg2 + 1) + i` lies strictly to its right.  That is why the
tail is handed to `g1CS_repair_pass_exact` as its unconstrained argument and
comes out bit-for-bit. -/
theorem g1RepairTail_unread (r : G1Request) (s : Nat) (hs : s ≤ r.arg2)
    (hm : r.arg2 < r.vals.length) :
    G1Frame.blank ∈ g1RepairTail r ∧ ¬ G1RepairSkip G1Frame.blank ∧
      1 + (g1RepairLeft r s).length + s + (g1RepairMid r).length =
        g1WalkCursor r r.arg2 + 1 ∧
      ∀ i, 4 * (g1WalkCursor r r.arg2 + 1) - 1 <
        4 * (g1WalkCursor r r.arg2 + 1) + i := by
  refine ⟨by simp [g1RepairTail], g1Repair_not_skip.1, ?_, ?_⟩
  · rw [g1RepairLeft_length, g1RepairMid_length r hm, g1WalkCursor]
    omega
  · intro i
    simp only [g1WalkCursor]
    omega

/-- Repairing the consumed units restores the full operand-2 field. -/
theorem g1RepairLeft_append (r : G1Request) (s : Nat) (hs : s ≤ r.arg2) :
    g1RepairLeft r s ++ List.replicate s G1Frame.index = g1RepairLeft r 0 := by
  simp only [g1RepairLeft, Nat.sub_zero, List.append_assoc, List.cons_append,
    ← List.replicate_add]
  rw [show r.arg2 - s + s = r.arg2 from by omega]

/-- **The repaired tape is the canonical word plus the trailing blank frame.**
Not one consumed unit remains and nothing else was touched — the endpoint word is
*literally* the machine's initial word, not merely a word of the same length. -/
theorem g1RepairFrames_repaired (r : G1Request) (s : Nat) (hs : s ≤ r.arg2) :
    [G1Frame.bof] ++ g1RepairLeft r s ++ List.replicate s G1Frame.index ++
        g1RepairMid r ++ g1RepairTail r =
      encodeG1Frames r ++ [G1Frame.blank] := by
  rw [← g1BSpentFrames_zero r, g1BSpentFrames_repair_split r 0,
    show [G1Frame.bof] ++ g1RepairLeft r s ++ List.replicate s G1Frame.index =
        [G1Frame.bof] ++ g1RepairLeft r 0 from by
      rw [List.append_assoc, g1RepairLeft_append r s hs]]
  simp

/-! ## The repair sweep at the real layout -/

/-- **The exact cost of the repair sweep** from the post-B `readAResetStart`
boundary: the one-step bridge, `4` steps per frame of the two skipped runs, `13`
per consumed unit, and the anchor read plus the terminal dispatch. -/
def g1RepairSteps (r : G1Request) (s : Nat) : Nat :=
  4 * r.tag.units + 4 * r.arg1 + 8 * r.arg2 + 9 * s + 22

/-- **The decomposition of the sweep's cost** into the bridge and the generic
repair pass at this layout: `1 + (4 * (a + 2) + 13 * s + 4 * (u + a1 +
(a - s) + 2) + 5)`.  Every summand is provenance, not padding. -/
theorem g1RepairSteps_eq (r : G1Request) (s : Nat) (hs : s ≤ r.arg2)
    (hm : r.arg2 < r.vals.length) :
    g1RepairSteps r s =
      1 + g1RepairPassSteps (g1RepairLeft r s).length s
        (g1RepairMid r).length := by
  rw [g1RepairPassSteps, g1RepairLeft_length, g1RepairMid_length r hm,
    g1RepairSteps]
  omega

private theorem g1RAligned_congr (n h h' : Nat)
    (hh : h < G1M.tapeLength n) (hh' : h' < G1M.tapeLength n) (heq : h = h')
    (tape tape' : Fin (G1M.tapeLength n) → Bool) (hteq : tape = tape')
    (mode : G1Mode) (position : G1FramePosition) (b0 b1 b2 : Bool)
    (ctx : G1Ctx) :
    g1AlignedConfig n h hh tape mode position b0 b1 b2 ctx =
      g1AlignedConfig n h' hh' tape' mode position b0 b1 b2 ctx := by
  subst heq; subst hteq; rfl

/-- **The operand-2 repair pass.**  For a layout `g1BSpentFrames r s` with
`s ≤ arg2` consumed units and `arg2 < vals.length`, starting from the post-B
`readAResetStart` boundary **at its exact head** `4 * (g1WalkCursor r arg2 + 1)`,
exactly `g1RepairSteps r s = 4u + 4a1 + 8a + 9s + 22` genuine steps repair **all
`s`** consumed units back to `index`, finish on head `0` in the pass-A handoff
`readAStart`, leave the tape **exactly** `encodeG1Frames r ++ [blank]` — the
canonical encoded word plus the trailing blank frame — and leave the carried
context `ctx` **unchanged**, so a latched `G1Ctx.vB` survives the sweep
untouched.  The five phases are the bridge (`1`), the middle skip
(`4 * (a + 2)`), the repair iteration (`13 * s`), the left skip
(`4 * (u + a1 + (a - s) + 2)`) and the anchor read plus dispatch (`5`).

The two skipped runs satisfy the **narrowed** `G1RepairSkip`
(`g1RepairLeft_skip`, `g1RepairMid_skip`); the trailing `blank` sits in the
unconstrained tail and is never read (`g1RepairTail_unread`). -/
theorem g1CS_repair_sweep_exact (r : G1Request) (s : Nat) (hs : s ≤ r.arg2)
    (hm : r.arg2 < r.vals.length) (ctx : G1Ctx) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig (encodeG1 r).length (4 * (g1WalkCursor r r.arg2 + 1))
          (by have := g1WalkCursor_safe r r.arg2 (Nat.le_refl _) hm; omega)
          (g1ListTape ((g1BSpentFrames r s).flatMap G1Frame.bits))
          .readAResetStart .p0 false false false ctx)
        (g1RepairSteps r s) =
      g1AlignedConfig (encodeG1 r).length 0
        (by have := g1WalkCursor_safe r r.arg2 (Nat.le_refl _) hm; omega)
        (g1ListTape ((encodeG1Frames r ++ [G1Frame.blank]).flatMap G1Frame.bits))
        .readAStart .p0 false false false ctx := by
  have hTL := g1WalkCursor_safe r r.arg2 (Nat.le_refl _) hm
  have hcursor : 1 + (g1RepairLeft r s).length + s + (g1RepairMid r).length =
      g1WalkCursor r r.arg2 + 1 := by
    rw [g1RepairLeft_length, g1RepairMid_length r hm, g1WalkCursor]
    omega
  have hbridge := g1CS_step_readAReset_bridge (encodeG1 r).length
    (4 * (g1WalkCursor r r.arg2 + 1)) (by omega) (by omega)
    (g1ListTape (n := (encodeG1 r).length)
      ((g1BSpentFrames r s).flatMap G1Frame.bits)) ctx
  have hpass := g1CS_repair_pass_exact (encodeG1 r).length s
    (g1RepairLeft r s) (g1RepairMid r) (g1RepairTail r) ctx
    (g1RepairLeft_skip r s) (g1RepairMid_skip r) (by rw [hcursor]; omega)
  rw [← g1BSpentFrames_repair_split r s, g1RepairFrames_repaired r s hs] at hpass
  simp only [hcursor] at hpass
  rw [g1RepairSteps_eq r s hs hm, runConfig_add, hbridge, hpass]

/-! ## The common pass-A handoff -/

/-- **The canonical pass-A handoff.**  Head `0`, control `readAStart` with an
empty frame buffer, the tape **bit-for-bit the initial tape**, and the resolved
operand-2 value in `G1Ctx.vB`. -/
def g1ReadAConfig (r : G1Request) (b : Bool) :
    Configuration (M := G1M) (encodeG1 r).length :=
  g1AlignedConfig (encodeG1 r).length 0 (g1_route_lt_tapeLength r 0 (by omega))
    (G1M.initialConfig (g1Point (encodeG1 r))).tape
    .readAStart .p0 false false false (g1Ctx0.withVB b)

/-- **The restored tape is the canonical encoded word plus the blank frame.** -/
theorem g1ReadAConfig_tape (r : G1Request) (b : Bool) :
    (g1ReadAConfig r b).tape =
      g1ListTape ((encodeG1Frames r ++ [G1Frame.blank]).flatMap
        G1Frame.bits) := by
  show (G1M.initialConfig (g1Point (encodeG1 r))).tape = _
  rw [← g1ListTape_validation_eq_initial r]
  rfl

@[simp] theorem g1ReadAConfig_head (r : G1Request) (b : Bool) :
    ((g1ReadAConfig r b).head : Nat) = 0 := rfl

@[simp] theorem g1ReadAConfig_state (r : G1Request) (b : Bool) :
    (g1ReadAConfig r b).state.snd = g1ReadAState (g1Ctx0.withVB b) := rfl

@[simp] theorem g1ReadAConfig_vB (r : G1Request) (b : Bool) :
    (g1ReadAConfig r b).state.snd.ctx.vB = b := rfl

/-- The repaired endpoint of the sweep **is** the canonical pass-A handoff. -/
theorem g1CS_repair_sweep_readAConfig (r : G1Request) (s : Nat) (hs : s ≤ r.arg2)
    (hm : r.arg2 < r.vals.length) (b : Bool) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig (encodeG1 r).length (4 * (g1WalkCursor r r.arg2 + 1))
          (by have := g1WalkCursor_safe r r.arg2 (Nat.le_refl _) hm; omega)
          (g1ListTape ((g1BSpentFrames r s).flatMap G1Frame.bits))
          .readAResetStart .p0 false false false (g1Ctx0.withVB b))
        (g1RepairSteps r s) = g1ReadAConfig r b := by
  rw [g1CS_repair_sweep_exact r s hs hm (g1Ctx0.withVB b)]
  refine g1RAligned_congr _ _ _ _ _ rfl _ _ ?_ _ _ _ _ _ _
  show g1ListTape (n := (encodeG1 r).length)
      ((g1ValidationFrames r).flatMap G1Frame.bits) = _
  exact g1ListTape_validation_eq_initial r

/-! ## The two cumulative totals, and the unchanged clock -/

/-- Steps from `initialConfig` to the canonical pass-A handoff of a **positive**
operand-2 index: the read plus the repair sweep of its `arg2` consumed units. -/
def g1BPassASteps (r : G1Request) : Nat :=
  g1BReadSteps r + g1RepairSteps r r.arg2

/-- Steps from `initialConfig` to the canonical pass-A handoff of a **zero**
operand-2 index: the non-destructive read plus a sweep with nothing to
repair. -/
def g1ZPassASteps (r : G1Request) : Nat :=
  g1ReadBSteps r + g1RepairSteps r 0

theorem g1BPassASteps_eq (r : G1Request) :
    g1BPassASteps r =
      g1InstallScanSteps r +
        (8 * r.arg2 ^ 2 + 62 * r.arg2 + 4 * r.tag.units + 4 * r.arg1 + 59) := by
  simp only [g1BPassASteps, g1BReadSteps, g1RepairSteps]
  omega

theorem g1ZPassASteps_eq (r : G1Request) (h2 : r.arg2 = 0) :
    g1ZPassASteps r =
      g1ReadBHandoffSteps r + (8 * r.tag.units + 8 * r.arg1 + 43) := by
  simp only [g1ZPassASteps, g1ReadBSteps, g1RepairSteps, h2]
  omega

private theorem g1RSq_succ (k : Nat) : (k + 1) ^ 2 = k ^ 2 + (2 * k + 1) := by
  rw [Nat.pow_two, Nat.pow_two, Nat.mul_add, Nat.add_mul, Nat.add_mul]
  omega

private theorem g1RClock_quad (N : Nat) :
    g1Clock (4 * N) = 8192 * N ^ 2 + (4096 * N + 1024) := by
  rw [g1Clock, g1RSq_succ, Nat.mul_pow, show (4 : Nat) ^ 2 = 16 from rfl]
  omega

/-- The public clock of a canonical word, in arithmetic normal form.  `g1Clock`
itself is **not** widened anywhere in this slice. -/
private theorem g1RClock_eq (r : G1Request) :
    g1Clock (encodeG1 r).length =
      8192 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 6) ^ 2 +
        (4096 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 6) + 1024) := by
  rw [encodeG1_length r, g1RClock_quad]

/-- **The repaired positive-index total fits the unchanged public clock**, with
no hypothesis at all on the request. -/
theorem g1BPassASteps_le_clock (r : G1Request) :
    g1BPassASteps r ≤ g1Clock (encodeG1 r).length := by
  have hlen : (encodeG1 r).length =
      4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 6) :=
    encodeG1_length r
  have hsq : 8 * r.arg2 ^ 2 ≤
      8192 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 6) ^ 2 :=
    Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) 2)
  rw [g1RClock_eq r]
  simp only [g1BPassASteps, g1BReadSteps, g1InstallScanSteps,
    g1ReadBHandoffSteps, g1RepairSteps, hlen]
  omega

/-- **The repaired zero-index total fits the unchanged public clock**, with no
hypothesis at all on the request. -/
theorem g1ZPassASteps_le_clock (r : G1Request) :
    g1ZPassASteps r ≤ g1Clock (encodeG1 r).length := by
  have hlen : (encodeG1 r).length =
      4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 6) :=
    encodeG1_length r
  rw [g1RClock_eq r]
  simp only [g1ZPassASteps, g1ReadBSteps, g1ReadBHandoffSteps, g1RepairSteps,
    hlen]
  omega

/-! ## The two composed capstones -/

/-- **The positive-index operand-2 read, repaired.**  For a canonical `and`/`or`
request with `0 < arg2` and `r.vals[arg2]? = some b`, exactly
`g1BPassASteps r = g1BReadSteps r + (4u + 4a1 + 17a + 22) = g1InstallScanSteps r
+ 8a² + 62a + 4u + 4a1 + 59` genuine steps take `G1M.initialConfig` to the
canonical pass-A handoff `g1ReadAConfig r b`: head `0`, control `readAStart`,
`G1Ctx.vB = b`, and the tape restored **bit-for-bit to the initial tape** — the
canonical encoded word plus the trailing blank frame, with every consumed
operand-2 unit back to `index` and no `cursor` anywhere.

The bit `b` is the **actual** `r.vals[r.arg2]`, resolved physically out of the
unannotated data region: no value, target, cursor or index annotation is
supplied to the machine, which is the same fixed zero-parameter program as
before.

This is the statement the read alone could not make: after the sweep the tape is
the canonical word again, so pass A can start from a clean word.  It is *only*
the read plus its repair: `readAStart` is idle, operand 1 is not read, and
combine, the output write and `TM.accepts` are untouched. -/
theorem g1CS_readB_positive_repaired_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : 0 < r.arg2) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BPassASteps r) = g1ReadAConfig r b := by
  have hm : r.arg2 < r.vals.length := by
    by_contra hcon
    rw [List.getElem?_eq_none (by omega)] at hb
    exact Option.noConfusion hb
  rw [g1BPassASteps, runConfig_add,
    g1CS_readB_positive_exact r hc ht h2 b hb]
  exact g1CS_repair_sweep_readAConfig r r.arg2 (Nat.le_refl _) hm b

/-- **The zero-index operand-2 read, repaired.**  For a canonical `and`/`or`
request with `arg2 = 0` and `r.vals[0]? = some b`, exactly
`g1ZPassASteps r = g1ReadBSteps r + (4u + 4a1 + 22) = g1ReadBHandoffSteps r +
8u + 8a1 + 43` genuine steps take `G1M.initialConfig` to the **same** pass-A
`g1ReadAConfig r b`.  At `arg2 = 0` the read wrote nothing, so the sweep has no
consumed unit to repair (`s = 0`, `13 * 0 = 0` write steps): it is a pure rewind
back to head `0`.  That is why both branches share one endpoint. -/
theorem g1CS_readB_zero_repaired_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : r.arg2 = 0) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ZPassASteps r) = g1ReadAConfig r b := by
  have hm : r.arg2 < r.vals.length := by
    by_contra hcon
    rw [List.getElem?_eq_none (by omega)] at hb
    exact Option.noConfusion hb
  have hhead : 4 * (r.tag.units + r.arg1 + 5) =
      4 * (g1WalkCursor r r.arg2 + 1) := by
    simp only [g1WalkCursor, h2]
  have hstart : g1AlignedConfig (encodeG1 r).length
      (4 * (r.tag.units + r.arg1 + 5))
      (g1_route_lt_tapeLength r _ (by omega))
      (G1M.initialConfig (g1Point (encodeG1 r))).tape
      .readAResetStart .p0 false false false (g1Ctx0.withVB b) =
    g1AlignedConfig (encodeG1 r).length (4 * (g1WalkCursor r r.arg2 + 1))
      (by have := g1WalkCursor_safe r r.arg2 (Nat.le_refl _) hm; omega)
      (g1ListTape ((g1BSpentFrames r 0).flatMap G1Frame.bits))
      .readAResetStart .p0 false false false (g1Ctx0.withVB b) := by
    refine g1RAligned_congr _ _ _ _ _ hhead _ _ ?_ _ _ _ _ _ _
    rw [g1BSpentFrames_zero r, ← g1ListTape_validation_eq_initial r]; rfl
  rw [g1ZPassASteps, runConfig_add, g1CS_readB_zero_exact r hc ht h2 b hb,
    hstart]
  exact g1CS_repair_sweep_readAConfig r 0 (by omega) hm b

/-! ## The exact projections of the common endpoint -/

theorem g1CS_readB_positive_repaired_head (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : 0 < r.arg2) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    ((TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BPassASteps r)).head : Nat) = 0 := by
  rw [g1CS_readB_positive_repaired_exact r hc ht h2 b hb]; rfl

theorem g1CS_readB_positive_repaired_state (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : 0 < r.arg2) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BPassASteps r)).state.snd = g1ReadAState (g1Ctx0.withVB b) := by
  rw [g1CS_readB_positive_repaired_exact r hc ht h2 b hb]; rfl

/-- **The latched operand-2 value survives the repair sweep.** -/
theorem g1CS_readB_positive_repaired_vB (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : 0 < r.arg2) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BPassASteps r)).state.snd.ctx.vB = b := by
  rw [g1CS_readB_positive_repaired_exact r hc ht h2 b hb]; rfl

/-- **The whole tape is back to the canonical encoded word plus the blank
frame** — bit for bit the machine's initial tape, not merely a word of the same
length. -/
theorem g1CS_readB_positive_repaired_tape (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : 0 < r.arg2) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BPassASteps r)).tape =
      g1ListTape ((encodeG1Frames r ++ [G1Frame.blank]).flatMap
        G1Frame.bits) := by
  rw [g1CS_readB_positive_repaired_exact r hc ht h2 b hb]
  exact g1ReadAConfig_tape r b

/-- **And that word is literally the initial tape.** -/
theorem g1CS_readB_positive_repaired_tape_initial (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .and ∨ r.tag = .or) (h2 : 0 < r.arg2)
    (b : Bool) (hb : r.vals[r.arg2]? = some b) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BPassASteps r)).tape =
      (G1M.initialConfig (g1Point (encodeG1 r))).tape := by
  rw [g1CS_readB_positive_repaired_exact r hc ht h2 b hb]; rfl

theorem g1CS_readB_zero_repaired_head (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : r.arg2 = 0) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    ((TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ZPassASteps r)).head : Nat) = 0 := by
  rw [g1CS_readB_zero_repaired_exact r hc ht h2 b hb]; rfl

theorem g1CS_readB_zero_repaired_state (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : r.arg2 = 0) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ZPassASteps r)).state.snd = g1ReadAState (g1Ctx0.withVB b) := by
  rw [g1CS_readB_zero_repaired_exact r hc ht h2 b hb]; rfl

theorem g1CS_readB_zero_repaired_vB (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : r.arg2 = 0) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ZPassASteps r)).state.snd.ctx.vB = b := by
  rw [g1CS_readB_zero_repaired_exact r hc ht h2 b hb]; rfl

/-- **The zero-index branch is genuinely non-destructive**: the sweep writes
nothing, so the endpoint tape is the initial tape itself. -/
theorem g1CS_readB_zero_repaired_tape (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : r.arg2 = 0) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ZPassASteps r)).tape =
      (G1M.initialConfig (g1Point (encodeG1 r))).tape := by
  rw [g1CS_readB_zero_repaired_exact r hc ht h2 b hb]; rfl

/-- **The two branches really do meet.**  Whatever the operand-2 index is, a
successful read followed by the repair sweep ends in one and the same
configuration, so the deferred pass-A slice has a single entry point.  The
conditional is on the *request*, not on the machine: the fixed control takes no
argument telling it which branch it is in. -/
theorem g1CS_readB_repaired_common (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (if r.arg2 = 0 then g1ZPassASteps r else g1BPassASteps r) =
      g1ReadAConfig r b := by
  by_cases h2 : r.arg2 = 0
  · rw [if_pos h2]
    exact g1CS_readB_zero_repaired_exact r hc ht h2 b hb
  · rw [if_neg h2]
    exact g1CS_readB_positive_repaired_exact r hc ht (by omega) b hb

/-- **The common total also fits the unchanged public clock.** -/
theorem g1CS_readB_repaired_common_le_clock (r : G1Request) :
    (if r.arg2 = 0 then g1ZPassASteps r else g1BPassASteps r) ≤
      g1Clock (encodeG1 r).length := by
  by_cases h2 : r.arg2 = 0
  · rw [if_pos h2]; exact g1ZPassASteps_le_clock r
  · rw [if_neg h2]; exact g1BPassASteps_le_clock r

/-! ## The out-of-range boundary is untouched

`bOOB` is where the read stops when the operand-2 index points past the data
region.  No sweep is composed behind it, and none is claimed: the boundary stays
exactly as `GateOneWalkDriver` leaves it. -/

/-- The pass-A handoff and the out-of-range boundary are different states, so no
theorem can confuse the repaired endpoint with the unrepaired one. -/
theorem g1ReadAState_ne_oob (ctx ctx' : G1Ctx) :
    g1ReadAState ctx ≠ g1OOBState ctx' := by
  intro h
  have hmode : G1Mode.readAStart = G1Mode.bOOB := congrArg G1State.mode h
  exact absurd hmode (by decide)

/-- **The out-of-range branch is still unrepaired, and still stable.**  For
`0 < arg2` with `vals.length ≤ arg2`, the endpoint after `g1BOOBSteps r + k`
steps is the same `bOOB` configuration for every `k`, its tape still carries
`m = vals.length` consumed operand-2 units, and its state is **not** the pass-A
handoff.  Nothing here repairs that tape, and nothing here calls the boundary a
rejection. -/
theorem g1CS_readB_positive_oob_unrepaired (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : 0 < r.arg2)
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
  ⟨g1CS_readB_positive_oob_stable r hc ht h2 hm k,
    g1BSpentFrames_count_spent r r.vals.length,
    fun ctx => g1ReadAState_ne_oob ctx (g1BOOBCtx r)⟩

end Pnp3.Internal.PsubsetPpoly.TM
