import Complexity.TMVerifier.TuringToolkit.GateOneWalkDriverExamples

/-!
# G1 cursor walk, driver layer: surface tests

Theorem-style exact wrappers for the PR3c surface: the `8k² + 29k` loop clock,
the induction from the **real** initial configuration into `Σ(k)`, the
`g1BSpentFrames` repair-pending layout family, the successful terminal at
`j = arg2`, the **public arbitrary positive-index operand-2 read** with its
projections, the aggregated out-of-range branch in both of its branches, both
clock bounds, and the four all-literal probes.

Two facts the wrappers pin deliberately.  The induction's endpoint is
`g1WalkConfig r k hk2 hk v hv`, formed with the *caller's own* hidden-bit proof,
so a later slice cannot weaken `Σ` into a configuration whose latch is unrelated
to the data region.  And every endpoint tape is `g1BSpentFrames r s`:
cursor-free and data-restored, but with the operand-2 field still consumed.

**Absent from this surface**: the `spent ↦ index` repair sweep, any pass-A read,
any combine step, any output write, and any `TM.accepts`, verdict, full-clock,
gate-semantics, acceptance-gate, multi-gate, specification-bridge or padded-tape
surface.  It pins public signatures and proves nothing new.
-/

namespace Pnp3.Tests.TMGateOneWalkDriverSurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM
theorem check_g1BLoopSteps_zero : g1BLoopSteps 0 = 0 := g1BLoopSteps_zero

/-- One more round costs exactly the `16k + 37` of the merged round theorem. -/
theorem check_g1BLoopSteps_succ (k : Nat) :
    g1BLoopSteps (k + 1) = g1BLoopSteps k + (16 * k + 37) :=
  g1BLoopSteps_succ k

/-- The closed form really is the sum of the individual round costs. -/
theorem check_g1BLoopSteps_eq_sum (k : Nat) :
    g1BLoopSteps k = ((List.range k).map (fun j => 16 * j + 37)).sum :=
  g1BLoopSteps_eq_sum k

theorem check_g1CS_walk_loop_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k0 : Nat) (h2 : r.arg2 = k0 + 1) :
    ∀ (k : Nat) (hk2 : k ≤ r.arg2) (hk : k < r.vals.length) (v : Bool)
      (hv : r.vals[k]? = some v),
      TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1WalkInstallSteps r + g1BLoopSteps k) =
        g1WalkConfig r k hk2 hk v hv :=
  g1CS_walk_loop_exact r hc ht k0 h2

/-- The one-round out-of-range tape *is* this family… -/
theorem check_g1BSpentFrames_eq_restored (r : G1Request) (j : Nat) :
    g1WalkFramesRestored r j = g1BSpentFrames r (j + 1) :=
  g1BSpentFrames_eq_restored r j

/-- …and at `s = 0` on an empty data region it is the initial word. -/
theorem check_g1BSpentFrames_empty (r : G1Request) (hv : r.vals = []) :
    g1BSpentFrames r 0 = encodeG1Frames r ++ [G1Frame.blank] :=
  g1BSpentFrames_empty r hv

/-- The length — no frame invented, none lost — and the three counts: **no
cursor survives**, `s` units are consumed, `arg2 - s` remain (not repaired). -/
theorem check_g1BSpentFrames_shape (r : G1Request) (s : Nat) (hs : s ≤ r.arg2) :
    (g1BSpentFrames r s).length =
        r.tag.units + r.arg1 + r.arg2 + r.vals.length + 7 ∧
      (g1BSpentFrames r s).length =
        (encodeG1Frames r ++ [G1Frame.blank]).length ∧
      (g1BSpentFrames r s).count G1Frame.cursor = 0 ∧
      (g1BSpentFrames r s).count G1Frame.spent = s ∧
      (g1BSpentFrames r s).count G1Frame.index = r.arg1 + (r.arg2 - s) :=
  ⟨g1BSpentFrames_length r s hs, g1BSpentFrames_length_eq_validation r s hs,
    g1BSpentFrames_count_cursor r s, g1BSpentFrames_count_spent r s,
    g1BSpentFrames_count_index r s⟩

/-- The exhaustion prefix: its length, and the `argSep` it stops on closing the
field route. -/
theorem check_g1ExhPre (r : G1Request) :
    (g1ExhPre r).length = r.tag.units + r.arg1 + 2 ∧
      g1ExhPre r ++ [G1Frame.argSep] = g1FieldRouteFrames r :=
  ⟨g1ExhPre_length r, g1ExhPre_argSep r⟩

/-- **`Σ(r, arg2, v) → readAResetStart`** in exactly `16 * arg2 + 28` steps, on
the repair-pending `g1BSpentFrames r arg2`: data region `vals`, no cursor,
operand 2 `spent^arg2`, `vB = vals[arg2]`. -/
theorem check_g1CS_walk_terminal_exact (r : G1Request)
    (hm : r.arg2 < r.vals.length) (v : Bool) (hv : r.vals[r.arg2]? = some v) :
    TM.runConfig (M := G1M)
        (g1WalkConfig r r.arg2 (Nat.le_refl _) hm v hv) (16 * r.arg2 + 28) =
      g1AlignedConfig (encodeG1 r).length (4 * (g1WalkCursor r r.arg2 + 1))
        (by have := g1WalkCursor_safe r r.arg2 (Nat.le_refl _) hm; omega)
        (g1ListTape ((g1BSpentFrames r r.arg2).flatMap G1Frame.bits))
        .readAResetStart .p0 false false false (g1Ctx0.withVB v) :=
  g1CS_walk_terminal_exact r hm v hv
theorem check_g1BSteps_eq (r : G1Request) :
    g1BReadSteps r =
        g1WalkInstallSteps r + g1BLoopSteps r.arg2 + (16 * r.arg2 + 28) ∧
      g1BReadSteps r =
        g1WalkInstallSteps r + (8 * r.arg2 ^ 2 + 45 * r.arg2 + 28) ∧
      g1BOOBSteps r =
        g1InstallScanSteps r +
          (8 * r.vals.length ^ 2 + 29 * r.vals.length + 4) :=
  ⟨g1BReadSteps_eq r, g1BReadSteps_eq_install r, g1BOOBSteps_eq r⟩
theorem check_g1BSteps_le_clock (r : G1Request) :
    g1BReadSteps r ≤ g1Clock (encodeG1 r).length ∧
      g1BOOBSteps r ≤ g1Clock (encodeG1 r).length :=
  ⟨g1BReadSteps_le_clock r, g1BOOBSteps_le_clock r⟩
/-- **The machine resolves `r.vals[r.arg2]` for an arbitrary `arg2 > 0`**, from
the real initial configuration, in exactly `g1BReadSteps r` genuine steps; the
returned bit is the *actual* data bit — no value is supplied to the machine —
and the final tape is repair-pending. -/
theorem check_g1CS_readB_positive_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : 0 < r.arg2) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BReadSteps r) =
      g1AlignedConfig (encodeG1 r).length (4 * (g1WalkCursor r r.arg2 + 1))
        (by
          have hm : r.arg2 < r.vals.length := by
            by_contra hc'; rw [List.getElem?_eq_none (by omega)] at hb
            exact Option.noConfusion hb
          have := g1WalkCursor_safe r r.arg2 (Nat.le_refl _) hm; omega)
        (g1ListTape ((g1BSpentFrames r r.arg2).flatMap G1Frame.bits))
        .readAResetStart .p0 false false false (g1Ctx0.withVB b) :=
  g1CS_readB_positive_exact r hc ht h2 b hb

/-- The four projections of the read: head, control state, the latched bit —
which is `r.vals[r.arg2]` — and the **repair-pending** final tape. -/
theorem check_g1CS_readB_positive_proj (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : 0 < r.arg2) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    ((TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BReadSteps r)).head : Nat) = 4 * (g1WalkCursor r r.arg2 + 1) ∧
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1BReadSteps r)).state.snd = g1ReadAResetState (g1Ctx0.withVB b) ∧
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1BReadSteps r)).state.snd.ctx.vB = b ∧
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1BReadSteps r)).tape =
        g1ListTape ((g1BSpentFrames r r.arg2).flatMap G1Frame.bits) :=
  ⟨g1CS_readB_positive_head r hc ht h2 b hb,
    g1CS_readB_positive_state r hc ht h2 b hb,
    g1CS_readB_positive_vB r hc ht h2 b hb,
    g1CS_readB_positive_tape r hc ht h2 b hb⟩

/-- The context split: `g1Ctx0` on an empty data region… -/
theorem check_g1BOOBCtx_nil (r : G1Request) (hv : r.vals = []) :
    g1BOOBCtx r = g1Ctx0 :=
  g1BOOBCtx_nil r hv

/-- …and the last latched bit otherwise. -/
theorem check_g1BOOBCtx_last (r : G1Request) (t : Nat) (v : Bool)
    (ht : t + 1 = r.vals.length) (hv : r.vals[t]? = some v) :
    g1BOOBCtx r = g1Ctx0.withVB v :=
  g1BOOBCtx_last r t v ht hv

/-- The empty-data branch: read-only, tape bit-for-bit the initial word. -/
theorem check_g1CS_readB_positive_oob_nil (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : 0 < r.arg2) (hv : r.vals = []) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BOOBSteps r) =
      g1AlignedConfig (encodeG1 r).length
        (4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 5))
        (g1_route_lt_tapeLength r _ (by omega))
        (g1ListTape ((g1BSpentFrames r r.vals.length).flatMap G1Frame.bits))
        .bOOB .p0 false false false (g1BOOBCtx r) :=
  g1CS_readB_positive_oob_nil r hc ht h2 hv

/-- The non-empty branch: installation, `m - 1` rounds and the aborting one. -/
theorem check_g1CS_readB_positive_oob_cons (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (t : Nat)
    (hlen : t + 1 = r.vals.length) (hm : r.vals.length ≤ r.arg2) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BOOBSteps r) =
      g1AlignedConfig (encodeG1 r).length
        (4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 5))
        (g1_route_lt_tapeLength r _ (by omega))
        (g1ListTape ((g1BSpentFrames r r.vals.length).flatMap G1Frame.bits))
        .bOOB .p0 false false false (g1BOOBCtx r) :=
  g1CS_readB_positive_oob_cons r hc ht t hlen hm

/-- **The aggregated branch.**  One count and one endpoint for every data
region with `vals.length ≤ arg2`; the tape is repair-pending and `bOOB` is a
boundary, not a verdict. -/
theorem check_g1CS_readB_positive_oob_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : 0 < r.arg2)
    (hm : r.vals.length ≤ r.arg2) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BOOBSteps r) =
      g1AlignedConfig (encodeG1 r).length
        (4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 5))
        (g1_route_lt_tapeLength r _ (by omega))
        (g1ListTape ((g1BSpentFrames r r.vals.length).flatMap G1Frame.bits))
        .bOOB .p0 false false false (g1BOOBCtx r) :=
  g1CS_readB_positive_oob_exact r hc ht h2 hm

theorem check_g1CS_readB_positive_oob_stable (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : 0 < r.arg2)
    (hm : r.vals.length ≤ r.arg2) (k : Nat) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BOOBSteps r + k) =
      g1AlignedConfig (encodeG1 r).length
        (4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 5))
        (g1_route_lt_tapeLength r _ (by omega))
        (g1ListTape ((g1BSpentFrames r r.vals.length).flatMap G1Frame.bits))
        .bOOB .p0 false false false (g1BOOBCtx r) :=
  g1CS_readB_positive_oob_stable r hc ht h2 hm k

/-- The boundary's projections: head, stable `bOOB` with its context split, and
the **repair-pending** tape. -/
theorem check_g1CS_readB_positive_oob_proj (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (h2 : 0 < r.arg2)
    (hm : r.vals.length ≤ r.arg2) :
    ((TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BOOBSteps r)).head : Nat) =
        4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 5) ∧
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1BOOBSteps r)).state.snd = g1OOBState (g1BOOBCtx r) ∧
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
          (g1BOOBSteps r)).tape =
        g1ListTape ((g1BSpentFrames r r.vals.length).flatMap G1Frame.bits) :=
  ⟨g1CS_readB_positive_oob_head r hc ht h2 hm,
    g1CS_readB_positive_oob_state r hc ht h2 hm,
    g1CS_readB_positive_oob_tape r hc ht h2 hm⟩

/-- **Success and out-of-range are different boundaries**, so the exhaustive
`arg2 < vals.length` / `vals.length ≤ arg2` really separate the capstones. -/
theorem check_g1CS_readB_positive_oob_ne_success (ctx ctx' : G1Ctx) :
    g1OOBState ctx ≠ g1ReadAResetState ctx' :=
  g1CS_readB_positive_oob_ne_success ctx ctx'

open G1WalkDriverExamples in
/-- The loop clock on literals, with the recurrence at `k = 1`. -/
theorem check_loopSteps_literals :
    g1BLoopSteps 0 = 0 ∧ g1BLoopSteps 1 = 37 ∧ g1BLoopSteps 2 = 90 ∧
      g1BLoopSteps 3 = 159 ∧ g1BLoopSteps 2 = g1BLoopSteps 1 + 53 :=
  ⟨loopSteps_zero, loopSteps_one, loopSteps_two, loopSteps_three,
    loopSteps_two_eq⟩

open G1WalkDriverExamples in
/-- `⟨and, 0, 1, [false, true]⟩`: `52` cells, `149` scan steps, `239` total,
and a fourteen-frame final word with no cursor, one `spent` and no `index`. -/
theorem check_readExample_layout :
    g1BReadExample.Canonical ∧
      (encodeG1 g1BReadExample).length = 52 ∧
      g1BSpentFrames g1BReadExample g1BReadExample.arg2 = g1BReadFramesFinal ∧
      g1BReadFramesFinal.length = 14 ∧
      g1BReadFramesFinal.count G1Frame.cursor = 0 ∧
      g1BReadFramesFinal.count G1Frame.spent = 1 ∧
      g1BReadFramesFinal.count G1Frame.index = 0 ∧
      g1InstallScanSteps g1BReadExample = 149 ∧
      g1BReadSteps g1BReadExample = 239 ∧
      g1BReadSteps g1BReadExample = 158 + 37 + 44 :=
  ⟨g1BReadExample_canonical, g1BReadExample_length, readFramesFinal_eq,
    readFramesFinal_length, readFramesFinal_count_cursor,
    readFramesFinal_count_spent, readFramesFinal_count_index,
    readExample_install_scan_steps, readExample_steps,
    readExample_steps_split⟩

open G1WalkDriverExamples in
/-- **`239` genuine steps read `vals[1] = true`**, head `44`, inside the literal
clock `1438720`. -/
theorem check_read_positive :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 g1BReadExample))) 239 =
      g1AlignedConfig (encodeG1 g1BReadExample).length 44
        (g1_route_lt_tapeLength g1BReadExample 11 (by decide))
        (g1ListTape (g1BReadFramesFinal.flatMap G1Frame.bits))
        .readAResetStart .p0 false false false (g1Ctx0.withVB true) ∧
      (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1BReadExample)))
          239).state.snd.ctx.vB = true ∧
      ((TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1BReadExample)))
          239).head : Nat) = 44 ∧
      g1Clock (encodeG1 g1BReadExample).length = 1438720 ∧
      239 ≤ g1Clock (encodeG1 g1BReadExample).length :=
  ⟨read_positive, read_positive_vB, read_positive_head,
    readExample_clock_value, read_positive_clock⟩

open G1InstallScanExamples G1WalkExamples G1WalkDriverExamples in
/-- **`328` genuine steps read `vals[2] = true`** of
`⟨and, 0, 2, [false, true, true]⟩`, ending on the merged literal word
`g1WalkFramesFinal`, head `52`, inside the clock. -/
theorem check_read_positive_two :
    g1BSpentFrames g1WalkExample g1WalkExample.arg2 = g1WalkFramesFinal ∧
      g1BReadSteps g1WalkExample = 328 ∧
      g1BReadSteps g1WalkExample = 178 + (37 + 53) + 60 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1WalkExample))) 328 =
        g1AlignedConfig (encodeG1 g1WalkExample).length 52
          (g1_route_lt_tapeLength g1WalkExample 13 (by decide))
          (g1ListTape (g1WalkFramesFinal.flatMap G1Frame.bits))
          .readAResetStart .p0 false false false (g1Ctx0.withVB true) ∧
      (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1WalkExample)))
          328).state.snd.ctx.vB = true ∧
      328 ≤ g1Clock (encodeG1 g1WalkExample).length :=
  ⟨walkExample_framesFinal, walkExample_steps, walkExample_steps_split,
    read_positive_two, read_positive_two_vB, read_positive_two_clock⟩

open G1WalkInvariantExamples G1WalkDriverExamples in
/-- **The aggregated out-of-range branch at `m = 0`**: `149` steps of
`⟨and, 0, 2, []⟩` to the stable `bOOB` boundary at head `44`, on a tape that is
literally the initial word. -/
theorem check_oob_empty :
    g1BOOBSteps g1EmptyExample = 149 ∧
      g1BSpentFrames g1EmptyExample g1EmptyExample.vals.length =
        encodeG1Frames g1EmptyExample ++ [G1Frame.blank] ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1EmptyExample))) 149 =
        g1AlignedConfig (encodeG1 g1EmptyExample).length 44
          (g1_route_lt_tapeLength g1EmptyExample 11 (by decide))
          (g1ListTape
            ((g1BSpentFrames g1EmptyExample 0).flatMap G1Frame.bits))
          .bOOB .p0 false false false g1Ctx0 ∧
      149 ≤ g1Clock (encodeG1 g1EmptyExample).length :=
  ⟨emptyExample_oob_steps, emptyExample_frames, oob_empty, oob_empty_clock⟩

open G1WalkInvariantExamples G1WalkDriverExamples in
/-- **The aggregated out-of-range branch at `m = 2`**: `255` steps of
`⟨and, 0, 2, [false, true]⟩` — `170 + 37 + 48` — to the stable `bOOB` boundary
at head `52`, on the merged unrepaired literal `g1OOBFramesRestored1`. -/
theorem check_oob_nonempty :
    g1BOOBSteps g1OOBExample = 255 ∧
      g1BOOBSteps g1OOBExample = 170 + 37 + 48 ∧
      g1BSpentFrames g1OOBExample g1OOBExample.vals.length =
        g1OOBFramesRestored1 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1OOBExample))) 255 =
        g1AlignedConfig (encodeG1 g1OOBExample).length 52
          (g1_route_lt_tapeLength g1OOBExample 13 (by decide))
          (g1ListTape (g1OOBFramesRestored1.flatMap G1Frame.bits))
          .bOOB .p0 false false false (g1Ctx0.withVB true) ∧
      ((TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1OOBExample)))
          255).head : Nat) = 52 ∧
      255 ≤ g1Clock (encodeG1 g1OOBExample).length :=
  ⟨oobExample_oob_steps, oobExample_oob_steps_split, oobExample_frames,
    oob_nonempty, oob_nonempty_head, oob_nonempty_clock⟩

end Pnp3.Tests.TMGateOneWalkDriverSurface
