import Complexity.TMVerifier.TuringToolkit.GateOneWalkInvariantExamples

/-!
# G1 cursor walk, invariant layer: surface tests

Import-side contracts for the PR3a surface: the exact `Σ(j)` layout with its
length, counts and structural facts, the installation into `Σ(0)` from the
**real** initial configuration, the empty-data out-of-range branch, and the
all-literal probes of both executed capstones.

**Deliberately absent**: any one-round iteration theorem `Σ(j) → Σ(j+1)`, any
normal-round or out-of-range preservation theorem on `Σ(j)`, any induction over
`j`, any loop, driver or cumulative clock, any successful terminal at
`j = arg2`, any aggregation of the two out-of-range branches, any addressing or
positive-index operand-value surface — those are PR3b — and any repair, pass-A,
output-write, `TM.accepts`, gate-semantics, full-clock or padded-tape surface.

This is an audit surface: it pins public signatures and proves nothing new.
-/

namespace Pnp3.Tests.TMGateOneWalkInvariantSurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM

#check @g1WalkFrames
#check @g1WalkFramesMarked
#check @g1WalkFramesRestored
#check @g1WalkCursor
#check @g1WalkConfig
#check @g1WalkInstallSteps
#check @g1WalkEmptyOOBSteps
#check @G1WalkInvariantExamples.g1WalkFramesRound0
#check @G1WalkInvariantExamples.g1EmptyExample
#check @G1WalkInvariantExamples.g1EmptyExample_canonical
#check @G1WalkInvariantExamples.g1EmptyExample_length

theorem check_g1EmptyExample_canonical :
    G1WalkInvariantExamples.g1EmptyExample.Canonical :=
  G1WalkInvariantExamples.g1EmptyExample_canonical

theorem check_g1EmptyExample_length :
    (encodeG1 G1WalkInvariantExamples.g1EmptyExample).length = 48 :=
  G1WalkInvariantExamples.g1EmptyExample_length

/-! ## The structural facts, pinned exactly

Each is a theorem *about the layout*; a later slice must not turn one back into
a hypothesis of the round it feeds. -/

/-- The run both scans of a round cross carries only skippable frames. -/
theorem check_g1WalkSkipRun_mem (j : Nat) (vals : List Bool) :
    ∀ f ∈ (List.replicate j G1Frame.spent ++ [G1Frame.separator] ++
        (vals.take j).map G1Frame.data), G1WalkSkip f :=
  g1WalkSkipRun_mem j vals

/-- That run contains **no** unspent `index`, which is why `bFwd` never
stalls. -/
theorem check_g1WalkSkipRun_no_index (j : Nat) (vals : List Bool) :
    G1Frame.index ∉ (List.replicate j G1Frame.spent ++ [G1Frame.separator] ++
      (vals.take j).map G1Frame.data) :=
  g1WalkSkipRun_no_index j vals

/-- `spent^j` is the **right** suffix of the operand-2 field. -/
theorem check_g1WalkOperand2_spent_suffix (a2 j : Nat) (hj : j < a2) :
    List.replicate (a2 - j) G1Frame.index ++ List.replicate j G1Frame.spent =
      (List.replicate (a2 - j - 1) G1Frame.index ++ [G1Frame.index]) ++
        List.replicate j G1Frame.spent :=
  g1WalkOperand2_spent_suffix a2 j hj

/-! ## Lengths, counts and head safety, pinned exactly -/

/-- The invariant word is exactly as long as the real tape word. -/
theorem check_g1WalkFrames_length_eq_validation (r : G1Request) (j : Nat)
    (hj2 : j ≤ r.arg2) (hj : j < r.vals.length) :
    (g1WalkFrames r j).length = (encodeG1Frames r ++ [G1Frame.blank]).length :=
  g1WalkFrames_length_eq_validation r j hj2 hj

theorem check_g1WalkFrames_length (r : G1Request) (j : Nat)
    (hj2 : j ≤ r.arg2) (hj : j < r.vals.length) :
    (g1WalkFrames r j).length =
      r.tag.units + r.arg1 + r.arg2 + r.vals.length + 7 :=
  g1WalkFrames_length r j hj2 hj

theorem check_g1WalkFrames_count_index (r : G1Request) (j : Nat) :
    (g1WalkFrames r j).count G1Frame.index = r.arg1 + (r.arg2 - j) :=
  g1WalkFrames_count_index r j

theorem check_g1WalkFrames_count_spent (r : G1Request) (j : Nat) :
    (g1WalkFrames r j).count G1Frame.spent = j :=
  g1WalkFrames_count_spent r j

/-- **The cursor is unique** in `Σ(j)`. -/
theorem check_g1WalkFrames_count_cursor (r : G1Request) (j : Nat) :
    (g1WalkFrames r j).count G1Frame.cursor = 1 :=
  g1WalkFrames_count_cursor r j

theorem check_g1WalkFramesMarked_length (r : G1Request) (j : Nat)
    (hj2 : j < r.arg2) (hj : j < r.vals.length) :
    (g1WalkFramesMarked r j).length =
      r.tag.units + r.arg1 + r.arg2 + r.vals.length + 7 :=
  g1WalkFramesMarked_length r j hj2 hj

theorem check_g1WalkFramesMarked_count_cursor (r : G1Request) (j : Nat) :
    (g1WalkFramesMarked r j).count G1Frame.cursor = 1 :=
  g1WalkFramesMarked_count_cursor r j

theorem check_g1WalkFramesMarked_count_spent (r : G1Request) (j : Nat) :
    (g1WalkFramesMarked r j).count G1Frame.spent = j + 1 :=
  g1WalkFramesMarked_count_spent r j

theorem check_g1WalkFramesMarked_count_index (r : G1Request) (j : Nat) :
    (g1WalkFramesMarked r j).count G1Frame.index =
      r.arg1 + (r.arg2 - j - 1) :=
  g1WalkFramesMarked_count_index r j

/-- The restored layout carries **no** cursor. -/
theorem check_g1WalkFramesRestored_count_cursor (r : G1Request) (j : Nat) :
    (g1WalkFramesRestored r j).count G1Frame.cursor = 0 :=
  g1WalkFramesRestored_count_cursor r j

theorem check_g1WalkFramesRestored_count_spent (r : G1Request) (j : Nat) :
    (g1WalkFramesRestored r j).count G1Frame.spent = j + 1 :=
  g1WalkFramesRestored_count_spent r j

/-- The restored layout is **not repaired**: `arg2 - j - 1` units remain. -/
theorem check_g1WalkFramesRestored_count_index (r : G1Request) (j : Nat) :
    (g1WalkFramesRestored r j).count G1Frame.index =
      r.arg1 + (r.arg2 - j - 1) :=
  g1WalkFramesRestored_count_index r j

/-- Head safety on the invariant domain. -/
theorem check_g1WalkCursor_safe (r : G1Request) (j : Nat)
    (hj2 : j ≤ r.arg2) (hj : j < r.vals.length) :
    4 * (g1WalkCursor r j + 2) < G1M.tapeLength (encodeG1 r).length :=
  g1WalkCursor_safe r j hj2 hj

/-! ## `Σ(j)`'s projections, pinned exactly -/

theorem check_g1WalkConfig_tape (r : G1Request) (j : Nat) (hj2 : j ≤ r.arg2)
    (hj : j < r.vals.length) (v : Bool) (hv : r.vals[j]? = some v) :
    (g1WalkConfig r j hj2 hj v hv).tape =
      g1ListTape ((g1WalkFrames r j).flatMap G1Frame.bits) :=
  g1WalkConfig_tape r j hj2 hj v hv

theorem check_g1WalkConfig_head (r : G1Request) (j : Nat) (hj2 : j ≤ r.arg2)
    (hj : j < r.vals.length) (v : Bool) (hv : r.vals[j]? = some v) :
    ((g1WalkConfig r j hj2 hj v hv).head : Nat) = 4 * g1WalkCursor r j - 1 :=
  g1WalkConfig_head r j hj2 hj v hv

theorem check_g1WalkConfig_state (r : G1Request) (j : Nat) (hj2 : j ≤ r.arg2)
    (hj : j < r.vals.length) (v : Bool) (hv : r.vals[j]? = some v) :
    (g1WalkConfig r j hj2 hj v hv).state.snd =
      g1State .bSeek .p3 false false false (g1Ctx0.withVB v) :=
  g1WalkConfig_state r j hj2 hj v hv

/-- The latched bit is the one the cursor is hiding. -/
theorem check_g1WalkConfig_vB (r : G1Request) (j : Nat) (hj2 : j ≤ r.arg2)
    (hj : j < r.vals.length) (v : Bool) (hv : r.vals[j]? = some v) :
    (g1WalkConfig r j hj2 hj v hv).state.snd.ctx.vB = v :=
  g1WalkConfig_vB r j hj2 hj v hv

theorem check_g1WalkConfig_hidden (r : G1Request) (j : Nat)
    (hj2 : j ≤ r.arg2) (hj : j < r.vals.length)
    (v : Bool) (hv : r.vals[j]? = some v) :
    r.vals[j]? = some v :=
  g1WalkConfig_hidden r j hj2 hj v hv

/-! ## The step counts, pinned exactly -/

theorem check_g1WalkInstallSteps_eq (r : G1Request) :
    g1WalkInstallSteps r = g1FieldRouteSteps r + 4 * (r.arg2 + 1) + 9 :=
  g1WalkInstallSteps_eq r

theorem check_g1WalkEmptyOOBSteps_eq (r : G1Request) :
    g1WalkEmptyOOBSteps r =
      g1FieldRouteSteps r + 4 * (r.arg2 + 1) + 4 :=
  g1WalkEmptyOOBSteps_eq r

/-- Both real-run counts stay inside the **unchanged** public clock. -/
theorem check_g1WalkInstallSteps_le_clock (r : G1Request) :
    g1WalkInstallSteps r ≤ g1Clock (encodeG1 r).length :=
  g1WalkInstallSteps_le_clock r

theorem check_g1WalkEmptyOOBSteps_le_clock (r : G1Request) :
    g1WalkEmptyOOBSteps r ≤ g1Clock (encodeG1 r).length :=
  g1WalkEmptyOOBSteps_le_clock r

/-! ## The two executed capstones, pinned exactly

Both start from `G1M.initialConfig` and both **stop** at their endpoint: no
statement below moves off `Σ(0)`. -/

/-- **Installation into `Σ(0)`**: `g1WalkInstallSteps r` genuine steps, the
whole state pinned by `g1WalkConfig`, one frame written. -/
theorem check_g1CS_walk_install_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1)
    (v : Bool) (hv : r.vals[0]? = some v) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1WalkInstallSteps r) =
      g1WalkConfig r 0 (Nat.zero_le _)
        (by
          cases hl : r.vals with
          | nil => rw [hl] at hv; simp at hv
          | cons c cs => simp) v hv :=
  g1CS_walk_install_exact r hc ht k h2 v hv

theorem check_g1CS_walk_install_head (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1)
    (v : Bool) (hv : r.vals[0]? = some v) :
    ((TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1WalkInstallSteps r)).head : Nat) = 4 * g1WalkCursor r 0 - 1 :=
  g1CS_walk_install_head r hc ht k h2 v hv

/-- The latched operand bit really is `vals[0]`. -/
theorem check_g1CS_walk_install_vB (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1)
    (v : Bool) (hv : r.vals[0]? = some v) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1WalkInstallSteps r)).state.snd.ctx.vB = v :=
  g1CS_walk_install_vB r hc ht k h2 v hv

/-- The resulting tape is exactly the invariant word `g1WalkFrames r 0`. -/
theorem check_g1CS_walk_install_tape (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1)
    (v : Bool) (hv : r.vals[0]? = some v) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1WalkInstallSteps r)).tape =
      g1ListTape ((g1WalkFrames r 0).flatMap G1Frame.bits) :=
  g1CS_walk_install_tape r hc ht k h2 v hv

theorem check_g1CS_walk_install_state (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1)
    (v : Bool) (hv : r.vals[0]? = some v) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1WalkInstallSteps r)).state.snd =
      g1State .bSeek .p3 false false false (g1Ctx0.withVB v) :=
  g1CS_walk_install_state r hc ht k h2 v hv

/-- **The empty-data out-of-range branch**: the stable `bOOB` boundary with the
tape bit-for-bit the initial tape. -/
theorem check_g1CS_walk_install_oob_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1)
    (hv : r.vals = []) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1WalkEmptyOOBSteps r) =
      g1AlignedConfig (encodeG1 r).length (4 * (g1WalkCursor r 0 + 1))
        (g1_route_lt_tapeLength r _ (by simp only [g1WalkCursor]; omega))
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        .bOOB .p0 false false false g1Ctx0 :=
  g1CS_walk_install_oob_exact r hc ht k h2 hv

theorem check_g1CS_walk_install_oob_stable (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1)
    (hv : r.vals = []) (n : Nat) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1WalkEmptyOOBSteps r + n) =
      g1AlignedConfig (encodeG1 r).length (4 * (g1WalkCursor r 0 + 1))
        (g1_route_lt_tapeLength r _ (by simp only [g1WalkCursor]; omega))
        (G1M.initialConfig (g1Point (encodeG1 r))).tape
        .bOOB .p0 false false false g1Ctx0 :=
  g1CS_walk_install_oob_stable r hc ht k h2 hv n

/-- **Not one tape cell changes** on the empty-data branch. -/
theorem check_g1CS_walk_install_oob_tape (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1)
    (hv : r.vals = []) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1WalkEmptyOOBSteps r)).tape =
      (G1M.initialConfig (g1Point (encodeG1 r))).tape :=
  g1CS_walk_install_oob_tape r hc ht k h2 hv

theorem check_g1CS_walk_install_oob_head (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1)
    (hv : r.vals = []) :
    ((TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1WalkEmptyOOBSteps r)).head : Nat) = 4 * (g1WalkCursor r 0 + 1) :=
  g1CS_walk_install_oob_head r hc ht k h2 hv

theorem check_g1CS_walk_install_oob_state (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (k : Nat) (h2 : r.arg2 = k + 1)
    (hv : r.vals = []) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1WalkEmptyOOBSteps r)).state.snd = g1OOBState g1Ctx0 :=
  g1CS_walk_install_oob_state r hc ht k h2 hv

/-- The two endpoints are **different** boundaries. -/
theorem check_g1CS_walk_oob_ne_invariant (ctx ctx' : G1Ctx) :
    g1OOBState ctx ≠ g1State .bSeek .p3 false false false ctx' :=
  g1CS_walk_oob_ne_invariant ctx ctx'

/-! ## The literal probes, pinned exactly -/

open G1InstallScanExamples G1WalkInvariantExamples in
/-- `Σ(0)` of `⟨and, 0, 2, [false, true, true]⟩` is the merged post-install
layout, with the cursor at ordinal `10` and no spent unit yet. -/
theorem check_walkFrames_zero :
    g1WalkFrames g1WalkExample 0 = g1WalkFramesRound0 ∧
      g1WalkCursor g1WalkExample 0 = 10 ∧
      (g1WalkFrames g1WalkExample 0).length = 16 ∧
      (g1WalkFrames g1WalkExample 0).count G1Frame.cursor = 1 ∧
      (g1WalkFrames g1WalkExample 0).count G1Frame.index = 2 ∧
      (g1WalkFrames g1WalkExample 0).count G1Frame.spent = 0 :=
  ⟨walkFrames_zero, walkCursor_zero, walkFrames_zero_length,
    walkFrames_zero_count_cursor, walkFrames_zero_count_index,
    walkFrames_zero_count_spent⟩

open G1InstallScanExamples G1WalkInvariantExamples in
/-- `169 + 5 + 4 = 178` steps from the real initial configuration into `Σ(0)`,
head `39`, inside the unchanged clock. -/
theorem check_walk_install :
    g1WalkInstallSteps g1WalkExample = 178 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1WalkExample))) 178 =
        g1WalkConfig g1WalkExample 0 (by decide) (by decide) false (by decide) ∧
      ((TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1WalkExample)))
          178).head : Nat) = 39 ∧
      178 ≤ g1Clock (encodeG1 g1WalkExample).length :=
  ⟨walk_install_steps, walk_install, walk_install_head, walk_install_clock⟩

open G1WalkInvariantExamples in
/-- `149` steps from the real initial configuration of `⟨and, 0, 2, []⟩` to the
stable `bOOB` boundary at head `44`, tape unchanged, inside the clock. -/
theorem check_walk_empty_oob :
    g1WalkEmptyOOBSteps g1EmptyExample = 149 ∧
      TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1EmptyExample))) 149 =
        g1AlignedConfig (encodeG1 g1EmptyExample).length 44
          (g1_route_lt_tapeLength g1EmptyExample 11 (by decide))
          (G1M.initialConfig (g1Point (encodeG1 g1EmptyExample))).tape
          .bOOB .p0 false false false g1Ctx0 ∧
      (TM.runConfig (M := G1M)
          (G1M.initialConfig (g1Point (encodeG1 g1EmptyExample))) 149).tape =
        (G1M.initialConfig (g1Point (encodeG1 g1EmptyExample))).tape ∧
      149 ≤ g1Clock (encodeG1 g1EmptyExample).length :=
  ⟨walk_empty_oob_steps, walk_empty_oob, walk_empty_oob_tape,
    walk_empty_oob_clock⟩

end Pnp3.Tests.TMGateOneWalkInvariantSurface
