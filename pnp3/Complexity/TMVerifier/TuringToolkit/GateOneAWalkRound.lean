import Complexity.TMVerifier.TuringToolkit.GateOneAWalkInvariant

/-!
# S6 exact one-round operand-A walk (2026-08-30)

**Progress classification: Infrastructure, not P-vs-NP mainline progress.**

This module composes the merged operand-A walk atoms for exactly one machine
round.  In the normal case it takes the canonical `Σᴬ(j)` configuration to
`Σᴬ(j+1)`: the rightmost remaining operand-A `index` becomes `spent`, the
designated cursor is restored to the value hidden at slot `j`, slot `j+1` is
probed and re-latched, and the unique cursor is installed there.

The two boundaries are intentionally separate.  If the operand-A field is
exhausted, execution stops at the local `aExh` boundary immediately produced
by the mixed reverse seek.  If an operand-A index remains but successor data is
absent, the round restores all data, removes the cursor and stops at the
existing `bOOB` boundary.  No terminal continuation, A-repair, driver,
induction, result/combine row, output write or acceptance theorem is composed.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

/-! ## Exact costs and boundary configurations -/

/-- Mixed seek cost from `Σᴬ(j)` to the selected operand-A `index`, before the
four-cell `index → spent` writer. -/
def g1AWalkSeekSteps (r : G1Request) (j : Nat) : Nat :=
  8 * j + 4 * r.arg2 + 12

/-- Shared seek/mark/forward/turn/restore prefix of a normal or data-OOB round. -/
def g1AWalkRoundPrefixSteps (r : G1Request) (j : Nat) : Nat :=
  16 * j + 8 * r.arg2 + 36

/-- Exact normal-round cost, including successor probe/latch and cursor install. -/
def g1AWalkRoundSteps (r : G1Request) (j : Nat) : Nat :=
  16 * j + 8 * r.arg2 + 45

/-- Exact data-OOB round cost: the shared prefix and the four-step OOB probe. -/
def g1AWalkRoundOOBSteps (r : G1Request) (j : Nat) : Nat :=
  16 * j + 8 * r.arg2 + 40

/-- Exact mixed-seek cost when `j = arg1` and the operand-A field is exhausted. -/
def g1AWalkExhaustSteps (r : G1Request) : Nat :=
  8 * r.arg1 + 4 * r.arg2 + 12

set_option linter.unusedVariables false in
/-- The exact successor-data OOB endpoint.  Its data region has been restored,
its operand-A field has one additional `spent`, and it has no cursor. -/
def g1AWalkOOBConfig (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j < r.arg1) (hj : j < r.vals.length) (v : Bool)
    (hv : r.vals[j]? = some v) :
    Configuration (M := G1M) (encodeG1 r).length :=
  g1AlignedConfig (encodeG1 r).length (4 * (g1AWalkCursor r j + 2))
    (g1AWalkCursor_safe r j hj)
    (g1ListTape ((g1AWalkFramesRestored r j).flatMap G1Frame.bits))
    .bOOB .p0 false false false (g1AWalkCtx r b v)

set_option linter.unusedVariables false in
/-- The local operand-index exhaustion endpoint.  The seek is read-only, so the
whole `Σᴬ(arg1)` tape and the current latch/residual context are unchanged. -/
def g1AWalkExhaustConfig (r : G1Request) (b v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    Configuration (M := G1M) (encodeG1 r).length :=
  g1AlignedConfig (encodeG1 r).length (4 * (r.tag.units + 1))
    (by
      have h := g1AWalkCursor_safe r r.arg1 hj
      simp only [g1AWalkCursor] at h
      omega)
    (g1ListTape ((g1AWalkFrames r r.arg1).flatMap G1Frame.bits))
    .aExh .p0 false false false (g1AWalkCtx r b v)

@[simp] theorem g1AWalkOOBConfig_tape (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j < r.arg1) (hj : j < r.vals.length) (v : Bool)
    (hv : r.vals[j]? = some v) :
    (g1AWalkOOBConfig r b j hj1 hj v hv).tape =
      g1ListTape ((g1AWalkFramesRestored r j).flatMap G1Frame.bits) := rfl

@[simp] theorem g1AWalkOOBConfig_head (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j < r.arg1) (hj : j < r.vals.length) (v : Bool)
    (hv : r.vals[j]? = some v) :
    ((g1AWalkOOBConfig r b j hj1 hj v hv).head : Nat) =
      4 * (g1AWalkCursor r j + 2) := rfl

@[simp] theorem g1AWalkOOBConfig_state (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j < r.arg1) (hj : j < r.vals.length) (v : Bool)
    (hv : r.vals[j]? = some v) :
    (g1AWalkOOBConfig r b j hj1 hj v hv).state.snd =
      g1State .bOOB .p0 false false false (g1AWalkCtx r b v) := rfl

@[simp] theorem g1AWalkOOBConfig_res (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j < r.arg1) (hj : j < r.vals.length) (v : Bool)
    (hv : r.vals[j]? = some v) :
    (g1AWalkOOBConfig r b j hj1 hj v hv).state.snd.ctx.res =
      g1Residual r.tag b := by
  simp [g1AWalkOOBConfig, g1State]

@[simp] theorem g1AWalkOOBConfig_vB (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j < r.arg1) (hj : j < r.vals.length) (v : Bool)
    (hv : r.vals[j]? = some v) :
    (g1AWalkOOBConfig r b j hj1 hj v hv).state.snd.ctx.vB = v := rfl

@[simp] theorem g1AWalkExhaustConfig_tape (r : G1Request) (b v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    (g1AWalkExhaustConfig r b v hj hv).tape =
      g1ListTape ((g1AWalkFrames r r.arg1).flatMap G1Frame.bits) := rfl

@[simp] theorem g1AWalkExhaustConfig_head (r : G1Request) (b v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    ((g1AWalkExhaustConfig r b v hj hv).head : Nat) =
      4 * (r.tag.units + 1) := rfl

@[simp] theorem g1AWalkExhaustConfig_state (r : G1Request) (b v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    (g1AWalkExhaustConfig r b v hj hv).state.snd =
      g1State .aExh .p0 false false false (g1AWalkCtx r b v) := rfl

@[simp] theorem g1AWalkExhaustConfig_res (r : G1Request) (b v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    (g1AWalkExhaustConfig r b v hj hv).state.snd.ctx.res =
      g1Residual r.tag b := by
  simp [g1AWalkExhaustConfig, g1State]

@[simp] theorem g1AWalkExhaustConfig_vB (r : G1Request) (b v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    (g1AWalkExhaustConfig r b v hj hv).state.snd.ctx.vB = v := rfl

/-! ## Shared normal/OOB prefix -/

set_option maxHeartbeats 1000000 in
/-- Seek the current operand-A unit, mark it, return to the designated cursor,
turn, and restore exactly the value hidden at slot `j`.  The endpoint is the
successor probe on the cursor-free restored layout. -/
theorem g1CS_aWalk_round_prefix_exact (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j < r.arg1) (hj : j < r.vals.length) (v : Bool)
    (hv : r.vals[j]? = some v) :
    TM.runConfig (M := G1M)
        (g1AWalkConfig r b j (by omega) hj v hv)
        (g1AWalkRoundPrefixSteps r j) =
      g1AlignedConfig (encodeG1 r).length
        (4 * (g1AWalkCursor r j + 1)) (by
          have h := g1AWalkCursor_safe r j hj
          omega)
        (g1ListTape ((g1AWalkFramesRestored r j).flatMap G1Frame.bits))
        .aProbe .p0 false false false (g1AWalkCtx r b v) := by
  have hdv : r.vals[j] = v := g1AGetn hv hj
  have hsafe := g1AWalkCursor_safe r j hj
  have hsafe' :
      4 * (r.tag.units + r.arg1 + r.arg2 + j + 6) <
        G1M.tapeLength (encodeG1 r).length := by
    simpa only [g1AWalkCursor] using hsafe
  have hLmark := g1AWalkMarkPre_length r j
  have hLinner := g1AWalkInnerRun_length j
  have hLouter := g1AWalkOuterRun_length r j (by omega)
  have hLfwd := g1AWalkFwdPre_length r j
  have hLrun := g1AWalkFwdRun_length r j (by omega)
  have hLcur := g1AWalkCursorPre_length r j hj1 hj
  have hA : TM.runConfig (M := G1M)
      (g1AlignedConfig (encodeG1 r).length (4 * g1AWalkCursor r j - 1)
        (by omega) (g1ListTape ((g1AWalkFrames r j).flatMap G1Frame.bits))
        .aSeekOut .p3 false false false (g1AWalkCtx r b v))
      (g1AWalkSeekSteps r j) =
    g1AlignedConfig (encodeG1 r).length
      (4 * (r.tag.units + 2 + (r.arg1 - j - 1))) (by omega)
      (g1ListTape ((g1AWalkFrames r j).flatMap G1Frame.bits))
      .aDec .p0 false false false (g1AWalkCtx r b v) := by
    have h := g1CS_aWalk_seek_index (encodeG1 r).length
      (g1TagRouteFrames r ++
        List.replicate (r.arg1 - j - 1) G1Frame.index)
      (g1AWalkInnerRun j) (g1AWalkOuterRun r j)
      (G1Frame.cursor :: g1AWalkTail r j) (g1AWalkCtx r b v)
      (g1AWalkOuterRun_skip r j) (g1AWalkInnerRun_skip j)
      (by rw [hLmark, hLinner, hLouter];
          simp only [g1AWalkCursor] at hsafe
          omega)
    rw [g1AWalkSplit_seek r j hj1] at h
    simp only [hLmark, hLinner, hLouter,
      show 4 * (r.tag.units + 2 + (r.arg1 - j - 1) +
          (j + (r.arg2 + j + 1) + 1)) + 3 =
        4 * g1AWalkCursor r j - 1 by simp only [g1AWalkCursor]; omega,
      show 4 * (j + (r.arg2 + j + 1) + 1) + 4 =
        8 * j + 4 * r.arg2 + 12 by omega] at h
    exact h
  have hB : TM.runConfig (M := G1M)
      (g1AlignedConfig (encodeG1 r).length
        (4 * (r.tag.units + 2 + (r.arg1 - j - 1))) (by omega)
        (g1ListTape ((g1AWalkFrames r j).flatMap G1Frame.bits))
        .aDec .p0 false false false (g1AWalkCtx r b v)) 4 =
    g1AlignedConfig (encodeG1 r).length
      (4 * (r.tag.units + 3 + (r.arg1 - j - 1))) (by omega)
      (g1ListTape ((g1AWalkFramesMarked r j).flatMap G1Frame.bits))
      .aFwd .p0 false false false (g1AWalkCtx r b v) := by
    have h := g1CS_aWalk_mark (encodeG1 r).length
      (g1TagRouteFrames r ++
        List.replicate (r.arg1 - j - 1) G1Frame.index)
      (g1AWalkInnerRun j ++ G1Frame.argSep ::
        (g1AWalkOuterRun r j ++ G1Frame.cursor :: g1AWalkTail r j))
      (g1AWalkCtx r b v) (by rw [hLmark]; omega)
    rw [g1AWalkSplit_mark r j hj1, g1AWalkSplit_marked r j] at h
    simpa only [hLmark,
      show 4 * (r.tag.units + 2 + (r.arg1 - j - 1)) + 4 =
        4 * (r.tag.units + 3 + (r.arg1 - j - 1)) by omega] using h
  have hC : TM.runConfig (M := G1M)
      (g1AlignedConfig (encodeG1 r).length
        (4 * (r.tag.units + 3 + (r.arg1 - j - 1))) (by omega)
        (g1ListTape ((g1AWalkFramesMarked r j).flatMap G1Frame.bits))
        .aFwd .p0 false false false (g1AWalkCtx r b v))
      (8 * j + 4 * r.arg2 + 12) =
    g1AlignedConfig (encodeG1 r).length
      (4 * (g1AWalkCursor r j + 1)) (by omega)
      (g1ListTape ((g1AWalkFramesMarked r j).flatMap G1Frame.bits))
      .aTurn .p0 false false false (g1AWalkCtx r b v) := by
    have h := g1CS_aWalk_fwd_to_cursor (encodeG1 r).length
      (g1TagRouteFrames r ++
        List.replicate (r.arg1 - j - 1) G1Frame.index ++ [.spent])
      (g1AWalkFwdRun r j) (g1AWalkTail r j) (g1AWalkCtx r b v)
      (g1AWalkFwdRun_skip r j)
      (by rw [hLfwd, hLrun];
          simp only [g1AWalkCursor] at hsafe
          omega)
    rw [g1AWalkSplit_marked_fwd r j] at h
    simp only [hLfwd, hLrun,
      show r.tag.units + 3 + (r.arg1 - j - 1) +
          (2 * j + r.arg2 + 2 + 1) = g1AWalkCursor r j + 1 by
        simp only [g1AWalkCursor]; omega,
      show 4 * (2 * j + r.arg2 + 2 + 1) =
        8 * j + 4 * r.arg2 + 12 by omega] at h
    exact h
  have hD : TM.runConfig (M := G1M)
      (g1AlignedConfig (encodeG1 r).length
        (4 * (g1AWalkCursor r j + 1)) (by omega)
        (g1ListTape ((g1AWalkFramesMarked r j).flatMap G1Frame.bits))
        .aTurn .p0 false false false (g1AWalkCtx r b v)) 4 =
    g1AlignedConfig (encodeG1 r).length (4 * g1AWalkCursor r j) (by omega)
      (g1ListTape ((g1AWalkFramesMarked r j).flatMap G1Frame.bits))
      (g1ARestoreMode v) .p0 false false false (g1AWalkCtx r b v) := by
    have h := g1CS_aWalk_turn (encodeG1 r).length
      (4 * g1AWalkCursor r j) (by omega)
      (g1ListTape (n := (encodeG1 r).length)
        ((g1AWalkFramesMarked r j).flatMap G1Frame.bits)) (g1AWalkCtx r b v)
    simpa only [show 4 * g1AWalkCursor r j + 4 =
      4 * (g1AWalkCursor r j + 1) by omega, g1AWalkCtx_vB] using h
  have hE : TM.runConfig (M := G1M)
      (g1AlignedConfig (encodeG1 r).length (4 * g1AWalkCursor r j) (by omega)
        (g1ListTape ((g1AWalkFramesMarked r j).flatMap G1Frame.bits))
        (g1ARestoreMode v) .p0 false false false (g1AWalkCtx r b v)) 4 =
    g1AlignedConfig (encodeG1 r).length
      (4 * (g1AWalkCursor r j + 1)) (by omega)
      (g1ListTape ((g1AWalkFramesRestored r j).flatMap G1Frame.bits))
      .aProbe .p0 false false false (g1AWalkCtx r b v) := by
    have h := g1CS_aWalk_restore (encodeG1 r).length
      (g1AWalkCursorPre r j) (g1AWalkTail r j) v (g1AWalkCtx r b v)
      (by rw [hLcur]; omega)
    rw [g1AWalkSplit_marked_cursor r j,
      g1AWalkSplit_restored_cursor r j v hj hdv] at h
    simpa only [hLcur, show 4 * g1AWalkCursor r j + 4 =
      4 * (g1AWalkCursor r j + 1) by omega] using h
  simp only [g1AWalkConfig, g1AWalkRoundPrefixSteps]
  rw [show 16 * j + 8 * r.arg2 + 36 =
      g1AWalkSeekSteps r j + (4 + ((8 * j + 4 * r.arg2 + 12) + (4 + 4))) by
        simp only [g1AWalkSeekSteps]; omega,
    runConfig_add, hA, runConfig_add, hB, runConfig_add, hC,
    runConfig_add, hD, hE]

/-! ## The exact normal round and data-OOB boundary -/

set_option maxHeartbeats 1000000 in
/-- **One exact normal operand-A round.**  Under a remaining operand-A index and
an explicit value witness for slot `j+1`, this moves exactly the designated
cursor and re-establishes `Σᴬ(j+1)` with `vB` re-latched to that slot. -/
theorem g1CS_aWalk_round_exact (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j < r.arg1) (hnext : j + 1 < r.vals.length) (v v' : Bool)
    (hv : r.vals[j]? = some v) (hv' : r.vals[j + 1]? = some v') :
    TM.runConfig (M := G1M)
        (g1AWalkConfig r b j (by omega) (by omega) v hv)
        (g1AWalkRoundSteps r j) =
      g1AWalkConfig r b (j + 1) (by omega) hnext v' hv' := by
  have hdv' : r.vals[j + 1] = v' := g1AGetn hv' hnext
  have hLprobe := g1AWalkProbePre_length r j hj1 (by omega)
  have hsafe := g1AWalkCursor_safe r j (by omega)
  have hF : TM.runConfig (M := G1M)
      (g1AlignedConfig (encodeG1 r).length
        (4 * (g1AWalkCursor r j + 1)) (by omega)
        (g1ListTape ((g1AWalkFramesRestored r j).flatMap G1Frame.bits))
        .aProbe .p0 false false false (g1AWalkCtx r b v)) 5 =
    g1AlignedConfig (encodeG1 r).length
      (4 * (g1AWalkCursor r j + 1) + 3) (by omega)
      (g1ListTape ((g1AWalkFramesRestored r j).flatMap G1Frame.bits))
      .aIns .p3 false false false (g1AWalkCtx r b v') := by
    have h := g1CS_aProbe_latch (encodeG1 r).length
      (g1AWalkProbePre r j)
      ((r.vals.drop (j + 2)).map G1Frame.data ++
        [.output false, .finish, .blank]) v' (g1AWalkCtx r b v)
      (by rw [hLprobe]; omega)
    rw [g1AWalkSplit_restored_probe r j v' hnext hdv'] at h
    simpa only [hLprobe, g1AWalkCtx_withVB] using h
  have hG : TM.runConfig (M := G1M)
      (g1AlignedConfig (encodeG1 r).length
        (4 * (g1AWalkCursor r j + 1) + 3) (by omega)
        (g1ListTape ((g1AWalkFramesRestored r j).flatMap G1Frame.bits))
        .aIns .p3 false false false (g1AWalkCtx r b v')) 4 =
    g1AlignedConfig (encodeG1 r).length
      (4 * (g1AWalkCursor r j + 1) - 1) (by omega)
      (g1ListTape ((g1AWalkFrames r (j + 1)).flatMap G1Frame.bits))
      .aSeekOut .p3 false false false (g1AWalkCtx r b v') := by
    have h := g1CS_aInstall_cursor (encodeG1 r).length
      (g1AWalkProbePre r j)
      ((r.vals.drop (j + 2)).map G1Frame.data ++
        [.output false, .finish, .blank]) (.data v') (g1AWalkCtx r b v')
      (by rw [hLprobe]; omega) (by rw [hLprobe]; omega)
    rw [g1AWalkSplit_restored_probe r j v' hnext hdv',
      g1AWalkSplit_succ r j] at h
    simpa only [hLprobe] using h
  rw [show g1AWalkRoundSteps r j =
      g1AWalkRoundPrefixSteps r j + (5 + 4) by
        simp [g1AWalkRoundSteps, g1AWalkRoundPrefixSteps],
    runConfig_add, g1CS_aWalk_round_prefix_exact r b j hj1 (by omega) v hv,
    runConfig_add, hF, hG]
  simp only [g1AWalkConfig, g1AWalkCursor]
  congr 1

set_option maxHeartbeats 1000000 in
/-- **One exact successor-data OOB round.**  An operand-A index remains, but
slot `j+1` is absent.  The current cursor is restored, no new cursor is
installed, and the machine stops at the existing `bOOB` endpoint. -/
theorem g1CS_aWalk_round_oob_exact (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j < r.arg1) (hlast : j + 1 = r.vals.length) (v : Bool)
    (hv : r.vals[j]? = some v) :
    TM.runConfig (M := G1M)
        (g1AWalkConfig r b j (by omega) (by omega) v hv)
        (g1AWalkRoundOOBSteps r j) =
      g1AWalkOOBConfig r b j hj1 (by omega) v hv := by
  have hLprobe := g1AWalkProbePre_length r j hj1 (by omega)
  have hsafe := g1AWalkCursor_safe r j (by omega)
  have hP : TM.runConfig (M := G1M)
      (g1AlignedConfig (encodeG1 r).length
        (4 * (g1AWalkCursor r j + 1)) (by omega)
        (g1ListTape ((g1AWalkFramesRestored r j).flatMap G1Frame.bits))
        .aProbe .p0 false false false (g1AWalkCtx r b v)) 4 =
    g1AWalkOOBConfig r b j hj1 (by omega) v hv := by
    have h := g1CS_aProbe_oob (encodeG1 r).length (g1AWalkProbePre r j)
      [.finish, .blank] (g1AWalkCtx r b v) (by rw [hLprobe]; omega)
    rw [g1AWalkSplit_restored_oob r j hlast] at h
    simpa only [g1AWalkOOBConfig, hLprobe,
      show 4 * (g1AWalkCursor r j + 1) + 4 =
        4 * (g1AWalkCursor r j + 2) by omega] using h
  rw [show g1AWalkRoundOOBSteps r j =
      g1AWalkRoundPrefixSteps r j + 4 by
        simp [g1AWalkRoundOOBSteps, g1AWalkRoundPrefixSteps],
    runConfig_add, g1CS_aWalk_round_prefix_exact r b j hj1 (by omega) v hv, hP]

/-! ## The operand-index exhaustion boundary -/

/-- Prefix before the `argSep` that opens the operand-A field. -/
def g1AWalkExhaustPre (r : G1Request) : List G1Frame :=
  G1Frame.bof :: List.replicate r.tag.units G1Frame.tag

@[simp] theorem g1AWalkExhaustPre_length (r : G1Request) :
    (g1AWalkExhaustPre r).length = r.tag.units + 1 := by
  simp [g1AWalkExhaustPre]

/-- `Σᴬ(arg1)` in the exact two-boundary shape consumed by the exhaustion seek. -/
theorem g1AWalkSplit_exhaust (r : G1Request) :
    g1AWalkExhaustPre r ++ G1Frame.argSep ::
        g1AWalkInnerRun r.arg1 ++ G1Frame.argSep ::
        g1AWalkOuterRun r r.arg1 ++
        G1Frame.cursor :: g1AWalkTail r r.arg1 =
      g1AWalkFrames r r.arg1 := by
  simp [g1AWalkExhaustPre, g1AWalkFrames, g1AWalkOperand1,
    g1AWalkInnerRun, g1AWalkOuterRun, g1AWalkTail, g1TagRouteFrames,
    List.append_assoc]

set_option maxHeartbeats 1000000 in
/-- **Exact operand-index exhaustion.**  At `j = arg1`, the mixed seek stops at
the opening operand-A `argSep` in local mode `aExh`.  It performs no cursor
return, terminal restore or A-repair. -/
theorem g1CS_aWalk_exhaust_exact (r : G1Request) (b v : Bool)
    (hj : r.arg1 < r.vals.length) (hv : r.vals[r.arg1]? = some v) :
    TM.runConfig (M := G1M)
        (g1AWalkConfig r b r.arg1 (Nat.le_refl _) hj v hv)
        (g1AWalkExhaustSteps r) =
      g1AWalkExhaustConfig r b v hj hv := by
  have hLpre := g1AWalkExhaustPre_length r
  have hLinner := g1AWalkInnerRun_length r.arg1
  have hLouter := g1AWalkOuterRun_length r r.arg1 (by omega)
  have hsafe := g1AWalkCursor_safe r r.arg1 hj
  have h := g1CS_aWalk_seek_exhaust (encodeG1 r).length
    (g1AWalkExhaustPre r) (g1AWalkInnerRun r.arg1)
    (g1AWalkOuterRun r r.arg1)
    (G1Frame.cursor :: g1AWalkTail r r.arg1) (g1AWalkCtx r b v)
    (g1AWalkOuterRun_skip r r.arg1) (g1AWalkInnerRun_skip r.arg1)
    (by rw [hLpre, hLinner, hLouter];
        simp only [g1AWalkCursor] at hsafe
        omega)
  rw [g1AWalkSplit_exhaust r] at h
  simp only [hLpre, hLinner, hLouter,
    show 4 * (r.tag.units + 1 +
        (r.arg1 + (r.arg2 + r.arg1 + 1) + 1)) + 3 =
      4 * g1AWalkCursor r r.arg1 - 1 by simp only [g1AWalkCursor]; omega,
    show 4 * (r.arg1 + (r.arg2 + r.arg1 + 1) + 1) + 4 =
      8 * r.arg1 + 4 * r.arg2 + 12 by omega] at h
  exact h

/-! ## Preservation and unchanged-clock projections -/

/-- The normal round pins the whole canonical successor layout, preserves the
gate residual, re-latches `vB`, retains one designated cursor, and advances the
operand-A spent/index counts by exactly one. -/
theorem g1CS_aWalk_round_preservation (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j < r.arg1) (hnext : j + 1 < r.vals.length) (v v' : Bool)
    (hv : r.vals[j]? = some v) (hv' : r.vals[j + 1]? = some v') :
    let out := TM.runConfig (M := G1M)
      (g1AWalkConfig r b j (by omega) (by omega) v hv)
      (g1AWalkRoundSteps r j)
    (g1AWalkConfig r b j (by omega) (by omega) v hv).state.snd.ctx.vB = v ∧
      out.tape = g1ListTape
        ((g1AWalkFrames r (j + 1)).flatMap G1Frame.bits) ∧
      out.state.snd.ctx.res = g1Residual r.tag b ∧
      out.state.snd.ctx.vB = v' ∧
      (g1AWalkFrames r (j + 1)).count .cursor = 1 ∧
      (g1AWalkFrames r (j + 1)).count .spent = j + 1 ∧
      (g1AWalkFrames r (j + 1)).count .index =
        (r.arg1 - (j + 1)) + r.arg2 ∧
      (g1AWalkOperand1 r (j + 1)).count .index = r.arg1 - (j + 1) := by
  dsimp only
  rw [g1CS_aWalk_round_exact r b j hj1 hnext v v' hv hv']
  exact ⟨rfl, rfl, g1AWalkConfig_res _ _ _ _ _ _ _, rfl,
    g1AWalkFrames_count_cursor _ _, g1AWalkFrames_count_spent _ _,
    g1AWalkFrames_count_index _ _, g1AWalkOperand1_count_index _ _⟩

/-- The data-OOB endpoint is a different boundary: restored data, no cursor,
one additional spent operand-A unit, the same residual and the current `vB`. -/
theorem g1CS_aWalk_round_oob_preservation (r : G1Request) (b : Bool) (j : Nat)
    (hj1 : j < r.arg1) (hlast : j + 1 = r.vals.length) (v : Bool)
    (hv : r.vals[j]? = some v) :
    let out := TM.runConfig (M := G1M)
      (g1AWalkConfig r b j (by omega) (by omega) v hv)
      (g1AWalkRoundOOBSteps r j)
    out.tape = g1ListTape
        ((g1AWalkFramesRestored r j).flatMap G1Frame.bits) ∧
      out.state.snd.mode = .bOOB ∧
      out.state.snd.ctx.res = g1Residual r.tag b ∧
      out.state.snd.ctx.vB = v ∧
      (g1AWalkFramesRestored r j).count .cursor = 0 ∧
      (g1AWalkFramesRestored r j).count .spent = j + 1 ∧
      (g1AWalkFramesRestored r j).count .index =
        (r.arg1 - j - 1) + r.arg2 := by
  dsimp only
  rw [g1CS_aWalk_round_oob_exact r b j hj1 hlast v hv]
  exact ⟨rfl, rfl, g1AWalkOOBConfig_res _ _ _ _ _ _ _, rfl,
    g1AWalkFramesRestored_count_cursor _ _,
    g1AWalkFramesRestored_count_spent _ _,
    g1AWalkFramesRestored_count_index _ _⟩

/-- Every normal one-round cost fits the unchanged public `g1Clock`. -/
theorem g1AWalkRoundSteps_le_clock (r : G1Request) (j : Nat)
    (hj1 : j < r.arg1) :
    g1AWalkRoundSteps r j ≤ g1Clock (encodeG1 r).length := by
  have hlin : g1AWalkRoundSteps r j ≤ 32 * ((encodeG1 r).length + 1) := by
    rw [encodeG1_length]
    simp only [g1AWalkRoundSteps]
    omega
  have hx : (encodeG1 r).length + 1 ≤ ((encodeG1 r).length + 1) ^ 2 := by
    simpa [pow_two] using Nat.le_mul_of_pos_right
      ((encodeG1 r).length + 1) (by omega)
  rw [g1Clock]
  omega

/-- Every successor-data OOB round cost fits the unchanged public clock. -/
theorem g1AWalkRoundOOBSteps_le_clock (r : G1Request) (j : Nat)
    (hj1 : j < r.arg1) :
    g1AWalkRoundOOBSteps r j ≤ g1Clock (encodeG1 r).length := by
  have hle : g1AWalkRoundOOBSteps r j ≤ g1AWalkRoundSteps r j := by
    simp [g1AWalkRoundOOBSteps, g1AWalkRoundSteps]
  exact hle.trans (g1AWalkRoundSteps_le_clock r j hj1)

/-- The local operand-index exhaustion seek also fits the unchanged clock. -/
theorem g1AWalkExhaustSteps_le_clock (r : G1Request) :
    g1AWalkExhaustSteps r ≤ g1Clock (encodeG1 r).length := by
  have hlin : g1AWalkExhaustSteps r ≤ 32 * ((encodeG1 r).length + 1) := by
    rw [encodeG1_length]
    simp only [g1AWalkExhaustSteps]
    omega
  have hx : (encodeG1 r).length + 1 ≤ ((encodeG1 r).length + 1) ^ 2 := by
    simpa [pow_two] using Nat.le_mul_of_pos_right
      ((encodeG1 r).length + 1) (by omega)
  rw [g1Clock]
  omega

/-! ## One real-initial composition and literal probes -/

/-- One unary real-initial S5 installation followed by exactly one S6 round.
This is a fixed two-capstone composition, not an iteration or driver. -/
theorem g1CS_readA_round_unary_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .input ∨ r.tag = .not) (harg : 0 < r.arg1)
    (v v' : Bool) (rest : List Bool) (hvals : r.vals = v :: v' :: rest) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1AUnaryCursorSteps r + g1AWalkRoundSteps r 0) =
      g1AWalkConfig r false 1 (by omega) (by rw [hvals]; simp) v'
        (by rw [hvals]; simp) := by
  have h0 : r.vals[0]? = some v := by rw [hvals]; simp
  have h1 : r.vals[1]? = some v' := by rw [hvals]; simp
  rw [runConfig_add,
    g1CS_readA_sigma0_unary_exact r hc ht v (v' :: rest) hvals,
    g1CS_aWalk_round_exact r false 0 harg (by rw [hvals]; simp) v v' h0 h1]

namespace G1AWalkRoundExamples

/-- Canonical literal used for a normal round and the local exhaustion probe. -/
def reqNormal : G1Request := ⟨.input, 1, 0, [false, true]⟩

/-- Canonical literal whose successor data is absent while one A-index remains. -/
def reqOOB : G1Request := ⟨.input, 1, 0, [false]⟩

theorem requests_canonical : reqNormal.Canonical ∧ reqOOB.Canonical := by decide

/-- Caller-supplied `Σᴬ(0)` executes one normal round in exactly 45 steps. -/
theorem normal_round_exact :
    TM.runConfig (M := G1M)
        (g1AWalkConfig reqNormal false 0 (by decide) (by decide) false (by decide))
        45 =
      g1AWalkConfig reqNormal false 1 (by decide) (by decide) true (by decide) := by
  simpa [g1AWalkRoundSteps, reqNormal] using
    g1CS_aWalk_round_exact reqNormal false 0 (by decide) (by decide)
      false true (by decide) (by decide)

/-- The same normal literal composed from the real initial configuration through
S5 and exactly one S6 round, with no further step. -/
theorem normal_round_from_initial_exact :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqNormal))) 196 =
      g1AWalkConfig reqNormal false 1 (by decide) (by decide) true (by decide) := by
  have h := g1CS_readA_round_unary_exact reqNormal requests_canonical.1
    (Or.inl rfl) (by decide) false true [] rfl
  simpa [g1AUnaryCursorSteps, g1UActivatedSteps, g1UReadASteps,
    g1ReadARouteSteps, g1ReadBHandoffSteps, g1AUnaryRewindSteps,
    g1AWalkRoundSteps, reqNormal, g1ALiveInstallSteps] using h

/-- Caller-supplied `Σᴬ(0)` reaches the exact cursor-free `bOOB` endpoint in
40 steps; this is data OOB, not operand-index exhaustion. -/
theorem oob_round_exact :
    TM.runConfig (M := G1M)
        (g1AWalkConfig reqOOB false 0 (by decide) (by decide) false (by decide))
        40 =
      g1AWalkOOBConfig reqOOB false 0 (by decide) (by decide) false
        (by decide) := by
  simpa [g1AWalkRoundOOBSteps, reqOOB] using
    g1CS_aWalk_round_oob_exact reqOOB false 0 (by decide) (by decide)
      false (by decide)

/-- Caller-supplied `Σᴬ(1)` reaches only the local `aExh` boundary in 20 steps.
No terminal cursor return or repair is composed. -/
theorem exhaust_exact :
    TM.runConfig (M := G1M)
        (g1AWalkConfig reqNormal false 1 (by decide) (by decide) true (by decide))
        20 =
      g1AWalkExhaustConfig reqNormal false true (by decide) (by decide) := by
  simpa [g1AWalkExhaustSteps, reqNormal] using
    g1CS_aWalk_exhaust_exact reqNormal false true (by decide) (by decide)

/-- Exact literal costs and the composed real-initial cost all fit the unchanged
public clock. -/
theorem literal_clock_bounds :
    45 ≤ g1Clock (encodeG1 reqNormal).length ∧
      196 ≤ g1Clock (encodeG1 reqNormal).length ∧
      40 ≤ g1Clock (encodeG1 reqOOB).length ∧
      20 ≤ g1Clock (encodeG1 reqNormal).length := by decide

end G1AWalkRoundExamples

end Pnp3.Internal.PsubsetPpoly.TM
