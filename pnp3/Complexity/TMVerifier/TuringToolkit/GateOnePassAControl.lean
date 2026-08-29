import Complexity.TMVerifier.TuringToolkit.GateOneRepairDriver

/-!
# G1 pass A: live entry activation and residual latch

**Progress classification: Infrastructure.**

S1b2b activates the S1b1 calling convention.  `readAStart` now dispatches an
entry context to `aBof` and a result context to `combineStart`.  The existing
caller-supplied rescan theorems remain reusable, and this module composes them
with the merged unary, constant and binary repaired routes from the real
`G1M.initialConfig`.

**The four capstones**, for `u = r.tag.units`:

| what | from | steps | to |
|------|------|-------|----|
| the tag recount | `aBof` | `4 * (u + 2)` | `g1AOpMode r.tag` |
| the operation latch | `g1AOpMode t`, `t ≠ const` | `1` | `aInstallStart`, residual latched |
| the whole entry | `aBof` | `4 * (u + 2) + 1` | `aInstallStart`, residual latched |
| the `const` rescan | `aBof` | `16` | `g1RejectState` |

In every one of them the tape is **bit-for-bit the caller's tape**: the recount
is read-only and the latch writes back the cell it scans.  `vB` survives the
latch untouched — it is the deferred walk's value slot — and only the pair
`(pass, crossed)` changes.

S4 changes only the next one-step atom: `aInstallStart` now enters
`aInsSeek .p0` in place, preserving head, tape and context.  The scan/probe and
writer composition lives in `GateOneAWalkInstallAtoms`; this module still
executes no operand-A scan, writer, normal walk, repair, combine, output or
acceptance row.  The `const` rejection is a *local* fact about an `aBof`
configuration its real route never reaches; the result-ready route bypasses
pass A and reaches `combineStart` carrying `g1ResultCtx b`.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

/-- Head positions that are equal as numbers give the same configuration; the
safety proofs are irrelevant. -/
private theorem g1AConfig_congr (n h h' : Nat)
    (hh : h < G1M.tapeLength n) (hh' : h' < G1M.tapeLength n) (heq : h = h')
    (tape : Fin (G1M.tapeLength n) → Bool) (mode : G1Mode)
    (position : G1FramePosition) (b0 b1 b2 : Bool) (ctx : G1Ctx) :
    g1AlignedConfig n h hh tape mode position b0 b1 b2 ctx =
      g1AlignedConfig n h' hh' tape mode position b0 b1 b2 ctx := by
  subst heq; rfl

/-! ## The two executed one-step atoms

Each is one generic aligned-step adapter applied to one standalone tuple lemma
of `GateOneControl`; `g1Transition` is never unfolded. -/

/-- **The operand-1 operation latch, executed.**  One stationary step writes the
residual of the rescanned tag and the operand-2 value latched in `vB` into the
two spare context bits; the tape, the head and `vB` are untouched. -/
theorem g1CS_step_aOp (n h : Nat) (hh : h < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (t : G1Tag) (ht : t ≠ .const)
    (ctx : G1Ctx) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n h hh tape (g1AOpMode t) .p0 false false false ctx)
        1 =
      g1AlignedConfig n h hh tape .aInstallStart .p0 false false false
        (ctx.withRes (g1Residual t ctx.vB)) := by
  rw [runConfig_one]
  have hstep := g1CS_aligned_step_stay n h hh tape
    (g1State (g1AOpMode t) .p0 false false false ctx)
    (g1AInstallState (ctx.withRes (g1Residual t ctx.vB))) (tape ⟨h, hh⟩)
    (fun phase => g1Transition_aOp phase t ht .p0 false false false _ ctx)
  rwa [writeCell_self] at hstep

/-- **The live S4 entry, executed.**  One stationary step enters the aligned
installation scan without changing the head, tape or latched context. -/
theorem g1CS_step_aInstallStart (n h : Nat) (hh : h < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n h hh tape .aInstallStart .p0 false false false ctx)
        1 =
      g1AlignedConfig n h hh tape .aInsSeek .p0 false false false ctx := by
  rw [runConfig_one]
  have hstep := g1CS_aligned_step_stay n h hh tape
    (g1AInstallState ctx) (g1AInsSeekState ctx) (tape ⟨h, hh⟩)
    (fun phase => g1Transition_aInstallStart_live phase .p0 false false false _ ctx)
  rwa [writeCell_self] at hstep

/-! ## The pass-A rescan, on a caller-supplied frame word

The A-counters read the same prefix `g1TagRouteFrames r` the pass-B rescan
reads — the anchor and the unary tag run — so the runs below are the generic
`g1FrameScanner_scanFrames` at the frame-level route of `GateOneRouting`.  The
prefix `pre` and the suffix are the caller's: no theorem here says which word is
on the tape, only that the machine folds the tag run it physically reads. -/

/-- **The A-specific tag recount, executed.**  Four steps per frame from the
anchor read `aBof`, ending in the operation latch the closing `argSep` selects,
with the tape untouched and the whole context threaded through.  The tag enters
only as a fact about the request whose frames the caller put on the tape;
nothing about it is carried in `G1State`. -/
theorem g1CS_aTagRescan_exact (n : Nat) (pre suffix : List G1Frame)
    (r : G1Request) (ht : r.tag ≠ .const) (ctx : G1Ctx)
    (hsafe : 4 * (pre.length + (r.tag.units + 2)) < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * pre.length) (by omega)
          (g1ListTape (n := n)
            ((pre ++ g1TagRouteFrames r ++ suffix).flatMap G1Frame.bits))
          .aBof .p0 false false false ctx)
        (4 * (r.tag.units + 2)) =
      g1AlignedConfig n (4 * (pre.length + (r.tag.units + 2))) hsafe
        (g1ListTape (n := n)
          ((pre ++ g1TagRouteFrames r ++ suffix).flatMap G1Frame.bits))
        (g1AOpMode r.tag) .p0 false false false ctx := by
  have hlen : (g1TagRouteFrames r).length = r.tag.units + 2 :=
    g1TagRouteFrames_length r
  have hsafe' : 4 * (pre.length + (g1TagRouteFrames r).length) <
      G1M.tapeLength n := by rw [hlen]; exact hsafe
  have hscan := g1FrameScanner_scanFrames n pre (g1TagRouteFrames r) suffix .aBof
    ctx ((g1FrameScanner_validPath _ _).mpr (g1ATagRoute_validPath r ht)) hsafe'
  simp only [g1AlignedFrame_eq, g1FrameScanner_advanceList,
    g1ATagRoute_advance] at hscan
  refine Eq.trans ?_ (g1AConfig_congr n _ _ hsafe' hsafe (by rw [hlen]) _
    (g1AOpMode r.tag) .p0 false false false ctx)
  rw [show 4 * (r.tag.units + 2) = 4 * (g1TagRouteFrames r).length from
    by rw [hlen]]
  exact hscan

/-- **The whole pass-A entry, executed.**  Exactly `4u + 9` genuine
steps recount the tag run and latch `g1Residual r.tag ctx.vB` into the two spare
context bits, stopping on the first cell after the `argSep` that closes the run
— the first cell of the operand-1 field — with the tape bit-for-bit the
caller's and `ctx.vB` untouched. -/
theorem g1CS_passA_entry_exact (n : Nat) (pre suffix : List G1Frame)
    (r : G1Request) (ht : r.tag ≠ .const) (ctx : G1Ctx)
    (hsafe : 4 * (pre.length + (r.tag.units + 2)) < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * pre.length) (by omega)
          (g1ListTape (n := n)
            ((pre ++ g1TagRouteFrames r ++ suffix).flatMap G1Frame.bits))
          .aBof .p0 false false false ctx)
        (4 * (r.tag.units + 2) + 1) =
      g1AlignedConfig n (4 * (pre.length + (r.tag.units + 2))) hsafe
        (g1ListTape (n := n)
          ((pre ++ g1TagRouteFrames r ++ suffix).flatMap G1Frame.bits))
        .aInstallStart .p0 false false false
        (ctx.withRes (g1Residual r.tag ctx.vB)) := by
  rw [runConfig_add, g1CS_aTagRescan_exact n pre suffix r ht ctx hsafe]
  exact g1CS_step_aOp n _ hsafe _ r.tag ht ctx

/-- **The latched residual is the gate's residual**, and **the operand-2 value
survives** in the third context bit, which the deferred operand-1 walk uses as
its value latch. -/
theorem g1CS_passA_entry_ctx (r : G1Request) (ctx : G1Ctx) :
    (ctx.withRes (g1Residual r.tag ctx.vB)).res = g1Residual r.tag ctx.vB ∧
      (ctx.withRes (g1Residual r.tag ctx.vB)).vB = ctx.vB :=
  ⟨G1Ctx.res_withRes ctx _, rfl⟩

/-- **The local `const` pass-A rescan rejects, executed.**  From the
anchor read `aBof` — in *any* context — exactly `16` genuine steps (four frames,
`bof · tag · tag · argSep`) drive the machine into the literal `g1RejectState`
with the tape bit-for-bit the caller's.  This is the executed counterpart of the
frame-table equation `g1ATagRoute_advance_const`.

**It is a *local* rejection and nothing more.**  The starting configuration is
one nothing reaches: a `const` request's live route is decided in pass B,
  rewinds through `readAResetStart`, and takes the result branch to
  `combineStart` (`g1CS_activate_const_exact`).  Nothing here says a `const` request is
rejected by the machine; it says the A-counters have no `const` row,
physically — which is exactly why the `const` filler row of `g1Residual` is
never consumed. -/
theorem g1CS_passA_const_reject_exact (n : Nat) (pre suffix : List G1Frame)
    (r : G1Request) (ht : r.tag = .const) (ctx : G1Ctx)
    (hsafe : 4 * (pre.length + 4) < G1M.tapeLength n) :
    (TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * pre.length) (by omega)
          (g1ListTape (n := n)
            ((pre ++ g1TagRouteFrames r ++ suffix).flatMap G1Frame.bits))
          .aBof .p0 false false false ctx) 16).state.snd = g1RejectState ∧
      (TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * pre.length) (by omega)
          (g1ListTape (n := n)
            ((pre ++ g1TagRouteFrames r ++ suffix).flatMap G1Frame.bits))
          .aBof .p0 false false false ctx) 16).tape =
        g1ListTape (n := n)
          ((pre ++ g1TagRouteFrames r ++ suffix).flatMap G1Frame.bits) := by
  have hlen : 4 * (g1TagRouteFrames r).length = 16 := by
    rw [g1TagRouteFrames_length, ht]; rfl
  obtain ⟨h, hh, hrun⟩ := g1CS_scan_reject n pre (g1TagRouteFrames r) suffix
    .aBof ctx (g1ATagRoute_rejectPath r ht)
    (by rw [g1TagRouteFrames_length, ht]; exact hsafe)
  rw [g1AlignedFrame_eq, hlen] at hrun
  rw [hrun]
  exact ⟨rfl, rfl⟩

/-! ## Live activation from the real initial configuration -/

/-- The exact live entry boundary: head zero on the initial tape, with the
operand-B value still in the non-result context. -/
def g1ABofConfig (r : G1Request) (b : Bool) :
    Configuration (M := G1M) (encodeG1 r).length :=
  g1AlignedConfig (encodeG1 r).length 0 (g1_route_lt_tapeLength r 0 (by omega))
    (G1M.initialConfig (g1Point (encodeG1 r))).tape
    .aBof .p0 false false false (g1Ctx0.withVB b)

/-- The exact pass-A install boundary.  Operand 1 is still unread; its unary
residual is latched and the operand-B value remains in `vB`. -/
def g1AInstallConfig (r : G1Request) (b : Bool) :
    Configuration (M := G1M) (encodeG1 r).length :=
  g1AlignedConfig (encodeG1 r).length (4 * (r.tag.units + 2))
    (g1_route_lt_tapeLength r _ (by omega))
    (G1M.initialConfig (g1Point (encodeG1 r))).tape
    .aInstallStart .p0 false false false
    ((g1Ctx0.withVB b).withRes (g1Residual r.tag b))

/-- The exact live installation-scan entry, one step after
`g1AInstallConfig`: same aligned head, canonical tape and latched context. -/
def g1AInstallSeekConfig (r : G1Request) (b : Bool) :
    Configuration (M := G1M) (encodeG1 r).length :=
  g1AlignedConfig (encodeG1 r).length (4 * (r.tag.units + 2))
    (g1_route_lt_tapeLength r _ (by omega))
    (G1M.initialConfig (g1Point (encodeG1 r))).tape
    .aInsSeek .p0 false false false
    ((g1Ctx0.withVB b).withRes (g1Residual r.tag b))

/-- The exact result-ready boundary of the `const` bypass. -/
def g1CombineConfig (r : G1Request) (b : Bool) :
    Configuration (M := G1M) (encodeG1 r).length :=
  g1AlignedConfig (encodeG1 r).length 0 (g1_route_lt_tapeLength r 0 (by omega))
    (G1M.initialConfig (g1Point (encodeG1 r))).tape
    .combineStart .p0 false false false (g1ResultCtx b)

@[simp] theorem g1ABofConfig_head (r : G1Request) (b : Bool) :
    ((g1ABofConfig r b).head : Nat) = 0 := rfl

@[simp] theorem g1ABofConfig_ctx (r : G1Request) (b : Bool) :
    (g1ABofConfig r b).state.snd.ctx = g1Ctx0.withVB b := rfl

@[simp] theorem g1AInstallConfig_head (r : G1Request) (b : Bool) :
    ((g1AInstallConfig r b).head : Nat) = 4 * (r.tag.units + 2) := rfl

@[simp] theorem g1AInstallConfig_res (r : G1Request) (b : Bool) :
    (g1AInstallConfig r b).state.snd.ctx.res = g1Residual r.tag b := by
  simp [g1AInstallConfig, g1AlignedConfig, g1AlignedConfigQ, g1State]

@[simp] theorem g1AInstallConfig_vB (r : G1Request) (b : Bool) :
    (g1AInstallConfig r b).state.snd.ctx.vB = b := rfl

@[simp] theorem g1AInstallSeekConfig_head (r : G1Request) (b : Bool) :
    ((g1AInstallSeekConfig r b).head : Nat) = 4 * (r.tag.units + 2) := rfl

@[simp] theorem g1AInstallSeekConfig_res (r : G1Request) (b : Bool) :
    (g1AInstallSeekConfig r b).state.snd.ctx.res = g1Residual r.tag b := by
  simp [g1AInstallSeekConfig, g1AlignedConfig, g1AlignedConfigQ, g1State]

@[simp] theorem g1AInstallSeekConfig_vB (r : G1Request) (b : Bool) :
    (g1AInstallSeekConfig r b).state.snd.ctx.vB = b := rfl

@[simp] theorem g1CombineConfig_ctx (r : G1Request) (b : Bool) :
    (g1CombineConfig r b).state.snd.ctx = g1ResultCtx b := rfl

/-- The three repaired-route totals, extended by exactly the one live dispatch
step. -/
def g1UActivatedSteps (r : G1Request) : Nat := g1UReadASteps r + 1
def g1BActivatedSteps (r : G1Request) : Nat :=
  (if r.arg2 = 0 then g1ZPassASteps r else g1BPassASteps r) + 1
def g1ConstActivatedSteps (r : G1Request) : Nat := g1ConstReadASteps r + 1

/-- Unary repaired routes take the live entry branch in exactly one more step. -/
theorem g1CS_activate_unary_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .input ∨ r.tag = .not) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1UActivatedSteps r) = g1ABofConfig r false := by
  rw [g1UActivatedSteps, runConfig_add,
    g1CS_readA_unary_repaired_exact r hc ht]
  exact g1CS_step_readAStart_entry _ _ _ _ _ rfl

/-- Every successful binary repaired route takes the entry branch in exactly
one more step; the operand-B value cannot be delivered to `combineStart`. -/
theorem g1CS_activate_binary_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BActivatedSteps r) = g1ABofConfig r b := by
  rw [g1BActivatedSteps, runConfig_add,
    g1CS_readB_repaired_common r hc ht b hb]
  exact g1CS_step_readAStart_entry _ _ _ _ _ rfl

/-- Run-level no-wrong-exit closure: a successful operand-B route is at the
pass-A anchor scan after activation, never at the final-result boundary. -/
theorem g1CS_activate_binary_not_result (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BActivatedSteps r)).state.snd.mode = .aBof ∧
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BActivatedSteps r)).state.snd.mode ≠ .combineStart := by
  rw [g1CS_activate_binary_exact r hc ht b hb]
  exact ⟨rfl, fun h => G1Mode.noConfusion h⟩

/-- A repaired `const` route carries `g1ResultCtx` and takes the other branch
in exactly one more step.  It never enters the pass-A scan. -/
theorem g1CS_activate_const_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .const) (b : Bool) (hs : r.spec = some b) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ConstActivatedSteps r) = g1CombineConfig r b := by
  rw [g1ConstActivatedSteps, runConfig_add,
    g1CS_const_repaired_exact r hc ht b hs]
  exact g1CS_step_readAStart_result _ _ _ _ _ rfl

/-- The pass-A scan, reached from the live entry, latches the exact
residual on the real initial tape without reading operand 1. -/
theorem g1CS_passA_entry_initial_exact (r : G1Request) (ht : r.tag ≠ .const)
    (b : Bool) :
    TM.runConfig (M := G1M) (g1ABofConfig r b)
        (4 * (r.tag.units + 2) + 1) = g1AInstallConfig r b := by
  have h := g1CS_passA_entry_exact (encodeG1 r).length []
    (g1TagRouteRest r) r ht (g1Ctx0.withVB b)
    (by simpa using g1_route_lt_tapeLength r (r.tag.units + 2) (by omega))
  rw [List.nil_append, g1TagRoute_split] at h
  have htape := g1ListTape_validation_eq_initial r
  simp only [g1ValidationFrames] at htape
  rw [htape] at h
  simpa only [g1ABofConfig, g1AInstallConfig, List.length_nil, Nat.zero_add,
    G1Ctx.withVB_vB] using h

/-- The residual-latched real-tape boundary takes its one exact live step into
the S3b1 installation scan. -/
theorem g1CS_aInstall_entry_initial_exact (r : G1Request) (b : Bool) :
    TM.runConfig (M := G1M) (g1AInstallConfig r b) 1 =
      g1AInstallSeekConfig r b := by
  simpa [g1AInstallConfig, g1AInstallSeekConfig] using
    g1CS_step_aInstallStart (encodeG1 r).length (4 * (r.tag.units + 2))
      (g1_route_lt_tapeLength r _ (by omega))
      (G1M.initialConfig (g1Point (encodeG1 r))).tape
      ((g1Ctx0.withVB b).withRes (g1Residual r.tag b))

/-- Real unary routes reach the exact install boundary with their residual
latched and operand 1 unread. -/
theorem g1CS_install_unary_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .input ∨ r.tag = .not) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1UActivatedSteps r + (4 * (r.tag.units + 2) + 1)) =
      g1AInstallConfig r false := by
  rw [runConfig_add, g1CS_activate_unary_exact r hc ht]
  exact g1CS_passA_entry_initial_exact r
    (by rcases ht with h | h <;> rw [h] <;> decide) false

/-- Real successful binary routes reach the same exact install boundary with
the residual selected by the physically read operand-B value. -/
theorem g1CS_install_binary_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BActivatedSteps r + (4 * (r.tag.units + 2) + 1)) =
      g1AInstallConfig r b := by
  rw [runConfig_add, g1CS_activate_binary_exact r hc ht b hb]
  exact g1CS_passA_entry_initial_exact r
    (by rcases ht with h | h <;> rw [h] <;> decide) b

private theorem g1PAClock_sq (k : Nat) :
    (k + 1) ^ 2 = k ^ 2 + (2 * k + 1) := by
  rw [Nat.pow_two, Nat.pow_two, Nat.mul_add, Nat.add_mul, Nat.add_mul]
  omega

private theorem g1PAClock_quad (N : Nat) :
    g1Clock (4 * N) = 8192 * N ^ 2 + (4096 * N + 1024) := by
  rw [g1Clock, g1PAClock_sq, Nat.mul_pow, show (4 : Nat) ^ 2 = 16 from rfl]
  omega

private theorem g1PAClock_eq (r : G1Request) :
    g1Clock (encodeG1 r).length =
      8192 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 6) ^ 2 +
        (4096 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 6) + 1024) := by
  rw [encodeG1_length r, g1PAClock_quad]

theorem g1UActivatedSteps_le_clock (r : G1Request) :
    g1UActivatedSteps r + (4 * (r.tag.units + 2) + 1) ≤
      g1Clock (encodeG1 r).length := by
  have hlen := encodeG1_length r
  rw [g1PAClock_eq]
  simp only [g1UActivatedSteps, g1UReadASteps, g1ReadARouteSteps,
    g1ReadBHandoffSteps, g1AUnaryRewindSteps, hlen]
  omega

theorem g1ConstActivatedSteps_le_clock (r : G1Request) :
    g1ConstActivatedSteps r ≤ g1Clock (encodeG1 r).length := by
  have hlen := encodeG1_length r
  rw [g1PAClock_eq]
  simp only [g1ConstActivatedSteps, g1ConstReadASteps, g1ConstRouteSteps,
    g1FieldRouteSteps, g1ReadBHandoffSteps, g1AConstRewindSteps, hlen]
  omega

theorem g1BActivatedSteps_le_clock (r : G1Request) :
    g1BActivatedSteps r + (4 * (r.tag.units + 2) + 1) ≤
      g1Clock (encodeG1 r).length := by
  have hlen := encodeG1_length r
  have hsq : 8 * r.arg2 ^ 2 ≤
      8192 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 6) ^ 2 :=
    Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) 2)
  rw [g1PAClock_eq]
  simp only [g1BActivatedSteps, g1BPassASteps, g1BReadSteps,
    g1InstallScanSteps, g1ZPassASteps, g1ReadBSteps, g1RepairSteps,
    g1ReadBHandoffSteps, hlen]
  split_ifs <;> omega

/-! ## All-literal probes

Five caller-supplied words, one per gate tag, each the canonical frame word of a
literal request plus its trailing `blank`.  Every step count, head position and
frame is a literal.  These remain local caller-supplied probes of the rescan;
they are not the expanded real-initial literal matrix deferred to S1c. -/

namespace G1PassAControlExamples

/-- The five literal requests, one per tag.  Each is canonical, so its frame
word is a word the encoder really writes. -/
def aInputExample : G1Request := ⟨.input, 0, 0, [true]⟩
def aNotExample : G1Request := ⟨.not, 0, 0, [true]⟩
def aAndExample : G1Request := ⟨.and, 0, 0, [true]⟩
def aOrExample : G1Request := ⟨.or, 0, 0, [true]⟩
def aConstExample : G1Request := ⟨.const, 1, 0, []⟩

theorem examples_canonical :
    aInputExample.Canonical ∧ aNotExample.Canonical ∧ aAndExample.Canonical ∧
      aOrExample.Canonical ∧ aConstExample.Canonical := by decide

/-- The **encoded input length** parameter of each probe: eight, ten, eleven and
twelve frames for `input`, `not`, `and` and `or`, and nine for `const`.
Physical configurations use `G1M.tapeLength` of it, not a tape of that length. -/
theorem example_lengths :
    (encodeG1 aInputExample).length = 32 ∧ (encodeG1 aNotExample).length = 40 ∧
      (encodeG1 aAndExample).length = 44 ∧ (encodeG1 aOrExample).length = 48 ∧
      (encodeG1 aConstExample).length = 36 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (rw [encodeG1_length]; rfl)

/-- Every cell the probes touch is far inside the physical tape, and the bound
is *derived* from an encoded length rather than assumed. -/
theorem probe_safe {m k : Nat} (hk : k ≤ 52) : k < G1M.tapeLength (32 + m) :=
  g1_lt_tapeLength (by omega)

/-- **`input`: the residual is the identity.**  Thirteen steps — `bof · tag ·
argSep`, then the latch — from head `0` to head `12`, whatever the caller's
operand-2 bit `b`. -/
theorem input_latch (b : Bool) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig 32 0 (probe_safe (m := 0) (by omega))
          (g1ListTape (n := 32)
            ((g1TagRouteFrames aInputExample ++
              g1TagRouteRest aInputExample).flatMap G1Frame.bits))
          .aBof .p0 false false false (g1Ctx0.withVB b)) 13 =
      g1AlignedConfig 32 12 (probe_safe (m := 0) (by omega))
        (g1ListTape (n := 32)
          ((g1TagRouteFrames aInputExample ++
            g1TagRouteRest aInputExample).flatMap G1Frame.bits))
        .aInstallStart .p0 false false false
        ((g1Ctx0.withVB b).withRes .idA) := by
  have h := g1CS_passA_entry_exact 32 [] (g1TagRouteRest aInputExample)
    aInputExample (by decide) (g1Ctx0.withVB b)
    (by simpa using probe_safe (m := 0) (k := 12) (by omega))
  simpa using h

/-- **`not`: the residual is negation.**  Twenty-one steps, head `0 ↦ 20`. -/
theorem not_latch (b : Bool) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig 40 0 (probe_safe (m := 8) (by omega))
          (g1ListTape (n := 40)
            ((g1TagRouteFrames aNotExample ++
              g1TagRouteRest aNotExample).flatMap G1Frame.bits))
          .aBof .p0 false false false (g1Ctx0.withVB b)) 21 =
      g1AlignedConfig 40 20 (probe_safe (m := 8) (by omega))
        (g1ListTape (n := 40)
          ((g1TagRouteFrames aNotExample ++
            g1TagRouteRest aNotExample).flatMap G1Frame.bits))
        .aInstallStart .p0 false false false
        ((g1Ctx0.withVB b).withRes .notA) := by
  have h := g1CS_passA_entry_exact 40 [] (g1TagRouteRest aNotExample)
    aNotExample (by decide) (g1Ctx0.withVB b)
    (by simpa using probe_safe (m := 8) (k := 20) (by omega))
  simpa using h

/-- **`and` with `vB = false`: the absorbing residual.**  Twenty-five steps,
head `0 ↦ 24`, and the latched context is *literally* `g1ResultCtx false` — the
aliasing `g1ResultCtx_eq_andFalse_res` records.  The live successor is
`aInsSeek`, whose installation path does not branch on `pass`. -/
theorem and_false_latch :
    TM.runConfig (M := G1M)
        (g1AlignedConfig 44 0 (probe_safe (m := 12) (by omega))
          (g1ListTape (n := 44)
            ((g1TagRouteFrames aAndExample ++
              g1TagRouteRest aAndExample).flatMap G1Frame.bits))
          .aBof .p0 false false false (g1Ctx0.withVB false)) 25 =
      g1AlignedConfig 44 24 (probe_safe (m := 12) (by omega))
        (g1ListTape (n := 44)
          ((g1TagRouteFrames aAndExample ++
            g1TagRouteRest aAndExample).flatMap G1Frame.bits))
        .aInstallStart .p0 false false false (g1ResultCtx false) := by
  have h := g1CS_passA_entry_exact 44 [] (g1TagRouteRest aAndExample)
    aAndExample (by decide) (g1Ctx0.withVB false)
    (by simpa using probe_safe (m := 12) (k := 24) (by omega))
  simpa using h

/-- **`and` with `vB = true`: the residual is the identity.** -/
theorem and_true_latch :
    TM.runConfig (M := G1M)
        (g1AlignedConfig 44 0 (probe_safe (m := 12) (by omega))
          (g1ListTape (n := 44)
            ((g1TagRouteFrames aAndExample ++
              g1TagRouteRest aAndExample).flatMap G1Frame.bits))
          .aBof .p0 false false false (g1Ctx0.withVB true)) 25 =
      g1AlignedConfig 44 24 (probe_safe (m := 12) (by omega))
        (g1ListTape (n := 44)
          ((g1TagRouteFrames aAndExample ++
            g1TagRouteRest aAndExample).flatMap G1Frame.bits))
        .aInstallStart .p0 false false false
        ((g1Ctx0.withVB true).withRes .idA) := by
  have h := g1CS_passA_entry_exact 44 [] (g1TagRouteRest aAndExample)
    aAndExample (by decide) (g1Ctx0.withVB true)
    (by simpa using probe_safe (m := 12) (k := 24) (by omega))
  simpa using h

/-- **`or` with `vB = true`: the other absorbing residual.**  Twenty-nine steps,
head `0 ↦ 28`. -/
theorem or_true_latch :
    TM.runConfig (M := G1M)
        (g1AlignedConfig 48 0 (probe_safe (m := 16) (by omega))
          (g1ListTape (n := 48)
            ((g1TagRouteFrames aOrExample ++
              g1TagRouteRest aOrExample).flatMap G1Frame.bits))
          .aBof .p0 false false false (g1Ctx0.withVB true)) 29 =
      g1AlignedConfig 48 28 (probe_safe (m := 16) (by omega))
        (g1ListTape (n := 48)
          ((g1TagRouteFrames aOrExample ++
            g1TagRouteRest aOrExample).flatMap G1Frame.bits))
        .aInstallStart .p0 false false false
        ((g1Ctx0.withVB true).withRes .constTrue) := by
  have h := g1CS_passA_entry_exact 48 [] (g1TagRouteRest aOrExample)
    aOrExample (by decide) (g1Ctx0.withVB true)
    (by simpa using probe_safe (m := 16) (k := 28) (by omega))
  simpa using h

/-- **`const` rejects the dormant rescan.**  Sixteen steps on the canonical word
of a real `const` request drive the A-counters into the literal reject sink,
with the word unchanged.  Local: nothing routes a `const` request here. -/
theorem const_reject :
    (TM.runConfig (M := G1M)
        (g1AlignedConfig 36 0 (probe_safe (m := 4) (by omega))
          (g1ListTape (n := 36)
            ((g1TagRouteFrames aConstExample ++
              g1TagRouteRest aConstExample).flatMap G1Frame.bits))
          .aBof .p0 false false false g1Ctx0) 16).state.snd = g1RejectState := by
  have h := g1CS_passA_const_reject_exact 36 [] (g1TagRouteRest aConstExample)
    aConstExample rfl g1Ctx0
    (by simpa using probe_safe (m := 4) (k := 16) (by omega))
  simpa using h.1

/-- **The four latched residuals are pairwise different**, so the probes above
really do distinguish the four operand-1 operations rather than agreeing. -/
theorem latched_residuals_distinct :
    g1Residual aInputExample.tag false = .idA ∧
      g1Residual aNotExample.tag false = .notA ∧
      g1Residual aAndExample.tag false = .constFalse ∧
      g1Residual aOrExample.tag true = .constTrue ∧
      ({.idA, .notA, .constFalse, .constTrue} : Finset G1Residual).card = 4 := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  decide

end G1PassAControlExamples

end Pnp3.Internal.PsubsetPpoly.TM
