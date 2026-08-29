import Complexity.TMVerifier.TuringToolkit.GateOneReadB

/-!
# G1 pass A: the executed capstones of the **dormant** control ABI

**Progress classification: Infrastructure.**

The S1b1 slice declares the pass-A calling convention — twelve modes, the
residual view of the two spare context bits, and the frame rows that connect
them — and this module *executes* it.  Every run below starts from a
**caller-supplied** aligned configuration: nothing here starts from
`G1M.initialConfig`, and nothing can, because the live machine cannot reach a
single one of these modes.

**Why "dormant" is a proved word, not a label.**

* `g1Advance_passA` — no frame-table row crosses into the pass-A family;
* `g1Transition_passA_closed` — no row of the executed control does either;
* `g1Transition_readAStart_idle` — `readAStart`, the handoff S1b2b will turn into
  the dispatch that *does* reach `aBof`, is still a stationary self-loop, and
  `g1CS_runConfig_readA_idle` of `GateOneReadB` executes that.

So the four capstones here are exact statements about configurations a caller
writes down, and they change no existing run: the validation scan, the pass-B
rescan, the cursor walk and the operand-2 repair sweep all execute exactly as
before.

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

**Explicitly deferred and claimed nowhere.**  Operand 1 is not read: the install
handoff self-loops (`g1CS_runConfig_aInstall_idle`).  There is no operand-1
walk, invariant, repair or out-of-range branch, no combine step, no output
write, no `TM.accepts`, no full-clock and no acceptance-gate claim, and no
statement at all about a run from the real initial configuration.  The `const`
rejection is a *local* fact about a configuration nothing reaches; it is not a
claim that the machine rejects `const` requests.  Their live pass-B route
carries `g1ResultCtx b` through the common repair rewind and stops at the
still-idle `readAStart` boundary.
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

/-- **The pass-A install handoff is idle**: it holds its state, head and tape for
the whole remaining budget.  This is the honest boundary of the dormant entry —
operand 1 is not read — and it is also what makes a latched residual harmless,
since the latched context never moves on to anything that reads `pass`. -/
theorem g1CS_runConfig_aInstall_idle (n h : Nat) (hh : h < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx) (k : Nat) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n h hh tape .aInstallStart .p0 false false false ctx)
        k =
      g1AlignedConfig n h hh tape .aInstallStart .p0 false false false ctx :=
  g1CS_runConfig_stable n h hh tape (g1AInstallState ctx)
    (fun phase scan => g1Transition_aInstallStart_idle phase .p0 false false
      false scan ctx) k

/-! ## The dormant rescan, on a caller-supplied frame word

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

/-- **The whole dormant pass-A entry, executed.**  Exactly `4u + 9` genuine
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

/-- **The `const` rescan of the dormant entry rejects, executed.**  From the
anchor read `aBof` — in *any* context — exactly `16` genuine steps (four frames,
`bof · tag · tag · argSep`) drive the machine into the literal `g1RejectState`
with the tape bit-for-bit the caller's.  This is the executed counterpart of the
frame-table equation `g1ATagRoute_advance_const`.

**It is a *local* rejection and nothing more.**  The starting configuration is
one nothing reaches: a `const` request's live route is decided in pass B,
rewinds through `readAResetStart`, and ends at idle `readAStart`
(`GateOneRepairDriver.g1CS_const_repaired_exact`); the pass-A family is
unreachable anyway.  Nothing here says a `const` request is
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

/-! ## All-literal probes

Five caller-supplied words, one per gate tag, each the canonical frame word of a
literal request plus its trailing `blank`.  Every step count, head position and
frame is a literal.  These are probes of a **dormant** table: no run of the
machine from any real configuration reaches the mode they start in. -/

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
aliasing `g1ResultCtx_eq_andFalse_res` records, harmless only because
`aInstallStart` self-loops. -/
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
