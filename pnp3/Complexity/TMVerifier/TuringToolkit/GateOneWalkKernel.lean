import Complexity.TMVerifier.TuringToolkit.FrameScannerSeek
import Complexity.TMVerifier.TuringToolkit.GateOneProbeInstall

/-!
# G1 cursor walk: the remaining kernel instances and atomic macros

**Progress classification: Infrastructure.**

One **normal round** of the walk behind the merged reverse-seek entry `bSeek`,
plus the **terminal exhaustion path** behind the merged `bExh` handoff.
`GateOneControl` supplies the modes and their tuple lemmas; this module
turns them into four more instances of the generic frame kernels —
`g1WalkScanner` (`ReverseFrameScanner`: the reverse seek, stopping on an `index`
at the write handoff `bDec` or on the opening `argSep` at the exhaustion
handoff `bExh`), `g1DecWriter` (`FrameWriter`: `index ↦ spent`),
`g1RestoreWriter b` (`FrameWriter`: `cursor ↦ data b`, back into the walk's
probe) and `g1FinWriter b` (`FrameWriter`: the same write, out into
`readAResetStart` with no cursor left on the tape) — and into the exact
`TM.runConfig` macro of each step: steps, head,
control state, carried context and the complete list-backed tape all pinned, on
an **arbitrary** surrounding frame list.  The forward and exhaustion scans reuse
the existing `g1FrameScanner`; both tape-preserving turns are the generic
`Phased.holdWalk4`.

Nothing merged is restated: `G1InstallSkip`, `g1Advance_bInsSeek_of_skip`,
`g1ValidPath_fix`, `g1AdvanceList_fix`, `g1CS_walk_install_scan` and
`g1CS_readB_install_scan_exact` come from `GateOneInstallScan`, and
`g1CursorWriter`, `g1CS_walk_probe_latch`, `g1CS_walk_probe_oob` and
`g1CS_walk_install_cursor` from `GateOneProbeInstall`.  The terminal path
**reuses** `G1WalkSkip` and the merged forward-scan plumbing; no normal-round
macro is duplicated for it.

**Explicit deferrals.**  Every theorem below takes the **caller's**
configuration, tape length and safety bound; none starts from
`G1M.initialConfig`, so there is no installation driver here, and nothing
composes two macros into a round or iterates one.  `g1CS_walk_seek_exhaust`
stops at `.bExh .p0`, head on the first cell of the opening `argSep`, and
`g1CS_walk_exh_to_cursor` is the **caller-supplied** continuation from exactly
that shape: nothing here proves that a real run reaches it, or reaches it after
the right number of rounds.  No walk invariant,
no iteration or loop clock, no out-of-range aggregation, no addressing, no
positive-index operand-value theorem, no repair, no pass A, no output write, no
`TM.accepts`, no gate-semantics correctness, no full-clock theorem and no
padded-tape claim.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan

/-- Frames the walk's two right-running scans cross: consumed units, the
`separator`, data. -/
def G1WalkSkip : G1Frame → Prop
  | .spent => True
  | .separator => True
  | .data _ => True
  | _ => False

instance : DecidablePred G1WalkSkip := fun f => by
  cases f <;> first | exact isTrue trivial | exact isFalse id

theorem g1Advance_bFwd_of_skip {f : G1Frame} (h : G1WalkSkip f) :
    g1Advance .bFwd f = .bFwd := by
  cases f <;> first | rfl | exact (show False from h).elim

/-- The exhaustion scan crosses exactly the same frames as the round's forward
scan, so it reuses `G1WalkSkip` rather than a second predicate. -/
theorem g1Advance_bRet_of_skip {f : G1Frame} (h : G1WalkSkip f) :
    g1Advance .bRet f = .bRet := by
  cases f <;> first | rfl | exact (show False from h).elim

/-- G1's right-to-left seek table: an `index` stops the pass at the write
handoff, the opening `argSep` at the exhaustion handoff, everything else
continues it one frame further left. -/
def g1WalkRevAdvance : G1Mode → G1Frame → G1Mode
  | _, .index => .bDec
  | _, .argSep => .bExh
  | _, _ => .bSeek

/-- The bit-level form of `g1WalkRevAdvance`, as `g1Transition` computes it. -/
def g1WalkRevComplete (_mode : G1Mode) (b0 b1 b2 b3 : Bool) : G1Mode :=
  match decodeG1Frame? [b0, b1, b2, b3] with
  | some .index => .bDec
  | some .argSep => .bExh
  | _ => .bSeek

/-- The single G1 mode of the cursor walk that reads frames right to left. -/
def G1WalkMode : G1Mode → Prop
  | .bSeek => True
  | _ => False

theorem G1WalkMode.eq {m : G1Mode} (h : G1WalkMode m) : m = .bSeek := by
  cases m <;> simp_all [G1WalkMode]

/-- The reverse seek stops at the write handoff or at the exhaustion handoff. -/
def G1WalkStop (mode : G1Mode) : Prop := mode = .bDec ∨ mode = .bExh

theorem g1WalkRevAdvance_of_skip {m : G1Mode} {f : G1Frame} (h : G1WalkSkip f) :
    g1WalkRevAdvance m f = .bSeek := by
  cases f <;> first | rfl | exact (show False from h).elim

private theorem g1WalkRevComplete_cases (m : G1Mode) (b0 b1 b2 b3 : Bool) :
    (g1WalkRevComplete m b0 b1 b2 b3 = .bDec ∧
        decodeG1Frame? [b0, b1, b2, b3] = some .index) ∨
      (g1WalkRevComplete m b0 b1 b2 b3 = .bExh ∧
        decodeG1Frame? [b0, b1, b2, b3] = some .argSep) ∨
      (g1WalkRevComplete m b0 b1 b2 b3 = .bSeek ∧
        decodeG1Frame? [b0, b1, b2, b3] ≠ some .index ∧
        decodeG1Frame? [b0, b1, b2, b3] ≠ some .argSep) := by
  unfold g1WalkRevComplete
  cases hd : decodeG1Frame? [b0, b1, b2, b3] with
  | none => exact Or.inr (Or.inr ⟨rfl, by simp, by simp⟩)
  | some f => cases f <;> simp_all

/-- **G1's cursor-walk seek is an instance of the generic reverse kernel.**  All
six obligations are standalone tuple lemmas of `GateOneControl`; `g1Transition`
is not unfolded here. -/
def g1WalkScanner : ReverseFrameScanner G1State G1Frame G1Mode G1Ctx where
  program := g1CS
  phase := g1CS.startPhase
  codec := g1FrameCodec
  Stop := G1WalkStop
  revAdvance := g1WalkRevAdvance
  revComplete := g1WalkRevComplete
  Reverse := G1WalkMode
  rst3 := fun m ctx => g1State m .p3 false false false ctx
  rst2 := fun m ctx b3 => g1State m .p2 false false b3 ctx
  rst1 := fun m ctx b2 b3 => g1State m .p1 false b2 b3 ctx
  rst0 := fun m ctx b1 b2 b3 => g1State m .p0 b1 b2 b3 ctx
  stopState := fun m ctx => g1State m .p0 false false false ctx
  revComplete_decode := by
    intro m f b0 b1 b2 b3 h
    have h' : decodeG1Frame? [b0, b1, b2, b3] = some f := h
    unfold g1WalkRevComplete
    rw [h']
    cases f <;> rfl
  rstep_p3 := by
    intro m hm ctx scan
    obtain rfl := hm.eq
    exact g1Transition_bSeek_p3 g1CS.startPhase false false false scan ctx
  rstep_p2 := by
    intro m hm ctx b3 scan
    obtain rfl := hm.eq
    exact g1Transition_bSeek_p2 g1CS.startPhase false false b3 scan ctx
  rstep_p1 := by
    intro m hm ctx b2 b3 scan
    obtain rfl := hm.eq
    exact g1Transition_bSeek_p1 g1CS.startPhase false b2 b3 scan ctx
  rstep_p0 := by
    intro m hm ctx b1 b2 b3 scan hne
    obtain rfl := hm.eq
    rcases g1WalkRevComplete_cases .bSeek scan b1 b2 b3 with
      ⟨he, -⟩ | ⟨he, -⟩ | ⟨he, hi, ha⟩
    · exact absurd (he ▸ Or.inl rfl : G1WalkStop _) hne
    · exact absurd (he ▸ Or.inr rfl : G1WalkStop _) hne
    · rw [he]
      exact g1Transition_bSeek_p0_other g1CS.startPhase b1 b2 b3 scan ctx hi ha
  rstep_p0_stop := by
    intro m hm ctx b1 b2 b3 scan hstop
    obtain rfl := hm.eq
    rcases g1WalkRevComplete_cases .bSeek scan b1 b2 b3 with
      ⟨he, hd⟩ | ⟨he, hd⟩ | ⟨he, -, -⟩
    · rw [he]
      exact g1Transition_bSeek_p0_index g1CS.startPhase b1 b2 b3 scan ctx hd
    · rw [he]
      exact g1Transition_bSeek_p0_argSep g1CS.startPhase b1 b2 b3 scan ctx hd
    · rw [he] at hstop
      rcases hstop with h | h <;> exact absurd h (by decide)

@[simp] theorem g1WalkScanner_machine : g1WalkScanner.machine = G1M := rfl

/-- **The `index ↦ spent` writer**, exiting into the forward scan. -/
def g1DecWriter : FrameWriter G1State G1Frame G1Ctx where
  program := g1CS
  phase := g1CS.startPhase
  codec := g1FrameCodec
  target := .spent
  w0 := true
  w1 := true
  w2 := false
  w3 := false
  wst0 := fun ctx => g1DecState ctx
  wst1 := fun ctx => g1State .bDec .p1 false false false ctx
  wst2 := fun ctx => g1State .bDec .p2 false false false ctx
  wst3 := fun ctx => g1State .bDec .p3 false false false ctx
  exitState := fun ctx => g1FwdState ctx
  target_bits := rfl
  wstep_p0 := fun ctx scan =>
    g1Transition_bDec_p0 g1CS.startPhase false false false scan ctx
  wstep_p1 := fun ctx scan =>
    g1Transition_bDec_p1 g1CS.startPhase false false false scan ctx
  wstep_p2 := fun ctx scan =>
    g1Transition_bDec_p2 g1CS.startPhase false false false scan ctx
  wstep_p3 := fun ctx scan =>
    g1Transition_bDec_p3 g1CS.startPhase false false false scan ctx

/-- **The cursor-restore writer**: `cursor ↦ data b`, into the walk's probe. -/
def g1RestoreWriter (b : Bool) : FrameWriter G1State G1Frame G1Ctx where
  program := g1CS
  phase := g1CS.startPhase
  codec := g1FrameCodec
  target := .data b
  w0 := false
  w1 := true
  w2 := b
  w3 := !b
  wst0 := fun ctx => g1State (g1RestoreMode b) .p0 false false false ctx
  wst1 := fun ctx => g1State (g1RestoreMode b) .p1 false false false ctx
  wst2 := fun ctx => g1State (g1RestoreMode b) .p2 false false false ctx
  wst3 := fun ctx => g1State (g1RestoreMode b) .p3 false false false ctx
  exitState := fun ctx => g1Probe2State ctx
  target_bits := by cases b <;> rfl
  wstep_p0 := fun ctx scan =>
    g1Transition_bRestore_p0 g1CS.startPhase b false false false scan ctx
  wstep_p1 := fun ctx scan =>
    g1Transition_bRestore_p1 g1CS.startPhase b false false false scan ctx
  wstep_p2 := fun ctx scan =>
    g1Transition_bRestore_p2 g1CS.startPhase b false false false scan ctx
  wstep_p3 := fun ctx scan =>
    g1Transition_bRestore_p3 g1CS.startPhase b false false false scan ctx

/-- **The terminal restore writer.**  The same `cursor ↦ data b` write, into the
pass-A reset handoff: the row that leaves **no cursor on the tape**. -/
def g1FinWriter (b : Bool) : FrameWriter G1State G1Frame G1Ctx where
  program := g1CS
  phase := g1CS.startPhase
  codec := g1FrameCodec
  target := .data b
  w0 := false
  w1 := true
  w2 := b
  w3 := !b
  wst0 := fun ctx => g1State (g1FinMode b) .p0 false false false ctx
  wst1 := fun ctx => g1State (g1FinMode b) .p1 false false false ctx
  wst2 := fun ctx => g1State (g1FinMode b) .p2 false false false ctx
  wst3 := fun ctx => g1State (g1FinMode b) .p3 false false false ctx
  exitState := fun ctx => g1ReadAResetState ctx
  target_bits := by cases b <;> rfl
  wstep_p0 := fun ctx scan =>
    g1Transition_bFin_p0 g1CS.startPhase b false false false scan ctx
  wstep_p1 := fun ctx scan =>
    g1Transition_bFin_p1 g1CS.startPhase b false false false scan ctx
  wstep_p2 := fun ctx scan =>
    g1Transition_bFin_p2 g1CS.startPhase b false false false scan ctx
  wstep_p3 := fun ctx scan =>
    g1Transition_bFin_p3 g1CS.startPhase b false false false scan ctx

/-! ## The atomic macros.  Each is an exact configuration equality on an
**arbitrary** surrounding frame list: nothing is assumed about which request,
index or round the frames belong to, and the caller supplies `n` and the bound. -/

/-- **The seek stops on the rightmost remaining `index`.**  `4k + 4` steps cross
the run right to left; the head finishes on the `index`'s *first* cell, tape and
`G1Ctx` untouched, control in the write handoff `bDec`. -/
theorem g1CS_walk_seek_to_index (n : Nat) (pre skipped suffix : List G1Frame)
    (ctx : G1Ctx) (hskip : ∀ f ∈ skipped, G1WalkSkip f)
    (hsafe : 4 * (pre.length + skipped.length) + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * (pre.length + skipped.length) + 3) (by omega)
          (g1ListTape
            ((pre ++ G1Frame.index :: skipped ++ suffix).flatMap G1Frame.bits))
          .bSeek .p3 false false false ctx)
        (4 * skipped.length + 4) =
      g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape
          ((pre ++ G1Frame.index :: skipped ++ suffix).flatMap G1Frame.bits))
        .bDec .p0 false false false ctx :=
  g1WalkScanner.revSeekToMarker n pre .index skipped suffix .bSeek ctx trivial
    (by simp [g1WalkScanner, G1WalkStop])
    (fun f hf => g1WalkRevAdvance_of_skip (hskip f hf)) (Or.inl rfl) hsafe

/-- **The seek stops on the opening `argSep`.**  The exact exhaustion endpoint:
head on that frame's first cell, in `bExh`.  The terminal path continues from
this *shape* in `g1CS_walk_exh_to_cursor`, on a configuration the caller
supplies; nothing composes the two. -/
theorem g1CS_walk_seek_exhaust (n : Nat) (pre skipped suffix : List G1Frame)
    (ctx : G1Ctx) (hskip : ∀ f ∈ skipped, G1WalkSkip f)
    (hsafe : 4 * (pre.length + skipped.length) + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * (pre.length + skipped.length) + 3) (by omega)
          (g1ListTape
            ((pre ++ G1Frame.argSep :: skipped ++ suffix).flatMap G1Frame.bits))
          .bSeek .p3 false false false ctx)
        (4 * skipped.length + 4) =
      g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape
          ((pre ++ G1Frame.argSep :: skipped ++ suffix).flatMap G1Frame.bits))
        .bExh .p0 false false false ctx :=
  g1WalkScanner.revSeekToMarker n pre .argSep skipped suffix .bSeek ctx trivial
    (by simp [g1WalkScanner, G1WalkStop])
    (fun f hf => g1WalkRevAdvance_of_skip (hskip f hf)) (Or.inr rfl) hsafe

/-- **The `index ↦ spent` write.**  Four steps replace the `index` at ordinal
`pre.length` by `spent` — nothing else changes — and enter the forward scan. -/
theorem g1CS_walk_mark (n : Nat) (pre suffix : List G1Frame) (ctx : G1Ctx)
    (hsafe : 4 * pre.length + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape ((pre ++ G1Frame.index :: suffix).flatMap G1Frame.bits))
        .bDec .p0 false false false ctx) 4 =
      g1AlignedConfig n (4 * pre.length + 4) hsafe
        (g1ListTape ((pre ++ G1Frame.spent :: suffix).flatMap G1Frame.bits))
        .bFwd .p0 false false false ctx :=
  g1DecWriter.writeFrameOnList n pre suffix .index ctx hsafe

set_option maxHeartbeats 1000000 in
/-- **Reverse seek plus mark.**  `4k + 8` steps cross the run and replace the
rightmost remaining `index` by `spent`; nothing else changes. -/
theorem g1CS_walk_seek_mark (n : Nat) (pre skipped suffix : List G1Frame)
    (ctx : G1Ctx) (hskip : ∀ f ∈ skipped, G1WalkSkip f)
    (hsafe : 4 * (pre.length + skipped.length) + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (4 * (pre.length + skipped.length) + 3) (by omega)
          (g1ListTape
            ((pre ++ G1Frame.index :: skipped ++ suffix).flatMap G1Frame.bits))
          .bSeek .p3 false false false ctx)
        (4 * skipped.length + 8) =
      g1AlignedConfig n (4 * pre.length + 4) (by omega)
        (g1ListTape
          ((pre ++ G1Frame.spent :: skipped ++ suffix).flatMap G1Frame.bits))
        .bFwd .p0 false false false ctx := by
  rw [show 4 * skipped.length + 8 = 4 * skipped.length + 4 + 4 by omega,
    runConfig_add]
  refine Eq.trans (congrArg (fun c => TM.runConfig (M := G1M) c 4)
    (g1CS_walk_seek_to_index n pre skipped suffix ctx hskip hsafe)) ?_
  simp only [List.append_assoc, List.cons_append]
  exact g1CS_walk_mark n pre (skipped ++ suffix) ctx (by omega)

/-- **The forward scan back to the cursor.**  `4 * (k + 1)` read-only steps
cross the run and read the `cursor`, entering the turn just past it. -/
theorem g1CS_walk_fwd_to_cursor (n : Nat) (pre skipped suffix : List G1Frame)
    (ctx : G1Ctx) (hskip : ∀ f ∈ skipped, G1WalkSkip f)
    (hsafe : 4 * (pre.length + (skipped.length + 1)) < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape
          ((pre ++ skipped ++ G1Frame.cursor :: suffix).flatMap G1Frame.bits))
        .bFwd .p0 false false false ctx)
        (4 * (skipped.length + 1)) =
      g1AlignedConfig n (4 * (pre.length + (skipped.length + 1))) hsafe
        (g1ListTape
          ((pre ++ skipped ++ G1Frame.cursor :: suffix).flatMap G1Frame.bits))
        .bTurn .p0 false false false ctx := by
  have hfix : ∀ f ∈ skipped, g1Advance .bFwd f = .bFwd :=
    fun f hf => g1Advance_bFwd_of_skip (hskip f hf)
  have hlen : (skipped ++ [G1Frame.cursor]).length = skipped.length + 1 := by
    simp
  have hlist : pre ++ (skipped ++ [G1Frame.cursor]) ++ suffix =
      pre ++ skipped ++ G1Frame.cursor :: suffix := by
    simp [List.append_assoc]
  have hpath : G1ValidPath .bFwd (skipped ++ [G1Frame.cursor]) :=
    g1ValidPath_fix (mode := .bFwd) trivial [G1Frame.cursor]
      ⟨trivial, by decide, trivial⟩ skipped hfix
  have hfold : g1AdvanceList .bFwd (skipped ++ [G1Frame.cursor]) = .bTurn := by
    rw [g1AdvanceList_fix (mode := .bFwd) [G1Frame.cursor] skipped hfix]; rfl
  have hscan := g1FrameScanner_scanFrames n pre (skipped ++ [G1Frame.cursor])
    suffix .bFwd ctx ((g1FrameScanner_validPath _ _).mpr hpath)
    (by rw [hlen]; exact hsafe)
  simp only [hlist, hlen, g1AlignedFrame_eq, g1FrameScanner_advanceList, hfold]
    at hscan
  exact hscan

/-- **The turn.**  Four hold-and-move-left steps from just past the cursor back
onto its first cell, tape untouched, into the restore writer of `ctx.vB`. -/
theorem g1CS_walk_turn (n k : Nat) (hsafe : k + 4 < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (k + 4) hsafe tape .bTurn .p0 false false false ctx)
        4 =
      g1AlignedConfig n k (by omega) tape
        (g1RestoreMode ctx.vB) .p0 false false false ctx :=
  Phased.holdWalk4 g1CS g1CS.startPhase n k hsafe tape _ _ _ _ _
    (fun scan => g1Transition_bTurn_p0 g1CS.startPhase false false false scan ctx)
    (fun scan => g1Transition_bTurn_p1 g1CS.startPhase false false false scan ctx)
    (fun scan => g1Transition_bTurn_p2 g1CS.startPhase false false false scan ctx)
    (fun scan => g1Transition_bTurn_p3 g1CS.startPhase false false false scan ctx)

/-- **The cursor restore.**  Four steps replace the `cursor` at ordinal
`pre.length` by `data b` and open the walk's probe on the next frame. -/
theorem g1CS_walk_restore (n : Nat) (pre suffix : List G1Frame) (b : Bool)
    (ctx : G1Ctx) (hsafe : 4 * pre.length + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape ((pre ++ G1Frame.cursor :: suffix).flatMap G1Frame.bits))
        (g1RestoreMode b) .p0 false false false ctx) 4 =
      g1AlignedConfig n (4 * pre.length + 4) hsafe
        (g1ListTape ((pre ++ G1Frame.data b :: suffix).flatMap G1Frame.bits))
        .bProbe2 .p0 false false false ctx :=
  (g1RestoreWriter b).writeFrameOnList n pre suffix .cursor ctx hsafe

/-! ## The terminal exhaustion path

Three macros behind the merged `bExh` handoff, in the same caller-supplied
shape as the round's: the exhaustion scan, the terminal turn and the terminal
restore.  They reuse `G1WalkSkip`, `g1FrameScanner`, `g1ValidPath_fix`,
`g1AdvanceList_fix` and `Phased.holdWalk4`; nothing chains them, and no run
below reaches `bExh` on its own. -/

/-- **The exhaustion scan.**  From the first cell of the opening `argSep`,
`4 * (k + 2)` read-only steps re-read that `argSep`, cross the `k` consumed
units, separator and data frames after it and read the `cursor`, entering the
terminal turn just past it. -/
theorem g1CS_walk_exh_to_cursor (n : Nat) (pre skipped suffix : List G1Frame)
    (ctx : G1Ctx) (hskip : ∀ f ∈ skipped, G1WalkSkip f)
    (hsafe : 4 * (pre.length + (skipped.length + 2)) < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape
          ((pre ++ G1Frame.argSep :: skipped ++ G1Frame.cursor ::
            suffix).flatMap G1Frame.bits))
        .bExh .p0 false false false ctx)
        (4 * (skipped.length + 2)) =
      g1AlignedConfig n (4 * (pre.length + (skipped.length + 2))) hsafe
        (g1ListTape
          ((pre ++ G1Frame.argSep :: skipped ++ G1Frame.cursor ::
            suffix).flatMap G1Frame.bits))
        .bTurnFin .p0 false false false ctx := by
  have hfix : ∀ f ∈ skipped, g1Advance .bRet f = .bRet :=
    fun f hf => g1Advance_bRet_of_skip (hskip f hf)
  have hlen :
      (G1Frame.argSep :: (skipped ++ [G1Frame.cursor])).length =
        skipped.length + 2 := by
    simp
  have hlist :
      pre ++ (G1Frame.argSep :: (skipped ++ [G1Frame.cursor])) ++ suffix =
        pre ++ G1Frame.argSep :: skipped ++ G1Frame.cursor :: suffix := by
    simp [List.append_assoc]
  have hpath : G1ValidPath .bExh
      (G1Frame.argSep :: (skipped ++ [G1Frame.cursor])) :=
    ⟨trivial, by decide,
      g1ValidPath_fix (mode := .bRet) trivial [G1Frame.cursor]
        ⟨trivial, by decide, trivial⟩ skipped hfix⟩
  have hfold : g1AdvanceList .bExh
      (G1Frame.argSep :: (skipped ++ [G1Frame.cursor])) = .bTurnFin := by
    rw [g1AdvanceList_cons,
      show g1Advance .bExh G1Frame.argSep = .bRet from rfl,
      g1AdvanceList_fix (mode := .bRet) [G1Frame.cursor] skipped hfix]
    rfl
  have hscan := g1FrameScanner_scanFrames n pre
    (G1Frame.argSep :: (skipped ++ [G1Frame.cursor])) suffix .bExh ctx
    ((g1FrameScanner_validPath _ _).mpr hpath)
    (by rw [hlen]; exact hsafe)
  simp only [hlist, hlen, g1AlignedFrame_eq, g1FrameScanner_advanceList, hfold]
    at hscan
  exact hscan

/-- **The terminal turn.**  The same four hold-and-move-left steps as
`g1CS_walk_turn`, on an arbitrary tape, into the *terminal* writer of
`ctx.vB`. -/
theorem g1CS_walk_turn_fin (n k : Nat) (hsafe : k + 4 < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (ctx : G1Ctx) :
    TM.runConfig (M := G1M)
        (g1AlignedConfig n (k + 4) hsafe tape .bTurnFin .p0 false false false
          ctx) 4 =
      g1AlignedConfig n k (by omega) tape
        (g1FinMode ctx.vB) .p0 false false false ctx :=
  Phased.holdWalk4 g1CS g1CS.startPhase n k hsafe tape _ _ _ _ _
    (fun scan =>
      g1Transition_bTurnFin_p0 g1CS.startPhase false false false scan ctx)
    (fun scan =>
      g1Transition_bTurnFin_p1 g1CS.startPhase false false false scan ctx)
    (fun scan =>
      g1Transition_bTurnFin_p2 g1CS.startPhase false false false scan ctx)
    (fun scan =>
      g1Transition_bTurnFin_p3 g1CS.startPhase false false false scan ctx)

/-- **The terminal restore.**  Four steps replace the `cursor` at ordinal
`pre.length` by `data b` and hand off to `readAResetStart` on the next frame:
the resulting frame list has **no `cursor` in it at all** wherever the caller's
`pre` and `suffix` had none. -/
theorem g1CS_walk_fin_restore (n : Nat) (pre suffix : List G1Frame) (b : Bool)
    (ctx : G1Ctx) (hsafe : 4 * pre.length + 4 < G1M.tapeLength n) :
    TM.runConfig (M := G1M) (g1AlignedConfig n (4 * pre.length) (by omega)
        (g1ListTape ((pre ++ G1Frame.cursor :: suffix).flatMap G1Frame.bits))
        (g1FinMode b) .p0 false false false ctx) 4 =
      g1AlignedConfig n (4 * pre.length + 4) hsafe
        (g1ListTape ((pre ++ G1Frame.data b :: suffix).flatMap G1Frame.bits))
        .readAResetStart .p0 false false false ctx :=
  (g1FinWriter b).writeFrameOnList n pre suffix .cursor ctx hsafe

end Pnp3.Internal.PsubsetPpoly.TM
