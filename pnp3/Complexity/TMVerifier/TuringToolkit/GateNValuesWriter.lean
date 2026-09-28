import Complexity.TMVerifier.TuringToolkit.GateNValuesRewind

/-!
# GN-E2-5a values/tail control and the input-free first request (2026-09-28)

**Progress classification: infrastructure, not P-vs-NP mainline progress.**

GN-E2-4a stopped in the literal `valuesEntry` state on p0 of the frame after
the word's leading `bof`, with the scratch region holding the installed image
of the selected record and the first request's tail still unwritten.  This
slice activates that state: the finite values control classifies the frame
under the head, seeks the scratch frontier, turns around, and physically
writes the request's fixed `output false`/`finish` tail, ending in the new
literal `requestReady` state on p0 of the blank just past the installed word.

**Fixed control added** (in the machine owner, not here): `GNValuesMode`, the
`GNState` constructors `values` and `requestReady`, the row set
`gnValuesStep`, one changed `valuesEntry` row, one new
`gnInstallExitDispatch` route for a carried `data` frame, and the matching
narrowing of `GNInstallExitInvalid`.  No mode, buffer or payload holds a
natural number, index, width, base, request, list, gate, clock counter or
proof, and nothing is request-dependent: the same rows run for every program.

**Added here**: the row facts, the tail seek as an instance of the shared
forward frame-scanner kernel, the two tail frames as instances of the shared
frame writer, the room and clock bounds, and two capstones — a generic one
from the GN-E2-4a values boundary and a real-input one from
`GNM.initialConfig (gnPoint (encodeGN r))`.  Their only premises are
`hg : r.program.gates[0]? = some g` and `hinputs : r.inputs = []`: no
well-formedness, canonicality, evaluation success, room premise, precomputed
answer or runtime witness is assumed, and every room fact is proved internally.

**Scope, stated exactly.**  `hinputs` is the scope of this slice: with no
current values the classification meets the first reserved output slot at once,
so the data classification, the four `back` rows and the carried-`data` exit
dispatch are *installed and pinned* — by `gnTransition_values_rows` and
`gnTransition_dataExit` — but **dormant**, executed by no theorem here.  The
per-value copy round, its list induction and the resulting nonempty-input
capstone are GN-E2-5b's obligation, and nothing here claims them.

**Explicitly not here, and claimed nowhere.**  `requestReady` is a dormant
absorbing arrival: there is no rewind to the scratch `bof`, no launch, no
delegation of the installed request to the G1 control, no commit of a returned
bit, no cursor/spent advance, no next-gate loop, no total installer clock, no
verdict and no acceptance.  In particular the pure evaluator `evalGNProgram`
is **not** executed by this machine and no statement here says it is: at this
endpoint the machine has relocated the selected record's frames and written
two fixed frames, and the semantic conjuncts of
`gnFirstRequestReadyConfig_structure` are about the **pure** request `g`
determines.  This is a *first*-request theorem: the shared temporary marker is
decoded `output true`, whose absence holds on the stage-zero real path and the
mapped scratch but not automatically after a later commit.  The fixed tail
writer overwrites its two destination frames unconditionally; on the real path
both are proved blank from the full tape, and no claim is made that an
arbitrary corrupted destination would reject.
-/
namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan
open Encoding

/-! ## Exact finite values rows -/

/-- The complete values/tail row set.  The activated `valuesEntry` entry read
buffers the scanned cell and steps right; every `values` row is exactly the
finite `gnValuesStep` decision; `requestReady` is a dormant self-loop.  The
last four conjuncts spell out the rows a reader most needs to see: the `back`
walk's handoff to the existing installer probe, the `tailBack` walk's handoff
to the writer, and the first and last of the eight write/right tail rows. -/
theorem gnTransition_values_rows (phase : Fin 1) (mode : GNValuesMode)
    (buffer : GNInstallBuffer) (scan : Bool) :
    gnTransition phase .valuesEntry scan =
        (0, .values .probe (.p1 scan), scan, .right) ∧
      gnTransition phase (.values mode buffer) scan =
        (0, gnValuesStep mode buffer scan) ∧
      gnTransition phase .requestReady scan = (0, .requestReady, scan, .stay) ∧
      gnValuesStep .back .p0 scan = (.install .probe .p0 .empty, scan, .left) ∧
      gnValuesStep .tailBack .p0 scan =
        (.values .writeOutput .p0, scan, .left) ∧
      gnValuesStep .writeOutput .p0 scan =
        (.values .writeOutput (.p1 false), true, .right) ∧
      gnValuesStep .writeFinish (.p3 false false false) scan =
        (.requestReady, false, .right) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The two complete frame-position-3 decisions, in decoded form.  This is a
readable corollary of `gnTransition_values_rows`, which already pins every
`values` row as the finite `gnValuesStep` decision; it stays private because
the public `gnTransition_values_reserved` carries the fail-closed statements a
caller needs. -/
private theorem gnTransition_values_decision (phase : Fin 1)
    (b0 b1 b2 b3 : Bool) :
    (∀ frame : G1Frame, decodeG1Frame? [b0, b1, b2, b3] = some frame →
        gnValuesClassify frame ≠ .reject →
        gnTransition phase (.values .probe (.p3 b0 b1 b2)) b3 =
          (0, gnValuesClassify frame, b3, .right)) ∧
      (gnValuesClassifyBits b0 b1 b2 b3 = .reject →
        gnTransition phase (.values .probe (.p3 b0 b1 b2)) b3 =
          (0, .reject, b3, .stay)) ∧
      (∀ frame : G1Frame, decodeG1Frame? [b0, b1, b2, b3] = some frame →
        gnValuesAdvance .seekTail frame ≠ .reject →
        gnTransition phase (.values .seekTail (.p3 b0 b1 b2)) b3 =
          (0, gnValuesControl (gnValuesAdvance .seekTail frame)
            (gnValuesEnter (gnValuesAdvance .seekTail frame)), b3, .right)) ∧
      (gnValuesComplete .seekTail b0 b1 b2 b3 = .reject →
        gnTransition phase (.values .seekTail (.p3 b0 b1 b2)) b3 =
          (0, .reject, b3, .stay)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro frame hdec hne
    have hclass : gnValuesClassifyBits b0 b1 b2 b3 = gnValuesClassify frame := by
      rw [gnValuesClassifyBits, hdec]
    simp only [gnTransition, gnValuesStep, hclass, if_neg hne]
  · intro hreject
    simp [gnTransition, gnValuesStep, hreject]
  · intro frame hdec hne
    have hcomplete : gnValuesComplete .seekTail b0 b1 b2 b3 =
        gnValuesAdvance .seekTail frame := by
      rw [gnValuesComplete, hdec]
    simp only [gnTransition, gnValuesStep, hcomplete, if_neg hne]
  · intro hreject
    simp [gnTransition, gnValuesStep, hreject]

/-- Every undecodable window and every frame the two new ingress points must
refuse is a rejection row: the three reserved public codes at both, the
installer's temporary `output true` marker at both, and — at the values
boundary only — a decoded blank and a decoded record `tag`, neither of which
may start an unintended copy.  This slice opens exactly two new places where
tape data enters the finite control, and both fail closed. -/
theorem gnTransition_values_reserved (phase : Fin 1) :
    (∀ b0 b1 b2 b3 : Bool, decodeG1Frame? [b0, b1, b2, b3] = none →
        gnTransition phase (.values .probe (.p3 b0 b1 b2)) b3 =
            (0, .reject, b3, .stay) ∧
          gnTransition phase (.values .seekTail (.p3 b0 b1 b2)) b3 =
            (0, .reject, b3, .stay)) ∧
      gnTransition phase (.values .probe (.p3 true false false)) true =
          (0, .reject, true, .stay) ∧
      gnTransition phase (.values .seekTail (.p3 true false false)) true =
          (0, .reject, true, .stay) ∧
      gnTransition phase (.values .probe (.p3 false false false)) false =
          (0, .reject, false, .stay) ∧
      gnTransition phase (.values .probe (.p3 false false true)) false =
          (0, .reject, false, .stay) :=
  ⟨fun b0 b1 b2 b3 hnone =>
      ⟨(gnTransition_values_decision phase b0 b1 b2 b3).2.1
          (by rw [gnValuesClassifyBits, hnone]),
        (gnTransition_values_decision phase b0 b1 b2 b3).2.2.2
          (by rw [gnValuesComplete, hnone])⟩,
    (gnTransition_values_decision phase true false false true).2.1 rfl,
    (gnTransition_values_decision phase true false false true).2.2.2 rfl,
    (gnTransition_values_decision phase false false false false).2.1 rfl,
    (gnTransition_values_decision phase false false true false).2.1 rfl⟩

/-- **The new data route out of the installer exit.**  A carried `data` frame
is dispatched stationarily to `valuesEntry`, which is neither a continuing
payload — "continuing" means specifically the one-step dispatch back to the
installer probe — nor, since GN-E2-5, an invalid one.  This is the statement
that keeps `gnTransition_install_exit_dispatch`'s unchanged invalid clause from
silently covering the case it no longer covers. -/
theorem gnTransition_dataExit (phase : Fin 1) (b scan : Bool) :
    gnTransition phase (gnInstallExitState (.carried (.data b))) scan =
        (0, .valuesEntry, scan, .stay) ∧
      ¬ GNInstallExitContinue (GNInstallAux.carried (.data b)) ∧
      ¬ GNInstallExitInvalid (GNInstallAux.carried (.data b)) :=
  ⟨rfl, fun h => h, fun h => absurd rfl (h.2.2 b)⟩

/-! ## The tail seek as an instance of the shared forward kernel -/

/-- Only the tail seek consumes ordinary frames left to right. -/
private def GNValuesForward : GNValuesMode → Prop
  | .seekTail => True
  | _ => False

/-- The tail seek as an instance of the shared frame-scanner kernel.  All nine
obligations are discharged from the fixed table above; no control row is
modified here. -/
private def gnValuesSeekScanner : FrameScanner GNState G1Frame GNValuesMode Unit where
  program := gnCS
  phase := gnCS.startPhase
  codec := g1FrameCodec
  rejectMode := .reject
  advance := gnValuesAdvance
  complete := gnValuesComplete
  Forward := GNValuesForward
  st0 := fun mode _ => gnValuesControl mode (gnValuesEnter mode)
  st1 := fun mode _ b0 => gnValuesControl mode (.p1 b0)
  st2 := fun mode _ b0 b1 => gnValuesControl mode (.p2 b0 b1)
  st3 := fun mode _ b0 b1 b2 => gnValuesControl mode (.p3 b0 b1 b2)
  complete_decode := by
    intro mode b0 b1 b2 b3
    cases h : decodeG1Frame? [b0, b1, b2, b3] <;>
      simp only [gnValuesComplete, g1FrameCodec_decode, h]
  step_p0 := by
    intro mode hm _ scan
    cases mode <;> simp [GNValuesForward] at hm
    rfl
  step_p1 := by
    intro mode hm _ b0 scan
    cases mode <;> simp [GNValuesForward] at hm
    rfl
  step_p2 := by
    intro mode hm _ b0 b1 scan
    cases mode <;> simp [GNValuesForward] at hm
    rfl
  step_p3 := by
    intro mode hm _ b0 b1 b2 scan hne
    cases mode <;> simp [GNValuesForward] at hm
    simp only [gnValuesControl, gnCS, gnTransition, gnValuesStep, if_neg hne]

/-- A block with neither a blank nor the temporary marker, followed by the
scratch frontier blank, is a valid forward seek path ending in `tailBack`.
This is the only fact about the scanned frames the seek needs: it deliberately
passes separators, `bof` and `finish`, because the remaining original word and
the scratch header contain them and stopping there would select the wrong
boundary. -/
private theorem gnValuesSeek_validPath {frames : List G1Frame}
    (h : ∀ f ∈ frames, GNInstallAdmissible f) :
    gnValuesSeekScanner.ValidPath .seekTail (frames ++ [G1Frame.blank]) ∧
      gnValuesSeekScanner.advanceList .seekTail (frames ++ [G1Frame.blank]) =
        .tailBack := by
  induction frames with
  | nil => exact ⟨⟨trivial, fun hc => GNValuesMode.noConfusion hc, trivial⟩, rfl⟩
  | cons f rest ih =>
      have hf := h f (by simp)
      have hrest := ih (fun g hg => h g (List.mem_cons_of_mem _ hg))
      have hadv : gnValuesSeekScanner.advance .seekTail f =
          GNValuesMode.seekTail := by
        cases f with
        | blank => exact absurd rfl hf.1
        | output b => cases b with
          | true => exact absurd rfl hf.2
          | false => rfl
        | data b => cases b <;> rfl
        | bof | tag | index | separator | cursor | finish | argSep | spent => rfl
      refine ⟨⟨trivial, ?_, ?_⟩, ?_⟩
      · rw [hadv]; exact fun hc => GNValuesMode.noConfusion hc
      · rw [hadv]; exact hrest.1
      · rw [List.cons_append, FrameScanner.advanceList_cons, hadv]
        exact hrest.2

/-- The request's reserved output slot, as a four-row frame writer. -/
private def gnValuesOutputWriter : FrameWriter GNState G1Frame Unit where
  program := gnCS
  phase := gnCS.startPhase
  codec := g1FrameCodec
  target := .output false
  w0 := true
  w1 := false
  w2 := false
  w3 := false
  wst0 := fun _ => .values .writeOutput .p0
  wst1 := fun _ => .values .writeOutput (.p1 false)
  wst2 := fun _ => .values .writeOutput (.p2 false false)
  wst3 := fun _ => .values .writeOutput (.p3 false false false)
  exitState := fun _ => .values .writeFinish .p0
  target_bits := rfl
  wstep_p0 := by intro _ _; rfl
  wstep_p1 := by intro _ _; rfl
  wstep_p2 := by intro _ _; rfl
  wstep_p3 := by intro _ _; rfl

/-- The request's closing `finish`, as a four-row frame writer.  Its exit is
the dormant `requestReady` arrival. -/
private def gnValuesFinishWriter : FrameWriter GNState G1Frame Unit where
  program := gnCS
  phase := gnCS.startPhase
  codec := g1FrameCodec
  target := .finish
  w0 := true
  w1 := false
  w2 := true
  w3 := false
  wst0 := fun _ => .values .writeFinish .p0
  wst1 := fun _ => .values .writeFinish (.p1 false)
  wst2 := fun _ => .values .writeFinish (.p2 false false)
  wst3 := fun _ => .values .writeFinish (.p3 false false false)
  exitState := fun _ => .requestReady
  target_bits := rfl
  wstep_p0 := by intro _ _; rfl
  wstep_p1 := by intro _ _; rfl
  wstep_p2 := by intro _ _; rfl
  wstep_p3 := by intro _ _; rfl

/-! ## Private aligned-configuration glue -/

/-- The shared phase layer's compiled machine is literally `GNM`; this is the
only place the two spellings of the tape length are reconciled. -/
private theorem gnValues_lt {n h : Nat} (hh : h < GNM.tapeLength n) :
    h < (Phased.machine gnCS).tapeLength n := hh

private theorem gnValues_room_le {n k m : Nat} (h : k ≤ 4 * m)
    (hm : 4 * m < GNM.tapeLength n) : k < GNM.tapeLength n :=
  Nat.lt_of_le_of_lt h hm

/-- A `GNM` configuration at an explicit head on a frame-list tape. -/
private def gnFrameCfg (n head : Nat) (frames : List G1Frame) (q : GNState)
    (hh : head < GNM.tapeLength n) : Configuration (M := GNM) n :=
  Phased.alignedAt gnCS gnCS.startPhase n head (gnValues_lt hh)
    (frameListTape (L := GNM.tapeLength n) (frames.flatMap G1Frame.bits)) q

private theorem gnFrameCfg_ext {n h1 h2 : Nat} {f1 f2 : List G1Frame}
    {q : GNState} {p1 : h1 < GNM.tapeLength n} {p2 : h2 < GNM.tapeLength n}
    (hh : h1 = h2)
    (hf : frameListTape (L := GNM.tapeLength n) (f1.flatMap G1Frame.bits) =
      frameListTape (f2.flatMap G1Frame.bits)) :
    gnFrameCfg n h1 f1 q p1 = gnFrameCfg n h2 f2 q p2 := by
  subst hh
  simp only [gnFrameCfg, hf]

private theorem gnCS_valuesRead (n h : Nat) (hh : h < GNM.tapeLength n)
    (hb : h + 1 < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool) (q : GNState) (f : Bool → GNState)
    (htr : ∀ scan : Bool, gnTransition gnCS.startPhase q scan =
      (gnCS.startPhase, f scan, scan, .right)) :
    TM.stepConfig (M := GNM)
        (Phased.alignedAt gnCS gnCS.startPhase n h hh tape q) =
      Phased.alignedAt gnCS gnCS.startPhase n (h + 1) hb tape
        (f (tape ⟨h, hh⟩)) := by
  have hstep := Phased.stepRight gnCS gnCS.startPhase n h hh hb tape q
    (f (tape ⟨h, hh⟩)) (tape ⟨h, hh⟩) (htr _)
  rwa [writeCell_self] at hstep

private theorem gnCS_valuesStay (n h : Nat) (hh : h < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool) (q q' : GNState)
    (htr : ∀ scan : Bool, gnTransition gnCS.startPhase q scan =
      (gnCS.startPhase, q', scan, .stay)) :
    TM.stepConfig (M := GNM)
        (Phased.alignedAt gnCS gnCS.startPhase n h hh tape q) =
      Phased.alignedAt gnCS gnCS.startPhase n h hh tape q' := by
  have hstep := Phased.stepStay gnCS gnCS.startPhase n h hh tape q q'
    (tape ⟨h, hh⟩) (htr _)
  rwa [writeCell_self] at hstep

/-- Appending one explicit blank frame does not change the physical tape. -/
private theorem gnValues_tape_blank (n : Nat) (k : List G1Frame) :
    frameListTape (L := GNM.tapeLength n) (k.flatMap G1Frame.bits) =
      frameListTape ((k ++ [G1Frame.blank]).flatMap G1Frame.bits) := by
  simpa only [g1FrameCodec_bits] using
    frameListTape_append_blank (L := GNM.tapeLength n) g1FrameCodec k
      G1Frame.blank rfl

/-- The three buffering rows of the values boundary, on an arbitrary tape. -/
private theorem gnCS_values_buffer (n base : Nat)
    (hsafe : base + 4 < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool) (b0 b1 b2 : Bool)
    (h0 : tape ⟨base, by omega⟩ = b0) (h1 : tape ⟨base + 1, by omega⟩ = b1)
    (h2 : tape ⟨base + 2, by omega⟩ = b2) :
    TM.runConfig (M := GNM)
        (Phased.alignedAt gnCS gnCS.startPhase n base (gnValues_lt (by omega))
          tape .valuesEntry) 3 =
      Phased.alignedAt gnCS gnCS.startPhase n (base + 3)
        (gnValues_lt (by omega)) tape (.values .probe (.p3 b0 b1 b2)) := by
  have s0 := gnCS_valuesRead n base (by omega) (by omega) tape .valuesEntry
    (fun s => .values .probe (.p1 s)) (fun _ => rfl)
  have s1 := gnCS_valuesRead n (base + 1) (by omega) (by omega) tape
    (.values .probe (.p1 b0)) (fun s => .values .probe (.p2 b0 s))
    (fun _ => rfl)
  have s2 := gnCS_valuesRead n (base + 2) (by omega) (by omega) tape
    (.values .probe (.p2 b0 b1)) (fun s => .values .probe (.p3 b0 b1 s))
    (fun _ => rfl)
  simp only [h0] at s0
  simp only [h1] at s1
  simp only [h2] at s2
  show TM.runConfig (M := GNM) _ (1 + 1 + 1) = _
  rw [runConfig_add, runConfig_add]
  simp only [runConfig_one]
  rw [s0, s1, s2]

/-- **The four classification rows.**  On any tape whose aligned window at
`base` spells `frame`, the values boundary reads that window in exactly four
physical rows, writes nothing, and lands one frame further right in the state
the finite classification assigns to `frame`. -/
private theorem gnCS_values_classify (n base : Nat)
    (hsafe : base + 4 < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool) (frame : G1Frame)
    (hbits : physicalBitsAt hsafe tape = frame.bits)
    (hne : gnValuesClassify frame ≠ .reject) :
    TM.runConfig (M := GNM)
        (Phased.alignedAt gnCS gnCS.startPhase n base (gnValues_lt (by omega))
          tape .valuesEntry) 4 =
      Phased.alignedAt gnCS gnCS.startPhase n (base + 4) (gnValues_lt hsafe)
        tape (gnValuesClassify frame) := by
  obtain ⟨b0, b1, b2, b3, hfb⟩ := g1FrameCodec.bits_eq_four frame
  rw [g1FrameCodec_bits] at hfb
  rw [hfb] at hbits
  have hcells : tape ⟨base, by omega⟩ = b0 ∧ tape ⟨base + 1, by omega⟩ = b1 ∧
      tape ⟨base + 2, by omega⟩ = b2 ∧ tape ⟨base + 3, by omega⟩ = b3 := by
    simpa only [physicalBitsAt, List.cons.injEq, and_true] using hbits
  obtain ⟨h0, h1, h2, h3⟩ := hcells
  have hrow := (gnTransition_values_decision gnCS.startPhase b0 b1 b2 b3).1
    frame (by rw [← hfb]; exact decodeG1Frame_bits frame) hne
  have s3 := Phased.stepRight gnCS gnCS.startPhase n (base + 3)
    (gnValues_lt (by omega)) (gnValues_lt hsafe) tape
    (.values .probe (.p3 b0 b1 b2)) (gnValuesClassify frame)
    (tape ⟨base + 3, by omega⟩) (by rw [h3]; exact hrow)
  rw [writeCell_self] at s3
  show TM.runConfig (M := GNM) _ (3 + 1) = _
  rw [runConfig_add, gnCS_values_buffer n base hsafe tape b0 b1 b2 h0 h1 h2,
    runConfig_one, s3]

/-! ## The exact terminal seek and tail write -/

/-- Physical frame presentation of the terminal phase: the copied value prefix,
the reserved output slot that ends the value run, every frame up to the scratch
frontier, and the two tail frames with the blank past them. -/
private def gnValuesTerminalFrames (pre mid : List G1Frame) (f1 f2 : G1Frame) :
    List G1Frame :=
  pre ++ G1Frame.output false :: (mid ++ [f1, f2, G1Frame.blank])

/-- The tail seek, with head positions supplied by the caller. -/
private theorem gnCS_values_seek (n hstart hend steps : Nat)
    (pre frames suffix full : List G1Frame)
    (hfull : full = pre ++ frames ++ suffix)
    (hs : hstart = 4 * pre.length)
    (he : hend = 4 * (pre.length + frames.length))
    (hk : steps = 4 * frames.length)
    (hpath : gnValuesSeekScanner.ValidPath .seekTail frames)
    (hmode : gnValuesSeekScanner.advanceList .seekTail frames = .tailBack)
    (hsafe : 4 * (pre.length + frames.length) < GNM.tapeLength n) :
    TM.runConfig (M := GNM)
        (gnFrameCfg n hstart full (.values .seekTail .p0) (by omega)) steps =
      gnFrameCfg n hend full (.values .tailBack (.p3 false false false))
        (by omega) := by
  subst hfull; subst hs; subst he; subst hk
  have h := gnValuesSeekScanner.scanFrames n pre frames suffix .seekTail ()
    hpath (by
      change 4 * (pre.length + frames.length) < GNM.tapeLength n
      omega)
  rw [hmode] at h
  exact h

/-- The eight fixed tail-write rows, with head positions supplied by the
caller.  The two destination frames are overwritten unconditionally. -/
private theorem gnCS_values_tailWrite (n hstart hend : Nat)
    (pre suffix full1 full3 : List G1Frame)
    (h1 : full1 = pre ++ G1Frame.blank :: G1Frame.blank :: suffix)
    (h3 : full3 = pre ++ G1Frame.output false :: G1Frame.finish :: suffix)
    (hs : hstart = 4 * pre.length) (he : hend = 4 * pre.length + 8)
    (hsafe : 4 * pre.length + 8 < GNM.tapeLength n) :
    TM.runConfig (M := GNM)
        (gnFrameCfg n hstart full1 (.values .writeOutput .p0) (by omega)) 8 =
      gnFrameCfg n hend full3 .requestReady (by omega) := by
  subst h1; subst h3; subst hs
  have hlen : (pre ++ [G1Frame.output false]).length = pre.length + 1 := by simp
  have hw1 : TM.runConfig (M := GNM)
      (gnFrameCfg n (4 * pre.length)
        (pre ++ G1Frame.blank :: G1Frame.blank :: suffix)
        (.values .writeOutput .p0) (by omega)) 4 =
      gnFrameCfg n (4 * pre.length + 4)
        (pre ++ G1Frame.output false :: G1Frame.blank :: suffix)
        (.values .writeFinish .p0) (by omega) :=
    gnValuesOutputWriter.writeFrameOnList n pre (G1Frame.blank :: suffix)
      G1Frame.blank () (by
        change 4 * pre.length + 4 < GNM.tapeLength n
        omega)
  have hw2 : TM.runConfig (M := GNM)
      (gnFrameCfg n (4 * (pre ++ [G1Frame.output false]).length)
        ((pre ++ [G1Frame.output false]) ++ G1Frame.blank :: suffix)
        (.values .writeFinish .p0) (by rw [hlen]; omega)) 4 =
      gnFrameCfg n (4 * (pre ++ [G1Frame.output false]).length + 4)
        ((pre ++ [G1Frame.output false]) ++ G1Frame.finish :: suffix)
        .requestReady (by rw [hlen]; omega) :=
    gnValuesFinishWriter.writeFrameOnList n (pre ++ [G1Frame.output false])
      suffix G1Frame.blank () (by
        change 4 * (pre ++ [G1Frame.output false]).length + 4 <
          GNM.tapeLength n
        rw [hlen]
        omega)
  have hbridge : gnFrameCfg n (4 * pre.length + 4)
        (pre ++ G1Frame.output false :: G1Frame.blank :: suffix)
        (.values .writeFinish .p0) (by omega) =
      gnFrameCfg n (4 * (pre ++ [G1Frame.output false]).length)
        ((pre ++ [G1Frame.output false]) ++ G1Frame.blank :: suffix)
        (.values .writeFinish .p0) (by rw [hlen]; omega) :=
    gnFrameCfg_ext (by rw [hlen]; omega) (by simp)
  rw [show (8 : Nat) = 4 + 4 from rfl, runConfig_add, hw1, hbridge, hw2]
  exact gnFrameCfg_ext (by rw [hlen]; omega) (by simp)

/-- **The terminal phase.**  From the values boundary standing on the first
reserved output slot, the machine reads that slot, seeks right past every
admissible frame to the scratch frontier blank, returns to it, and writes the
request's `output false`/`finish` tail, in exactly `4 * mid.length + 20`
rows. -/
private theorem gnCS_values_terminal (n head : Nat) (pre mid : List G1Frame)
    (hhead : head = 4 * pre.length)
    (hmid : ∀ f ∈ mid, GNInstallAdmissible f)
    (hroom : 4 * (pre.length + mid.length + 3) < GNM.tapeLength n) :
    TM.runConfig (M := GNM)
        (gnFrameCfg n head
          (gnValuesTerminalFrames pre mid G1Frame.blank G1Frame.blank)
          .valuesEntry (by omega)) (4 * mid.length + 20) =
      gnFrameCfg n (4 * (pre.length + mid.length + 3))
        (gnValuesTerminalFrames pre mid (G1Frame.output false) G1Frame.finish)
        .requestReady hroom := by
  subst hhead
  have hsafe : 4 * pre.length + 4 < GNM.tapeLength n :=
    gnValues_room_le (by omega) hroom
  have hbits : physicalBitsAt hsafe
      (frameListTape (L := GNM.tapeLength n)
        ((gnValuesTerminalFrames pre mid G1Frame.blank G1Frame.blank).flatMap
          G1Frame.bits)) = (G1Frame.output false).bits := by
    simpa only [g1FrameCodec_bits, gnValuesTerminalFrames] using
      physicalBitsAt_flatMap g1FrameCodec pre
        (mid ++ [G1Frame.blank, G1Frame.blank, G1Frame.blank])
        (G1Frame.output false) hsafe
  have hclassify : TM.runConfig (M := GNM)
      (gnFrameCfg n (4 * pre.length)
        (gnValuesTerminalFrames pre mid G1Frame.blank G1Frame.blank)
        .valuesEntry (by omega)) 4 =
      gnFrameCfg n (4 * pre.length + 4)
        (gnValuesTerminalFrames pre mid G1Frame.blank G1Frame.blank)
        (gnValuesClassify (G1Frame.output false)) hsafe :=
    gnCS_values_classify n (4 * pre.length) hsafe _ (G1Frame.output false)
      hbits (fun hc => GNState.noConfusion hc)
  have hpath := gnValuesSeek_validPath hmid
  have hscan : TM.runConfig (M := GNM)
      (gnFrameCfg n (4 * pre.length + 4)
        (gnValuesTerminalFrames pre mid G1Frame.blank G1Frame.blank)
        (gnValuesClassify (G1Frame.output false)) hsafe)
      (4 * (mid.length + 1)) =
      gnFrameCfg n (4 * (pre.length + mid.length + 1) + 4)
        (gnValuesTerminalFrames pre mid G1Frame.blank G1Frame.blank)
        (.values .tailBack (.p3 false false false))
        (gnValues_room_le (by omega) hroom) :=
    gnCS_values_seek n (4 * pre.length + 4)
      (4 * (pre.length + mid.length + 1) + 4) (4 * (mid.length + 1))
      (pre ++ [G1Frame.output false]) (mid ++ [G1Frame.blank])
      [G1Frame.blank, G1Frame.blank]
      (gnValuesTerminalFrames pre mid G1Frame.blank G1Frame.blank)
      (by simp [gnValuesTerminalFrames, List.append_assoc])
      (by simp; omega) (by simp; omega) (by simp) hpath.1 hpath.2
      (gnValues_room_le (by simp; omega) hroom)
  have hback : TM.runConfig (M := GNM)
      (gnFrameCfg n (4 * (pre.length + mid.length + 1) + 4)
        (gnValuesTerminalFrames pre mid G1Frame.blank G1Frame.blank)
        (.values .tailBack (.p3 false false false))
        (gnValues_room_le (by omega) hroom)) 4 =
      gnFrameCfg n (4 * (pre.length + mid.length + 1))
        (gnValuesTerminalFrames pre mid G1Frame.blank G1Frame.blank)
        (.values .writeOutput .p0) (gnValues_room_le (by omega) hroom) :=
    Phased.holdWalk4 gnCS gnCS.startPhase n (4 * (pre.length + mid.length + 1))
      (gnValues_lt (gnValues_room_le (by omega) hroom)) _
      (.values .tailBack (.p3 false false false))
      (.values .tailBack (.p2 false false)) (.values .tailBack (.p1 false))
      (.values .tailBack .p0) (.values .writeOutput .p0)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have hwrite := gnCS_values_tailWrite n (4 * (pre.length + mid.length + 1))
    (4 * (pre.length + mid.length + 3))
    (pre ++ G1Frame.output false :: mid) [G1Frame.blank]
    (gnValuesTerminalFrames pre mid G1Frame.blank G1Frame.blank)
    (gnValuesTerminalFrames pre mid (G1Frame.output false) G1Frame.finish)
    (by simp [gnValuesTerminalFrames, List.append_assoc])
    (by simp [gnValuesTerminalFrames, List.append_assoc])
    (by simp; omega) (by simp; omega)
    (gnValues_room_le (by simp; omega) hroom)
  have hsched : 4 * mid.length + 20 =
      4 + (4 * (mid.length + 1) + (4 + 8)) := by omega
  rw [hsched, runConfig_add, hclassify, runConfig_add, hscan, runConfig_add,
    hback, hwrite]

/-! ## The real-input geometry -/

private theorem gnRecordFrames_cursor_admissible {k : Nat} (g : SLGate k) :
    ∀ f ∈ gnRecordFrames .cursor g, GNInstallAdmissible f := by
  intro f hf
  rw [gnRecordFrames_cursor_split] at hf
  rcases List.mem_cons.1 hf with rfl | hf
  · exact ⟨by decide, by decide⟩
  rcases List.mem_append.1 hf with hf | hf
  · rcases gnGateBodyFrames_body g f hf with rfl | rfl | rfl <;>
      exact ⟨by decide, by decide⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf
    exact ⟨by decide, by decide⟩

private def gnValuesBlockTail (r : GNProgram) (g : SLGate r.inputs.length) :
    List G1Frame :=
  gnSlotFrames (r.program.gates.length - 1) ++ [G1Frame.separator] ++
    gnRecordsFrames .cursor r.program.gates ++
    [G1Frame.separator, G1Frame.output false, G1Frame.finish] ++
    (gnRecordFrames .cursor g).map gnInstallImage

/-- Everything the values pass steps over after the current-value run: the
reserved output slot the run stops on, the remaining slots, the record region,
the word's fixed tail, and the installed scratch image of the selected
record. -/
private def gnValuesBlock (r : GNProgram) (g : SLGate r.inputs.length) : List G1Frame :=
  G1Frame.output false :: gnValuesBlockTail r g

/-- Exact split of the values-boundary word: the leading `bof`, the current
values, and the fixed block.  The first frame after the value run is the first
reserved output slot, which exists because `hg` selects a gate. -/
private theorem gnValuesBlock_frames {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) :
    encodeGNFrames r ++ (gnRecordFrames .cursor g).map gnInstallImage =
      G1Frame.bof :: (r.inputs.map G1Frame.data ++ gnValuesBlock r g) := by
  have hslots : gnSlotFrames r.program.gates.length =
      G1Frame.output false :: gnSlotFrames (r.program.gates.length - 1) := by
    rcases hk : r.program.gates with _ | ⟨first, rest⟩
    · rw [hk] at hg; simp at hg
    · simp [gnSlotFrames, List.replicate_succ]
  simp [encodeGNFrames, gnValuesBlock, gnValuesBlockTail, gnAssignFrames,
    hslots, List.append_assoc]

/-- Every frame of the block is an admissible shuttle/seek frame: it is neither
the destination frontier blank nor the installer's temporary marker. -/
private theorem gnValuesBlock_admissible {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) :
    ∀ f ∈ gnValuesBlock r g, GNInstallAdmissible f := by
  intro f hf
  have hmem : f ∈ encodeGNFrames r ++
      (gnRecordFrames .cursor g).map gnInstallImage := by
    rw [gnValuesBlock_frames hg]
    exact List.mem_cons_of_mem _ (List.mem_append_right _ hf)
  rcases List.mem_append.1 hmem with h | h
  · exact encodeGNFrames_no_blank_no_outputTrue r f h
  · obtain ⟨f0, hf0, rfl⟩ := List.mem_map.1 h
    exact gnInstallImage_laws.2.2.2 f0 (gnRecordFrames_cursor_admissible g f0 hf0)

private theorem gnValuesBlock_length {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) :
    (encodeGNFrames r).length + (gnRecordFrames .cursor g).length =
      r.inputs.length + (gnValuesBlock r g).length + 1 := by
  have h := congrArg List.length (gnValuesBlock_frames hg)
  simp only [List.length_append, List.length_cons, List.length_map] at h
  omega

private theorem gnRecordFrames_length_le {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    (gnRecordFrames .cursor g).length ≤
      (r.program.gates.map (gnRecordSize ∘ gnGateFields)).sum := by
  rcases r with ⟨inputs, ⟨gates⟩⟩
  cases gates with
  | nil => simp at hg
  | cons first rest =>
      simp at hg
      subst g
      simp [gnRecordFrames, g1RecordFrames_length, Function.comp_def]

/-! ## Exact schedule, room, and boundary configuration -/

/-- Exact distance the values shuttle and the tail seek both travel: every
frame of the word strictly after the value under the head, together with the
installed scratch image, and excluding the frontier blank. -/
def gnValuesTailDistance (r : GNProgram) (g : SLGate r.inputs.length) : Nat :=
  (encodeGNFrames r).length + (gnRecordFrames .cursor g).length - 2

/-- Exact tail-phase schedule: four rows read the reserved output slot ending
the current-value run, four per frame seek the frontier and the blank itself,
four return to it, and eight write the request's fixed tail. -/
def gnValuesTailSteps (r : GNProgram) (g : SLGate r.inputs.length) : Nat :=
  4 * gnValuesTailDistance r g + 20

/-- Full real-initial schedule through the completed first request. -/
def gnFirstRequestReadySteps (r : GNProgram) (g : SLGate r.inputs.length) :
    Nat :=
  gnValuesEntrySteps r g + gnValuesTailSteps r g

/-- Exact arithmetic provenance: the distance is the word plus the installed
record less the value under the head and the frontier blank, and the two
schedules are the sums their names claim. -/
theorem gnValuesTailSteps_provenance (r : GNProgram)
    (g : SLGate r.inputs.length) :
    gnValuesTailDistance r g + 2 =
        (encodeGNFrames r).length + (gnRecordFrames .cursor g).length ∧
      gnValuesTailSteps r g = 4 * gnValuesTailDistance r g + 20 ∧
      gnFirstRequestReadySteps r g =
        gnValuesEntrySteps r g + gnValuesTailSteps r g := by
  have hF : 5 ≤ (encodeGNFrames r).length := by
    rw [encodeGNFrames_length]; omega
  refine ⟨?_, rfl, rfl⟩
  unfold gnValuesTailDistance
  omega

/-- **Room, proved internally.**  The whole installed first request, the
retained blank past it, and the head standing on that blank all fit inside the
unchanged memory allocation.  This is never a caller premise. -/
theorem gnFirstRequestReady_room {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) :
    4 * ((encodeGNFrames r).length + (gnRecordFrames .cursor g).length +
      r.inputs.length + 3) < GNM.tapeLength (encodeGN r).length := by
  have hN : (encodeGN r).length = 4 * (encodeGNFrames r).length :=
    encodeGN_length r
  have hF : (encodeGNFrames r).length = r.inputs.length +
      r.program.gates.length +
      (r.program.gates.map (gnRecordSize ∘ gnGateFields)).sum + 5 :=
    encodeGNFrames_length r
  have hR := gnRecordFrames_length_le hg
  have hclock : gnClock (encodeGN r).length =
      512 * ((encodeGN r).length + 1) ^ 2 + 512 := rfl
  have hpow : ((encodeGN r).length + 1) ^ 2 =
      ((encodeGN r).length + 1) * ((encodeGN r).length + 1) := pow_two _
  have hsquare : (encodeGN r).length + 1 ≤
      ((encodeGN r).length + 1) * ((encodeGN r).length + 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  change 4 * ((encodeGNFrames r).length + (gnRecordFrames .cursor g).length +
      r.inputs.length + 3) <
    (encodeGN r).length + gnClock (encodeGN r).length + 1
  rw [hclock, hpow]
  omega

/-- Exact real-input endpoint: the literal `requestReady` state on p0 of the
blank immediately after the installed request, with the original GN word
restored verbatim and the scratch region holding exactly
`encodeG1Frames (gnFirstRequest r g)`. -/
def gnFirstRequestReadyConfig (r : GNProgram) (g : SLGate r.inputs.length)
    (hg : r.program.gates[0]? = some g) :
    Configuration (M := GNM) (encodeGN r).length where
  state := ⟨(0 : Fin 1), .requestReady⟩
  head := ⟨4 * ((encodeGNFrames r).length + (gnRecordFrames .cursor g).length +
      r.inputs.length + 2),
    gnValues_room_le (by omega) (gnFirstRequestReady_room hg)⟩
  tape := frameListTape
    ((encodeGNFrames r ++ encodeG1Frames (gnFirstRequest r g) ++
      [G1Frame.blank]).flatMap G1Frame.bits)

/-! ## The generic and real-input capstones -/

/-- **Generic capstone for the empty current-value run.**  From the GN-E2-4a
values boundary of a program with no inputs, the machine runs exactly
`gnValuesTailSteps r g` rows of genuine `TM.runConfig (M := GNM)` execution and
stops in the exact first-request endpoint.  `hg` and `hinputs` are the only
premises; every room fact is proved internally.  `hinputs` is the scope of this
slice: the copy round a nonempty run needs is not exercised here, and it, its
list induction and the nonempty capstone are GN-E2-5b's obligation. -/
theorem gnCS_valuesTail_exact {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) (hinputs : r.inputs = []) :
    TM.runConfig (M := GNM) (gnValuesEntryConfig r g hg)
        (gnValuesTailSteps r g) = gnFirstRequestReadyConfig r g hg := by
  have hlen := gnValuesBlock_length hg
  have hdist := (gnValuesTailSteps_provenance r g).1
  have hroom := gnFirstRequestReady_room hg
  have hm : r.inputs.length = 0 := by simp [hinputs]
  have hbt : (gnValuesBlock r g).length =
      (gnValuesBlockTail r g).length + 1 := by simp [gnValuesBlock]
  have hmid : (gnValuesBlockTail r g).length = gnValuesTailDistance r g := by
    omega
  have hadm : ∀ f ∈ gnValuesBlockTail r g, GNInstallAdmissible f := fun f hf =>
    gnValuesBlock_admissible hg f (List.mem_cons_of_mem _ hf)
  have hroomT : 4 * (([G1Frame.bof] : List G1Frame).length +
      (gnValuesBlockTail r g).length + 3) <
        GNM.tapeLength (encodeGN r).length :=
    gnValues_room_le (by
      simp only [List.length_cons, List.length_nil]
      omega) hroom
  have hstart : gnValuesEntryConfig r g hg =
      gnFrameCfg (encodeGN r).length 4
        (gnValuesTerminalFrames [G1Frame.bof] (gnValuesBlockTail r g)
          G1Frame.blank G1Frame.blank) .valuesEntry
        (gnValues_room_le (by omega) hroom) := by
    apply Configuration.ext_of_components
    · rfl
    · rfl
    · change frameListTape _ = frameListTape _
      rw [gnValues_tape_blank (encodeGN r).length
          (encodeGNFrames r ++ (gnRecordFrames .cursor g).map gnInstallImage ++
            [G1Frame.blank]),
        gnValues_tape_blank (encodeGN r).length
          (encodeGNFrames r ++ (gnRecordFrames .cursor g).map gnInstallImage ++
            [G1Frame.blank] ++ [G1Frame.blank])]
      rw [gnValuesBlock_frames hg, hinputs]
      simp [gnValuesTerminalFrames, gnValuesBlock, List.append_assoc]
  have hterm := gnCS_values_terminal (encodeGN r).length 4 [G1Frame.bof]
    (gnValuesBlockTail r g) (by simp) hadm hroomT
  have hend : gnFrameCfg (encodeGN r).length
        (4 * (([G1Frame.bof] : List G1Frame).length +
          (gnValuesBlockTail r g).length + 3))
        (gnValuesTerminalFrames [G1Frame.bof] (gnValuesBlockTail r g)
          (G1Frame.output false) G1Frame.finish) .requestReady hroomT =
      gnFirstRequestReadyConfig r g hg := by
    apply Configuration.ext_of_components
    · rfl
    · apply Fin.ext
      show 4 * (([G1Frame.bof] : List G1Frame).length +
          (gnValuesBlockTail r g).length + 3) =
        4 * ((encodeGNFrames r).length + (gnRecordFrames .cursor g).length +
          r.inputs.length + 2)
      simp only [List.length_cons, List.length_nil]
      omega
    · change frameListTape _ = frameListTape _
      rw [encodeG1Frames_eq_prefix, ← gnFirstRecord_image_request_prefix r g]
      simp only [← List.append_assoc]
      rw [gnValuesBlock_frames hg, hinputs]
      simp [gnValuesTerminalFrames, gnValuesBlock, List.append_assoc]
  have hsched : gnValuesTailSteps r g =
      4 * (gnValuesBlockTail r g).length + 20 := by
    rw [hmid, gnValuesTailSteps]
  rw [hsched, hstart, hterm]
  exact hend

/-- **Real-input capstone.**  Starting from the genuine
`GNM.initialConfig (gnPoint (encodeGN r))` and using the actually selected
first gate `g`, an input-free program's machine runs exactly
`gnFirstRequestReadySteps r g` rows of genuine `TM.runConfig (M := GNM)`
execution and stops in the exact first-request endpoint.  Execution stops
there: `requestReady` is dormant, and launch, delegation, commit and looping
all remain later obligations, as does the nonempty-value capstone. -/
theorem gnCS_encodeGN_firstRequestReady_exact {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g)
    (hinputs : r.inputs = []) :
    TM.runConfig (M := GNM) (GNM.initialConfig (gnPoint (encodeGN r)))
        (gnFirstRequestReadySteps r g) = gnFirstRequestReadyConfig r g hg := by
  rw [gnFirstRequestReadySteps, runConfig_add,
    gnCS_encodeGN_valuesEntry_exact hg, gnCS_valuesTail_exact hg hinputs]

/-- Complete exact projections of the real-input endpoint.  The first three
conjuncts pin state, head and the full physical tape — fixing *every* cell,
including the all-false suffix past the retained blank; the fourth expands the
installed scratch region as mapped record, current values, reserved output
slot, `finish` and blank; the fifth is the **pure** list identity making that
expansion the canonical G1 prefix of the request `g` determines; the sixth
records that request's pure semantics at the stage-zero environment.

These are projections of the *configuration definition*, for an arbitrary `r`;
they do not by themselves say the machine reaches it.  The execution statement
is `gnCS_encodeGN_firstRequestReady_exact`, which this slice proves for
`r.inputs = []`.  The last two conjuncts are about the **pure** request:
nothing here says the machine has evaluated anything. -/
theorem gnFirstRequestReadyConfig_structure {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    (gnFirstRequestReadyConfig r g hg).state =
        ⟨(0 : Fin 1), GNState.requestReady⟩ ∧
      ((gnFirstRequestReadyConfig r g hg).head : Nat) =
        4 * ((encodeGNFrames r).length + (gnRecordFrames .cursor g).length +
          r.inputs.length + 2) ∧
      (gnFirstRequestReadyConfig r g hg).tape =
        frameListTape
          ((encodeGNFrames r ++ encodeG1Frames (gnFirstRequest r g) ++
            [G1Frame.blank]).flatMap G1Frame.bits) ∧
      encodeGNFrames r ++ encodeG1Frames (gnFirstRequest r g) ++
          [G1Frame.blank] =
        encodeGNFrames r ++ (gnRecordFrames .cursor g).map gnInstallImage ++
          r.inputs.map G1Frame.data ++
            [G1Frame.output false, G1Frame.finish, G1Frame.blank] ∧
      (gnRecordFrames .cursor g).map gnInstallImage ++
          (gnCurrentValues r []).map G1Frame.data =
        g1PrefixFrames (gnFirstRequest r g) ∧
      (gnFirstRequest r g).spec =
        g.compute (fun i => r.inputs[i.val]'(by omega)) [] := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · rw [encodeG1Frames_eq_prefix, ← gnFirstRecord_image_request_prefix r g]
    simp [List.append_assoc]
  · rw [gnCurrentValues_zero]
    exact gnFirstRecord_image_request_prefix r g
  · have h := (gnWorkRequest_spec (r := r) (prior := []) (g := g) hg).1
    rw [gnCurrentValues_zero] at h
    exact h

/-- Scoped clock fact: the complete proved prefix — validation, locator, the
`firstRecord` door, the cursor seed shuttle, the first-record body driver, the
values rewind and the fixed tail write — fits inside the
unchanged public `gnClock`.  This bounds exactly that prefix.  It is **not** a
total installer, multigate, or runtime clock theorem. -/
theorem gnFirstRequestReadySteps_le_gnClock {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    gnFirstRequestReadySteps r g ≤ gnClock (encodeGN r).length := by
  have hs := encodeGNFrames_firstRecord_split hg
  have hmidsplit := gnFirstRecordMiddle_split hg
  have hn : (encodeGN r).length =
      4 * (gnRecordsStart r + 1 + (gnFirstRecordMiddle r).length) := by
    rw [encodeGN_length, hs.1]
    simp only [List.length_append, List.length_cons, gnFirstRecordMiddle,
      List.length_nil]
    omega
  have hsplit : (gnFirstRecordMiddle r).length =
      (gnGateBodyFrames g).length + 1 + (gnFirstRecordTail r).length := by
    rw [hmidsplit]
    simp only [List.length_append, List.length_cons]
    omega
  have hsize : gnRecordSize (gnGateFields g) =
      (gnGateBodyFrames g).length + 2 := by
    simp only [gnRecordSize, gnGateBodyFrames, List.length_append,
      List.length_replicate, List.length_cons, List.length_nil]
    omega
  have hstart : gnRecordsStart r =
      r.inputs.length + r.program.gates.length + 2 := rfl
  have hseed := gnBofSeedSteps_provenance r
  have hprod : (gnGateBodyFrames g).length *
        (8 * (gnFirstRecordMiddle r).length + 30) ≤
      (gnFirstRecordMiddle r).length *
        (8 * (gnFirstRecordMiddle r).length + 30) :=
    Nat.mul_le_mul_right _ (by omega)
  have hexp : (gnFirstRecordMiddle r).length *
        (8 * (gnFirstRecordMiddle r).length + 30) =
      8 * ((gnFirstRecordMiddle r).length * (gnFirstRecordMiddle r).length) +
        30 * (gnFirstRecordMiddle r).length := by
    rw [Nat.mul_add, Nat.mul_left_comm,
      Nat.mul_comm (gnFirstRecordMiddle r).length 30]
  have hsq : (gnFirstRecordMiddle r).length * (gnFirstRecordMiddle r).length ≤
      ((encodeGN r).length + 1) * ((encodeGN r).length + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hF : (encodeGNFrames r).length = r.inputs.length +
      r.program.gates.length +
      (r.program.gates.map (gnRecordSize ∘ gnGateFields)).sum + 5 :=
    encodeGNFrames_length r
  have hNF : (encodeGN r).length = 4 * (encodeGNFrames r).length :=
    encodeGN_length r
  have hR := gnRecordFrames_length_le hg
  have hdist := (gnValuesTailSteps_provenance r g).1
  have hpow : ((encodeGN r).length + 1) ^ 2 =
      ((encodeGN r).length + 1) * ((encodeGN r).length + 1) := pow_two _
  have hsquare : (encodeGN r).length + 1 ≤
      ((encodeGN r).length + 1) * ((encodeGN r).length + 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hclock : gnClock (encodeGN r).length =
      512 * ((encodeGN r).length + 1) ^ 2 + 512 := rfl
  rw [gnFirstRequestReadySteps, gnValuesTailSteps, gnValuesEntrySteps,
    gnValuesRewindSteps, gnFirstRecordDoneSteps, gnBodyDriverSteps,
    gnBodyRoundSteps, gnBodyTerminalSteps, hclock, hpow]
  rw [hexp] at hprod
  omega

/-! ## Executable rejection at the new values ingress -/

/-- **Exact four-row rejection at the values boundary.**  The reserved code
`1101`, supplied at an arbitrary aligned window under the head, reaches the
existing stationary reject sink in exactly four rows of genuine
`TM.runConfig (M := GNM)` execution, with the head left on the window's last
cell and the caller's tape untouched. -/
theorem gnCS_valuesEntry_reserved1101_reject_four (n base : Nat)
    (hsafe : base + 4 < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool)
    (hbits : physicalBitsAt hsafe tape = [true, true, false, true]) :
    TM.runConfig (M := GNM)
        (Phased.alignedAt gnCS gnCS.startPhase n base (gnValues_lt (by omega))
          tape .valuesEntry) 4 =
      Phased.alignedAt gnCS gnCS.startPhase n (base + 3)
        (gnValues_lt (by omega)) tape .reject := by
  have hcells : tape ⟨base, by omega⟩ = true ∧
      tape ⟨base + 1, by omega⟩ = true ∧
      tape ⟨base + 2, by omega⟩ = false ∧
      tape ⟨base + 3, by omega⟩ = true := by
    simpa only [physicalBitsAt, List.cons.injEq, and_true] using hbits
  obtain ⟨h0, h1, h2, _⟩ := hcells
  have s3 := gnCS_valuesStay n (base + 3) (by omega) tape
    (.values .probe (.p3 true true false)) .reject (fun scan => by
      cases scan <;>
        exact (gnTransition_values_decision gnCS.startPhase true true false
          _).2.1 rfl)
  show TM.runConfig (M := GNM) _ (3 + 1) = _
  rw [runConfig_add,
    gnCS_values_buffer n base hsafe tape true true false h0 h1 h2,
    runConfig_one, s3]

/-- Stable reject padding after that exact four-row values failure: the sink is
the existing absorbing one, so extra budget changes nothing. -/
theorem gnCS_valuesEntry_reserved1101_reject_stable (n base : Nat)
    (hsafe : base + 4 < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool)
    (hbits : physicalBitsAt hsafe tape = [true, true, false, true]) (k : Nat) :
    TM.runConfig (M := GNM)
        (Phased.alignedAt gnCS gnCS.startPhase n base (gnValues_lt (by omega))
          tape .valuesEntry) (4 + k) =
      Phased.alignedAt gnCS gnCS.startPhase n (base + 3)
        (gnValues_lt (by omega)) tape .reject := by
  rw [runConfig_add,
    gnCS_valuesEntry_reserved1101_reject_four n base hsafe tape hbits]
  exact gnCS_reject_stable _ rfl k

/-! ## One literal real-input first request -/

namespace GNValuesWriterProbes

open GNFixedDelegateProbes

theorem oneConstFalseGate_mem : oneConstFalseProgram.program.gates[0]? =
    some (SLGate.const false : SLGate 0) := rfl

theorem oneConstFalseNoInputs : oneConstFalseProgram.inputs = [] := rfl

/-- The 21 literal endpoint frames of the zero-input program: the restored
twelve-frame GN word, the installed request, and the retained blank. -/
def oneConstFalseRequestReadyFrames : List G1Frame :=
  [G1Frame.bof, .output false, .separator, .cursor, .tag, .tag, .argSep,
    .argSep, .finish, .separator, .output false, .finish, .bof, .tag, .tag,
    .argSep, .argSep, .separator, .output false, .finish, .blank]

def oneConstFalseRequestReadyConfig : Configuration (M := GNM) 48 where
  state := ⟨(0 : Fin 1), .requestReady⟩
  head := ⟨80, by decide⟩
  tape := frameListTape (oneConstFalseRequestReadyFrames.flatMap G1Frame.bits)

/-- Kernel-confirmed literal capstone: 784 rows of genuine execution from the
real initial configuration reach `requestReady` at physical head 80.  The fifth
and sixth conjuncts show the original twelve-frame GN word restored verbatim
and the written tail followed by the retained blank; the seventh shows the
installer's temporary marker is gone.  The last four assert changed destination
*bits* rather than a different state: cell 72 of the written `output false`
frame and cell 76 of the written `finish` frame are `true` here and `false` at
the GN-E2-4a boundary, where both frames were blank.  This program has no
inputs, so no copy round runs; it is **not** a data-copy witness. -/
theorem literal_oneConstFalse_requestReady :
    TM.runConfig (M := GNM)
        (GNM.initialConfig (gnPoint (encodeGN oneConstFalseProgram))) 784 =
      oneConstFalseRequestReadyConfig ∧
    (oneConstFalseRequestReadyConfig.head : Nat) = 80 ∧
    oneConstFalseRequestReadyConfig.state =
      ⟨(0 : Fin 1), GNState.requestReady⟩ ∧
    oneConstFalseRequestReadyConfig.tape =
      frameListTape (oneConstFalseRequestReadyFrames.flatMap G1Frame.bits) ∧
    oneConstFalseRequestReadyFrames.take 12 =
      encodeGNFrames oneConstFalseProgram ∧
    oneConstFalseRequestReadyFrames.drop 18 =
      [G1Frame.output false, G1Frame.finish, G1Frame.blank] ∧
    G1Frame.output true ∉ oneConstFalseRequestReadyFrames ∧
    oneConstFalseRequestReadyConfig.tape ⟨72, by decide⟩ = true ∧
    oneConstFalseRequestReadyConfig.tape ⟨76, by decide⟩ = true ∧
    (gnValuesEntryConfig oneConstFalseProgram (SLGate.const false)
        oneConstFalseGate_mem).tape ⟨72, by decide⟩ = false ∧
    (gnValuesEntryConfig oneConstFalseProgram (SLGate.const false)
        oneConstFalseGate_mem).tape ⟨76, by decide⟩ = false := by
  have hrun := gnCS_encodeGN_firstRequestReady_exact oneConstFalseGate_mem
    oneConstFalseNoInputs
  have hsched : gnFirstRequestReadySteps oneConstFalseProgram
      (SLGate.const false : SLGate 0) = 784 := by decide
  rw [hsched] at hrun
  refine ⟨hrun.trans ?_, rfl, rfl, rfl, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  apply Configuration.ext_of_components
  · rfl
  · rfl
  · rfl

end GNValuesWriterProbes

end Pnp3.Internal.PsubsetPpoly.TM
