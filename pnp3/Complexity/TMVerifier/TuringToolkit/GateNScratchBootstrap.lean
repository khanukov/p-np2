import Complexity.TMVerifier.TuringToolkit.GateNFrameShuttle
import Complexity.TMVerifier.TuringToolkit.GateNFirstInstallBridge

/-!
# GN-E2-1c live read-only scratch bootstrap (2026-09-02)

**Progress classification: infrastructure, not P-vs-NP mainline progress.**

This module proves the live pass after `scratchEntry` is activated in the fixed
GN control.  It leaves the whole scratch slice `[N, …)` blank and writes every
scanned source bit back unchanged.  On a nonempty stage-zero program it stops
on p0 of the unique `cursor` in fixed `firstRecord`; on an empty program it
stops on the adjacent earlier `separator` in fixed `noGate`.

Both arrival states are dormant.  In particular this slice performs no
`cursor → bof` source-boundary transform, does not enter `install`, and does
not execute the shuttle.  The final theorem exposes exactly the source,
middle, first-blank, and room facts needed by the next GN-E2-2 handoff.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan
open Encoding

/-! ## Exact stage-zero frame shapes -/

/-- Frames strictly before the stage-zero record region. -/
def gnLocatePrefix (r : GNProgram) : List G1Frame :=
  [.bof] ++ gnAssignFrames r.inputs ++ gnSlotFrames r.program.gates.length ++
    [.separator]

/-- Frames strictly after the first record's `cursor` and before the terminal
record-region separator. -/
def gnFirstRecordInner (r : GNProgram) : List G1Frame :=
  (gnRecordsFrames .cursor r.program.gates).drop 1

/-- The forward middle from the first `cursor` to the first scratch blank. -/
def gnFirstRecordMiddle (r : GNProgram) : List G1Frame :=
  gnFirstRecordInner r ++ [.separator, .output false, .finish]

/-- Exact nonempty stage-zero split, with the prefix and inner lengths needed
for physical head and schedule arithmetic. -/
theorem encodeGNFrames_firstRecord_split {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    encodeGNFrames r =
        gnLocatePrefix r ++ .cursor :: gnFirstRecordInner r ++
          [.separator, .output false, .finish] ∧
      (gnLocatePrefix r).length = gnRecordsStart r ∧
      (gnFirstRecordInner r).length + 1 = gnRecordsLength r := by
  rcases r with ⟨inputs, ⟨gates⟩⟩
  cases gates with
  | nil => simp at hg
  | cons first rest =>
      simp at hg
      subst g
      constructor
      · simp [encodeGNFrames, gnLocatePrefix, gnFirstRecordInner,
          gnAssignFrames, gnSlotFrames, gnRecordsFrames,
          gnFieldRecordsFrames, g1RecordFrames, List.append_assoc]
      constructor
      · simp [gnLocatePrefix, gnRecordsStart]
        omega
      · simp only [gnFirstRecordInner, List.length_drop]
        rw [gnRecordsFrames_length]
        simp only [gnRecordsLength, List.map_cons, List.sum_cons,
          Function.comp_apply]
        have hpos : 1 ≤ gnRecordSize (gnGateFields first) := by
          simp [gnRecordSize]
        omega

/-- Exact empty stage-zero split. -/
theorem encodeGNFrames_noGate_split {r : GNProgram}
    (hg : r.program.gates = []) :
    encodeGNFrames r =
      [.bof] ++ gnAssignFrames r.inputs ++
        [.separator] ++ [.separator] ++ [.output false, .finish] := by
  simp [encodeGNFrames, hg, gnSlotFrames, gnRecordsFrames,
    gnFieldRecordsFrames, List.append_assoc]

private theorem gnFieldRecordsFrames_no_forbidden (marker : G1Frame)
    (hm : marker ≠ .blank ∧ marker ≠ .output true) (fields : List GNField) :
    ∀ frame ∈ gnFieldRecordsFrames marker fields,
      frame ≠ .blank ∧ frame ≠ .output true := by
  induction fields generalizing marker with
  | nil => simp [gnFieldRecordsFrames]
  | cons field rest ih =>
      intro frame hframe
      rw [gnFieldRecordsFrames, List.mem_append] at hframe
      rcases hframe with hframe | hframe
      · rcases field with ⟨tag, a1, a2⟩
        have hb : G1Frame.blank ∉
            g1RecordFrames marker (tag, a1, a2) := by
          simp [g1RecordFrames, ne_comm.mp hm.1]
        have ht : G1Frame.output true ∉
            g1RecordFrames marker (tag, a1, a2) := by
          simp [g1RecordFrames, ne_comm.mp hm.2]
        exact ⟨fun h => hb (h ▸ hframe), fun h => ht (h ▸ hframe)⟩
      · exact ih .bof (by decide) frame hframe

/-- Canonical initial GN words contain neither blank nor the installer's
temporary `output true` marker. -/
theorem encodeGNFrames_no_blank_no_outputTrue (r : GNProgram) :
    ∀ frame ∈ encodeGNFrames r,
      frame ≠ .blank ∧ frame ≠ .output true := by
  rcases r with ⟨inputs, ⟨gates⟩⟩
  have hrecords := gnFieldRecordsFrames_no_forbidden .cursor (by decide)
    (gates.map gnGateFields)
  have hbrec : G1Frame.blank ∉
      gnFieldRecordsFrames .cursor (gates.map gnGateFields) := by
    intro h
    exact (hrecords .blank h).1 rfl
  have htrec : G1Frame.output true ∉
      gnFieldRecordsFrames .cursor (gates.map gnGateFields) := by
    intro h
    exact (hrecords (.output true) h).2 rfl
  intro frame hframe
  constructor
  · intro h
    subst frame
    simp [encodeGNFrames, gnAssignFrames, gnSlotFrames, gnRecordsFrames,
      hbrec] at hframe
  · intro h
    subst frame
    simp [encodeGNFrames, gnAssignFrames, gnSlotFrames, gnRecordsFrames,
      htrec] at hframe

/-- The first-record marker is unique in a nonempty initial GN word. -/
theorem encodeGNFrames_cursor_unique {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    (encodeGNFrames r).count .cursor = 1 := by
  have hrecords := encodeGNAtFrames_zero_cursor_unique hg
  have hr : (gnRecordsFrames .cursor r.program.gates).count .cursor = 1 := by
    simpa [gnRecordsAtFrames] using hrecords
  have hi : (r.inputs.map G1Frame.data).count .cursor = 0 := by
    induction r.inputs with
    | nil => rfl
    | cons b rest ih => cases b <;> simp [ih]
  have hs : (List.replicate r.program.gates.length
      (G1Frame.output false)).count G1Frame.cursor = 0 := by
    simp [List.count_replicate]
  simp [encodeGNFrames, List.count_append, gnAssignFrames, gnSlotFrames,
    hi, hs, hr]

/-! ## Same-machine reverse scanner -/

/-- Collapse the three terminal locator modes to their fixed outer states. -/
def gnLocateStopState : GNLocateMode → GNState
  | .firstRecord => .firstRecord
  | .noGate => .noGate
  | _ => .reject

/-- The strict locator as an instance of the shared reverse scanner kernel. -/
def gnLocateScanner :
    ReverseFrameScanner GNState G1Frame GNLocateMode Unit where
  program := gnCS
  phase := gnCS.startPhase
  codec := g1FrameCodec
  Stop := GNLocateMode.Stop
  revAdvance := gnLocateAdvance
  revComplete := gnLocateComplete
  Reverse := GNLocateMode.Reverse
  rst3 := fun mode _ => .locating ⟨mode, .r3⟩
  rst2 := fun mode _ b3 => .locating ⟨mode, .r2 b3⟩
  rst1 := fun mode _ b2 b3 => .locating ⟨mode, .r1 b2 b3⟩
  rst0 := fun mode _ b1 b2 b3 => .locating ⟨mode, .r0 b1 b2 b3⟩
  stopState := fun mode _ => gnLocateStopState mode
  revComplete_decode := by
    intro mode frame b0 b1 b2 b3 h
    simp only [gnLocateComplete]
    rw [show decodeG1Frame? [b0, b1, b2, b3] = some frame by
      simpa using h]
  rstep_p3 := by
    intro mode hm _ scan
    cases mode <;> simp [GNLocateMode.Reverse] at hm
    all_goals rfl
  rstep_p2 := by
    intro mode hm _ b3 scan
    cases mode <;> simp [GNLocateMode.Reverse] at hm
    all_goals rfl
  rstep_p1 := by
    intro mode hm _ b2 b3 scan
    cases mode <;> simp [GNLocateMode.Reverse] at hm
    all_goals rfl
  rstep_p0 := by
    intro mode hm _ b1 b2 b3 scan hstop
    cases mode <;> simp [GNLocateMode.Reverse] at hm
    all_goals cases scan <;> cases b1 <;> cases b2 <;> cases b3 <;>
      simp_all [gnCS, gnTransition, gnLocateComplete, gnLocateAdvance,
        GNLocateMode.Stop, decodeG1Frame?]
  rstep_p0_stop := by
    intro mode hm _ b1 b2 b3 scan hstop
    cases mode <;> simp [GNLocateMode.Reverse] at hm
    all_goals cases scan <;> cases b1 <;> cases b2 <;> cases b3 <;>
      simp_all [gnCS, gnTransition, gnLocateComplete, gnLocateAdvance,
        GNLocateMode.Stop, gnLocateStopState, decodeG1Frame?]

/-- A raw undecodable reverse window enters the existing stationary reject
sink at p0, preserving the scanned bit and head position. -/
theorem gnTransition_locate_none (phase : Fin 1) (mode : GNLocateMode)
    (b0 b1 b2 b3 : Bool)
    (hbad : decodeG1Frame? [b0, b1, b2, b3] = none) :
    gnTransition phase (.locating ⟨mode, .r0 b1 b2 b3⟩) b0 =
      (0, .reject, b0, .stay) := by
  simp [gnTransition, gnLocateComplete, hbad]

/-- A decoded frame rejected by the strict grammar takes the same literal
read-only, stationary reject row. -/
theorem gnTransition_locate_decoded_reject (phase : Fin 1)
    (mode : GNLocateMode) (frame : G1Frame) (b0 b1 b2 b3 : Bool)
    (hdecode : decodeG1Frame? [b0, b1, b2, b3] = some frame)
    (hbad : gnLocateAdvance mode frame = .reject) :
    gnTransition phase (.locating ⟨mode, .r0 b1 b2 b3⟩) b0 =
      (0, .reject, b0, .stay) := by
  simp [gnTransition, gnLocateComplete, hdecode, hbad]

/-- The three reserved public-code windows are raw locator rejection rows. -/
theorem gnTransition_locate_reserved (phase : Fin 1) (mode : GNLocateMode) :
    gnTransition phase (.locating ⟨mode, .r0 true false true⟩) true =
        (0, .reject, true, .stay) ∧
      gnTransition phase (.locating ⟨mode, .r0 true true false⟩) true =
        (0, .reject, true, .stay) ∧
      gnTransition phase (.locating ⟨mode, .r0 true true true⟩) true =
        (0, .reject, true, .stay) := by
  exact ⟨gnTransition_locate_none phase mode true true false true rfl,
    gnTransition_locate_none phase mode true true true false rfl,
    gnTransition_locate_none phase mode true true true true rfl⟩

/-- Private exact four-row raw reverse rejection helper. -/
private theorem gnCS_locate_reject_four (n base : Nat)
    (hsafe : base + 4 < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool) (mode : GNLocateMode)
    (b0 b1 b2 b3 : Bool)
    (hbits : physicalBitsAt hsafe tape = [b0, b1, b2, b3])
    (hreject : gnLocateComplete mode b0 b1 b2 b3 = .reject) :
    TM.runConfig (M := GNM)
        (Phased.alignedAt gnCS gnCS.startPhase n (base + 3)
          (by exact lt_trans (by omega) hsafe) tape
          (.locating ⟨mode, .r3⟩)) 4 =
      Phased.alignedAt gnCS gnCS.startPhase n base
        (by exact lt_trans (by omega) hsafe) tape .reject := by
  have hmachine : (Phased.machine gnCS).tapeLength n = GNM.tapeLength n := rfl
  have hcells :
      tape ⟨base, by omega⟩ = b0 ∧
        tape ⟨base + 1, by omega⟩ = b1 ∧
        tape ⟨base + 2, by omega⟩ = b2 ∧
        tape ⟨base + 3, by omega⟩ = b3 := by
    simpa only [physicalBitsAt, List.cons.injEq, and_true] using hbits
  rcases hcells with ⟨h0, h1, h2, h3⟩
  show TM.runConfig (M := GNM) _ (1 + 1 + 1 + 1) = _
  rw [runConfig_add, runConfig_add, runConfig_add]
  simp only [runConfig_one]
  have s3 : TM.stepConfig (M := GNM)
      (Phased.alignedAt gnCS gnCS.startPhase n (base + 3)
          (by exact lt_trans (by omega) hsafe) tape (.locating ⟨mode, .r3⟩)) =
      Phased.alignedAt gnCS gnCS.startPhase n (base + 2) (by omega) tape
        (.locating ⟨mode, .r2 (tape ⟨base + 3, by omega⟩)⟩) := by
    have h := Phased.stepLeft gnCS gnCS.startPhase n (base + 3) (by omega) (by omega) tape (.locating ⟨mode, .r3⟩)
      (.locating ⟨mode, .r2 (tape ⟨base + 3, by omega⟩)⟩)
      (tape ⟨base + 3, by omega⟩) (by rfl)
    rw [writeCell_self] at h
    simpa using h
  rw [s3]
  have s2 : TM.stepConfig (M := GNM)
      (Phased.alignedAt gnCS gnCS.startPhase n (base + 2) (by omega) tape
        (.locating ⟨mode, .r2 (tape ⟨base + 3, by omega⟩)⟩)) =
      Phased.alignedAt gnCS gnCS.startPhase n (base + 1) (by omega) tape
        (.locating ⟨mode, .r1 (tape ⟨base + 2, by omega⟩)
          (tape ⟨base + 3, by omega⟩)⟩) := by
    have h := Phased.stepLeft gnCS gnCS.startPhase n (base + 2) (by omega) (by omega) tape
      (.locating ⟨mode, .r2 (tape ⟨base + 3, by omega⟩)⟩)
      (.locating ⟨mode, .r1 (tape ⟨base + 2, by omega⟩)
        (tape ⟨base + 3, by omega⟩)⟩)
      (tape ⟨base + 2, by omega⟩) (by rfl)
    rw [writeCell_self] at h
    simpa using h
  rw [s2]
  have s1 : TM.stepConfig (M := GNM)
      (Phased.alignedAt gnCS gnCS.startPhase n (base + 1) (by omega) tape
        (.locating ⟨mode, .r1 (tape ⟨base + 2, by omega⟩)
          (tape ⟨base + 3, by omega⟩)⟩)) =
      Phased.alignedAt gnCS gnCS.startPhase n base (by omega) tape
        (.locating ⟨mode, .r0 (tape ⟨base + 1, by omega⟩)
          (tape ⟨base + 2, by omega⟩) (tape ⟨base + 3, by omega⟩)⟩) := by
    have h := Phased.stepLeft gnCS gnCS.startPhase n (base + 1) (by omega) (by omega) tape
      (.locating ⟨mode, .r1 (tape ⟨base + 2, by omega⟩)
        (tape ⟨base + 3, by omega⟩)⟩)
      (.locating ⟨mode, .r0 (tape ⟨base + 1, by omega⟩)
        (tape ⟨base + 2, by omega⟩) (tape ⟨base + 3, by omega⟩)⟩)
      (tape ⟨base + 1, by omega⟩) (by rfl)
    rw [writeCell_self] at h
    simpa using h
  rw [s1]
  have s0 := Phased.stepStay gnCS gnCS.startPhase n base (by omega) tape
    (.locating ⟨mode, .r0 (tape ⟨base + 1, by omega⟩)
      (tape ⟨base + 2, by omega⟩) (tape ⟨base + 3, by omega⟩)⟩)
    .reject (tape ⟨base, by omega⟩) (by
      simp [gnCS, gnTransition, h0, h1, h2, h3, hreject])
  rwa [writeCell_self] at s0

/-- The reserved word `1101`, supplied at an arbitrary aligned locator window,
reaches outer reject in exactly four rows with p0 and the full tape fixed. -/
theorem gnCS_locate_reserved1101_reject_four (n base : Nat)
    (hsafe : base + 4 < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool) (mode : GNLocateMode)
    (hbits : physicalBitsAt hsafe tape = [true, true, false, true]) :
    TM.runConfig (M := GNM)
        (Phased.alignedAt gnCS gnCS.startPhase n (base + 3)
          (by exact lt_trans (by omega) hsafe) tape
          (.locating ⟨mode, .r3⟩)) 4 =
      Phased.alignedAt gnCS gnCS.startPhase n base
        (by exact lt_trans (by omega) hsafe) tape .reject :=
  gnCS_locate_reject_four n base hsafe tape mode true true false true hbits
    (gnLocateComplete_reserved mode).1

/-- The literal four-row `1101` rejection admits arbitrary stable reject-sink
padding while retaining the same state, p0 head, and caller-supplied tape. -/
theorem gnCS_locate_reserved1101_reject_stable (n base : Nat)
    (hsafe : base + 4 < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool) (mode : GNLocateMode)
    (hbits : physicalBitsAt hsafe tape = [true, true, false, true]) (k : Nat) :
    TM.runConfig (M := GNM)
        (Phased.alignedAt gnCS gnCS.startPhase n (base + 3)
          (by exact lt_trans (by omega) hsafe) tape
          (.locating ⟨mode, .r3⟩)) (4 + k) =
      Phased.alignedAt gnCS gnCS.startPhase n base
        (by exact lt_trans (by omega) hsafe) tape .reject := by
  rw [runConfig_add, gnCS_locate_reserved1101_reject_four n base hsafe tape mode
    hbits]
  exact gnCS_reject_stable _ rfl k

private theorem gnLocateScanner_machine : gnLocateScanner.machine = GNM := rfl

private theorem gnLocateScanner_advanceList (mode : GNLocateMode)
    (frames : List G1Frame) :
    gnLocateScanner.revAdvanceList mode frames =
      gnLocateAdvanceList mode frames := rfl

private theorem gnLocateScanner_validPath (mode : GNLocateMode)
    (frames : List G1Frame) :
    gnLocateScanner.RevValidPath mode frames ↔
      GNLocateRevValidPath mode frames := by
  unfold ReverseFrameScanner.RevValidPath GNLocateRevValidPath
  have h : ∀ (list : List G1Frame) (m : GNLocateMode),
      gnLocateScanner.RevPathFrom m list ↔ GNLocateRevPathFrom m list := by
    intro list
    induction list with
    | nil => intro m; exact Iff.rfl
    | cons frame rest ih =>
        intro m
        simp only [ReverseFrameScanner.RevPathFrom, GNLocateRevPathFrom]
        change (m.Reverse ∧ ¬(gnLocateAdvance m frame).Stop ∧
            gnLocateScanner.RevPathFrom (gnLocateAdvance m frame) rest) ↔ _
        rw [ih (gnLocateAdvance m frame)]
  exact h frames.reverse mode

/-! ## Canonical reverse-language paths -/

/-- A pure reading-order segment, with both its final mode and its nonstopping
path. -/
private def GNLocateReadTo (mode : GNLocateMode) (frames : List G1Frame)
    (final : GNLocateMode) : Prop :=
  frames.foldl gnLocateAdvance mode = final ∧
    GNLocateRevPathFrom mode frames

private theorem gnLocateRevPathFrom_append (mode : GNLocateMode)
    (left right : List G1Frame) :
    GNLocateRevPathFrom mode (left ++ right) ↔
      GNLocateRevPathFrom mode left ∧
        GNLocateRevPathFrom (left.foldl gnLocateAdvance mode) right := by
  induction left generalizing mode with
  | nil => simp [GNLocateRevPathFrom]
  | cons frame rest ih =>
      simp only [List.cons_append, GNLocateRevPathFrom, List.foldl_cons]
      rw [ih (gnLocateAdvance mode frame)]
      tauto

private theorem GNLocateReadTo.append {m m' m'' : GNLocateMode}
    {left right : List G1Frame}
    (hl : GNLocateReadTo m left m') (hr : GNLocateReadTo m' right m'') :
    GNLocateReadTo m (left ++ right) m'' := by
  rcases hl with ⟨hl, hp⟩
  rcases hr with ⟨hr, hq⟩
  constructor
  · simpa [List.foldl_append, hl] using hr
  · rw [gnLocateRevPathFrom_append, hl]
    exact ⟨hp, hq⟩

private theorem gnLocateRead_arg2_indices (n : Nat) :
    GNLocateReadTo .arg2 (List.replicate n .index) .arg2 := by
  induction n with
  | zero => simp [GNLocateReadTo, GNLocateRevPathFrom]
  | succ n ih =>
      simpa [List.replicate_succ, GNLocateReadTo, GNLocateRevPathFrom,
        GNLocateMode.Reverse, GNLocateMode.Stop, gnLocateAdvance] using ih

private theorem gnLocateRead_arg1_indices (n : Nat) :
    GNLocateReadTo .arg1 (List.replicate n .index) .arg1 := by
  induction n with
  | zero => simp [GNLocateReadTo, GNLocateRevPathFrom]
  | succ n ih =>
      simpa [List.replicate_succ, GNLocateReadTo, GNLocateRevPathFrom,
        GNLocateMode.Reverse, GNLocateMode.Stop, gnLocateAdvance] using ih

private theorem gnLocateRead_tags (tag : G1Tag) :
    ∃ mode, GNLocateReadTo .tag0 (List.replicate tag.units .tag) mode ∧
      mode.Reverse ∧
      gnLocateAdvance mode .bof = .moreRecord ∧
      gnLocateAdvance mode .cursor = .firstRecord := by
  cases tag <;>
    simp [G1Tag.units, GNLocateReadTo, GNLocateRevPathFrom,
      GNLocateMode.Reverse, GNLocateMode.Stop, gnLocateAdvance]

/-- Reading any canonical record body from either record-entry mode reaches a
finite tag-count mode at which `bof` continues and `cursor` is the stop. -/
private theorem gnLocateRead_recordBody (entry : GNLocateMode)
    (hentry : entry = .recordEdge ∨ entry = .moreRecord) (field : GNField) :
    ∃ mode, GNLocateReadTo entry
        ((g1RecordFrames .cursor field).drop 1).reverse mode ∧
      mode.Reverse ∧
      gnLocateAdvance mode .bof = .moreRecord ∧
      gnLocateAdvance mode .cursor = .firstRecord := by
  rcases field with ⟨tag, a1, a2⟩
  have hfinish : GNLocateReadTo entry [.finish] .arg2 := by
    rcases hentry with rfl | rfl <;>
      simp [GNLocateReadTo, GNLocateRevPathFrom, GNLocateMode.Reverse,
        GNLocateMode.Stop, gnLocateAdvance]
  have h2 := hfinish.append (gnLocateRead_arg2_indices a2)
  have hsep2 : GNLocateReadTo .arg2 [.argSep] .arg1 := by
    simp [GNLocateReadTo, GNLocateRevPathFrom, GNLocateMode.Reverse,
      GNLocateMode.Stop, gnLocateAdvance]
  have h3 := h2.append hsep2
  have h4 := h3.append (gnLocateRead_arg1_indices a1)
  have hsep1 : GNLocateReadTo .arg1 [.argSep] .tag0 := by
    simp [GNLocateReadTo, GNLocateRevPathFrom, GNLocateMode.Reverse,
      GNLocateMode.Stop, gnLocateAdvance]
  have h5 := h4.append hsep1
  obtain ⟨mode, htags, hrev, hbof, hcursor⟩ := gnLocateRead_tags tag
  refine ⟨mode, ?_, hrev, hbof, hcursor⟩
  have hall := h5.append htags
  simpa [g1RecordFrames, List.reverse_append, List.append_assoc] using hall

/-- Tail plus any list of later `bof` records is a valid reverse path and
leaves either the initial record edge or the continuing-record mode. -/
private theorem gnLocateRead_laterTail (fields : List GNField) :
    ∃ mode, GNLocateReadTo .tailFinish
        (gnFieldRecordsFrames .bof fields ++
          [G1Frame.separator, G1Frame.output false, G1Frame.finish]).reverse mode ∧
      (mode = .recordEdge ∨ mode = .moreRecord) := by
  induction fields with
  | nil =>
      refine ⟨.recordEdge, ?_, Or.inl rfl⟩
      simp [gnFieldRecordsFrames, GNLocateReadTo, GNLocateRevPathFrom,
        GNLocateMode.Reverse, GNLocateMode.Stop, gnLocateAdvance]
  | cons field rest ih =>
      obtain ⟨entry, htail, hentry⟩ := ih
      obtain ⟨mode, hbody, hrev, hbof, _⟩ :=
        gnLocateRead_recordBody entry hentry field
      have hmarker : GNLocateReadTo mode [.bof] .moreRecord := by
        simp [GNLocateReadTo, GNLocateRevPathFrom, hrev, hbof,
          GNLocateMode.Stop]
      refine ⟨.moreRecord, ?_, Or.inr rfl⟩
      have hrecord := hbody.append hmarker
      have hall := htail.append hrecord
      simpa [gnFieldRecordsFrames, g1RecordFrames, List.reverse_append,
        List.append_assoc] using hall

/-- Exact canonical nonempty reverse path: scan everything strictly after the
first cursor without stopping, then the cursor produces `firstRecord`. -/
theorem gnLocate_firstRecord_path {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    GNLocateRevValidPath .tailFinish (gnFirstRecordMiddle r) ∧
      (gnLocateAdvanceList .tailFinish (gnFirstRecordMiddle r)).Reverse ∧
      gnLocateAdvance
        (gnLocateAdvanceList .tailFinish (gnFirstRecordMiddle r)) .cursor =
          .firstRecord := by
  rcases r with ⟨inputs, ⟨gates⟩⟩
  cases gates with
  | nil => simp at hg
  | cons first rest =>
      simp at hg
      subst g
      obtain ⟨entry, htail, hentry⟩ :=
        gnLocateRead_laterTail (rest.map gnGateFields)
      obtain ⟨mode, hbody, hrev, _, hcursor⟩ :=
        gnLocateRead_recordBody entry hentry (gnGateFields first)
      have hall := htail.append hbody
      have hrecord_ne :
          g1RecordFrames .cursor (gnGateFields first) ≠ [] := by
        simp [g1RecordFrames]
      have hshape : (gnFirstRecordMiddle
          { inputs := inputs, program := { gates := first :: rest } }).reverse =
          (gnFieldRecordsFrames .bof (rest.map gnGateFields) ++
              [G1Frame.separator, G1Frame.output false,
                G1Frame.finish]).reverse ++
            ((g1RecordFrames .cursor (gnGateFields first)).drop 1).reverse := by
        simp [gnFirstRecordMiddle, gnFirstRecordInner, gnRecordsFrames,
          gnFieldRecordsFrames, List.reverse_append,
          List.tail_append_of_ne_nil hrecord_ne]
      rw [GNLocateRevValidPath, gnLocateAdvanceList, hshape]
      rw [List.foldl_append]
      exact ⟨by
        rw [gnLocateRevPathFrom_append, htail.1]
        exact ⟨htail.2, hbody.2⟩,
        by rw [htail.1, hbody.1]; exact hrev,
        by rw [htail.1, hbody.1]; exact hcursor⟩

/-- Exact canonical empty reverse path and adjacent-separator stop. -/
theorem gnLocate_noGate_path {r : GNProgram} (_hg : r.program.gates = []) :
    GNLocateRevValidPath .tailFinish
        [.separator, .output false, .finish] ∧
      gnLocateAdvanceList .tailFinish
        [.separator, .output false, .finish] = .recordEdge ∧
      gnLocateAdvance .recordEdge .separator = .noGate := by
  simp [GNLocateRevValidPath, GNLocateRevPathFrom, gnLocateAdvanceList,
    GNLocateMode.Reverse, GNLocateMode.Stop, gnLocateAdvance]

/-! ## Exact configurations and read-only local runs -/

/-- Complete fixed GNM state at the nonempty locator handoff. -/
def gnFirstRecordQ : GNM.state := ⟨(0 : Fin 1), .firstRecord⟩

/-- Complete fixed GNM state at the empty locator handoff. -/
def gnNoGateQ : GNM.state := ⟨(0 : Fin 1), .noGate⟩

/-- Exact nonempty endpoint.  The proof arguments select the first typed gate
but are not stored in finite control. -/
def gnFirstRecordConfig (r : GNProgram) (g : SLGate r.inputs.length)
    (hg : r.program.gates[0]? = some g) :
    Configuration (M := GNM) (encodeGN r).length where
  state := gnFirstRecordQ
  head := ⟨4 * gnRecordsStart r, by
    have hs := encodeGNFrames_firstRecord_split hg
    have hlt : 4 * gnRecordsStart r < (encodeGN r).length := by
      rw [encodeGN_length, hs.1]
      simp only [List.length_append, List.length_cons, List.length_nil]
      rw [hs.2.1]
      omega
    change 4 * gnRecordsStart r <
      (encodeGN r).length + gnClock (encodeGN r).length + 1
    omega⟩
  tape := (GNM.initialConfig (gnPoint (encodeGN r))).tape

/-- Exact empty endpoint. -/
def gnNoGateConfig (r : GNProgram) :
    Configuration (M := GNM) (encodeGN r).length where
  state := gnNoGateQ
  head := ⟨4 * (r.inputs.length + 1), by
    simp [TM.tapeLength, gnCS, gnClock, g1Clock]
    omega⟩
  tape := (GNM.initialConfig (gnPoint (encodeGN r))).tape

/-- Locator-only schedule after `scratchEntry` for a nonempty program. -/
def gnFirstRecordLocateSteps (r : GNProgram) : Nat :=
  1 + 4 * (gnFirstRecordMiddle r).length + 4

/-- Full validation-plus-locator schedule for a nonempty program. -/
def gnFirstRecordSteps (r : GNProgram) : Nat :=
  gnValidateSteps r + gnFirstRecordLocateSteps r

/-- Locator-only schedule for an empty record region: entry plus the terminal
three frames and the adjacent stopping separator. -/
def gnNoGateLocateSteps : Nat := 1 + 4 * 3 + 4

/-- Full validation-plus-locator schedule for an empty program. -/
def gnNoGateSteps (r : GNProgram) : Nat :=
  gnValidateSteps r + gnNoGateLocateSteps

/-- Nonempty schedule provenance: one entry-left row, four rows per frame
strictly after the first cursor, and four stationary anchor-completion rows. -/
theorem gnFirstRecordSteps_provenance (r : GNProgram) :
    gnFirstRecordSteps r =
      ((encodeGN r).length + 9) +
        (1 + 4 * (gnFirstRecordMiddle r).length + 4) := rfl

/-- Empty schedule provenance: validation, one entry-left row, three reverse
tail frames, and the four-row adjacent-separator completion. -/
theorem gnNoGateSteps_provenance (r : GNProgram) :
    gnNoGateSteps r = ((encodeGN r).length + 9) + 17 := by
  rfl

/-- Both exact endpoints retain the real initial tape, hence every physical
scratch cell at or after the logical word end is still blank. -/
theorem gnFirstRecordConfig_scratch_blank (r : GNProgram)
    (g : SLGate r.inputs.length) (hg : r.program.gates[0]? = some g)
    (j : Fin (GNM.tapeLength (encodeGN r).length))
    (hj : (encodeGN r).length ≤ (j : Nat)) :
    (gnFirstRecordConfig r g hg).tape j = false :=
  GNM.initial_tape_blank (gnPoint (encodeGN r)) hj

theorem gnNoGateConfig_scratch_blank (r : GNProgram)
    (j : Fin (GNM.tapeLength (encodeGN r).length))
    (hj : (encodeGN r).length ≤ (j : Nat)) :
    (gnNoGateConfig r).tape j = false :=
  GNM.initial_tape_blank (gnPoint (encodeGN r)) hj

/-- Exact nonempty endpoint projections: fixed state, first cursor p0, and the
unchanged real initial tape. -/
theorem gnFirstRecordConfig_structure (r : GNProgram)
    (g : SLGate r.inputs.length) (hg : r.program.gates[0]? = some g) :
    (gnFirstRecordConfig r g hg).state = gnFirstRecordQ ∧
      ((gnFirstRecordConfig r g hg).head : Nat) = 4 * gnRecordsStart r ∧
      (gnFirstRecordConfig r g hg).tape =
        (GNM.initialConfig (gnPoint (encodeGN r))).tape := by
  exact ⟨rfl, rfl, rfl⟩

/-- Exact empty endpoint projections: fixed state, adjacent separator p0, and
the unchanged real initial tape. -/
theorem gnNoGateConfig_structure (r : GNProgram) :
    (gnNoGateConfig r).state = gnNoGateQ ∧
      ((gnNoGateConfig r).head : Nat) = 4 * (r.inputs.length + 1) ∧
      (gnNoGateConfig r).tape =
        (GNM.initialConfig (gnPoint (encodeGN r))).tape := by
  exact ⟨rfl, rfl, rfl⟩

/-- Exact E2-2 premise package at the nonempty endpoint.  The cursor source
and every frame up to the first implicit blank meet `gnCopyShuttle`'s explicit
blank/marker exclusions, the physical shuttle span fits, and making that first
blank explicit leaves the endpoint tape unchanged.  No shuttle row executes. -/
theorem gnFirstRecord_copyShuttle_handoff {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    GNInstallAdmissible G1Frame.cursor ∧
      (∀ frame ∈ gnFirstRecordMiddle r, GNInstallAdmissible frame) ∧
      4 * ((gnLocatePrefix r).length +
        (gnFirstRecordMiddle r).length + 2) <
          GNM.tapeLength (encodeGN r).length ∧
      frameListTape
          (((gnLocatePrefix r ++ .cursor :: gnFirstRecordMiddle r) ++
            [G1Frame.blank]).flatMap G1Frame.bits) =
        (gnFirstRecordConfig r g hg).tape := by
  have hs := encodeGNFrames_firstRecord_split hg
  have hshape : encodeGNFrames r =
      gnLocatePrefix r ++ .cursor :: gnFirstRecordMiddle r := by
    simpa [gnFirstRecordMiddle, List.append_assoc] using hs.1
  have hmiddle : ∀ frame ∈ gnFirstRecordMiddle r,
      GNInstallAdmissible frame := by
    intro frame hframe
    exact encodeGNFrames_no_blank_no_outputTrue r frame (by
      rw [hshape]
      simp [hframe])
  have hn : (encodeGN r).length =
      4 * ((gnLocatePrefix r).length +
        (gnFirstRecordMiddle r).length + 1) := by
    rw [encodeGN_length, hshape]
    simp [Nat.add_assoc]
  have hroom : 4 * ((gnLocatePrefix r).length +
      (gnFirstRecordMiddle r).length + 2) <
      GNM.tapeLength (encodeGN r).length := by
    change 4 * ((gnLocatePrefix r).length +
        (gnFirstRecordMiddle r).length + 2) <
      (encodeGN r).length + gnClock (encodeGN r).length + 1
    have hclock : 4 < gnClock (encodeGN r).length := by
      simp [gnClock, g1Clock]
    omega
  refine ⟨by simp [GNInstallAdmissible], hmiddle, hroom, ?_⟩
  change frameListTape
      (((gnLocatePrefix r ++ G1Frame.cursor :: gnFirstRecordMiddle r) ++
        [G1Frame.blank]).flatMap G1Frame.bits) =
    (GNM.initialConfig (gnPoint (encodeGN r))).tape
  have hblankTape : frameListTape
      (L := GNM.tapeLength (encodeGN r).length)
      ((gnLocatePrefix r ++ G1Frame.cursor ::
        gnFirstRecordMiddle r).flatMap G1Frame.bits) =
      frameListTape
        (L := GNM.tapeLength (encodeGN r).length)
        (((gnLocatePrefix r ++ G1Frame.cursor :: gnFirstRecordMiddle r) ++
          [G1Frame.blank]).flatMap G1Frame.bits) := by
    simpa only [g1FrameCodec_bits] using
      (frameListTape_append_blank (L := GNM.tapeLength (encodeGN r).length)
        g1FrameCodec
        (gnLocatePrefix r ++ G1Frame.cursor :: gnFirstRecordMiddle r)
        G1Frame.blank rfl)
  rw [← hblankTape]
  rw [← hshape]
  change frameListTape (encodeGN r) = _
  exact (gnInitialTape_eq_frameListTape _).symm

/-- Generic physical row accounting for the one unaligned entry step, a
right-to-left list scan, and its stationary anchor completion. -/
private theorem gnCS_scratchEntry_locateOnList (n : Nat)
    (pre : List G1Frame) (anchor : G1Frame) (scanned : List G1Frame)
    (final : GNLocateMode) (target : GNState)
    (hn : n = 4 * (pre.length + scanned.length + 1))
    (hpath : GNLocateRevValidPath .tailFinish scanned)
    (hrev : final.Reverse)
    (hfinal : gnLocateAdvanceList .tailFinish scanned = final)
    (hstop : (gnLocateAdvance final anchor).Stop)
    (htarget : gnLocateStopState (gnLocateAdvance final anchor) = target) :
    let tape : Fin (GNM.tapeLength n) → Bool :=
      frameListTape ((pre ++ anchor :: scanned).flatMap G1Frame.bits)
    TM.runConfig (M := GNM)
        (Phased.alignedAt gnCS gnCS.startPhase n n (by
          change n < n + gnClock n + 1
          omega) tape .scratchEntry)
        (1 + 4 * scanned.length + 4) =
      Phased.alignedAt gnCS gnCS.startPhase n (4 * pre.length) (by
        change 4 * pre.length < n + gnClock n + 1
        omega) tape target := by
  dsimp only
  let tape : Fin (GNM.tapeLength n) → Bool :=
    frameListTape ((pre ++ anchor :: scanned).flatMap G1Frame.bits)
  have hnpos : 0 < n := by omega
  have hnroom : n < GNM.tapeLength n := by
    change n < n + gnClock n + 1
    omega
  have hentry := Phased.holdLeft gnCS gnCS.startPhase n n hnroom hnpos tape
    GNState.scratchEntry (.locating ⟨.tailFinish, .r3⟩) (fun _ => rfl)
  have hrevroom : 4 * (pre.length + scanned.length) + 3 <
      gnLocateScanner.machine.tapeLength n := by
    rw [gnLocateScanner_machine]
    change 4 * (pre.length + scanned.length) + 3 < n + gnClock n + 1
    omega
  have hentry' : TM.runConfig (M := GNM)
      (Phased.alignedAt gnCS gnCS.startPhase n n hnroom tape .scratchEntry) 1 =
      Phased.alignedAt gnCS gnCS.startPhase n
        (4 * (pre.length + scanned.length) + 3) (by
          change 4 * (pre.length + scanned.length) + 3 < n + gnClock n + 1
          omega) tape (.locating ⟨.tailFinish, .r3⟩) := by
    rw [runConfig_one]
    have hhead : n - 1 = 4 * (pre.length + scanned.length) + 3 := by omega
    simpa only [hhead] using hentry
  have hsafe : 4 * (pre.length + scanned.length) + 4 <
      gnLocateScanner.machine.tapeLength n := by
    rw [gnLocateScanner_machine]
    change 4 * (pre.length + scanned.length) + 4 < n + gnClock n + 1
    omega
  have hscan := gnLocateScanner.revScanFrames n pre anchor scanned []
    .tailFinish () ((gnLocateScanner_validPath _ _).2 hpath) hsafe
  rw [gnLocateScanner_advanceList, hfinal] at hscan
  have hscan' : TM.runConfig (M := GNM)
      (Phased.alignedAt gnCS gnCS.startPhase n
        (4 * (pre.length + scanned.length) + 3) (by
          change 4 * (pre.length + scanned.length) + 3 < n + gnClock n + 1
          omega) tape (.locating ⟨.tailFinish, .r3⟩))
        (4 * scanned.length) =
      Phased.alignedAt gnCS gnCS.startPhase n (4 * pre.length + 3) (by
        change 4 * pre.length + 3 < n + gnClock n + 1
        omega) tape (.locating ⟨final, .r3⟩) := by
    simpa [gnLocateScanner, tape, List.append_assoc] using hscan
  have hanchorSafe : 4 * pre.length + 4 < GNM.tapeLength n := by
    change 4 * pre.length + 4 < n + gnClock n + 1
    omega
  have hbits : physicalBitsAt (h := 4 * pre.length) hanchorSafe tape =
      g1FrameCodec.bits anchor := by
    simpa [tape, List.append_assoc] using
      physicalBitsAt_flatMap (L := GNM.tapeLength n) g1FrameCodec pre scanned anchor
        hanchorSafe
  have hanchor := gnLocateScanner.revAnchorStep n (4 * pre.length) (by
      rw [gnLocateScanner_machine]
      exact hanchorSafe)
    tape final anchor () hrev hstop hbits
  have hanchor' : TM.runConfig (M := GNM)
      (Phased.alignedAt gnCS gnCS.startPhase n (4 * pre.length + 3) (by
        change 4 * pre.length + 3 < n + gnClock n + 1
        omega) tape (.locating ⟨final, .r3⟩)) 4 =
      Phased.alignedAt gnCS gnCS.startPhase n (4 * pre.length) (by
        change 4 * pre.length < n + gnClock n + 1
        omega)
        tape target := by
    simpa [gnLocateScanner, htarget] using hanchor
  rw [show 1 + 4 * scanned.length + 4 =
      1 + (4 * scanned.length + 4) by omega, runConfig_add, hentry']
  rw [runConfig_add, hscan', hanchor']

set_option maxHeartbeats 800000 in
/-- Exact local nonempty run from E1b's public scratch entry. -/
theorem gnCS_scratchEntry_to_firstRecord (r : GNProgram)
    (g : SLGate r.inputs.length) (hg : r.program.gates[0]? = some g) :
    TM.runConfig (M := GNM) (gnScratchEntryConfig r)
        (gnFirstRecordLocateSteps r) =
      gnFirstRecordConfig r g hg := by
  have hs := encodeGNFrames_firstRecord_split hg
  have hp := gnLocate_firstRecord_path hg
  let pre := gnLocatePrefix r
  let scanned := gnFirstRecordMiddle r
  let n := (encodeGN r).length
  have hn : n = 4 * (pre.length + scanned.length + 1) := by
    rw [show n = (encodeGN r).length from rfl, encodeGN_length, hs.1]
    simp [pre, scanned, gnFirstRecordMiddle]
    omega
  have hlocal := gnCS_scratchEntry_locateOnList n pre .cursor scanned
    (gnLocateAdvanceList .tailFinish scanned) .firstRecord hn hp.1 hp.2.1 rfl
    (by rw [hp.2.2]; simp [GNLocateMode.Stop])
    (by rw [hp.2.2]; rfl)
  have htape : frameListTape
      ((pre ++ .cursor :: scanned).flatMap G1Frame.bits) =
      (GNM.initialConfig (gnPoint (encodeGN r))).tape := by
    rw [show pre ++ .cursor :: scanned = encodeGNFrames r by
      simpa [pre, scanned, gnFirstRecordMiddle, List.append_assoc] using hs.1.symm]
    change frameListTape (encodeGN r) = _
    exact (gnInitialTape_eq_frameListTape _).symm
  have hstart : gnScratchEntryConfig r =
      Phased.alignedAt gnCS gnCS.startPhase n n (by
        change n < n + gnClock n + 1
        omega)
        (frameListTape ((pre ++ .cursor :: scanned).flatMap G1Frame.bits))
        .scratchEntry := by
    apply Configuration.ext_of_components
    · rfl
    · apply Fin.ext
      rfl
    · exact htape.symm
  have hend : Phased.alignedAt gnCS gnCS.startPhase n
        (4 * pre.length) (by
          change 4 * pre.length < n + gnClock n + 1
          omega)
        (frameListTape ((pre ++ .cursor :: scanned).flatMap G1Frame.bits))
        .firstRecord = gnFirstRecordConfig r g hg := by
    apply Configuration.ext_of_components
    · rfl
    · apply Fin.ext
      change 4 * (gnLocatePrefix r).length = 4 * gnRecordsStart r
      rw [hs.2.1]
    · exact htape
  have hsched : gnFirstRecordLocateSteps r =
      1 + 4 * scanned.length + 4 := rfl
  rw [hsched, hstart]
  exact hlocal.trans hend

set_option maxHeartbeats 800000 in
/-- Exact local empty-program run from E1b's public scratch entry. -/
theorem gnCS_scratchEntry_to_noGate (r : GNProgram)
    (hg : r.program.gates = []) :
    TM.runConfig (M := GNM) (gnScratchEntryConfig r) gnNoGateLocateSteps =
      gnNoGateConfig r := by
  let pre : List G1Frame := [.bof] ++ gnAssignFrames r.inputs
  let scanned : List G1Frame :=
    [.separator, .output false, .finish]
  let n := (encodeGN r).length
  have hs := encodeGNFrames_noGate_split hg
  have hp := gnLocate_noGate_path hg
  have hn : n = 4 * (pre.length + scanned.length + 1) := by
    rw [show n = (encodeGN r).length from rfl, encodeGN_length, hs]
    simp [pre, scanned]
  have hlocal := gnCS_scratchEntry_locateOnList n pre .separator scanned
    .recordEdge .noGate hn hp.1 (by simp [GNLocateMode.Reverse]) hp.2.1
    (by simp [gnLocateAdvance, GNLocateMode.Stop]) (by rfl)
  have htape : frameListTape
      ((pre ++ .separator :: scanned).flatMap G1Frame.bits) =
      (GNM.initialConfig (gnPoint (encodeGN r))).tape := by
    rw [show pre ++ .separator :: scanned = encodeGNFrames r by
      simpa [pre, scanned, List.append_assoc] using hs.symm]
    change frameListTape (encodeGN r) = _
    exact (gnInitialTape_eq_frameListTape _).symm
  have hstart : gnScratchEntryConfig r =
      Phased.alignedAt gnCS gnCS.startPhase n n (by
        change n < n + gnClock n + 1
        omega)
        (frameListTape ((pre ++ .separator :: scanned).flatMap G1Frame.bits))
        .scratchEntry := by
    apply Configuration.ext_of_components
    · rfl
    · apply Fin.ext
      rfl
    · exact htape.symm
  have hend : Phased.alignedAt gnCS gnCS.startPhase n
        (4 * pre.length) (by
          change 4 * pre.length < n + gnClock n + 1
          omega)
        (frameListTape ((pre ++ .separator :: scanned).flatMap G1Frame.bits))
        .noGate = gnNoGateConfig r := by
    apply Configuration.ext_of_components
    · rfl
    · apply Fin.ext
      change 4 * pre.length = 4 * (r.inputs.length + 1)
      simp [pre, gnAssignFrames_length]
    · exact htape
  have hsched : gnNoGateLocateSteps = 1 + 4 * scanned.length + 4 := by
    simp [gnNoGateLocateSteps, scanned]
  rw [hsched, hstart]
  exact hlocal.trans hend

/-- Full real-input nonempty capstone: E1b followed by the live locator. -/
theorem gnCS_encodeGN_firstRecord (r : GNProgram)
    (g : SLGate r.inputs.length) (hg : r.program.gates[0]? = some g) :
    TM.runConfig (M := GNM)
        (GNM.initialConfig (gnPoint (encodeGN r))) (gnFirstRecordSteps r) =
      gnFirstRecordConfig r g hg := by
  rw [gnFirstRecordSteps, runConfig_add, gnCS_encodeGN_scratchEntry,
    gnCS_scratchEntry_to_firstRecord r g hg]

/-- Full real-input empty-program capstone: E1b followed by the live locator. -/
theorem gnCS_encodeGN_noGate (r : GNProgram) (hg : r.program.gates = []) :
    TM.runConfig (M := GNM)
        (GNM.initialConfig (gnPoint (encodeGN r))) (gnNoGateSteps r) =
      gnNoGateConfig r := by
  rw [gnNoGateSteps, runConfig_add, gnCS_encodeGN_scratchEntry,
    gnCS_scratchEntry_to_noGate r hg]

/-! ## Scoped clock facts and kernel-reduced literal probes -/

/-- Validation plus the nonempty locator fits the existing public clock.  This
is deliberately not an installer, shuttle, loop, or total-runtime bound. -/
theorem gnFirstRecordSteps_le_gnClock {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    gnFirstRecordSteps r ≤ gnClock (encodeGN r).length := by
  let N := (encodeGN r).length
  have hs := encodeGNFrames_firstRecord_split hg
  have hshape : encodeGNFrames r =
      gnLocatePrefix r ++ .cursor :: gnFirstRecordMiddle r := by
    simpa [gnFirstRecordMiddle, List.append_assoc] using hs.1
  have hn : N = 4 * ((gnLocatePrefix r).length +
      (gnFirstRecordMiddle r).length + 1) := by
    rw [show N = (encodeGN r).length from rfl, encodeGN_length, hshape]
    simp [Nat.add_assoc]
  have hsquare : N + 1 ≤ (N + 1) ^ 2 := by
    rw [pow_two]
    exact Nat.le_mul_of_pos_left _ (by omega)
  change (N + 9) +
      (1 + 4 * (gnFirstRecordMiddle r).length + 4) ≤
    512 * (N + 1) ^ 2 + 512
  omega

/-- Validation plus the empty-program locator fits the existing public clock;
no later terminal routing is included. -/
theorem gnNoGateSteps_le_gnClock (r : GNProgram) :
    gnNoGateSteps r ≤ gnClock (encodeGN r).length := by
  let N := (encodeGN r).length
  have hsquare : N + 1 ≤ (N + 1) ^ 2 := by
    rw [pow_two]
    exact Nat.le_mul_of_pos_left _ (by omega)
  change (N + 9) + 17 ≤ 512 * (N + 1) ^ 2 + 512
  omega

namespace GNScratchBootstrapProbes

open GNFixedDelegateProbes

/-- Kernel-reduced real-initial nonempty capstone: total 94 rows and cursor p0
at physical head 12. -/
theorem literal_oneConstFalse_firstRecord :
    TM.runConfig (M := GNM)
        (GNM.initialConfig (gnPoint (encodeGN oneConstFalseProgram))) 94 =
      gnFirstRecordConfig oneConstFalseProgram
        (SLGate.const false : SLGate 0) (by rfl) ∧
    ((gnFirstRecordConfig oneConstFalseProgram
      (SLGate.const false : SLGate 0) (by rfl)).head : Nat) = 12 := by
  have hg : oneConstFalseProgram.program.gates[0]? =
      some (SLGate.const false : SLGate 0) := by rfl
  have hrun := gnCS_encodeGN_firstRecord oneConstFalseProgram
    (SLGate.const false : SLGate 0) hg
  have hsched : gnFirstRecordSteps oneConstFalseProgram = 94 := by decide
  rw [hsched] at hrun
  exact ⟨by simpa only using hrun, by decide⟩

/-- Kernel-reduced real-initial empty capstone: total 46 rows and adjacent
separator p0 at physical head 4. -/
theorem literal_empty_noGate :
    TM.runConfig (M := GNM)
        (GNM.initialConfig (gnPoint (encodeGN emptyProgram))) 46 =
      gnNoGateConfig emptyProgram ∧
    ((gnNoGateConfig emptyProgram).head : Nat) = 4 := by
  have hg : emptyProgram.program.gates = [] := by rfl
  have hrun := gnCS_encodeGN_noGate emptyProgram hg
  have hsched : gnNoGateSteps emptyProgram = 46 := by decide
  rw [hsched] at hrun
  exact ⟨hrun, by decide⟩

end GNScratchBootstrapProbes

end Pnp3.Internal.PsubsetPpoly.TM
