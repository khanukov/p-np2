import Complexity.TMVerifier.TuringToolkit.GateNBodyDriver

/-!
# GN-E2-4a read-only rewind from `recordDone` to the values boundary (2026-09-27)

**Progress classification: infrastructure, not P-vs-NP mainline progress.**

GN-E2-3b stopped at the literal `recordDone` state, where the scratch region
holds exactly `bof :: gnGateBodyFrames g ++ [separator]` — that is,
`g1PrefixFrames (gnFirstRequest r g)` with its current-value `data` suffix still
missing — and the head stands on p0 of the source frame just past the consumed
record.  The values the machine must still copy live at the *left* end of the
word, in the maximal `data` run after the leading `bof`.  This slice activates
`recordDone` and carries the head there, and does nothing else.

**What it adds to the fixed control.**  Two `GNState` constructors,
`rewind (buffer : GNInstallBuffer)` and `valuesEntry`; one changed row
(`recordDone` was a stationary self-loop and now steps left into the pass); and
the finite `gnRewindControl` row set.  No mode, buffer or payload of the new
rows contains a natural number, index, width, base, request, list, or any other
runtime geometry, and nothing is request-dependent: the pass is the same eight
rows for every program.  `valuesEntry` is a dormant absorbing arrival, exactly
as `recordDone` was before this slice.

**What the pass does.**  Three leftward buffering rows and a frame-position-0
decision read the word right to left, four rows per frame, writing back every
cell they scan; the decision anchors on the leading `bof`, rejects every
undecodable window, and otherwise steps left again.  Four rightward rows then
stand on p0 of the frame immediately after the anchor.  The whole pass is
read-only: the endpoint tape is *literally* the `recordDone` endpoint tape.

**Explicitly not here, and claimed nowhere.**  No value is copied and no frame
is written: this slice moves the head and nothing else.  There is no values
writer, no `[output false, finish]` tail writer, no completed request word, no
launch, delegation, commit, next-gate loop, total installer clock, verdict, or
acceptance.  In particular the pure evaluator `evalGNProgram` is **not**
executed by this machine, and no statement here says it is.  The one-frame exit
dispatcher `gnInstallExitDispatch` is deliberately left byte-identical, so the
installer shuttle still rejects a carried `data` frame; extending it is the next
slice's obligation, not this one's.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan
open Encoding

/-! ## Exact finite rewind rows -/

/-- Every fixed row of the pass, in execution order: the activated `recordDone`
entry, the three leftward buffering rows, the four rightward standing rows, and
the dormant `valuesEntry` arrival.  The frame-position-0 decision is separate
because it reads the tape. -/
theorem gnTransition_rewind_rows (phase : Fin 1) (b0 b1 b2 b3 scan : Bool) :
    gnTransition phase .recordDone scan = (0, .rewind .r3, scan, .left) ∧
      gnTransition phase (.rewind .r3) scan =
        (0, .rewind (.r2 scan), scan, .left) ∧
      gnTransition phase (.rewind (.r2 b3)) scan =
        (0, .rewind (.r1 scan b3), scan, .left) ∧
      gnTransition phase (.rewind (.r1 b2 b3)) scan =
        (0, .rewind (.r0 scan b2 b3), scan, .left) ∧
      gnTransition phase (.rewind .p0) scan =
        (0, .rewind (.p1 false), scan, .right) ∧
      gnTransition phase (.rewind (.p1 b0)) scan =
        (0, .rewind (.p2 false false), scan, .right) ∧
      gnTransition phase (.rewind (.p2 b0 b1)) scan =
        (0, .rewind (.p3 false false false), scan, .right) ∧
      gnTransition phase (.rewind (.p3 b0 b1 b2)) scan =
        (0, .valuesEntry, scan, .right) ∧
      gnTransition phase .valuesEntry scan = (0, .valuesEntry, scan, .stay) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The complete frame-position-0 decision: the leading `bof` anchors the pass
and turns the head around, every other decodable frame steps left again, and
every undecodable window enters the existing stationary reject sink.  All three
rows write the scanned bit back. -/
theorem gnTransition_rewind_decision (phase : Fin 1) :
    (∀ b1 b2 b3 scan : Bool,
        decodeG1Frame? [scan, b1, b2, b3] = some G1Frame.bof →
        gnTransition phase (.rewind (.r0 b1 b2 b3)) scan =
          (0, .rewind .p0, scan, .stay)) ∧
      (∀ (frame : G1Frame) (b1 b2 b3 scan : Bool),
        decodeG1Frame? [scan, b1, b2, b3] = some frame →
        frame ≠ G1Frame.bof →
        gnTransition phase (.rewind (.r0 b1 b2 b3)) scan =
          (0, .rewind .r3, scan, .left)) ∧
      (∀ b1 b2 b3 scan : Bool,
        decodeG1Frame? [scan, b1, b2, b3] = none →
        gnTransition phase (.rewind (.r0 b1 b2 b3)) scan =
          (0, .reject, scan, .stay)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b1 b2 b3 scan hbof
    simp [gnTransition, gnRewindControl, gnRewindComplete, hbof, gnRewindAdvance]
  · intro frame b1 b2 b3 scan hdecode hne
    have hnext : gnRewindComplete .scan scan b1 b2 b3 = .scan := by
      rw [gnRewindComplete, hdecode]
      cases frame with
      | bof => exact absurd rfl hne
      | data b | output b => cases b <;> rfl
      | blank | tag | index | separator | cursor | finish | argSep | spent => rfl
    simp [gnTransition, gnRewindControl, hnext]
  · intro b1 b2 b3 scan hbad
    simp [gnTransition, gnRewindControl, gnRewindComplete, hbad]

/-- The three reserved public codes are rewind rejection rows: this pass opens
one new place where tape data enters the finite control, and every window it
cannot decode fails closed into the existing sink. -/
theorem gnTransition_rewind_reserved (phase : Fin 1) :
    gnTransition phase (.rewind (.r0 true false true)) true =
        (0, .reject, true, .stay) ∧
      gnTransition phase (.rewind (.r0 true true false)) true =
        (0, .reject, true, .stay) ∧
      gnTransition phase (.rewind (.r0 true true true)) true =
        (0, .reject, true, .stay) :=
  ⟨gnTransition_rewind_decision phase |>.2.2 true false true true rfl,
    gnTransition_rewind_decision phase |>.2.2 true true false true rfl,
    gnTransition_rewind_decision phase |>.2.2 true true true true rfl⟩

/-- Exact frame-level rewind table: `bof` anchors, and every representative
frame a stage-zero GN word can carry to the left of a finished record
continues the pass. -/
theorem gnRewindAdvance_laws (mode : GNRewindMode) (b : Bool) :
    gnRewindAdvance mode .bof = .anchor ∧
      gnRewindAdvance mode (.data b) = .scan ∧
      gnRewindAdvance mode (.output false) = .scan ∧
      gnRewindAdvance mode .separator = .scan ∧
      gnRewindAdvance mode .cursor = .scan ∧
      gnRewindAdvance mode .tag = .scan ∧
      gnRewindAdvance mode .index = .scan ∧
      gnRewindAdvance mode .argSep = .scan ∧
      gnRewindAdvance mode .finish = .scan := by
  cases b <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The pass as an instance of the shared reverse kernel -/

/-- The pass ends exactly at the anchor and at rejection. -/
def GNRewindMode.Stop : GNRewindMode → Prop
  | .scan => False
  | _ => True

/-- Exactly the one mode that reads frames right to left. -/
def GNRewindMode.Reverse : GNRewindMode → Prop
  | .scan => True
  | _ => False

theorem GNRewindMode.Reverse.eq {mode : GNRewindMode} (h : mode.Reverse) :
    mode = .scan := by
  cases mode <;> simp_all [GNRewindMode.Reverse]

/-- Collapse the two terminal rewind modes to their fixed outer states: the
anchor turns the head around, everything else is the existing reject sink. -/
def gnRewindStopState : GNRewindMode → GNState
  | .anchor => .rewind .p0
  | _ => .reject

/-- The rewind as an instance of the shared reverse frame-scanner kernel.  All
six obligations are discharged from the fixed table above; no control row is
modified here. -/
def gnRewindScanner : ReverseFrameScanner GNState G1Frame GNRewindMode Unit where
  program := gnCS
  phase := gnCS.startPhase
  codec := g1FrameCodec
  Stop := GNRewindMode.Stop
  revAdvance := gnRewindAdvance
  revComplete := gnRewindComplete
  Reverse := GNRewindMode.Reverse
  rst3 := fun _ _ => .rewind .r3
  rst2 := fun _ _ b3 => .rewind (.r2 b3)
  rst1 := fun _ _ b2 b3 => .rewind (.r1 b2 b3)
  rst0 := fun _ _ b1 b2 b3 => .rewind (.r0 b1 b2 b3)
  stopState := fun mode _ => gnRewindStopState mode
  revComplete_decode := by
    intro mode frame b0 b1 b2 b3 h
    simp only [gnRewindComplete]
    rw [show decodeG1Frame? [b0, b1, b2, b3] = some frame by simpa using h]
  rstep_p3 := by
    intro mode hm _ scan
    obtain rfl := hm.eq
    rfl
  rstep_p2 := by
    intro mode hm _ b3 scan
    obtain rfl := hm.eq
    rfl
  rstep_p1 := by
    intro mode hm _ b2 b3 scan
    obtain rfl := hm.eq
    rfl
  rstep_p0 := by
    intro mode hm _ b1 b2 b3 scan hnext
    obtain rfl := hm.eq
    cases scan <;> cases b1 <;> cases b2 <;> cases b3 <;>
      simp_all [gnCS, gnTransition, gnRewindControl, gnRewindComplete,
        gnRewindAdvance, GNRewindMode.Stop, decodeG1Frame?]
  rstep_p0_stop := by
    intro mode hm _ b1 b2 b3 scan hstop
    obtain rfl := hm.eq
    cases scan <;> cases b1 <;> cases b2 <;> cases b3 <;>
      simp_all [gnCS, gnTransition, gnRewindControl, gnRewindComplete,
        gnRewindAdvance, GNRewindMode.Stop, gnRewindStopState, decodeG1Frame?]

private theorem gnRewindScanner_machine : gnRewindScanner.machine = GNM := rfl

/-- The shared phase layer's compiled machine is literally `GNM`.  This is the
only place the two spellings of the tape length are reconciled, so that head
safety can be discharged against `GNM.tapeLength` throughout. -/
private theorem gnPhased_lt {n h : Nat} (hh : h < GNM.tapeLength n) :
    h < (Phased.machine gnCS).tapeLength n := hh

/-- A block with no `bof` is a valid reverse path that leaves the mode at
`scan`: this is the only fact about the scanned frames the pass needs. -/
theorem gnRewind_validPath {frames : List G1Frame}
    (h : ∀ f ∈ frames, f ≠ G1Frame.bof) :
    gnRewindScanner.RevValidPath .scan frames ∧
      gnRewindScanner.revAdvanceList .scan frames = .scan := by
  refine gnRewindScanner.revValidPath_const (m := GNRewindMode.scan) ?_ ?_
    frames ?_
  · exact trivial
  · exact fun hc => hc
  · intro f hf
    cases f with
    | bof => exact absurd rfl (h _ hf)
    | data b | output b => cases b <;> rfl
    | blank | tag | index | separator | cursor | finish | argSep | spent => rfl

/-! ## Executable rejection at the one new ingress -/

/-- **Exact four-row rejection at the new boundary.**  The reserved code `1101`,
supplied at an arbitrary aligned rewind window, reaches the existing stationary
reject sink in exactly four rows of genuine `TM.runConfig (M := GNM)` execution,
with the head left on p0 of that window and the caller's tape untouched.  This
is the run-level companion of `gnTransition_rewind_reserved`: the one new place
where tape data enters the finite control fails closed in execution, not only in
the table. -/
theorem gnCS_rewind_reserved1101_reject_four (n base : Nat)
    (hsafe : base + 4 < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool)
    (hbits : physicalBitsAt hsafe tape = [true, true, false, true]) :
    TM.runConfig (M := GNM)
        (Phased.alignedAt gnCS gnCS.startPhase n (base + 3) (by
          change base + 3 < GNM.tapeLength n
          omega) tape (.rewind .r3)) 4 =
      Phased.alignedAt gnCS gnCS.startPhase n base (by
        change base < GNM.tapeLength n
        omega) tape .reject := by
  have hcells :
      tape ⟨base, by omega⟩ = true ∧ tape ⟨base + 1, by omega⟩ = true ∧
        tape ⟨base + 2, by omega⟩ = false ∧ tape ⟨base + 3, by omega⟩ = true := by
    simpa only [physicalBitsAt, List.cons.injEq, and_true] using hbits
  obtain ⟨h0, h1, h2, h3⟩ := hcells
  have hcomplete : gnRewindComplete .scan (tape ⟨base, by omega⟩)
      (tape ⟨base + 1, by omega⟩) (tape ⟨base + 2, by omega⟩)
      (tape ⟨base + 3, by omega⟩) = .reject := by
    rw [h0, h1, h2, h3]
    rfl
  have hstop : gnRewindScanner.Stop
      (gnRewindScanner.revComplete .scan (tape ⟨base, by omega⟩)
        (tape ⟨base + 1, by omega⟩) (tape ⟨base + 2, by omega⟩)
        (tape ⟨base + 3, by omega⟩)) := by
    show GNRewindMode.Stop (gnRewindComplete .scan _ _ _ _)
    rw [hcomplete]
    trivial
  have hrun := gnRewindScanner.revWindowStop n base
    (by rw [gnRewindScanner_machine]; omega) tape .scan () trivial hstop
  simpa [gnRewindScanner, gnRewindStopState, hcomplete] using hrun

/-- Stable reject padding after that exact four-row rewind failure: the sink is
the existing absorbing one, so extra budget changes nothing. -/
theorem gnCS_rewind_reserved1101_reject_stable (n base : Nat)
    (hsafe : base + 4 < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool)
    (hbits : physicalBitsAt hsafe tape = [true, true, false, true]) (k : Nat) :
    TM.runConfig (M := GNM)
        (Phased.alignedAt gnCS gnCS.startPhase n (base + 3) (by
          change base + 3 < GNM.tapeLength n
          omega) tape (.rewind .r3)) (4 + k) =
      Phased.alignedAt gnCS gnCS.startPhase n base (by
        change base < GNM.tapeLength n
        omega) tape .reject := by
  rw [runConfig_add,
    gnCS_rewind_reserved1101_reject_four n base hsafe tape hbits]
  exact gnCS_reject_stable _ rfl k

/-! ## Exact schedule and boundary configurations -/

/-- Exact rewind schedule: one activated `recordDone` row, four rows per
scanned frame, four rows for the anchor frame, and four rows to stand on the
frame after it. -/
def gnValuesRewindSteps (scanned : Nat) : Nat := 4 * scanned + 9

/-- Exact arithmetic provenance of the schedule, split into the three phases
the proof composes. -/
theorem gnValuesRewindSteps_provenance (scanned : Nat) :
    gnValuesRewindSteps scanned = 1 + (4 * scanned + 4) + 4 ∧
      gnValuesRewindSteps 0 = 9 := by
  constructor
  · simp only [gnValuesRewindSteps]; omega
  · rfl

/-- The physical tape of a rewind: the leading `bof` anchor, the block the pass
scans, and everything to the right of it. -/
def gnRewindTape (n : Nat) (pre post : List G1Frame) :
    Fin (GNM.tapeLength n) → Bool :=
  frameListTape ((G1Frame.bof :: pre ++ post).flatMap G1Frame.bits)

/-- The exact `recordDone` boundary the pass starts from: head on p0 of the
frame immediately past the scanned block. -/
def gnValuesRewindConfig (n : Nat) (pre post : List G1Frame)
    (hroom : 4 * pre.length + 4 < GNM.tapeLength n) :
    Configuration (M := GNM) n :=
  Phased.alignedAt gnCS gnCS.startPhase n (4 * (pre.length + 1))
    (gnPhased_lt (by omega)) (gnRewindTape n pre post) .recordDone

/-- The values boundary: head on p0 of the frame immediately after the leading
`bof`, in the fixed `valuesEntry` state, with the tape untouched. -/
def gnValuesEntryConfigOf (n : Nat) (pre post : List G1Frame)
    (hroom : 4 * pre.length + 4 < GNM.tapeLength n) :
    Configuration (M := GNM) n :=
  Phased.alignedAt gnCS gnCS.startPhase n 4 (gnPhased_lt (by omega))
    (gnRewindTape n pre post) .valuesEntry

private theorem gnCS_holdRight (n h : Nat) (hh : h < GNM.tapeLength n)
    (hb : h + 1 < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool) (q q' : GNState)
    (htr : ∀ scan : Bool,
      gnTransition gnCS.startPhase q scan = (gnCS.startPhase, q', scan, .right)) :
    TM.stepConfig (M := GNM)
        (Phased.alignedAt gnCS gnCS.startPhase n h hh tape q) =
      Phased.alignedAt gnCS gnCS.startPhase n (h + 1) hb tape q' := by
  have hstep := Phased.stepRight gnCS gnCS.startPhase n h hh hb tape q q'
    (tape ⟨h, hh⟩) (htr _)
  rwa [writeCell_self] at hstep

private theorem gnCS_valuesEntry_walk (n : Nat) (hsafe : 4 < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool) :
    TM.runConfig (M := GNM)
        (Phased.alignedAt gnCS gnCS.startPhase n 0 (gnPhased_lt (by omega)) tape
          (.rewind .p0)) 4 =
      Phased.alignedAt gnCS gnCS.startPhase n 4 hsafe tape .valuesEntry := by
  show TM.runConfig (M := GNM) _ (1 + 1 + 1 + 1) = _
  rw [runConfig_add, runConfig_add, runConfig_add]
  simp only [runConfig_one]
  have s0 : TM.stepConfig (M := GNM)
      (Phased.alignedAt gnCS gnCS.startPhase n 0 (gnPhased_lt (by omega)) tape
        (.rewind .p0)) =
      Phased.alignedAt gnCS gnCS.startPhase n 1 (gnPhased_lt (by omega)) tape
        (.rewind (.p1 false)) := by
    simpa using gnCS_holdRight n 0 (by omega) (by omega) tape _ _ (fun _ => rfl)
  have s1 : TM.stepConfig (M := GNM)
      (Phased.alignedAt gnCS gnCS.startPhase n 1 (gnPhased_lt (by omega)) tape
        (.rewind (.p1 false))) =
      Phased.alignedAt gnCS gnCS.startPhase n 2 (gnPhased_lt (by omega)) tape
        (.rewind (.p2 false false)) := by
    simpa using gnCS_holdRight n 1 (by omega) (by omega) tape _ _ (fun _ => rfl)
  have s2 : TM.stepConfig (M := GNM)
      (Phased.alignedAt gnCS gnCS.startPhase n 2 (gnPhased_lt (by omega)) tape
        (.rewind (.p2 false false))) =
      Phased.alignedAt gnCS gnCS.startPhase n 3 (gnPhased_lt (by omega)) tape
        (.rewind (.p3 false false false)) := by
    simpa using gnCS_holdRight n 2 (by omega) (by omega) tape _ _ (fun _ => rfl)
  have s3 : TM.stepConfig (M := GNM)
      (Phased.alignedAt gnCS gnCS.startPhase n 3 (gnPhased_lt (by omega)) tape
        (.rewind (.p3 false false false))) =
      Phased.alignedAt gnCS gnCS.startPhase n 4 hsafe tape .valuesEntry := by
    simpa using gnCS_holdRight n 3 (by omega) hsafe tape _ _ (fun _ => rfl)
  rw [s0, s1, s2, s3]

/-- **Generic exact rewind.**  From any `recordDone` boundary whose word is one
leading `bof`, a `bof`-free scanned block `pre`, and an arbitrary right context
`post`, the machine runs exactly `gnValuesRewindSteps pre.length` rows of
genuine `TM.runConfig (M := GNM)` execution and stops in the literal
`valuesEntry` state on p0 of the frame just after the anchor.  The tape of the
endpoint is *syntactically* the tape of the start: the pass writes nothing. -/
theorem gnCS_valuesRewind_exact (n : Nat) (pre post : List G1Frame)
    (hpre : ∀ f ∈ pre, f ≠ G1Frame.bof)
    (hroom : 4 * pre.length + 4 < GNM.tapeLength n) :
    TM.runConfig (M := GNM) (gnValuesRewindConfig n pre post hroom)
        (gnValuesRewindSteps pre.length) =
      gnValuesEntryConfigOf n pre post hroom := by
  have hpath := gnRewind_validPath hpre
  have hentry : TM.runConfig (M := GNM) (gnValuesRewindConfig n pre post hroom) 1 =
      Phased.alignedAt gnCS gnCS.startPhase n (4 * pre.length + 3)
        (gnPhased_lt (by omega)) (gnRewindTape n pre post) (.rewind .r3) := by
    rw [runConfig_one]
    have hstep := Phased.holdLeft gnCS gnCS.startPhase n (4 * (pre.length + 1))
      (gnPhased_lt (by omega)) (by omega) (gnRewindTape n pre post)
      GNState.recordDone (.rewind .r3) (fun _ => rfl)
    have hhead : 4 * (pre.length + 1) - 1 = 4 * pre.length + 3 := by omega
    simpa only [hhead] using hstep
  have hscan := gnRewindScanner.revScanToAnchor n G1Frame.bof pre post .scan ()
    hpath.1 (by rw [hpath.2]; trivial) (by rw [hpath.2]; trivial)
    (by rw [gnRewindScanner_machine]; omega)
  rw [hpath.2] at hscan
  have hscan' : TM.runConfig (M := GNM)
      (Phased.alignedAt gnCS gnCS.startPhase n (4 * pre.length + 3)
        (gnPhased_lt (by omega)) (gnRewindTape n pre post) (.rewind .r3))
        (4 * pre.length + 4) =
      Phased.alignedAt gnCS gnCS.startPhase n 0 (gnPhased_lt (by omega))
        (gnRewindTape n pre post) (.rewind .p0) := by
    simpa [gnRewindScanner, gnRewindTape, gnRewindStopState, gnRewindAdvance,
      List.append_assoc] using hscan
  rw [(gnValuesRewindSteps_provenance pre.length).1, runConfig_add, runConfig_add,
    hentry, hscan']
  exact gnCS_valuesEntry_walk n (by omega) (gnRewindTape n pre post)

/-! ## Real-input capstone -/

/-- Stage-zero frames strictly between the leading `bof` and the frame just
past the selected first record's closing `finish`: the current-value `data`
run, the reserved output slots, the record-region separator, and the whole
selected record. -/
def gnValuesRewindPre (r : GNProgram) (g : SLGate r.inputs.length) :
    List G1Frame :=
  gnAssignFrames r.inputs ++ gnSlotFrames r.program.gates.length ++
    [G1Frame.separator] ++ gnRecordFrames .cursor g

/-- Everything to the right of that block at the `recordDone` endpoint: the
rest of the source word, the installed scratch image, and the retained blank
frontier. -/
def gnValuesRewindPost (r : GNProgram) (g : SLGate r.inputs.length) :
    List G1Frame :=
  gnFirstRecordTail r ++ (gnRecordFrames .cursor g).map gnInstallImage ++
    [G1Frame.blank]

/-- Exact frame count of the scanned block. -/
theorem gnValuesRewindPre_length (r : GNProgram) (g : SLGate r.inputs.length) :
    (gnValuesRewindPre r g).length =
      r.inputs.length + r.program.gates.length + 1 +
        gnRecordSize (gnGateFields g) := by
  simp only [gnValuesRewindPre, gnRecordFrames, List.length_append,
    gnAssignFrames_length, gnSlotFrames_length, g1RecordFrames_length,
    List.length_cons, List.length_nil]

/-- The scanned block carries no `bof`, so the anchor the pass stops at is the
word's leading one.  Every frame of the block is a `data`, an output slot, the
record-region separator, the record's `cursor` marker, an ordinary record-body
frame, or the record's closing `finish`. -/
theorem gnValuesRewindPre_ne_bof (r : GNProgram) (g : SLGate r.inputs.length) :
    ∀ f ∈ gnValuesRewindPre r g, f ≠ G1Frame.bof := by
  intro f hf
  simp only [gnValuesRewindPre] at hf
  rcases List.mem_append.1 hf with hf | hf
  · rcases List.mem_append.1 hf with hf | hf
    · rcases List.mem_append.1 hf with hf | hf
      · obtain ⟨b, _, rfl⟩ := List.mem_map.1 hf
        cases b <;> decide
      · rw [List.eq_of_mem_replicate hf]; decide
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      subst hf; decide
  · rw [gnRecordFrames_cursor_split] at hf
    rcases List.mem_append.1 hf with hf | hf
    · rcases List.mem_cons.1 hf with rfl | hf
      · decide
      · rcases gnGateBodyFrames_body g f hf with rfl | rfl | rfl <;> decide
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      subst hf; decide

/-- Exact split of the `recordDone` endpoint word into anchor, scanned block,
and right context. -/
theorem gnValuesRewind_frames {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) :
    G1Frame.bof :: gnValuesRewindPre r g ++ gnValuesRewindPost r g =
      encodeGNFrames r ++ (gnRecordFrames .cursor g).map gnInstallImage ++
        [G1Frame.blank] := by
  have hsplit : encodeGNFrames r =
      gnLocatePrefix r ++ G1Frame.cursor :: gnFirstRecordMiddle r := by
    simpa [gnFirstRecordMiddle, List.append_assoc] using
      (encodeGNFrames_firstRecord_split hg).1
  rw [hsplit, gnFirstRecordMiddle_split hg]
  simp [gnValuesRewindPre, gnValuesRewindPost, gnLocatePrefix,
    gnRecordFrames_cursor_split, List.append_assoc]

private theorem gnValuesEntry_head_lt (N : Nat) : 4 < GNM.tapeLength N := by
  have hclock : gnClock N = 512 * (N + 1) ^ 2 + 512 := rfl
  change 4 < N + gnClock N + 1
  omega

private theorem gnValuesRewind_room {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) :
    4 * (gnValuesRewindPre r g).length + 4 <
      GNM.tapeLength (encodeGN r).length := by
  have h : 4 * (gnRecordsStart r + gnRecordSize (gnGateFields g)) <
      GNM.tapeLength (encodeGN r).length :=
    (gnFirstRecordDoneConfig r g hg).head.isLt
  have hlen := gnValuesRewindPre_length r g
  have hstart : gnRecordsStart r =
      r.inputs.length + r.program.gates.length + 2 := rfl
  omega

/-- Full real-initial schedule through the exact values boundary: GN-E2-3b's
first-record schedule, then the rewind. -/
def gnValuesEntrySteps (r : GNProgram) (g : SLGate r.inputs.length) : Nat :=
  gnFirstRecordDoneSteps r g +
    gnValuesRewindSteps
      (r.inputs.length + r.program.gates.length + 1 +
        gnRecordSize (gnGateFields g))

/-- Exact real-input values boundary.  Only the head differs from
`gnFirstRecordDoneConfig`; the physical tape is the same term. -/
def gnValuesEntryConfig (r : GNProgram) (g : SLGate r.inputs.length)
    (hg : r.program.gates[0]? = some g) :
    Configuration (M := GNM) (encodeGN r).length where
  state := ⟨(0 : Fin 1), .valuesEntry⟩
  head := ⟨4, gnValuesEntry_head_lt _⟩
  tape := (gnFirstRecordDoneConfig r g hg).tape

private theorem gnFirstRecordDone_eq_rewindConfig {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    gnFirstRecordDoneConfig r g hg =
      gnValuesRewindConfig (encodeGN r).length (gnValuesRewindPre r g)
        (gnValuesRewindPost r g) (gnValuesRewind_room hg) := by
  have hlen := gnValuesRewindPre_length r g
  have hstart : gnRecordsStart r =
      r.inputs.length + r.program.gates.length + 2 := rfl
  apply Configuration.ext_of_components
  · rfl
  · apply Fin.ext
    change 4 * (gnRecordsStart r + gnRecordSize (gnGateFields g)) =
      4 * ((gnValuesRewindPre r g).length + 1)
    omega
  · change frameListTape _ = gnRewindTape _ _ _
    simp only [gnRewindTape]
    rw [gnValuesRewind_frames hg]

/-- **Real-input capstone.**  Starting from the genuine
`GNM.initialConfig (gnPoint (encodeGN r))` and using the actually selected
first gate `g`, the machine runs exactly `gnValuesEntrySteps r g` rows of
genuine `TM.runConfig (M := GNM)` execution and stops in the exact values
boundary.  Nothing has been written since `recordDone`; what remains is the
values copy itself, which E2-4b owns. -/
theorem gnCS_encodeGN_valuesEntry_exact {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    TM.runConfig (M := GNM) (GNM.initialConfig (gnPoint (encodeGN r)))
        (gnValuesEntrySteps r g) = gnValuesEntryConfig r g hg := by
  have hlen := gnValuesRewindPre_length r g
  have hsched : gnValuesEntrySteps r g =
      gnFirstRecordDoneSteps r g +
        gnValuesRewindSteps (gnValuesRewindPre r g).length := by
    rw [gnValuesEntrySteps, hlen]
  rw [hsched, runConfig_add, gnCS_encodeGN_firstRecordDone_exact hg,
    gnFirstRecordDone_eq_rewindConfig hg,
    gnCS_valuesRewind_exact _ _ _ (gnValuesRewindPre_ne_bof r g)
      (gnValuesRewind_room hg)]
  apply Configuration.ext_of_components
  · rfl
  · rfl
  · change gnRewindTape _ _ _ = frameListTape _
    simp only [gnRewindTape]
    rw [gnValuesRewind_frames hg]

/-- Complete exact projections of the real-input values boundary.  The first
three conjuncts pin state, head and the full physical tape; the fourth says the
tape is *the same term* as the `recordDone` endpoint's, so the pass wrote
nothing; the fifth identifies head `4` as p0 of the first frame after the
leading `bof`, where the current-value `data` run
`gnCurrentValues r [] = r.inputs` begins; the sixth records what still has to be
written, namely that the installed scratch image followed by exactly that
current-value run is `g1PrefixFrames (gnFirstRequest r g)`.

The sixth conjunct is a statement about the **pure** request determined by `g`.
Nothing here says the machine has copied a value or evaluated anything: at this
endpoint it has only relocated the record's frames and moved its head. -/
theorem gnValuesEntryConfig_structure {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    (gnValuesEntryConfig r g hg).state =
        ⟨(0 : Fin 1), GNState.valuesEntry⟩ ∧
      ((gnValuesEntryConfig r g hg).head : Nat) = 4 ∧
      (gnValuesEntryConfig r g hg).tape =
        frameListTape
          ((encodeGNFrames r ++ (gnRecordFrames .cursor g).map gnInstallImage ++
            [G1Frame.blank]).flatMap G1Frame.bits) ∧
      (gnValuesEntryConfig r g hg).tape = (gnFirstRecordDoneConfig r g hg).tape ∧
      G1Frame.bof :: ((gnCurrentValues r []).map G1Frame.data ++
          gnSlotFrames r.program.gates.length ++ [G1Frame.separator]) =
        gnLocatePrefix r ∧
      (gnRecordFrames .cursor g).map gnInstallImage ++
          (gnCurrentValues r []).map G1Frame.data =
        g1PrefixFrames (gnFirstRequest r g) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · rw [gnCurrentValues_zero]
    simp [gnLocatePrefix, gnAssignFrames, List.append_assoc]
  · rw [gnCurrentValues_zero]
    exact gnFirstRecord_image_request_prefix r g

/-- Scoped clock fact: the complete proved prefix — validation, locator, the
`firstRecord` door, the cursor seed shuttle, the whole first-record body driver
and this rewind — fits inside the unchanged public `gnClock`.  This bounds
exactly that prefix.  It is **not** a total installer, multigate, or runtime
clock theorem. -/
theorem gnValuesEntrySteps_le_gnClock {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    gnValuesEntrySteps r g ≤ gnClock (encodeGN r).length := by
  have hs := encodeGNFrames_firstRecord_split hg
  have hmid := gnFirstRecordMiddle_split hg
  have hn : (encodeGN r).length =
      4 * (gnRecordsStart r + 1 + (gnFirstRecordMiddle r).length) := by
    rw [encodeGN_length, hs.1]
    simp only [List.length_append, List.length_cons, gnFirstRecordMiddle,
      List.length_nil]
    omega
  have hsplit : (gnFirstRecordMiddle r).length =
      (gnGateBodyFrames g).length + 1 + (gnFirstRecordTail r).length := by
    rw [hmid]
    simp only [List.length_append, List.length_cons]
    omega
  have hsize : gnRecordSize (gnGateFields g) = (gnGateBodyFrames g).length + 2 := by
    simp only [gnRecordSize, gnGateBodyFrames, List.length_append,
      List.length_replicate, List.length_cons, List.length_nil]
    omega
  have hstart : gnRecordsStart r =
      r.inputs.length + r.program.gates.length + 2 := rfl
  have hseed := gnBofSeedSteps_provenance r
  have hbound : (gnGateBodyFrames g).length ≤ (gnFirstRecordMiddle r).length := by
    omega
  have hprod : (gnGateBodyFrames g).length *
        (8 * (gnFirstRecordMiddle r).length + 30) ≤
      (gnFirstRecordMiddle r).length *
        (8 * (gnFirstRecordMiddle r).length + 30) :=
    Nat.mul_le_mul_right _ hbound
  have hexp : (gnFirstRecordMiddle r).length *
        (8 * (gnFirstRecordMiddle r).length + 30) =
      8 * ((gnFirstRecordMiddle r).length * (gnFirstRecordMiddle r).length) +
        30 * (gnFirstRecordMiddle r).length := by
    rw [Nat.mul_add, Nat.mul_left_comm,
      Nat.mul_comm (gnFirstRecordMiddle r).length 30]
  have hsq : (gnFirstRecordMiddle r).length * (gnFirstRecordMiddle r).length ≤
      ((encodeGN r).length + 1) * ((encodeGN r).length + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hpow : ((encodeGN r).length + 1) ^ 2 =
      ((encodeGN r).length + 1) * ((encodeGN r).length + 1) := pow_two _
  have hsquare : (encodeGN r).length + 1 ≤
      ((encodeGN r).length + 1) * ((encodeGN r).length + 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hclock : gnClock (encodeGN r).length =
      512 * ((encodeGN r).length + 1) ^ 2 + 512 := rfl
  rw [gnValuesEntrySteps, gnValuesRewindSteps, gnFirstRecordDoneSteps,
    gnBodyDriverSteps, gnBodyRoundSteps, gnBodyTerminalSteps, hclock, hpow]
  rw [hexp] at hprod
  omega

/-! ## One literal real-input values boundary -/

namespace GNValuesRewindProbes

open GNFixedDelegateProbes

/-- Exact literal values boundary for the one-constant-false program: the
nineteen-frame `recordDone` tape verbatim, head back at physical cell 4, which
is p0 of the frame after the leading `bof`. -/
def oneConstFalseValuesEntryConfig : Configuration (M := GNM) 48 where
  state := ⟨(0 : Fin 1), .valuesEntry⟩
  head := ⟨4, by
    simp [TM.tapeLength, gnCS, gnClock, g1Clock]⟩
  tape := frameListTape
    ([G1Frame.bof, .output false, .separator, .cursor, .tag, .tag,
      .argSep, .argSep, .finish, .separator, .output false, .finish,
      .bof, .tag, .tag, .argSep, .argSep, .separator,
      .blank].flatMap G1Frame.bits)

/-- Kernel-confirmed literal capstone: from the genuine real initial
configuration, 700 rows reach `valuesEntry` at physical head 4 with the exact
`recordDone` tape unchanged.  This program has no inputs, so the current-value
run at head 4 is empty and the frame there is the single reserved output
slot. -/
theorem literal_oneConstFalse_valuesEntry :
    TM.runConfig (M := GNM)
        (GNM.initialConfig (gnPoint (encodeGN oneConstFalseProgram))) 700 =
      oneConstFalseValuesEntryConfig ∧
    (oneConstFalseValuesEntryConfig.head : Nat) = 4 ∧
    oneConstFalseValuesEntryConfig.state =
      ⟨(0 : Fin 1), GNState.valuesEntry⟩ ∧
    oneConstFalseValuesEntryConfig.tape =
      GNBodyDriverProbes.oneConstFalseRecordDoneConfig.tape := by
  have hg : oneConstFalseProgram.program.gates[0]? =
      some (SLGate.const false : SLGate 0) := by rfl
  have hrun := gnCS_encodeGN_valuesEntry_exact hg
  have hsched : gnValuesEntrySteps oneConstFalseProgram
      (SLGate.const false : SLGate 0) = 700 := by decide
  rw [hsched] at hrun
  refine ⟨?_, rfl, rfl, rfl⟩
  refine hrun.trans ?_
  apply Configuration.ext_of_components
  · rfl
  · rfl
  · rfl

end GNValuesRewindProbes

end Pnp3.Internal.PsubsetPpoly.TM
