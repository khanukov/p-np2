import Complexity.TMVerifier.TuringToolkit.GateNEncoding

/-!
# GN-E1a finite lexical discovery grammar (2026-09-01)

**Progress classification: infrastructure, not P-vs-NP mainline progress.**

This is the pure, finite-control grammar used by the live GN word scan.  It
recognises the self-delimiting lexical shape of `encodeGNFrames`: initial
data, zero or more output-slot frames, a record region, and the terminal
`separator · output false · finish`.  Record `finish` returns to record mode;
only the terminal `finish` reaches `wordEnd`.

This grammar deliberately does not count slots or records and does not retain
indices.  Consequently it does not enforce slot-count = record-count, input
or prior-gate index bounds, or the typed argument conventions checked by the
exact-list parser.  Its language is lexical and self-delimiting; it is not
equivalent to `decodeGN?` and makes no claim about zero-padded physical tapes.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

/-- Fixed discovery modes.  `tag0` through `tag5` are the entire unary-tag
counter; index runs use self-loops and store no count. -/
inductive GNDiscoveryMode where
  | start | assignments | slots
  | firstRecord | laterRecord
  | tag0 | tag1 | tag2 | tag3 | tag4 | tag5
  | arg1 | arg2
  | terminalOutput | terminalFinish
  | wordEnd | reject
  deriving Fintype, DecidableEq, Repr

/-- Exactly the modes in which another four-cell frame may be consumed. -/
def GNDiscoveryMode.Forward : GNDiscoveryMode → Prop
  | .wordEnd | .reject => False
  | _ => True

/-- One shared frame-level lexical decision.  Unexpected decoded frames go to
`reject`; `finish` is interpreted according to the current finite mode. -/
def gnDiscoveryAdvance : GNDiscoveryMode → G1Frame → GNDiscoveryMode
  | .start, .bof => .assignments
  | .assignments, .data _ => .assignments
  | .assignments, .output false => .slots
  | .assignments, .separator => .firstRecord
  | .slots, .output false => .slots
  | .slots, .separator => .firstRecord
  | .firstRecord, .cursor => .tag0
  | .firstRecord, .separator => .terminalOutput
  | .laterRecord, .bof => .tag0
  | .laterRecord, .separator => .terminalOutput
  | .tag0, .tag => .tag1
  | .tag1, .tag => .tag2
  | .tag2, .tag => .tag3
  | .tag3, .tag => .tag4
  | .tag4, .tag => .tag5
  | .tag1, .argSep => .arg1
  | .tag2, .argSep => .arg1
  | .tag3, .argSep => .arg1
  | .tag4, .argSep => .arg1
  | .tag5, .argSep => .arg1
  | .arg1, .index => .arg1
  | .arg1, .argSep => .arg2
  | .arg2, .index => .arg2
  | .arg2, .finish => .laterRecord
  | .terminalOutput, .output false => .terminalFinish
  | .terminalFinish, .finish => .wordEnd
  | _, _ => .reject

/-- Bit-level completion used verbatim by the machine table.  This is the
single reserved-window decision: all undecodable windows reject. -/
def gnDiscoveryComplete (m : GNDiscoveryMode)
    (b0 b1 b2 b3 : Bool) : GNDiscoveryMode :=
  match decodeG1Frame? [b0, b1, b2, b3] with
  | some frame => gnDiscoveryAdvance m frame
  | none => .reject

theorem gnDiscoveryComplete_decode (m : GNDiscoveryMode)
    (b0 b1 b2 b3 : Bool) :
    gnDiscoveryComplete m b0 b1 b2 b3 =
      match decodeG1Frame? [b0, b1, b2, b3] with
      | some frame => gnDiscoveryAdvance m frame
      | none => .reject := rfl

/-- Pure list fold of the lexical decision. -/
def gnDiscoveryAdvanceList : GNDiscoveryMode → List G1Frame → GNDiscoveryMode
  | m, [] => m
  | m, frame :: rest =>
      gnDiscoveryAdvanceList (gnDiscoveryAdvance m frame) rest

/-- Pure path predicate matching the scanner kernel's obligations. -/
def GNDiscoveryValidPath : GNDiscoveryMode → List G1Frame → Prop
  | _, [] => True
  | m, frame :: rest =>
      m.Forward ∧ gnDiscoveryAdvance m frame ≠ .reject ∧
        GNDiscoveryValidPath (gnDiscoveryAdvance m frame) rest

private theorem gnDiscoveryAdvanceList_append (m : GNDiscoveryMode)
    (fs gs : List G1Frame) :
    gnDiscoveryAdvanceList m (fs ++ gs) =
      gnDiscoveryAdvanceList (gnDiscoveryAdvanceList m fs) gs := by
  induction fs generalizing m with
  | nil => rfl
  | cons f fs ih => simpa [gnDiscoveryAdvanceList] using ih (gnDiscoveryAdvance m f)

private theorem gnDiscoveryValidPath_append (m : GNDiscoveryMode)
    (fs gs : List G1Frame) :
    GNDiscoveryValidPath m (fs ++ gs) ↔
      GNDiscoveryValidPath m fs ∧
        GNDiscoveryValidPath (gnDiscoveryAdvanceList m fs) gs := by
  induction fs generalizing m with
  | nil => simp [GNDiscoveryValidPath, gnDiscoveryAdvanceList]
  | cons f fs ih =>
      simp only [List.cons_append, GNDiscoveryValidPath, gnDiscoveryAdvanceList]
      rw [ih (gnDiscoveryAdvance m f)]
      tauto

private theorem gnDiscovery_scan_append {m m' m'' : GNDiscoveryMode}
    {fs gs : List G1Frame}
    (hf : gnDiscoveryAdvanceList m fs = m' ∧ GNDiscoveryValidPath m fs)
    (hg : gnDiscoveryAdvanceList m' gs = m'' ∧ GNDiscoveryValidPath m' gs) :
    gnDiscoveryAdvanceList m (fs ++ gs) = m'' ∧
      GNDiscoveryValidPath m (fs ++ gs) := by
  rw [gnDiscoveryAdvanceList_append, gnDiscoveryValidPath_append, hf.1]
  exact ⟨hg.1, hf.2, hg.2⟩

private theorem gnDiscovery_data (bs : List Bool) :
    gnDiscoveryAdvanceList .assignments (bs.map G1Frame.data) = .assignments ∧
      GNDiscoveryValidPath .assignments (bs.map G1Frame.data) := by
  induction bs with
  | nil => exact ⟨rfl, trivial⟩
  | cons b bs ih => simpa [gnDiscoveryAdvanceList, GNDiscoveryValidPath,
      GNDiscoveryMode.Forward, gnDiscoveryAdvance] using ih

private theorem gnDiscovery_slots_separator (n : Nat) :
    gnDiscoveryAdvanceList .assignments
        (List.replicate n (.output false) ++ [.separator]) = .firstRecord ∧
      GNDiscoveryValidPath .assignments
        (List.replicate n (.output false) ++ [.separator]) := by
  induction n with
  | zero => simp [gnDiscoveryAdvanceList, GNDiscoveryValidPath,
      GNDiscoveryMode.Forward, gnDiscoveryAdvance]
  | succ n ih => simpa [List.replicate_succ, gnDiscoveryAdvanceList,
      GNDiscoveryValidPath, GNDiscoveryMode.Forward, gnDiscoveryAdvance] using
      (show gnDiscoveryAdvanceList .slots
          (List.replicate n (.output false) ++ [.separator]) = .firstRecord ∧
        GNDiscoveryValidPath .slots
          (List.replicate n (.output false) ++ [.separator]) by
        induction n with
        | zero => simp [gnDiscoveryAdvanceList, GNDiscoveryValidPath,
            GNDiscoveryMode.Forward, gnDiscoveryAdvance]
        | succ n ih => simpa [List.replicate_succ, gnDiscoveryAdvanceList,
            GNDiscoveryValidPath, GNDiscoveryMode.Forward, gnDiscoveryAdvance]
            using ih)

private theorem gnDiscovery_tag (tag : G1Tag) :
    gnDiscoveryAdvanceList .tag0 (List.replicate tag.units .tag ++ [.argSep]) =
        .arg1 ∧
      GNDiscoveryValidPath .tag0
        (List.replicate tag.units .tag ++ [.argSep]) := by
  cases tag <;> simp [G1Tag.units, gnDiscoveryAdvanceList,
    GNDiscoveryValidPath, GNDiscoveryMode.Forward, gnDiscoveryAdvance]

private theorem gnDiscovery_arg1_indices (n : Nat) :
    gnDiscoveryAdvanceList .arg1 (List.replicate n .index ++ [.argSep]) =
        .arg2 ∧
      GNDiscoveryValidPath .arg1 (List.replicate n .index ++ [.argSep]) := by
  induction n with
  | zero => simp [gnDiscoveryAdvanceList, GNDiscoveryValidPath,
      GNDiscoveryMode.Forward, gnDiscoveryAdvance]
  | succ n ih =>
      simpa [List.replicate_succ, gnDiscoveryAdvanceList,
        GNDiscoveryValidPath, GNDiscoveryMode.Forward, gnDiscoveryAdvance] using ih

private theorem gnDiscovery_arg2_indices (n : Nat) :
    gnDiscoveryAdvanceList .arg2 (List.replicate n .index ++ [.finish]) =
        .laterRecord ∧
      GNDiscoveryValidPath .arg2 (List.replicate n .index ++ [.finish]) := by
  induction n with
  | zero => simp [gnDiscoveryAdvanceList, GNDiscoveryValidPath,
      GNDiscoveryMode.Forward, gnDiscoveryAdvance]
  | succ n ih => simpa [List.replicate_succ, gnDiscoveryAdvanceList,
      GNDiscoveryValidPath, GNDiscoveryMode.Forward, gnDiscoveryAdvance] using ih

private theorem gnDiscovery_record (marker : G1Frame) (f : GNField)
    (hm : marker = .cursor ∨ marker = .bof) :
    gnDiscoveryAdvanceList (if marker = .cursor then .firstRecord else .laterRecord)
        (g1RecordFrames marker f) = .laterRecord ∧
      GNDiscoveryValidPath
        (if marker = .cursor then .firstRecord else .laterRecord)
        (g1RecordFrames marker f) := by
  rcases f with ⟨tag, a1, a2⟩
  let tagPart := List.replicate tag.units G1Frame.tag ++ [.argSep]
  let a1Part := List.replicate a1 G1Frame.index ++ [.argSep]
  let a2Part := List.replicate a2 G1Frame.index ++ [.finish]
  have hshape : g1RecordFrames marker (tag, a1, a2) =
      [marker] ++ tagPart ++ a1Part ++ a2Part := by
    simp [g1RecordFrames, tagPart, a1Part, a2Part, List.append_assoc]
  have hmarker : gnDiscoveryAdvanceList
      (if marker = .cursor then .firstRecord else .laterRecord) [marker] =
        .tag0 ∧
      GNDiscoveryValidPath
        (if marker = .cursor then .firstRecord else .laterRecord) [marker] := by
    rcases hm with rfl | rfl <;>
      simp [gnDiscoveryAdvanceList, GNDiscoveryValidPath,
        GNDiscoveryMode.Forward, gnDiscoveryAdvance]
  rw [hshape]
  have h0 := gnDiscovery_scan_append hmarker (gnDiscovery_tag tag)
  have h1 := gnDiscovery_scan_append h0 (gnDiscovery_arg1_indices a1)
  exact gnDiscovery_scan_append h1 (gnDiscovery_arg2_indices a2)

private theorem gnDiscovery_records_tail (marker : G1Frame)
    (fields : List GNField) (hm : marker = .cursor ∨ marker = .bof) :
    let mode0 := if marker = .cursor then .firstRecord else .laterRecord
    let frames := gnFieldRecordsFrames marker fields ++
      [.separator, .output false, .finish]
    gnDiscoveryAdvanceList mode0 frames = .wordEnd ∧
      GNDiscoveryValidPath mode0 frames := by
  induction fields generalizing marker with
  | nil =>
      rcases hm with rfl | rfl <;>
        simp [gnFieldRecordsFrames, gnDiscoveryAdvanceList,
          GNDiscoveryValidPath, GNDiscoveryMode.Forward, gnDiscoveryAdvance]
  | cons f fs ih =>
      dsimp only
      rw [gnFieldRecordsFrames, List.append_assoc]
      have ht := ih .bof (Or.inr rfl)
      exact gnDiscovery_scan_append (gnDiscovery_record marker f hm) ht

/-- Canonical GN frame words follow the finite lexical path and end exactly at
`wordEnd`.  This is one-way encoder coverage, not a parser equivalence. -/
theorem gnDiscovery_encodeGNFrames (r : GNProgram) :
    gnDiscoveryAdvanceList .start (encodeGNFrames r) = .wordEnd ∧
      GNDiscoveryValidPath .start (encodeGNFrames r) := by
  rcases r with ⟨inputs, ⟨gates⟩⟩
  let dataPart := inputs.map G1Frame.data
  let slotPart : List G1Frame :=
    List.replicate gates.length (.output false) ++ [.separator]
  let recordPart : List G1Frame :=
    gnFieldRecordsFrames .cursor (gates.map gnGateFields) ++
      [.separator, .output false, .finish]
  have hshape : encodeGNFrames ⟨inputs, ⟨gates⟩⟩ =
      [.bof] ++ dataPart ++ slotPart ++ recordPart := by
    simp [encodeGNFrames, gnAssignFrames, gnSlotFrames, gnRecordsFrames,
      dataPart, slotPart, recordPart, List.append_assoc]
  rw [hshape]
  have hbof : gnDiscoveryAdvanceList .start [.bof] = .assignments ∧
      GNDiscoveryValidPath .start [.bof] := by
    simp [gnDiscoveryAdvanceList, GNDiscoveryValidPath,
      GNDiscoveryMode.Forward, gnDiscoveryAdvance]
  have h0 := gnDiscovery_scan_append hbof (gnDiscovery_data inputs)
  have h1 := gnDiscovery_scan_append h0 (gnDiscovery_slots_separator gates.length)
  exact gnDiscovery_scan_append h1
    (gnDiscovery_records_tail .cursor (gates.map gnGateFields) (Or.inl rfl))

/-- The three reserved four-bit windows share the same rejecting completion
decision in every aligned forward mode. -/
theorem gnDiscoveryComplete_reserved (m : GNDiscoveryMode) :
    gnDiscoveryComplete m true true false true = .reject ∧
      gnDiscoveryComplete m true true true false = .reject ∧
        gnDiscoveryComplete m true true true true = .reject := by
  cases m <;> simp [gnDiscoveryComplete, decodeG1Frame?]

/-- Representative decoded-but-lexically-malformed frames reject at start. -/
theorem gnDiscoveryAdvance_start_malformed :
    gnDiscoveryAdvance .start .blank = .reject ∧
      gnDiscoveryAdvance .start .spent = .reject ∧
        gnDiscoveryAdvance .start (.output true) = .reject ∧
          gnDiscoveryAdvance .start .separator = .reject ∧
            gnDiscoveryAdvance .start .cursor = .reject ∧
              gnDiscoveryAdvance .assignments .bof = .reject := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Pnp3.Internal.PsubsetPpoly.TM
