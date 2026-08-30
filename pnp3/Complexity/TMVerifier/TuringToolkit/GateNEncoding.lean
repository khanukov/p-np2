import Complexity.TMVerifier.TuringToolkit.GateOneSemantics
import Complexity.TMVerifier.TuringToolkit.Encoding

/-!
# GN-1: fixed pure multi-gate encoding

**Progress classification: Infrastructure.**  This module defines only a
finite `G1Frame`-based ABI, total/optional parsers, and pure list semantics.
It contains no machine parameters, advice, transition system, execution,
clock, or acceptance claim.

The existing thirteen decoded `G1Frame` codes are reused unchanged; the
reserved codes `1101`, `1110`, and `1111` remain rejected by
`decodeG1Frame?`.  A program word is

```text
bof · data(inputs) · output(false)^m · separator
    · record_0 ... record_(m-1) · separator · output(false) · finish

record_i = marker_i · tag^units · argSep · index^arg1
           · argSep · index^arg2 · finish
```

Here `marker_0 = cursor`, later markers are `bof`, and `m` is the gate count.
An input index is absolute in the initial value region.  A prior-gate index
`k` is stored as `n + k`, also absolute.  The pure meaning of every record is
exactly `G1Request.spec` on the caller's current `vals`; in particular the
`input` tag selects `vals[arg1]?` and does not itself read an external input.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Encoding

/-- The three serialized fields of one gate: tag and two absolute indices. -/
abbrev GNField := G1Tag × Nat × Nat

/-- A typed program paired with the initial on-word value environment. -/
structure GNProgram where
  inputs : List Bool
  program : SLProgram inputs.length

/-- Serialize an `SLGate` into the current G1 tag/operand convention. -/
def gnGateFields {n : Nat} : SLGate n → GNField
  | .input i => (.input, i.val, 0)
  | .const b => (.const, if b then 1 else 0, 0)
  | .notGate k => (.not, n + k, 0)
  | .andGate k l => (.and, n + k, n + l)
  | .orGate k l => (.or, n + k, n + l)

@[simp] theorem gnGateFields_input {n : Nat} (i : Fin n) :
    gnGateFields (SLGate.input i) = (G1Tag.input, i.val, 0) := rfl

@[simp] theorem gnGateFields_const {n : Nat} (b : Bool) :
    gnGateFields (SLGate.const b : SLGate n) =
      (G1Tag.const, if b then 1 else 0, 0) := rfl

@[simp] theorem gnGateFields_not {n : Nat} (k : Nat) :
    gnGateFields (SLGate.notGate k : SLGate n) = (.not, n + k, 0) := rfl

@[simp] theorem gnGateFields_and {n : Nat} (k l : Nat) :
    gnGateFields (SLGate.andGate k l : SLGate n) = (.and, n + k, n + l) := rfl

@[simp] theorem gnGateFields_or {n : Nat} (k l : Nat) :
    gnGateFields (SLGate.orGate k l : SLGate n) = (.or, n + k, n + l) := rfl

/-- The exact typed-image condition enforced by the record/program parser. -/
def GNField.CanonicalFor (n : Nat) (f : GNField) : Prop :=
  ∃ g : SLGate n, f = gnGateFields g

/-- Turn serialized fields and the current value environment into a G1 request. -/
def gnFieldRequest (f : GNField) (vals : List Bool) : G1Request :=
  ⟨f.1, f.2.1, f.2.2, vals⟩

/-- Pure field interpretation; this is precisely the current G1 semantics. -/
def gnFieldEval (f : GNField) (vals : List Bool) : Option Bool :=
  (gnFieldRequest f vals).spec

@[simp] theorem gnFieldEval_input {n : Nat} (i : Fin n) (vals : List Bool) :
    gnFieldEval (gnGateFields (SLGate.input i)) vals = vals[i.val]? := rfl

@[simp] theorem gnFieldEval_const {n : Nat} (b : Bool) (vals : List Bool) :
    gnFieldEval (gnGateFields (SLGate.const b : SLGate n)) vals = some b := by
  cases b <;> rfl

@[simp] theorem gnFieldEval_not {n : Nat} (k : Nat) (vals : List Bool) :
    gnFieldEval (gnGateFields (SLGate.notGate k : SLGate n)) vals =
      vals[n + k]?.map (!·) := rfl

theorem gnFieldEval_and {n : Nat} (k l : Nat) (vals : List Bool)
    (a b : Bool) (h1 : vals[n + k]? = some a) (h2 : vals[n + l]? = some b) :
    gnFieldEval (gnGateFields (SLGate.andGate k l : SLGate n)) vals =
      some (a && b) :=
  G1Request.spec_and_of h1 h2

theorem gnFieldEval_or {n : Nat} (k l : Nat) (vals : List Bool)
    (a b : Bool) (h1 : vals[n + k]? = some a) (h2 : vals[n + l]? = some b) :
    gnFieldEval (gnGateFields (SLGate.orGate k l : SLGate n)) vals =
      some (a || b) :=
  G1Request.spec_or_of h1 h2

/-- A field evaluates exactly when the corresponding current G1 request is
well formed for the supplied current environment. -/
theorem gnFieldEval_isSome_iff (f : GNField) (vals : List Bool) :
    (gnFieldEval f vals).isSome = true ↔ (gnFieldRequest f vals).WellFormed :=
  G1Request.spec_isSome_iff _

/-! ## Individual records -/

/-- One frame-level record, with unary tag and absolute-index fields. -/
def g1RecordFrames (marker : G1Frame) (f : GNField) : List G1Frame :=
  [marker] ++ List.replicate f.1.units .tag ++ [.argSep] ++
    List.replicate f.2.1 .index ++ [.argSep] ++
    List.replicate f.2.2 .index ++ [.finish]

def gnRecordFrames {n : Nat} (marker : G1Frame) (g : SLGate n) : List G1Frame :=
  g1RecordFrames marker (gnGateFields g)

def encodeGNRecord (marker : G1Frame) (f : GNField) : List Bool :=
  (g1RecordFrames marker f).flatMap G1Frame.bits

def gnRecordSize (f : GNField) : Nat := f.1.units + f.2.1 + f.2.2 + 4

@[simp] theorem g1RecordFrames_length (marker : G1Frame) (f : GNField) :
    (g1RecordFrames marker f).length = gnRecordSize f := by
  simp [g1RecordFrames, gnRecordSize]
  omega

@[simp] theorem encodeGNRecord_length (marker : G1Frame) (f : GNField) :
    (encodeGNRecord marker f).length = 4 * gnRecordSize f := by
  rw [encodeGNRecord, G1Frame.flatMap_bits_length, g1RecordFrames_length]

/-- Parse a record body after its marker. -/
def parseGNRecordBody (fs : List G1Frame) : Option (GNField × List G1Frame) := do
  let (units, fs) ← parseG1Run .tag .argSep fs
  let tag ← g1TagOfUnits? units
  let (a1, fs) ← parseG1Run .index .argSep fs
  let (a2, fs) ← parseG1Run .index .finish fs
  pure ((tag, a1, a2), fs)

/-- Parse one record and leave its unconsumed suffix. -/
def parseGNRecord (marker : G1Frame) :
    List G1Frame → Option (GNField × List G1Frame)
  | [] => none
  | f :: rest => if f = marker then parseGNRecordBody rest else none

/-- Exact-list frame parser for an individual record. -/
def decodeGNRecordFrames? (marker : G1Frame) (fs : List G1Frame) : Option GNField := do
  let (field, rest) ← parseGNRecord marker fs
  if rest = [] then some field else none

/-- Physical exact-list parser for an individual record. -/
def decodeGNRecord? (marker : G1Frame) (bits : List Bool) : Option GNField := do
  decodeGNRecordFrames? marker (← decodeG1Frames? bits)

private theorem parseGNRecord_encoded (marker : G1Frame) (f : GNField)
    (rest : List G1Frame) :
    parseGNRecord marker (g1RecordFrames marker f ++ rest) = some (f, rest) := by
  rcases f with ⟨tag, a1, a2⟩
  simp [g1RecordFrames, parseGNRecord, parseGNRecordBody, List.append_assoc,
    parseG1Run_encoded (by decide : G1Frame.tag ≠ G1Frame.argSep),
    parseG1Run_encoded (by decide : G1Frame.index ≠ G1Frame.argSep),
    parseG1Run_encoded (by decide : G1Frame.index ≠ G1Frame.finish)]

@[simp] theorem decodeGNRecordFrames?_encoded (marker : G1Frame) (f : GNField) :
    decodeGNRecordFrames? marker (g1RecordFrames marker f) = some f := by
  have hrec : parseGNRecord marker (g1RecordFrames marker f) = some (f, []) := by
    simpa using parseGNRecord_encoded marker f []
  unfold decodeGNRecordFrames?
  rw [hrec]
  rfl

@[simp] theorem decodeGNRecord?_encoded (marker : G1Frame) (f : GNField) :
    decodeGNRecord? marker (encodeGNRecord marker f) = some f := by
  simp [decodeGNRecord?, encodeGNRecord]

theorem encodeGNRecord_injective (marker : G1Frame) :
    Function.Injective (encodeGNRecord marker) := by
  intro f g h
  have := congrArg (decodeGNRecord? marker) h
  simpa using this

/-! ## Whole-program encoder and parser -/

def gnAssignFrames (inputs : List Bool) : List G1Frame := inputs.map .data

def gnSlotFrames (m : Nat) : List G1Frame := List.replicate m (.output false)

def gnFieldRecordsFrames : G1Frame → List GNField → List G1Frame
  | _, [] => []
  | marker, f :: rest =>
      g1RecordFrames marker f ++ gnFieldRecordsFrames .bof rest

def gnRecordsFrames {n : Nat} (marker : G1Frame) (gates : List (SLGate n)) :
    List G1Frame :=
  gnFieldRecordsFrames marker (gates.map gnGateFields)

def encodeGNFrames (r : GNProgram) : List G1Frame :=
  [.bof] ++ gnAssignFrames r.inputs ++ gnSlotFrames r.program.gates.length ++
    [.separator] ++ gnRecordsFrames .cursor r.program.gates ++
    [.separator, .output false, .finish]

def encodeGN (r : GNProgram) : List Bool :=
  (encodeGNFrames r).flatMap G1Frame.bits

/-- First frame of the reserved output-slot region. -/
def gnOutputSlotsStart (r : GNProgram) : Nat := 1 + r.inputs.length

/-- Number of reserved output-slot frames. -/
def gnOutputSlotsLength (r : GNProgram) : Nat := r.program.gates.length

/-- First frame of the gate-record region. -/
def gnRecordsStart (r : GNProgram) : Nat :=
  r.inputs.length + r.program.gates.length + 2

/-- Number of frames occupied by all gate records. -/
def gnRecordsLength (r : GNProgram) : Nat :=
  (r.program.gates.map (gnRecordSize ∘ gnGateFields)).sum

/-- Frame position of the final output cell's four-bit frame. -/
def gnFinalOutputFrame (r : GNProgram) : Nat :=
  r.inputs.length + r.program.gates.length + gnRecordsLength r + 3

private theorem gnFieldRecordsFrames_length (marker : G1Frame)
    (fields : List GNField) :
    (gnFieldRecordsFrames marker fields).length = (fields.map gnRecordSize).sum := by
  induction fields generalizing marker with
  | nil => rfl
  | cons f fs ih =>
      simp [gnFieldRecordsFrames, ih, g1RecordFrames_length]

@[simp] theorem gnAssignFrames_length (inputs : List Bool) :
    (gnAssignFrames inputs).length = inputs.length := by
  simp [gnAssignFrames]

@[simp] theorem gnSlotFrames_length (m : Nat) :
    (gnSlotFrames m).length = m := by
  simp [gnSlotFrames]

theorem gnRecordsFrames_length {n : Nat} (marker : G1Frame)
    (gates : List (SLGate n)) :
    (gnRecordsFrames marker gates).length =
      (gates.map (gnRecordSize ∘ gnGateFields)).sum := by
  simp [gnRecordsFrames, gnFieldRecordsFrames_length, Function.comp_def]

@[simp] theorem encodeGNFrames_length (r : GNProgram) :
    (encodeGNFrames r).length = r.inputs.length + r.program.gates.length +
      (r.program.gates.map (gnRecordSize ∘ gnGateFields)).sum + 5 := by
  rcases r with ⟨inputs, ⟨gates⟩⟩
  simp [encodeGNFrames, gnAssignFrames, gnSlotFrames, gnRecordsFrames,
    gnFieldRecordsFrames_length, Function.comp_def]
  omega

@[simp] theorem encodeGN_length (r : GNProgram) :
    (encodeGN r).length = 4 * (encodeGNFrames r).length := by
  rw [encodeGN, G1Frame.flatMap_bits_length]

theorem gnOutputSlots_extent (r : GNProgram) :
    gnOutputSlotsStart r + gnOutputSlotsLength r =
      r.inputs.length + r.program.gates.length + 1 := by
  simp [gnOutputSlotsStart, gnOutputSlotsLength]
  omega

theorem gnRecords_extent (r : GNProgram) :
    gnRecordsStart r + gnRecordsLength r =
      r.inputs.length + r.program.gates.length + gnRecordsLength r + 2 := by
  simp [gnRecordsStart]
  omega

theorem gnFinalOutputFrame_eq (r : GNProgram) :
    gnFinalOutputFrame r = (encodeGNFrames r).length - 2 := by
  simp [gnFinalOutputFrame, gnRecordsLength]

/-- Both variable regions and the final-output frame lie within the frame word. -/
theorem gnRegions_within_frames (r : GNProgram) :
    gnOutputSlotsStart r + gnOutputSlotsLength r ≤ (encodeGNFrames r).length ∧
      gnRecordsStart r + gnRecordsLength r ≤ (encodeGNFrames r).length ∧
        gnFinalOutputFrame r < (encodeGNFrames r).length := by
  simp [gnOutputSlotsStart, gnOutputSlotsLength, gnRecordsStart,
    gnRecordsLength, gnFinalOutputFrame]
  omega

/-- Multiplying the frame extents by four gives in-bounds physical bit extents. -/
theorem gnRegions_within_bits (r : GNProgram) :
    4 * (gnOutputSlotsStart r + gnOutputSlotsLength r) ≤ (encodeGN r).length ∧
      4 * (gnRecordsStart r + gnRecordsLength r) ≤ (encodeGN r).length ∧
        4 * gnFinalOutputFrame r + 4 ≤ (encodeGN r).length := by
  rw [encodeGN_length]
  obtain ⟨hslots, hrecords, hfinal⟩ := gnRegions_within_frames r
  omega

def parseGNAssign : List G1Frame → List Bool × List G1Frame
  | .data b :: rest =>
      let parsed := parseGNAssign rest
      (b :: parsed.1, parsed.2)
  | fs => ([], fs)

def parseGNSlots : List G1Frame → Nat × List G1Frame
  | .output false :: rest =>
      let parsed := parseGNSlots rest
      (parsed.1 + 1, parsed.2)
  | fs => (0, fs)

def parseGNRecords :
    G1Frame → Nat → List G1Frame → Option (List GNField × List G1Frame)
  | _, 0, fs => some ([], fs)
  | marker, k + 1, fs => do
      let (record, fs) ← parseGNRecord marker fs
      let (records, fs) ← parseGNRecords .bof k fs
      pure (record :: records, fs)

/-- Typed inverse of the absolute-index field convention. -/
def gnGateOfFields? (n : Nat) : GNField → Option (SLGate n)
  | (.input, a1, a2) =>
      if h : a1 < n then if a2 = 0 then some (.input ⟨a1, h⟩) else none else none
  | (.const, a1, a2) =>
      if a2 = 0 then
        if a1 = 0 then some (.const false)
        else if a1 = 1 then some (.const true) else none
      else none
  | (.not, a1, a2) =>
      if n ≤ a1 then if a2 = 0 then some (.notGate (a1 - n)) else none else none
  | (.and, a1, a2) =>
      if n ≤ a1 then
        if n ≤ a2 then some (.andGate (a1 - n) (a2 - n)) else none
      else none
  | (.or, a1, a2) =>
      if n ≤ a1 then
        if n ≤ a2 then some (.orGate (a1 - n) (a2 - n)) else none
      else none

def gnGatesOfFields? (n : Nat) : List GNField → Option (List (SLGate n))
  | [] => some []
  | f :: rest => do
      let g ← gnGateOfFields? n f
      pure (g :: (← gnGatesOfFields? n rest))

def gnProgramOf? (inputs : List Bool) (fields : List GNField) : Option GNProgram := do
  let gates ← gnGatesOfFields? inputs.length fields
  pure ⟨inputs, ⟨gates⟩⟩

def gnCanonicalTail : List G1Frame := [.separator, .output false, .finish]

def decodeGNTail? (inputs : List Bool) (slots : Nat) (fs : List G1Frame) :
    Option GNProgram := do
  let (fields, rest) ← parseGNRecords .cursor slots fs
  if rest = gnCanonicalTail then gnProgramOf? inputs fields else none

def decodeGNFrameList? : List G1Frame → Option GNProgram
  | .bof :: rest =>
      let (inputs, rest) := parseGNAssign rest
      let (slots, rest) := parseGNSlots rest
      match rest with
      | .separator :: rest => decodeGNTail? inputs slots rest
      | _ => none
  | _ => none

def decodeGN? (bits : List Bool) : Option GNProgram := do
  decodeGNFrameList? (← decodeG1Frames? bits)

private theorem parseGNAssign_append (bs : List Bool) (rest : List G1Frame)
    (h : ∀ b, rest.head? ≠ some (.data b)) :
    parseGNAssign (bs.map G1Frame.data ++ rest) = (bs, rest) := by
  induction bs with
  | nil =>
      cases rest with
      | nil => rfl
      | cons f tl =>
          cases f with
          | data b => exact absurd rfl (h b)
          | output b => cases b <;> rfl
          | blank | bof | tag | index | separator | cursor | finish | argSep
          | spent => rfl
  | cons b bs ih => simp [parseGNAssign, ih]

private theorem parseGNSlots_append (m : Nat) (rest : List G1Frame)
    (h : rest.head? ≠ some (.output false)) :
    parseGNSlots (gnSlotFrames m ++ rest) = (m, rest) := by
  induction m with
  | zero =>
      cases rest with
      | nil => rfl
      | cons f tl =>
          cases f with
          | output b => cases b with
            | false => exact absurd rfl h
            | true => rfl
          | data b => rfl
          | blank | bof | tag | index | separator | cursor | finish | argSep
          | spent => rfl
  | succ m ih =>
      have hshape : gnSlotFrames (m + 1) ++ rest =
          G1Frame.output false :: (gnSlotFrames m ++ rest) := by
        simp [gnSlotFrames, List.replicate_succ]
      rw [hshape]
      simp only [parseGNSlots]
      rw [ih]

private theorem parseGNRecords_encoded (marker : G1Frame) (fields : List GNField)
    (rest : List G1Frame) :
    parseGNRecords marker fields.length
        (gnFieldRecordsFrames marker fields ++ rest) = some (fields, rest) := by
  induction fields generalizing marker with
  | nil => rfl
  | cons f fs ih =>
      simp only [List.length_cons, parseGNRecords, gnFieldRecordsFrames]
      rw [List.append_assoc, parseGNRecord_encoded]
      change (parseGNRecords G1Frame.bof fs.length
        (gnFieldRecordsFrames G1Frame.bof fs ++ rest)).bind
          (fun q => some (f :: q.1, q.2)) = some (f :: fs, rest)
      rw [ih G1Frame.bof]
      rfl

private theorem parseGNAssign_exact (fs : List G1Frame) :
    fs = (parseGNAssign fs).1.map G1Frame.data ++ (parseGNAssign fs).2 := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      cases f with
      | data b =>
          simpa only [parseGNAssign, Prod.fst, Prod.snd, List.map_cons,
            List.cons_append] using congrArg (List.cons (G1Frame.data b)) ih
      | output b => cases b <;> rfl
      | blank | bof | tag | index | separator | cursor | finish | argSep
      | spent => rfl

private theorem parseGNSlots_exact (fs : List G1Frame) :
    fs = gnSlotFrames (parseGNSlots fs).1 ++ (parseGNSlots fs).2 := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      cases f with
      | output b => cases b with
        | false =>
            simp only [parseGNSlots]
            calc
              G1Frame.output false :: fs = .output false ::
                  (gnSlotFrames (parseGNSlots fs).1 ++
                    (parseGNSlots fs).2) := congrArg _ ih
              _ = gnSlotFrames ((parseGNSlots fs).1 + 1) ++
                  (parseGNSlots fs).2 := by
                    simp [gnSlotFrames, List.replicate_succ]
        | true => rfl
      | data b => rfl
      | blank | bof | tag | index | separator | cursor | finish | argSep
      | spent => rfl

private theorem parseGNRecordBody_eq_some {fs : List G1Frame}
    {f : GNField} {rest : List G1Frame}
    (h : parseGNRecordBody fs = some (f, rest)) :
    fs = List.replicate f.1.units .tag ++ .argSep ::
      (List.replicate f.2.1 .index ++ .argSep ::
        (List.replicate f.2.2 .index ++ .finish :: rest)) := by
  cases ht : parseG1Run .tag .argSep fs with
  | none => simp [parseGNRecordBody, ht] at h
  | some rt =>
      rcases rt with ⟨units, afterTag⟩
      cases htag : g1TagOfUnits? units with
      | none => simp [parseGNRecordBody, ht, htag] at h
      | some tag =>
          cases h1 : parseG1Run .index .argSep afterTag with
          | none => simp [parseGNRecordBody, ht, htag, h1] at h
          | some r1 =>
              rcases r1 with ⟨a1, after1⟩
              cases h2 : parseG1Run .index .finish after1 with
              | none => simp [parseGNRecordBody, ht, htag, h1, h2] at h
              | some r2 =>
                  rcases r2 with ⟨a2, after2⟩
                  simp [parseGNRecordBody, ht, htag, h1, h2] at h
                  rcases h with ⟨rfl, rfl⟩
                  rw [parseG1Run_eq_some ht, parseG1Run_eq_some h1,
                    parseG1Run_eq_some h2, g1TagOfUnits?_eq_some htag]

private theorem parseGNRecord_eq_some {marker : G1Frame} {fs : List G1Frame}
    {f : GNField} {rest : List G1Frame}
    (h : parseGNRecord marker fs = some (f, rest)) :
    fs = g1RecordFrames marker f ++ rest := by
  cases fs with
  | nil => simp [parseGNRecord] at h
  | cons head tail =>
      by_cases hm : head = marker
      · subst head
        simp [parseGNRecord] at h
        rw [parseGNRecordBody_eq_some h]
        simp [g1RecordFrames, List.append_assoc]
      · simp [parseGNRecord, hm] at h

private theorem parseGNRecords_eq_some {marker : G1Frame} {k : Nat}
    {fs : List G1Frame} {fields : List GNField} {rest : List G1Frame}
    (h : parseGNRecords marker k fs = some (fields, rest)) :
    fields.length = k ∧ fs = gnFieldRecordsFrames marker fields ++ rest := by
  induction k generalizing marker fs fields rest with
  | zero =>
      simp [parseGNRecords] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
  | succ k ih =>
      simp only [parseGNRecords] at h
      cases hr : parseGNRecord marker fs with
      | none => simp [hr] at h
      | some rr =>
          rcases rr with ⟨f, afterRecord⟩
          cases hrs : parseGNRecords .bof k afterRecord with
          | none => simp [hr, hrs] at h
          | some rs =>
              rcases rs with ⟨tail, afterRecords⟩
              simp [hr, hrs] at h
              rcases h with ⟨rfl, rfl⟩
              obtain ⟨hlen, hexact⟩ := ih hrs
              constructor
              · simp [hlen]
              · rw [parseGNRecord_eq_some hr, hexact]
                simp [gnFieldRecordsFrames, List.append_assoc]

@[simp] theorem gnGateOfFields?_gnGateFields {n : Nat} (g : SLGate n) :
    gnGateOfFields? n (gnGateFields g) = some g := by
  cases g with
  | input i => simp [gnGateOfFields?, i.isLt]
  | const b => cases b <;> simp [gnGateOfFields?]
  | notGate k => simp [gnGateOfFields?]
  | andGate k l => simp [gnGateOfFields?]
  | orGate k l => simp [gnGateOfFields?]

private theorem gnGatesOfFields?_map {n : Nat} (gates : List (SLGate n)) :
    gnGatesOfFields? n (gates.map gnGateFields) = some gates := by
  induction gates with
  | nil => rfl
  | cons g gs ih => simp [gnGatesOfFields?, gnGateOfFields?_gnGateFields, ih]

theorem gnGateFields_canonical {n : Nat} (g : SLGate n) :
    (gnGateFields g).CanonicalFor n := ⟨g, rfl⟩

theorem gnGateOfFields?_eq_some {n : Nat} {f : GNField} {g : SLGate n}
    (h : gnGateOfFields? n f = some g) : f = gnGateFields g := by
  rcases f with ⟨tag, a1, a2⟩
  cases tag with
  | input =>
      by_cases h1 : a1 < n
      · by_cases h2 : a2 = 0
        · subst a2
          simp [gnGateOfFields?, h1] at h
          subst g
          rfl
        · simp [gnGateOfFields?, h1, h2] at h
      · simp [gnGateOfFields?, h1] at h
  | const =>
      by_cases h2 : a2 = 0
      · subst a2
        by_cases h0 : a1 = 0
        · subst a1
          simp [gnGateOfFields?] at h
          subst g
          rfl
        · by_cases h1 : a1 = 1
          · subst a1
            simp [gnGateOfFields?, h0] at h
            subst g
            rfl
          · simp [gnGateOfFields?, h0, h1] at h
      · simp [gnGateOfFields?, h2] at h
  | not =>
      by_cases h1 : n ≤ a1
      · by_cases h2 : a2 = 0
        · subst a2
          simp [gnGateOfFields?, h1] at h
          subst g
          simp [gnGateFields]
          omega
        · simp [gnGateOfFields?, h1, h2] at h
      · simp [gnGateOfFields?, h1] at h
  | and =>
      by_cases h1 : n ≤ a1
      · by_cases h2 : n ≤ a2
        · simp [gnGateOfFields?, h1, h2] at h
          subst g
          simp [gnGateFields]
          omega
        · simp [gnGateOfFields?, h1, h2] at h
      · simp [gnGateOfFields?, h1] at h
  | or =>
      by_cases h1 : n ≤ a1
      · by_cases h2 : n ≤ a2
        · simp [gnGateOfFields?, h1, h2] at h
          subst g
          simp [gnGateFields]
          omega
        · simp [gnGateOfFields?, h1, h2] at h
      · simp [gnGateOfFields?, h1] at h

theorem gnGateOfFields?_isSome_iff (n : Nat) (f : GNField) :
    (gnGateOfFields? n f).isSome = true ↔ f.CanonicalFor n := by
  constructor
  · intro h
    cases hg : gnGateOfFields? n f with
    | none => simp [hg] at h
    | some g => exact ⟨g, gnGateOfFields?_eq_some hg⟩
  · rintro ⟨g, rfl⟩
    simp

private theorem gnGatesOfFields?_eq_some {n : Nat} {fields : List GNField}
    {gates : List (SLGate n)} (h : gnGatesOfFields? n fields = some gates) :
    fields = gates.map gnGateFields := by
  induction fields generalizing gates with
  | nil => simp [gnGatesOfFields?] at h; subst gates; rfl
  | cons f fs ih =>
      simp only [gnGatesOfFields?] at h
      cases hg : gnGateOfFields? n f with
      | none => simp [hg] at h
      | some g =>
          cases hgs : gnGatesOfFields? n fs with
          | none => simp [hg, hgs] at h
          | some gs =>
              simp [hg, hgs] at h
              subst gates
              rw [gnGateOfFields?_eq_some hg, ih hgs]
              rfl

private theorem slots_head_ne_data (m : Nat) (rest : List G1Frame) (b : Bool) :
    (gnSlotFrames m ++ G1Frame.separator :: rest).head? ≠ some (.data b) := by
  cases m <;> simp [gnSlotFrames, List.replicate_succ]

@[simp] theorem decodeGNFrameList?_encodeGNFrames (r : GNProgram) :
    decodeGNFrameList? (encodeGNFrames r) = some r := by
  rcases r with ⟨inputs, ⟨gates⟩⟩
  have hshape : encodeGNFrames ⟨inputs, ⟨gates⟩⟩ =
      G1Frame.bof :: (inputs.map G1Frame.data ++
        (gnSlotFrames gates.length ++ G1Frame.separator ::
          (gnFieldRecordsFrames G1Frame.cursor (gates.map gnGateFields) ++
            gnCanonicalTail))) := by
    simp [encodeGNFrames, gnAssignFrames, gnRecordsFrames, gnCanonicalTail,
      List.append_assoc]
  rw [hshape]
  simp only [decodeGNFrameList?]
  rw [parseGNAssign_append _ _ (slots_head_ne_data gates.length _)]
  rw [parseGNSlots_append _ _ (by simp)]
  unfold decodeGNTail?
  change (parseGNRecords G1Frame.cursor gates.length
      (gnFieldRecordsFrames G1Frame.cursor (gates.map gnGateFields) ++
        gnCanonicalTail)).bind
        (fun p => if p.2 = gnCanonicalTail then gnProgramOf? inputs p.1 else none) =
      some ⟨inputs, ⟨gates⟩⟩
  rw [show gates.length = (gates.map gnGateFields).length by simp]
  rw [parseGNRecords_encoded]
  simp [gnProgramOf?, gnGatesOfFields?_map]

/-- A successful frame parse determines the entire canonical frame image. -/
theorem decodeGNFrameList?_eq_some {fs : List G1Frame} {r : GNProgram}
    (h : decodeGNFrameList? fs = some r) : fs = encodeGNFrames r := by
  rcases fs with _ | ⟨frame, originalRest⟩
  · simp [decodeGNFrameList?] at h
  cases frame with
  | bof =>
      simp only [decodeGNFrameList?] at h
      cases ha : parseGNAssign originalRest with
      | mk inputs afterInputs =>
          cases hs : parseGNSlots afterInputs with
          | mk slots afterSlots =>
              rcases afterSlots with _ | ⟨head, recordFrames⟩
              · simp [ha, hs] at h
              cases head with
              | separator =>
                  simp [ha, hs] at h
                  unfold decodeGNTail? at h
                  cases hr : parseGNRecords .cursor slots recordFrames with
                  | none => simp [hr] at h
                  | some result =>
                      rcases result with ⟨fields, tail⟩
                      by_cases ht : tail = gnCanonicalTail
                      · simp [hr, ht] at h
                        cases hg : gnGatesOfFields? inputs.length fields with
                        | none => simp [gnProgramOf?, hg] at h
                        | some gates =>
                            simp [gnProgramOf?, hg] at h
                            subst r
                            obtain ⟨hlen, hrecords⟩ := parseGNRecords_eq_some hr
                            have hfields := gnGatesOfFields?_eq_some hg
                            have hassign := parseGNAssign_exact originalRest
                            rw [ha] at hassign
                            have hslots := parseGNSlots_exact afterInputs
                            rw [hs] at hslots
                            have hslotCount : slots = gates.length := by
                              rw [← hlen, hfields]
                              simp
                            calc
                              G1Frame.bof :: originalRest = .bof ::
                                  (inputs.map .data ++ afterInputs) := by rw [hassign]
                              _ = .bof :: (inputs.map .data ++
                                  (gnSlotFrames slots ++ .separator :: recordFrames)) := by
                                    rw [hslots]
                              _ = encodeGNFrames
                                  ⟨inputs, ⟨gates⟩⟩ := by
                                    rw [hslotCount, hrecords, ht, hfields]
                                    simp [encodeGNFrames, gnAssignFrames,
                                      gnRecordsFrames, gnCanonicalTail,
                                      List.append_assoc]
                      · simp [hr, ht] at h
              | data b | output b => cases b <;> simp [ha, hs] at h
              | blank | bof | tag | index | cursor | finish | argSep | spent =>
                  simp [ha, hs] at h
  | data b | output b => cases b <;> simp [decodeGNFrameList?] at h
  | blank | tag | index | separator | cursor | finish | argSep | spent =>
      simp [decodeGNFrameList?] at h

theorem decodeGNFrameList?_iff (fs : List G1Frame) (r : GNProgram) :
    decodeGNFrameList? fs = some r ↔ fs = encodeGNFrames r := by
  constructor
  · exact decodeGNFrameList?_eq_some
  · rintro rfl
    exact decodeGNFrameList?_encodeGNFrames r

@[simp] theorem decodeGN?_encodeGN (r : GNProgram) :
    decodeGN? (encodeGN r) = some r := by
  simp [decodeGN?, encodeGN]

private theorem decodeG1Frame?_eq_some_gn {bits : List Bool} {f : G1Frame}
    (h : decodeG1Frame? bits = some f) : bits = f.bits := by
  rcases bits with _ | ⟨a, bits⟩
  · simp [decodeG1Frame?] at h
  rcases bits with _ | ⟨b, bits⟩
  · simp [decodeG1Frame?] at h
  rcases bits with _ | ⟨c, bits⟩
  · simp [decodeG1Frame?] at h
  rcases bits with _ | ⟨d, bits⟩
  · simp [decodeG1Frame?] at h
  rcases bits with _ | ⟨e, rest⟩
  · cases a <;> cases b <;> cases c <;> cases d <;>
      simp [decodeG1Frame?] at h <;> subst f <;> rfl
  · simp [decodeG1Frame?] at h

private theorem decodeG1Frames?_eq_some_gn {bits : List Bool}
    {fs : List G1Frame} (h : decodeG1Frames? bits = some fs) :
    bits = fs.flatMap G1Frame.bits := by
  match bits with
  | [] => simp [decodeG1Frames?] at h; subst fs; rfl
  | [_] => simp [decodeG1Frames?] at h
  | [_, _] => simp [decodeG1Frames?] at h
  | [_, _, _] => simp [decodeG1Frames?] at h
  | a :: b :: c :: d :: rest =>
      simp only [decodeG1Frames?] at h
      cases hf : decodeG1Frame? [a, b, c, d] with
      | none => simp [hf] at h
      | some frame =>
          cases hrs : decodeG1Frames? rest with
          | none => simp [hf, hrs] at h
          | some tail =>
              simp [hf, hrs] at h
              subst fs
              rw [decodeG1Frames?_eq_some_gn hrs]
              simp only [List.flatMap_cons]
              rw [← decodeG1Frame?_eq_some_gn hf]
              rfl

/-- A successful physical parse determines the entire canonical bit image. -/
theorem decodeGN?_eq_some {bits : List Bool} {r : GNProgram}
    (h : decodeGN? bits = some r) : bits = encodeGN r := by
  unfold decodeGN? at h
  cases hf : decodeG1Frames? bits with
  | none => simp [hf] at h
  | some fs =>
      simp [hf] at h
      rw [decodeG1Frames?_eq_some_gn hf, decodeGNFrameList?_eq_some h]
      rfl

theorem decodeGN?_iff (bits : List Bool) (r : GNProgram) :
    decodeGN? bits = some r ↔ bits = encodeGN r := by
  constructor
  · exact decodeGN?_eq_some
  · rintro rfl
    exact decodeGN?_encodeGN r

theorem encodeGN_injective : Function.Injective encodeGN := by
  intro r s h
  have := congrArg decodeGN? h
  simpa using this

private theorem decodeG1Frames?_append_none (pre : List G1Frame) {rest : List Bool}
    (h : decodeG1Frames? rest = none) :
    decodeG1Frames? (pre.flatMap G1Frame.bits ++ rest) = none := by
  induction pre with
  | nil => simpa using h
  | cons f pre ih =>
      cases f with
      | data b | output b =>
          cases b <;> simp [decodeG1Frames?, decodeG1Frame?, G1Frame.bits, ih]
      | blank | bof | tag | index | separator | cursor | finish | argSep | spent =>
          simp [decodeG1Frames?, decodeG1Frame?, G1Frame.bits, ih]

/-- Any rejected four-bit code at an aligned frame boundary rejects the whole
physical GN parse, independently of its aligned prefix and suffix. -/
theorem decodeGN?_reserved_aligned (pre : List G1Frame) {b0 b1 b2 b3 : Bool}
    (hbad : decodeG1Frame? [b0, b1, b2, b3] = none) (rest : List Bool) :
    decodeGN?
        (pre.flatMap G1Frame.bits ++ b0 :: b1 :: b2 :: b3 :: rest) = none := by
  have hframes : decodeG1Frames?
      (pre.flatMap G1Frame.bits ++ b0 :: b1 :: b2 :: b3 :: rest) = none := by
    apply decodeG1Frames?_append_none pre
    simp [decodeG1Frames?, hbad]
  simp [decodeGN?, hframes]

/-! ## Pure sequential semantics -/

theorem gnFieldEval_gnGateFields {n : Nat} (inputs : List Bool)
    (hinputs : inputs.length = n) (gateVals : List Bool) (g : SLGate n) :
    gnFieldEval (gnGateFields g) (inputs ++ gateVals) =
      g.compute (fun i => inputs[i.val]'(by omega)) gateVals := by
  subst n
  cases g with
  | input i =>
      simp [gnFieldEval, gnFieldRequest, gnGateFields, G1Request.spec,
        SLGate.compute, List.getElem?_append_left i.isLt]
  | const b => cases b <;> rfl
  | notGate k => simp [gnFieldEval, gnFieldRequest, gnGateFields,
      G1Request.spec, SLGate.compute, List.getElem?_append_right]
  | andGate k l =>
      simp [gnFieldEval, gnFieldRequest, gnGateFields, G1Request.spec,
        SLGate.compute, List.getElem?_append_right]
      cases gateVals[k]? <;> cases gateVals[l]? <;> rfl
  | orGate k l =>
      simp [gnFieldEval, gnFieldRequest, gnGateFields, G1Request.spec,
        SLGate.compute, List.getElem?_append_right]
      cases gateVals[k]? <;> cases gateVals[l]? <;> rfl

/-- Evaluate serialized fields left-to-right, appending each result to the
single current value environment. -/
def evalGNFields : List GNField → List Bool → Option (List Bool)
  | [], vals => some vals
  | f :: rest, vals => do
      let value ← gnFieldEval f vals
      evalGNFields rest (vals ++ [value])

theorem evalGNFields_gates {n : Nat} (inputs : List Bool)
    (hinputs : inputs.length = n) (gates : List (SLGate n))
    (gateVals : List Bool) :
    evalGNFields (gates.map gnGateFields) (inputs ++ gateVals) =
      (SLProgram.evalAux (fun i => inputs[i.val]'(by omega)) gates gateVals).map
        (fun out => inputs ++ out) := by
  induction gates generalizing gateVals with
  | nil => simp [evalGNFields, SLProgram.evalAux]
  | cons g gates ih =>
      simp only [List.map_cons, evalGNFields, SLProgram.evalAux_cons]
      rw [gnFieldEval_gnGateFields inputs hinputs gateVals g]
      cases g.compute (fun i => inputs[i.val]'(by omega)) gateVals with
      | none => simp
      | some value =>
          simp only [Option.bind_some]
          change evalGNFields (gates.map gnGateFields)
              ((inputs ++ gateVals) ++ [value]) =
            (SLProgram.evalAux (fun i => inputs[i.val]'(by omega)) gates
              (gateVals ++ [value])).map (fun out => inputs ++ out)
          rw [List.append_assoc, ih]

def evalGNProgramAll (r : GNProgram) : Option (List Bool) :=
  evalGNFields (r.program.gates.map gnGateFields) r.inputs

/-- The environment evaluator retains the input prefix and appends exactly the
same gate-result list produced by `SLProgram.evalAll`. -/
theorem evalGNProgramAll_eq_SLProgram_evalAll (r : GNProgram) :
    evalGNProgramAll r =
      (r.program.evalAll (fun i => r.inputs[i.val]'(by omega))).map
        (fun gateVals => r.inputs ++ gateVals) := by
  rw [evalGNProgramAll]
  simpa using evalGNFields_gates r.inputs rfl r.program.gates []

def evalGNProgram (r : GNProgram) : Option Bool :=
  (evalGNProgramAll r).bind
    (fun vals => (vals.drop r.inputs.length).getLast?)

/-- Final-result semantics agrees exactly with the existing straight-line
program evaluator, including `none` for the empty gate list. -/
theorem evalGNProgram_eq_SLProgram_eval (r : GNProgram) :
    evalGNProgram r = r.program.eval (fun i => r.inputs[i.val]'(by omega)) := by
  rw [evalGNProgram, evalGNProgramAll_eq_SLProgram_evalAll]
  unfold SLProgram.eval
  cases r.program.evalAll (fun i => r.inputs[i.val]'(by omega)) with
  | none => simp
  | some gateVals => simp

theorem evalGNFields_length {fields : List GNField} {vals out : List Bool}
    (h : evalGNFields fields vals = some out) :
    out.length = vals.length + fields.length := by
  induction fields generalizing vals out with
  | nil => simp [evalGNFields] at h; subst out; simp
  | cons f fs ih =>
      simp only [evalGNFields] at h
      cases hf : gnFieldEval f vals with
      | none => simp [hf] at h
      | some value =>
          simp [hf] at h
          calc
            out.length = (vals ++ [value]).length + fs.length := ih h
            _ = vals.length + (f :: fs).length := by simp; omega

end Pnp3.Internal.PsubsetPpoly.TM
