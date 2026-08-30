import Complexity.TMVerifier.TuringToolkit.GateNEncoding

/-!
# GN-2: pure multi-gate tape state

**Progress classification: Infrastructure.**  This file gives the canonical
partially committed GN word, its list-backed views, and one pure commit.  It
defines no machine mode, transition, execution, relocation, clock, or
acceptance theorem.  In particular it does not reduce either pnp4 lower-bound
source obligation.

For `r : GNProgram`, put `n = r.inputs.length`, `m = r.program.gates.length`,
`S = gnRecordsLength r`, and `j = prior.length`.  At every reachable stage
`j <= m` the frame word is

```text
bof · data(inputs) · data(prior) · output(false)^(m-j) · separator
    · recordsAt(j) · separator · output(finalAt(j)) · finish.
```

Record bodies never change.  Records below `j` have marker `spent`, record
`j` has marker `cursor`, and later records have marker `bof`.  `finalAt(j)` is
false before the terminal stage and the last committed result at `j = m`.
Thus a commit changes exactly slot `j`, the current/next record markers, and,
only on the last commit, the final-output frame.  All positions are related to
the general GN-1 offsets; no width-specific offset arithmetic is introduced.

The implicit physical tape is represented purely by `gnTapeCell`: cells past
the finite word return false.  The work-word theorem is the tight word-length
comparison `W + 16 <= N`.  It is not a relocation or a claim about a machine's
finite tape budget, and `W + 17 <= N` is false at the named boundary example.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Encoding

/-! ## Small list facts -/

theorem gnIndex_lt_length {α : Type _} {l : List α} {a : α} {j : Nat}
    (h : l[j]? = some a) : j < l.length := by
  by_contra hn
  rw [List.getElem?_eq_none_iff.mpr (by omega)] at h
  exact Option.noConfusion h

theorem gnNat_le_sum {l : List Nat} {a : Nat} (h : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons b bs ih =>
      rw [List.sum_cons]
      rcases List.mem_cons.mp h with rfl | h
      · omega
      · have := ih h; omega

/-! ## Record markers and immutable record bodies -/

/-- A record region whose every record has the same marker. -/
def gnUniformRecordsFrames {n : Nat} (marker : G1Frame) :
    List (SLGate n) → List G1Frame
  | [] => []
  | g :: gs => gnRecordFrames marker g ++ gnUniformRecordsFrames marker gs

@[simp] theorem gnUniformRecordsFrames_nil {n : Nat} (marker : G1Frame) :
    gnUniformRecordsFrames marker ([] : List (SLGate n)) = [] := rfl

@[simp] theorem gnUniformRecordsFrames_length {n : Nat} (marker : G1Frame)
    (gates : List (SLGate n)) :
    (gnUniformRecordsFrames marker gates).length =
      (gates.map (gnRecordSize ∘ gnGateFields)).sum := by
  induction gates with
  | nil => rfl
  | cons g gs ih =>
      simp [gnUniformRecordsFrames, gnRecordFrames, ih, Function.comp_def]

theorem gnRecordsFrames_bof {n : Nat} (gates : List (SLGate n)) :
    gnRecordsFrames .bof gates = gnUniformRecordsFrames .bof gates := by
  induction gates with
  | nil => rfl
  | cons g gs ih =>
      change g1RecordFrames .bof (gnGateFields g) ++
          gnFieldRecordsFrames .bof (gs.map gnGateFields) =
        gnRecordFrames .bof g ++ gnUniformRecordsFrames .bof gs
      rw [show g1RecordFrames .bof (gnGateFields g) = gnRecordFrames .bof g from rfl]
      rw [show gnFieldRecordsFrames .bof (gs.map gnGateFields) =
        gnRecordsFrames .bof gs from rfl, ih]

/-- Record region at controller index `j`. -/
def gnRecordsAtFrames {n : Nat} (j : Nat) :
    List (SLGate n) → List G1Frame
  | [] => []
  | g :: gs => match j with
    | 0 => gnRecordFrames .cursor g ++ gnRecordsFrames .bof gs
    | k + 1 => gnRecordFrames .spent g ++ gnRecordsAtFrames k gs

@[simp] theorem gnRecordsAtFrames_nil {n : Nat} (j : Nat) :
    gnRecordsAtFrames j ([] : List (SLGate n)) = [] := by cases j <;> rfl

@[simp] theorem gnRecordsAtFrames_zero {n : Nat} (gates : List (SLGate n)) :
    gnRecordsAtFrames 0 gates = gnRecordsFrames .cursor gates := by
  cases gates <;> rfl

@[simp] theorem gnRecordsAtFrames_length {n : Nat} (j : Nat)
    (gates : List (SLGate n)) :
    (gnRecordsAtFrames j gates).length =
      (gates.map (gnRecordSize ∘ gnGateFields)).sum := by
  induction gates generalizing j with
  | nil => rw [gnRecordsAtFrames_nil]; rfl
  | cons g gs ih =>
      cases j <;>
        simp [gnRecordsAtFrames, gnRecordsFrames_length, ih, gnRecordFrames,
          Function.comp_def]

/-- The exact record split at the selected gate. -/
theorem gnRecordsAtFrames_split {n : Nat} {j : Nat}
    {gates : List (SLGate n)} {g : SLGate n} (hg : gates[j]? = some g) :
    gnRecordsAtFrames j gates =
      gnUniformRecordsFrames .spent (gates.take j) ++
        gnRecordFrames .cursor g ++
          gnUniformRecordsFrames .bof (gates.drop (j + 1)) := by
  induction gates generalizing j with
  | nil => simp at hg
  | cons g' gs ih =>
      cases j with
      | zero =>
          have hgg : g' = g := by simpa using hg
          subst g'
          simp [gnRecordsAtFrames, gnRecordsFrames_bof]
      | succ k =>
          have hgs : gs[k]? = some g := by simpa using hg
          rw [gnRecordsAtFrames, ih hgs]
          simp [gnUniformRecordsFrames, List.append_assoc]

/-- Advancing one index changes the selected marker to `spent` and then uses
the stage-zero marker convention on the untouched suffix. -/
theorem gnRecordsAtFrames_succ_split {n : Nat} {j : Nat}
    {gates : List (SLGate n)} {g : SLGate n} (hg : gates[j]? = some g) :
    gnRecordsAtFrames (j + 1) gates =
      gnUniformRecordsFrames .spent (gates.take j) ++
        gnRecordFrames .spent g ++ gnRecordsAtFrames 0 (gates.drop (j + 1)) := by
  induction gates generalizing j with
  | nil => simp at hg
  | cons g' gs ih =>
      cases j with
      | zero =>
          have hgg : g' = g := by simpa using hg
          subst g'
          simp [gnRecordsAtFrames]
      | succ k =>
          have hgs : gs[k]? = some g := by simpa using hg
          simpa [gnRecordsAtFrames, gnUniformRecordsFrames, List.append_assoc]
            using ih hgs

/-- At and beyond the terminal index every record is spent. -/
theorem gnRecordsAtFrames_all_spent {n : Nat} {j : Nat}
    {gates : List (SLGate n)} (h : gates.length ≤ j) :
    gnRecordsAtFrames j gates = gnUniformRecordsFrames .spent gates := by
  induction gates generalizing j with
  | nil => rw [gnRecordsAtFrames_nil, gnUniformRecordsFrames_nil]
  | cons g gs ih =>
      cases j with
      | zero => simp at h
      | succ k =>
          have hk : gs.length ≤ k := by simpa using h
          simp [gnRecordsAtFrames, gnUniformRecordsFrames, ih hk]

private theorem gnRecordFrames_count_cursor_ne {n : Nat} (marker : G1Frame)
    (g : SLGate n) (h : marker ≠ .cursor) :
    (gnRecordFrames marker g).count .cursor = 0 := by
  rcases gnGateFields g with ⟨tag, a1, a2⟩
  simp [gnRecordFrames, g1RecordFrames, List.count_replicate, h]

private theorem gnRecordFrames_count_cursor {n : Nat} (g : SLGate n) :
    (gnRecordFrames .cursor g).count .cursor = 1 := by
  rcases gnGateFields g with ⟨tag, a1, a2⟩
  simp [gnRecordFrames, g1RecordFrames, List.count_replicate]

private theorem gnRecordsFrames_count_cursor_bof {n : Nat}
    (gates : List (SLGate n)) :
    (gnRecordsFrames .bof gates).count .cursor = 0 := by
  rw [gnRecordsFrames_bof]
  induction gates with
  | nil => rfl
  | cons g gs ih =>
      simp [gnUniformRecordsFrames, List.count_append,
        gnRecordFrames_count_cursor_ne .bof g (by decide), ih]

/-- Exactly one selected record exists before the terminal index, and none after. -/
theorem gnRecordsAtFrames_count_cursor {n : Nat} (j : Nat)
    (gates : List (SLGate n)) :
    (gnRecordsAtFrames j gates).count .cursor = if j < gates.length then 1 else 0 := by
  induction gates generalizing j with
  | nil => simp
  | cons g gs ih =>
      cases j with
      | zero =>
          simp [gnRecordsAtFrames, List.count_append, gnRecordFrames_count_cursor,
            gnRecordsFrames_count_cursor_bof]
      | succ k =>
          simp [gnRecordsAtFrames, List.count_append,
            gnRecordFrames_count_cursor_ne .spent g (by decide), ih]

private theorem gnRecordFrames_count_spent_ne {n : Nat} (marker : G1Frame)
    (g : SLGate n) (h : marker ≠ .spent) :
    (gnRecordFrames marker g).count .spent = 0 := by
  rcases gnGateFields g with ⟨tag, a1, a2⟩
  simp [gnRecordFrames, g1RecordFrames, List.count_replicate, h]

private theorem gnRecordFrames_count_spent {n : Nat} (g : SLGate n) :
    (gnRecordFrames .spent g).count .spent = 1 := by
  rcases gnGateFields g with ⟨tag, a1, a2⟩
  simp [gnRecordFrames, g1RecordFrames, List.count_replicate]

private theorem gnRecordsFrames_count_spent_bof {n : Nat}
    (gates : List (SLGate n)) : (gnRecordsFrames .bof gates).count .spent = 0 := by
  rw [gnRecordsFrames_bof]
  induction gates with
  | nil => rfl
  | cons g gs ih =>
      simp [gnUniformRecordsFrames, List.count_append,
        gnRecordFrames_count_spent_ne .bof g (by decide), ih]

/-- Exactly `min j m` record markers have been consumed at stage `j`. -/
theorem gnRecordsAtFrames_count_spent {n : Nat} (j : Nat)
    (gates : List (SLGate n)) :
    (gnRecordsAtFrames j gates).count .spent = min j gates.length := by
  induction gates generalizing j with
  | nil => simp
  | cons g gs ih =>
      cases j with
      | zero =>
          simp [gnRecordsAtFrames, List.count_append,
            gnRecordFrames_count_spent_ne .cursor g (by decide),
            gnRecordsFrames_count_spent_bof]
      | succ k =>
          simp [gnRecordsAtFrames, List.count_append, gnRecordFrames_count_spent, ih]
          omega

/-! ## Canonical stage word and GN-1 offsets -/

def gnCurrentValues (r : GNProgram) (prior : List Bool) : List Bool :=
  r.inputs ++ prior

/-- Structural reader for the maximal current-value `data` run after `bof`. -/
def gnReadCurrentValues (fs : List G1Frame) : List Bool :=
  match fs with
  | .bof :: rest => (parseGNAssign rest).1
  | _ => []

/-- The final output is written only at the terminal stage. -/
def gnFinalValue (r : GNProgram) (prior : List Bool) : Bool :=
  if prior.length = r.program.gates.length then prior.getLast?.getD false else false

def gnFinalTail (b : Bool) : List G1Frame :=
  [.separator, .output b, .finish]

/-- Canonical partially committed frame word. -/
def encodeGNAtFrames (r : GNProgram) (prior : List Bool) : List G1Frame :=
  [.bof] ++ (gnCurrentValues r prior).map .data ++
    gnSlotFrames (gnOutputSlotsLength r - prior.length) ++ [.separator] ++
    gnRecordsAtFrames prior.length r.program.gates ++
    gnFinalTail (gnFinalValue r prior)

def encodeGNAt (r : GNProgram) (prior : List Bool) : List Bool :=
  (encodeGNAtFrames r prior).flatMap G1Frame.bits

theorem encodeGNAtFrames_shape (r : GNProgram) (prior : List Bool) :
    encodeGNAtFrames r prior =
      [.bof] ++ r.inputs.map .data ++ prior.map .data ++
        gnSlotFrames (gnOutputSlotsLength r - prior.length) ++ [.separator] ++
        gnRecordsAtFrames prior.length r.program.gates ++
        gnFinalTail (gnFinalValue r prior) := by
  simp [encodeGNAtFrames, gnCurrentValues, List.map_append, List.append_assoc]

@[simp] theorem encodeGNAtFrames_zero (r : GNProgram) :
    encodeGNAtFrames r [] = encodeGNFrames r := by
  simp [encodeGNAtFrames, encodeGNFrames, gnCurrentValues, gnOutputSlotsLength,
    gnFinalValue, gnFinalTail, gnAssignFrames, List.append_assoc]

@[simp] theorem encodeGNAt_zero (r : GNProgram) : encodeGNAt r [] = encodeGN r := by
  rw [encodeGNAt, encodeGN, encodeGNAtFrames_zero]

/-- Exact frame count, expressed only through the GN-1 general extents. -/
theorem encodeGNAtFrames_length (r : GNProgram) (prior : List Bool)
    (h : prior.length ≤ gnOutputSlotsLength r) :
    (encodeGNAtFrames r prior).length = (encodeGNFrames r).length := by
  change prior.length ≤ r.program.gates.length at h
  rw [encodeGNAtFrames, encodeGNFrames_length]
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_map,
    gnCurrentValues, List.length_append, gnSlotFrames_length,
    gnRecordsAtFrames_length, gnFinalTail, gnOutputSlotsLength]
  omega

theorem encodeGNAt_length (r : GNProgram) (prior : List Bool)
    (h : prior.length ≤ gnOutputSlotsLength r) :
    (encodeGNAt r prior).length = (encodeGN r).length := by
  rw [encodeGNAt, encodeGN, G1Frame.flatMap_bits_length,
    G1Frame.flatMap_bits_length, encodeGNAtFrames_length r prior h]

/-- Exact region equation and extents, using all four GN-1 general offsets. -/
theorem encodeGNAt_regions (r : GNProgram) (prior : List Bool)
    (h : prior.length ≤ gnOutputSlotsLength r) :
    let inputs := G1Frame.bof :: r.inputs.map .data
    let slots := prior.map G1Frame.data ++
      gnSlotFrames (gnOutputSlotsLength r - prior.length)
    let records := gnRecordsAtFrames prior.length r.program.gates
    encodeGNAtFrames r prior = inputs ++ slots ++ [G1Frame.separator] ++ records ++
        [G1Frame.separator, .output (gnFinalValue r prior), .finish] ∧
      inputs.length = gnOutputSlotsStart r ∧
      slots.length = gnOutputSlotsLength r ∧
      (inputs ++ slots ++ [G1Frame.separator]).length = gnRecordsStart r ∧
      records.length = gnRecordsLength r ∧
      (inputs ++ slots ++ [G1Frame.separator] ++ records ++ [G1Frame.separator]).length =
        gnFinalOutputFrame r := by
  dsimp
  constructor
  · rw [encodeGNAtFrames_shape]
    simp [gnFinalTail, List.append_assoc]
  change prior.length ≤ r.program.gates.length at h
  simp [gnOutputSlotsStart, gnOutputSlotsLength, gnRecordsStart, gnRecordsLength,
    gnFinalOutputFrame]
  omega

private theorem gnParseAssign_append (vals : List Bool) (rest : List G1Frame)
    (h : ∀ b, rest.head? ≠ some (.data b)) :
    parseGNAssign (vals.map G1Frame.data ++ rest) = (vals, rest) := by
  induction vals with
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

private theorem gnSlots_head_ne_data (k : Nat) (rest : List G1Frame) (b : Bool) :
    (gnSlotFrames k ++ G1Frame.separator :: rest).head? ≠ some (.data b) := by
  cases k <;> simp [gnSlotFrames, List.replicate_succ]

/-- Reading the canonical stage word returns exactly inputs followed by commits. -/
theorem gnReadCurrentValues_exact (r : GNProgram) (prior : List Bool) :
    gnReadCurrentValues (encodeGNAtFrames r prior) = gnCurrentValues r prior := by
  rw [encodeGNAtFrames]
  simp only [gnReadCurrentValues, List.cons_append, List.nil_append]
  simp only [List.append_assoc]
  change (parseGNAssign ((gnCurrentValues r prior).map G1Frame.data ++
    (gnSlotFrames (gnOutputSlotsLength r - prior.length) ++ G1Frame.separator ::
      (gnRecordsAtFrames prior.length r.program.gates ++
        gnFinalTail (gnFinalValue r prior))))).1 = gnCurrentValues r prior
  rw [gnParseAssign_append _ _ (gnSlots_head_ne_data _ _)]

/-! ## Selected record, values, and one-gate work view -/

def gnSelectedGate? (r : GNProgram) (prior : List Bool) :
    Option (SLGate r.inputs.length) := r.program.gates[prior.length]?

def gnSelectedRecord? (r : GNProgram) (prior : List Bool) : Option (List G1Frame) :=
  (gnSelectedGate? r prior).map (gnRecordFrames .cursor)

def gnWorkRequest? (r : GNProgram) (prior : List Bool) : Option G1Request :=
  (gnSelectedGate? r prior).map
    (fun g => gnFieldRequest (gnGateFields g) (gnCurrentValues r prior))

def gnCurrentWork? (r : GNProgram) (prior : List Bool) : Option (List G1Frame) :=
  (gnWorkRequest? r prior).map encodeG1Frames

theorem gnSelectedGate?_exact {r : GNProgram} {prior : List Bool}
    {g : SLGate r.inputs.length} (hg : r.program.gates[prior.length]? = some g) :
    gnSelectedGate? r prior = some g := hg

theorem gnSelectedRecord?_exact {r : GNProgram} {prior : List Bool}
    {g : SLGate r.inputs.length} (hg : r.program.gates[prior.length]? = some g) :
    gnSelectedRecord? r prior = some (gnRecordFrames .cursor g) := by
  simp [gnSelectedRecord?, gnSelectedGate?, hg]

theorem gnSelectedRecord_decode {r : GNProgram} {prior : List Bool}
    {g : SLGate r.inputs.length} (hg : r.program.gates[prior.length]? = some g) :
    decodeGNRecordFrames? .cursor (gnRecordFrames .cursor g) = some (gnGateFields g) ∧
      prior.length < gnOutputSlotsLength r :=
  ⟨decodeGNRecordFrames?_encoded _ _, by
    simpa [gnOutputSlotsLength] using gnIndex_lt_length hg⟩

theorem gnSelectedRecord_embedded {r : GNProgram} {prior : List Bool}
    {g : SLGate r.inputs.length} (hg : r.program.gates[prior.length]? = some g) :
    gnRecordsAtFrames prior.length r.program.gates =
      gnUniformRecordsFrames .spent (r.program.gates.take prior.length) ++
        gnRecordFrames .cursor g ++
          gnUniformRecordsFrames .bof (r.program.gates.drop (prior.length + 1)) :=
  gnRecordsAtFrames_split hg

theorem gnSelected_index_bound {r : GNProgram} {prior : List Bool}
    {g : SLGate r.inputs.length} (hg : r.program.gates[prior.length]? = some g) :
    prior.length < gnOutputSlotsLength r := by
  simpa [gnOutputSlotsLength] using gnIndex_lt_length hg

@[simp] theorem gnCurrentValues_length (r : GNProgram) (prior : List Bool) :
    (gnCurrentValues r prior).length = r.inputs.length + prior.length := by
  simp [gnCurrentValues]

theorem gnCurrentWork?_exact {r : GNProgram} {prior : List Bool}
    {g : SLGate r.inputs.length} (hg : r.program.gates[prior.length]? = some g) :
    gnCurrentWork? r prior =
      some (encodeG1Frames
        (gnFieldRequest (gnGateFields g) (gnCurrentValues r prior))) := by
  simp [gnCurrentWork?, gnWorkRequest?, gnSelectedGate?, hg]

/-- The work request uses exactly GN-1's absolute-index semantics. -/
theorem gnWorkRequest_spec {r : GNProgram} {prior : List Bool}
    {g : SLGate r.inputs.length} (hg : r.program.gates[prior.length]? = some g) :
    (gnFieldRequest (gnGateFields g) (gnCurrentValues r prior)).spec =
        g.compute (fun i => r.inputs[i.val]'(by omega)) prior ∧
      prior.length < gnOutputSlotsLength r := by
  exact ⟨gnFieldEval_gnGateFields r.inputs rfl prior g, gnSelected_index_bound hg⟩

/-! ## Pure commit and exact frame effects -/

/-- A pure commit returns the next result list and its canonical frame word. -/
def gnCommit? (r : GNProgram) (prior : List Bool) (b : Bool) :
    Option (List Bool × List G1Frame) :=
  if prior.length < gnOutputSlotsLength r then
    some (prior ++ [b], encodeGNAtFrames r (prior ++ [b]))
  else none

theorem gnCommit?_exact (r : GNProgram) (prior : List Bool) (b : Bool)
    (h : prior.length < gnOutputSlotsLength r) :
    gnCommit? r prior b = some (prior ++ [b], encodeGNAtFrames r (prior ++ [b])) := by
  simp [gnCommit?, h]

theorem gnCommit?_terminal (r : GNProgram) (prior : List Bool) (b : Bool)
    (h : gnOutputSlotsLength r ≤ prior.length) : gnCommit? r prior b = none := by
  simp [gnCommit?, h]

/-- Exact next-frame equation: slot `j` becomes `data b`; no frame is inserted. -/
theorem encodeGNAt_commit_shape (r : GNProgram) (prior : List Bool) (b : Bool) :
    encodeGNAtFrames r (prior ++ [b]) =
      [.bof] ++ r.inputs.map .data ++ prior.map .data ++ [.data b] ++
        gnSlotFrames (gnOutputSlotsLength r - (prior.length + 1)) ++ [.separator] ++
        gnRecordsAtFrames (prior.length + 1) r.program.gates ++
        gnFinalTail (gnFinalValue r (prior ++ [b])) := by
  simp [encodeGNAtFrames_shape, List.append_assoc]

theorem encodeGNAt_commit_length (r : GNProgram) (prior : List Bool) (b : Bool)
    (h : prior.length < gnOutputSlotsLength r) :
    (encodeGNAtFrames r (prior ++ [b])).length = (encodeGNAtFrames r prior).length := by
  rw [encodeGNAtFrames_length r (prior ++ [b]) (by simp; omega),
    encodeGNAtFrames_length r prior (le_of_lt h)]

/-- Every commit preserves the immutable encoded-input prefix. -/
theorem encodeGNAt_commit_inputs (r : GNProgram) (prior : List Bool) (b : Bool) :
    ∃ beforeRest afterRest,
      encodeGNAtFrames r prior =
          (G1Frame.bof :: r.inputs.map .data) ++ beforeRest ∧
        encodeGNAtFrames r (prior ++ [b]) =
          (G1Frame.bof :: r.inputs.map .data) ++ afterRest := by
  refine ⟨prior.map .data ++
      gnSlotFrames (gnOutputSlotsLength r - prior.length) ++ [.separator] ++
      gnRecordsAtFrames prior.length r.program.gates ++
      gnFinalTail (gnFinalValue r prior),
    (prior ++ [b]).map .data ++
      gnSlotFrames (gnOutputSlotsLength r - (prior ++ [b]).length) ++ [.separator] ++
      gnRecordsAtFrames (prior ++ [b]).length r.program.gates ++
      gnFinalTail (gnFinalValue r (prior ++ [b])), ?_, ?_⟩ <;>
    rw [encodeGNAtFrames_shape] <;> simp [List.append_assoc]

/-- Record bodies are preserved: this equation exposes only the two marker changes. -/
theorem encodeGNAt_commit_records {r : GNProgram} {prior : List Bool} (b : Bool)
    {g : SLGate r.inputs.length} (hg : r.program.gates[prior.length]? = some g) :
    gnRecordsAtFrames prior.length r.program.gates =
        gnUniformRecordsFrames .spent (r.program.gates.take prior.length) ++
          gnRecordFrames .cursor g ++
            gnUniformRecordsFrames .bof (r.program.gates.drop (prior.length + 1)) ∧
      gnRecordsAtFrames (prior ++ [b]).length r.program.gates =
        gnUniformRecordsFrames .spent
            (r.program.gates.take prior.length) ++
          gnRecordFrames .spent g ++
            gnRecordsAtFrames 0 (r.program.gates.drop (prior.length + 1)) := by
  constructor
  · exact gnRecordsAtFrames_split hg
  · simpa using gnRecordsAtFrames_succ_split hg

theorem gnFinalValue_before_terminal (r : GNProgram) (prior : List Bool)
    (h : prior.length < gnOutputSlotsLength r) : gnFinalValue r prior = false := by
  have hne : prior.length ≠ r.program.gates.length := by
    simpa [gnOutputSlotsLength] using ne_of_lt h
  simp [gnFinalValue, hne]

/-- The last commit writes its result to the final-output frame. -/
theorem gnFinalValue_terminal_commit (r : GNProgram) (prior : List Bool) (b : Bool)
    (h : prior.length + 1 = gnOutputSlotsLength r) :
    gnFinalValue r (prior ++ [b]) = b := by
  have heq : (prior ++ [b]).length = r.program.gates.length := by
    simpa [gnOutputSlotsLength] using h
  simp [gnFinalValue, heq]

/-- A nonterminal commit leaves the final output false. -/
theorem gnFinalValue_nonterminal_commit (r : GNProgram) (prior : List Bool) (b : Bool)
    (h : prior.length + 1 < gnOutputSlotsLength r) :
    gnFinalValue r (prior ++ [b]) = false := by
  have hne : prior.length + 1 ≠ r.program.gates.length := by
    have hlt : prior.length + 1 < r.program.gates.length := by
      simpa [gnOutputSlotsLength] using h
    exact ne_of_lt hlt
  simp [gnFinalValue, hne]

/-! ## State invariant, counts, and parser preservation -/

def GateNTapeState (r : GNProgram) (prior : List Bool) (fs : List G1Frame) : Prop :=
  prior.length ≤ gnOutputSlotsLength r ∧ fs = encodeGNAtFrames r prior

theorem GateNTapeState.initial (r : GNProgram) :
    GateNTapeState r [] (encodeGNFrames r) := by
  exact ⟨by simp [gnOutputSlotsLength], (encodeGNAtFrames_zero r).symm⟩

theorem GateNTapeState.step {r : GNProgram} {prior : List Bool}
    {fs : List G1Frame} (h : GateNTapeState r prior fs) (b : Bool)
    (hlt : prior.length < gnOutputSlotsLength r) :
    gnCommit? r prior b = some (prior ++ [b], encodeGNAtFrames r (prior ++ [b])) ∧
      GateNTapeState r (prior ++ [b]) (encodeGNAtFrames r (prior ++ [b])) ∧
      (encodeGNAtFrames r (prior ++ [b])).length = fs.length := by
  refine ⟨gnCommit?_exact r prior b hlt, ⟨by simp; omega, rfl⟩, ?_⟩
  rw [h.2]
  exact encodeGNAt_commit_length r prior b hlt

theorem GateNTapeState.cursor_count {r : GNProgram} {prior : List Bool}
    {fs : List G1Frame} (h : GateNTapeState r prior fs) :
    fs = encodeGNAtFrames r prior ∧
      (gnRecordsAtFrames prior.length r.program.gates).count .cursor =
        if prior.length < gnOutputSlotsLength r then 1 else 0 := by
  refine ⟨h.2, ?_⟩
  simpa [gnOutputSlotsLength] using gnRecordsAtFrames_count_cursor
    prior.length r.program.gates

theorem GateNTapeState.initial_parser (r : GNProgram) :
    decodeGNFrameList? (encodeGNAtFrames r []) = some r := by
  rw [encodeGNAtFrames_zero]
  exact decodeGNFrameList?_encodeGNFrames r

/-! ## Pure blank suffix and tight work-word capacity -/

/-- Finite list presentation with an explicit caller-chosen blank suffix. -/
def gnTapeFrames (r : GNProgram) (prior : List Bool) (scratchFrames : Nat) :
    List G1Frame := encodeGNAtFrames r prior ++ List.replicate scratchFrames .blank

theorem gnTapeFrames_scratch (r : GNProgram) (prior : List Bool)
    (scratchFrames : Nat) :
    (gnTapeFrames r prior scratchFrames).drop (encodeGNAtFrames r prior).length =
      List.replicate scratchFrames .blank := by
  simp [gnTapeFrames]

/-- Infinite all-false extension of the finite cell word, represented as a function. -/
def gnTapeCell (r : GNProgram) (prior : List Bool) (i : Nat) : Bool :=
  (encodeGNAt r prior)[i]?.getD false

theorem gnTapeCell_scratch_blank (r : GNProgram) (prior : List Bool) {i : Nat}
    (h : (encodeGNAt r prior).length ≤ i) : gnTapeCell r prior i = false := by
  simp [gnTapeCell, List.getElem?_eq_none h]

theorem gnWorkWord_length (r : GNProgram) (prior : List Bool)
    (g : SLGate r.inputs.length) :
    (encodeG1 (gnFieldRequest (gnGateFields g) (gnCurrentValues r prior))).length =
      4 * (gnRecordSize (gnGateFields g) + r.inputs.length + prior.length + 2) := by
  rw [encodeG1_length]
  simp [gnFieldRequest, gnCurrentValues, gnRecordSize]
  omega

theorem encodeGN_length_eq (r : GNProgram) :
    (encodeGN r).length =
      4 * (r.inputs.length + gnOutputSlotsLength r + gnRecordsLength r + 5) := by
  rw [encodeGN_length, encodeGNFrames_length]
  simp [gnOutputSlotsLength, gnRecordsLength]

theorem gnRecordSize_le_recordsLength {r : GNProgram} {prior : List Bool}
    {g : SLGate r.inputs.length} (hg : r.program.gates[prior.length]? = some g) :
    gnRecordSize (gnGateFields g) ≤ gnRecordsLength r := by
  apply gnNat_le_sum
  exact List.mem_map.mpr ⟨g, List.mem_of_getElem? hg, rfl⟩

/-- Tight pure capacity: the current one-gate word is at least 16 cells shorter. -/
theorem gnWorkWord_add_sixteen_le_input {r : GNProgram} {prior : List Bool}
    {g : SLGate r.inputs.length} (hg : r.program.gates[prior.length]? = some g) :
    (encodeG1 (gnFieldRequest (gnGateFields g) (gnCurrentValues r prior))).length + 16 ≤
      (encodeGN r).length := by
  rw [gnWorkWord_length, encodeGN_length_eq]
  have hsize := gnRecordSize_le_recordsLength hg
  have hindex := gnSelected_index_bound hg
  omega

end Pnp3.Internal.PsubsetPpoly.TM
