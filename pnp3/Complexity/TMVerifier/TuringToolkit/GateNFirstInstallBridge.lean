import Complexity.TMVerifier.TuringToolkit.GateNFixedDelegateRelocation

/-!
# GN-E2-0 pure physical first-install bridge (2026-09-01)

**Progress classification: infrastructure, not P-vs-NP mainline progress.**

This module closes the representation gap between the pure `GateNTapeState`
word and the already-proved `gnGateShiftConfig` target.  It identifies the
E1b scratch-entry tape with the stage-zero physical tape, selects the literal
first-gate request, proves its capacity and physical room, and gives a complete
configuration equality for the installed physical endpoint.

There is no `gnTransition` or `GNState` change here, and no execution claim.
In particular this module adds no installer, shuttle, runtime marker codec,
scratch-entry transition, result, commit, clock-adequacy, multigate loop,
verdict, or acceptance theorem.  Later E2-1 work chooses `output true` as the
temporary source marker and the first blank as frontier; this pure bridge does
not itself introduce either runtime row.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan
open Encoding

/-! ## Pure stage words as physical GNM tapes -/

/-- The exact list-backed physical tape for one pure GN stage. -/
def gnStageTape (r : GNProgram) (prior : List Bool) :
    Fin (GNM.tapeLength (encodeGN r).length) → Bool :=
  frameListTape (encodeGNAt r prior)

/-- A physical tape represents precisely the fitted pure GN stage. -/
def GateNPhysicalTapeState (r : GNProgram) (prior : List Bool)
    (tape : Fin (GNM.tapeLength (encodeGN r).length) → Bool) : Prop :=
  prior.length ≤ gnOutputSlotsLength r ∧ tape = gnStageTape r prior

/-- A fitted stage word has exactly the original physical GN word length. -/
theorem gnStageWord_length (r : GNProgram) (prior : List Bool)
    (hfit : prior.length ≤ gnOutputSlotsLength r) :
    (encodeGNAt r prior).length = (encodeGN r).length :=
  encodeGNAt_length r prior hfit

/-- Stage zero is exactly the real GN initial tape. -/
theorem gnStageTape_zero (r : GNProgram) :
    gnStageTape r [] = (GNM.initialConfig (gnPoint (encodeGN r))).tape := by
  rw [gnStageTape, encodeGNAt_zero, gnInitialTape_eq_frameListTape]

/-- Every physical cell inside the stage word is the corresponding list bit. -/
theorem gnStageTape_cell (r : GNProgram) (prior : List Bool)
    (i : Fin (GNM.tapeLength (encodeGN r).length))
    (hi : i.val < (encodeGNAt r prior).length) :
    gnStageTape r prior i = (encodeGNAt r prior)[i.val] := by
  simp [gnStageTape, frameListTape, List.getD, hi]

/-- Every physical cell outside the finite stage word is blank. -/
theorem gnStageTape_outside_blank (r : GNProgram) (prior : List Bool)
    (i : Fin (GNM.tapeLength (encodeGN r).length))
    (hi : (encodeGNAt r prior).length ≤ i.val) :
    gnStageTape r prior i = false := by
  simp [gnStageTape, frameListTape, List.getD, List.getElem?_eq_none hi]

/-- `GateNTapeState` is reused verbatim: flattening its exact frame word gives
the exact physical stage tape, without a second semantic invariant. -/
theorem GateNTapeState.physical_tape_eq {r : GNProgram} {prior : List Bool}
    {fs : List G1Frame} (h : GateNTapeState r prior fs) :
    frameListTape (L := GNM.tapeLength (encodeGN r).length)
        (fs.flatMap G1Frame.bits) = gnStageTape r prior := by
  rw [h.2]
  rfl

/-- The exact pure state therefore induces the exact physical state. -/
theorem GateNTapeState.toPhysical {r : GNProgram} {prior : List Bool}
    {fs : List G1Frame} (h : GateNTapeState r prior fs) :
    GateNPhysicalTapeState r prior
      (frameListTape (L := GNM.tapeLength (encodeGN r).length)
        (fs.flatMap G1Frame.bits)) :=
  ⟨h.1, h.physical_tape_eq⟩

/-- E1b ends at the exact stage-zero physical boundary: fixed scratch-entry
control, head `N`, and the stage-zero list-backed tape. -/
theorem gnScratchEntryConfig_stage_zero (r : GNProgram) :
    (gnScratchEntryConfig r).state = gnScratchEntryQ ∧
      ((gnScratchEntryConfig r).head : Nat) = (encodeGN r).length ∧
      (gnScratchEntryConfig r).tape = gnStageTape r [] := by
  refine ⟨rfl, rfl, ?_⟩
  exact (gnStageTape_zero r).symm

/-- The tape projection of the E1b endpoint satisfies the exact physical
stage-state predicate, including the stage-zero fit fact. -/
theorem gnScratchEntryConfig_physical_state (r : GNProgram) :
    GateNPhysicalTapeState r [] (gnScratchEntryConfig r).tape := by
  refine ⟨by simp [gnOutputSlotsLength], ?_⟩
  exact (gnScratchEntryConfig_stage_zero r).2.2

/-! ## Exact first-gate request and record boundary -/

/-- The canonical G1 request determined by the first typed GN gate. -/
def gnFirstRequest (r : GNProgram) (g : SLGate r.inputs.length) : G1Request :=
  gnFieldRequest (gnGateFields g) r.inputs

@[simp] theorem gnCurrentValues_zero (r : GNProgram) :
    gnCurrentValues r [] = r.inputs := by
  simp [gnCurrentValues]

/-- Selection at stage zero returns exactly the canonical first request. -/
theorem gnWorkRequest?_zero {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) :
    gnWorkRequest? r [] = some (gnFirstRequest r g) := by
  simp [gnWorkRequest?, gnSelectedGate?, gnFirstRequest, hg]

/-- Every request obtained from a typed first gate obeys the G1 canonical
unused-field convention. -/
theorem gnFirstRequest_canonical (r : GNProgram)
    (g : SLGate r.inputs.length) : (gnFirstRequest r g).Canonical := by
  rw [G1Request.canonical_iff]
  cases g with
  | input i => simp [gnFirstRequest, gnFieldRequest, gnGateFields, G1Tag.arity]
  | const b => cases b <;>
      simp [gnFirstRequest, gnFieldRequest, gnGateFields, G1Tag.arity]
  | notGate k => simp [gnFirstRequest, gnFieldRequest, gnGateFields, G1Tag.arity]
  | andGate k l => simp [gnFirstRequest, gnFieldRequest, gnGateFields, G1Tag.arity]
  | orGate k l => simp [gnFirstRequest, gnFieldRequest, gnGateFields, G1Tag.arity]

/-- Exact physical width of the first request. -/
theorem gnFirstRequest_width (r : GNProgram) (g : SLGate r.inputs.length) :
    (encodeG1 (gnFirstRequest r g)).length =
      4 * (gnRecordSize (gnGateFields g) + r.inputs.length + 2) := by
  simpa [gnFirstRequest, gnCurrentValues] using gnWorkWord_length r [] g

/-- The existing tight `W+16≤N` theorem specialized to the selected first
request. -/
theorem gnFirstRequest_add_sixteen_le {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    (encodeG1 (gnFirstRequest r g)).length + 16 ≤ (encodeGN r).length := by
  simpa [gnFirstRequest, gnCurrentValues] using
    (gnWorkWord_add_sixteen_le_input (r := r) (prior := []) hg)

/-- The selected first request has room for its exact `W+5` physical footprint
at base `N`. -/
theorem gnFirstRequest_room {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) :
    (encodeGN r).length + gnLocalSpan (encodeG1 (gnFirstRequest r g)).length ≤
      GNM.tapeLength (encodeGN r).length :=
  gnScratch_room_of_add_sixteen (gnFirstRequest_add_sixteen_le hg)

/-- Stage zero splits exactly around the unique cursor-marked first record. -/
theorem encodeGNAtFrames_zero_first_split {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    encodeGNAtFrames r [] =
      [.bof] ++ r.inputs.map .data ++ gnSlotFrames (gnOutputSlotsLength r) ++
        [.separator] ++ gnRecordFrames .cursor g ++
        gnUniformRecordsFrames .bof (r.program.gates.drop 1) ++
        gnFinalTail false := by
  rw [encodeGNAtFrames_shape]
  have hrecords := gnSelectedRecord_embedded (r := r) (prior := []) hg
  simp only [List.length_nil, List.take_zero, gnUniformRecordsFrames_nil,
    List.nil_append, Nat.zero_add] at hrecords
  simp only [List.map_nil, List.length_nil, Nat.sub_zero]
  rw [hrecords]
  simp [gnFinalValue, List.append_assoc]

/-- The selected stage-zero record cursor is unique. -/
theorem encodeGNAtFrames_zero_cursor_unique {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    (gnRecordsAtFrames 0 r.program.gates).count .cursor = 1 := by
  have hnonempty : 0 < r.program.gates.length := gnIndex_lt_length hg
  rw [gnRecordsAtFrames_count_cursor]
  simp [hnonempty]

/-- Stage zero contains no consumed-record marker. -/
theorem encodeGNAtFrames_zero_no_spent (r : GNProgram) :
    (gnRecordsAtFrames 0 r.program.gates).count .spent = 0 := by
  simpa using gnRecordsAtFrames_count_spent 0 r.program.gates

/-- A canonical G1 request word contains neither machine-internal marker.
This pins encoder output only; it introduces no runtime marker code. -/
theorem encodeG1Frames_first_no_internal_markers (r : GNProgram)
    (g : SLGate r.inputs.length) :
    (encodeG1Frames (gnFirstRequest r g)).count .cursor = 0 ∧
      (encodeG1Frames (gnFirstRequest r g)).count .spent = 0 := by
  have hcursor : (r.inputs.map G1Frame.data).count .cursor = 0 := by
    induction r.inputs with
    | nil => rfl
    | cons b bs ih => cases b <;> simp [ih]
  have hspent : (r.inputs.map G1Frame.data).count .spent = 0 := by
    induction r.inputs with
    | nil => rfl
    | cons b bs ih => cases b <;> simp [ih]
  simp [encodeG1Frames, gnFirstRequest, gnFieldRequest, hcursor, hspent,
    List.count_replicate]

/-! ## Complete physical first-install endpoint -/

/-- The already-proved shifted target specialized to the first request,
physical base `N`, and the real GN ambient tape. -/
def gnFirstInstalledConfig (r : GNProgram) (g : SLGate r.inputs.length)
    (hg : r.program.gates[0]? = some g) :
    Configuration (M := GNM) (encodeGN r).length :=
  gnGateShiftConfig (N := (encodeGN r).length) (base := (encodeGN r).length)
    (gnFirstRequest r g)
    (GNM.initialConfig (gnPoint (encodeGN r))).tape
    (gnFirstRequest_room hg)

/-- The explicit aligned configuration represented by the physical install:
delegated G1 start, head `N`, and the concatenated list-backed GN/G1 tape. -/
def gnFirstInstalledPhysicalConfig (r : GNProgram)
    (g : SLGate r.inputs.length) :
    Configuration (M := GNM) (encodeGN r).length where
  state := gnEmbed (G1M.initialConfig
    (g1Point (encodeG1 (gnFirstRequest r g)))).state
  head := ⟨(encodeGN r).length, by
    simp [TM.tapeLength, gnCS, gnClock, g1Clock]
    omega⟩
  tape := frameListTape (encodeGN r ++ encodeG1 (gnFirstRequest r g))

private theorem g1InitialTape_eq_frameListTape (bits : List Bool) :
    (G1M.initialConfig (g1Point bits)).tape = frameListTape bits := by
  funext i
  simp only [TM.initialConfig, g1Point, frameListTape]
  split <;> rename_i h
  · simp [List.getD, h]
  · have hi : bits.length ≤ i.val := Nat.le_of_not_gt h
    simp [List.getD, h]

private theorem gnFirstOverlay_eq_concat (r : GNProgram)
    (g : SLGate r.inputs.length)
    (hroom : (encodeGN r).length +
      gnLocalSpan (encodeG1 (gnFirstRequest r g)).length ≤
        GNM.tapeLength (encodeGN r).length) :
    gnOverlayTape GNM (encodeGN r).length hroom
        (G1M.initialConfig (g1Point (encodeG1 (gnFirstRequest r g))))
        (GNM.initialConfig (gnPoint (encodeGN r))).tape =
      frameListTape (encodeGN r ++ encodeG1 (gnFirstRequest r g)) := by
  funext i
  by_cases hlocal : (encodeGN r).length ≤ i.val ∧
      i.val < (encodeGN r).length +
        gnLocalSpan (encodeG1 (gnFirstRequest r g)).length
  · unfold gnOverlayTape
    rw [dif_pos hlocal, g1InitialTape_eq_frameListTape]
    simp only [frameListTape, gnSourceIndex_val, List.getD]
    rw [List.getElem?_append_right hlocal.1]
  · unfold gnOverlayTape
    rw [dif_neg hlocal, gnInitialTape_eq_frameListTape]
    have hout : i.val < (encodeGN r).length ∨
        (encodeGN r).length +
          gnLocalSpan (encodeG1 (gnFirstRequest r g)).length ≤ i.val := by
      omega
    rcases hout with hleft | hright
    · simp only [frameListTape, List.getD]
      rw [List.getElem?_append_left hleft]
    · have hgn : (encodeGN r).length ≤ i.val := by omega
      have hall : (encodeGN r ++ encodeG1 (gnFirstRequest r g)).length ≤
          i.val := by
        simp only [List.length_append]
        unfold gnLocalSpan at hright
        omega
      simp only [frameListTape, List.getD]
      rw [List.getElem?_eq_none hgn, List.getElem?_eq_none hall]

/-- Concrete capstone: the shifted configuration is exactly the explicit
aligned, concatenated-list physical configuration.  This is an equality of
complete configurations, not an execution-reachability statement. -/
theorem gnFirstInstalledConfig_eq_physical {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    gnFirstInstalledConfig r g hg = gnFirstInstalledPhysicalConfig r g := by
  apply Configuration.ext_of_components
  · rfl
  · apply Fin.ext
    change (encodeGN r).length +
      ((G1M.initialConfig
        (g1Point (encodeG1 (gnFirstRequest r g)))).head : Nat) =
          (encodeGN r).length
    rfl
  · change gnOverlayTape GNM (encodeGN r).length (gnFirstRequest_room hg)
        (G1M.initialConfig (g1Point (encodeG1 (gnFirstRequest r g))))
        (GNM.initialConfig (gnPoint (encodeGN r))).tape =
      frameListTape (encodeGN r ++ encodeG1 (gnFirstRequest r g))
    exact gnFirstOverlay_eq_concat r g (gnFirstRequest_room hg)

/-- Complete component/range description of the explicit physical endpoint. -/
theorem gnFirstInstalledPhysicalConfig_structure (r : GNProgram)
    (g : SLGate r.inputs.length) :
    let q := gnFirstRequest r g
    let N := (encodeGN r).length
    let W := (encodeG1 q).length
    (gnFirstInstalledPhysicalConfig r g).state =
        gnEmbed (G1M.initialConfig (g1Point (encodeG1 q))).state ∧
      ((gnFirstInstalledPhysicalConfig r g).head : Nat) = N ∧
      (gnFirstInstalledPhysicalConfig r g).tape =
        frameListTape (encodeGN r ++ encodeG1 q) ∧
      (∀ i : Fin (GNM.tapeLength N), i.val < N →
        (gnFirstInstalledPhysicalConfig r g).tape i =
          (GNM.initialConfig (gnPoint (encodeGN r))).tape i) ∧
      (∀ (i : Fin (GNM.tapeLength N))
        (hi : N ≤ i.val ∧ i.val < N + W),
        (gnFirstInstalledPhysicalConfig r g).tape i =
          (encodeG1 q).get ⟨i.val - N, by omega⟩) ∧
      (∀ i : Fin (GNM.tapeLength N), N + W ≤ i.val → i.val < N + W + 5 →
        (gnFirstInstalledPhysicalConfig r g).tape i = false) ∧
      (∀ i : Fin (GNM.tapeLength N),
        (i.val < N ∨ N + W + 5 ≤ i.val) →
        (gnFirstInstalledPhysicalConfig r g).tape i =
          (GNM.initialConfig (gnPoint (encodeGN r))).tape i) := by
  dsimp only
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [gnInitialTape_eq_frameListTape]
    change frameListTape (encodeGN r ++ encodeG1 (gnFirstRequest r g)) i =
      frameListTape (encodeGN r) i
    simp only [frameListTape, List.getD]
    rw [List.getElem?_append_left hi]
  · intro i hi
    have hoff : i.val - (encodeGN r).length <
        (encodeG1 (gnFirstRequest r g)).length := by omega
    change frameListTape (encodeGN r ++ encodeG1 (gnFirstRequest r g)) i = _
    simp only [frameListTape, List.getD]
    rw [List.getElem?_append_right hi.1, List.getElem?_eq_getElem hoff]
    rfl
  · intro i hlow _
    have hoff : (encodeG1 (gnFirstRequest r g)).length ≤
        i.val - (encodeGN r).length := by omega
    change frameListTape (encodeGN r ++ encodeG1 (gnFirstRequest r g)) i = false
    simp only [frameListTape, List.getD]
    rw [List.getElem?_append_right (by omega), List.getElem?_eq_none hoff]
    rfl
  · intro i hout
    rw [gnInitialTape_eq_frameListTape]
    rcases hout with hleft | hright
    · change frameListTape (encodeGN r ++ encodeG1 (gnFirstRequest r g)) i =
        frameListTape (encodeGN r) i
      simp only [frameListTape, List.getD]
      rw [List.getElem?_append_left hleft]
    · have hgn : (encodeGN r).length ≤ i.val := by omega
      have hall : (encodeGN r ++ encodeG1 (gnFirstRequest r g)).length ≤ i.val := by
        simp only [List.length_append]
        omega
      change frameListTape (encodeGN r ++ encodeG1 (gnFirstRequest r g)) i =
        frameListTape (encodeGN r) i
      simp only [frameListTape, List.getD]
      rw [List.getElem?_eq_none hall, List.getElem?_eq_none hgn]

/-! ## Nonempty and empty literal capstones -/

namespace GNFirstInstallProbes

open GNFixedDelegateProbes
open G1AResultProbes

theorem oneConstFalse_first_gate :
    oneConstFalseProgram.program.gates[0]? =
      some (SLGate.const false : SLGate 0) := rfl

theorem oneConstFalse_first_request :
    gnFirstRequest oneConstFalseProgram (SLGate.const false : SLGate 0) =
      reqConstF := by rfl

theorem oneConstFalse_width_room :
    (encodeGN oneConstFalseProgram).length = 48 ∧
      (encodeG1 (gnFirstRequest oneConstFalseProgram
        (SLGate.const false : SLGate 0))).length = 32 ∧
      48 + gnLocalSpan 32 ≤ GNM.tapeLength 48 := by decide

theorem oneConstFalse_installed_physical :
    gnFirstInstalledConfig oneConstFalseProgram
        (SLGate.const false : SLGate 0) oneConstFalse_first_gate =
      gnFirstInstalledPhysicalConfig oneConstFalseProgram
        (SLGate.const false : SLGate 0) :=
  gnFirstInstalledConfig_eq_physical oneConstFalse_first_gate

/-- The empty program has no first gate and therefore no install witness. -/
theorem empty_no_first_gate : emptyProgram.program.gates[0]? = none := rfl

end GNFirstInstallProbes

end Pnp3.Internal.PsubsetPpoly.TM
