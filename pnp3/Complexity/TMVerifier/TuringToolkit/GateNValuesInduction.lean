import Complexity.TMVerifier.TuringToolkit.GateNValuesCopy

/-!
# GN-E2-5c actual values-list execution (Infrastructure)

Induct through the live valuesEntry classifier using the landed one-value
execution, then run the landed output-false tail writer. The exact target and
premises were frozen in `Docs/GN_E2_5C_VALUES_INDUCTION.md` before implementation.
No transition, encoding or memory/runtime allocation changes. All clocks here
are exact additive runConfig endpoints; first arrival and runtime adequacy,
launch, delegation, commit, repeated gates, verdict and acceptance remain open.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan
open Encoding

/-- Each copy advances both the source head and destination frontier by one
frame, so the distance stays constant throughout this actual list. -/
def gnValuesListSteps (values : List Bool) (middle : List G1Frame) : Nat :=
  values.length * (8 * (values.length + middle.length) + 38)

/-- Exact additive recurrence for the live one-value clock. -/
theorem gnValuesListSteps_cons (b : Bool) (bs : List Bool)
    (middle : List G1Frame) :
    gnValuesListSteps (b :: bs) middle =
      (8 * (bs.length + 1 + middle.length) + 38) +
        gnValuesListSteps bs (middle ++ [G1Frame.data b]) := by
  simp only [gnValuesListSteps, List.length_cons, List.length_append,
    List.length_nil]
  have hd : bs.length + (middle.length + (0 + 1)) =
      bs.length + 1 + middle.length := by omega
  rw [hd, Nat.add_mul, Nat.one_mul]
  omega

private theorem gnValuesList_admissible (middle : List G1Frame)
    (values : List Bool) (h : ∀ f ∈ middle, GNInstallAdmissible f) :
    ∀ f ∈ middle ++ values.map G1Frame.data, GNInstallAdmissible f := by
  intro f hf
  rcases List.mem_append.1 hf with hf | hf
  · exact h f hf
  · obtain ⟨b, _, rfl⟩ := List.mem_map.1 hf
    exact ⟨(by intro he; cases he), (by intro he; cases he)⟩

/-- Execute every actual list element, restoring the source and appending its
data frame to scratch in list order. The next output slot is still pending. -/
theorem gnCS_values_list_exact (n : Nat) (pre : List G1Frame)
    (values : List Bool) (middle : List G1Frame)
    (hmiddle : ∀ f ∈ middle, GNInstallAdmissible f)
    (hroom : 4 * (pre.length + 2 * values.length + middle.length + 3) <
      GNM.tapeLength n) :
    TM.runConfig (M := GNM)
        (gnPendingValuesConfig n pre values middle (by omega) .valuesEntry)
        (gnValuesListSteps values middle) =
      gnPendingValuesConfig n (pre ++ values.map G1Frame.data) []
        (middle ++ values.map G1Frame.data) (by
          simp only [List.length_append, List.length_map]; omega) .valuesEntry := by
  induction values generalizing pre middle with
  | nil => simp [gnValuesListSteps, TM.runConfig]
  | cons b bs ih =>
      rw [gnValuesListSteps_cons, runConfig_add,
        gnCS_values_cons_exact n pre b bs middle hmiddle (by
          simp only [List.length_cons] at hroom; omega)]
      have hadm := gnValuesList_admissible middle [b] hmiddle
      have hr := ih (pre ++ [G1Frame.data b]) (middle ++ [G1Frame.data b])
        hadm (by
          simp only [List.length_append, List.length_cons, List.length_nil] at *
          omega)
      simpa only [List.map_cons, List.append_assoc, List.cons_append,
        List.nil_append] using hr

/-- Full tape after the values list and fixed tail; the head is on the blank
after the installed request. Generic prefixes need not be program encodings. -/
def gnValuesListReadyConfig (n : Nat) (pre : List G1Frame) (values : List Bool)
    (middle : List G1Frame)
    (hroom : 4 * (pre.length + 2 * values.length + middle.length + 3) <
      GNM.tapeLength n) : Configuration (M := GNM) n :=
  gnCopyShuttle.cfg n (4 * (pre.length + 2 * values.length + middle.length + 3))
    hroom
    (frameListTape ((pre ++ values.map G1Frame.data ++ G1Frame.output false ::
      middle ++ values.map G1Frame.data ++
      [G1Frame.output false, G1Frame.finish, G1Frame.blank]).flatMap G1Frame.bits))
    .requestReady

/-- Execute the list, classify output false, seek and write both tail frames. -/
theorem gnCS_values_list_requestReady_exact (n : Nat) (pre : List G1Frame)
    (values : List Bool) (middle : List G1Frame)
    (hmiddle : ∀ f ∈ middle, GNInstallAdmissible f)
    (hroom : 4 * (pre.length + 2 * values.length + middle.length + 3) <
      GNM.tapeLength n) :
    TM.runConfig (M := GNM)
        (gnPendingValuesConfig n pre values middle (by omega) .valuesEntry)
        (gnValuesListSteps values middle + (4 * (middle.length + values.length) + 20)) =
      gnValuesListReadyConfig n pre values middle hroom := by
  rw [runConfig_add, gnCS_values_list_exact n pre values middle hmiddle hroom]
  have ht := gnCS_values_outputFalse_tail_exact n (pre ++ values.map G1Frame.data)
    (middle ++ values.map G1Frame.data) (gnValuesList_admissible middle values hmiddle)
    (by simp only [List.length_append, List.length_map]; omega)
  simp only [List.length_append, List.length_map] at ht
  simp only [gnPendingValuesConfig, gnPendingValuesFrames, List.map_nil,
    List.append_nil, List.length_append, List.length_map]
  refine ht.trans ?_
  apply Configuration.ext_of_components
  · rfl
  · apply Fin.ext
    change 4 * (pre.length + values.length + (middle.length + values.length) + 3) =
      4 * (pre.length + 2 * values.length + middle.length + 3)
    omega
  · change frameListTape _ = frameListTape _
    simp only [List.append_assoc, List.cons_append]

/-- Actual encoded frames after the first reserved output slot, through the
installed first record image. A selected first gate ensures that slot exists. -/
def gnValuesListMiddle (r : GNProgram) (g : SLGate r.inputs.length) : List G1Frame :=
  gnSlotFrames (r.program.gates.length - 1) ++ [G1Frame.separator] ++
    gnRecordsFrames .cursor r.program.gates ++
    [G1Frame.separator, G1Frame.output false, G1Frame.finish] ++
    (gnRecordFrames .cursor g).map gnInstallImage

private theorem gnValuesListMiddle_frames {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    encodeGNFrames r ++ (gnRecordFrames .cursor g).map gnInstallImage =
      [G1Frame.bof] ++ r.inputs.map G1Frame.data ++
        G1Frame.output false :: gnValuesListMiddle r g := by
  have hslots : gnSlotFrames r.program.gates.length =
      G1Frame.output false :: gnSlotFrames (r.program.gates.length - 1) := by
    rcases hk : r.program.gates with _ | ⟨first, rest⟩
    · rw [hk] at hg; simp at hg
    · simp [gnSlotFrames, List.replicate_succ]
  simp [encodeGNFrames, gnValuesListMiddle, gnAssignFrames, hslots, List.append_assoc]

private theorem gnValuesListMiddle_admissible {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    ∀ f ∈ gnValuesListMiddle r g, GNInstallAdmissible f := by
  intro f hf
  have hmem : f ∈ encodeGNFrames r ++ (gnRecordFrames .cursor g).map gnInstallImage := by
    rw [gnValuesListMiddle_frames hg]
    simp only [List.singleton_append, List.mem_cons, List.mem_append, List.mem_map]
    exact Or.inr (Or.inr hf)
  rcases List.mem_append.1 hmem with h | h
  · exact encodeGNFrames_no_blank_no_outputTrue r f h
  · rw [gnRecordFrames_map_image] at h
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨by decide, by decide⟩
    · rcases List.mem_append.1 h with h | h
      · rcases gnGateBodyFrames_body g f h with rfl | rfl | rfl <;>
          exact ⟨by decide, by decide⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        subst h
        exact ⟨by decide, by decide⟩

private theorem gnValuesListMiddle_length {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    (encodeGNFrames r).length + (gnRecordFrames .cursor g).length =
      r.inputs.length + (gnValuesListMiddle r g).length + 2 := by
  have h := congrArg List.length (gnValuesListMiddle_frames hg)
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] at h
  omega

private theorem gnValuesListMiddle_room {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    4 * (([G1Frame.bof] : List G1Frame).length + 2 * r.inputs.length +
      (gnValuesListMiddle r g).length + 3) < GNM.tapeLength (encodeGN r).length := by
  have hr := gnFirstRequestReady_room hg
  have hl := gnValuesListMiddle_length hg
  simp only [List.length_cons, List.length_nil]
  omega

/-- Exact real initial clock: landed values-entry prefix, every physical value
copy at distance d, and the existing tail clock at that same distance d. -/
def gnValuesRequestReadySteps (r : GNProgram) (g : SLGate r.inputs.length) : Nat :=
  gnValuesEntrySteps r g +
    (r.inputs.length * (8 * gnValuesTailDistance r g + 38) + gnValuesTailSteps r g)

theorem gnValuesRequestReadySteps_provenance (r : GNProgram)
    (g : SLGate r.inputs.length) :
    gnValuesRequestReadySteps r g = gnValuesEntrySteps r g +
      (r.inputs.length * (8 * gnValuesTailDistance r g + 38) +
        (4 * gnValuesTailDistance r g + 20)) := rfl

/-- Complete the actual values list and tail from the real values boundary.
Only the selected first-gate equation is assumed; values are r.inputs. -/
theorem gnCS_valuesEntry_requestReady_exact {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    TM.runConfig (M := GNM) (gnValuesEntryConfig r g hg)
        (r.inputs.length * (8 * gnValuesTailDistance r g + 38) + gnValuesTailSteps r g) =
      gnFirstRequestReadyConfig r g hg := by
  have hlen := gnValuesListMiddle_length hg
  have hdist := (gnValuesTailSteps_provenance r g).1
  have hd : r.inputs.length + (gnValuesListMiddle r g).length =
      gnValuesTailDistance r g := by omega
  have hroom := gnValuesListMiddle_room hg
  have hstart : gnValuesEntryConfig r g hg =
      gnPendingValuesConfig (encodeGN r).length [G1Frame.bof] r.inputs
        (gnValuesListMiddle r g) (by
          simp only [List.length_cons, List.length_nil] at hroom ⊢; omega) .valuesEntry := by
    apply Configuration.ext_of_components
    · rfl
    · rfl
    · change frameListTape _ = frameListTape _
      have hb := frameListTape_append_blank (L := GNM.tapeLength (encodeGN r).length)
        g1FrameCodec
        (encodeGNFrames r ++ (gnRecordFrames .cursor g).map gnInstallImage ++
          [G1Frame.blank]) G1Frame.blank rfl
      simp only [g1FrameCodec_bits] at hb
      rw [hb]
      rw [gnPendingValuesFrames, ← gnValuesListMiddle_frames hg]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hend : gnValuesListReadyConfig (encodeGN r).length [G1Frame.bof]
      r.inputs (gnValuesListMiddle r g) hroom = gnFirstRequestReadyConfig r g hg := by
    apply Configuration.ext_of_components
    · rfl
    · apply Fin.ext
      change 4 * (([G1Frame.bof] : List G1Frame).length + 2 * r.inputs.length +
        (gnValuesListMiddle r g).length + 3) = _
      simp only [List.length_cons, List.length_nil]
      change 4 * (1 + 2 * r.inputs.length + (gnValuesListMiddle r g).length + 3) =
        4 * ((encodeGNFrames r).length + (gnRecordFrames .cursor g).length +
          r.inputs.length + 2)
      omega
    · change frameListTape _ = frameListTape _
      rw [encodeG1Frames_eq_prefix, ← gnFirstRecord_image_request_prefix r g]
      simp only [← List.append_assoc]
      rw [gnValuesListMiddle_frames hg]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hsched : gnValuesListSteps r.inputs (gnValuesListMiddle r g) +
      (4 * ((gnValuesListMiddle r g).length + r.inputs.length) + 20) =
      r.inputs.length * (8 * gnValuesTailDistance r g + 38) + gnValuesTailSteps r g := by
    simp only [gnValuesListSteps, gnValuesTailSteps, Nat.add_comm
      (gnValuesListMiddle r g).length r.inputs.length, hd]
  rw [← hsched, hstart, gnCS_values_list_requestReady_exact _ _ _ _
    (gnValuesListMiddle_admissible hg) hroom]
  exact hend

/-- Genuine initial execution for arbitrary actual input lists, including all
nonempty lists, to the existing exact first-request tape and requestReady state.
This installs the request; it does not execute that request or evaluate a gate. -/
theorem gnCS_encodeGN_valuesRequestReady_exact {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    TM.runConfig (M := GNM) (GNM.initialConfig (gnPoint (encodeGN r)))
        (gnValuesRequestReadySteps r g) = gnFirstRequestReadyConfig r g hg := by
  rw [gnValuesRequestReadySteps, runConfig_add, gnCS_encodeGN_valuesEntry_exact hg,
    gnCS_valuesEntry_requestReady_exact hg]

namespace GNValuesInductionProbes

open GNEncodingExamples GNValuesCopyProbes

def twoValuesStart : Configuration (M := GNM) 0 :=
  gnPendingValuesConfig 0 [] [true, false] [] (by decide) .valuesEntry

/-- Literal complete tape, including restored source and both installed bits. -/
def twoValuesReady : Configuration (M := GNM) 0 :=
  gnCopyShuttle.cfg 0 28 (by decide)
    (frameListTape ([G1Frame.data true, .data false, .output false,
      .data true, .data false, .output false, .finish, .blank].flatMap G1Frame.bits))
    .requestReady

theorem literal_two_values_requestReady :
    TM.runConfig (M := GNM) twoValuesStart 136 = twoValuesReady ∧
      gnValuesListSteps [true, false] [] = 108 ∧
      (twoValuesReady.head : Nat) = 28 ∧
      twoValuesReady.state = ⟨(0 : Fin 1), .requestReady⟩ := by
  refine ⟨?_, rfl, rfl, rfl⟩
  exact gnCS_values_list_requestReady_exact 0 [] [true, false] [] (by simp) (by decide)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- Independent kernel reduction of the actual 136-row machine, checking the
newly installed true value and both tail frames as well as state and head. -/
theorem literal_two_values_executable :
    (TM.runConfig (M := GNM) twoValuesStart 136).state =
        ⟨(0 : Fin 1), .requestReady⟩ ∧
      ((TM.runConfig (M := GNM) twoValuesStart 136).head : Nat) = 28 ∧
      twoValuesStart.tape ⟨13, by decide⟩ = false ∧
      (TM.runConfig (M := GNM) twoValuesStart 136).tape ⟨13, by decide⟩ = true ∧
      (TM.runConfig (M := GNM) twoValuesStart 136).tape ⟨20, by decide⟩ = true ∧
      (TM.runConfig (M := GNM) twoValuesStart 136).tape ⟨26, by decide⟩ = true := by
  decide +kernel

def capValuesReady : Configuration (M := GNM) 84 :=
  gnCopyShuttle.cfg 84 116 (by decide)
    (frameListTape
      ([G1Frame.bof, .data true, .output false, .output false, .separator,
        .cursor, .tag, .argSep, .argSep, .finish,
        .bof, .tag, .tag, .tag, .argSep, .index, .argSep, .finish,
        .separator, .output false, .finish,
        .bof, .tag, .argSep, .argSep, .separator,
        .data true, .output false, .finish, .blank].flatMap G1Frame.bits)) .requestReady

/-- Actual nonempty encoded initial program through the complete scratch
request. The pure decoding identity identifies the input whose values ran. -/
theorem literal_cap_valuesRequestReady :
    TM.runConfig (M := GNM)
        (GNM.initialConfig (gnPoint (encodeGN capProgram))) 1300 = capValuesReady ∧
      gnValuesRequestReadySteps capProgram capFirstGate = 1300 ∧
      (capValuesReady.head : Nat) = 116 ∧
      capValuesReady.state = ⟨(0 : Fin 1), .requestReady⟩ ∧
      decodeGN? (encodeGN capProgram) = some capProgram := by
  have hg : capProgram.program.gates[0]? = some capFirstGate := rfl
  have hs : gnValuesRequestReadySteps capProgram capFirstGate = 1300 := by decide
  have hr := gnCS_encodeGN_valuesRequestReady_exact hg
  rw [hs] at hr
  refine ⟨?_, hs, rfl, rfl, decodeGN?_encodeGN capProgram⟩
  exact hr

/-- The existing malformed ingress still rejects and stays rejected, without
changing tape or head after the fourth row. No new success route is installed. -/
theorem literal_reserved_reject_stable (extra : Nat) :
    TM.runConfig (M := GNM) reservedCopyStart (4 + extra) =
      gnCopyShuttle.cfg 0 3 (by decide) (frameListTape [true, true, false, true])
        .reject := by
  exact gnCS_valuesEntry_reserved1101_reject_stable 0 0 (by decide) _ rfl extra

end GNValuesInductionProbes

end Pnp3.Internal.PsubsetPpoly.TM
