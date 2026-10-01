import Complexity.TMVerifier.TuringToolkit.GateNValuesWriter
import Complexity.TMVerifier.TuringToolkit.GateNEncodingExamples

/-!
# GN-E2-5b one physical value copy (Infrastructure)

The live E2-5a classifier takes four rows, then four backward rows enter the
installer. Its source-restoring shuttle costs `8*d+29`; thus `8*d+37` reaches
the data exit and one further row returns to `valuesEntry`. No machine row,
clock, encoder or finite control changes here. The remaining values and the
request tail are pending. No full values induction, nonempty request completion,
launch, delegation, commit, verdict, acceptance or lower bound is claimed.
The exact target and hypotheses are frozen in `Docs/GN_E2_5B_VALUES_COPY.md`.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan
open Encoding

/-- Exact data classification followed by the four physical backward rows. -/
theorem gnCS_values_data_to_install_eight (n base : Nat)
    (hsafe : base + 4 < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool) (b : Bool)
    (hbits : physicalBitsAt hsafe tape = (G1Frame.data b).bits) :
    TM.runConfig (M := GNM)
        (gnCopyShuttle.cfg n base (by change base < GNM.tapeLength n; omega)
          tape .valuesEntry) 8 =
      gnCopyShuttle.cfg n base (by change base < GNM.tapeLength n; omega)
        tape (.install .probe .p0 .empty) := by
  have hc := gnCS_values_classify n base hsafe tape (.data b) hbits
    (fun h => GNState.noConfusion h)
  have hb := Phased.holdWalk4 gnCS gnCS.startPhase n base hsafe tape
    (.values .back (.p3 false false false))
    (.values .back (.p2 false false)) (.values .back (.p1 false))
    (.values .back .p0) (.install .probe .p0 .empty)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  change TM.runConfig (M := GNM)
    (Phased.alignedAt gnCS gnCS.startPhase n base
      (by change base < GNM.tapeLength n; omega) tape .valuesEntry) 8 = _
  rw [show (8 : Nat) = 4 + 4 from rfl, runConfig_add, hc]
  exact hb

/-- The landed carried-data route preserves the tape/head and returns to the
classifier. In particular it does not dispatch directly into the installer. -/
theorem gnCS_dataExit_to_valuesEntry_one (n head : Nat)
    (hhead : head < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool) (b : Bool) :
    TM.runConfig (M := GNM)
        (gnCopyShuttle.cfg n head hhead tape
          (gnInstallExitState (.carried (.data b)))) 1 =
      gnCopyShuttle.cfg n head hhead tape .valuesEntry := by
  have hs := Phased.stepStay gnCS gnCS.startPhase n head hhead tape
    (gnInstallExitState (.carried (.data b))) .valuesEntry (tape ⟨head, hhead⟩)
    (gnTransition_dataExit gnCS.startPhase b _).1
  rw [writeCell_self] at hs
  rw [runConfig_one]
  exact hs

/-- Copy clock through the installer exit, excluding its stationary dispatch. -/
def gnValueCopySteps (distance : Nat) : Nat := 8 * distance + 37

/-- Both endpoints have explicit, distinct clocks. -/
theorem gnValueCopySteps_provenance (d : Nat) :
    gnValueCopySteps d = 8 + (8 * d + 29) ∧
      gnValueCopySteps d + 1 = 8 * d + 38 := by
  constructor <;> unfold gnValueCopySteps <;> omega

/-- Exact physical copy on an arbitrary frame prefix, through the data exit. -/
theorem gnCS_valueCopy_exit_exact (n : Nat) (pre : List G1Frame) (b : Bool)
    (middle rest : List G1Frame)
    (hmiddle : ∀ f ∈ middle, GNInstallAdmissible f)
    (hroom : 4 * (pre.length + middle.length + 2) < GNM.tapeLength n) :
    TM.runConfig (M := GNM)
        (gnCopyShuttle.cfg n (4 * pre.length) (by
          change 4 * pre.length < GNM.tapeLength n; omega)
          (frameListTape ((pre ++ G1Frame.data b :: middle ++
            G1Frame.blank :: G1Frame.blank :: rest).flatMap G1Frame.bits))
          .valuesEntry) (gnValueCopySteps middle.length) =
      gnCopyShuttle.cfg n (4 * pre.length + 4) (by
        change 4 * pre.length + 4 < GNM.tapeLength n; omega)
        (frameListTape ((pre ++ G1Frame.data b :: middle ++
          G1Frame.data b :: G1Frame.blank :: rest).flatMap G1Frame.bits))
        (gnInstallExitState (.carried (.data b))) := by
  have hsafe : 4 * pre.length + 4 < GNM.tapeLength n := by omega
  have hbits : physicalBitsAt hsafe
      (frameListTape ((pre ++ G1Frame.data b :: middle ++
        G1Frame.blank :: G1Frame.blank :: rest).flatMap G1Frame.bits)) =
      (G1Frame.data b).bits := by
    simpa only [g1FrameCodec_bits, List.append_assoc, List.cons_append] using
      physicalBitsAt_flatMap g1FrameCodec pre
        (middle ++ G1Frame.blank :: G1Frame.blank :: rest) (.data b) hsafe
  rw [(gnValueCopySteps_provenance _).1, runConfig_add,
    gnCS_values_data_to_install_eight n _ hsafe _ b hbits]
  exact gnCS_copyShuttle_nextBlank n pre (.data b) middle rest .empty
    ⟨(by intro h; cases h), (by intro h; cases h)⟩ hmiddle hroom

/-- One genuine copy and the data exit dispatch, returning to the live
classifier on the next source frame. The destination blank has become data. -/
theorem gnCS_valueCopy_return_exact (n : Nat) (pre : List G1Frame) (b : Bool)
    (middle rest : List G1Frame)
    (hmiddle : ∀ f ∈ middle, GNInstallAdmissible f)
    (hroom : 4 * (pre.length + middle.length + 2) < GNM.tapeLength n) :
    TM.runConfig (M := GNM)
        (gnCopyShuttle.cfg n (4 * pre.length) (by
          change 4 * pre.length < GNM.tapeLength n; omega)
          (frameListTape ((pre ++ G1Frame.data b :: middle ++
            G1Frame.blank :: G1Frame.blank :: rest).flatMap G1Frame.bits))
          .valuesEntry) (8 * middle.length + 38) =
      gnCopyShuttle.cfg n (4 * pre.length + 4) (by
        change 4 * pre.length + 4 < GNM.tapeLength n; omega)
        (frameListTape ((pre ++ G1Frame.data b :: middle ++
          G1Frame.data b :: G1Frame.blank :: rest).flatMap G1Frame.bits))
        .valuesEntry := by
  rw [← (gnValueCopySteps_provenance _).2, runConfig_add,
    gnCS_valueCopy_exit_exact n pre b middle rest hmiddle hroom,
    gnCS_dataExit_to_valuesEntry_one]

/-- Source prefix, values still pending, output-slot terminator and the block
up to the scratch frontier. Two explicit blanks equal the ambient blank tail. -/
def gnPendingValuesFrames (pre : List G1Frame) (values : List Bool)
    (middle : List G1Frame) : List G1Frame :=
  pre ++ values.map G1Frame.data ++ G1Frame.output false :: middle ++
    [G1Frame.blank, G1Frame.blank]

def gnPendingValuesConfig (n : Nat) (pre : List G1Frame) (values : List Bool)
    (middle : List G1Frame) (hh : 4 * pre.length < GNM.tapeLength n)
    (q : GNState) : Configuration (M := GNM) n :=
  gnCopyShuttle.cfg n (4 * pre.length) hh
    (frameListTape ((gnPendingValuesFrames pre values middle).flatMap G1Frame.bits)) q

/-- One cons step on a pending list. The copied bit moves into the installed
prefix at the old blank; the remaining list and its output-slot terminator stay
pending. This is an execution equality, not an inductive full-list claim. -/
theorem gnCS_values_cons_exact (n : Nat) (pre : List G1Frame)
    (b : Bool) (bs : List Bool) (middle : List G1Frame)
    (hmiddle : ∀ f ∈ middle, GNInstallAdmissible f)
    (hroom : 4 * (pre.length + bs.length + middle.length + 3) < GNM.tapeLength n) :
    TM.runConfig (M := GNM)
        (gnPendingValuesConfig n pre (b :: bs) middle (by omega) .valuesEntry)
        (8 * (bs.length + 1 + middle.length) + 38) =
      gnPendingValuesConfig n (pre ++ [G1Frame.data b]) bs
        (middle ++ [G1Frame.data b]) (by
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega) .valuesEntry := by
  let mid := bs.map G1Frame.data ++ G1Frame.output false :: middle
  have hlen : mid.length = bs.length + 1 + middle.length := by simp [mid]; omega
  have hadm : ∀ f ∈ mid, GNInstallAdmissible f := by
    intro f hf
    rcases List.mem_append.1 hf with hf | hf
    · obtain ⟨v, _, rfl⟩ := List.mem_map.1 hf
      exact ⟨(by intro h; cases h), (by intro h; cases h)⟩
    · rcases List.mem_cons.1 hf with rfl | hf
      · exact ⟨by decide, by decide⟩
      · exact hmiddle f hf
  have hr := gnCS_valueCopy_return_exact n pre b mid [] hadm (by rw [hlen]; omega)
  have hstart : gnCopyShuttle.cfg n (4 * pre.length)
      (by change 4 * pre.length < GNM.tapeLength n; omega)
      (frameListTape ((pre ++ G1Frame.data b :: mid ++
        [G1Frame.blank, G1Frame.blank]).flatMap G1Frame.bits)) .valuesEntry =
      gnPendingValuesConfig n pre (b :: bs) middle (by omega) .valuesEntry := by
    simp [gnPendingValuesConfig, gnPendingValuesFrames, mid, List.append_assoc]
  simp only [hlen] at hr
  rw [hstart] at hr
  refine hr.trans ?_
  apply Configuration.ext_of_components
  · rfl
  · apply Fin.ext
    change 4 * pre.length + 4 = 4 * (pre ++ [G1Frame.data b]).length
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · change frameListTape _ = frameListTape _
    have hf : gnPendingValuesFrames (pre ++ [G1Frame.data b]) bs
        (middle ++ [G1Frame.data b]) =
        (pre ++ G1Frame.data b :: mid ++ [G1Frame.data b, G1Frame.blank]) ++
          [G1Frame.blank] := by
      simp [gnPendingValuesFrames, mid, List.append_assoc]
    rw [hf]
    exact frameListTape_append_blank g1FrameCodec _ G1Frame.blank rfl

/-- A nonempty residual list enters the existing installer via all eight live
classifier/back rows, with the physical tape unchanged. -/
theorem gnCS_values_nonempty_handoff (n : Nat) (pre : List G1Frame)
    (b : Bool) (bs : List Bool) (middle : List G1Frame)
    (hsafe : 4 * pre.length + 4 < GNM.tapeLength n) :
    TM.runConfig (M := GNM)
        (gnPendingValuesConfig n pre (b :: bs) middle (by omega) .valuesEntry) 8 =
      gnPendingValuesConfig n pre (b :: bs) middle (by omega)
        (.install .probe .p0 .empty) := by
  apply gnCS_values_data_to_install_eight n _ hsafe _ b
  simpa [gnPendingValuesFrames, List.append_assoc] using
    physicalBitsAt_flatMap (L := GNM.tapeLength n) g1FrameCodec pre
      (bs.map G1Frame.data ++ G1Frame.output false :: middle ++
        [G1Frame.blank, G1Frame.blank]) (.data b) hsafe

/-- An exhausted residual list reads its reserved output slot and enters the
landed tail seek. It has not yet written either tail frame. -/
theorem gnCS_values_nil_tail_handoff (n : Nat) (pre middle : List G1Frame)
    (hsafe : 4 * pre.length + 4 < GNM.tapeLength n) :
    TM.runConfig (M := GNM)
        (gnPendingValuesConfig n pre [] middle (by omega) .valuesEntry) 4 =
      gnCopyShuttle.cfg n (4 * pre.length + 4) hsafe
        (frameListTape ((gnPendingValuesFrames pre [] middle).flatMap G1Frame.bits))
        (.values .seekTail .p0) := by
  apply gnCS_values_classify n _ hsafe _ (G1Frame.output false) _
    (fun h => GNState.noConfusion h)
  simpa [gnPendingValuesFrames, List.append_assoc] using
    physicalBitsAt_flatMap (L := GNM.tapeLength n) g1FrameCodec pre
      (middle ++ [G1Frame.blank, G1Frame.blank]) (G1Frame.output false) hsafe

/-- Values boundary tape before the copy. -/
def gnValueCopyFrames (b : Bool) (middle rest : List G1Frame) : List G1Frame :=
  [G1Frame.bof] ++ G1Frame.data b :: middle ++ G1Frame.blank ::
    G1Frame.blank :: rest

/-- Values boundary tape after the copy, with the next frontier retained. -/
def gnValueCopyExitFrames (b : Bool) (middle rest : List G1Frame) :
    List G1Frame :=
  [G1Frame.bof] ++ G1Frame.data b :: middle ++ G1Frame.data b ::
    G1Frame.blank :: rest

/-- Real-input specialization of the arbitrary-prefix source configuration. -/
def gnValueCopyConfig (n : Nat) (b : Bool) (middle rest : List G1Frame)
    (hroom : 4 * (1 + middle.length + 2) < GNM.tapeLength n) :
    Configuration (M := GNM) n :=
  gnCopyShuttle.cfg n 4 (by
      change 4 < GNM.tapeLength n
      omega)
    (frameListTape ((gnValueCopyFrames b middle rest).flatMap G1Frame.bits))
    .valuesEntry

theorem gnRecordFrames_map_image {n : Nat} (g : SLGate n) :
    (gnRecordFrames .cursor g).map gnInstallImage =
      G1Frame.bof :: (gnGateBodyFrames g ++ [G1Frame.separator]) := by
  rw [gnRecordFrames_cursor_split]
  simp [gnGateBodyFrames_map_image, gnInstallImage]

def gnValueCopyMiddle (r : GNProgram) (g : SLGate r.inputs.length)
    (bs : List Bool) : List G1Frame :=
  gnAssignFrames bs ++ gnSlotFrames r.program.gates.length ++
    [G1Frame.separator] ++ (G1Frame.cursor :: gnFirstRecordMiddle r) ++
    (gnRecordFrames .cursor g).map gnInstallImage

def gnValueCopyDistance (r : GNProgram) (g : SLGate r.inputs.length) : Nat :=
  r.inputs.length + r.program.gates.length + (gnFirstRecordMiddle r).length +
    gnRecordSize (gnGateFields g) + 1

theorem gnValueCopyMiddle_length {r : GNProgram} {g : SLGate r.inputs.length}
    {b : Bool} {bs : List Bool} (hvals : r.inputs = b :: bs) :
    (gnValueCopyMiddle r g bs).length = gnValueCopyDistance r g := by
  have hlen : r.inputs.length = bs.length + 1 := by
    rw [hvals]; simp
  simp only [gnValueCopyMiddle, gnValueCopyDistance, List.length_append,
    List.length_map, List.length_cons, List.length_nil, gnAssignFrames_length,
    gnSlotFrames_length, gnRecordFrames, g1RecordFrames_length]
  omega

theorem gnValueCopy_frames {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) {b : Bool} {bs : List Bool}
    (hvals : r.inputs = b :: bs) :
    [G1Frame.bof] ++ G1Frame.data b :: gnValueCopyMiddle r g bs =
      encodeGNFrames r ++ (gnRecordFrames .cursor g).map gnInstallImage := by
  have hshape : encodeGNFrames r =
      gnLocatePrefix r ++ G1Frame.cursor :: gnFirstRecordMiddle r := by
    simpa [gnFirstRecordMiddle, List.append_assoc] using
      (encodeGNFrames_firstRecord_split hg).1
  have hassign : gnAssignFrames r.inputs =
      G1Frame.data b :: gnAssignFrames bs := by
    rw [hvals]; rfl
  rw [hshape, gnLocatePrefix, hassign]
  simp [gnValueCopyMiddle, List.append_assoc]

theorem gnValueCopyMiddle_admissible {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g)
    (bs : List Bool) :
    ∀ frame ∈ gnValueCopyMiddle r g bs, GNInstallAdmissible frame := by
  have hmiddle := (gnFirstRecord_copyShuttle_handoff hg).2.1
  intro frame hframe
  rw [gnValueCopyMiddle] at hframe
  rcases List.mem_append.1 hframe with hframe | hframe
  · rcases List.mem_append.1 hframe with hframe | hframe
    · rcases List.mem_append.1 hframe with hframe | hframe
      · rcases List.mem_append.1 hframe with hframe | hframe
        · simp only [gnAssignFrames] at hframe
          obtain ⟨v, -, rfl⟩ := List.mem_map.1 hframe
          cases v <;> exact ⟨by decide, by decide⟩
        · simp only [gnSlotFrames] at hframe
          rw [List.eq_of_mem_replicate hframe]
          exact ⟨by decide, by decide⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hframe
        subst hframe
        exact ⟨by decide, by decide⟩
    · rcases List.mem_cons.1 hframe with rfl | hframe
      · exact ⟨by decide, by decide⟩
      · exact hmiddle frame hframe
  · rw [gnRecordFrames_map_image] at hframe
    rcases List.mem_cons.1 hframe with rfl | hframe
    · exact ⟨by decide, by decide⟩
    · rcases List.mem_append.1 hframe with hframe | hframe
      · rcases gnGateBodyFrames_body g frame hframe with rfl | rfl | rfl <;>
          exact ⟨by decide, by decide⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hframe
        subst hframe
        exact ⟨by decide, by decide⟩

/-- Initial execution through the first copy and its return to valuesEntry. -/
def gnFirstValueCopySteps (r : GNProgram) (g : SLGate r.inputs.length) : Nat :=
  gnValuesEntrySteps r g + (gnValueCopySteps (gnValueCopyDistance r g) + 1)

theorem gnFirstValueCopySteps_provenance (r : GNProgram)
    (g : SLGate r.inputs.length) :
    gnFirstValueCopySteps r g =
      gnValuesEntrySteps r g + (8 * gnValueCopyDistance r g + 38) := by
  rfl

private theorem gnValueCopy_head_lt (N : Nat) : 8 < GNM.tapeLength N := by
  have hclock : gnClock N = 512 * (N + 1) ^ 2 + 512 := rfl
  change 8 < N + gnClock N + 1
  omega

/-- The original GN word and first record image, followed by exactly one
copied value. The request's output/finish tail has not been written. -/
def gnFirstValueCopiedConfig (r : GNProgram) (g : SLGate r.inputs.length)
    (b : Bool) : Configuration (M := GNM) (encodeGN r).length where
  state := ⟨(0 : Fin 1), .valuesEntry⟩
  head := ⟨8, gnValueCopy_head_lt _⟩
  tape := frameListTape
    ((encodeGNFrames r ++ (gnRecordFrames .cursor g).map gnInstallImage ++
      [G1Frame.data b, G1Frame.blank]).flatMap G1Frame.bits)

private theorem gnValueCopy_room {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) {b : Bool} {bs : List Bool}
    (hvals : r.inputs = b :: bs) :
    4 * (1 + (gnValueCopyMiddle r g bs).length + 2) <
      GNM.tapeLength (encodeGN r).length := by
  have hlen := gnValueCopyMiddle_length (g := g) hvals
  have hs := encodeGNFrames_firstRecord_split hg
  have hn : (encodeGN r).length =
      4 * (gnRecordsStart r + 1 + (gnFirstRecordMiddle r).length) := by
    rw [encodeGN_length, hs.1]
    simp only [List.length_append, List.length_cons, gnFirstRecordMiddle,
      List.length_nil]
    omega
  have hsplit : (gnFirstRecordMiddle r).length =
      (gnGateBodyFrames g).length + 1 + (gnFirstRecordTail r).length := by
    rw [gnFirstRecordMiddle_split hg]
    simp only [List.length_append, List.length_cons]
    omega
  have hsize : gnRecordSize (gnGateFields g) =
      (gnGateBodyFrames g).length + 2 := by
    simp only [gnRecordSize, gnGateBodyFrames, List.length_append,
      List.length_replicate, List.length_cons, List.length_nil]
    omega
  have hstart : gnRecordsStart r =
      r.inputs.length + r.program.gates.length + 2 := rfl
  have hsquare : (encodeGN r).length + 1 ≤ ((encodeGN r).length + 1) ^ 2 := by
    rw [pow_two]
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hclock : gnClock (encodeGN r).length =
      512 * ((encodeGN r).length + 1) ^ 2 + 512 := rfl
  change 4 * (1 + (gnValueCopyMiddle r g bs).length + 2) <
    (encodeGN r).length + gnClock (encodeGN r).length + 1
  rw [hlen, gnValueCopyDistance]
  omega

private theorem gnValuesEntry_eq_valueCopyConfig {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g)
    {b : Bool} {bs : List Bool} (hvals : r.inputs = b :: bs) :
    gnValuesEntryConfig r g hg =
      gnValueCopyConfig (encodeGN r).length b (gnValueCopyMiddle r g bs) []
        (gnValueCopy_room hg hvals) := by
  apply Configuration.ext_of_components
  · rfl
  · rfl
  · change frameListTape _ = frameListTape _
    rw [show gnValueCopyFrames b (gnValueCopyMiddle r g bs) [] =
        (encodeGNFrames r ++ (gnRecordFrames .cursor g).map gnInstallImage ++
          [G1Frame.blank]) ++ [G1Frame.blank] from by
      rw [gnValueCopyFrames, ← gnValueCopy_frames hg hvals]
      simp [List.append_assoc]]
    simpa only [g1FrameCodec_bits] using
      (frameListTape_append_blank
        (L := GNM.tapeLength (encodeGN r).length) g1FrameCodec
        (encodeGNFrames r ++ (gnRecordFrames .cursor g).map gnInstallImage ++
          [G1Frame.blank]) G1Frame.blank rfl)

/-- Exact one-value real-input execution. Only gate selection and the actual
nonempty input equation are assumed; room and admissibility are derived. -/
theorem gnCS_encodeGN_firstValueCopied_exact {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g)
    {b : Bool} {bs : List Bool} (hvals : r.inputs = b :: bs) :
    TM.runConfig (M := GNM) (GNM.initialConfig (gnPoint (encodeGN r)))
        (gnFirstValueCopySteps r g) = gnFirstValueCopiedConfig r g b := by
  have hlen := gnValueCopyMiddle_length (g := g) hvals
  have hframes : gnValueCopyExitFrames b (gnValueCopyMiddle r g bs) [] =
      encodeGNFrames r ++ (gnRecordFrames .cursor g).map gnInstallImage ++
        [G1Frame.data b, G1Frame.blank] := by
    rw [gnValueCopyExitFrames, ← gnValueCopy_frames hg hvals]
  have hsched : gnFirstValueCopySteps r g =
      gnValuesEntrySteps r g +
        (8 * (gnValueCopyMiddle r g bs).length + 38) := by
    rw [gnFirstValueCopySteps_provenance, hlen]
  rw [hsched, runConfig_add, gnCS_encodeGN_valuesEntry_exact hg,
    gnValuesEntry_eq_valueCopyConfig hg hvals]
  have hr := gnCS_valueCopy_return_exact (encodeGN r).length [G1Frame.bof] b
    (gnValueCopyMiddle r g bs) [] (gnValueCopyMiddle_admissible hg bs)
    (gnValueCopy_room hg hvals)
  change TM.runConfig (M := GNM)
    (gnValueCopyConfig (encodeGN r).length b (gnValueCopyMiddle r g bs) []
      (gnValueCopy_room hg hvals)) _ = _ at hr
  rw [hr]
  apply Configuration.ext_of_components
  · rfl
  · rfl
  · change frameListTape ((gnValueCopyExitFrames b _ []).flatMap _) = _
    rw [hframes]
    rfl

theorem gnFirstValueCopiedConfig_structure {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g)
    {b : Bool} {bs : List Bool} (hvals : r.inputs = b :: bs) :
    (gnFirstValueCopiedConfig r g b).state =
        ⟨(0 : Fin 1), .valuesEntry⟩ ∧
      ((gnFirstValueCopiedConfig r g b).head : Nat) = 8 ∧
      (gnFirstValueCopiedConfig r g b).tape =
        frameListTape
          ((encodeGNFrames r ++ (gnRecordFrames .cursor g).map gnInstallImage ++
            [G1Frame.data b, G1Frame.blank]).flatMap G1Frame.bits) ∧
      gnAssignFrames r.inputs = G1Frame.data b :: gnAssignFrames bs ∧
      (gnRecordFrames .cursor g).map gnInstallImage ++
          G1Frame.data b :: gnAssignFrames bs =
        g1PrefixFrames (gnFirstRequest r g) := by
  have hmap : List.map G1Frame.data r.inputs =
      G1Frame.data b :: gnAssignFrames bs := by
    rw [hvals]; rfl
  have hprefix := (gnValuesEntryConfig_structure hg).2.2.2.2.2
  rw [gnCurrentValues_zero, hmap] at hprefix
  exact ⟨rfl, rfl, rfl, by rw [hvals]; rfl, hprefix⟩

namespace GNValuesCopyProbes

open GNEncodingExamples

def capFirstGate : SLGate capProgram.inputs.length := SLGate.input ⟨0, by decide⟩

def capFirstValueCopiedConfig : Configuration (M := GNM) 84 where
  state := ⟨(0 : Fin 1), .valuesEntry⟩
  head := ⟨8, by
    simp [TM.tapeLength, gnCS, gnClock, g1Clock]⟩
  tape := frameListTape
    ([G1Frame.bof, .data true, .output false, .output false, .separator,
      .cursor, .tag, .argSep, .argSep, .finish,
      .bof, .tag, .tag, .tag, .argSep, .index, .argSep, .finish,
      .separator, .output false, .finish,
      .bof, .tag, .argSep, .argSep, .separator,
      .data true, .blank].flatMap G1Frame.bits)

/-- Literal initial execution: the destination at bit 104 was blank and now
contains data true; head 8 is back on the first reserved output slot. -/
theorem literal_cap_firstValueCopied :
    TM.runConfig (M := GNM)
        (GNM.initialConfig (gnPoint (encodeGN capProgram))) 1184 =
      capFirstValueCopiedConfig ∧
    (capFirstValueCopiedConfig.head : Nat) = 8 ∧
    capFirstValueCopiedConfig.state =
      ⟨(0 : Fin 1), .valuesEntry⟩ ∧
    gnFirstValueCopySteps capProgram capFirstGate = 1184 ∧
    gnValueCopyDistance capProgram capFirstGate = 24 := by
  have hg : capProgram.program.gates[0]? = some capFirstGate := by rfl
  have hvals : capProgram.inputs = true :: [] := rfl
  have hsched : gnFirstValueCopySteps capProgram capFirstGate = 1184 := by decide
  have hrun := gnCS_encodeGN_firstValueCopied_exact hg hvals
  rw [hsched] at hrun
  refine ⟨?_, rfl, rfl, hsched, by decide⟩
  refine hrun.trans ?_
  apply Configuration.ext_of_components
  · rfl
  · rfl
  · rfl

/-- A small fixture whose destination changes at physical cell 9. -/
def tinyCopyStart (b : Bool) : Configuration (M := GNM) 0 :=
  gnPendingValuesConfig 0 [] [b] [] (by decide) .valuesEntry

def tinyCopyEnd (b : Bool) : Configuration (M := GNM) 0 :=
  gnPendingValuesConfig 0 [G1Frame.data b] [] [G1Frame.data b]
    (by change 4 < GNM.tapeLength 0; decide) .valuesEntry

/-- Full literal tape equality for both source bits; no tail writer is run. -/
theorem literal_tiny_copy (b : Bool) :
    TM.runConfig (M := GNM) (tinyCopyStart b) 46 = tinyCopyEnd b := by
  exact gnCS_values_cons_exact 0 [] b [] [] (by simp) (by decide)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- Independently reduce the small machine run in the kernel, including the
changed destination cell. This uses the actual transition function. -/
theorem literal_tiny_executable :
    (TM.runConfig (M := GNM) (tinyCopyStart true) 46).state =
        ⟨(0 : Fin 1), .valuesEntry⟩ ∧
      ((TM.runConfig (M := GNM) (tinyCopyStart true) 46).head : Nat) = 4 ∧
      (tinyCopyStart true).tape ⟨9, by decide⟩ = false ∧
      (TM.runConfig (M := GNM) (tinyCopyStart true) 46).tape ⟨9, by decide⟩ = true := by
  decide +kernel

/-- A second value remains pending; it takes eight classifier/back rows to
reach its installer after the first copy, rather than a direct exit door. -/
theorem literal_two_values_handoff :
    TM.runConfig (M := GNM)
        (gnPendingValuesConfig 0 [] [true, false] [] (by decide) .valuesEntry)
        62 =
      gnPendingValuesConfig 0 [G1Frame.data true] [false] [G1Frame.data true]
        (by decide) (.install .probe .p0 .empty) := by
  have hc := gnCS_values_cons_exact 0 [] true [false] [] (by simp) (by decide)
  simp only [List.length_cons, List.length_nil, List.nil_append] at hc
  rw [show (62 : Nat) = 54 + 8 from rfl, runConfig_add, hc]
  exact gnCS_values_nonempty_handoff 0 [G1Frame.data true] false []
    [G1Frame.data true] (by decide)

/-- After a singleton copy the next four rows enter the tail seek, while both
request-tail frames at the destination remain blank. -/
theorem literal_singleton_tail_handoff :
    TM.runConfig (M := GNM) (tinyCopyStart false) 50 =
      gnCopyShuttle.cfg 0 8 (by decide)
        (frameListTape ((gnPendingValuesFrames [G1Frame.data false] []
          [G1Frame.data false]).flatMap G1Frame.bits)) (.values .seekTail .p0) := by
  rw [show (50 : Nat) = 46 + 4 from rfl, runConfig_add, literal_tiny_copy]
  exact gnCS_values_nil_tail_handoff 0 [G1Frame.data false]
    [G1Frame.data false] (by decide)

/-- Malformed values ingress still rejects through the landed classifier in
four rows, with no write. This fixture pins the E2-5a fail-closed clock. -/
def reservedCopyStart : Configuration (M := GNM) 0 :=
  gnCopyShuttle.cfg 0 0 (by decide) (frameListTape [true, true, false, true])
    .valuesEntry

theorem literal_reserved_reject :
    TM.runConfig (M := GNM) reservedCopyStart 4 =
      gnCopyShuttle.cfg 0 3 (by decide) (frameListTape [true, true, false, true])
        .reject := by
  exact gnCS_valuesEntry_reserved1101_reject_four 0 0 (by decide) _ rfl

end GNValuesCopyProbes

end Pnp3.Internal.PsubsetPpoly.TM
