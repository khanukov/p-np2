import Complexity.TMVerifier.TuringToolkit.GateNScratchBootstrap

/-!
# GN-E2-2 live cursor boundary shuttle (2026-09-02)

**Progress classification: infrastructure, not P-vs-NP mainline progress.**

This module activates exactly the stationary `firstRecord` door and composes
it with one source-restoring shuttle.  The source cursor is restored, the
first scratch frame becomes `bof`, the next scratch frame remains blank, and
execution stops in payload-preserving
`gnInstallExitState (.carried .cursor)` at p0 of the first record-body frame.

There is no body driver or body copy, no live finish-to-separator execution,
no E2-3a exit activation or record-done dispatch, no values/tail writer, no launch,
delegation, commit, loop, total installer clock, verdict, or acceptance.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

open Pnp3.Internal.PsubsetPpoly.TM.FrameScan
open Encoding

/-! ## Pure prefix anchor and exact configurations -/

/-- Mapping the selected cursor-marked record gives exactly the G1 request
prefix through its separator; the current values are the remaining suffix. -/
theorem gnFirstRecord_image_request_prefix (r : GNProgram)
    (g : SLGate r.inputs.length) :
    (gnRecordFrames .cursor g).map gnInstallImage ++ r.inputs.map .data =
      g1PrefixFrames (gnFirstRequest r g) := by
  cases g with
  | input i => simp [gnRecordFrames, g1RecordFrames, gnInstallImage,
      gnFirstRequest, gnFieldRequest, gnGateFields, g1PrefixFrames,
      List.append_assoc]
  | const b => cases b <;>
      simp [gnRecordFrames, g1RecordFrames, gnInstallImage,
        gnFirstRequest, gnFieldRequest, gnGateFields, g1PrefixFrames,
        List.append_assoc]
  | notGate k => simp [gnRecordFrames, g1RecordFrames, gnInstallImage,
      gnFirstRequest, gnFieldRequest, gnGateFields, g1PrefixFrames,
      List.append_assoc]
  | andGate k l => simp [gnRecordFrames, g1RecordFrames, gnInstallImage,
      gnFirstRequest, gnFieldRequest, gnGateFields, g1PrefixFrames,
      List.append_assoc]
  | orGate k l => simp [gnRecordFrames, g1RecordFrames, gnInstallImage,
      gnFirstRequest, gnFieldRequest, gnGateFields, g1PrefixFrames,
      List.append_assoc]

/-- Exact post-door configuration, still on cursor p0 with unchanged tape. -/
def gnFirstRecordProbeConfig (r : GNProgram) (g : SLGate r.inputs.length)
    (hg : r.program.gates[0]? = some g) :
    Configuration (M := GNM) (encodeGN r).length where
  state := ⟨(0 : Fin 1), .install .probe .p0 .empty⟩
  head := (gnFirstRecordConfig r g hg).head
  tape := (gnFirstRecordConfig r g hg).tape

/-- Exact E2-2 endpoint.  Its list presentation pins the restored cursor,
the unchanged GN word, the first scratch `bof`, and the following blank. -/
def gnBofSeedConfig (r : GNProgram) (g : SLGate r.inputs.length)
    (hg : r.program.gates[0]? = some g) :
    Configuration (M := GNM) (encodeGN r).length where
  state := ⟨(0 : Fin 1), gnInstallExitState (.carried .cursor)⟩
  head := ⟨4 * (gnRecordsStart r + 1), by
    have hs := encodeGNFrames_firstRecord_split hg
    have hlt : 4 * (gnRecordsStart r + 1) < (encodeGN r).length := by
      rw [encodeGN_length, hs.1]
      simp only [List.length_append, List.length_cons, List.length_nil]
      rw [hs.2.1]
      omega
    change 4 * (gnRecordsStart r + 1) <
      (encodeGN r).length + gnClock (encodeGN r).length + 1
    omega⟩
  tape := frameListTape
    ((gnLocatePrefix r ++ G1Frame.cursor :: gnFirstRecordMiddle r ++
      [G1Frame.bof, G1Frame.blank]).flatMap G1Frame.bits)

/-- The newly activated stationary door is exact and tape preserving. -/
theorem gnCS_firstRecord_to_probe_exact (r : GNProgram)
    (g : SLGate r.inputs.length) (hg : r.program.gates[0]? = some g) :
    TM.runConfig (M := GNM) (gnFirstRecordConfig r g hg) 1 =
      gnFirstRecordProbeConfig r g hg := by
  let n := (encodeGN r).length
  let h := 4 * gnRecordsStart r
  let tape := (GNM.initialConfig (gnPoint (encodeGN r))).tape
  have hh : h < GNM.tapeLength n := by
    change 4 * gnRecordsStart r < n + gnClock n + 1
    have hs := encodeGNFrames_firstRecord_split hg
    have hlt : 4 * gnRecordsStart r < n := by
      rw [show n = (encodeGN r).length from rfl, encodeGN_length, hs.1]
      simp only [List.length_append, List.length_cons, List.length_nil]
      rw [hs.2.1]
      omega
    omega
  have hstep := Phased.stepStay gnCS gnCS.startPhase n h hh tape
    .firstRecord (.install .probe .p0 .empty) (tape ⟨h, hh⟩)
    (gnTransition_boundary_rows gnCS.startPhase _).1
  rw [writeCell_self] at hstep
  rw [runConfig_one]
  simpa [n, h, tape, gnFirstRecordConfig, gnFirstRecordProbeConfig,
    gnFirstRecordQ] using hstep

/-! ## One live cursor shuttle -/

/-- Door plus one shuttle schedule; the `8d+29` term is inherited from the
generic source-restoring shuttle kernel. -/
def gnCursorSeedSteps (r : GNProgram) : Nat :=
  1 + (8 * (gnFirstRecordMiddle r).length + 29)

/-- Full real-initial schedule through the E2-2 seed endpoint. -/
def gnBofSeedSteps (r : GNProgram) : Nat :=
  gnFirstRecordSteps r + gnCursorSeedSteps r

theorem gnBofSeedSteps_provenance (r : GNProgram) :
    gnBofSeedSteps r =
      ((encodeGN r).length + 9) +
        (1 + 4 * (gnFirstRecordMiddle r).length + 4) +
        (1 + (8 * (gnFirstRecordMiddle r).length + 29)) := by
  simp [gnBofSeedSteps, gnCursorSeedSteps, gnFirstRecordSteps,
    gnValidateSteps, gnFirstRecordLocateSteps]

private theorem gnFirstRecordProbe_tape_explicit {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    (gnFirstRecordProbeConfig r g hg).tape =
      frameListTape
        ((gnLocatePrefix r ++ G1Frame.cursor :: gnFirstRecordMiddle r ++
          [G1Frame.blank, G1Frame.blank]).flatMap G1Frame.bits) := by
  have hh := gnFirstRecord_copyShuttle_handoff hg
  change (gnFirstRecordConfig r g hg).tape = _
  rw [← hh.2.2.2]
  simpa only [List.append_assoc, g1FrameCodec_bits] using
    (frameListTape_append_blank
      (L := GNM.tapeLength (encodeGN r).length) g1FrameCodec
      ((gnLocatePrefix r ++ G1Frame.cursor :: gnFirstRecordMiddle r) ++
        [G1Frame.blank]) G1Frame.blank rfl)

/-- Local exact E2-2 capstone: one door row followed by the concrete shuttle
schedule, stopping at the dormant installer exit. -/
theorem gnCS_firstRecord_to_bofSeed_exact {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    TM.runConfig (M := GNM) (gnFirstRecordConfig r g hg)
        (gnCursorSeedSteps r) = gnBofSeedConfig r g hg := by
  have hh := gnFirstRecord_copyShuttle_handoff hg
  have hshuttle := gnCS_copyShuttle_nextBlank (encodeGN r).length
    (gnLocatePrefix r) .cursor (gnFirstRecordMiddle r) [] .empty
    hh.1 hh.2.1 hh.2.2.1
  have hprobe : gnFirstRecordProbeConfig r g hg =
      gnCopyShuttle.cfg (encodeGN r).length
        (4 * (gnLocatePrefix r).length) (by
          change 4 * (gnLocatePrefix r).length <
            GNM.tapeLength (encodeGN r).length
          omega)
        (frameListTape
          ((gnLocatePrefix r ++ G1Frame.cursor :: gnFirstRecordMiddle r ++
            [G1Frame.blank, G1Frame.blank]).flatMap G1Frame.bits))
        (.install .probe .p0 .empty) := by
    apply Configuration.ext_of_components
    · rfl
    · apply Fin.ext
      have hpre := (encodeGNFrames_firstRecord_split hg).2.1
      change 4 * gnRecordsStart r = 4 * (gnLocatePrefix r).length
      omega
    · exact gnFirstRecordProbe_tape_explicit hg
  have hseed :
      gnCopyShuttle.cfg (encodeGN r).length
        (4 * (gnLocatePrefix r).length + 4) (by
          change 4 * (gnLocatePrefix r).length + 4 <
            GNM.tapeLength (encodeGN r).length
          omega)
        (frameListTape
          ((gnLocatePrefix r ++ G1Frame.cursor :: gnFirstRecordMiddle r ++
            [G1Frame.bof, G1Frame.blank]).flatMap G1Frame.bits))
        (gnInstallExitState (.carried .cursor)) =
      gnBofSeedConfig r g hg := by
    apply Configuration.ext_of_components
    · rfl
    · apply Fin.ext
      have hpre := (encodeGNFrames_firstRecord_split hg).2.1
      change 4 * (gnLocatePrefix r).length + 4 =
        4 * (gnRecordsStart r + 1)
      omega
    · rfl
  have hshuttle' := hshuttle
  simp only [gnInstallImage] at hshuttle'
  rw [gnCursorSeedSteps, runConfig_add, gnCS_firstRecord_to_probe_exact,
    hprobe]
  exact hshuttle'.trans hseed

/-- Exact real-initial composition through validation, locator, door, and the
single cursor shuttle. -/
theorem gnCS_encodeGN_bofSeed_exact {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    TM.runConfig (M := GNM)
        (GNM.initialConfig (gnPoint (encodeGN r))) (gnBofSeedSteps r) =
      gnBofSeedConfig r g hg := by
  rw [gnBofSeedSteps, runConfig_add, gnCS_encodeGN_firstRecord r g hg,
    gnCS_firstRecord_to_bofSeed_exact hg]

/-! ## Exact endpoint and E2-3 handoff -/

/-- Complete seed projections and exact list tape.  The source portion is the
original encoded GN word; only the first scratch frame is appended as `bof`. -/
theorem gnBofSeedConfig_structure {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    (gnBofSeedConfig r g hg).state =
        ⟨(0 : Fin 1), gnInstallExitState (.carried .cursor)⟩ ∧
      ((gnBofSeedConfig r g hg).head : Nat) = 4 * (gnRecordsStart r + 1) ∧
      (gnBofSeedConfig r g hg).tape = frameListTape
        ((gnLocatePrefix r ++ G1Frame.cursor :: gnFirstRecordMiddle r ++
          [G1Frame.bof, G1Frame.blank]).flatMap G1Frame.bits) ∧
      gnLocatePrefix r ++ G1Frame.cursor :: gnFirstRecordMiddle r =
        encodeGNFrames r := by
  exact ⟨rfl, rfl, rfl, by
    simpa [gnFirstRecordMiddle, List.append_assoc] using
      (encodeGNFrames_firstRecord_split hg).1.symm⟩

/-- Frames traversed by E2-3's next ordinary-body shuttle. -/
def gnFirstBodyMiddle (r : GNProgram) : List G1Frame :=
  (gnFirstRecordMiddle r).drop 1 ++ [.bof]

/-- The exact, unexecuted E2-3 handoff: first body frame `tag`, complete
source/middle/frontier tape split, admissibility, and physical room. -/
theorem gnBofSeed_firstBody_handoff {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    gnFirstRecordMiddle r = G1Frame.tag :: (gnFirstRecordMiddle r).drop 1 ∧
      (gnBofSeedConfig r g hg).tape = frameListTape
        (((gnLocatePrefix r ++ [G1Frame.cursor]) ++
          G1Frame.tag :: gnFirstBodyMiddle r ++ [G1Frame.blank]).flatMap
            G1Frame.bits) ∧
      GNInstallBody G1Frame.tag ∧
      (∀ frame ∈ gnFirstBodyMiddle r, GNInstallAdmissible frame) ∧
      4 * ((gnLocatePrefix r ++ [G1Frame.cursor]).length +
        (gnFirstBodyMiddle r).length + 2) <
          GNM.tapeLength (encodeGN r).length := by
  have hs := encodeGNFrames_firstRecord_split hg
  have hfirst : gnFirstRecordMiddle r =
      G1Frame.tag :: (gnFirstRecordMiddle r).drop 1 := by
    rcases r with ⟨inputs, ⟨gates⟩⟩
    cases gates with
    | nil => simp at hg
    | cons first rest =>
        simp at hg
        subst g
        cases first <;>
          simp [gnFirstRecordMiddle, gnFirstRecordInner, gnRecordsFrames,
            gnFieldRecordsFrames, g1RecordFrames, gnGateFields, G1Tag.units]
  have hmiddle : ∀ frame ∈ gnFirstBodyMiddle r,
      GNInstallAdmissible frame := by
    intro frame hframe
    rw [gnFirstBodyMiddle, List.mem_append] at hframe
    rcases hframe with hframe | hframe
    · exact (gnFirstRecord_copyShuttle_handoff hg).2.1 frame
        (List.mem_of_mem_drop hframe)
    · simp at hframe
      subst frame
      simp [GNInstallAdmissible]
  have hshape : encodeGNFrames r =
      gnLocatePrefix r ++ G1Frame.cursor :: gnFirstRecordMiddle r := by
    simpa [gnFirstRecordMiddle, List.append_assoc] using hs.1
  have hn : (encodeGN r).length =
      4 * ((gnLocatePrefix r).length + (gnFirstRecordMiddle r).length + 1) := by
    rw [encodeGN_length, hshape]
    simp [Nat.add_assoc]
  have hroom : 4 * ((gnLocatePrefix r ++ [G1Frame.cursor]).length +
      (gnFirstBodyMiddle r).length + 2) <
      GNM.tapeLength (encodeGN r).length := by
    change 4 * ((gnLocatePrefix r ++ [G1Frame.cursor]).length +
      (gnFirstBodyMiddle r).length + 2) <
      (encodeGN r).length + gnClock (encodeGN r).length + 1
    have hlen : (gnFirstBodyMiddle r).length =
        (gnFirstRecordMiddle r).length := by
      rw [gnFirstBodyMiddle, List.length_append, List.length_singleton]
      have hpos : 0 < (gnFirstRecordMiddle r).length := by rw [hfirst]; simp
      simp
      omega
    simp only [List.length_append, List.length_singleton]
    have hclock : 8 < gnClock (encodeGN r).length := by
      simp [gnClock, g1Clock]
    omega
  refine ⟨hfirst, ?_, by simp [GNInstallBody], hmiddle, hroom⟩
  rw [gnBofSeedConfig]
  rw [hfirst]
  simp [gnFirstBodyMiddle, List.append_assoc]

/-- Scoped only to validation, locator, the door, and one boundary shuttle;
this is not a total installer or multigate clock theorem. -/
theorem gnBofSeedSteps_le_gnClock {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    gnBofSeedSteps r ≤ gnClock (encodeGN r).length := by
  let N := (encodeGN r).length
  have hs := encodeGNFrames_firstRecord_split hg
  have hn : N = 4 * ((gnLocatePrefix r).length +
      (gnFirstRecordMiddle r).length + 1) := by
    rw [show N = (encodeGN r).length from rfl, encodeGN_length, hs.1]
    simp [gnFirstRecordMiddle, Nat.add_assoc]
  have hsquare : N + 1 ≤ (N + 1) ^ 2 := by
    rw [pow_two]
    exact Nat.le_mul_of_pos_left _ (by omega)
  change ((N + 9) + (1 + 4 * (gnFirstRecordMiddle r).length + 4)) +
      (1 + (8 * (gnFirstRecordMiddle r).length + 29)) ≤
    512 * (N + 1) ^ 2 + 512
  omega

/-! ## Genuine post-door rejection -/

private theorem gnCS_probe_reserved1101_reject_four (n base : Nat)
    (hsafe : base + 4 < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool)
    (hbits : physicalBitsAt hsafe tape = [true, true, false, true]) :
    TM.runConfig (M := GNM)
        (Phased.alignedAt gnCS gnCS.startPhase n base (by
          change base < GNM.tapeLength n
          omega) tape
          (.install .probe .p0 .empty)) 4 =
      Phased.alignedAt gnCS gnCS.startPhase n (base + 3) (by
        change base + 3 < GNM.tapeLength n
        omega) tape
        .reject := by
  have hmachine : (Phased.machine gnCS).tapeLength n = GNM.tapeLength n := rfl
  have hcells :
      tape ⟨base, by omega⟩ = true ∧
        tape ⟨base + 1, by omega⟩ = true ∧
        tape ⟨base + 2, by omega⟩ = false ∧
        tape ⟨base + 3, by omega⟩ = true := by
    simpa only [physicalBitsAt, List.cons.injEq, and_true] using hbits
  rcases hcells with ⟨h0, h1, h2, h3⟩
  show TM.runConfig (M := GNM) _ (1 + 1 + 1 + 1) = _
  rw [runConfig_add, runConfig_add, runConfig_add]
  simp only [runConfig_one]
  have s0 : TM.stepConfig (M := GNM)
      (Phased.alignedAt gnCS gnCS.startPhase n base (by omega) tape
        (.install .probe .p0 .empty)) =
      Phased.alignedAt gnCS gnCS.startPhase n (base + 1) (by omega) tape
        (.install .probe (.p1 true) .empty) := by
    have h := Phased.stepRight gnCS gnCS.startPhase n base
      (by rw [hmachine]; omega) (by rw [hmachine]; omega) tape
      (.install .probe .p0 .empty)
      (.install .probe (.p1 (tape ⟨base, by omega⟩)) .empty)
      (tape ⟨base, by omega⟩) (by rfl)
    rw [writeCell_self] at h
    simpa only [h0] using h
  have s1 : TM.stepConfig (M := GNM)
      (Phased.alignedAt gnCS gnCS.startPhase n (base + 1) (by omega) tape
        (.install .probe (.p1 true) .empty)) =
      Phased.alignedAt gnCS gnCS.startPhase n (base + 2) (by omega) tape
        (.install .probe (.p2 true true) .empty) := by
    have h := Phased.stepRight gnCS gnCS.startPhase n (base + 1)
      (by rw [hmachine]; omega) (by rw [hmachine]; omega) tape
      (.install .probe (.p1 true) .empty)
      (.install .probe (.p2 true (tape ⟨base + 1, by omega⟩)) .empty)
      (tape ⟨base + 1, by omega⟩) (by rfl)
    rw [writeCell_self] at h
    simpa only [h1] using h
  have s2 : TM.stepConfig (M := GNM)
      (Phased.alignedAt gnCS gnCS.startPhase n (base + 2) (by omega) tape
        (.install .probe (.p2 true true) .empty)) =
      Phased.alignedAt gnCS gnCS.startPhase n (base + 3) (by omega) tape
        (.install .probe (.p3 true true false) .empty) := by
    have h := Phased.stepRight gnCS gnCS.startPhase n (base + 2)
      (by rw [hmachine]; omega) (by rw [hmachine]; omega) tape
      (.install .probe (.p2 true true) .empty)
      (.install .probe (.p3 true true (tape ⟨base + 2, by omega⟩)) .empty)
      (tape ⟨base + 2, by omega⟩) (by rfl)
    rw [writeCell_self] at h
    simpa only [h2] using h
  have s3 : TM.stepConfig (M := GNM)
      (Phased.alignedAt gnCS gnCS.startPhase n (base + 3) (by omega) tape
        (.install .probe (.p3 true true false) .empty)) =
      Phased.alignedAt gnCS gnCS.startPhase n (base + 3) (by omega) tape
        .reject := by
    have h := Phased.stepStay gnCS gnCS.startPhase n (base + 3)
      (by rw [hmachine]; omega) tape
      (.install .probe (.p3 true true false) .empty) .reject
      (tape ⟨base + 3, by omega⟩) (by
        rw [h3]
        rfl)
    rw [writeCell_self] at h
    simpa only using h
  rw [s0, s1, s2, s3]

/-- Reserved `1101` genuinely rejects after the live door: one stationary
door row plus four concrete probe rows. -/
theorem gnCS_firstRecord_reserved1101_reject_five (n base : Nat)
    (hsafe : base + 4 < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool)
    (hbits : physicalBitsAt hsafe tape = [true, true, false, true]) :
    TM.runConfig (M := GNM)
        (Phased.alignedAt gnCS gnCS.startPhase n base (by
          change base < GNM.tapeLength n
          omega) tape
          .firstRecord) 5 =
      Phased.alignedAt gnCS gnCS.startPhase n (base + 3) (by
        change base + 3 < GNM.tapeLength n
        omega) tape
        .reject := by
  have hmachine : (Phased.machine gnCS).tapeLength n = GNM.tapeLength n := rfl
  have hdoor := Phased.stepStay gnCS gnCS.startPhase n base
    (by rw [hmachine]; omega) tape
    .firstRecord (.install .probe .p0 .empty) (tape ⟨base, by omega⟩)
    (gnTransition_boundary_rows gnCS.startPhase _).1
  rw [writeCell_self] at hdoor
  show TM.runConfig (M := GNM) _ (1 + 4) = _
  rw [runConfig_add, runConfig_one, hdoor,
    gnCS_probe_reserved1101_reject_four n base hsafe tape hbits]

/-- Stable reject padding after the genuine five-row post-door failure. -/
theorem gnCS_firstRecord_reserved1101_reject_stable (n base : Nat)
    (hsafe : base + 4 < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool)
    (hbits : physicalBitsAt hsafe tape = [true, true, false, true]) (k : Nat) :
    TM.runConfig (M := GNM)
        (Phased.alignedAt gnCS gnCS.startPhase n base (by
          change base < GNM.tapeLength n
          omega) tape
          .firstRecord) (5 + k) =
      Phased.alignedAt gnCS gnCS.startPhase n (base + 3) (by
        change base + 3 < GNM.tapeLength n
        omega) tape
        .reject := by
  rw [runConfig_add,
    gnCS_firstRecord_reserved1101_reject_five n base hsafe tape hbits]
  exact gnCS_reject_stable _ rfl k

namespace GNBoundaryShuttleProbes

open GNFixedDelegateProbes

/-- Kernel-confirmed live capstone: 188 rows total, ending at first-body p0,
physical head 16. -/
theorem literal_oneConstFalse_bofSeed :
    TM.runConfig (M := GNM)
        (GNM.initialConfig (gnPoint (encodeGN oneConstFalseProgram))) 188 =
      gnBofSeedConfig oneConstFalseProgram
        (SLGate.const false : SLGate 0) (by rfl) ∧
    ((gnBofSeedConfig oneConstFalseProgram
      (SLGate.const false : SLGate 0) (by rfl)).head : Nat) = 16 := by
  have hg : oneConstFalseProgram.program.gates[0]? =
      some (SLGate.const false : SLGate 0) := by rfl
  have hrun := gnCS_encodeGN_bofSeed_exact hg
  have hsched : gnBofSeedSteps oneConstFalseProgram = 188 := by decide
  rw [hsched] at hrun
  exact ⟨by simpa only using hrun, by decide⟩

end GNBoundaryShuttleProbes

end Pnp3.Internal.PsubsetPpoly.TM
