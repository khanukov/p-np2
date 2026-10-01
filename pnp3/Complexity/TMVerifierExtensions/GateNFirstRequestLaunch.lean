import Complexity.TMVerifier.TuringToolkit.GateNValuesInduction

/-! GN-E2-5d Infrastructure: real first-request launch and successful return.
No commit, repeated gates, acceptance, clock adequacy or lower bound is claimed.
The semantic result indexes correctness, never the fixed finite control. -/
namespace Pnp3.Internal.PsubsetPpoly.TM
open FrameScan Encoding

theorem gnTransition_launch_rows (phase : Fin 1) (b0 b1 b2 b3 scan : Bool) :
    gnTransition phase .requestReady scan = (0, .launch .r3, scan, .left) ∧
      gnTransition phase (.launch .r3) scan =
        (0, .launch (.r2 scan), scan, .left) ∧
      gnTransition phase (.launch (.r2 b3)) scan =
        (0, .launch (.r1 scan b3), scan, .left) ∧
      gnTransition phase (.launch (.r1 b2 b3)) scan =
        (0, .launch (.r0 scan b2 b3), scan, .left) ∧
      gnTransition phase (.launch .p0) scan = (0, .reject, scan, .stay) ∧
      gnTransition phase (.launch (.p1 b0)) scan = (0, .reject, scan, .stay) ∧
      gnTransition phase (.launch (.p2 b0 b1)) scan = (0, .reject, scan, .stay) ∧
      gnTransition phase (.launch (.p3 b0 b1 b2)) scan = (0, .reject, scan, .stay) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem gnTransition_launch_decision (phase : Fin 1) :
    (∀ b1 b2 b3 scan : Bool,
      decodeG1Frame? [scan, b1, b2, b3] = some G1Frame.bof →
      gnTransition phase (.launch (.r0 b1 b2 b3)) scan =
        (0, .delegated G1M.start, scan, .stay)) ∧
    (∀ (f : G1Frame) (b1 b2 b3 scan : Bool),
      decodeG1Frame? [scan, b1, b2, b3] = some f → f ≠ G1Frame.bof →
      gnTransition phase (.launch (.r0 b1 b2 b3)) scan =
        (0, .launch .r3, scan, .left)) ∧
    (∀ b1 b2 b3 scan : Bool, decodeG1Frame? [scan, b1, b2, b3] = none →
      gnTransition phase (.launch (.r0 b1 b2 b3)) scan =
        (0, .reject, scan, .stay)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b1 b2 b3 scan h
    simp [gnTransition, gnLaunchControl, gnRewindComplete, h, gnRewindAdvance]
  · intro f b1 b2 b3 scan h hn
    cases f <;> simp_all [gnTransition, gnLaunchControl, gnRewindComplete,
      gnRewindAdvance]
  · intro b1 b2 b3 scan h
    simp [gnTransition, gnLaunchControl, gnRewindComplete, h]

def gnLaunchStopState : GNRewindMode → GNState
  | .anchor => .delegated G1M.start
  | _ => .reject

/-- Six scanner obligations proved from the active machine rows. -/
def gnLaunchScanner : ReverseFrameScanner GNState G1Frame GNRewindMode Unit where
  program := gnCS
  phase := gnCS.startPhase
  codec := g1FrameCodec
  Stop := GNRewindMode.Stop
  revAdvance := gnRewindAdvance
  revComplete := gnRewindComplete
  Reverse := GNRewindMode.Reverse
  rst3 := fun _ _ => .launch .r3
  rst2 := fun _ _ b3 => .launch (.r2 b3)
  rst1 := fun _ _ b2 b3 => .launch (.r1 b2 b3)
  rst0 := fun _ _ b1 b2 b3 => .launch (.r0 b1 b2 b3)
  stopState := fun m _ => gnLaunchStopState m
  revComplete_decode := by
    intro m f b0 b1 b2 b3 h
    simp only [gnRewindComplete]
    rw [show decodeG1Frame? [b0, b1, b2, b3] = some f from h]
  rstep_p3 := by intros; rfl
  rstep_p2 := by intros; rfl
  rstep_p1 := by intros; rfl
  rstep_p0 := by
    intro m hm _ b1 b2 b3 scan hnext
    obtain rfl := hm.eq
    cases scan <;> cases b1 <;> cases b2 <;> cases b3 <;>
      simp_all [gnCS, gnTransition, gnLaunchControl, gnRewindComplete,
        gnRewindAdvance, GNRewindMode.Stop, decodeG1Frame?]
  rstep_p0_stop := by
    intro m hm _ b1 b2 b3 scan hstop
    obtain rfl := hm.eq
    cases scan <;> cases b1 <;> cases b2 <;> cases b3 <;>
      simp_all [gnCS, gnTransition, gnLaunchControl, gnRewindComplete,
        gnRewindAdvance, GNRewindMode.Stop, gnLaunchStopState, decodeG1Frame?]

/-- Explicit complete configuration, sharing the existing phase geometry. -/
abbrev gnLaunchConfig (n h : Nat) (hh : h < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool) (q : GNState) :=
  Phased.alignedAt gnCS gnCS.startPhase n h hh tape q

private theorem launch_entry (n h : Nat) (hh : h < GNM.tapeLength n)
    (hp : 0 < h) (tape : Fin (GNM.tapeLength n) → Bool) :
    TM.runConfig (M := GNM) (gnLaunchConfig n h hh tape .requestReady) 1 =
      gnLaunchConfig n (h-1) (by omega) tape (.launch .r3) := by
  rw [runConfig_one]
  exact Phased.holdLeft gnCS gnCS.startPhase n h hh hp tape _ _ (fun _ => rfl)

/-- The no-internal-bof and room hypotheses are essential; the prefix is
arbitrary and may itself contain bof frames. All bits are preserved. -/
theorem gnCS_launch_onList_exact (n : Nat) (pre body post : List G1Frame)
    (hbody : ∀ f ∈ body, f ≠ G1Frame.bof)
    (hroom : 4 * (pre.length + body.length + 1) < GNM.tapeLength n) :
    TM.runConfig (M := GNM)
      (gnLaunchConfig n (4 * (pre.length + body.length + 1)) hroom
        (frameListTape ((pre ++ .bof :: body ++ post).flatMap G1Frame.bits))
        .requestReady) (4 * body.length + 5) =
      gnLaunchConfig n (4 * pre.length) (by omega)
        (frameListTape ((pre ++ .bof :: body ++ post).flatMap G1Frame.bits))
        (.delegated G1M.start) := by
  have hp : gnLaunchScanner.RevValidPath .scan body ∧
      gnLaunchScanner.revAdvanceList .scan body = .scan := by
    refine gnLaunchScanner.revValidPath_const (m := GNRewindMode.scan)
      trivial (fun h => h) body ?_
    intro f hf
    cases f with
    | bof => exact absurd rfl (hbody _ hf)
    | data b | output b => cases b <;> rfl
    | blank | tag | index | separator | cursor | finish | argSep | spent => rfl
  have hs := gnLaunchScanner.revScanFrames n pre .bof body post .scan () hp.1
    (by change 4 * (pre.length + body.length) + 4 < GNM.tapeLength n; omega)
  rw [hp.2] at hs
  have ha := gnLaunchScanner.revAnchorStep n (4 * pre.length)
    (by change 4 * pre.length + 4 < GNM.tapeLength n; omega)
    (frameListTape ((pre ++ .bof :: body ++ post).flatMap G1Frame.bits))
    .scan .bof () trivial trivial
    (by simpa only [List.append_assoc, List.cons_append, g1FrameCodec_bits] using
      physicalBitsAt_flatMap g1FrameCodec pre (body ++ post) .bof (by
        change 4 * pre.length + 4 < GNM.tapeLength n; omega))
  rw [show 4 * body.length + 5 = 1 + (4 * body.length + 4) by omega,
    runConfig_add, launch_entry n _ hroom (by omega), runConfig_add]
  have he : 4 * (pre.length + body.length + 1) - 1 =
      4 * (pre.length + body.length) + 3 := by omega
  simp only [he]
  change TM.runConfig (M := GNM)
    (gnLaunchConfig n (4 * (pre.length + body.length) + 3) _
      (frameListTape ((pre ++ .bof :: body ++ post).flatMap G1Frame.bits))
      (.launch .r3)) (4 * body.length) = _ at hs
  rw [hs]
  exact ha

theorem gnCS_requestReady_reserved1101_reject_five (n base : Nat)
    (hroom : base + 4 < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool)
    (hbits : physicalBitsAt hroom tape = [true, true, false, true]) :
    TM.runConfig (M := GNM)
      (gnLaunchConfig n (base+4) hroom tape .requestReady) 5 =
      gnLaunchConfig n base (by omega) tape .reject := by
  have hc : tape ⟨base, by omega⟩ = true ∧ tape ⟨base+1, by omega⟩ = true ∧
      tape ⟨base+2, by omega⟩ = false ∧ tape ⟨base+3, by omega⟩ = true := by
    simpa only [physicalBitsAt, List.cons.injEq, and_true] using hbits
  have hd : gnRewindComplete .scan (tape ⟨base, by omega⟩)
      (tape ⟨base+1, by omega⟩) (tape ⟨base+2, by omega⟩)
      (tape ⟨base+3, by omega⟩) = .reject := by
    rw [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2]; rfl
  have hs := gnLaunchScanner.revWindowStop n base hroom tape .scan () trivial
    (by change GNRewindMode.Stop (gnRewindComplete .scan _ _ _ _); rw [hd]; trivial)
  rw [show (5 : Nat) = 1+4 from rfl, runConfig_add,
    launch_entry n _ hroom (by omega)]
  simpa [gnLaunchScanner, gnLaunchStopState, hd] using hs

theorem gnCS_requestReady_reserved1101_reject_stable (n base : Nat)
    (hroom : base + 4 < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool)
    (hbits : physicalBitsAt hroom tape = [true, true, false, true]) (k : Nat) :
    TM.runConfig (M := GNM)
      (gnLaunchConfig n (base+4) hroom tape .requestReady) (5+k) =
      gnLaunchConfig n base (by omega) tape .reject := by
  rw [runConfig_add, gnCS_requestReady_reserved1101_reject_five n base hroom tape hbits]
  exact gnCS_reject_stable _ rfl k

private theorem first_lengths (r : GNProgram) (g : SLGate r.inputs.length) :
    (encodeG1 (gnFirstRequest r g)).length =
      4 * ((gnRecordFrames .cursor g).length + r.inputs.length + 2) := by
  rw [gnFirstRequest_width]
  simp [gnRecordFrames, g1RecordFrames_length, gnRecordSize]

theorem gnFirstRequestReady_geometry {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) :
    (gnFirstRequestReadyConfig r g hg).state = ⟨(0 : Fin 1), .requestReady⟩ ∧
    ((gnFirstRequestReadyConfig r g hg).head : Nat) =
      (encodeGN r).length + (encodeG1 (gnFirstRequest r g)).length ∧
    (gnFirstRequestReadyConfig r g hg).tape =
      frameListTape (encodeGN r ++ encodeG1 (gnFirstRequest r g)) ∧
    (encodeGN r).length + (encodeG1 (gnFirstRequest r g)).length <
      GNM.tapeLength (encodeGN r).length := by
  have hw := first_lengths r g
  have hn := encodeGN_length r
  have hr := gnFirstRequestReady_room hg
  refine ⟨rfl, ?_, ?_, by omega⟩
  · change 4 * (_ + _ + _ + 2) = _
    omega
  · change frameListTape ((_ ++ [G1Frame.blank]).flatMap G1Frame.bits) = _
    simpa only [g1FrameCodec_bits, encodeGN, encodeG1, List.flatMap_append] using
      (frameListTape_append_blank (L := GNM.tapeLength (encodeGN r).length)
        g1FrameCodec (encodeGNFrames r ++ encodeG1Frames (gnFirstRequest r g))
        G1Frame.blank rfl).symm

def gnFirstRequestLaunchSteps (r : GNProgram) (g : SLGate r.inputs.length) : Nat :=
  (encodeG1 (gnFirstRequest r g)).length + 1

def gnFirstLaunchSteps (r : GNProgram) (g : SLGate r.inputs.length) : Nat :=
  gnValuesRequestReadySteps r g + gnFirstRequestLaunchSteps r g

theorem gnFirstLaunchSteps_provenance (r : GNProgram) (g : SLGate r.inputs.length) :
    gnFirstRequestLaunchSteps r g = (encodeG1 (gnFirstRequest r g)).length + 1 ∧
    gnFirstLaunchSteps r g = gnValuesRequestReadySteps r g +
      ((encodeG1 (gnFirstRequest r g)).length + 1) ∧
    gnFirstLaunchSteps r g = gnValuesEntrySteps r g +
      (r.inputs.length * (8 * gnValuesTailDistance r g + 38) +
        (4 * gnValuesTailDistance r g + 20)) +
      ((encodeG1 (gnFirstRequest r g)).length + 1) ∧
    g1GateDoneSteps (gnFirstRequest r g) = g1GateResultSteps (gnFirstRequest r g) +
      (1 + g1OutputKernelSteps (gnFirstRequest r g)) := ⟨rfl, rfl, rfl, rfl⟩

private def requestBody (q : G1Request) : List G1Frame :=
  List.replicate q.tag.units .tag ++ [.argSep] ++
    List.replicate q.arg1 .index ++ [.argSep] ++
    List.replicate q.arg2 .index ++ [.separator] ++
    q.vals.map .data ++ [.output false, .finish]

private theorem request_frames (q : G1Request) :
    encodeG1Frames q = .bof :: requestBody q := by
  simp [encodeG1Frames, requestBody, List.append_assoc]

private theorem request_body_no_bof (q : G1Request) :
    ∀ f ∈ requestBody q, f ≠ G1Frame.bof := by
  intro f hf he
  subst f
  simp [requestBody] at hf

/-- Real ready endpoint to the exact dependent installed G1 start. -/
theorem gnCS_requestReady_launch_exact {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) :
    TM.runConfig (M := GNM) (gnFirstRequestReadyConfig r g hg)
      (gnFirstRequestLaunchSteps r g) = gnFirstInstalledConfig r g hg := by
  have hn := encodeGN_length r
  have hw : (encodeG1 (gnFirstRequest r g)).length =
      4 * ((requestBody (gnFirstRequest r g)).length + 1) := by
    rw [encodeG1, G1Frame.flatMap_bits_length, request_frames]
    simp
  have geom := gnFirstRequestReady_geometry hg
  have room : 4 * ((encodeGNFrames r).length +
      (requestBody (gnFirstRequest r g)).length + 1) <
      GNM.tapeLength (encodeGN r).length := by omega
  have hs := gnCS_launch_onList_exact (encodeGN r).length (encodeGNFrames r)
    (requestBody (gnFirstRequest r g)) [] (request_body_no_bof _) room
  have ht : ((encodeGNFrames r ++ G1Frame.bof :: requestBody (gnFirstRequest r g) ++
      []).flatMap G1Frame.bits) = encodeGN r ++ encodeG1 (gnFirstRequest r g) := by
    rw [List.append_nil, ← request_frames]
    exact List.flatMap_append
  rw [ht] at hs
  have hstart : gnFirstRequestReadyConfig r g hg =
      gnLaunchConfig (encodeGN r).length _ room
        (frameListTape (encodeGN r ++ encodeG1 (gnFirstRequest r g))) .requestReady := by
    apply Configuration.ext_of_components
    · exact geom.1
    · apply Fin.ext; dsimp [gnLaunchConfig, Phased.alignedAt]; omega
    · exact geom.2.2.1
  rw [hstart, show gnFirstRequestLaunchSteps r g =
      4 * (requestBody (gnFirstRequest r g)).length + 5 by
        unfold gnFirstRequestLaunchSteps; omega, hs, gnFirstInstalledConfig_eq_physical hg]
  apply Configuration.ext_of_components
  · rfl
  · apply Fin.ext; exact hn.symm
  · rfl

theorem gnCS_encodeGN_firstLaunch_exact {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) :
    TM.runConfig (M := GNM) (GNM.initialConfig (gnPoint (encodeGN r)))
      (gnFirstLaunchSteps r g) = gnFirstInstalledConfig r g hg := by
  rw [gnFirstLaunchSteps, runConfig_add, gnCS_encodeGN_valuesRequestReady_exact hg,
    gnCS_requestReady_launch_exact hg]

theorem gnCS_encodeGN_firstOutputDone_exact {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) (res : Bool)
    (hs : (gnFirstRequest r g).spec = some res) :
    TM.runConfig (M := GNM) (GNM.initialConfig (gnPoint (encodeGN r)))
      (gnFirstLaunchSteps r g + g1GateDoneSteps (gnFirstRequest r g)) =
    gnShiftConfig GNM (encodeGN r).length gnEmbed
      (GNM.initialConfig (gnPoint (encodeGN r))).tape
      (g1OutputDoneConfig (gnFirstRequest r g) res) (gnFirstRequest_room hg)
      (g1OutputDoneConfig_head_lt_gnLocalSpan (gnFirstRequest r g) res) := by
  rw [runConfig_add, gnCS_encodeGN_firstLaunch_exact hg]
  exact gnCS_gate_shift_exact _ (gnFirstRequest_canonical r g) res hs _ _

theorem gnCS_encodeGN_firstReturned_exact {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) (res : Bool)
    (hs : (gnFirstRequest r g).spec = some res) :
    TM.runConfig (M := GNM) (GNM.initialConfig (gnPoint (encodeGN r)))
      (gnFirstLaunchSteps r g + (g1GateDoneSteps (gnFirstRequest r g) + 1)) =
    gnReturnConfig res (gnShiftConfig GNM (encodeGN r).length gnEmbed
      (GNM.initialConfig (gnPoint (encodeGN r))).tape
      (g1OutputDoneConfig (gnFirstRequest r g) res) (gnFirstRequest_room hg)
      (g1OutputDoneConfig_head_lt_gnLocalSpan (gnFirstRequest r g) res)) := by
  rw [runConfig_add, gnCS_encodeGN_firstLaunch_exact hg]
  exact gnCS_gate_shift_intercept_exact _ (gnFirstRequest_canonical r g) res hs _ _

private theorem output_overlay {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) (res : Bool) :
    gnOverlayTape GNM (encodeGN r).length (gnFirstRequest_room hg)
      (g1OutputDoneConfig (gnFirstRequest r g) res)
      (GNM.initialConfig (gnPoint (encodeGN r))).tape =
    frameListTape ((encodeGNFrames r ++
      g1OutputFrames (gnFirstRequest r g) res).flatMap G1Frame.bits) := by
  have hlen : ((g1OutputFrames (gnFirstRequest r g) res).flatMap G1Frame.bits).length ≤
      gnLocalSpan (encodeG1 (gnFirstRequest r g)).length := by
    simp only [G1Frame.flatMap_bits_length, g1OutputFrames_length, gnLocalSpan,
      encodeG1_length]
    omega
  rw [List.flatMap_append]
  change _ = frameListTape (encodeGN r ++ _)
  funext i
  by_cases hi : (encodeGN r).length ≤ i.val ∧ i.val <
      (encodeGN r).length + gnLocalSpan (encodeG1 (gnFirstRequest r g)).length
  · unfold gnOverlayTape
    rw [dif_pos hi, g1OutputDoneConfig_tape]
    simp only [frameListTape, gnSourceIndex_val, List.getD]
    rw [List.getElem?_append_right hi.1]
  · unfold gnOverlayTape
    rw [dif_neg hi, gnInitialTape_eq_frameListTape]
    by_cases hl : i.val < (encodeGN r).length
    · simp only [frameListTape, List.getD]
      rw [List.getElem?_append_left hl]
    · have he : (encodeGN r ++
          (g1OutputFrames (gnFirstRequest r g) res).flatMap G1Frame.bits).length ≤
          i.val := by simp only [List.length_append]; omega
      simp only [frameListTape, List.getD]
      rw [List.getElem?_eq_none (by omega : (encodeGN r).length ≤ i.val),
        List.getElem?_eq_none he]

/-- Run-derived complete returned structure, including both exact tape forms. -/
theorem gnFirstReturned_structure {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) (res : Bool)
    (hs : (gnFirstRequest r g).spec = some res) :
    let out := TM.runConfig (M := GNM) (GNM.initialConfig (gnPoint (encodeGN r)))
      (gnFirstLaunchSteps r g + (g1GateDoneSteps (gnFirstRequest r g) + 1))
    out.state = gnReturnedQ res ∧
      (out.head : Nat) = (encodeGN r).length + g1OutputExitHead (gnFirstRequest r g) ∧
      out.tape = frameListTape ((encodeGNFrames r ++
        g1OutputFrames (gnFirstRequest r g) res).flatMap G1Frame.bits) ∧
      out.tape = gnOverlayTape GNM (encodeGN r).length (gnFirstRequest_room hg)
        (g1OutputDoneConfig (gnFirstRequest r g) res)
        (GNM.initialConfig (gnPoint (encodeGN r))).tape := by
  dsimp only
  rw [gnCS_encodeGN_firstReturned_exact hg res hs]
  exact ⟨rfl, rfl, output_overlay hg res, rfl⟩

end Pnp3.Internal.PsubsetPpoly.TM
