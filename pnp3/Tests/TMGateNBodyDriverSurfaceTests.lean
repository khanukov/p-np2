import Complexity.TMVerifier.TuringToolkit.GateNBodyDriver

/-!
# GN-E2-3b body-driver surface (2026-09-20)

Definition pins and one direct full-proposition wrapper for every public
theorem of `GateNBodyDriver`.  Private induction glue is deliberately excluded.
A bare `#check @name` pins only the name, so every substantive signature is
restated in full here.
-/

namespace Pnp3.Tests.TMGateNBodyDriverSurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.Encoding
open Pnp3.Internal.PsubsetPpoly.TM.FrameScan
open Pnp3.Internal.PsubsetPpoly.TM.GNFixedDelegateProbes

#check @gnGateBodyFrames
#check @gnGateBodyTail
#check @gnFirstRecordTail
#check @gnBodyDriverSteps
#check @gnFirstRecordDoneSteps
#check @gnFirstRecordDoneConfig
#check @GNBodyDriverProbes.oneConstFalseRecordDoneConfig
#check @gnGateBodyFrames_cons
#check @gnRecordFrames_cursor_split
#check @gnGateBodyFrames_body
#check @gnGateBodyFrames_map_image
#check @gnFirstRecordMiddle_split
#check @gnFirstRecordTail_admissible
#check @gnBodyDriverSteps_provenance
#check @gnBodyDriver_room_start
#check @gnCS_bodyDriver_recordDone_exact
#check @gnFirstRecordDoneSteps_provenance
#check @gnCS_encodeGN_firstRecordDone_exact
#check @gnFirstRecordDoneConfig_structure
#check @gnFirstRecordDoneSteps_le_gnClock
#check @GNBodyDriverProbes.literal_oneConstFalse_recordDone

theorem check_gnGateBodyFrames_cons {n : Nat} (g : SLGate n) :
    gnGateBodyFrames g = G1Frame.tag :: gnGateBodyTail g :=
  gnGateBodyFrames_cons g

theorem check_gnRecordFrames_cursor_split {n : Nat} (g : SLGate n) :
    gnRecordFrames .cursor g =
      G1Frame.cursor :: gnGateBodyFrames g ++ [G1Frame.finish] :=
  gnRecordFrames_cursor_split g

theorem check_gnGateBodyFrames_body {n : Nat} (g : SLGate n) :
    ∀ frame ∈ gnGateBodyFrames g, GNInstallBody frame :=
  gnGateBodyFrames_body g

theorem check_gnGateBodyFrames_map_image {n : Nat} (g : SLGate n) :
    (gnGateBodyFrames g).map gnInstallImage = gnGateBodyFrames g :=
  gnGateBodyFrames_map_image g

theorem check_gnFirstRecordMiddle_split {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    gnFirstRecordMiddle r =
      gnGateBodyFrames g ++ G1Frame.finish :: gnFirstRecordTail r :=
  gnFirstRecordMiddle_split hg

theorem check_gnFirstRecordTail_admissible {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    ∀ frame ∈ gnFirstRecordTail r, GNInstallAdmissible frame :=
  gnFirstRecordTail_admissible hg

theorem check_gnBodyDriverSteps_provenance (rounds distance : Nat) :
    gnBodyDriverSteps rounds distance =
        rounds * (8 * distance + 30) + (8 * distance + 31) ∧
      gnBodyDriverSteps 0 distance = gnBodyTerminalSteps distance ∧
      gnBodyDriverSteps (rounds + 1) distance =
        gnBodyRoundSteps distance + gnBodyDriverSteps rounds distance :=
  gnBodyDriverSteps_provenance rounds distance

theorem check_gnBodyDriver_room_start {n : Nat} {fixed done : List G1Frame}
    {current : G1Frame} {body tail seed : List G1Frame}
    (hroom : 4 * ((fixed ++ done).length + (current :: body).length +
      (gnBodyRoundMiddle done (body ++ G1Frame.finish :: tail) seed).length +
        2) < GNM.tapeLength n) :
    4 * ((fixed ++ done).length +
      (gnBodyRoundMiddle done (body ++ G1Frame.finish :: tail) seed).length +
        2) < GNM.tapeLength n :=
  gnBodyDriver_room_start hroom

theorem check_gnCS_bodyDriver_recordDone_exact (n : Nat)
    (fixed done : List G1Frame) (current : G1Frame)
    (body tail seed : List G1Frame) (previous : GNInstallAux)
    (hprevious : GNInstallExitContinue previous)
    (hcurrent : GNInstallBody current)
    (hbody : ∀ frame ∈ body, GNInstallBody frame)
    (hmiddle : ∀ frame ∈ tail ++ seed ++ done.map gnInstallImage,
      GNInstallAdmissible frame)
    (hroom : 4 * ((fixed ++ done).length + (current :: body).length +
      (gnBodyRoundMiddle done (body ++ G1Frame.finish :: tail) seed).length +
        2) < GNM.tapeLength n) :
    TM.runConfig (M := GNM)
        (gnBodyRoundConfig n fixed done current (body ++ G1Frame.finish :: tail)
          seed [] previous (gnBodyDriver_room_start hroom))
        (gnBodyDriverSteps (current :: body).length
          (gnBodyRoundMiddle done (body ++ G1Frame.finish :: tail)
            seed).length) =
      gnCopyShuttle.cfg n (4 * (fixed ++ (done ++ current :: body)).length + 4)
        (by
          change 4 * (fixed ++ (done ++ current :: body)).length + 4 <
            GNM.tapeLength n
          have h := hroom
          simp only [List.length_append, List.length_cons] at h ⊢
          omega)
        (frameListTape
          (((fixed ++ (done ++ current :: body)) ++ G1Frame.finish ::
            gnBodyRoundMiddle (done ++ current :: body) tail seed ++
              G1Frame.separator :: G1Frame.blank :: []).flatMap G1Frame.bits))
        .recordDone :=
  gnCS_bodyDriver_recordDone_exact n fixed done current body tail seed previous
    hprevious hcurrent hbody hmiddle hroom

theorem check_gnFirstRecordDoneSteps_provenance (r : GNProgram)
    (g : SLGate r.inputs.length) :
    gnFirstRecordDoneSteps r g =
      gnBofSeedSteps r +
        ((gnGateBodyFrames g).length *
            (8 * (gnFirstRecordMiddle r).length + 30) +
          (8 * (gnFirstRecordMiddle r).length + 31)) :=
  gnFirstRecordDoneSteps_provenance r g

theorem check_gnCS_encodeGN_firstRecordDone_exact {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    TM.runConfig (M := GNM)
        (GNM.initialConfig (gnPoint (encodeGN r)))
        (gnFirstRecordDoneSteps r g) =
      gnFirstRecordDoneConfig r g hg :=
  gnCS_encodeGN_firstRecordDone_exact hg

theorem check_gnFirstRecordDoneConfig_structure {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    (gnFirstRecordDoneConfig r g hg).state =
        ⟨(0 : Fin 1), GNState.recordDone⟩ ∧
      ((gnFirstRecordDoneConfig r g hg).head : Nat) =
        4 * (gnRecordsStart r + gnRecordSize (gnGateFields g)) ∧
      (gnFirstRecordDoneConfig r g hg).tape =
        frameListTape
          ((encodeGNFrames r ++ (gnRecordFrames .cursor g).map gnInstallImage ++
            [G1Frame.blank]).flatMap G1Frame.bits) ∧
      gnLocatePrefix r ++ G1Frame.cursor :: gnFirstRecordMiddle r =
        encodeGNFrames r ∧
      (gnRecordFrames .cursor g).map gnInstallImage =
        G1Frame.bof :: gnGateBodyFrames g ++ [G1Frame.separator] ∧
      (gnRecordFrames .cursor g).map gnInstallImage ++ r.inputs.map .data =
        g1PrefixFrames (gnFirstRequest r g) ∧
      (gnFirstRequest r g).spec =
        g.compute (fun i => r.inputs[i.val]'(by omega)) [] :=
  gnFirstRecordDoneConfig_structure hg

theorem check_gnFirstRecordDoneSteps_le_gnClock {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g) :
    gnFirstRecordDoneSteps r g ≤ gnClock (encodeGN r).length :=
  gnFirstRecordDoneSteps_le_gnClock hg

theorem check_literal_oneConstFalse_recordDone :
    TM.runConfig (M := GNM)
        (GNM.initialConfig (gnPoint (encodeGN oneConstFalseProgram))) 659 =
      GNBodyDriverProbes.oneConstFalseRecordDoneConfig ∧
    (GNBodyDriverProbes.oneConstFalseRecordDoneConfig.head : Nat) = 36 ∧
    GNBodyDriverProbes.oneConstFalseRecordDoneConfig.state =
      ⟨(0 : Fin 1), GNState.recordDone⟩ ∧
    GNBodyDriverProbes.oneConstFalseRecordDoneConfig.tape = frameListTape
      ([G1Frame.bof, .output false, .separator, .cursor, .tag, .tag,
        .argSep, .argSep, .finish, .separator, .output false, .finish,
        .bof, .tag, .tag, .argSep, .argSep, .separator,
        .blank].flatMap G1Frame.bits) :=
  GNBodyDriverProbes.literal_oneConstFalse_recordDone

end Pnp3.Tests.TMGateNBodyDriverSurface
