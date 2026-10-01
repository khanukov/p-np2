import Complexity.TMVerifier.TuringToolkit.GateNValuesInduction

/-! GN-E2-5c Infrastructure: named full-proposition surfaces for every public
execution, clock and literal theorem, including the existing writer interface.
These restatements pin all premises and complete runConfig conclusions. -/
namespace Pnp3.Tests.TMGateNValuesInductionSurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.FrameScan
open Pnp3.Internal.PsubsetPpoly.TM.Encoding
open Pnp3.Internal.PsubsetPpoly.TM.GNEncodingExamples
open Pnp3.Internal.PsubsetPpoly.TM.GNValuesCopyProbes
open Pnp3.Internal.PsubsetPpoly.TM.GNValuesInductionProbes

#check @gnValuesListSteps
#check @gnValuesListReadyConfig
#check @gnValuesListMiddle
#check @gnValuesRequestReadySteps
#check @twoValuesStart
#check @twoValuesReady
#check @capValuesReady

theorem check_gnCS_values_outputFalse_tail_exact :
    ∀ (n : Nat) (pre middle : List G1Frame)
    (hmiddle : ∀ f ∈ middle, GNInstallAdmissible f)
    (hroom : 4 * (pre.length + middle.length + 3) < GNM.tapeLength n),
    TM.runConfig (M := GNM)
        (gnCopyShuttle.cfg n (4 * pre.length) (by
          change 4 * pre.length < GNM.tapeLength n; omega)
          (frameListTape ((pre ++ G1Frame.output false :: middle ++
            [G1Frame.blank, G1Frame.blank]).flatMap G1Frame.bits))
          .valuesEntry) (4 * middle.length + 20) =
      gnCopyShuttle.cfg n (4 * (pre.length + middle.length + 3)) hroom
        (frameListTape ((pre ++ G1Frame.output false :: middle ++
          [G1Frame.output false, G1Frame.finish, G1Frame.blank]).flatMap
            G1Frame.bits)) .requestReady :=
  @Pnp3.Internal.PsubsetPpoly.TM.gnCS_values_outputFalse_tail_exact

theorem check_gnValuesListSteps_cons :
    ∀ (b : Bool) (bs : List Bool)
    (middle : List G1Frame),
    gnValuesListSteps (b :: bs) middle =
      (8 * (bs.length + 1 + middle.length) + 38) +
        gnValuesListSteps bs (middle ++ [G1Frame.data b]) :=
  @Pnp3.Internal.PsubsetPpoly.TM.gnValuesListSteps_cons

theorem check_gnCS_values_list_exact :
    ∀ (n : Nat) (pre : List G1Frame)
    (values : List Bool) (middle : List G1Frame)
    (hmiddle : ∀ f ∈ middle, GNInstallAdmissible f)
    (hroom : 4 * (pre.length + 2 * values.length + middle.length + 3) <
      GNM.tapeLength n),
    TM.runConfig (M := GNM)
        (gnPendingValuesConfig n pre values middle (by omega) .valuesEntry)
        (gnValuesListSteps values middle) =
      gnPendingValuesConfig n (pre ++ values.map G1Frame.data) []
        (middle ++ values.map G1Frame.data) (by
          simp only [List.length_append, List.length_map]; omega) .valuesEntry :=
  @Pnp3.Internal.PsubsetPpoly.TM.gnCS_values_list_exact

theorem check_gnCS_values_list_requestReady_exact :
    ∀ (n : Nat) (pre : List G1Frame)
    (values : List Bool) (middle : List G1Frame)
    (hmiddle : ∀ f ∈ middle, GNInstallAdmissible f)
    (hroom : 4 * (pre.length + 2 * values.length + middle.length + 3) <
      GNM.tapeLength n),
    TM.runConfig (M := GNM)
        (gnPendingValuesConfig n pre values middle (by omega) .valuesEntry)
        (gnValuesListSteps values middle + (4 * (middle.length + values.length) + 20)) =
      gnValuesListReadyConfig n pre values middle hroom :=
  @Pnp3.Internal.PsubsetPpoly.TM.gnCS_values_list_requestReady_exact

theorem check_gnValuesRequestReadySteps_provenance :
    ∀ (r : GNProgram)
    (g : SLGate r.inputs.length),
    gnValuesRequestReadySteps r g = gnValuesEntrySteps r g +
      (r.inputs.length * (8 * gnValuesTailDistance r g + 38) +
        (4 * gnValuesTailDistance r g + 20)) :=
  @Pnp3.Internal.PsubsetPpoly.TM.gnValuesRequestReadySteps_provenance

theorem check_gnCS_valuesEntry_requestReady_exact :
    ∀ {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g),
    TM.runConfig (M := GNM) (gnValuesEntryConfig r g hg)
        (r.inputs.length * (8 * gnValuesTailDistance r g + 38) + gnValuesTailSteps r g) =
      gnFirstRequestReadyConfig r g hg :=
  @Pnp3.Internal.PsubsetPpoly.TM.gnCS_valuesEntry_requestReady_exact

theorem check_gnCS_encodeGN_valuesRequestReady_exact :
    ∀ {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g),
    TM.runConfig (M := GNM) (GNM.initialConfig (gnPoint (encodeGN r)))
        (gnValuesRequestReadySteps r g) = gnFirstRequestReadyConfig r g hg :=
  @Pnp3.Internal.PsubsetPpoly.TM.gnCS_encodeGN_valuesRequestReady_exact

theorem check_literal_two_values_requestReady :
    TM.runConfig (M := GNM) twoValuesStart 136 = twoValuesReady ∧
      gnValuesListSteps [true, false] [] = 108 ∧
      (twoValuesReady.head : Nat) = 28 ∧
      twoValuesReady.state = ⟨(0 : Fin 1), .requestReady⟩ :=
  @Pnp3.Internal.PsubsetPpoly.TM.GNValuesInductionProbes.literal_two_values_requestReady

theorem check_literal_two_values_executable :
    (TM.runConfig (M := GNM) twoValuesStart 136).state =
        ⟨(0 : Fin 1), .requestReady⟩ ∧
      ((TM.runConfig (M := GNM) twoValuesStart 136).head : Nat) = 28 ∧
      twoValuesStart.tape ⟨13, by decide⟩ = false ∧
      (TM.runConfig (M := GNM) twoValuesStart 136).tape ⟨13, by decide⟩ = true ∧
      (TM.runConfig (M := GNM) twoValuesStart 136).tape ⟨20, by decide⟩ = true ∧
      (TM.runConfig (M := GNM) twoValuesStart 136).tape ⟨26, by decide⟩ = true :=
  @Pnp3.Internal.PsubsetPpoly.TM.GNValuesInductionProbes.literal_two_values_executable

theorem check_literal_cap_valuesRequestReady :
    TM.runConfig (M := GNM)
        (GNM.initialConfig (gnPoint (encodeGN capProgram))) 1300 = capValuesReady ∧
      gnValuesRequestReadySteps capProgram capFirstGate = 1300 ∧
      (capValuesReady.head : Nat) = 116 ∧
      capValuesReady.state = ⟨(0 : Fin 1), .requestReady⟩ ∧
      decodeGN? (encodeGN capProgram) = some capProgram :=
  @Pnp3.Internal.PsubsetPpoly.TM.GNValuesInductionProbes.literal_cap_valuesRequestReady

theorem check_literal_reserved_reject_stable :
    ∀ (extra : Nat),
    TM.runConfig (M := GNM) reservedCopyStart (4 + extra) =
      gnCopyShuttle.cfg 0 3 (by decide) (frameListTape [true, true, false, true])
        .reject :=
  @Pnp3.Internal.PsubsetPpoly.TM.GNValuesInductionProbes.literal_reserved_reject_stable

end Pnp3.Tests.TMGateNValuesInductionSurface
