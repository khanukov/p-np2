import Complexity.TMVerifier.TuringToolkit.GateNValuesCopy

/-! GN-E2-5b Infrastructure surfaces. Each public theorem (including the
promoted E2-5a classifier) has a named full-proposition wrapper. -/
namespace Pnp3.Tests.TMGateNValuesCopySurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.FrameScan
open Pnp3.Internal.PsubsetPpoly.TM.Encoding
open Pnp3.Internal.PsubsetPpoly.TM.GNValuesCopyProbes
open Pnp3.Internal.PsubsetPpoly.TM.GNEncodingExamples

#check @gnValueCopySteps
#check @gnPendingValuesFrames
#check @gnPendingValuesConfig
#check @gnValueCopyFrames
#check @gnValueCopyExitFrames
#check @gnValueCopyConfig
#check @gnValueCopyMiddle
#check @gnValueCopyDistance
#check @gnFirstValueCopySteps
#check @gnFirstValueCopiedConfig
#check @capFirstGate
#check @capFirstValueCopiedConfig
#check @tinyCopyStart
#check @tinyCopyEnd
#check @reservedCopyStart

theorem check_gnCS_values_classify :
    ∀ (n base : Nat)
    (hsafe : base + 4 < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool) (frame : G1Frame)
    (hbits : physicalBitsAt hsafe tape = frame.bits)
    (hne : gnValuesClassify frame ≠ .reject),
    TM.runConfig (M := GNM)
        (Phased.alignedAt gnCS gnCS.startPhase n base ((by change base < GNM.tapeLength n; omega))
          tape .valuesEntry) 4 =
      Phased.alignedAt gnCS gnCS.startPhase n (base + 4) (hsafe)
        tape (gnValuesClassify frame) :=
  @Pnp3.Internal.PsubsetPpoly.TM.gnCS_values_classify

theorem check_gnCS_values_data_to_install_eight :
    ∀ (n base : Nat)
    (hsafe : base + 4 < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool) (b : Bool)
    (hbits : physicalBitsAt hsafe tape = (G1Frame.data b).bits),
    TM.runConfig (M := GNM)
        (gnCopyShuttle.cfg n base (by change base < GNM.tapeLength n; omega)
          tape .valuesEntry) 8 =
      gnCopyShuttle.cfg n base (by change base < GNM.tapeLength n; omega)
        tape (.install .probe .p0 .empty) :=
  @Pnp3.Internal.PsubsetPpoly.TM.gnCS_values_data_to_install_eight

theorem check_gnCS_dataExit_to_valuesEntry_one :
    ∀ (n head : Nat)
    (hhead : head < GNM.tapeLength n)
    (tape : Fin (GNM.tapeLength n) → Bool) (b : Bool),
    TM.runConfig (M := GNM)
        (gnCopyShuttle.cfg n head hhead tape
          (gnInstallExitState (.carried (.data b)))) 1 =
      gnCopyShuttle.cfg n head hhead tape .valuesEntry :=
  @Pnp3.Internal.PsubsetPpoly.TM.gnCS_dataExit_to_valuesEntry_one

theorem check_gnValueCopySteps_provenance :
    ∀ (d : Nat),
    gnValueCopySteps d = 8 + (8 * d + 29) ∧
      gnValueCopySteps d + 1 = 8 * d + 38 :=
  @Pnp3.Internal.PsubsetPpoly.TM.gnValueCopySteps_provenance

theorem check_gnCS_valueCopy_exit_exact :
    ∀ (n : Nat) (pre : List G1Frame) (b : Bool)
    (middle rest : List G1Frame)
    (hmiddle : ∀ f ∈ middle, GNInstallAdmissible f)
    (hroom : 4 * (pre.length + middle.length + 2) < GNM.tapeLength n),
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
        (gnInstallExitState (.carried (.data b))) :=
  @Pnp3.Internal.PsubsetPpoly.TM.gnCS_valueCopy_exit_exact

theorem check_gnCS_valueCopy_return_exact :
    ∀ (n : Nat) (pre : List G1Frame) (b : Bool)
    (middle rest : List G1Frame)
    (hmiddle : ∀ f ∈ middle, GNInstallAdmissible f)
    (hroom : 4 * (pre.length + middle.length + 2) < GNM.tapeLength n),
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
        .valuesEntry :=
  @Pnp3.Internal.PsubsetPpoly.TM.gnCS_valueCopy_return_exact

theorem check_gnCS_values_cons_exact :
    ∀ (n : Nat) (pre : List G1Frame)
    (b : Bool) (bs : List Bool) (middle : List G1Frame)
    (hmiddle : ∀ f ∈ middle, GNInstallAdmissible f)
    (hroom : 4 * (pre.length + bs.length + middle.length + 3) < GNM.tapeLength n),
    TM.runConfig (M := GNM)
        (gnPendingValuesConfig n pre (b :: bs) middle (by omega) .valuesEntry)
        (8 * (bs.length + 1 + middle.length) + 38) =
      gnPendingValuesConfig n (pre ++ [G1Frame.data b]) bs
        (middle ++ [G1Frame.data b]) (by
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega) .valuesEntry :=
  @Pnp3.Internal.PsubsetPpoly.TM.gnCS_values_cons_exact

theorem check_gnCS_values_nonempty_handoff :
    ∀ (n : Nat) (pre : List G1Frame)
    (b : Bool) (bs : List Bool) (middle : List G1Frame)
    (hsafe : 4 * pre.length + 4 < GNM.tapeLength n),
    TM.runConfig (M := GNM)
        (gnPendingValuesConfig n pre (b :: bs) middle (by omega) .valuesEntry) 8 =
      gnPendingValuesConfig n pre (b :: bs) middle (by omega)
        (.install .probe .p0 .empty) :=
  @Pnp3.Internal.PsubsetPpoly.TM.gnCS_values_nonempty_handoff

theorem check_gnCS_values_nil_tail_handoff :
    ∀ (n : Nat) (pre middle : List G1Frame)
    (hsafe : 4 * pre.length + 4 < GNM.tapeLength n),
    TM.runConfig (M := GNM)
        (gnPendingValuesConfig n pre [] middle (by omega) .valuesEntry) 4 =
      gnCopyShuttle.cfg n (4 * pre.length + 4) hsafe
        (frameListTape ((gnPendingValuesFrames pre [] middle).flatMap G1Frame.bits))
        (.values .seekTail .p0) :=
  @Pnp3.Internal.PsubsetPpoly.TM.gnCS_values_nil_tail_handoff

theorem check_gnRecordFrames_map_image :
    ∀ {n : Nat} (g : SLGate n),
    (gnRecordFrames .cursor g).map gnInstallImage =
      G1Frame.bof :: (gnGateBodyFrames g ++ [G1Frame.separator]) :=
  @Pnp3.Internal.PsubsetPpoly.TM.gnRecordFrames_map_image

theorem check_gnValueCopyMiddle_length :
    ∀ {r : GNProgram} {g : SLGate r.inputs.length}
    {b : Bool} {bs : List Bool} (hvals : r.inputs = b :: bs),
    (gnValueCopyMiddle r g bs).length = gnValueCopyDistance r g :=
  @Pnp3.Internal.PsubsetPpoly.TM.gnValueCopyMiddle_length

theorem check_gnValueCopy_frames :
    ∀ {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) {b : Bool} {bs : List Bool}
    (hvals : r.inputs = b :: bs),
    [G1Frame.bof] ++ G1Frame.data b :: gnValueCopyMiddle r g bs =
      encodeGNFrames r ++ (gnRecordFrames .cursor g).map gnInstallImage :=
  @Pnp3.Internal.PsubsetPpoly.TM.gnValueCopy_frames

theorem check_gnValueCopyMiddle_admissible :
    ∀ {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g)
    (bs : List Bool),
    ∀ frame ∈ gnValueCopyMiddle r g bs, GNInstallAdmissible frame :=
  @Pnp3.Internal.PsubsetPpoly.TM.gnValueCopyMiddle_admissible

theorem check_gnFirstValueCopySteps_provenance :
    ∀ (r : GNProgram)
    (g : SLGate r.inputs.length),
    gnFirstValueCopySteps r g =
      gnValuesEntrySteps r g + (8 * gnValueCopyDistance r g + 38) :=
  @Pnp3.Internal.PsubsetPpoly.TM.gnFirstValueCopySteps_provenance

theorem check_gnCS_encodeGN_firstValueCopied_exact :
    ∀ {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g)
    {b : Bool} {bs : List Bool} (hvals : r.inputs = b :: bs),
    TM.runConfig (M := GNM) (GNM.initialConfig (gnPoint (encodeGN r)))
        (gnFirstValueCopySteps r g) = gnFirstValueCopiedConfig r g b :=
  @Pnp3.Internal.PsubsetPpoly.TM.gnCS_encodeGN_firstValueCopied_exact

theorem check_gnFirstValueCopiedConfig_structure :
    ∀ {r : GNProgram}
    {g : SLGate r.inputs.length} (hg : r.program.gates[0]? = some g)
    {b : Bool} {bs : List Bool} (hvals : r.inputs = b :: bs),
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
        g1PrefixFrames (gnFirstRequest r g) :=
  @Pnp3.Internal.PsubsetPpoly.TM.gnFirstValueCopiedConfig_structure

/-- The literal contract pins the 1184-row endpoint, head, state, schedule and
distance. Its endpoint tape is defined by `capFirstValueCopiedConfig`; there is
no separate pre-state blank-cell conjunct. The frozen owner's phrase "was blank"
is explanatory prose, not an additional theorem assertion. The distinct
`check_literal_tiny_executable` below explicitly pins both cell values. -/
theorem check_literal_cap_firstValueCopied :
    TM.runConfig (M := GNM)
        (GNM.initialConfig (gnPoint (encodeGN capProgram))) 1184 =
      capFirstValueCopiedConfig ∧
    (capFirstValueCopiedConfig.head : Nat) = 8 ∧
    capFirstValueCopiedConfig.state =
      ⟨(0 : Fin 1), .valuesEntry⟩ ∧
    gnFirstValueCopySteps capProgram capFirstGate = 1184 ∧
    gnValueCopyDistance capProgram capFirstGate = 24 :=
  @Pnp3.Internal.PsubsetPpoly.TM.GNValuesCopyProbes.literal_cap_firstValueCopied

theorem check_literal_tiny_copy :
    ∀ (b : Bool),
    TM.runConfig (M := GNM) (tinyCopyStart b) 46 = tinyCopyEnd b :=
  @Pnp3.Internal.PsubsetPpoly.TM.GNValuesCopyProbes.literal_tiny_copy

theorem check_literal_tiny_executable :
    (TM.runConfig (M := GNM) (tinyCopyStart true) 46).state =
        ⟨(0 : Fin 1), .valuesEntry⟩ ∧
      ((TM.runConfig (M := GNM) (tinyCopyStart true) 46).head : Nat) = 4 ∧
      (tinyCopyStart true).tape ⟨9, by decide⟩ = false ∧
      (TM.runConfig (M := GNM) (tinyCopyStart true) 46).tape ⟨9, by decide⟩ = true :=
  @Pnp3.Internal.PsubsetPpoly.TM.GNValuesCopyProbes.literal_tiny_executable

theorem check_literal_two_values_handoff :
    TM.runConfig (M := GNM)
        (gnPendingValuesConfig 0 [] [true, false] [] (by decide) .valuesEntry)
        62 =
      gnPendingValuesConfig 0 [G1Frame.data true] [false] [G1Frame.data true]
        (by decide) (.install .probe .p0 .empty) :=
  @Pnp3.Internal.PsubsetPpoly.TM.GNValuesCopyProbes.literal_two_values_handoff

theorem check_literal_singleton_tail_handoff :
    TM.runConfig (M := GNM) (tinyCopyStart false) 50 =
      gnCopyShuttle.cfg 0 8 (by decide)
        (frameListTape ((gnPendingValuesFrames [G1Frame.data false] []
          [G1Frame.data false]).flatMap G1Frame.bits)) (.values .seekTail .p0) :=
  @Pnp3.Internal.PsubsetPpoly.TM.GNValuesCopyProbes.literal_singleton_tail_handoff

theorem check_literal_reserved_reject :
    TM.runConfig (M := GNM) reservedCopyStart 4 =
      gnCopyShuttle.cfg 0 3 (by decide) (frameListTape [true, true, false, true])
        .reject :=
  @Pnp3.Internal.PsubsetPpoly.TM.GNValuesCopyProbes.literal_reserved_reject

end Pnp3.Tests.TMGateNValuesCopySurface
