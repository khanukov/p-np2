import Complexity.TMVerifierExtensions.GateNFirstRequestLaunch

/-! Literal real encoded execution; first returned true is not the program's
final false. The small launch probe is independent kernel reduction. -/
namespace Pnp3.Internal.PsubsetPpoly.TM.GNFirstRequestLaunchProbes
open FrameScan Encoding GNEncodingExamples GNValuesCopyProbes GNValuesInductionProbes

/-- Literal unchanged 84-bit GN prefix. -/
def capGNFrames : List G1Frame :=
  [.bof, .data true, .output false, .output false, .separator,
    .cursor, .tag, .argSep, .argSep, .finish,
    .bof, .tag, .tag, .tag, .argSep, .index, .argSep, .finish,
    .separator, .output false, .finish]

def capLaunched : Configuration (M := GNM) 84 :=
  gnLaunchConfig 84 84 (by decide)
    (frameListTape ((capGNFrames ++ [G1Frame.bof, .tag, .argSep, .argSep, .separator,
      .data true, .output false, .finish]).flatMap G1Frame.bits))
    (.delegated G1M.start)

def capOutputDone : Configuration (M := GNM) 84 :=
  gnLaunchConfig 84 107 (by decide)
    (frameListTape ((capGNFrames ++ [G1Frame.bof, .tag, .argSep, .argSep, .separator,
      .data true, .output true, .finish, .blank]).flatMap G1Frame.bits))
    (.delegated (g1DoneQ true))

def capReturned : Configuration (M := GNM) 84 :=
  gnLaunchConfig 84 107 (by decide)
    (frameListTape ((capGNFrames ++ [G1Frame.bof, .tag, .argSep, .argSep, .separator,
      .data true, .output true, .finish, .blank]).flatMap G1Frame.bits))
    .returnedTrue

theorem literal_cap_firstLaunch :
    TM.runConfig (M := GNM)
      (GNM.initialConfig (gnPoint (encodeGN capProgram))) 1333 = capLaunched ∧
    (encodeGN capProgram).length = 84 ∧
    (encodeG1 (gnFirstRequest capProgram capFirstGate)).length = 32 ∧
    gnValuesRequestReadySteps capProgram capFirstGate = 1300 ∧
    gnFirstRequestLaunchSteps capProgram capFirstGate = 33 ∧
    gnFirstLaunchSteps capProgram capFirstGate = 1333 ∧
    (capLaunched.head : Nat) = 84 ∧ capLaunched.state = gnEmbed G1M.start := by
  have hg : capProgram.program.gates[0]? = some capFirstGate := rfl
  have hc : gnFirstLaunchSteps capProgram capFirstGate = 1333 := by decide
  have hr := gnCS_encodeGN_firstLaunch_exact hg
  rw [hc, gnFirstInstalledConfig_eq_physical hg] at hr
  exact ⟨hr, rfl, rfl, by decide, by decide, hc, rfl, rfl⟩

theorem literal_cap_firstReturned :
    TM.runConfig (M := GNM)
      (GNM.initialConfig (gnPoint (encodeGN capProgram))) 1562 = capOutputDone ∧
    TM.runConfig (M := GNM)
      (GNM.initialConfig (gnPoint (encodeGN capProgram))) 1563 = capReturned ∧
    g1GateDoneSteps (gnFirstRequest capProgram capFirstGate) = 229 ∧
    capReturned.state = gnReturnedQ true ∧ (capReturned.head : Nat) = 107 ∧
    capReturned.tape ⟨111, by decide⟩ = true ∧
    capReturned.tape ⟨11, by decide⟩ = false ∧
    capLaunched.tape ⟨111, by decide⟩ = false ∧
    evalGNProgram capProgram = some false := by
  have hg : capProgram.program.gates[0]? = some capFirstGate := rfl
  have hs : (gnFirstRequest capProgram capFirstGate).spec = some true := by decide
  have hc : gnFirstLaunchSteps capProgram capFirstGate = 1333 := by decide
  have hd : g1GateDoneSteps (gnFirstRequest capProgram capFirstGate) = 229 := by decide
  have hr := gnCS_encodeGN_firstReturned_exact hg true hs
  have ho := gnCS_encodeGN_firstOutputDone_exact hg true hs
  have ht := (gnFirstReturned_structure hg true hs).2.2.1
  rw [gnCS_encodeGN_firstReturned_exact hg true hs] at ht
  rw [hc, hd] at hr ho
  refine ⟨?_, ?_, hd, rfl, rfl, rfl, rfl, rfl, by decide⟩
  · rw [ho]
    apply Configuration.ext_of_components
    · rfl
    · rfl
    · exact ht
  · rw [hr]
    apply Configuration.ext_of_components
    · rfl
    · rfl
    · exact ht

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- Independent kernel execution from the existing literal ready tape. -/
theorem literal_cap_launch_executable :
    (TM.runConfig (M := GNM) capValuesReady 33).state = gnEmbed G1M.start ∧
    ((TM.runConfig (M := GNM) capValuesReady 33).head : Nat) = 84 ∧
    (TM.runConfig (M := GNM) capValuesReady 34).state =
      gnEmbed ⟨(0 : Fin 1), g1State .vBof .p1 false⟩ ∧
    ((TM.runConfig (M := GNM) capValuesReady 34).head : Nat) = 85 ∧
    (TM.runConfig (M := GNM) capValuesReady 34).tape ⟨84, by decide⟩ = false ∧
    (TM.runConfig (M := GNM) capValuesReady 34).tape ⟨111, by decide⟩ = false := by
  decide +kernel

def firstNotProgram : GNProgram := ⟨[true], ⟨[.notGate 0]⟩⟩

theorem literal_first_not_is_undefined :
    firstNotProgram.program.gates[0]? = some (.notGate 0) ∧
    (gnFirstRequest firstNotProgram (.notGate 0)).Canonical ∧
    (gnFirstRequest firstNotProgram (.notGate 0)).spec = none ∧
    TM.runConfig (M := GNM) (GNM.initialConfig (gnPoint (encodeGN firstNotProgram)))
      (gnFirstLaunchSteps firstNotProgram (.notGate 0)) =
      gnFirstInstalledConfig firstNotProgram (.notGate 0) rfl := by
  exact ⟨rfl, gnFirstRequest_canonical _ _, by decide, gnCS_encodeGN_firstLaunch_exact rfl⟩

theorem literal_reserved_launch_reject (k : Nat) :
    TM.runConfig (M := GNM)
      (gnLaunchConfig 0 4 (by decide) (frameListTape [true, true, false, true])
        .requestReady) (5+k) =
      gnLaunchConfig 0 0 (by decide) (frameListTape [true, true, false, true])
        .reject :=
  gnCS_requestReady_reserved1101_reject_stable 0 0 (by decide) _ rfl k

/-- Kernel execution at and above the left boundary, without an opening bof. -/
theorem literal_noBof_allBlank_launch_reject :
    (TM.runConfig (M := GNM)
      (gnLaunchConfig 0 0 (by decide) (fun _ => false) .requestReady) 5).state =
        ⟨(0 : Fin 1), GNState.reject⟩ ∧
    ((TM.runConfig (M := GNM)
      (gnLaunchConfig 0 0 (by decide) (fun _ => false) .requestReady) 5).head : Nat) = 0 ∧
    (TM.runConfig (M := GNM)
      (gnLaunchConfig 0 4 (by decide) (fun _ => false) .requestReady) 5).state =
        ⟨(0 : Fin 1), GNState.reject⟩ ∧
    ((TM.runConfig (M := GNM)
      (gnLaunchConfig 0 4 (by decide) (fun _ => false) .requestReady) 5).head : Nat) = 0 ∧
    (TM.runConfig (M := GNM)
      (gnLaunchConfig 0 0 (by decide) (fun _ => false) .requestReady) 9).state =
        ⟨(0 : Fin 1), GNState.reject⟩ := by
  decide +kernel

end Pnp3.Internal.PsubsetPpoly.TM.GNFirstRequestLaunchProbes
