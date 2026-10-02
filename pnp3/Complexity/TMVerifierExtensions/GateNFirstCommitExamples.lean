import Complexity.TMVerifierExtensions.GateNFirstCommit
import Complexity.TMVerifierExtensions.GateNFirstRequestLaunchExamples
import Complexity.TMVerifier.TuringToolkit.GateNTapeStateExamples

/-! Closed fixtures: full configurations by execution theorem, independent
kernel probes of the live rows, and composition of the actual initial run. -/
namespace Pnp3.Internal.PsubsetPpoly.TM.GNFirstCommitProbes
open FrameScan Encoding GNEncodingExamples GNValuesCopyProbes GNValuesInductionProbes GNFirstRequestLaunchProbes

def capCommitted : Configuration (M := GNM) 84 :=
  gnCommitConfig 84 40 (by decide)
    (frameListTape ((GNTapeStateExamples.capFirstFrames ++
      g1OutputFrames (gnFirstRequest capProgram capFirstGate) true).flatMap G1Frame.bits))
    .firstCommitNext

theorem literal_cap_commit :
    TM.runConfig (M := GNM) capReturned 179 = capCommitted ∧
    TM.runConfig (M := GNM) (GNM.initialConfig (gnPoint (encodeGN capProgram)))
      1742 = capCommitted ∧ gnFirstCommitSteps capProgram capFirstGate = 179 := by
  have h := gnCS_firstReturned_commit_exact (r := capProgram) (g := capFirstGate) rfl true
  rw [gnFirstReturnedConfig_eq_physical rfl true (by decide)] at h
  have hi := gnCS_encodeGN_firstCommit_exact (r := capProgram) (g := capFirstGate) rfl true (by decide)
  have hc : gnFirstLaunchSteps capProgram capFirstGate +
      (g1GateDoneSteps (gnFirstRequest capProgram capFirstGate)+1) +
      gnFirstCommitSteps capProgram capFirstGate = 1742 := by decide
  rw [hc] at hi
  exact ⟨h, hi, by decide⟩

def oneTrue : GNProgram := ⟨[], ⟨[.const true]⟩⟩
def oneFalse : GNProgram := ⟨[], ⟨[.const false]⟩⟩

def trueReturned : Configuration (M := GNM) 52 :=
  gnCommitConfig 52 79 (by decide)
    (frameListTape ((encodeGNFrames oneTrue ++
      g1OutputFrames (gnFirstRequest oneTrue (.const true)) true).flatMap G1Frame.bits)) .returnedTrue

def falseReturned : Configuration (M := GNM) 48 :=
  gnCommitConfig 48 71 (by decide)
    (frameListTape ((encodeGNFrames oneFalse ++
      g1OutputFrames (gnFirstRequest oneFalse (.const false)) false).flatMap G1Frame.bits)) .returnedFalse

theorem literal_single_gate_commit :
    TM.runConfig (M := GNM) trueReturned 151 = gnFirstCommitConfig oneTrue (.const true) rfl true ∧
    TM.runConfig (M := GNM) falseReturned 139 = gnFirstCommitConfig oneFalse (.const false) rfl false := by
  have ht := gnCS_firstReturned_commit_exact (r := oneTrue) (g := .const true) rfl true
  have hf := gnCS_firstReturned_commit_exact (r := oneFalse) (g := .const false) rfl false
  rw [gnFirstReturnedConfig_eq_physical rfl true (by decide)] at ht
  rw [gnFirstReturnedConfig_eq_physical rfl false (by decide)] at hf
  exact ⟨ht, hf⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
/-- Independent reduction of the actual TM rows. Cell 47 distinguishes the
canonical terminal commit from the rejected partial-tape schedule. -/
theorem literal_true_terminal_kernel :
    (TM.runConfig (M := GNM) trueReturned 151).state = ⟨(0 : Fin 1), .firstCommitTerminal⟩ ∧
    ((TM.runConfig (M := GNM) trueReturned 151).head : Nat) = 48 ∧
    (TM.runConfig (M := GNM) trueReturned 151).tape ⟨47, by decide⟩ = true ∧
    (TM.runConfig (M := GNM) trueReturned 151).tape ⟨83, by decide⟩ = true ∧
    (TM.runConfig (M := GNM) trueReturned 151).tape ⟨7, by decide⟩ = false := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem literal_cap_kernel :
    (TM.runConfig (M := GNM) capReturned 179).state = ⟨(0 : Fin 1), .firstCommitNext⟩ ∧
    ((TM.runConfig (M := GNM) capReturned 179).head : Nat) = 40 ∧
    (TM.runConfig (M := GNM) capReturned 179).tape ⟨10, by decide⟩ = true ∧
    (TM.runConfig (M := GNM) capReturned 179).tape ⟨11, by decide⟩ = false ∧
    (TM.runConfig (M := GNM) capReturned 179).tape ⟨111, by decide⟩ = true := by
  decide +kernel

def falseNext : GNProgram := ⟨[], ⟨[.const false, .const true]⟩⟩

theorem literal_false_nonterminal :
    TM.runConfig (M := GNM) (gnFirstReturnedConfig falseNext (.const false) rfl false)
      175 = gnFirstCommitConfig falseNext (.const false) rfl false ∧
    (gnFirstCommitConfig falseNext (.const false) rfl false).state =
      ⟨(0 : Fin 1), .firstCommitNext⟩ ∧
    (gnFirstCommitConfig falseNext (.const false) rfl false).tape ⟨7, by decide⟩ = true := by
  exact ⟨gnCS_firstReturned_commit_exact rfl false, rfl, rfl⟩

/-- Reserved codewords fail closed in every first-commit reader mode. -/
theorem literal_reserved_commit (m : GNCommitMode) (res : Bool) :
    gnCommitComplete m true true false true res = (.reject, .stay) ∧
    gnCommitComplete m true true true false res = (.reject, .stay) ∧
    gnCommitComplete m true true true true res = (.reject, .stay) ∧
    gnCommitComplete .seekCursor false false false false res = (.reject, .stay) ∧
    gnCommitComplete .seekOpening false false false false res = (.reject, .stay) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end Pnp3.Internal.PsubsetPpoly.TM.GNFirstCommitProbes
