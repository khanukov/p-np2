import Complexity.TMVerifierExtensions.GateNFirstCommitExamples

/-! Full-proposition pins for GN-E2-5e infrastructure. -/
namespace Pnp3.Tests.TMGateNFirstCommitSurface
open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open FrameScan Encoding GNEncodingExamples GNValuesCopyProbes GNValuesInductionProbes GNFirstRequestLaunchProbes GNFirstCommitProbes

#synth Fintype GNState
#synth DecidableEq GNState
#check gnFirstCommitSteps
#check gnFirstCommitHead
#check gnFirstCommitConfig

theorem check_gnFirstReturnedConfig_eq_physical {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) (res : Bool)
    (hr : 4*((encodeGNFrames r).length+(g1PrefixFrames (gnFirstRequest r g)).length)-1 <
      GNM.tapeLength (encodeGN r).length) :
    gnFirstReturnedConfig r g hg res =
      gnCommitConfig (encodeGN r).length
        (4*((encodeGNFrames r).length+(g1PrefixFrames (gnFirstRequest r g)).length)-1) hr
        (frameListTape ((encodeGNFrames r ++
          g1OutputFrames (gnFirstRequest r g) res).flatMap G1Frame.bits)) (gnReturnedState res) := by
  exact Pnp3.Internal.PsubsetPpoly.TM.gnFirstReturnedConfig_eq_physical hg res hr

theorem check_gnCS_firstReturned_commit_exact {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) (res : Bool) :
    TM.runConfig (M := GNM) (gnFirstReturnedConfig r g hg res)
      (gnFirstCommitSteps r g) = gnFirstCommitConfig r g hg res := by
  exact Pnp3.Internal.PsubsetPpoly.TM.gnCS_firstReturned_commit_exact hg res

theorem check_gnCS_encodeGN_firstCommit_exact {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) (res : Bool)
    (hs : (gnFirstRequest r g).spec = some res) :
    TM.runConfig (M := GNM) (GNM.initialConfig (gnPoint (encodeGN r)))
      (gnFirstLaunchSteps r g + (g1GateDoneSteps (gnFirstRequest r g)+1) +
        gnFirstCommitSteps r g) = gnFirstCommitConfig r g hg res := by
  exact Pnp3.Internal.PsubsetPpoly.TM.gnCS_encodeGN_firstCommit_exact hg res hs

theorem check_gnFirstCommit_structure {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) (res : Bool) :
    let out := TM.runConfig (M := GNM) (gnFirstReturnedConfig r g hg res) (gnFirstCommitSteps r g)
    out.state = ⟨(0 : Fin 1), if r.program.gates.length = 1 then
      .firstCommitTerminal else .firstCommitNext⟩ ∧
    (out.head : Nat) = gnFirstCommitHead r g ∧
    out.tape = frameListTape ((encodeGNAtFrames r [res] ++
      g1OutputFrames (gnFirstRequest r g) res).flatMap G1Frame.bits) ∧
    gnCommit? r [] res = some ([res], encodeGNAtFrames r [res]) ∧
    gnCurrentValues r [res] = r.inputs ++ [res] ∧
    gnFinalValue r [res] = (if r.program.gates.length = 1 then res else false) := by
  exact Pnp3.Internal.PsubsetPpoly.TM.gnFirstCommit_structure hg res

theorem check_gnFirstCommit_scratch_preserved {r : GNProgram} {g : SLGate r.inputs.length}
    (hg : r.program.gates[0]? = some g) (res : Bool)
    (i : Fin (GNM.tapeLength (encodeGN r).length)) (hi : (encodeGN r).length ≤ i.val) :
    (TM.runConfig (M := GNM) (gnFirstReturnedConfig r g hg res)
      (gnFirstCommitSteps r g)).tape i = (gnFirstReturnedConfig r g hg res).tape i := by
  exact Pnp3.Internal.PsubsetPpoly.TM.gnFirstCommit_scratch_preserved hg res i hi

theorem check_literal_cap_commit :
    TM.runConfig (M := GNM) capReturned 179 = capCommitted ∧
    TM.runConfig (M := GNM) (GNM.initialConfig (gnPoint (encodeGN capProgram)))
      1742 = capCommitted ∧ gnFirstCommitSteps capProgram capFirstGate = 179 := by
  exact Pnp3.Internal.PsubsetPpoly.TM.GNFirstCommitProbes.literal_cap_commit

theorem check_literal_single_gate_commit :
    TM.runConfig (M := GNM) trueReturned 151 = gnFirstCommitConfig oneTrue (.const true) rfl true ∧
    TM.runConfig (M := GNM) falseReturned 139 = gnFirstCommitConfig oneFalse (.const false) rfl false := by
  exact Pnp3.Internal.PsubsetPpoly.TM.GNFirstCommitProbes.literal_single_gate_commit

theorem check_literal_true_terminal_kernel :
    (TM.runConfig (M := GNM) trueReturned 151).state = ⟨(0 : Fin 1), .firstCommitTerminal⟩ ∧
    ((TM.runConfig (M := GNM) trueReturned 151).head : Nat) = 48 ∧
    (TM.runConfig (M := GNM) trueReturned 151).tape ⟨47, by decide⟩ = true ∧
    (TM.runConfig (M := GNM) trueReturned 151).tape ⟨83, by decide⟩ = true ∧
    (TM.runConfig (M := GNM) trueReturned 151).tape ⟨7, by decide⟩ = false := by
  exact Pnp3.Internal.PsubsetPpoly.TM.GNFirstCommitProbes.literal_true_terminal_kernel

theorem check_literal_cap_kernel :
    (TM.runConfig (M := GNM) capReturned 179).state = ⟨(0 : Fin 1), .firstCommitNext⟩ ∧
    ((TM.runConfig (M := GNM) capReturned 179).head : Nat) = 40 ∧
    (TM.runConfig (M := GNM) capReturned 179).tape ⟨10, by decide⟩ = true ∧
    (TM.runConfig (M := GNM) capReturned 179).tape ⟨11, by decide⟩ = false ∧
    (TM.runConfig (M := GNM) capReturned 179).tape ⟨111, by decide⟩ = true := by
  exact Pnp3.Internal.PsubsetPpoly.TM.GNFirstCommitProbes.literal_cap_kernel

theorem check_literal_false_nonterminal :
    TM.runConfig (M := GNM) (gnFirstReturnedConfig falseNext (.const false) rfl false)
      175 = gnFirstCommitConfig falseNext (.const false) rfl false ∧
    (gnFirstCommitConfig falseNext (.const false) rfl false).state =
      ⟨(0 : Fin 1), .firstCommitNext⟩ ∧
    (gnFirstCommitConfig falseNext (.const false) rfl false).tape ⟨7, by decide⟩ = true := by
  exact Pnp3.Internal.PsubsetPpoly.TM.GNFirstCommitProbes.literal_false_nonterminal

theorem check_literal_reserved_commit (m : GNCommitMode) (res : Bool) :
    gnCommitComplete m true true false true res = (.reject, .stay) ∧
    gnCommitComplete m true true true false res = (.reject, .stay) ∧
    gnCommitComplete m true true true true res = (.reject, .stay) ∧
    gnCommitComplete .seekCursor false false false false res = (.reject, .stay) ∧
    gnCommitComplete .seekOpening false false false false res = (.reject, .stay) := by
  exact GNFirstCommitProbes.literal_reserved_commit m res

end Pnp3.Tests.TMGateNFirstCommitSurface
