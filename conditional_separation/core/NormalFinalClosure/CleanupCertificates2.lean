import NormalFinalClosure.Cleanup2
import NormalFinalClosure.CodeCertificates2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["ns2","Safe2","ns2_safe"]),
    (`NormalFinalClosure.CounterSupport2,`NormalFinalClosure,["nativeRow"]),
    (`NormalFinalClosure.Cleanup2,`NormalFinalClosure,["CleanChain"]),
    (`NormalFinalClosure.NavigationRows4,`NormalFinalClosure,["d_to_h_3303","d_to_h_3489","d_to_h_3659","d_to_h_3845","d_to_h_4031","d_to_h_4201"]),
    (`NormalFinalClosure.CodeCertificates2,`NormalFinalClosure,["clearCode_75", "clearCode_76", "clearCode_77", "clearCode_78", "clearCode_79", "clearCode_80", "clearCode_81", "clearCode_82", "clearCode_83", "clearCode_84", "clearCode_85", "clearCode_86", "clearCode_87", "clearCode_88", "clearCode_89", "clearCode_90", "clearCode_91", "clearCode_92", "clearCode_93", "clearCode_94", "clearCode_95", "clearCode_96", "clearCode_97", "clearCode_98", "clearCode_99", "clearCode_100", "clearCode_101", "clearCode_102", "clearCode_103", "clearCode_104"])] do
    for leaf in leaves do
      let name:=Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns) leaf
      let some ci:=e.find? name | throwError "Missing exact native cleanup record"
      let some i:=e.getModuleIdxFor? name | throwError "Missing cleanup record owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong cleanup record owner"
      logInfo m!"actual-cleanup-record-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) name::st.openDecls}
private theorem cleanup_3139 (k : Nat) : CleanChain (M:=machine2 k) (Safe:=Safe2 k) (ns2 k 3139) (machine2 k).accept := by
  refine ⟨ns2 k 3159,ns2 k 3183,ns2 k 3211,ns2 k 3259,ns2 k 3303,ns2 k 3307,clearCode_75 k,clearCode_76 k,clearCode_77 k,clearCode_78 k,clearCode_79 k,d_to_h_3303 k,ns2_safe k 3307,?_⟩
  run_tac nativeRow
private theorem cleanup_3325 (k : Nat) : CleanChain (M:=machine2 k) (Safe:=Safe2 k) (ns2 k 3325) (machine2 k).accept := by
  refine ⟨ns2 k 3345,ns2 k 3369,ns2 k 3397,ns2 k 3445,ns2 k 3489,ns2 k 3493,clearCode_80 k,clearCode_81 k,clearCode_82 k,clearCode_83 k,clearCode_84 k,d_to_h_3489 k,ns2_safe k 3493,?_⟩
  run_tac nativeRow
private theorem cleanup_3495 (k : Nat) : CleanChain (M:=machine2 k) (Safe:=Safe2 k) (ns2 k 3495) (machine2 k).accept := by
  refine ⟨ns2 k 3515,ns2 k 3539,ns2 k 3567,ns2 k 3615,ns2 k 3659,ns2 k 3663,clearCode_85 k,clearCode_86 k,clearCode_87 k,clearCode_88 k,clearCode_89 k,d_to_h_3659 k,ns2_safe k 3663,?_⟩
  run_tac nativeRow
private theorem cleanup_3681 (k : Nat) : CleanChain (M:=machine2 k) (Safe:=Safe2 k) (ns2 k 3681) (machine2 k).reject := by
  refine ⟨ns2 k 3701,ns2 k 3725,ns2 k 3753,ns2 k 3801,ns2 k 3845,ns2 k 3849,clearCode_90 k,clearCode_91 k,clearCode_92 k,clearCode_93 k,clearCode_94 k,d_to_h_3845 k,ns2_safe k 3849,?_⟩
  run_tac nativeRow
private theorem cleanup_3867 (k : Nat) : CleanChain (M:=machine2 k) (Safe:=Safe2 k) (ns2 k 3867) (machine2 k).reject := by
  refine ⟨ns2 k 3887,ns2 k 3911,ns2 k 3939,ns2 k 3987,ns2 k 4031,ns2 k 4035,clearCode_95 k,clearCode_96 k,clearCode_97 k,clearCode_98 k,clearCode_99 k,d_to_h_4031 k,ns2_safe k 4035,?_⟩
  run_tac nativeRow
private theorem cleanup_4037 (k : Nat) : CleanChain (M:=machine2 k) (Safe:=Safe2 k) (ns2 k 4037) (machine2 k).reject := by
  refine ⟨ns2 k 4057,ns2 k 4081,ns2 k 4109,ns2 k 4157,ns2 k 4201,ns2 k 4205,clearCode_100 k,clearCode_101 k,clearCode_102 k,clearCode_103 k,clearCode_104 k,d_to_h_4201 k,ns2_safe k 4205,?_⟩
  run_tac nativeRow
end NormalFinalClosure
