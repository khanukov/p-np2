import NormalFinalClosure.CodeCertificates2
import NormalFinalClosure.Copy2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
private def exactMacro (owner ns : Name) (leaf kind : String) : TacticM Unit := do
  let n:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
  let e←getEnv
  let some ci:=e.find? n | throwError "Missing exact macro component"
  let actual:=match ci with|.defnInfo _=>"definition"|.ctorInfo _=>"constructor"|.thmInfo _=>"theorem"|_=>"other"
  unless actual==kind do throwError "Wrong macro component kind"
  let some i:=e.getModuleIdxFor? n | throwError "Missing macro component owner"
  unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong macro component owner"
  logInfo m!"native-macro-exact-component|{n}|{kind}|{ci.type}"
  closeMainGoal `exactMacro (mkConst n (ci.levelParams.map Level.param))
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`NormalFinalClosure.Copy2,`NormalFinalClosure,["CopyRows","TransferRows"]),
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["ns2","Safe2"]),
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["DecRows","IncRows","FromHRows"])] do
    for leaf in leaves do
      let n:=Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns) leaf
      let some ci:=e.find? n | throwError "Missing exact macro API"
      let some i:=e.getModuleIdxFor? n | throwError "Missing macro API owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong macro API owner"
      logInfo m!"native-macro-type|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private abbrev nativeRow : TacticM Unit := by
  run_tac exactMacro `NormalFinalClosure.Rows2Code `NormalFinalClosure "nativeRow2" "definition"
private theorem nsSafe : ∀ k i,Safe2 k (ns2 k i) := by
  run_tac exactMacro `NormalFinalClosure.Rows2Code `NormalFinalClosure "ns2_safe" "theorem"
private abbrev copyMk : {M : UniformTM} → {Safe : Fin M.stateCount → Prop} →
    {s d tmp : Nat} → {start out : Fin M.stateCount} →
    (restore id it ir : Fin M.stateCount) → DecRows (Safe:=Safe) s start restore id →
    IncRows (Safe:=Safe) d id it → IncRows (Safe:=Safe) tmp it start →
    DecRows (Safe:=Safe) tmp restore out ir → IncRows (Safe:=Safe) s ir restore →
    CopyRows (Safe:=Safe) s d tmp start out := by
  run_tac exactMacro `NormalFinalClosure.Copy2 `NormalFinalClosure "CopyRows.mk" "constructor"
private abbrev transferMk : {M : UniformTM} → {Safe : Fin M.stateCount → Prop} →
    {s d : Nat} → {start out : Fin M.stateCount} → (pos : Fin M.stateCount) →
    DecRows (Safe:=Safe) s start out pos → IncRows (Safe:=Safe) d pos start →
    TransferRows (Safe:=Safe) s d start out := by
  run_tac exactMacro `NormalFinalClosure.Copy2 `NormalFinalClosure "TransferRows.mk" "constructor"
run_cmd do
  let e←getEnv
  let owner:=`NormalFinalClosure.CodeCertificates2
  for leaf in ["decCode_15","decCode_21","decCode_24","decCode_26","decCode_29","decCode_36","decCode_38","decCode_4","decCode_41","decCode_50","decCode_54","decCode_57","decCode_66","decCode_68","decCode_7","decCode_71","incCode_16","incCode_22","incCode_23","incCode_25","incCode_27","incCode_28","incCode_30","incCode_37","incCode_39","incCode_40","incCode_42","incCode_5","incCode_51","incCode_55","incCode_56","incCode_58","incCode_6","incCode_67","incCode_69","incCode_70","incCode_72","incCode_8"] do
    let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "NormalFinalClosure") leaf
    let some (.thmInfo ci):=e.find? n | throwError "Missing actual macro row certificate"
    let some i:=e.getModuleIdxFor? n | throwError "Missing macro row owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong macro row owner"
    logInfo m!"native-macro-row|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private def copyCore_0 (k : Nat) : CopyRows (Safe:=Safe2 k) 3 4 5 (ns2 k 125) (ns2 k 238) := by
  exact copyMk (ns2 k 189) (ns2 k 147) (ns2 k 166) (ns2 k 223) (decCode_4 k) (incCode_5 k) (incCode_6 k) (decCode_7 k) (incCode_8 k)
private theorem macroEntry_0 (k : Nat) : (machine2 k).step (ns2 k 124) none=(ns2 k 125,none,Move.stay) := by
  run_tac nativeRow
private def transferCore_1 (k : Nat) : TransferRows (Safe:=Safe2 k) 5 4 (ns2 k 392) (ns2 k 238) := by
  exact transferMk (ns2 k 426) (decCode_15 k) (incCode_16 k)
private theorem macroEntry_1 (k : Nat) : (machine2 k).step (ns2 k 391) none=(ns2 k 392,none,Move.stay) := by
  run_tac nativeRow
private def copyCore_2 (k : Nat) : CopyRows (Safe:=Safe2 k) 3 4 5 (ns2 k 623) (ns2 k 850) := by
  exact copyMk (ns2 k 687) (ns2 k 645) (ns2 k 664) (ns2 k 721) (decCode_21 k) (incCode_22 k) (incCode_23 k) (decCode_24 k) (incCode_25 k)
private theorem macroEntry_2 (k : Nat) : (machine2 k).step (ns2 k 622) none=(ns2 k 623,none,Move.stay) := by
  run_tac nativeRow
private def copyCore_3 (k : Nat) : CopyRows (Safe:=Safe2 k) 3 4 5 (ns2 k 737) (ns2 k 1628) := by
  exact copyMk (ns2 k 801) (ns2 k 759) (ns2 k 778) (ns2 k 835) (decCode_26 k) (incCode_27 k) (incCode_28 k) (decCode_29 k) (incCode_30 k)
private theorem macroEntry_3 (k : Nat) : (machine2 k).step (ns2 k 736) none=(ns2 k 737,none,Move.stay) := by
  run_tac nativeRow
private def transferCore_4 (k : Nat) : TransferRows (Safe:=Safe2 k) 5 11 (ns2 k 1036) (ns2 k 1117) := by
  exact transferMk (ns2 k 1070) (decCode_36 k) (incCode_37 k)
private theorem macroEntry_4 (k : Nat) : (machine2 k).step (ns2 k 1035) none=(ns2 k 1036,none,Move.stay) := by
  run_tac nativeRow
private def copyCore_5 (k : Nat) : CopyRows (Safe:=Safe2 k) 3 5 6 (ns2 k 1150) (ns2 k 1277) := by
  exact copyMk (ns2 k 1222) (ns2 k 1172) (ns2 k 1195) (ns2 k 1262) (decCode_38 k) (incCode_39 k) (incCode_40 k) (decCode_41 k) (incCode_42 k)
private theorem macroEntry_5 (k : Nat) : (machine2 k).step (ns2 k 1149) none=(ns2 k 1150,none,Move.stay) := by
  run_tac nativeRow
private def transferCore_6 (k : Nat) : TransferRows (Safe:=Safe2 k) 5 11 (ns2 k 1814) (ns2 k 1895) := by
  exact transferMk (ns2 k 1848) (decCode_50 k) (incCode_51 k)
private theorem macroEntry_6 (k : Nat) : (machine2 k).step (ns2 k 1813) none=(ns2 k 1814,none,Move.stay) := by
  run_tac nativeRow
private def copyCore_7 (k : Nat) : CopyRows (Safe:=Safe2 k) 3 5 6 (ns2 k 2002) (ns2 k 2129) := by
  exact copyMk (ns2 k 2074) (ns2 k 2024) (ns2 k 2047) (ns2 k 2114) (decCode_54 k) (incCode_55 k) (incCode_56 k) (decCode_57 k) (incCode_58 k)
private theorem macroEntry_7 (k : Nat) : (machine2 k).step (ns2 k 2001) none=(ns2 k 2002,none,Move.stay) := by
  run_tac nativeRow
private def transferCore_8 (k : Nat) : TransferRows (Safe:=Safe2 k) 5 11 (ns2 k 2620) (ns2 k 2701) := by
  exact transferMk (ns2 k 2654) (decCode_66 k) (incCode_67 k)
private theorem macroEntry_8 (k : Nat) : (machine2 k).step (ns2 k 2619) none=(ns2 k 2620,none,Move.stay) := by
  run_tac nativeRow
private def copyCore_9 (k : Nat) : CopyRows (Safe:=Safe2 k) 3 5 6 (ns2 k 2704) (ns2 k 2831) := by
  exact copyMk (ns2 k 2776) (ns2 k 2726) (ns2 k 2749) (ns2 k 2816) (decCode_68 k) (incCode_69 k) (incCode_70 k) (decCode_71 k) (incCode_72 k)
private theorem macroEntry_9 (k : Nat) : (machine2 k).step (ns2 k 2703) none=(ns2 k 2704,none,Move.stay) := by
  run_tac nativeRow
private theorem fromHCode (k : Nat) : FromHRows (Safe:=Safe2 k) (ns2 k 1) (ns2 k 4) := by
  refine ⟨ns2 k 2,ns2 k 3,nsSafe k 1,nsSafe k 2,nsSafe k 3,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
end NormalFinalClosure
