import NormalFinalClosure.IndexImage2
import NormalFinalClosure.MacroCertificates2
import NormalFinalClosure.NativeCleanup2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["Node","Path","DecRows","IncRows","keep"]),
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["ns2","Safe2","ns2_safe"]),
    (`NormalFinalClosure.CounterSupport2,`NormalFinalClosure,["nativeRow"]),
    (`NormalFinalClosure.IndexImage2,`NormalFinalClosure,["sourceMode","beState","beAdvance"]),
    (`NormalFinalClosure.Copy2,`NormalFinalClosure,["TransferRows"]),
    (`NormalFinalClosure.NativeCleanup2,`NormalFinalClosure,["start"]),
    (`NormalFinalClosure.CodeCertificates2,`NormalFinalClosure,["decCode_31","decCode_32","decCode_33","incCode_34","incCode_35","decCode_45","decCode_46","decCode_47","incCode_48","incCode_49","decCode_61","decCode_62","decCode_63","incCode_64","incCode_65","decCode_52","incCode_53"]),
    (`NormalFinalClosure.MacroCertificates2,`NormalFinalClosure,["transferCore_4","transferCore_6","transferCore_8","macroEntry_4","macroEntry_6","macroEntry_8"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing literal BE code API {name}"
      let some i:=e.getModuleIdxFor? name | throwError "Missing literal BE owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong literal BE owner"
      logInfo m!"literal-BE-code-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous (leaf.splitOn ".").getLast!) name::st.openDecls}
private def selectState (k : Nat) (m : Fin 3) (a b c : Nat) :=
  if m.val=0 then ns2 k a else if m.val=1 then ns2 k b else ns2 k c
private def beDone (k : Nat) (m : Fin 3) := selectState k m 1149 2001 2703
private def beTaken (k : Nat) (m : Fin 3) := selectState k m 890 1668 2474
private def doubleState (k : Nat) (m : Fin 3) := selectState k m 891 1669 2475
private def doublePay (k : Nat) (m : Fin 3) := selectState k m 961 1739 2545
private def doubleAdd1 (k : Nat) (m : Fin 3) := selectState k m 989 1767 2573
private def doubleAdd2 (k : Nat) (m : Fin 3) := selectState k m 1012 1790 2596
private def transferEntry (k : Nat) (m : Fin 3) := selectState k m 1035 1813 2619
private def transferState (k : Nat) (m : Fin 3) := selectState k m 1036 1814 2620
private def transferDone (k : Nat) (m : Fin 3) := selectState k m 1117 1895 2701
private theorem be_dec (k : Nat) (m : Fin 3) : DecRows (Safe:=Safe2 k) 6 (beState k m) (beDone k m) (beTaken k m) := by
  fin_cases m
  · exact decCode_31 k
  · exact decCode_45 k
  · exact decCode_61 k
private theorem double_take (k : Nat) (m : Fin 3) : DecRows (Safe:=Safe2 k) 11 (doubleState k m) (transferEntry k m) (doublePay k m) := by
  fin_cases m
  · exact decCode_32 k
  · exact decCode_46 k
  · exact decCode_62 k
private theorem double_pay (k : Nat) (m : Fin 3) : DecRows (Safe:=Safe2 k) 4 (doublePay k m) (start k false m) (doubleAdd1 k m) := by
  fin_cases m
  · exact decCode_33 k
  · exact decCode_47 k
  · exact decCode_63 k
private theorem double_add1 (k : Nat) (m : Fin 3) : IncRows (Safe:=Safe2 k) 5 (doubleAdd1 k m) (doubleAdd2 k m) := by
  fin_cases m
  · exact incCode_34 k
  · exact incCode_48 k
  · exact incCode_64 k
private theorem double_add2 (k : Nat) (m : Fin 3) : IncRows (Safe:=Safe2 k) 5 (doubleAdd2 k m) (doubleState k m) := by
  fin_cases m
  · exact incCode_35 k
  · exact incCode_49 k
  · exact incCode_65 k
private def transfer_code (k : Nat) (m : Fin 3) : TransferRows (Safe:=Safe2 k) 5 11 (transferState k m) (transferDone k m) := by
  by_cases h:m.val=0
  · have eq:m=0:=Fin.ext h
    subst m
    exact transferCore_4 k
  · by_cases h1:m.val=1
    · have eq:m=1:=Fin.ext h1
      subst m
      exact transferCore_6 k
    · have eq:m=2:=Fin.ext (by omega)
      subst m
      exact transferCore_8 k
private theorem double_entry (k : Nat) (m : Fin 3) :
    (machine2 k).step (beTaken k m) none=(doubleState k m,none,.stay) := by
  fin_cases m
  all_goals change (machine2 k).step (ns2 k _) none=_
  all_goals run_tac nativeRow
private theorem transfer_entry (k : Nat) (m : Fin 3) :
    (machine2 k).step (transferEntry k m) none=(transferState k m,none,.stay) := by
  fin_cases m
  · exact macroEntry_4 k
  · exact macroEntry_6 k
  · exact macroEntry_8 k
private theorem transfer_zero_exit (k : Nat) (m : Fin 3) (notOne:m.val≠1) :
    (machine2 k).step (transferDone k m) none=(beAdvance k m,none,.stay) := by
  fin_cases m
  · change (machine2 k).step (ns2 k 1117) none=_
    run_tac nativeRow
  · norm_num at notOne
  · change (machine2 k).step (ns2 k 2701) none=_
    run_tac nativeRow
private theorem bit_pay (k : Nat) : DecRows (Safe:=Safe2 k) 4 (transferDone k 1) (start k false 1) (ns2 k 1923) := decCode_52 k
private theorem bit_add (k : Nat) : IncRows (Safe:=Safe2 k) 11 (ns2 k 1923) (beAdvance k 1) := incCode_53 k
private theorem select_safe (k : Nat) (m : Fin 3) (a b c : Nat) : Safe2 k (selectState k m a b c) := by
  fin_cases m <;> exact ns2_safe k _
end NormalFinalClosure
