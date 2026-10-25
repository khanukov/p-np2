import NormalFinalClosure.BufferNative2
import NormalFinalClosure.SourceConsumer2
import NormalFinalClosure.BECode2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["DecRows"]),
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["ns2","Safe2"]),
    (`NormalFinalClosure.CounterSupport2,`NormalFinalClosure,["nativeRow"]),
    (`NormalFinalClosure.BECode2,`NormalFinalClosure,["selectState"]),
    (`NormalFinalClosure.BufferAppend2,`NormalFinalClosure,["AppendRows"]),
    (`NormalFinalClosure.BufferCertificates2,`NormalFinalClosure,["append_1381","append_1428","append_2233","append_2935","append_2982"]),
    (`NormalFinalClosure.Copy2,`NormalFinalClosure,["CopyRows"]),
    (`NormalFinalClosure.MacroCertificates2,`NormalFinalClosure,["copyCore_5","copyCore_7","copyCore_9","macroEntry_5","macroEntry_7","macroEntry_9"]),
    (`NormalFinalClosure.CodeCertificates2,`NormalFinalClosure,["decCode_43","decCode_44","decCode_59","decCode_60","decCode_73","decCode_74"]),
    (`NormalFinalClosure.BECode2,`NormalFinalClosure,["beDone"]),
    (`NormalFinalClosure.SourceAdvance2,`NormalFinalClosure,["AdvanceRows"]),
    (`NormalFinalClosure.AdvanceCertificates2,`NormalFinalClosure,["advance_1475","advance_2281","virtualAdvance_3029"]),
    (`NormalFinalClosure.NativeCleanup2,`NormalFinalClosure,["start"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing actual prefix consumer code {name}"
      let some i:=e.getModuleIdxFor? name | throwError "Missing prefix consumer owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong prefix consumer owner"
      logInfo m!"actual-prefix-consumer-code-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous (leaf.splitOn ".").getLast!) name::st.openDecls}
private def prefixState (k : Nat) (m : Fin 3) := selectState k m 1277 2129 2831
private def prefixTaken (k : Nat) (m : Fin 3) := selectState k m 1311 2163 2865
private def prefixActive (k : Nat) (m : Fin 3) := selectState k m 1381 2233 2935
private def prefixInactive (k : Nat) (m : Fin 3) := selectState k m 1428 2280 2982
private def prefixAdvance (k : Nat) (m : Fin 3) := selectState k m 1475 2281 3029
private def compareState (k : Nat) (m : Fin 3) := selectState k m 1506 2312 3030
private def prefixCopy (k : Nat) (m : Fin 3) := selectState k m 1150 2002 2704
private def activeCode (m : Fin 3) : Nat := if m.val=1 then 2 else 1
private def prefixCopyCode (k : Nat) (m : Fin 3) :
    CopyRows (Safe:=Safe2 k) 3 5 6 (prefixCopy k m) (prefixState k m) := by
  by_cases zero:m.val=0
  · have eq:m=0:=Fin.ext zero
    subst m
    exact copyCore_5 k
  · by_cases one:m.val=1
    · have eq:m=1:=Fin.ext one
      subst m
      exact copyCore_7 k
    · have eq:m=2:=Fin.ext (by omega)
      subst m
      exact copyCore_9 k
private theorem prefix_entry (k : Nat) (m : Fin 3) :
    (machine2 k).step (beDone k m) none=(prefixCopy k m,none,.stay) := by
  fin_cases m
  · exact macroEntry_5 k
  · exact macroEntry_7 k
  · exact macroEntry_9 k
private theorem prefix_dec (k : Nat) (m : Fin 3) :
    DecRows (Safe:=Safe2 k) 5 (prefixState k m) (compareState k m) (prefixTaken k m) := by
  fin_cases m
  · exact decCode_43 k
  · exact decCode_59 k
  · exact decCode_73 k
private theorem active_dec (k : Nat) (m : Fin 3) :
    DecRows (Safe:=Safe2 k) 11 (prefixTaken k m) (prefixInactive k m) (prefixActive k m) := by
  fin_cases m
  · exact decCode_44 k
  · exact decCode_60 k
  · exact decCode_74 k
private theorem append_active (k : Nat) (m : Fin 3) :
    AppendRows (Safe:=Safe2 k) (prefixActive k m) (prefixAdvance k m)
      (Nat.testBit (activeCode m) 1) (Nat.testBit (activeCode m) 0) := by
  fin_cases m
  · exact append_1381 k
  · exact append_2233 k
  · exact append_2935 k
private theorem append_inactive (k : Nat) (m : Fin 3) (zero:m.val≠1) :
    AppendRows (Safe:=Safe2 k) (prefixInactive k m) (prefixAdvance k m) false false := by
  fin_cases m
  · exact append_1428 k
  · norm_num at zero
  · exact append_2982 k
private theorem inactive_one (k : Nat) :
    (machine2 k).step (prefixInactive k 1) none=(start k false 1,none,.stay) := by
  change (machine2 k).step (ns2 k 2280) none=_
  run_tac nativeRow
private theorem prefix_advance_code (k : Nat) (b : Bool) :
    AdvanceRows (Safe:=Safe2 k) (prefixAdvance k (if b then 1 else 0)) (prefixState k) b := by
  cases b
  · exact advance_1475 k
  · exact advance_2281 k
private theorem prefix_virtual_advance (k : Nat) :
    (machine2 k).step (prefixAdvance k 2) none=(prefixState k 2,none,.stay) := by
  exact virtualAdvance_3029 k
end NormalFinalClosure
