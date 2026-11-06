import NormalFinalClosure.CompareSupport2
import NormalFinalClosure.CounterSupport2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,leaves) in [
    (`NormalFinalClosure.Rows2Code,["ns2","Safe2","ns2_safe"]),
    (`NormalFinalClosure.CounterSupport2,["nativeRow","nativeRoute"]),
    (`NormalFinalClosure.CompareSupport2,["CompareRows","RetreatRows"])] do
    for leaf in leaves do
      let name:=Name.str (Name.append (Name.num (Name.append `_private owner) 0) `NormalFinalClosure) leaf
      let some ci:=e.find? name | throwError "Missing actual compare row API"
      let some i:=e.getModuleIdxFor? name | throwError "Missing compare row owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong compare row owner"
      logInfo m!"actual-compare-row-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) name::st.openDecls}
private theorem compare_1506 (k : Nat) : CompareRows (Safe:=Safe2 k) (ns2 k 1506) (ns2 k 1597) (ns2 k 3122) (ns2 k 3664) false := by
  refine ⟨ns2 k 1526,ns2 k 1527,ns2 k 1528,ns2 k 1529,ns2 k 1530,ns2 k 1531,ns2 k 1532,ns2 k 1533,ns2 k 1553,ns2 k 1575,?_,?_,ns2_safe k _,ns2_safe k _,ns2_safe k _,ns2_safe k _,ns2_safe k _,ns2_safe k _,ns2_safe k _,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 13
  · run_tac nativeRoute 13
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b
    cases b
    · change (machine2 k).step (ns2 k 1529) (some true)=_
      run_tac nativeRow
    · change (machine2 k).step (ns2 k 1530) (some false)=_
      run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · refine ⟨ns2 k 1554,ns2 k 1555,ns2_safe k _,ns2_safe k _,?_,?_,?_,?_⟩
    · intro b;cases b <;> (run_tac nativeRow)
    · intro b;cases b <;> (run_tac nativeRow)
    · run_tac nativeRow
    · run_tac nativeRoute 13
  · refine ⟨ns2 k 1576,ns2 k 1577,ns2_safe k _,ns2_safe k _,?_,?_,?_,?_⟩
    · intro b;cases b <;> (run_tac nativeRow)
    · intro b;cases b <;> (run_tac nativeRow)
    · run_tac nativeRow
    · run_tac nativeRoute 13
private theorem compare_2312 (k : Nat) : CompareRows (Safe:=Safe2 k) (ns2 k 2312) (ns2 k 2403) (ns2 k 3308) (ns2 k 3850) true := by
  refine ⟨ns2 k 2332,ns2 k 2333,ns2 k 2334,ns2 k 2335,ns2 k 2336,ns2 k 2337,ns2 k 2338,ns2 k 2339,ns2 k 2359,ns2 k 2381,?_,?_,ns2_safe k _,ns2_safe k _,ns2_safe k _,ns2_safe k _,ns2_safe k _,ns2_safe k _,ns2_safe k _,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 13
  · run_tac nativeRoute 13
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b
    cases b
    · change (machine2 k).step (ns2 k 2335) (some true)=_
      run_tac nativeRow
    · change (machine2 k).step (ns2 k 2336) (some false)=_
      run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · refine ⟨ns2 k 2360,ns2 k 2361,ns2_safe k _,ns2_safe k _,?_,?_,?_,?_⟩
    · intro b;cases b <;> (run_tac nativeRow)
    · intro b;cases b <;> (run_tac nativeRow)
    · run_tac nativeRow
    · run_tac nativeRoute 13
  · refine ⟨ns2 k 2382,ns2 k 2383,ns2_safe k _,ns2_safe k _,?_,?_,?_,?_⟩
    · intro b;cases b <;> (run_tac nativeRow)
    · intro b;cases b <;> (run_tac nativeRow)
    · run_tac nativeRow
    · run_tac nativeRoute 13
private theorem compare_3030 (k : Nat) : CompareRows (Safe:=Safe2 k) (ns2 k 3030) (ns2 k 3121) (ns2 k 3494) (ns2 k 4036) false := by
  refine ⟨ns2 k 3050,ns2 k 3051,ns2 k 3052,ns2 k 3053,ns2 k 3054,ns2 k 3055,ns2 k 3056,ns2 k 3057,ns2 k 3077,ns2 k 3099,?_,?_,ns2_safe k _,ns2_safe k _,ns2_safe k _,ns2_safe k _,ns2_safe k _,ns2_safe k _,ns2_safe k _,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 13
  · run_tac nativeRoute 13
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b
    cases b
    · change (machine2 k).step (ns2 k 3053) (some true)=_
      run_tac nativeRow
    · change (machine2 k).step (ns2 k 3054) (some false)=_
      run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · refine ⟨ns2 k 3078,ns2 k 3079,ns2_safe k _,ns2_safe k _,?_,?_,?_,?_⟩
    · intro b;cases b <;> (run_tac nativeRow)
    · intro b;cases b <;> (run_tac nativeRow)
    · run_tac nativeRow
    · run_tac nativeRoute 13
  · refine ⟨ns2 k 3100,ns2 k 3101,ns2_safe k _,ns2_safe k _,?_,?_,?_,?_⟩
    · intro b;cases b <;> (run_tac nativeRow)
    · intro b;cases b <;> (run_tac nativeRow)
    · run_tac nativeRow
    · run_tac nativeRoute 13
end NormalFinalClosure
