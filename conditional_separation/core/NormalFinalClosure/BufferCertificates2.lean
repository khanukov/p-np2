import NormalFinalClosure.BufferAppend2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,leaves) in [
    (`NormalFinalClosure.Rows2Code,["ns2","Safe2","ns2_safe"]),
    (`NormalFinalClosure.CounterSupport2,["nativeRow","nativeRoute"]),
    (`NormalFinalClosure.BufferAppend2,["AppendRows","TripleRows"])] do
    for leaf in leaves do
      let name:=Name.str (Name.append (Name.num (Name.append `_private owner) 0) `NormalFinalClosure) leaf
      let some ci:=e.find? name | throwError "Missing actual prefix-buffer row API"
      let some i:=e.getModuleIdxFor? name | throwError "Missing buffer-row owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong buffer-row owner"
      logInfo m!"actual-prefix-buffer-row-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) name::st.openDecls}
private theorem append_1381 (k : Nat) : AppendRows (Safe:=Safe2 k) (ns2 k 1381) (ns2 k 1475) false true := by
  refine ⟨ns2 k 1401,ns2 k 1402,ns2 k 1403,ns2 k 1404,ns2 k 1405,ns2 k 1406,ns2 k 1407,ns2 k 1408,?_,?_,ns2_safe k _,ns2_safe k _,ns2_safe k _,ns2_safe k _,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 13
  · run_tac nativeRoute 13
  · refine ⟨ns2_safe k _,ns2_safe k _,ns2_safe k _,?_,?_,?_⟩
    · run_tac nativeRow
    · intro b;cases b <;> (run_tac nativeRow)
    · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem append_1428 (k : Nat) : AppendRows (Safe:=Safe2 k) (ns2 k 1428) (ns2 k 1475) false false := by
  refine ⟨ns2 k 1448,ns2 k 1449,ns2 k 1450,ns2 k 1451,ns2 k 1452,ns2 k 1453,ns2 k 1454,ns2 k 1455,?_,?_,ns2_safe k _,ns2_safe k _,ns2_safe k _,ns2_safe k _,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 13
  · run_tac nativeRoute 13
  · refine ⟨ns2_safe k _,ns2_safe k _,ns2_safe k _,?_,?_,?_⟩
    · run_tac nativeRow
    · intro b;cases b <;> (run_tac nativeRow)
    · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem append_2233 (k : Nat) : AppendRows (Safe:=Safe2 k) (ns2 k 2233) (ns2 k 2281) true false := by
  refine ⟨ns2 k 2253,ns2 k 2254,ns2 k 2255,ns2 k 2256,ns2 k 2257,ns2 k 2258,ns2 k 2259,ns2 k 2260,?_,?_,ns2_safe k _,ns2_safe k _,ns2_safe k _,ns2_safe k _,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 13
  · run_tac nativeRoute 13
  · refine ⟨ns2_safe k _,ns2_safe k _,ns2_safe k _,?_,?_,?_⟩
    · run_tac nativeRow
    · intro b;cases b <;> (run_tac nativeRow)
    · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem append_2935 (k : Nat) : AppendRows (Safe:=Safe2 k) (ns2 k 2935) (ns2 k 3029) false true := by
  refine ⟨ns2 k 2955,ns2 k 2956,ns2 k 2957,ns2 k 2958,ns2 k 2959,ns2 k 2960,ns2 k 2961,ns2 k 2962,?_,?_,ns2_safe k _,ns2_safe k _,ns2_safe k _,ns2_safe k _,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 13
  · run_tac nativeRoute 13
  · refine ⟨ns2_safe k _,ns2_safe k _,ns2_safe k _,?_,?_,?_⟩
    · run_tac nativeRow
    · intro b;cases b <;> (run_tac nativeRow)
    · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem append_2982 (k : Nat) : AppendRows (Safe:=Safe2 k) (ns2 k 2982) (ns2 k 3029) false false := by
  refine ⟨ns2 k 3002,ns2 k 3003,ns2 k 3004,ns2 k 3005,ns2 k 3006,ns2 k 3007,ns2 k 3008,ns2 k 3009,?_,?_,ns2_safe k _,ns2_safe k _,ns2_safe k _,ns2_safe k _,?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 13
  · run_tac nativeRoute 13
  · refine ⟨ns2_safe k _,ns2_safe k _,ns2_safe k _,?_,?_,?_⟩
    · run_tac nativeRow
    · intro b;cases b <;> (run_tac nativeRow)
    · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
end NormalFinalClosure
