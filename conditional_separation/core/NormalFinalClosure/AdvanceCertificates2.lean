import NormalFinalClosure.SourceCertificates2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["ns2","Safe2","ns2_safe"]),
    (`NormalFinalClosure.CounterSupport2,`NormalFinalClosure,["nativeRow"]),
    (`NormalFinalClosure.SourceAdvance2,`NormalFinalClosure,["AdvanceRows"]),
    (`NormalFinalClosure.SourceCertificates2,`NormalFinalClosure,["locate_1118","sd_1143","sd_1130","sd_1137","locate_1475","sd_1500","sd_1487","sd_1494","locate_1597","sd_1622","sd_1609","sd_1616","locate_1970","sd_1995","sd_1982","sd_1989","locate_2281","sd_2306","sd_2293","sd_2300","locate_2403","sd_2428","sd_2415","sd_2422"])] do
    for leaf in leaves do
      let name:=Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns) leaf
      let some ci:=e.find? name | throwError "Missing exact physical advance API"
      let some i:=e.getModuleIdxFor? name | throwError "Missing physical advance owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong physical advance owner"
      logInfo m!"physical-advance-exact-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) name::st.openDecls}
private theorem advance_1118 (k : Nat) : AdvanceRows (Safe:=Safe2 k) (ns2 k 1118) (fun mode : Fin 3=>if mode.val=0 then ns2 k 850 else if mode.val=1 then ns2 k 1628 else ns2 k 2434) false := by
  refine ⟨ns2 k 1127,ns2 k 1128,ns2 k 1143,(fun b=>if b then ns2 k 1136 else ns2 k 1129),(fun b=>if b then ns2 k 1137 else ns2 k 1130),locate_1118 k,ns2_safe k 1127,ns2_safe k 1128,?_,?_,sd_1143 k,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> exact ns2_safe k _
  · intro b;cases b <;> (run_tac nativeRow)
  · intro b v
    cases b with
    | false=>
      cases v with
      | false=>
        change (machine2 k).step (ns2 k 1129) (some false)=_
        run_tac nativeRow
      | true=>
        change (machine2 k).step (ns2 k 1129) (some true)=_
        run_tac nativeRow
    | true=>
      cases v with
      | false=>
        change (machine2 k).step (ns2 k 1136) (some false)=_
        run_tac nativeRow
      | true=>
        change (machine2 k).step (ns2 k 1136) (some true)=_
        run_tac nativeRow
  · intro b
    cases b with
    | false=>
      change (machine2 k).step (ns2 k 1129) none=_
      run_tac nativeRow
    | true=>
      change (machine2 k).step (ns2 k 1136) none=_
      run_tac nativeRow
  · intro b;cases b
    · exact sd_1130 k
    · exact sd_1137 k
private theorem advance_1475 (k : Nat) : AdvanceRows (Safe:=Safe2 k) (ns2 k 1475) (fun mode : Fin 3=>if mode.val=0 then ns2 k 1277 else if mode.val=1 then ns2 k 2129 else ns2 k 2831) false := by
  refine ⟨ns2 k 1484,ns2 k 1485,ns2 k 1500,(fun b=>if b then ns2 k 1493 else ns2 k 1486),(fun b=>if b then ns2 k 1494 else ns2 k 1487),locate_1475 k,ns2_safe k 1484,ns2_safe k 1485,?_,?_,sd_1500 k,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> exact ns2_safe k _
  · intro b;cases b <;> (run_tac nativeRow)
  · intro b v
    cases b with
    | false=>
      cases v with
      | false=>
        change (machine2 k).step (ns2 k 1486) (some false)=_
        run_tac nativeRow
      | true=>
        change (machine2 k).step (ns2 k 1486) (some true)=_
        run_tac nativeRow
    | true=>
      cases v with
      | false=>
        change (machine2 k).step (ns2 k 1493) (some false)=_
        run_tac nativeRow
      | true=>
        change (machine2 k).step (ns2 k 1493) (some true)=_
        run_tac nativeRow
  · intro b
    cases b with
    | false=>
      change (machine2 k).step (ns2 k 1486) none=_
      run_tac nativeRow
    | true=>
      change (machine2 k).step (ns2 k 1493) none=_
      run_tac nativeRow
  · intro b;cases b
    · exact sd_1487 k
    · exact sd_1494 k
private theorem advance_1597 (k : Nat) : AdvanceRows (Safe:=Safe2 k) (ns2 k 1597) (fun mode : Fin 3=>if mode.val=0 then ns2 k 1506 else if mode.val=1 then ns2 k 2312 else ns2 k 3030) false := by
  refine ⟨ns2 k 1606,ns2 k 1607,ns2 k 1622,(fun b=>if b then ns2 k 1615 else ns2 k 1608),(fun b=>if b then ns2 k 1616 else ns2 k 1609),locate_1597 k,ns2_safe k 1606,ns2_safe k 1607,?_,?_,sd_1622 k,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> exact ns2_safe k _
  · intro b;cases b <;> (run_tac nativeRow)
  · intro b v
    cases b with
    | false=>
      cases v with
      | false=>
        change (machine2 k).step (ns2 k 1608) (some false)=_
        run_tac nativeRow
      | true=>
        change (machine2 k).step (ns2 k 1608) (some true)=_
        run_tac nativeRow
    | true=>
      cases v with
      | false=>
        change (machine2 k).step (ns2 k 1615) (some false)=_
        run_tac nativeRow
      | true=>
        change (machine2 k).step (ns2 k 1615) (some true)=_
        run_tac nativeRow
  · intro b
    cases b with
    | false=>
      change (machine2 k).step (ns2 k 1608) none=_
      run_tac nativeRow
    | true=>
      change (machine2 k).step (ns2 k 1615) none=_
      run_tac nativeRow
  · intro b;cases b
    · exact sd_1609 k
    · exact sd_1616 k
private theorem advance_1970 (k : Nat) : AdvanceRows (Safe:=Safe2 k) (ns2 k 1970) (fun mode : Fin 3=>if mode.val=0 then ns2 k 850 else if mode.val=1 then ns2 k 1628 else ns2 k 2434) true := by
  refine ⟨ns2 k 1979,ns2 k 1980,ns2 k 1995,(fun b=>if b then ns2 k 1988 else ns2 k 1981),(fun b=>if b then ns2 k 1989 else ns2 k 1982),locate_1970 k,ns2_safe k 1979,ns2_safe k 1980,?_,?_,sd_1995 k,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> exact ns2_safe k _
  · intro b;cases b <;> (run_tac nativeRow)
  · intro b v
    cases b with
    | false=>
      cases v with
      | false=>
        change (machine2 k).step (ns2 k 1981) (some false)=_
        run_tac nativeRow
      | true=>
        change (machine2 k).step (ns2 k 1981) (some true)=_
        run_tac nativeRow
    | true=>
      cases v with
      | false=>
        change (machine2 k).step (ns2 k 1988) (some false)=_
        run_tac nativeRow
      | true=>
        change (machine2 k).step (ns2 k 1988) (some true)=_
        run_tac nativeRow
  · intro b
    cases b with
    | false=>
      change (machine2 k).step (ns2 k 1981) none=_
      run_tac nativeRow
    | true=>
      change (machine2 k).step (ns2 k 1988) none=_
      run_tac nativeRow
  · intro b;cases b
    · exact sd_1982 k
    · exact sd_1989 k
private theorem advance_2281 (k : Nat) : AdvanceRows (Safe:=Safe2 k) (ns2 k 2281) (fun mode : Fin 3=>if mode.val=0 then ns2 k 1277 else if mode.val=1 then ns2 k 2129 else ns2 k 2831) true := by
  refine ⟨ns2 k 2290,ns2 k 2291,ns2 k 2306,(fun b=>if b then ns2 k 2299 else ns2 k 2292),(fun b=>if b then ns2 k 2300 else ns2 k 2293),locate_2281 k,ns2_safe k 2290,ns2_safe k 2291,?_,?_,sd_2306 k,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> exact ns2_safe k _
  · intro b;cases b <;> (run_tac nativeRow)
  · intro b v
    cases b with
    | false=>
      cases v with
      | false=>
        change (machine2 k).step (ns2 k 2292) (some false)=_
        run_tac nativeRow
      | true=>
        change (machine2 k).step (ns2 k 2292) (some true)=_
        run_tac nativeRow
    | true=>
      cases v with
      | false=>
        change (machine2 k).step (ns2 k 2299) (some false)=_
        run_tac nativeRow
      | true=>
        change (machine2 k).step (ns2 k 2299) (some true)=_
        run_tac nativeRow
  · intro b
    cases b with
    | false=>
      change (machine2 k).step (ns2 k 2292) none=_
      run_tac nativeRow
    | true=>
      change (machine2 k).step (ns2 k 2299) none=_
      run_tac nativeRow
  · intro b;cases b
    · exact sd_2293 k
    · exact sd_2300 k
private theorem advance_2403 (k : Nat) : AdvanceRows (Safe:=Safe2 k) (ns2 k 2403) (fun mode : Fin 3=>if mode.val=0 then ns2 k 1506 else if mode.val=1 then ns2 k 2312 else ns2 k 3030) true := by
  refine ⟨ns2 k 2412,ns2 k 2413,ns2 k 2428,(fun b=>if b then ns2 k 2421 else ns2 k 2414),(fun b=>if b then ns2 k 2422 else ns2 k 2415),locate_2403 k,ns2_safe k 2412,ns2_safe k 2413,?_,?_,sd_2428 k,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · intro b;cases b <;> exact ns2_safe k _
  · intro b;cases b <;> (run_tac nativeRow)
  · intro b v
    cases b with
    | false=>
      cases v with
      | false=>
        change (machine2 k).step (ns2 k 2414) (some false)=_
        run_tac nativeRow
      | true=>
        change (machine2 k).step (ns2 k 2414) (some true)=_
        run_tac nativeRow
    | true=>
      cases v with
      | false=>
        change (machine2 k).step (ns2 k 2421) (some false)=_
        run_tac nativeRow
      | true=>
        change (machine2 k).step (ns2 k 2421) (some true)=_
        run_tac nativeRow
  · intro b
    cases b with
    | false=>
      change (machine2 k).step (ns2 k 2414) none=_
      run_tac nativeRow
    | true=>
      change (machine2 k).step (ns2 k 2421) none=_
      run_tac nativeRow
  · intro b;cases b
    · exact sd_2415 k
    · exact sd_2422 k
private theorem virtualAdvance_2702 (k : Nat) : (machine2 k).step (ns2 k 2702) none=(ns2 k 2434,none,.stay) := by
  run_tac nativeRow
private theorem virtualAdvance_3029 (k : Nat) : (machine2 k).step (ns2 k 3029) none=(ns2 k 2831,none,.stay) := by
  run_tac nativeRow
private theorem virtualAdvance_3121 (k : Nat) : (machine2 k).step (ns2 k 3121) none=(ns2 k 3030,none,.stay) := by
  run_tac nativeRow
end NormalFinalClosure
