import NormalFinalClosure.NavigationRows1
import NormalFinalClosure.NavigationRows2
import NormalFinalClosure.NavigationRows3
import NormalFinalClosure.NavigationRows4
import NormalFinalClosure.SourceLeft2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["ns2","Safe2","ns2_safe"]),
    (`NormalFinalClosure.CounterSupport2,`NormalFinalClosure,["nativeRow"]),
    (`NormalFinalClosure.SourceRoute2,`NormalFinalClosure,["DSToRows","SDToRows","LocateRows","RestoreRows"]),
    (`NormalFinalClosure.SourceAdvance2,`NormalFinalClosure,["AdvanceRows"]),
    (`NormalFinalClosure.SourceLeft2,`NormalFinalClosure,["LeftTailRows","PhysicalLeftRows","EOFLeftRows"]),
    (`NormalFinalClosure.NavigationRows1,`NormalFinalClosure,["h_to_d_1","d_to_h_493","h_to_s_497","s_to_h_505","h_to_d_508","s_to_h_512","h_to_d_515","d_to_h_546","h_to_s_550","s_to_h_558","h_to_d_561","s_to_h_565","h_to_d_568","d_to_h_599","h_to_s_603","s_to_h_609","h_to_d_612","s_to_h_616","h_to_d_619","d_to_h_1118","h_to_s_1122","s_to_h_1130","h_to_d_1133"]),
    (`NormalFinalClosure.NavigationRows2,`NormalFinalClosure,["s_to_h_1137","h_to_d_1140","s_to_h_1143","h_to_d_1146","d_to_h_1475","h_to_s_1479","s_to_h_1487","h_to_d_1490","s_to_h_1494","h_to_d_1497","s_to_h_1500","h_to_d_1503","d_to_h_1597","h_to_s_1601","s_to_h_1609","h_to_d_1612","s_to_h_1616","h_to_d_1619","s_to_h_1622","h_to_d_1625","d_to_h_1970","h_to_s_1974","s_to_h_1982"]),
    (`NormalFinalClosure.NavigationRows3,`NormalFinalClosure,["h_to_d_1985","s_to_h_1989","h_to_d_1992","s_to_h_1995","h_to_d_1998","d_to_h_2281","h_to_s_2285","s_to_h_2293","h_to_d_2296","s_to_h_2300","h_to_d_2303","s_to_h_2306","h_to_d_2309","d_to_h_2403","h_to_s_2407","s_to_h_2415","h_to_d_2418","s_to_h_2422","h_to_d_2425","s_to_h_2428","h_to_d_2431","d_to_h_3122","h_to_s_3126"]),
    (`NormalFinalClosure.NavigationRows4,`NormalFinalClosure,["s_to_h_3133","h_to_d_3136","d_to_h_3303","d_to_h_3308","h_to_s_3312","s_to_h_3319","h_to_d_3322","d_to_h_3489","d_to_h_3659","d_to_h_3664","h_to_s_3668","s_to_h_3675","h_to_d_3678","d_to_h_3845","d_to_h_3850","h_to_s_3854","s_to_h_3861","h_to_d_3864","d_to_h_4031","d_to_h_4201"])] do
    for leaf in leaves do
      let name:=Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns) leaf
      let some ci:=e.find? name | throwError "Missing exact source literal record"
      let some i:=e.getModuleIdxFor? name | throwError "Missing source literal owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong source literal owner"
      logInfo m!"source-literal-record-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) name::st.openDecls}
private theorem ds_493 (k : Nat) : DSToRows (Safe:=Safe2 k) (ns2 k 493) (ns2 k 500) :=
  ⟨ns2 k 497,d_to_h_493 k,h_to_s_497 k⟩
private theorem sd_505 (k : Nat) : SDToRows (Safe:=Safe2 k) (ns2 k 505) (ns2 k 465) :=
  ⟨ns2 k 508,s_to_h_505 k,h_to_d_508 k⟩
private theorem sd_512 (k : Nat) : SDToRows (Safe:=Safe2 k) (ns2 k 512) (ns2 k 518) :=
  ⟨ns2 k 515,s_to_h_512 k,h_to_d_515 k⟩
private theorem ds_546 (k : Nat) : DSToRows (Safe:=Safe2 k) (ns2 k 546) (ns2 k 553) :=
  ⟨ns2 k 550,d_to_h_546 k,h_to_s_550 k⟩
private theorem sd_558 (k : Nat) : SDToRows (Safe:=Safe2 k) (ns2 k 558) (ns2 k 465) :=
  ⟨ns2 k 561,s_to_h_558 k,h_to_d_561 k⟩
private theorem sd_565 (k : Nat) : SDToRows (Safe:=Safe2 k) (ns2 k 565) (ns2 k 518) :=
  ⟨ns2 k 568,s_to_h_565 k,h_to_d_568 k⟩
private theorem ds_599 (k : Nat) : DSToRows (Safe:=Safe2 k) (ns2 k 599) (ns2 k 606) :=
  ⟨ns2 k 603,d_to_h_599 k,h_to_s_603 k⟩
private theorem sd_609 (k : Nat) : SDToRows (Safe:=Safe2 k) (ns2 k 609) (ns2 k 465) :=
  ⟨ns2 k 612,s_to_h_609 k,h_to_d_612 k⟩
private theorem sd_616 (k : Nat) : SDToRows (Safe:=Safe2 k) (ns2 k 616) (ns2 k 518) :=
  ⟨ns2 k 619,s_to_h_616 k,h_to_d_619 k⟩
private theorem ds_1118 (k : Nat) : DSToRows (Safe:=Safe2 k) (ns2 k 1118) (ns2 k 1125) :=
  ⟨ns2 k 1122,d_to_h_1118 k,h_to_s_1122 k⟩
private theorem sd_1130 (k : Nat) : SDToRows (Safe:=Safe2 k) (ns2 k 1130) (ns2 k 850) :=
  ⟨ns2 k 1133,s_to_h_1130 k,h_to_d_1133 k⟩
private theorem sd_1137 (k : Nat) : SDToRows (Safe:=Safe2 k) (ns2 k 1137) (ns2 k 1628) :=
  ⟨ns2 k 1140,s_to_h_1137 k,h_to_d_1140 k⟩
private theorem sd_1143 (k : Nat) : SDToRows (Safe:=Safe2 k) (ns2 k 1143) (ns2 k 2434) :=
  ⟨ns2 k 1146,s_to_h_1143 k,h_to_d_1146 k⟩
private theorem ds_1475 (k : Nat) : DSToRows (Safe:=Safe2 k) (ns2 k 1475) (ns2 k 1482) :=
  ⟨ns2 k 1479,d_to_h_1475 k,h_to_s_1479 k⟩
private theorem sd_1487 (k : Nat) : SDToRows (Safe:=Safe2 k) (ns2 k 1487) (ns2 k 1277) :=
  ⟨ns2 k 1490,s_to_h_1487 k,h_to_d_1490 k⟩
private theorem sd_1494 (k : Nat) : SDToRows (Safe:=Safe2 k) (ns2 k 1494) (ns2 k 2129) :=
  ⟨ns2 k 1497,s_to_h_1494 k,h_to_d_1497 k⟩
private theorem sd_1500 (k : Nat) : SDToRows (Safe:=Safe2 k) (ns2 k 1500) (ns2 k 2831) :=
  ⟨ns2 k 1503,s_to_h_1500 k,h_to_d_1503 k⟩
private theorem ds_1597 (k : Nat) : DSToRows (Safe:=Safe2 k) (ns2 k 1597) (ns2 k 1604) :=
  ⟨ns2 k 1601,d_to_h_1597 k,h_to_s_1601 k⟩
private theorem sd_1609 (k : Nat) : SDToRows (Safe:=Safe2 k) (ns2 k 1609) (ns2 k 1506) :=
  ⟨ns2 k 1612,s_to_h_1609 k,h_to_d_1612 k⟩
private theorem sd_1616 (k : Nat) : SDToRows (Safe:=Safe2 k) (ns2 k 1616) (ns2 k 2312) :=
  ⟨ns2 k 1619,s_to_h_1616 k,h_to_d_1619 k⟩
private theorem sd_1622 (k : Nat) : SDToRows (Safe:=Safe2 k) (ns2 k 1622) (ns2 k 3030) :=
  ⟨ns2 k 1625,s_to_h_1622 k,h_to_d_1625 k⟩
private theorem ds_1970 (k : Nat) : DSToRows (Safe:=Safe2 k) (ns2 k 1970) (ns2 k 1977) :=
  ⟨ns2 k 1974,d_to_h_1970 k,h_to_s_1974 k⟩
private theorem sd_1982 (k : Nat) : SDToRows (Safe:=Safe2 k) (ns2 k 1982) (ns2 k 850) :=
  ⟨ns2 k 1985,s_to_h_1982 k,h_to_d_1985 k⟩
private theorem sd_1989 (k : Nat) : SDToRows (Safe:=Safe2 k) (ns2 k 1989) (ns2 k 1628) :=
  ⟨ns2 k 1992,s_to_h_1989 k,h_to_d_1992 k⟩
private theorem sd_1995 (k : Nat) : SDToRows (Safe:=Safe2 k) (ns2 k 1995) (ns2 k 2434) :=
  ⟨ns2 k 1998,s_to_h_1995 k,h_to_d_1998 k⟩
private theorem ds_2281 (k : Nat) : DSToRows (Safe:=Safe2 k) (ns2 k 2281) (ns2 k 2288) :=
  ⟨ns2 k 2285,d_to_h_2281 k,h_to_s_2285 k⟩
private theorem sd_2293 (k : Nat) : SDToRows (Safe:=Safe2 k) (ns2 k 2293) (ns2 k 1277) :=
  ⟨ns2 k 2296,s_to_h_2293 k,h_to_d_2296 k⟩
private theorem sd_2300 (k : Nat) : SDToRows (Safe:=Safe2 k) (ns2 k 2300) (ns2 k 2129) :=
  ⟨ns2 k 2303,s_to_h_2300 k,h_to_d_2303 k⟩
private theorem sd_2306 (k : Nat) : SDToRows (Safe:=Safe2 k) (ns2 k 2306) (ns2 k 2831) :=
  ⟨ns2 k 2309,s_to_h_2306 k,h_to_d_2309 k⟩
private theorem ds_2403 (k : Nat) : DSToRows (Safe:=Safe2 k) (ns2 k 2403) (ns2 k 2410) :=
  ⟨ns2 k 2407,d_to_h_2403 k,h_to_s_2407 k⟩
private theorem sd_2415 (k : Nat) : SDToRows (Safe:=Safe2 k) (ns2 k 2415) (ns2 k 1506) :=
  ⟨ns2 k 2418,s_to_h_2415 k,h_to_d_2418 k⟩
private theorem sd_2422 (k : Nat) : SDToRows (Safe:=Safe2 k) (ns2 k 2422) (ns2 k 2312) :=
  ⟨ns2 k 2425,s_to_h_2422 k,h_to_d_2425 k⟩
private theorem sd_2428 (k : Nat) : SDToRows (Safe:=Safe2 k) (ns2 k 2428) (ns2 k 3030) :=
  ⟨ns2 k 2431,s_to_h_2428 k,h_to_d_2431 k⟩
private theorem ds_3122 (k : Nat) : DSToRows (Safe:=Safe2 k) (ns2 k 3122) (ns2 k 3129) :=
  ⟨ns2 k 3126,d_to_h_3122 k,h_to_s_3126 k⟩
private theorem sd_3133 (k : Nat) : SDToRows (Safe:=Safe2 k) (ns2 k 3133) (ns2 k 3139) :=
  ⟨ns2 k 3136,s_to_h_3133 k,h_to_d_3136 k⟩
private theorem ds_3308 (k : Nat) : DSToRows (Safe:=Safe2 k) (ns2 k 3308) (ns2 k 3315) :=
  ⟨ns2 k 3312,d_to_h_3308 k,h_to_s_3312 k⟩
private theorem sd_3319 (k : Nat) : SDToRows (Safe:=Safe2 k) (ns2 k 3319) (ns2 k 3325) :=
  ⟨ns2 k 3322,s_to_h_3319 k,h_to_d_3322 k⟩
private theorem ds_3664 (k : Nat) : DSToRows (Safe:=Safe2 k) (ns2 k 3664) (ns2 k 3671) :=
  ⟨ns2 k 3668,d_to_h_3664 k,h_to_s_3668 k⟩
private theorem sd_3675 (k : Nat) : SDToRows (Safe:=Safe2 k) (ns2 k 3675) (ns2 k 3681) :=
  ⟨ns2 k 3678,s_to_h_3675 k,h_to_d_3678 k⟩
private theorem ds_3850 (k : Nat) : DSToRows (Safe:=Safe2 k) (ns2 k 3850) (ns2 k 3857) :=
  ⟨ns2 k 3854,d_to_h_3850 k,h_to_s_3854 k⟩
private theorem sd_3861 (k : Nat) : SDToRows (Safe:=Safe2 k) (ns2 k 3861) (ns2 k 3867) :=
  ⟨ns2 k 3864,s_to_h_3861 k,h_to_d_3864 k⟩
private theorem locate_493 (k : Nat) : LocateRows (Safe:=Safe2 k) (ns2 k 493) (ns2 k 502) := by
  refine ⟨ns2 k 500,ns2 k 501,ds_493 k,ns2_safe k 500,ns2_safe k 501,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem locate_546 (k : Nat) : LocateRows (Safe:=Safe2 k) (ns2 k 546) (ns2 k 555) := by
  refine ⟨ns2 k 553,ns2 k 554,ds_546 k,ns2_safe k 553,ns2_safe k 554,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem locate_1118 (k : Nat) : LocateRows (Safe:=Safe2 k) (ns2 k 1118) (ns2 k 1127) := by
  refine ⟨ns2 k 1125,ns2 k 1126,ds_1118 k,ns2_safe k 1125,ns2_safe k 1126,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem locate_1475 (k : Nat) : LocateRows (Safe:=Safe2 k) (ns2 k 1475) (ns2 k 1484) := by
  refine ⟨ns2 k 1482,ns2 k 1483,ds_1475 k,ns2_safe k 1482,ns2_safe k 1483,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem locate_1597 (k : Nat) : LocateRows (Safe:=Safe2 k) (ns2 k 1597) (ns2 k 1606) := by
  refine ⟨ns2 k 1604,ns2 k 1605,ds_1597 k,ns2_safe k 1604,ns2_safe k 1605,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem locate_1970 (k : Nat) : LocateRows (Safe:=Safe2 k) (ns2 k 1970) (ns2 k 1979) := by
  refine ⟨ns2 k 1977,ns2 k 1978,ds_1970 k,ns2_safe k 1977,ns2_safe k 1978,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem locate_2281 (k : Nat) : LocateRows (Safe:=Safe2 k) (ns2 k 2281) (ns2 k 2290) := by
  refine ⟨ns2 k 2288,ns2 k 2289,ds_2281 k,ns2_safe k 2288,ns2_safe k 2289,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem locate_2403 (k : Nat) : LocateRows (Safe:=Safe2 k) (ns2 k 2403) (ns2 k 2412) := by
  refine ⟨ns2 k 2410,ns2 k 2411,ds_2403 k,ns2_safe k 2410,ns2_safe k 2411,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem locate_3122 (k : Nat) : LocateRows (Safe:=Safe2 k) (ns2 k 3122) (ns2 k 3131) := by
  refine ⟨ns2 k 3129,ns2 k 3130,ds_3122 k,ns2_safe k 3129,ns2_safe k 3130,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem locate_3308 (k : Nat) : LocateRows (Safe:=Safe2 k) (ns2 k 3308) (ns2 k 3317) := by
  refine ⟨ns2 k 3315,ns2 k 3316,ds_3308 k,ns2_safe k 3315,ns2_safe k 3316,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem locate_3664 (k : Nat) : LocateRows (Safe:=Safe2 k) (ns2 k 3664) (ns2 k 3673) := by
  refine ⟨ns2 k 3671,ns2 k 3672,ds_3664 k,ns2_safe k 3671,ns2_safe k 3672,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem locate_3850 (k : Nat) : LocateRows (Safe:=Safe2 k) (ns2 k 3850) (ns2 k 3859) := by
  refine ⟨ns2 k 3857,ns2 k 3858,ds_3850 k,ns2_safe k 3857,ns2_safe k 3858,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem restore_3122 (k : Nat) : RestoreRows (Safe:=Safe2 k) (ns2 k 3122) (ns2 k 3139) false := by
  refine ⟨ns2 k 3131,ns2 k 3132,ns2 k 3133,locate_3122 k,ns2_safe k 3131,ns2_safe k 3132,?_,?_,?_,sd_3133 k⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem restore_3308 (k : Nat) : RestoreRows (Safe:=Safe2 k) (ns2 k 3308) (ns2 k 3325) true := by
  refine ⟨ns2 k 3317,ns2 k 3318,ns2 k 3319,locate_3308 k,ns2_safe k 3317,ns2_safe k 3318,?_,?_,?_,sd_3319 k⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem virtualRestore_3494 (k : Nat) : (machine2 k).step (ns2 k 3494) none=(ns2 k 3495,none,.stay) := by
  run_tac nativeRow
private theorem restore_3664 (k : Nat) : RestoreRows (Safe:=Safe2 k) (ns2 k 3664) (ns2 k 3681) false := by
  refine ⟨ns2 k 3673,ns2 k 3674,ns2 k 3675,locate_3664 k,ns2_safe k 3673,ns2_safe k 3674,?_,?_,?_,sd_3675 k⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem restore_3850 (k : Nat) : RestoreRows (Safe:=Safe2 k) (ns2 k 3850) (ns2 k 3867) true := by
  refine ⟨ns2 k 3859,ns2 k 3860,ns2 k 3861,locate_3850 k,ns2_safe k 3859,ns2_safe k 3860,?_,?_,?_,sd_3861 k⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem virtualRestore_4036 (k : Nat) : (machine2 k).step (ns2 k 4036) none=(ns2 k 4037,none,.stay) := by
  run_tac nativeRow
private theorem leftTail_503 (k : Nat) : LeftTailRows (Safe:=Safe2 k) (ns2 k 503) (fun b=>if b then ns2 k 518 else ns2 k 465) := by
  refine ⟨(fun b=>if b then ns2 k 511 else ns2 k 504),(fun b=>if b then ns2 k 512 else ns2 k 505),ns2_safe k 503,?_,?_,?_,?_,?_⟩
  · intro b;cases b <;> exact ns2_safe k _
  · intro b;cases b <;> (run_tac nativeRow)
  · intro b v
    cases b with
    | false=>
      cases v with
      | false=>
        change (machine2 k).step (ns2 k 504) (some false)=_
        run_tac nativeRow
      | true=>
        change (machine2 k).step (ns2 k 504) (some true)=_
        run_tac nativeRow
    | true=>
      cases v with
      | false=>
        change (machine2 k).step (ns2 k 511) (some false)=_
        run_tac nativeRow
      | true=>
        change (machine2 k).step (ns2 k 511) (some true)=_
        run_tac nativeRow
  · intro b
    cases b with
    | false=>
      change (machine2 k).step (ns2 k 504) none=_
      run_tac nativeRow
    | true=>
      change (machine2 k).step (ns2 k 511) none=_
      run_tac nativeRow

  · intro b;cases b
    · exact sd_505 k
    · exact sd_512 k
private theorem left_493 (k : Nat) : PhysicalLeftRows (Safe:=Safe2 k) (ns2 k 493) (fun b=>if b then ns2 k 518 else ns2 k 465) false := by
  refine ⟨ns2 k 502,ns2 k 503,locate_493 k,ns2_safe k 502,?_,leftTail_503 k⟩
  · run_tac nativeRow
private theorem leftTail_556 (k : Nat) : LeftTailRows (Safe:=Safe2 k) (ns2 k 556) (fun b=>if b then ns2 k 518 else ns2 k 465) := by
  refine ⟨(fun b=>if b then ns2 k 564 else ns2 k 557),(fun b=>if b then ns2 k 565 else ns2 k 558),ns2_safe k 556,?_,?_,?_,?_,?_⟩
  · intro b;cases b <;> exact ns2_safe k _
  · intro b;cases b <;> (run_tac nativeRow)
  · intro b v
    cases b with
    | false=>
      cases v with
      | false=>
        change (machine2 k).step (ns2 k 557) (some false)=_
        run_tac nativeRow
      | true=>
        change (machine2 k).step (ns2 k 557) (some true)=_
        run_tac nativeRow
    | true=>
      cases v with
      | false=>
        change (machine2 k).step (ns2 k 564) (some false)=_
        run_tac nativeRow
      | true=>
        change (machine2 k).step (ns2 k 564) (some true)=_
        run_tac nativeRow
  · intro b
    cases b with
    | false=>
      change (machine2 k).step (ns2 k 557) none=_
      run_tac nativeRow
    | true=>
      change (machine2 k).step (ns2 k 564) none=_
      run_tac nativeRow

  · intro b;cases b
    · exact sd_558 k
    · exact sd_565 k
private theorem left_546 (k : Nat) : PhysicalLeftRows (Safe:=Safe2 k) (ns2 k 546) (fun b=>if b then ns2 k 518 else ns2 k 465) true := by
  refine ⟨ns2 k 555,ns2 k 556,locate_546 k,ns2_safe k 555,?_,leftTail_556 k⟩
  · run_tac nativeRow
private theorem leftTail_607 (k : Nat) : LeftTailRows (Safe:=Safe2 k) (ns2 k 607) (fun b=>if b then ns2 k 518 else ns2 k 465) := by
  refine ⟨(fun b=>if b then ns2 k 615 else ns2 k 608),(fun b=>if b then ns2 k 616 else ns2 k 609),ns2_safe k 607,?_,?_,?_,?_,?_⟩
  · intro b;cases b <;> exact ns2_safe k _
  · intro b;cases b <;> (run_tac nativeRow)
  · intro b v
    cases b with
    | false=>
      cases v with
      | false=>
        change (machine2 k).step (ns2 k 608) (some false)=_
        run_tac nativeRow
      | true=>
        change (machine2 k).step (ns2 k 608) (some true)=_
        run_tac nativeRow
    | true=>
      cases v with
      | false=>
        change (machine2 k).step (ns2 k 615) (some false)=_
        run_tac nativeRow
      | true=>
        change (machine2 k).step (ns2 k 615) (some true)=_
        run_tac nativeRow
  · intro b
    cases b with
    | false=>
      change (machine2 k).step (ns2 k 608) none=_
      run_tac nativeRow
    | true=>
      change (machine2 k).step (ns2 k 615) none=_
      run_tac nativeRow

  · intro b;cases b
    · exact sd_609 k
    · exact sd_616 k
private theorem left_599 (k : Nat) : EOFLeftRows (Safe:=Safe2 k) (ns2 k 599) (fun b=>if b then ns2 k 518 else ns2 k 465) := by
  refine ⟨ns2 k 606,ns2 k 607,ds_599 k,ns2_safe k 606,?_,leftTail_607 k⟩
  · run_tac nativeRow
end NormalFinalClosure
