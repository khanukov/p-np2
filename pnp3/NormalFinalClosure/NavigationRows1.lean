import NormalFinalClosure.CounterSupport2
import NormalFinalClosure.Navigation2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["ns2","Safe2","ns2_safe"]),
    (`NormalFinalClosure.CounterSupport2,`NormalFinalClosure,["nativeRow"]),
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["FromHRows"]),
    (`NormalFinalClosure.Navigation2,`NormalFinalClosure,["HToSRows","SToHRows","DToHRows"])] do
    for leaf in leaves do
      let name:=Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns) leaf
      let some ci:=e.find? name | throwError "Missing exact navigation certificate API"
      let some i:=e.getModuleIdxFor? name | throwError "Missing navigation certificate owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong navigation certificate owner"
      let kind:=match ci with|.defnInfo _=>"definition"|.thmInfo _=>"theorem"|_=>"other"
      unless kind != "other" do throwError "Wrong navigation certificate kind"
      logInfo m!"literal-navigation-certificate-interface|{name}|{kind}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) name::st.openDecls}
private theorem h_to_d_1 (k : Nat) : FromHRows (Safe:=Safe2 k) (ns2 k 1) (ns2 k 4) := by
  refine ⟨ns2 k 2,ns2 k 3,ns2_safe k 1,ns2_safe k 2,ns2_safe k 3,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem d_to_h_493 (k : Nat) : DToHRows (Safe:=Safe2 k) (ns2 k 493) (ns2 k 497) := by
  refine ⟨ns2 k 494,ns2 k 495,ns2 k 496,ns2_safe k 493,ns2_safe k 494,ns2_safe k 495,ns2_safe k 496,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem h_to_s_497 (k : Nat) : HToSRows (Safe:=Safe2 k) (ns2 k 497) (ns2 k 500) := by
  refine ⟨ns2 k 498,ns2 k 499,ns2_safe k 497,ns2_safe k 498,ns2_safe k 499,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem s_to_h_505 (k : Nat) : SToHRows (Safe:=Safe2 k) (ns2 k 505) (ns2 k 508) := by
  refine ⟨ns2 k 506,ns2 k 507,ns2_safe k 505,ns2_safe k 506,ns2_safe k 507,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem h_to_d_508 (k : Nat) : FromHRows (Safe:=Safe2 k) (ns2 k 508) (ns2 k 465) := by
  refine ⟨ns2 k 509,ns2 k 510,ns2_safe k 508,ns2_safe k 509,ns2_safe k 510,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem s_to_h_512 (k : Nat) : SToHRows (Safe:=Safe2 k) (ns2 k 512) (ns2 k 515) := by
  refine ⟨ns2 k 513,ns2 k 514,ns2_safe k 512,ns2_safe k 513,ns2_safe k 514,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem h_to_d_515 (k : Nat) : FromHRows (Safe:=Safe2 k) (ns2 k 515) (ns2 k 518) := by
  refine ⟨ns2 k 516,ns2 k 517,ns2_safe k 515,ns2_safe k 516,ns2_safe k 517,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem d_to_h_546 (k : Nat) : DToHRows (Safe:=Safe2 k) (ns2 k 546) (ns2 k 550) := by
  refine ⟨ns2 k 547,ns2 k 548,ns2 k 549,ns2_safe k 546,ns2_safe k 547,ns2_safe k 548,ns2_safe k 549,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem h_to_s_550 (k : Nat) : HToSRows (Safe:=Safe2 k) (ns2 k 550) (ns2 k 553) := by
  refine ⟨ns2 k 551,ns2 k 552,ns2_safe k 550,ns2_safe k 551,ns2_safe k 552,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem s_to_h_558 (k : Nat) : SToHRows (Safe:=Safe2 k) (ns2 k 558) (ns2 k 561) := by
  refine ⟨ns2 k 559,ns2 k 560,ns2_safe k 558,ns2_safe k 559,ns2_safe k 560,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem h_to_d_561 (k : Nat) : FromHRows (Safe:=Safe2 k) (ns2 k 561) (ns2 k 465) := by
  refine ⟨ns2 k 562,ns2 k 563,ns2_safe k 561,ns2_safe k 562,ns2_safe k 563,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem s_to_h_565 (k : Nat) : SToHRows (Safe:=Safe2 k) (ns2 k 565) (ns2 k 568) := by
  refine ⟨ns2 k 566,ns2 k 567,ns2_safe k 565,ns2_safe k 566,ns2_safe k 567,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem h_to_d_568 (k : Nat) : FromHRows (Safe:=Safe2 k) (ns2 k 568) (ns2 k 518) := by
  refine ⟨ns2 k 569,ns2 k 570,ns2_safe k 568,ns2_safe k 569,ns2_safe k 570,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem d_to_h_599 (k : Nat) : DToHRows (Safe:=Safe2 k) (ns2 k 599) (ns2 k 603) := by
  refine ⟨ns2 k 600,ns2 k 601,ns2 k 602,ns2_safe k 599,ns2_safe k 600,ns2_safe k 601,ns2_safe k 602,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem h_to_s_603 (k : Nat) : HToSRows (Safe:=Safe2 k) (ns2 k 603) (ns2 k 606) := by
  refine ⟨ns2 k 604,ns2 k 605,ns2_safe k 603,ns2_safe k 604,ns2_safe k 605,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem s_to_h_609 (k : Nat) : SToHRows (Safe:=Safe2 k) (ns2 k 609) (ns2 k 612) := by
  refine ⟨ns2 k 610,ns2 k 611,ns2_safe k 609,ns2_safe k 610,ns2_safe k 611,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem h_to_d_612 (k : Nat) : FromHRows (Safe:=Safe2 k) (ns2 k 612) (ns2 k 465) := by
  refine ⟨ns2 k 613,ns2 k 614,ns2_safe k 612,ns2_safe k 613,ns2_safe k 614,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem s_to_h_616 (k : Nat) : SToHRows (Safe:=Safe2 k) (ns2 k 616) (ns2 k 619) := by
  refine ⟨ns2 k 617,ns2 k 618,ns2_safe k 616,ns2_safe k 617,ns2_safe k 618,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem h_to_d_619 (k : Nat) : FromHRows (Safe:=Safe2 k) (ns2 k 619) (ns2 k 518) := by
  refine ⟨ns2 k 620,ns2 k 621,ns2_safe k 619,ns2_safe k 620,ns2_safe k 621,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem d_to_h_1118 (k : Nat) : DToHRows (Safe:=Safe2 k) (ns2 k 1118) (ns2 k 1122) := by
  refine ⟨ns2 k 1119,ns2 k 1120,ns2 k 1121,ns2_safe k 1118,ns2_safe k 1119,ns2_safe k 1120,ns2_safe k 1121,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem h_to_s_1122 (k : Nat) : HToSRows (Safe:=Safe2 k) (ns2 k 1122) (ns2 k 1125) := by
  refine ⟨ns2 k 1123,ns2 k 1124,ns2_safe k 1122,ns2_safe k 1123,ns2_safe k 1124,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem s_to_h_1130 (k : Nat) : SToHRows (Safe:=Safe2 k) (ns2 k 1130) (ns2 k 1133) := by
  refine ⟨ns2 k 1131,ns2 k 1132,ns2_safe k 1130,ns2_safe k 1131,ns2_safe k 1132,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem h_to_d_1133 (k : Nat) : FromHRows (Safe:=Safe2 k) (ns2 k 1133) (ns2 k 850) := by
  refine ⟨ns2 k 1134,ns2 k 1135,ns2_safe k 1133,ns2_safe k 1134,ns2_safe k 1135,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
end NormalFinalClosure
