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
private theorem s_to_h_3133 (k : Nat) : SToHRows (Safe:=Safe2 k) (ns2 k 3133) (ns2 k 3136) := by
  refine ⟨ns2 k 3134,ns2 k 3135,ns2_safe k 3133,ns2_safe k 3134,ns2_safe k 3135,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem h_to_d_3136 (k : Nat) : FromHRows (Safe:=Safe2 k) (ns2 k 3136) (ns2 k 3139) := by
  refine ⟨ns2 k 3137,ns2 k 3138,ns2_safe k 3136,ns2_safe k 3137,ns2_safe k 3138,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem d_to_h_3303 (k : Nat) : DToHRows (Safe:=Safe2 k) (ns2 k 3303) (ns2 k 3307) := by
  refine ⟨ns2 k 3304,ns2 k 3305,ns2 k 3306,ns2_safe k 3303,ns2_safe k 3304,ns2_safe k 3305,ns2_safe k 3306,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem d_to_h_3308 (k : Nat) : DToHRows (Safe:=Safe2 k) (ns2 k 3308) (ns2 k 3312) := by
  refine ⟨ns2 k 3309,ns2 k 3310,ns2 k 3311,ns2_safe k 3308,ns2_safe k 3309,ns2_safe k 3310,ns2_safe k 3311,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem h_to_s_3312 (k : Nat) : HToSRows (Safe:=Safe2 k) (ns2 k 3312) (ns2 k 3315) := by
  refine ⟨ns2 k 3313,ns2 k 3314,ns2_safe k 3312,ns2_safe k 3313,ns2_safe k 3314,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem s_to_h_3319 (k : Nat) : SToHRows (Safe:=Safe2 k) (ns2 k 3319) (ns2 k 3322) := by
  refine ⟨ns2 k 3320,ns2 k 3321,ns2_safe k 3319,ns2_safe k 3320,ns2_safe k 3321,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem h_to_d_3322 (k : Nat) : FromHRows (Safe:=Safe2 k) (ns2 k 3322) (ns2 k 3325) := by
  refine ⟨ns2 k 3323,ns2 k 3324,ns2_safe k 3322,ns2_safe k 3323,ns2_safe k 3324,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem d_to_h_3489 (k : Nat) : DToHRows (Safe:=Safe2 k) (ns2 k 3489) (ns2 k 3493) := by
  refine ⟨ns2 k 3490,ns2 k 3491,ns2 k 3492,ns2_safe k 3489,ns2_safe k 3490,ns2_safe k 3491,ns2_safe k 3492,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem d_to_h_3659 (k : Nat) : DToHRows (Safe:=Safe2 k) (ns2 k 3659) (ns2 k 3663) := by
  refine ⟨ns2 k 3660,ns2 k 3661,ns2 k 3662,ns2_safe k 3659,ns2_safe k 3660,ns2_safe k 3661,ns2_safe k 3662,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem d_to_h_3664 (k : Nat) : DToHRows (Safe:=Safe2 k) (ns2 k 3664) (ns2 k 3668) := by
  refine ⟨ns2 k 3665,ns2 k 3666,ns2 k 3667,ns2_safe k 3664,ns2_safe k 3665,ns2_safe k 3666,ns2_safe k 3667,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem h_to_s_3668 (k : Nat) : HToSRows (Safe:=Safe2 k) (ns2 k 3668) (ns2 k 3671) := by
  refine ⟨ns2 k 3669,ns2 k 3670,ns2_safe k 3668,ns2_safe k 3669,ns2_safe k 3670,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem s_to_h_3675 (k : Nat) : SToHRows (Safe:=Safe2 k) (ns2 k 3675) (ns2 k 3678) := by
  refine ⟨ns2 k 3676,ns2 k 3677,ns2_safe k 3675,ns2_safe k 3676,ns2_safe k 3677,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem h_to_d_3678 (k : Nat) : FromHRows (Safe:=Safe2 k) (ns2 k 3678) (ns2 k 3681) := by
  refine ⟨ns2 k 3679,ns2 k 3680,ns2_safe k 3678,ns2_safe k 3679,ns2_safe k 3680,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem d_to_h_3845 (k : Nat) : DToHRows (Safe:=Safe2 k) (ns2 k 3845) (ns2 k 3849) := by
  refine ⟨ns2 k 3846,ns2 k 3847,ns2 k 3848,ns2_safe k 3845,ns2_safe k 3846,ns2_safe k 3847,ns2_safe k 3848,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem d_to_h_3850 (k : Nat) : DToHRows (Safe:=Safe2 k) (ns2 k 3850) (ns2 k 3854) := by
  refine ⟨ns2 k 3851,ns2 k 3852,ns2 k 3853,ns2_safe k 3850,ns2_safe k 3851,ns2_safe k 3852,ns2_safe k 3853,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem h_to_s_3854 (k : Nat) : HToSRows (Safe:=Safe2 k) (ns2 k 3854) (ns2 k 3857) := by
  refine ⟨ns2 k 3855,ns2 k 3856,ns2_safe k 3854,ns2_safe k 3855,ns2_safe k 3856,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem s_to_h_3861 (k : Nat) : SToHRows (Safe:=Safe2 k) (ns2 k 3861) (ns2 k 3864) := by
  refine ⟨ns2 k 3862,ns2 k 3863,ns2_safe k 3861,ns2_safe k 3862,ns2_safe k 3863,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem h_to_d_3864 (k : Nat) : FromHRows (Safe:=Safe2 k) (ns2 k 3864) (ns2 k 3867) := by
  refine ⟨ns2 k 3865,ns2 k 3866,ns2_safe k 3864,ns2_safe k 3865,ns2_safe k 3866,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem d_to_h_4031 (k : Nat) : DToHRows (Safe:=Safe2 k) (ns2 k 4031) (ns2 k 4035) := by
  refine ⟨ns2 k 4032,ns2 k 4033,ns2 k 4034,ns2_safe k 4031,ns2_safe k 4032,ns2_safe k 4033,ns2_safe k 4034,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem d_to_h_4201 (k : Nat) : DToHRows (Safe:=Safe2 k) (ns2 k 4201) (ns2 k 4205) := by
  refine ⟨ns2 k 4202,ns2 k 4203,ns2 k 4204,ns2_safe k 4201,ns2_safe k 4202,ns2_safe k 4203,ns2_safe k 4204,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
end NormalFinalClosure
