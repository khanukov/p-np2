import NormalFinalClosure.Initialization2
import NormalFinalClosure.RepCounters2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.UnaryCopy,`PhysicalCallerClosure,["field","field_self"]),
    (`NormalFinalClosure.Frame2,`NormalFinalClosure,["GuardFrame","D","repImage","GuardFrame.freeStack"]),
    (`NormalFinalClosure.Copy2,`NormalFinalClosure,["three"]),
    (`NormalFinalClosure.Halving2,`NormalFinalClosure,["I"]),
    (`NormalFinalClosure.Initialization2,`NormalFinalClosure,["reset","reset_zero4","reset_zero5"]),
    (`NormalFinalClosure.RepCounters2,`NormalFinalClosure,["rep_disjoint"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing exact initialized-representation API"
      let some i:=e.getModuleIdxFor? name | throwError "Missing initialized image owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong initialized image owner"
      logInfo m!"initialized-source-representation-interface|{name}|{ci.type}"
      let aliasName:=(leaf.splitOn ".").getLast!
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
private theorem initialized_image {S z n F r W source T} (fr:GuardFrame S z n F r W source T) (ell : Nat) :
    I (reset T (D F r n)) (D F r n) 0 0 ell=repImage T F r n S S 0 0 ell 0 [] := by
  funext i
  have nohole:¬(i=S ∧ S < S):=by omega
  by_cases f4:D F r n 4 < i ∧ i < D F r n 5
  · simp only [I,three,reset,field,repImage,if_neg nohole,if_pos f4,
      if_neg (rep_disjoint (by decide : 4 ≤ 12) (by decide : 5 ≤ 12) (by decide) f4),
      if_neg (rep_disjoint (by decide : 4 ≤ 12) (by decide : 6 ≤ 12) (by decide) f4),
      if_neg (rep_disjoint (by decide : 4 ≤ 12) (by decide : 11 ≤ 12) (by decide) f4)]
  · by_cases f5:D F r n 5 < i ∧ i < D F r n 6
    · simp only [I,three,reset,field,repImage,if_neg nohole,if_neg f4,if_pos f5,
        if_neg (rep_disjoint (by decide : 5 ≤ 12) (by decide : 6 ≤ 12) (by decide) f5),
        if_neg (rep_disjoint (by decide : 5 ≤ 12) (by decide : 11 ≤ 12) (by decide) f5)]
    · by_cases f6:D F r n 6 < i ∧ i < D F r n 7
      · simp only [I,three,reset,field,repImage,if_neg nohole,if_neg f4,if_neg f5,if_pos f6,
          if_neg (rep_disjoint (by decide : 6 ≤ 12) (by decide : 11 ≤ 12) (by decide) f6)]
      · by_cases f11:D F r n 11 < i ∧ i < D F r n 12
        · simp only [I,three,reset,field,repImage,if_neg nohole,if_neg f4,if_neg f5,if_neg f6,if_pos f11]
        · simp only [I,three,reset,field,repImage,if_neg nohole,if_neg f4,if_neg f5,if_neg f6,if_neg f11]
          split
          · rename_i h
            rw [freeStack fr i h.1 h.2]
            simp only [List.length_nil,Nat.not_lt_zero,if_false]
          · rfl
end NormalFinalClosure
