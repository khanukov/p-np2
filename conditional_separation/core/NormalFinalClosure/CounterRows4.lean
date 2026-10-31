import NormalFinalClosure.CounterSupport2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
private def selectCounter (owner : Name) (leaf kind : String) : TacticM Unit := do
  let n:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num (Name.append `_private owner) 0) "NormalFinalClosure")
  let e←getEnv
  let some ci:=e.find? n | throwError "Missing exact split counter API"
  let actual:=match ci with|.defnInfo _=>"definition"|.thmInfo _=>"theorem"|_=>"other"
  unless actual==kind do throwError "Wrong split counter kind"
  let some i:=e.getModuleIdxFor? n | throwError "Missing split counter owner"
  unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong split counter owner"
  logInfo m!"split-native-certificate|{n}|{kind}|{ci.type}"
  closeMainGoal `selectCounter (mkConst n (ci.levelParams.map Level.param))
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["ns2","Safe2"]),
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["ClearRows","DecRows","IncRows"])] do
    for leaf in leaves do
      let n:=Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns) leaf
      let some ci:=e.find? n | throwError "Missing actual counter type"
      let some i:=e.getModuleIdxFor? n | throwError "Missing actual counter type owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong actual counter type owner"
      logInfo m!"split-native-type|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private abbrev nativeRow : TacticM Unit := by
  run_tac selectCounter `NormalFinalClosure.CounterSupport2 "nativeRow" "definition"
private abbrev nativeRoute : Nat → TacticM Unit := by
  run_tac selectCounter `NormalFinalClosure.CounterSupport2 "nativeRoute" "definition"
private theorem nsSafe : ∀ k i,Safe2 k (ns2 k i) := by
  run_tac selectCounter `NormalFinalClosure.CounterSupport2 "nsSafe" "theorem"

private theorem clearCode_81 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 5 false (ns2 k 3345) (ns2 k 3369) := by
  refine ⟨ns2 k 3355,ns2 k 3356,ns2 k 3357,nsSafe k 3355,nsSafe k 3356,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem clearCode_82 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 6 false (ns2 k 3369) (ns2 k 3397) := by
  refine ⟨ns2 k 3381,ns2 k 3382,ns2 k 3383,nsSafe k 3381,nsSafe k 3382,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem clearCode_83 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 11 false (ns2 k 3397) (ns2 k 3445) := by
  refine ⟨ns2 k 3419,ns2 k 3420,ns2 k 3421,nsSafe k 3419,nsSafe k 3420,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem clearCode_84 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 10 true (ns2 k 3445) (ns2 k 3489) := by
  refine ⟨ns2 k 3465,ns2 k 3466,ns2 k 3467,nsSafe k 3465,nsSafe k 3466,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem clearCode_85 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 4 false (ns2 k 3495) (ns2 k 3515) := by
  refine ⟨ns2 k 3503,ns2 k 3504,ns2 k 3505,nsSafe k 3503,nsSafe k 3504,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem clearCode_86 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 5 false (ns2 k 3515) (ns2 k 3539) := by
  refine ⟨ns2 k 3525,ns2 k 3526,ns2 k 3527,nsSafe k 3525,nsSafe k 3526,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem clearCode_87 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 6 false (ns2 k 3539) (ns2 k 3567) := by
  refine ⟨ns2 k 3551,ns2 k 3552,ns2 k 3553,nsSafe k 3551,nsSafe k 3552,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem clearCode_88 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 11 false (ns2 k 3567) (ns2 k 3615) := by
  refine ⟨ns2 k 3589,ns2 k 3590,ns2 k 3591,nsSafe k 3589,nsSafe k 3590,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem clearCode_89 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 10 true (ns2 k 3615) (ns2 k 3659) := by
  refine ⟨ns2 k 3635,ns2 k 3636,ns2 k 3637,nsSafe k 3635,nsSafe k 3636,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem clearCode_90 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 4 false (ns2 k 3681) (ns2 k 3701) := by
  refine ⟨ns2 k 3689,ns2 k 3690,ns2 k 3691,nsSafe k 3689,nsSafe k 3690,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem clearCode_91 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 5 false (ns2 k 3701) (ns2 k 3725) := by
  refine ⟨ns2 k 3711,ns2 k 3712,ns2 k 3713,nsSafe k 3711,nsSafe k 3712,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem clearCode_92 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 6 false (ns2 k 3725) (ns2 k 3753) := by
  refine ⟨ns2 k 3737,ns2 k 3738,ns2 k 3739,nsSafe k 3737,nsSafe k 3738,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem clearCode_93 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 11 false (ns2 k 3753) (ns2 k 3801) := by
  refine ⟨ns2 k 3775,ns2 k 3776,ns2 k 3777,nsSafe k 3775,nsSafe k 3776,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem clearCode_94 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 10 true (ns2 k 3801) (ns2 k 3845) := by
  refine ⟨ns2 k 3821,ns2 k 3822,ns2 k 3823,nsSafe k 3821,nsSafe k 3822,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem clearCode_95 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 4 false (ns2 k 3867) (ns2 k 3887) := by
  refine ⟨ns2 k 3875,ns2 k 3876,ns2 k 3877,nsSafe k 3875,nsSafe k 3876,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem clearCode_96 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 5 false (ns2 k 3887) (ns2 k 3911) := by
  refine ⟨ns2 k 3897,ns2 k 3898,ns2 k 3899,nsSafe k 3897,nsSafe k 3898,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem clearCode_97 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 6 false (ns2 k 3911) (ns2 k 3939) := by
  refine ⟨ns2 k 3923,ns2 k 3924,ns2 k 3925,nsSafe k 3923,nsSafe k 3924,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem clearCode_98 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 11 false (ns2 k 3939) (ns2 k 3987) := by
  refine ⟨ns2 k 3961,ns2 k 3962,ns2 k 3963,nsSafe k 3961,nsSafe k 3962,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem clearCode_99 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 10 true (ns2 k 3987) (ns2 k 4031) := by
  refine ⟨ns2 k 4007,ns2 k 4008,ns2 k 4009,nsSafe k 4007,nsSafe k 4008,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem clearCode_100 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 4 false (ns2 k 4037) (ns2 k 4057) := by
  refine ⟨ns2 k 4045,ns2 k 4046,ns2 k 4047,nsSafe k 4045,nsSafe k 4046,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem clearCode_101 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 5 false (ns2 k 4057) (ns2 k 4081) := by
  refine ⟨ns2 k 4067,ns2 k 4068,ns2 k 4069,nsSafe k 4067,nsSafe k 4068,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem clearCode_102 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 6 false (ns2 k 4081) (ns2 k 4109) := by
  refine ⟨ns2 k 4093,ns2 k 4094,ns2 k 4095,nsSafe k 4093,nsSafe k 4094,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem clearCode_103 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 11 false (ns2 k 4109) (ns2 k 4157) := by
  refine ⟨ns2 k 4131,ns2 k 4132,ns2 k 4133,nsSafe k 4131,nsSafe k 4132,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
private theorem clearCode_104 (k : Nat) : ClearRows (M:=machine2 k) (Safe:=Safe2 k) 10 true (ns2 k 4157) (ns2 k 4201) := by
  refine ⟨ns2 k 4177,ns2 k 4178,ns2 k 4179,nsSafe k 4177,nsSafe k 4178,?_,?_,?_,?_,?_⟩
  · run_tac nativeRoute 14
  · run_tac nativeRoute 14
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
end NormalFinalClosure
