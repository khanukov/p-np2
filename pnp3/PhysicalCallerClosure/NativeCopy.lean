import PhysicalCallerClosure.CopyRows0
import PhysicalCallerClosure.CopyRows1
import PhysicalCallerClosure.CopyRows2
import PhysicalCallerClosure.Reset
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
private def checkedSupport (owner : Name) (leaf kind : String) : TacticM Unit := do
  let e←getEnv
  let n:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure")
  let some ci:=e.find? n | throwError "Missing exact support constant {n}"
  let actual:=match ci with | .defnInfo _=>"definition" | .thmInfo _=>"theorem" | .inductInfo _=>"inductive" | .ctorInfo _=>"constructor" | _=>"other"
  unless actual==kind do throwError "Wrong support kind {n}: {actual}, expected {kind}"
  let some i:=e.getModuleIdxFor? n | throwError "Missing support owner"
  unless i.toNat < e.header.moduleNames.size do throwError "Owner index outside header"
  unless e.header.moduleNames[i]! == owner do throwError "Wrong support owner"
  logInfo m!"reset-proof-support|{owner}|{actual}|{n}|{ci.type}"
  closeMainGoal `checkedSupport (mkConst n (ci.levelParams.map Level.param))
run_cmd do
  let e←getEnv
  for leaf in ["Node","Path","Grid","embed","ns","NativeSafe","Unary"] do
    let n:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.Engine 0) "PhysicalCallerClosure")
    let some ci:=e.find? n | throwError "Missing exact Engine support {n}"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat < e.header.moduleNames.size do throwError "Owner index outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.Engine do throwError "Wrong Engine owner"
    logInfo m!"reset-proof-open|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private abbrev pin_Node : UniformTM → Type := by run_tac checkedSupport `PhysicalCallerClosure.Engine "Node" "inductive"
private abbrev pin_Path : (M : UniformTM) → (Fin M.stateCount → Prop) → Nat → Nat → Node M → Node M → Prop := by
  run_tac checkedSupport `PhysicalCallerClosure.Engine "Path" "inductive"
private abbrev pin_Grid : (Nat → Nat) → (Nat → Option Bool) → Prop := by run_tac checkedSupport `PhysicalCallerClosure.Engine "Grid" "inductive"
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac checkedSupport `PhysicalCallerClosure.Engine "Node.mk" "constructor"
private abbrev gridMk : {D : Nat → Nat} → {T : Nat → Option Bool} →
    (∀ j,j  <  13 → D j  <  D (j+1)) →
    (∀ a b,a ≤ b → b ≤ 13 → D a ≤ D b) →
    (∀ j,j ≤ 13 → T (D j)=none) →
    (∀ j i,j  <  13 → D j  <  i → i  <  D (j+1) → ∃ b,T i=some b) → Grid D T := by
  run_tac checkedSupport `PhysicalCallerClosure.Engine "Grid.mk" "constructor"
private abbrev gridRise : {D : Nat → Nat} → {T : Nat → Option Bool} → Grid D T →
    ∀ j,j < 13 → D j < D (j+1) := by
  run_tac checkedSupport `PhysicalCallerClosure.Engine "Grid.rise" "theorem"
private abbrev gridMono : {D : Nat → Nat} → {T : Nat → Option Bool} → Grid D T →
    ∀ a b,a ≤ b → b ≤ 13 → D a ≤ D b := by
  run_tac checkedSupport `PhysicalCallerClosure.Engine "Grid.mono" "theorem"
run_cmd do
  let e←getEnv
  for (owner,leaves) in [(`PhysicalCallerClosure.UnaryCopy,["field","field_grid","field_other","field_unary","field_self"]),
      (`PhysicalCallerClosure.CopyKernel,["CopyRows","copy_run"]),(`PhysicalCallerClosure.Reset,["reset_clear_path"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing typed copy dependency {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong owner"
      logInfo m!"native-copy-open|{owner}|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private def middle (k : Nat) (a : Fin 3) : Fin (callerMachine k).stateCount :=
  ns k (#[39,508,985][a.val]!)
private def home (k : Nat) (a : Fin 3) : Fin (callerMachine k).stateCount :=
  ns k (#[30,499,976][a.val]!)
private abbrev code_0_3 : ∀ k : Nat,
    CopyRows (M:=callerMachine k) (Safe:=NativeSafe k) 3 4 (ns k 132) (ns k 39) := by
  run_tac checkedSupport `PhysicalCallerClosure.CopyRows0 "copy_3_4_0" "definition"
private abbrev code_0_0 : ∀ k : Nat,
    CopyRows (M:=callerMachine k) (Safe:=NativeSafe k) 0 6 (ns k 39) (ns k 30) := by
  run_tac checkedSupport `PhysicalCallerClosure.CopyRows0 "copy_0_6_0" "definition"
private abbrev code_1_3 : ∀ k : Nat,
    CopyRows (M:=callerMachine k) (Safe:=NativeSafe k) 3 4 (ns k 601) (ns k 508) := by
  run_tac checkedSupport `PhysicalCallerClosure.CopyRows1 "copy_3_4_1" "definition"
private abbrev code_1_0 : ∀ k : Nat,
    CopyRows (M:=callerMachine k) (Safe:=NativeSafe k) 0 6 (ns k 508) (ns k 499) := by
  run_tac checkedSupport `PhysicalCallerClosure.CopyRows1 "copy_0_6_1" "definition"
private abbrev code_2_3 : ∀ k : Nat,
    CopyRows (M:=callerMachine k) (Safe:=NativeSafe k) 3 4 (ns k 1078) (ns k 985) := by
  run_tac checkedSupport `PhysicalCallerClosure.CopyRows2 "copy_3_4_2" "definition"
private abbrev code_2_0 : ∀ k : Nat,
    CopyRows (M:=callerMachine k) (Safe:=NativeSafe k) 0 6 (ns k 985) (ns k 976) := by
  run_tac checkedSupport `PhysicalCallerClosure.CopyRows2 "copy_0_6_2" "definition"
private def wcode (k : Nat) (a : Fin 3) :
    CopyRows (M:=callerMachine k) (Safe:=NativeSafe k) 3 4 (resetCopyEntry k a) (middle k a) := by
  refine Fin.cases ?_ (fun b=>Fin.cases ?_ (fun c=>Fin.cases ?_ (fun d=>Fin.elim0 d) c) b) a
  · exact code_0_3 k
  · exact code_1_3 k
  · exact code_2_3 k
private def gcode (k : Nat) (a : Fin 3) :
    CopyRows (M:=callerMachine k) (Safe:=NativeSafe k) 0 6 (middle k a) (home k a) := by
  refine Fin.cases ?_ (fun b=>Fin.cases ?_ (fun c=>Fin.cases ?_ (fun d=>Fin.elim0 d) c) b) a
  · exact code_0_0 k
  · exact code_1_0 k
  · exact code_2_0 k
private theorem pair_path (k : Nat) (a : Fin 3) (D : Nat → Nat) (T : Nat → Option Bool)
    (r g W P : Nat) (grid:Grid D T) (room:D 13 ≤ P)
    (width:∀ j,j=0 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 → D (j+1)=D j+r+1)
    (ug:Unary D T 0 g) (uw:Unary D T 3 W) (u4:Unary D T 4 0)
    (u5:Unary D T 5 0) (u6:Unary D T 6 0) (hg:g ≤ r) (hw:W ≤ r) :
    ∃ t,t ≤ 512*(r+1)*(P+1) ∧ Path (callerMachine k) (NativeSafe k) P t
      (node (resetCopyEntry k a) (D 0) T)
      (node (home k a) (D 0) (field (field T D 4 W) D 6 g)) := by
  obtain ⟨tw,pw,first⟩:=copy_run grid (by decide : 3 < 13) (by decide : 4 < 13)
    (by decide) (by decide) (by decide) room (by intro j hj;exact width j (by omega)) uw u4 u5 hw (wcode k a)
  have grid1:=field_grid grid 4 W (by decide)
  obtain ⟨tg,pg,second⟩:=copy_run grid1 (by decide : 0 < 13) (by decide : 6 < 13)
    (by decide) (by decide) (by decide) room (by intro j hj;exact width j (by omega))
    (field_other grid (by decide : 4 < 13) (by decide : 0 < 13) (by decide) ug)
    (field_other grid (by decide : 4 < 13) (by decide : 6 < 13) (by decide) u6)
    (field_other grid (by decide : 4 < 13) (by decide : 5 < 13) (by decide) u5) hg (gcode k a)
  refine ⟨tw+tg,?_,first.append second⟩
  have wle:256*(W+1)*(P+1) ≤ 256*(r+1)*(P+1):=Nat.mul_le_mul_right (P+1) (Nat.mul_le_mul_left 256 (by omega))
  have gle:256*(g+1)*(P+1) ≤ 256*(r+1)*(P+1):=Nat.mul_le_mul_right (P+1) (Nat.mul_le_mul_left 256 (by omega))
  have eq:512*(r+1)*(P+1)=256*(r+1)*(P+1)+256*(r+1)*(P+1):=by ring
  omega
end PhysicalCallerClosure
