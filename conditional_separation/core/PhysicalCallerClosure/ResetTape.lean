import PhysicalCallerClosure.NativeCopy
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
      (`PhysicalCallerClosure.NativeCopy,["home","pair_path"]),(`PhysicalCallerClosure.Reset,["reset_clear_path"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing typed copy dependency {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong owner"
      logInfo m!"native-copy-open|{owner}|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private def cleared (T : Nat → Option Bool) (D : Nat → Nat) :=
  field (field (field (field T D 5 0) D 4 0) D 6 0) D 11 0
private def resetTape (T : Nat → Option Bool) (D : Nat → Nat) (g W : Nat) :=
  field (field (cleared T D) D 4 W) D 6 g
private theorem cleared_grid {D T} (grid:Grid D T) : Grid D (cleared T D) :=
  field_grid (field_grid (field_grid (field_grid grid 5 0 (by decide)) 4 0 (by decide)) 6 0 (by decide)) 11 0 (by decide)
private theorem cleared_other {D T j v} (grid:Grid D T) (hj:j < 13)
    (n5:5≠j) (n4:4≠j) (n6:6≠j) (n11:11≠j) (u:Unary D T j v) : Unary D (cleared T D) j v := by
  have g1:=field_grid grid 5 0 (by decide)
  have g2:=field_grid g1 4 0 (by decide)
  have g3:=field_grid g2 6 0 (by decide)
  exact field_other g3 (by decide) hj n11 (field_other g2 (by decide) hj n6
    (field_other g1 (by decide) hj n4 (field_other grid (by decide) hj n5 u)))
private theorem cleared_4 {D T} (grid:Grid D T) : Unary D (cleared T D) 4 0 := by
  have g1:=field_grid grid 5 0 (by decide)
  have g2:=field_grid g1 4 0 (by decide)
  have g3:=field_grid g2 6 0 (by decide)
  exact field_other g3 (by decide) (by decide) (by decide)
    (field_other g2 (by decide) (by decide) (by decide) (field_unary _ D 4 0))
private theorem cleared_5 {D T} (grid:Grid D T) : Unary D (cleared T D) 5 0 := by
  have g1:=field_grid grid 5 0 (by decide)
  have g2:=field_grid g1 4 0 (by decide)
  have g3:=field_grid g2 6 0 (by decide)
  exact field_other g3 (by decide) (by decide) (by decide)
    (field_other g2 (by decide) (by decide) (by decide)
      (field_other g1 (by decide) (by decide) (by decide) (field_unary T D 5 0)))
private theorem cleared_6 {D T} (grid:Grid D T) : Unary D (cleared T D) 6 0 := by
  have g1:=field_grid (field_grid grid 5 0 (by decide)) 4 0 (by decide)
  exact field_other (field_grid g1 6 0 (by decide)) (by decide) (by decide) (by decide) (field_unary _ D 6 0)
private theorem field_zero (T D j) : field T D j 0=
    fun i=>if D j < i ∧ i < D (j+1) then some false else T i := by
  funext i
  by_cases h:D j < i ∧ i < D (j+1)
  · have hn:¬i-D j ≤ 0:=by omega
    simp only [field,if_pos h,decide_eq_false hn]
  · simp only [field,if_neg h]
private theorem cleared_eq (T D) : cleared T D=(fun i=>
    if D 11 < i ∧ i < D 12 then some false
    else if D 6 < i ∧ i < D 7 then some false
    else if D 4 < i ∧ i < D 5 then some false
    else if D 5 < i ∧ i < D 6 then some false else T i) := by
  dsimp only [cleared]
  rw [field_zero,field_zero,field_zero,field_zero]
private theorem field_low {D T j v i} (grid:Grid D T) (hj:j ≤ 13) (lo:i ≤ D 0) : field T D j v i=T i := by
  have order:=gridMono grid 0 j (by omega) hj
  have hn:¬(D j < i ∧ i < D (j+1)):=by omega
  simp only [field,if_neg hn]
private theorem reset_low {D T g W i} (grid:Grid D T) (lo:i ≤ D 0) : resetTape T D g W i=T i := by
  have g1:=field_grid grid 5 0 (by decide)
  have g2:=field_grid g1 4 0 (by decide)
  have g3:=field_grid g2 6 0 (by decide)
  have g4:=field_grid g3 11 0 (by decide)
  have g5:=field_grid g4 4 W (by decide)
  dsimp only [resetTape,cleared]
  rw [field_low g5 (by decide) lo,field_low g4 (by decide) lo,field_low g3 (by decide) lo,
    field_low g2 (by decide) lo,field_low g1 (by decide) lo,field_low grid (by decide) lo]
private theorem reset_path (k : Nat) (a : Fin 3) (D : Nat → Nat) (T : Nat → Option Bool)
    (H Q F P r g W : Nat) (grid:Grid D T) (anchor:D 0=F+1) (room:D 13 ≤ P)
    (width:∀ j,j=0 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 → D (j+1)=D j+r+1)
    (ug:Unary D T 0 g) (uw:Unary D T 3 W) (hg:g ≤ r) (hw:W ≤ r)
    (positive:0 < Q) (arena:H+Q < F) (th:T H=none) (tf:T F=some false)
    (marks:∀ i,H < i → i ≤ H+Q → T i=some true)
    (gap:∀ i,H+Q < i → i < F → T i=none) :
    ∃ t,t ≤ 640*(r+1)*(P+1) ∧ Path (callerMachine k) (NativeSafe k) P t
      (node (resetEntry k a) H T) (node (home k a) (D 0) (resetTape T D g W)) := by
  obtain ⟨t1,p1,first⟩:=reset_clear_path k a D T H Q F P grid anchor room positive arena th tf marks gap
  rw [←cleared_eq T D] at first
  obtain ⟨t2,p2,second⟩:=pair_path k a D (cleared T D) r g W P (cleared_grid grid) room width
    (cleared_other grid (by decide) (by decide) (by decide) (by decide) (by decide) ug)
    (cleared_other grid (by decide) (by decide) (by decide) (by decide) (by decide) uw)
    (cleared_4 grid) (cleared_5 grid) (cleared_6 grid) hg hw
  refine ⟨t1+t2,?_,first.append second⟩
  have le:64*(P+1) ≤ 64*(r+1)*(P+1):=by nlinarith
  have eq:640*(r+1)*(P+1)=64*(r+1)*(P+1)+576*(r+1)*(P+1):=by ring
  have rem:512*(r+1)*(P+1) ≤ 576*(r+1)*(P+1):=by nlinarith
  omega
end PhysicalCallerClosure
