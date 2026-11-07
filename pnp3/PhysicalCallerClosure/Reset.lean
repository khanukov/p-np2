import PhysicalCallerClosure.ResetRows0
import PhysicalCallerClosure.ResetRows1
import PhysicalCallerClosure.ResetRows2
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
  for leaf in ["Node","Path","Grid","paint","embed","ns","NativeSafe","ClearRows","FromHRows","from_H","clear_run"] do
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
private abbrev pin_paint : (Nat → Option Bool) → Nat → Nat → Bool → Nat → Option Bool := by
  run_tac checkedSupport `PhysicalCallerClosure.Engine "paint" "definition"
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
private theorem pin_from_H : ∀ {M : UniformTM} {Safe : Fin M.stateCount → Prop}
    {H Q F P : Nat} {T : Nat → Option Bool} {entry out : Fin M.stateCount},
    0 < Q → H+Q < F → F+1 ≤ P → T F=some false → T H=none →
    (∀ i,H < i → i ≤ H+Q → T i=some true) →
    (∀ i,H+Q < i → i < F → T i=none) → FromHRows (Safe:=Safe) entry out →
    Path M Safe P (F+1-H) (node entry H T) (node out (F+1) T) := by
  run_tac checkedSupport `PhysicalCallerClosure.Engine "from_H" "theorem"
private theorem pin_clear_run : ∀ {M : UniformTM} {Safe : Fin M.stateCount → Prop}
    {D : Nat → Nat} {T : Nat → Option Bool} {P j : Nat} {b : Bool} {start out : Fin M.stateCount},
    Grid D T → j < 13 → D 13 ≤ P → ClearRows (Safe:=Safe) j b start out →
    Path M Safe P (2*(D (j+1)-D 0+j)+2) (node start (D 0) T)
      (node out (D 0) (paint T (D j+1) (D (j+1)-D j-1) b)) := by
  run_tac checkedSupport `PhysicalCallerClosure.Engine "clear_run" "theorem"
private theorem code_0 : ∀ k : Nat,
    ∃ s0 s1 s2 s3 : Fin (callerMachine k).stateCount,
      FromHRows (Safe:=NativeSafe k) (resetEntry k ⟨0,by decide⟩) s0 ∧
      ClearRows (Safe:=NativeSafe k) 5 false s0 s1 ∧
      ClearRows (Safe:=NativeSafe k) 4 false s1 s2 ∧
      ClearRows (Safe:=NativeSafe k) 6 false s2 s3 ∧
      ClearRows (Safe:=NativeSafe k) 11 false s3 (resetCopyEntry k ⟨0,by decide⟩) := by
  run_tac checkedSupport `PhysicalCallerClosure.ResetRows0 "code_all_0" "theorem"
private theorem code_1 : ∀ k : Nat,
    ∃ s0 s1 s2 s3 : Fin (callerMachine k).stateCount,
      FromHRows (Safe:=NativeSafe k) (resetEntry k ⟨1,by decide⟩) s0 ∧
      ClearRows (Safe:=NativeSafe k) 5 false s0 s1 ∧
      ClearRows (Safe:=NativeSafe k) 4 false s1 s2 ∧
      ClearRows (Safe:=NativeSafe k) 6 false s2 s3 ∧
      ClearRows (Safe:=NativeSafe k) 11 false s3 (resetCopyEntry k ⟨1,by decide⟩) := by
  run_tac checkedSupport `PhysicalCallerClosure.ResetRows1 "code_all_1" "theorem"
private theorem code_2 : ∀ k : Nat,
    ∃ s0 s1 s2 s3 : Fin (callerMachine k).stateCount,
      FromHRows (Safe:=NativeSafe k) (resetEntry k ⟨2,by decide⟩) s0 ∧
      ClearRows (Safe:=NativeSafe k) 5 false s0 s1 ∧
      ClearRows (Safe:=NativeSafe k) 4 false s1 s2 ∧
      ClearRows (Safe:=NativeSafe k) 6 false s2 s3 ∧
      ClearRows (Safe:=NativeSafe k) 11 false s3 (resetCopyEntry k ⟨2,by decide⟩) := by
  run_tac checkedSupport `PhysicalCallerClosure.ResetRows2 "code_all_2" "theorem"
private theorem reset_codes (k : Nat) (a : Fin 3) :
    ∃ s0 s1 s2 s3 : Fin (callerMachine k).stateCount,
      FromHRows (Safe:=NativeSafe k) (resetEntry k a) s0 ∧
      ClearRows (Safe:=NativeSafe k) 5 false s0 s1 ∧
      ClearRows (Safe:=NativeSafe k) 4 false s1 s2 ∧
      ClearRows (Safe:=NativeSafe k) 6 false s2 s3 ∧
      ClearRows (Safe:=NativeSafe k) 11 false s3 (resetCopyEntry k a) := by
  fin_cases a
  · exact code_0 k
  · exact code_1 k
  · exact code_2 k
private theorem field_clear (T : Nat → Option Bool) (D : Nat → Nat) (j : Nat)
    (rise:D j < D (j+1)) :
    paint T (D j+1) (D (j+1)-D j-1) false=
      fun i=>if D j < i ∧ i < D (j+1) then some false else T i := by
  funext i
  have h:(D j+1 ≤ i ∧ i < D j+1+(D (j+1)-D j-1)) ↔ (D j < i ∧ i < D (j+1)) := by omega
  simp only [paint,h]
private theorem reset_price (P d0 d5 d6 d7 d12 F H : Nat)
    (fit:F+1 ≤ P) (h5:d5 ≤ P) (h6:d6 ≤ P) (h7:d7 ≤ P) (h12:d12 ≤ P) :
    F+1-H+((2*(d6-d0+5)+2)+((2*(d5-d0+4)+2)+
      ((2*(d7-d0+6)+2)+(2*(d12-d0+11)+2)))) ≤ 64*(P+1) := by omega
private theorem reset_clear_path (k : Nat) (a : Fin 3) (D : Nat → Nat) (T : Nat → Option Bool)
    (H Q F P : Nat) (grid : Grid D T) (anchor:D 0=F+1) (room:D 13 ≤ P)
    (positive:0 < Q) (arena:H+Q < F) (th:T H=none) (tf:T F=some false)
    (marks:∀ i,H < i → i ≤ H+Q → T i=some true)
    (gap:∀ i,H+Q < i → i < F → T i=none) :
    ∃ t,t ≤ 64*(P+1) ∧ Path (callerMachine k) (NativeSafe k) P t
      (node (resetEntry k a) H T) (node (resetCopyEntry k a) (D 0) (fun i=>
        if D 11 < i ∧ i < D 12 then some false
        else if D 6 < i ∧ i < D 7 then some false
        else if D 4 < i ∧ i < D 5 then some false
        else if D 5 < i ∧ i < D 6 then some false else T i)) := by
  obtain ⟨s0,s1,s2,s3,fromCode,code5,code4,code6,code11⟩:=reset_codes k a
  have d0:D 0 ≤ P:=le_trans (gridMono grid _ _ (by decide) (by decide)) room
  have first : Path (callerMachine k) (NativeSafe k) P (F+1-H)
      (node (resetEntry k a) H T) (node s0 (D 0) T) := by
    simpa only [anchor] using from_H positive arena (show F+1 ≤ P by omega) tf th marks gap fromCode
  let U1:=paint T (D 5+1) (D 6-D 5-1) false
  let U2:=paint U1 (D 4+1) (D 5-D 4-1) false
  let U3:=paint U2 (D 6+1) (D 7-D 6-1) false
  let U4:=paint U3 (D 11+1) (D 12-D 11-1) false
  have g1:Grid D U1:=grid.painted 5 (by decide) false
  have g2:Grid D U2:=g1.painted 4 (by decide) false
  have g3:Grid D U3:=g2.painted 6 (by decide) false
  have p5:=clear_run grid (by decide : 5 < 13) room code5
  have p4:=clear_run g1 (by decide : 4 < 13) room code4
  have p6:=clear_run g2 (by decide : 6 < 13) room code6
  have p11:=clear_run g3 (by decide : 11 < 13) room code11
  have whole:=first.append (p5.append (p4.append (p6.append p11)))
  have tapeEq:U4=(fun i=>
        if D 11 < i ∧ i < D 12 then some false
        else if D 6 < i ∧ i < D 7 then some false
        else if D 4 < i ∧ i < D 5 then some false
        else if D 5 < i ∧ i < D 6 then some false else T i) := by
    dsimp only [U4,U3,U2,U1]
    rw [field_clear _ D 11 (gridRise grid 11 (by decide)),field_clear _ D 6 (gridRise grid 6 (by decide)),
      field_clear _ D 4 (gridRise grid 4 (by decide)),field_clear _ D 5 (gridRise grid 5 (by decide))]
  change Path (callerMachine k) (NativeSafe k) P _ _ (node (resetCopyEntry k a) (D 0) U4) at whole
  rw [tapeEq] at whole
  refine ⟨_,?_,whole⟩
  exact reset_price P (D 0) (D 5) (D 6) (D 7) (D 12) F H (by omega)
    (le_trans (gridMono grid _ _ (by decide) (by decide)) room)
    (le_trans (gridMono grid _ _ (by decide) (by decide)) room)
    (le_trans (gridMono grid _ _ (by decide) (by decide)) room)
    (le_trans (gridMono grid _ _ (by decide) (by decide)) room)
private theorem safe_verdict (k : Nat) (q : Fin (callerMachine k).stateCount) (safe:NativeSafe k q) :
    q≠(callerMachine k).accept ∧ q≠(callerMachine k).reject ∧ q≠rowsDone k := by
  refine ⟨?_,?_,safe.2⟩
  · intro bad
    have values:=congrArg Fin.val bad
    change q.val=(BodyIngress.machine k).accept.val at values
    have bound:=(BodyIngress.machine k).accept.isLt
    have lower:=safe.1
    omega
  · intro bad
    have values:=congrArg Fin.val bad
    change q.val=(BodyIngress.machine k).reject.val at values
    have bound:=(BodyIngress.machine k).reject.isLt
    have lower:=safe.1
    omega
/-- Actual native H→clear→copy-entry segment. Metadata is a real occupied field;
this is one segment of reset, not the complete row loop. All finite tape cells are retained. -/
theorem reset_clear_prefix (k : Nat) (a : Fin 3) (N B H Q F P : Nat)
    (D : Nat → Nat) (T : Nat → Option Bool)
    (rise:∀ j,j < 13 → D j < D (j+1))
    (mono:∀ i j,i ≤ j → j ≤ 13 → D i ≤ D j)
    (blank:∀ j,j ≤ 13 → T (D j)=none)
    (cells:∀ j i,j < 13 → D j < i → i < D (j+1) → ∃ b,T i=some b)
    (anchor:D 0=F+1) (room:D 13 ≤ P) (fit:P < tapeLength N B)
    (positive:0 < Q) (arena:H+Q < F) (th:T H=none) (tf:T F=some false)
    (marks:∀ i,H < i → i ≤ H+Q → T i=some true)
    (gap:∀ i,H+Q < i → i < F → T i=none)
    (hH:H < tapeLength N B) (h0:D 0 < tapeLength N B) :
    let initial : Config (callerMachine k).stateCount N B:=⟨resetEntry k a,⟨H,hH⟩,fun i=>T i.val⟩
    ∃ t,t ≤ 64*(P+1) ∧ (callerMachine k).run t initial=
      ⟨resetCopyEntry k a,⟨D 0,h0⟩,fun i=>
        if D 11 < i.val ∧ i.val < D 12 then some false
        else if D 6 < i.val ∧ i.val < D 7 then some false
        else if D 4 < i.val ∧ i.val < D 5 then some false
        else if D 5 < i.val ∧ i.val < D 6 then some false else T i.val⟩ ∧
    (∀ u,u ≤ t → ((callerMachine k).run u initial).head.val ≤ P ∧
      ∀ i:Fin (tapeLength N B),P < i.val → ((callerMachine k).run u initial).tape i=T i.val) ∧
    (∀ u,u < t → ((callerMachine k).run u initial).state≠(callerMachine k).accept ∧
      ((callerMachine k).run u initial).state≠(callerMachine k).reject ∧
      ((callerMachine k).run u initial).state≠rowsDone k) := by
  obtain ⟨t,price,path⟩:=reset_clear_path k a D T H Q F P (gridMk rise mono blank cells)
    anchor room positive arena th tf marks gap
  refine ⟨t,price,?_,?_,?_⟩
  · simpa only [embed] using path.execute fit
  · intro u hu
    simpa only [embed] using path.footprint fit u hu
  · intro u hu
    exact safe_verdict k _ (path.safe_prefix fit u hu)
#print axioms reset_clear_prefix
end PhysicalCallerClosure
