import PhysicalCallerClosure.ResetTape
import PhysicalCallerClosure.NavigationRows
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
      (`PhysicalCallerClosure.NativeCopy,["home"]),(`PhysicalCallerClosure.ResetTape,["resetTape","reset_low","reset_path","cleared_grid","cleared","cleared_eq"]),(`PhysicalCallerClosure.Navigation,["ToHRows","to_H"]),(`PhysicalCallerClosure.SourcePrepare,["PrepareRows","prepare_source_path"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing typed copy dependency {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong owner"
      logInfo m!"native-copy-open|{owner}|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private theorem gridBlank : ∀ {D T},Grid D T → ∀ j,j ≤ 13 → T (D j)=none := by
  run_tac checkedSupport `PhysicalCallerClosure.Engine "Grid.blank" "theorem"
private def prep (k : Nat) (a : Fin 3) : Fin (callerMachine k).stateCount :=
  if a.val=0 then ns k 28 else if a.val=1 then ns k 497 else evalState k (SerializedBody.entry ⟨2,by decide⟩)
private theorem home_0 : ∀ k : Nat,
    ToHRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 30) (ns k 28) := by
  run_tac checkedSupport `PhysicalCallerClosure.NavigationRows "home_0" "theorem"
private theorem home_1 : ∀ k : Nat,
    ToHRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 499) (ns k 497) := by
  run_tac checkedSupport `PhysicalCallerClosure.NavigationRows "home_1" "theorem"
private theorem home_2 : ∀ k : Nat,
    ToHRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 976) (evalState k (SerializedBody.entry ⟨2,by decide⟩)) := by
  run_tac checkedSupport `PhysicalCallerClosure.NavigationRows "home_2" "theorem"
private theorem prep_0_false : ∀ k : Nat,
    PrepareRows (M:=callerMachine k) (Safe:=NativeSafe k) false (ns k 28)
      (evalState k (SerializedBody.entry ⟨0,by decide⟩)) := by
  run_tac checkedSupport `PhysicalCallerClosure.NavigationRows "prepare_0_false" "theorem"
private theorem prep_0_true : ∀ k : Nat,
    PrepareRows (M:=callerMachine k) (Safe:=NativeSafe k) true (ns k 28)
      (evalState k (SerializedBody.entry ⟨1,by decide⟩)) := by
  run_tac checkedSupport `PhysicalCallerClosure.NavigationRows "prepare_0_true" "theorem"
private theorem prep_1_false : ∀ k : Nat,
    PrepareRows (M:=callerMachine k) (Safe:=NativeSafe k) false (ns k 497)
      (evalState k (SerializedBody.entry ⟨0,by decide⟩)) := by
  run_tac checkedSupport `PhysicalCallerClosure.NavigationRows "prepare_1_false" "theorem"
private theorem prep_1_true : ∀ k : Nat,
    PrepareRows (M:=callerMachine k) (Safe:=NativeSafe k) true (ns k 497)
      (evalState k (SerializedBody.entry ⟨1,by decide⟩)) := by
  run_tac checkedSupport `PhysicalCallerClosure.NavigationRows "prepare_1_true" "theorem"
private theorem home_code (k : Nat) (a : Fin 3) :
    ToHRows (M:=callerMachine k) (Safe:=NativeSafe k) (home k a) (prep k a) := by
  fin_cases a
  · exact home_0 k
  · exact home_1 k
  · exact home_2 k
private theorem prep_code (k : Nat) (a : Fin 3) (ha:a.val < 2) (b : Bool) :
    PrepareRows (M:=callerMachine k) (Safe:=NativeSafe k) b (prep k a)
      (evalState k (SerializedBody.entry (if b then ⟨1,by decide⟩ else ⟨0,by decide⟩))) := by
  fin_cases a
  · cases b
    · exact prep_0_false k
    · exact prep_0_true k
  · cases b
    · exact prep_1_false k
    · exact prep_1_true k
  · change (2:Nat) < 2 at ha
    omega
private abbrev pointSet : (Nat → Option Bool) → Nat → Option Bool → Nat → Option Bool := by
  run_tac checkedSupport `PhysicalCallerClosure.Engine "put" "definition"
private theorem phase_price (r P t a b : Nat) (ht:t ≤ 640*(r+1)*(P+1))
    (ha:a ≤ P+1) (hb:b ≤ 8*(P+1)) : t+(a+b) ≤ 1024*(r+1)*(P+1) := by
  rw [Nat.mul_assoc] at ht ⊢
  have base:P+1 ≤ (r+1)*(P+1):=Nat.le_mul_of_pos_left _ (by omega)
  omega
private theorem reset_ready_path (k : Nat) (a : Fin 3) (D : Nat → Nat) (T : Nat → Option Bool)
    (S L H M Q F P r g W : Nat) (source : Fin S → Bool)
    (grid:Grid D T) (d0:D 0=F+1) (room:D 13 ≤ P)
    (width:∀ j,j=0 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 → D (j+1)=D j+r+1)
    (ug:Unary D T 0 g) (uw:Unary D T 3 W) (hg:g ≤ r) (hw:W ≤ r)
    (positive:0 < Q) (arena:H+Q < F) (th:T H=none) (tf:T F=some false)
    (marks:∀ i,H < i → i ≤ H+Q → T i=some true)
    (gap:∀ i,H+Q < i → i < F → T i=none)
    (sl:S < L) (lh:L < H) (ts:T S=none) (tl:T L=none)
    (reg:∀ i,S < i → i < L → ∃ b,T i=some b)
    (beta:∀ i,L < i → i < H → ∃ b,T i=some b)
    (src:∀ i,M ≤ i → ∀ hi:i < S,T i=some (source ⟨i,hi⟩))
    (tag:a.val=2 ↔ S ≤ M) (anchor:M < S → 0 < M ∧ T (M-1)=none) :
    ∃ t,t ≤ 1024*(r+1)*(P+1) ∧ Path (callerMachine k) (NativeSafe k) P t
      (node (resetEntry k a) H T)
      (node (evalState k (SerializedBody.entry (SerializedBody.sourceMode source M))) H
        (fun i=>if i=M ∧ i < S then none else resetTape T D g W i)) := by
  let U:=resetTape T D g W
  have gridU:Grid D U:=field_grid (field_grid (cleared_grid grid) 4 W (by decide)) 6 g (by decide)
  have low:∀ i,i ≤ F+1 → U i=T i:=by intro i hi;exact reset_low grid (by omega)
  have fd0:F+1 ≤ P:=by have h:=le_trans (gridMono grid 0 13 (by omega) le_rfl) room;omega
  obtain ⟨t1,p1,first⟩:=reset_path k a D T H Q F P r g W grid d0 room width ug uw hg hw positive arena th tf marks gap
  have second:=to_H positive arena fd0 (by rw [←d0];exact gridBlank gridU 0 (by omega))
    (by rw [low F (by omega)];exact tf) (by rw [low H (by omega)];exact th)
    (by intro i lo hi;rw [low i (by omega)];exact marks i lo hi)
    (by intro i lo hi;rw [low i (by omega)];exact gap i lo hi) (home_code k a)
  rw [←d0] at second
  have headroom:H ≤ P:=by omega
  by_cases physical:M < S
  · have ha:a.val < 2:=by
      have av:=a.isLt
      have ne:a.val≠2:=by
        intro eq
        have bad:=tag.mp eq
        omega
      omega
    have ac:=anchor physical
    have bit:U M=some (source ⟨M,physical⟩):=by rw [low M (by omega)];exact src M le_rfl physical
    have third:=prepare_source_path ac.1 physical sl lh headroom
      (by rw [low S (by omega)];exact ts) (by rw [low L (by omega)];exact tl)
      (by rw [low H (by omega)];exact th) (by rw [low (M-1) (by omega)];exact ac.2) bit
      (by intro i lo hi;rw [low i (by omega)];exact ⟨_,src i lo hi⟩)
      (by intro i lo hi;rw [low i (by omega)];exact reg i lo hi)
      (by intro i lo hi;rw [low i (by omega)];exact beta i lo hi)
      (prep_code k a ha (source ⟨M,physical⟩))
    have whole:=first.append (second.append third)
    refine ⟨t1+((F+2-H)+(2*(H-M)+8)),?_,?_⟩
    · exact phase_price r P t1 (F+2-H) (2*(H-M)+8) p1 (by omega) (by omega)
    · have mode:SerializedBody.sourceMode source M=(if source ⟨M,physical⟩ then ⟨1,by decide⟩ else ⟨0,by decide⟩):=by
        simp only [SerializedBody.sourceMode,dif_pos physical]
      have tape:(fun i=>if i=M ∧ i < S then none else resetTape T D g W i)=pointSet U M none:=by
        funext i
        change (if i=M ∧ i < S then none else U i)=(if i=M then none else U i)
        by_cases eq:i=M
        · simp only [eq,physical,and_self,ite_true]
        · simp only [if_neg eq,if_neg (show ¬(i=M ∧ i < S) by omega)]
      dsimp only [pointSet] at tape
      rw [←mode,←tape] at whole
      exact whole
  · have av:a.val=2:=tag.mpr (by omega)
    have mode:SerializedBody.sourceMode source M=⟨2,by decide⟩:=by simp only [SerializedBody.sourceMode,dif_neg physical]
    have endpoint:prep k a=evalState k (SerializedBody.entry ⟨2,by decide⟩):=by
      simp only [prep,if_neg (show a.val≠0 by omega),if_neg (show a.val≠1 by omega)]
    have whole:=first.append second
    refine ⟨t1+(F+2-H),?_,?_⟩
    · simpa only [Nat.add_zero] using phase_price r P t1 (F+2-H) 0 p1 (by omega) (by omega)
    · have tape:(fun i=>if i=M ∧ i < S then none else resetTape T D g W i)=U:=by
        funext i;rw [if_neg (by omega)]
      rw [endpoint,←mode,←tape] at whole
      exact whole
private theorem reset_normal (T D g W) : resetTape T D g W=fun i=>
    if D 6 < i ∧ i < D 7 then some (decide (i-D 6 ≤ g))
    else if D 4 < i ∧ i < D 5 then some (decide (i-D 4 ≤ W))
    else if D 11 < i ∧ i < D 12 then some false
    else if D 5 < i ∧ i < D 6 then some false else T i := by
  funext i
  dsimp only [resetTape]
  rw [cleared_eq]
  by_cases h6:D 6 < i ∧ i < D 7
  · simp only [field,if_pos h6]
  · by_cases h4:D 4 < i ∧ i < D 5
    · simp only [field,if_neg h6,if_pos h4]
    · simp only [field,if_neg h6,if_neg h4]
private theorem safe_verdict : ∀ k q,NativeSafe k q →
    q≠(callerMachine k).accept ∧ q≠(callerMachine k).reject ∧ q≠rowsDone k := by
  run_tac checkedSupport `PhysicalCallerClosure.Reset "safe_verdict" "theorem"
/-- Complete literal reset and source preparation. The two copy sources and every exterior
cell are restored; this is an executable entry to the copied BODY, not an initializer substitution. -/
theorem reset_body_entry (k : Nat) (a : Fin 3) (N B S L H M Q F P r g W : Nat)
    (D : Nat → Nat) (T : Nat → Option Bool) (source : Fin S → Bool)
    (rise:∀ j,j < 13 → D j < D (j+1))
    (mono:∀ i j,i ≤ j → j ≤ 13 → D i ≤ D j)
    (blank:∀ j,j ≤ 13 → T (D j)=none)
    (cells:∀ j i,j < 13 → D j < i → i < D (j+1) → ∃ b,T i=some b)
    (d0:D 0=F+1) (room:D 13 ≤ P) (fit:P < tapeLength N B)
    (width:∀ j,j=0 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 → D (j+1)=D j+r+1)
    (ug:∀ i,D 0 < i → i < D 1 → T i=some (decide (i-D 0 ≤ g)))
    (uw:∀ i,D 3 < i → i < D 4 → T i=some (decide (i-D 3 ≤ W)))
    (hg:g ≤ r) (hw:W ≤ r) (positive:0 < Q) (arena:H+Q < F)
    (th:T H=none) (tf:T F=some false)
    (marks:∀ i,H < i → i ≤ H+Q → T i=some true)
    (gap:∀ i,H+Q < i → i < F → T i=none)
    (sl:S < L) (lh:L < H) (ts:T S=none) (tl:T L=none)
    (reg:∀ i,S < i → i < L → ∃ b,T i=some b)
    (beta:∀ i,L < i → i < H → ∃ b,T i=some b)
    (src:∀ i,M ≤ i → ∀ hi:i < S,T i=some (source ⟨i,hi⟩))
    (tag:a.val=2 ↔ S ≤ M) (anchor:M < S → 0 < M ∧ T (M-1)=none)
    (hH:H < tapeLength N B) :
    let initial : Config (callerMachine k).stateCount N B:=⟨resetEntry k a,⟨H,hH⟩,fun i=>T i.val⟩
    ∃ t,t ≤ 1024*(r+1)*(P+1) ∧ (callerMachine k).run t initial=
      ⟨evalState k (SerializedBody.entry (SerializedBody.sourceMode source M)),⟨H,hH⟩,fun h=>
        if h.val=M ∧ h.val < S then none
        else if D 6 < h.val ∧ h.val < D 7 then some (decide (h.val-D 6 ≤ g))
        else if D 4 < h.val ∧ h.val < D 5 then some (decide (h.val-D 4 ≤ W))
        else if D 11 < h.val ∧ h.val < D 12 then some false
        else if D 5 < h.val ∧ h.val < D 6 then some false else T h.val⟩ ∧
    (∀ u,u ≤ t → ((callerMachine k).run u initial).head.val ≤ P ∧
      ∀ i:Fin (tapeLength N B),P < i.val → ((callerMachine k).run u initial).tape i=T i.val) ∧
    (∀ u,u < t → ((callerMachine k).run u initial).state≠(callerMachine k).accept ∧
      ((callerMachine k).run u initial).state≠(callerMachine k).reject ∧
      ((callerMachine k).run u initial).state≠rowsDone k) ∧
      (∀ u,u < t → (BodyIngress.machine k).stateCount+7500 ≤ ((callerMachine k).run u initial).state.val) := by
  obtain ⟨t,price,path⟩:=reset_ready_path k a D T S L H M Q F P r g W source
    (gridMk rise mono blank cells) d0 room width ug uw hg hw positive arena th tf marks gap
    sl lh ts tl reg beta src tag anchor
  refine ⟨t,price,?_,?_,?_,?_⟩
  · simpa only [embed,reset_normal] using path.execute fit
  · intro u hu;simpa only [embed] using path.footprint fit u hu
  · intro u hu;exact safe_verdict k _ (path.safe_prefix fit u hu)
  · intro u hu;exact (path.safe_prefix fit u hu).1
#print axioms reset_body_entry
end PhysicalCallerClosure
