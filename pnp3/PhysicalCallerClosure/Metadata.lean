import PhysicalCallerClosure.Navigation
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
private def support (leaf kind : String) : TacticM Unit := do
  let e←getEnv
  let n:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.Engine 0) "PhysicalCallerClosure")
  let some ci:=e.find? n | throwError "Missing Engine term {n}"
  let actual:=match ci with | .defnInfo _=>"definition" | .thmInfo _=>"theorem" | .inductInfo _=>"inductive" | .ctorInfo _=>"constructor" | _=>"other"
  unless actual==kind do throwError "Wrong Engine kind: {n}"
  let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
  unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
  unless e.header.moduleNames[i]! == `PhysicalCallerClosure.Engine do throwError "Wrong owner"
  logInfo m!"copy-support|{actual}|{n}|{ci.type}"
  closeMainGoal `support (mkConst n (ci.levelParams.map Level.param))
run_cmd do
  let e←getEnv
  for leaf in ["Node","Path","Grid","put","keep","sweepL","FromHRows","from_H","RouteR","RouteL"] do
    let n:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.Engine 0) "PhysicalCallerClosure")
    let some ci:=e.find? n | throwError "Missing Engine support {n}"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.Engine do throwError "Wrong owner"
    logInfo m!"copy-open|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac support "Node.mk" "constructor"
private abbrev gridMk : {D : Nat → Nat} → {T : Nat → Option Bool} →
    (∀ j,j < 13 → D j < D (j+1)) → (∀ a b,a ≤ b → b ≤ 13 → D a ≤ D b) →
    (∀ j,j ≤ 13 → T (D j)=none) →
    (∀ j i,j < 13 → D j < i → i < D (j+1) → ∃ b,T i=some b) → Grid D T := by
  run_tac support "Grid.mk" "constructor"
private theorem mono : ∀ {D T},Grid D T → ∀ a b,a ≤ b → b ≤ 13 → D a ≤ D b := by
  run_tac support "Grid.mono" "theorem"
private theorem rise : ∀ {D T},Grid D T → ∀ j,j < 13 → D j < D (j+1) := by
  run_tac support "Grid.rise" "theorem"
private theorem blanks : ∀ {D T},Grid D T → ∀ j,j ≤ 13 → T (D j)=none := by
  run_tac support "Grid.blank" "theorem"
private theorem occupied : ∀ {D T},Grid D T → ∀ j i,j < 13 → D j < i → i < D (j+1) → ∃ b,T i=some b := by
  run_tac support "Grid.cells" "theorem"
run_cmd do
  let e←getEnv
  for leaf in ["ToHRows","to_H"] do
    let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.Navigation 0) "PhysicalCallerClosure") leaf
    let some ci:=e.find? n | throwError "Missing exact navigation term {n}"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.Navigation do throwError "Wrong navigation owner"
    logInfo m!"metadata-support|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
variable {M : UniformTM} {Safe : Fin M.stateCount → Prop}
private structure BitsRows (bits : Fin 5 → Bool) (entry out : Fin M.stateCount) where
  states : Fin 6 → Fin M.stateCount
  back : Fin M.stateCount
  safeEntry : Safe entry
  safeStates : ∀ j,Safe (states j)
  safeBack : Safe back
  enter : M.step entry none=(states ⟨0,by decide⟩,none,.right)
  reads : ∀ j:Fin 5,M.step (states (Fin.castSucc j)) (some (bits j))=
    (states (Fin.succ j),some (bits j),.right)
  finish : M.step (states ⟨5,by decide⟩) none=(back,none,.left)
  retreat : ∀ b,M.step back (some b)=(back,some b,.left)
  exit : M.step back none=(out,none,.stay)
private theorem bits_path {D T P bits entry out} (room:D+6 ≤ P)
    (blank:T D=none) (last:T (D+6)=none) (values:∀ j:Fin 5,T (D+1+j.val)=some (bits j))
    (code:BitsRows (Safe:=Safe) bits entry out) :
    Path M Safe P 13 (node entry D T) (node out D T) := by
  have e:=keep entry (code.states ⟨0,by decide⟩) D (D+1) T .right (P:=P) (by omega) (by omega) code.safeEntry
    (by rw [blank];exact code.enter) rfl
  have read (j:Fin 5) : Path M Safe P 1
      (node (code.states (Fin.castSucc j)) (D+1+j.val) T)
      (node (code.states (Fin.succ j)) (D+1+(j.val+1)) T) := by
    exact keep _ _ _ _ T .right (P:=P) (by have h:=j.isLt;omega) (by have h:=j.isLt;omega)
      (code.safeStates _) (by rw [values j];exact code.reads j) (by change (D+1+j.val)+1=D+1+(j.val+1);omega)
  have a:=read ⟨0,by decide⟩
  have b:=read ⟨1,by decide⟩
  have c:=read ⟨2,by decide⟩
  have d:=read ⟨3,by decide⟩
  have f:=read ⟨4,by decide⟩
  have take:=keep (code.states ⟨5,by decide⟩) code.back (D+6) (D+5) T .left (P:=P) room (by omega)
    (code.safeStates _) (by rw [last];exact code.finish) (by change D+6-1=D+5;omega)
  have retreat:=sweepL code.back T D 5 (P:=P) (by omega) code.safeBack (by
    intro i lo hi
    let j:=i-D-1
    have hj:j < 5:=by dsimp only [j];omega
    have pos:D+1+j=i:=by dsimp only [j];omega
    have val:=values ⟨j,hj⟩
    rw [pos] at val
    rw [val];exact code.retreat _)
  have stop:=keep code.back out D D T .stay (P:=P) (by omega) (by omega) code.safeBack
    (by rw [blank];exact code.exit) rfl
  exact e.append (a.append (b.append (c.append (d.append (f.append (take.append (retreat.append stop)))))))
private structure MetaRows (bits : Fin 5 → Bool) (entry out : Fin M.stateCount) where
  first : Fin M.stateCount
  fieldEntry : Fin M.stateCount
  returnEntry : Fin M.stateCount
  homeEntry : Fin M.stateCount
  fromH : FromHRows (Safe:=Safe) entry first
  outward : RouteR M Safe 0 12 first fieldEntry
  bitsCode : BitsRows (Safe:=Safe) bits fieldEntry returnEntry
  inward : RouteL M Safe 12 0 returnEntry homeEntry
  home : ToHRows (Safe:=Safe) homeEntry out
private theorem metadata_path {D T H Q F P bits entry out} (grid:Grid D T)
    (anchor:D 0=F+1) (metaWidth:D 13=D 12+6) (room:D 13 ≤ P)
    (positive:0 < Q) (arena:H+Q < F) (th:T H=none) (tf:T F=some false)
    (marks:∀ i,H < i → i ≤ H+Q → T i=some true)
    (gap:∀ i,H+Q < i → i < F → T i=none)
    (values:∀ j:Fin 5,T (D 12+1+j.val)=some (bits j))
    (code:MetaRows (Safe:=Safe) bits entry out) :
    Path M Safe P (2*(D 12-H)+38) (node entry H T) (node out H T) := by
  have d0:D 0 ≤ P:=le_trans (mono grid 0 13 (by decide) le_rfl) room
  have first:=from_H positive arena (show F+1 ≤ P by omega) tf th marks gap code.fromH
  rw [←anchor] at first
  have route:=grid.goR code.outward (by decide) room
  have metaPart:=bits_path (show D 12+6 ≤ P by omega) (blanks grid 12 (by decide))
    (by rw [←metaWidth];exact blanks grid 13 (by decide)) values code.bitsCode
  have back:=grid.goL code.inward (by decide) room
  have last:=to_H positive arena (show F+1 ≤ P by omega)
    (by rw [←anchor];exact blanks grid 0 (by decide)) tf th marks gap code.home
  rw [←anchor] at last
  have whole:=first.append (route.append (metaPart.append (back.append last)))
  have order:=mono grid 0 12 (by decide) (by decide)
  convert whole using 1
  omega
end PhysicalCallerClosure
