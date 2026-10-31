import PhysicalCallerClosure.WriteBits
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
run_cmd do
  let e←getEnv
  for leaf in ["WriteRows","written","written_outside","written_value","write_path"] do
    let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.WriteBits 0) "PhysicalCallerClosure") leaf
    let some ci:=e.find? n | throwError "Missing exact writer term {n}"
    let some i:=e.getModuleIdxFor? n | throwError "Missing writer owner"
    unless i.toNat < e.header.moduleNames.size do throwError "Writer owner outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.WriteBits do throwError "Wrong writer owner"
    logInfo m!"writer-support|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
variable {M : UniformTM} {Safe : Fin M.stateCount → Prop}
-- Only fields 0..11 are traversed. Metadata may be entirely blank on first entry.
private structure FrontGrid (D : Nat → Nat) (T : Nat → Option Bool) : Prop where
  rise : ∀ j,j < 12 → D j < D (j+1)
  mono : ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b
  blank : ∀ j,j ≤ 12 → T (D j)=none
  cells : ∀ j i,j < 12 → D j < i → i < D (j+1) → ∃ b,T i=some b
private theorem front_after {D T bits} (g:FrontGrid D T) :
    FrontGrid D (written T (D 12) bits 5) := by
  have low (i) (hi:i ≤ D 12) : written T (D 12) bits 5 i=T i:=written_outside (Or.inl hi)
  refine ⟨g.rise,g.mono,?_,?_⟩
  · intro j hj;rw [low _ (g.mono j 12 hj le_rfl)];exact g.blank j hj
  · intro j i hj lo hi
    rw [low _ (by have h:=g.mono (j+1) 12 (by omega) le_rfl;omega)]
    exact g.cells j i hj lo hi
private theorem front_complete {D T bits} (g:FrontGrid D T)
    (width:D 13=D 12+6) (last:T (D 13)=none) :
    Grid D (written T (D 12) bits 5) := by
  have f:=front_after (bits:=bits) g
  refine gridMk ?_ ?_ ?_ ?_
  · intro j hj
    by_cases h:j < 12
    · exact g.rise j h
    · have eq:j=12:=by omega
      subst j;change D 12 < D 13;omega
  · intro a b ab hb
    by_cases h:b ≤ 12
    · exact g.mono a b ab h
    · have eq:b=13:=by omega
      subst b
      by_cases ha:a ≤ 12
      · have hh:=g.mono a 12 ha le_rfl;omega
      · have eq:a=13:=by omega
        subst a;exact le_rfl
  · intro j hj
    by_cases h:j ≤ 12
    · exact f.blank j h
    · have eq:j=13:=by omega
      subst j
      rw [written_outside (Or.inr (by omega))];exact last
  · intro j i hj lo hi
    by_cases h:j < 12
    · exact f.cells j i h lo hi
    · have eq:j=12:=by omega
      subst j
      change i < D 13 at hi
      let v:=i-D 12-1
      have hv:v < 5:=by dsimp only [v];omega
      have pos:D 12+1+v=i:=by dsimp only [v];omega
      have val:=written_value T (D 12) bits ⟨v,hv⟩
      rw [pos] at val
      exact ⟨bits ⟨v,hv⟩,val⟩
private structure WriteMetaRows (bits : Fin 5 → Bool) (entry out : Fin M.stateCount) where
  first : Fin M.stateCount
  fieldEntry : Fin M.stateCount
  returnEntry : Fin M.stateCount
  homeEntry : Fin M.stateCount
  fromH : FromHRows (Safe:=Safe) entry first
  outward : RouteR M Safe 0 12 first fieldEntry
  bitsCode : WriteRows (Safe:=Safe) bits fieldEntry returnEntry
  inward : RouteL M Safe 12 0 returnEntry homeEntry
  home : ToHRows (Safe:=Safe) homeEntry out
private theorem write_metadata {D T H Q F P bits entry out} (grid:FrontGrid D T)
    (anchor:D 0=F+1) (metaWidth:D 13=D 12+6) (last:T (D 13)=none) (room:D 13 ≤ P)
    (positive:0 < Q) (arena:H+Q < F) (th:T H=none) (tf:T F=some false)
    (marks:∀ i,H < i → i ≤ H+Q → T i=some true)
    (gap:∀ i,H+Q < i → i < F → T i=none)
    (code:WriteMetaRows (Safe:=Safe) bits entry out) :
    Path M Safe P (2*(D 12-H)+38) (node entry H T) (node out H (written T (D 12) bits 5)) := by
  have ord:=grid.mono 0 12 (by decide) le_rfl
  have d0:D 0 ≤ P:=by omega
  have first:=from_H positive arena (show F+1 ≤ P by omega) tf th marks gap code.fromH
  rw [←anchor] at first
  have route:=code.outward.execute D T (show D 12 ≤ P by omega)
    (by intro j _ hj;exact grid.rise j hj)
    (by intro a b _ ab hb;exact grid.mono a b ab hb)
    (by intro j _ hj;exact grid.blank j hj)
    (by intro j i _ hj lo hi;exact grid.cells j i hj lo hi)
  have part:=write_path (show D 12+6 ≤ P by omega) (grid.blank 12 le_rfl)
    (by rw [←metaWidth];exact last) code.bitsCode
  let U:=written T (D 12) bits 5
  have gu:Grid D U:=front_complete grid metaWidth last
  have back:=gu.goL code.inward (by decide) room
  have low (i) (hi:i ≤ D 12) : U i=T i:=written_outside (Or.inl hi)
  have lastPart:=to_H positive arena (show F+1 ≤ P by omega)
    (by rw [←anchor];exact blanks gu 0 (by decide)) (by rw [low F (by omega)];exact tf)
    (by rw [low H (by omega)];exact th)
    (by intro i lo hi;rw [low i (by omega)];exact marks i lo hi)
    (by intro i lo hi;rw [low i (by omega)];exact gap i lo hi) code.home
  rw [←anchor] at lastPart
  have whole:=first.append (route.append (part.append (back.append lastPart)))
  convert whole using 1
  omega
end PhysicalCallerClosure
