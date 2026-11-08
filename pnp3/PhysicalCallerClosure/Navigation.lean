import PhysicalCallerClosure.Engine
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
  for leaf in ["Node","Path","put","keep","hop","sweepL","sweepR","crossL","crossR","dest"] do
    let n:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.Engine 0) "PhysicalCallerClosure")
    let some ci:=e.find? n | throwError "Missing Engine support {n}"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.Engine do throwError "Wrong owner"
    logInfo m!"copy-open|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac support "Node.mk" "constructor"
variable {M : UniformTM} {Safe : Fin M.stateCount → Prop}
private def ToHRows (entry out : Fin M.stateCount) : Prop :=
  ∃ f g m : Fin M.stateCount,Safe entry ∧ Safe f ∧ Safe g ∧ Safe m ∧
    M.step entry none=(f,none,.left) ∧ M.step f (some false)=(g,some false,.left) ∧
    M.step g none=(g,none,.left) ∧ M.step g (some true)=(m,some true,.left) ∧
    M.step m (some true)=(m,some true,.left) ∧ M.step m none=(out,none,.stay)
private theorem to_H {H Q F P T entry out} (positive:0 < Q) (arena:H+Q < F)
    (room:F+1 ≤ P) (d0:T (F+1)=none) (tf:T F=some false) (th:T H=none)
    (marks:∀ i,H < i → i ≤ H+Q → T i=some true)
    (gap:∀ i,H+Q < i → i < F → T i=none) (code:ToHRows (Safe:=Safe) entry out) :
    Path M Safe P (F+2-H) (node entry (F+1) T) (node out H T) := by
  rcases code with ⟨f,g,m,se,sf,sg,sm,re,rf,rg,rt,rm,rn⟩
  have first:=keep entry f (F+1) F T .left room (by omega) se (by rw [d0];exact re) (by simp [dest])
  have fence:=keep f g F (F-1) T .left (P:=P) (by omega) (by omega) sf (by rw [tf];exact rf) (by simp [dest])
  have gs:=sweepL g T (H+Q) (F-(H+Q+1)) (P:=P) (by omega) sg (by
    intro i lo hi;rw [gap i lo (by omega)];exact rg)
  rw [show H+Q+(F-(H+Q+1))=F-1 by omega] at gs
  have touch:=keep g m (H+Q) (H+(Q-1)) T .left (P:=P) (by omega) (by omega) sg
    (by rw [marks _ (by omega) le_rfl];exact rt) (by simp only [dest];omega)
  have ms:=sweepL m T H (Q-1) (P:=P) (by omega) sm (by
    intro i lo hi;rw [marks i lo (by omega)];exact rm)
  have last:=keep m out H H T .stay (P:=P) (by omega) (by omega) sm (by rw [th];exact rn) rfl
  have path:=first.append (fence.append (gs.append (touch.append (ms.append last))))
  convert path using 1
  omega
end PhysicalCallerClosure
