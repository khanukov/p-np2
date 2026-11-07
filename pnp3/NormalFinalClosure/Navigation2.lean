import NormalFinalClosure.Support
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
private def navSupport (leaf kind : String) : TacticM Unit := do
  let owner:=`PhysicalCallerClosure.Engine
  let n:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure")
  let e←getEnv
  let some ci:=e.find? n | throwError "Missing exact native navigation support"
  let actual:=match ci with|.thmInfo _=>"theorem"|.defnInfo _=>"definition"|.ctorInfo _=>"constructor"|_=>"other"
  unless actual==kind do throwError "Wrong navigation support kind"
  let some i:=e.getModuleIdxFor? n | throwError "Missing navigation owner"
  unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong navigation owner"
  logInfo m!"native-nav-support|{n}|{kind}|{ci.type}"
  closeMainGoal `navSupport (mkConst n (ci.levelParams.map Level.param))
run_cmd do
  let e←getEnv
  for leaf in ["Node","Path","keep","sweepL","sweepR","dest"] do
    let owner:=`PhysicalCallerClosure.Engine
    let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
    let some ci:=e.find? n | throwError "Missing exact navigation API"
    let some i:=e.getModuleIdxFor? n | throwError "Missing navigation API owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong navigation API owner"
    logInfo m!"native-nav-open|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac navSupport "Node.mk" "constructor"
variable {M : UniformTM} {Safe : Fin M.stateCount → Prop}
private def HToSRows (entry out : Fin M.stateCount) : Prop :=
  ∃ ass reg : Fin M.stateCount,Safe entry ∧ Safe ass ∧ Safe reg ∧
    M.step entry none=(ass,none,.left) ∧
    (∀ b,M.step ass (some b)=(ass,some b,.left)) ∧ M.step ass none=(reg,none,.left) ∧
    (∀ b,M.step reg (some b)=(reg,some b,.left)) ∧ M.step reg none=(out,none,.stay)
private def SToHRows (entry out : Fin M.stateCount) : Prop :=
  ∃ reg ass : Fin M.stateCount,Safe entry ∧ Safe reg ∧ Safe ass ∧
    M.step entry none=(reg,none,.right) ∧
    (∀ b,M.step reg (some b)=(reg,some b,.right)) ∧ M.step reg none=(ass,none,.right) ∧
    (∀ b,M.step ass (some b)=(ass,some b,.right)) ∧ M.step ass none=(out,none,.stay)
private def DToHRows (entry out : Fin M.stateCount) : Prop :=
  ∃ fence gap paid : Fin M.stateCount,Safe entry ∧ Safe fence ∧ Safe gap ∧ Safe paid ∧
    M.step entry none=(fence,none,.left) ∧ M.step fence (some false)=(gap,some false,.left) ∧
    M.step gap none=(gap,none,.left) ∧ M.step gap (some true)=(paid,some true,.left) ∧
    M.step paid (some true)=(paid,some true,.left) ∧ M.step paid none=(out,none,.stay)
/-- Two distinct delimiter controls handle n=0 adjacent L/H blanks. -/
private theorem h_to_s {S z n P T entry out} (fit:S+z+2+n+1 ≤ P)
    (eof:T S=none) (left:T (S+z+2)=none) (right:T (S+z+2+n+1)=none)
    (reg:∀ i,S < i → i < S+z+2 → ∃ b,T i=some b)
    (ass:∀ i,S+z+2 < i → i < S+z+2+n+1 → ∃ b,T i=some b)
    (code:HToSRows (Safe:=Safe) entry out) :
    Path M Safe P (z+n+4) (node entry (S+z+2+n+1) T) (node out S T) := by
  obtain ⟨a,r,se,sa,sr,enter,aloop,next,rloop,stop⟩:=code
  have one:=keep entry a (S+z+2+n+1) (S+z+2+n) T .left (P:=P) fit (by omega) se
    (by rw [right];exact enter) (by simp only [dest];omega)
  have aa:=sweepL a T (S+z+2) n (P:=P) (by omega) sa (by
    intro i lo hi
    obtain ⟨b,hb⟩:=ass i lo (by omega)
    rw [hb];exact aloop b)
  have two:=keep a r (S+z+2) (S+z+1) T .left (P:=P) (by omega) (by omega) sa
    (by rw [left];exact next) (by simp only [dest];omega)
  have rr:=sweepL r T S (z+1) (P:=P) (by omega) sr (by
    intro i lo hi
    obtain ⟨b,hb⟩:=reg i lo (by omega)
    rw [hb];exact rloop b)
  rw [show S+(z+1)=S+z+1 by omega] at rr
  have last:=keep r out S S T .stay (P:=P) (by omega) (by omega) sr (by rw [eof];exact stop) rfl
  have path:=one.append (aa.append (two.append (rr.append last)))
  convert path using 1
  omega
private theorem s_to_h {S z n P T entry out} (fit:S+z+2+n+1 ≤ P)
    (eof:T S=none) (left:T (S+z+2)=none) (right:T (S+z+2+n+1)=none)
    (reg:∀ i,S < i → i < S+z+2 → ∃ b,T i=some b)
    (ass:∀ i,S+z+2 < i → i < S+z+2+n+1 → ∃ b,T i=some b)
    (code:SToHRows (Safe:=Safe) entry out) :
    Path M Safe P (z+n+4) (node entry S T) (node out (S+z+2+n+1) T) := by
  obtain ⟨r,a,se,sr,sa,enter,rloop,next,aloop,stop⟩:=code
  have one:=keep entry r S (S+1) T .right (P:=P) (by omega) (by omega) se (by rw [eof];exact enter) rfl
  have rr:=sweepR r T (S+1) (z+1) (P:=P) (by omega) sr (by
    intro i lo hi
    obtain ⟨b,hb⟩:=reg i (by omega) (by omega)
    rw [hb];exact rloop b)
  rw [show S+1+(z+1)=S+z+2 by omega] at rr
  have two:=keep r a (S+z+2) (S+z+2+1) T .right (P:=P) (by omega) (by omega) sr (by rw [left];exact next) rfl
  have aa:=sweepR a T (S+z+2+1) n (P:=P) (by omega) sa (by
    intro i lo hi
    obtain ⟨b,hb⟩:=ass i (by omega) (by omega)
    rw [hb];exact aloop b)
  rw [show S+z+2+1+n=S+z+2+n+1 by omega] at aa
  have last:=keep a out (S+z+2+n+1) (S+z+2+n+1) T .stay (P:=P) fit fit sa (by rw [right];exact stop) rfl
  have path:=one.append (rr.append (two.append (aa.append last)))
  convert path using 1
  omega
private theorem d_to_h {H F P T entry out} (room:H+1 < F) (fit:F+1 ≤ P)
    (d0:T (F+1)=none) (right:T H=none) (fence:T F=some false) (paid:T (H+1)=some true)
    (gap:∀ i,H+1 < i → i < F → T i=none) (code:DToHRows (Safe:=Safe) entry out) :
    Path M Safe P (F-H+2) (node entry (F+1) T) (node out H T) := by
  obtain ⟨f,g,p,se,sf,sg,sp,enter,atF,gloop,gstop,ploop,pstop⟩:=code
  have one:=keep entry f (F+1) F T .left (P:=P) fit (by omega) se (by rw [d0];exact enter) (by simp only [dest,Nat.add_sub_cancel])
  have two:=keep f g F (F-1) T .left (P:=P) (by omega) (by omega) sf (by rw [fence];exact atF) rfl
  have blanks:=sweepL g T (H+1) (F-(H+2)) (P:=P) (by omega) sg (by
    intro i lo hi
    rw [gap i lo (by omega)]
    exact gloop)
  rw [show H+1+(F-(H+2))=F-1 by omega] at blanks
  have three:=keep g p (H+1) H T .left (P:=P) (by omega) (by omega) sg (by rw [paid];exact gstop) (by simp only [dest,Nat.add_sub_cancel])
  have last:=keep p out H H T .stay (P:=P) (by omega) (by omega) sp (by rw [right];exact pstop) rfl
  have path:=one.append (two.append (blanks.append (three.append last)))
  convert path using 1
  omega
end NormalFinalClosure
