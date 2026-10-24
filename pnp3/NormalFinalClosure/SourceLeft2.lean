import NormalFinalClosure.SourceAdvance2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["Node","Path","keep","hop","put","dest","sweepR"]),
    (`NormalFinalClosure.SourceRoute2,`NormalFinalClosure,["LowFrame","LowFrame.room","LowFrame.eof","LocateRows","DSToRows","SDToRows","locate","ds","sd","low_put"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing exact source-left API {name}"
      let some i:=e.getModuleIdxFor? name | throwError "Missing source-left owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong source-left owner"
      logInfo m!"literal-source-left-interface|{name}|{ci.type}"
      let aliasName:=(leaf.splitOn ".").getLast!
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac do
    let owner:=`PhysicalCallerClosure.Engine
    let name:=Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") "Node") "mk"
    let e←getEnv
    let some (.ctorInfo ci):=e.find? name | throwError "Missing left Node constructor"
    let some i:=e.getModuleIdxFor? name | throwError "Missing left Node owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong left Node owner"
    closeMainGoal `node (mkConst name (ci.levelParams.map Level.param))
variable {M : UniformTM} {Safe : Fin M.stateCount → Prop}
private def LeftTailRows (read : Fin M.stateCount) (out : Bool → Fin M.stateCount) : Prop :=
  ∃ scan atS : Bool → Fin M.stateCount,Safe read ∧ (∀ b,Safe (scan b)) ∧
    (∀ b,M.step read (some b)=(scan b,none,.right)) ∧
    (∀ b v,M.step (scan b) (some v)=(scan b,some v,.right)) ∧
    (∀ b,M.step (scan b) none=(atS b,none,.stay)) ∧
    ∀ b,SDToRows (Safe:=Safe) (atS b) (out b)
private theorem lift_left {T S z n F P c read out b} (fr:LowFrame T S z n F)
    (fit:F+1 ≤ P) (cp:0 < c) (cS:c ≤ S) (bit:T (c-1)=some b)
    (source:∀ i,c ≤ i → i < S → ∃ v,T i=some v)
    (code:LeftTailRows (Safe:=Safe) read out) :
    Path M Safe P (F-c+4) (node read (c-1) T) (node (out b) (F+1) (put T (c-1) none)) := by
  obtain ⟨scan,atS,sr,ss,lift,loop,stop,back⟩:=code
  have bound:=room fr
  have one:=hop read (scan b) (c-1) c T none .right (P:=P) (by omega) (by omega) sr
    (by rw [bit];exact lift b) (by simp only [dest];omega)
  let E:=put T (c-1) none
  have frE:LowFrame E S z n F:=low_put fr (by omega)
  have middle:=sweepR (scan b) E c (S-c) (P:=P) (by omega) (ss b) (by
    intro i lo hi
    obtain ⟨v,hv⟩:=source i lo (by omega)
    change M.step (scan b) (put T (c-1) none i)=(scan b,put T (c-1) none i,.right)
    rw [show put T (c-1) none i=T i by simp only [put,show i≠c-1 by omega,if_false],hv]
    exact loop b v)
  rw [show c+(S-c)=S by omega] at middle
  have stay:=keep (scan b) (atS b) S S E .stay (P:=P) (by omega) (by omega) (ss b)
    (by rw [eof frE];exact stop b) rfl
  have finish:=sd frE fit (back b)
  have path:=one.append (middle.append (stay.append finish))
  convert path using 1
  omega
private def PhysicalLeftRows (entry : Fin M.stateCount) (out : Bool → Fin M.stateCount) (b : Bool) : Prop :=
  ∃ hole read,LocateRows (Safe:=Safe) entry hole ∧ Safe hole ∧
    M.step hole none=(read,some b,.left) ∧ LeftTailRows (Safe:=Safe) read out
private theorem left_physical {T S z n F P c entry out b} (fr:LowFrame T S z n F)
    (fit:F+1 ≤ P) (cp:0 < c) (cS:c < S) (hole:T c=none)
    (source:∀ i,c-1 ≤ i → i < S → i≠c → ∃ v,T i=some v)
    (code:PhysicalLeftRows (Safe:=Safe) entry out b) :
    ∃ v,T (c-1)=some v ∧ Path M Safe P (2*(F+1-c)+7)
      (node entry (F+1) T) (node (out v) (F+1) (put (put T c (some b)) (c-1) none)) := by
  obtain ⟨holeState,read,find,sh,write,tail⟩:=code
  have bound:=room fr
  have begin:=locate fr fit cS hole (by intro i lo hi;exact source i (by omega) hi (by omega)) find
  have one:=hop holeState read c (c-1) T (some b) .left (P:=P) (by omega) (by omega) sh
    (by rw [hole];exact write) rfl
  let E:=put T c (some b)
  have frE:LowFrame E S z n F:=low_put fr cS
  obtain ⟨v,hv⟩:=source (c-1) le_rfl (by omega) (by omega)
  have bit:E (c-1)=some v:=by simp only [E,put,show c-1≠c by omega,if_false];exact hv
  have restored:∀ i,c ≤ i → i < S → ∃ v,E i=some v:=by
    intro i lo hi
    by_cases eq:i=c
    · subst i;exact ⟨b,by simp only [E,put,if_true]⟩
    · obtain ⟨v,hv⟩:=source i (by omega) hi eq
      exact ⟨v,by simp only [E,put,eq,if_false];exact hv⟩
  have last:=lift_left frE fit cp cS.le bit restored tail
  have path:=begin.append (one.append last)
  refine ⟨v,hv,?_⟩
  convert path using 1
  omega
private def EOFLeftRows (entry : Fin M.stateCount) (out : Bool → Fin M.stateCount) : Prop :=
  ∃ hole read,DSToRows (Safe:=Safe) entry hole ∧ Safe hole ∧
    M.step hole none=(read,none,.left) ∧ LeftTailRows (Safe:=Safe) read out
private theorem left_eof {T S z n F P entry out} (fr:LowFrame T S z n F)
    (fit:F+1 ≤ P) (sp:0 < S) (source:∃ v,T (S-1)=some v)
    (code:EOFLeftRows (Safe:=Safe) entry out) :
    ∃ v,T (S-1)=some v ∧ Path M Safe P (2*(F+1-S)+6)
      (node entry (F+1) T) (node (out v) (F+1) (put T (S-1) none)) := by
  obtain ⟨hole,read,find,sh,write,tail⟩:=code
  have bound:=room fr
  have begin:=ds fr fit find
  have one:=keep hole read S (S-1) T .left (P:=P) (by omega) (by omega) sh
    (by rw [eof fr];exact write) rfl
  obtain ⟨v,hv⟩:=source
  have last:=lift_left fr fit sp le_rfl hv (by intro i lo hi;omega) tail
  have path:=begin.append (one.append last)
  refine ⟨v,hv,?_⟩
  convert path using 1
  omega
end NormalFinalClosure
