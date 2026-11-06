import NormalFinalClosure.BufferImage2
import NormalFinalClosure.CounterSupport2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["Node","Path","Grid","RouteR","RouteL","Grid.goR","Grid.goL","Grid.change_some","Grid.cells","put","dest","hop","keep","sweepL"]),
    (`PhysicalCallerClosure.UnaryCopy,`PhysicalCallerClosure,["blanks","mono"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing literal buffer execution API {name}"
      let some i:=e.getModuleIdxFor? name | throwError "Missing literal buffer owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong literal buffer owner"
      logInfo m!"literal-prefix-buffer-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous (leaf.splitOn ".").getLast!) name::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac do
    let owner:=`PhysicalCallerClosure.Engine
    let name:=Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") "Node") "mk"
    let e←getEnv
    let some (.ctorInfo ci):=e.find? name | throwError "Missing buffer Node constructor"
    let some i:=e.getModuleIdxFor? name | throwError "Missing buffer Node owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong buffer Node owner"
    closeMainGoal `node (mkConst name (ci.levelParams.map Level.param))
variable {M : UniformTM} {Safe : Fin M.stateCount → Prop}
private def TripleRows (scan s1 s2 : Fin M.stateCount) : Prop :=
  Safe scan ∧ Safe s1 ∧ Safe s2 ∧
  M.step scan (some false)=(s1,some false,.right) ∧
  (∀ b,M.step s1 (some b)=(s2,some b,.right)) ∧
  (∀ b,M.step s2 (some b)=(scan,some b,.right))
private theorem triple_walk {T P scan s1 s2} (code:TripleRows (Safe:=Safe) scan s1 s2)
    (base count : Nat) (fit:base+3*count ≤ P)
    (first:∀ j,j < count → T (base+3*j)=some false)
    (other:∀ j,j < count → ∀ bit,bit=1 ∨ bit=2 → ∃ b,T (base+3*j+bit)=some b) :
    Path M Safe P (3*count) (node scan base T) (node scan (base+3*count) T) := by
  obtain ⟨ss,sf,st,one,two,three⟩:=code
  induction count generalizing base with
  | zero=>simpa only [Nat.mul_zero,Nat.add_zero] using (Path.nil (node scan base T) (by change base ≤ P;omega))
  | succ count ih=>
    have onePath:=keep scan s1 base (base+1) T .right (P:=P) (by omega) (by omega) ss
      (by rw [show T base=some false by simpa only [Nat.mul_zero,Nat.add_zero] using first 0 (by omega)];exact one) rfl
    obtain ⟨b,hb⟩:=other 0 (by omega) 1 (Or.inl rfl)
    simp only [Nat.mul_zero,Nat.add_zero] at hb
    have twoPath:=keep s1 s2 (base+1) (base+2) T .right (P:=P) (by omega) (by omega) sf
      (by rw [hb];exact two b) rfl
    obtain ⟨c,hc⟩:=other 0 (by omega) 2 (Or.inr rfl)
    simp only [Nat.mul_zero,Nat.add_zero] at hc
    have threePath:=keep s2 scan (base+2) (base+3) T .right (P:=P) (by omega) (by omega) st
      (by rw [hc];exact three c) rfl
    have tail:=ih (base+3) (by omega) (by
      intro j hj
      simpa only [show base+3+3*j=base+3*(j+1) by omega] using first (j+1) (by omega)) (by
      intro j hj bit hbit
      simpa only [show base+3+3*j=base+3*(j+1) by omega] using other (j+1) (by omega) bit hbit)
    have path:=onePath.append (twoPath.append (threePath.append tail))
    rw [show base+3*(count+1)=base+3+3*count by omega,
      show 3*(count+1)=1+(1+(1+3*count)) by omega]
    exact path
private def AppendRows (entry out : Fin M.stateCount) (b1 b2 : Bool) : Prop :=
  ∃ enter scan skip1 skip2 write2 write3 back ret : Fin M.stateCount,
    RouteR M Safe 0 10 entry enter ∧ RouteL M Safe 10 0 ret out ∧
    Safe enter ∧ Safe write2 ∧ Safe write3 ∧ Safe back ∧
    TripleRows (Safe:=Safe) scan skip1 skip2 ∧
    M.step enter none=(scan,none,.right) ∧
    M.step scan (some true)=(write2,some false,.right) ∧
    M.step write2 (some true)=(write3,some b1,.right) ∧
    M.step write3 (some true)=(back,some b2,.left) ∧
    (∀ b,M.step back (some b)=(back,some b,.left)) ∧ M.step back none=(ret,none,.stay)
/-- Entire real 3bit append including delimiter routes, skip of ALL prior
records, sentinel writes and physical return to D0. No blank sentinel assumed. -/
private theorem append_run {D T P entry out b1 b2} (g:Grid D T) (room:D 13 ≤ P)
    (d : Nat) (fit:D 10+3*d+3 < D 11)
    (first:∀ j,j < d → T (D 10+1+3*j)=some false)
    (free:∀ bit,bit < 3 → T (D 10+1+3*d+bit)=some true)
    (code:AppendRows (Safe:=Safe) entry out b1 b2) :
    let h:=D 10+1+3*d
    Path M Safe P (2*(D 10-D 0+10)+6*d+7)
      (node entry (D 0) T)
      (node out (D 0) (put (put (put T h (some false)) (h+1) (some b1)) (h+2) (some b2))) := by
  intro h
  obtain ⟨enter,scan,skip1,skip2,write2,write3,back,ret,right,left,se,s2,s3,sb,triple,entryRow,firstRow,secondRow,thirdRow,backRow,stopRow⟩:=code
  have dP:D 11 ≤ P:=(mono g 11 13 (by decide) le_rfl).trans room
  have begin:=goR g right (by decide) room
  have entryPath:=keep enter scan (D 10) (D 10+1) T .right (P:=P) (by omega) (by omega) se
    (by rw [blanks g 10 (by decide)];exact entryRow) rfl
  have skip:=triple_walk (P:=P) triple (D 10+1) d (by omega) first (by
    intro j hj bit hb
    exact cells g 10 (D 10+1+3*j+bit) (by decide) (by omega) (by
      change D 10+1+3*j+bit < D 11
      rcases hb with h|h <;> subst bit <;> omega))
  have f0:T h=some true:=by simpa only [h,Nat.add_zero] using free 0 (by decide)
  have f1:T (h+1)=some true:=free 1 (by decide)
  have f2:T (h+2)=some true:=free 2 (by decide)
  obtain ⟨ss,_,_,_,_,_⟩:=triple
  have writeFirst:=hop scan write2 h (h+1) T (some false) .right (P:=P)
    (by omega) (by omega) ss (by rw [f0];exact firstRow) rfl
  let E1:=put T h (some false)
  have ef1:E1 (h+1)=some true:=by simp only [E1,put,show h+1≠h by omega,if_false,f1]
  have writeSecond:=hop write2 write3 (h+1) (h+2) E1 (some b1) .right (P:=P)
    (by omega) (by omega) s2 (by rw [ef1];exact secondRow) rfl
  let E2:=put E1 (h+1) (some b1)
  have ef2:E2 (h+2)=some true:=by simp only [E2,E1,put,show h+2≠h+1 by omega,show h+2≠h by omega,if_false,f2]
  have writeThird:=hop write3 back (h+2) (h+1) E2 (some b2) .left (P:=P)
    (by omega) (by omega) s3 (by rw [ef2];exact thirdRow) (by simp only [dest];omega)
  let E3:=put E2 (h+2) (some b2)
  have g1:=change_some g h true false f0
  have g2:=change_some g1 (h+1) true b1 ef1
  have g3:=change_some g2 (h+2) true b2 ef2
  change Grid D E3 at g3
  have retreat:=sweepL back E3 (D 10) (3*d+2) (P:=P) (by omega) sb (by
    intro i lo hi
    obtain ⟨b,hb⟩:=cells g3 10 i (by decide) lo (by change i < D 11;omega)
    rw [hb];exact backRow b)
  rw [show D 10+(3*d+2)=h+1 by omega] at retreat
  have last:=keep back ret (D 10) (D 10) E3 .stay (P:=P) (by omega) (by omega) sb
    (by rw [blanks g3 10 (by decide)];exact stopRow) rfl
  have finish:=goL g3 left (by decide) room
  have path:=begin.append (entryPath.append (skip.append (writeFirst.append (writeSecond.append (writeThird.append (retreat.append (last.append finish)))))))
  convert path using 1
  omega
end NormalFinalClosure
