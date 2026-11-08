import NormalFinalClosure.CompareCertificates2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["Node","Path","Grid","RouteR","Grid.goR","Grid.goL","Grid.change_some","Grid.cells","put","dest","keep","hop","sweepL"]),
    (`PhysicalCallerClosure.UnaryCopy,`PhysicalCallerClosure,["blanks","mono"]),
    (`NormalFinalClosure.CompareSupport2,`NormalFinalClosure,["CompareRows","CycleRows","cycle_walk","RetreatRows","retreat_run"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing complete literal compare kernel API"
      let some i:=e.getModuleIdxFor? name | throwError "Missing complete compare kernel owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong complete compare kernel owner"
      logInfo m!"complete-literal-compare-kernel-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous (leaf.splitOn ".").getLast!) name::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac do
    let owner:=`PhysicalCallerClosure.Engine
    let name:=Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") "Node") "mk"
    let e←getEnv
    let some (.ctorInfo ci):=e.find? name | throwError "Missing compare kernel Node constructor"
    let some i:=e.getModuleIdxFor? name | throwError "Missing compare kernel Node owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong compare kernel Node owner"
    closeMainGoal `node (mkConst name (ci.levelParams.map Level.param))
variable {M : UniformTM} {Safe : Fin M.stateCount → Prop}
private theorem compare_seek {D T P entry enter first second third}
    (g:Grid D T) (room:D 13 ≤ P) (seen : Nat) (fit:D 10+3*seen+1 < D 11)
    (route:RouteR M Safe 0 10 entry enter) (se:Safe enter)
    (enterRow:M.step enter none=(first,none,.right))
    (cycle:CycleRows (Safe:=Safe) first second third)
    (processed:∀ j,j < seen → T (D 10+1+3*j)=some false ∧
      T (D 10+1+3*j+1)=some true ∧ T (D 10+1+3*j+2)=some true) :
    Path M Safe P (D 10-D 0+10+1+3*seen) (node entry (D 0) T) (node first (D 10+1+3*seen) T) := by
  have dp:=(mono g 11 13 (by decide) le_rfl).trans room
  have begin:=goR g route (by decide) room
  have one:=keep enter first (D 10) (D 10+1) T .right (P:=P) (by omega) (by omega) se
    (by rw [blanks g 10 (by decide)];exact enterRow) rfl
  have scan:=cycle_walk (P:=P) cycle (D 10+1) seen (by omega) processed
  have path:=begin.append (one.append scan)
  convert path using 1
  omega
private theorem compare_cycle {first second third0 third1}
    (sf:Safe first) (ss:Safe second) (st:Safe third1)
    (atFirst:M.step first (some false)=(second,some false,.right))
    (atSecond:∀ b,M.step second (some b)=(if b then third1 else third0,some b,.right))
    (atThird:M.step third1 (some true)=(first,some true,.right)) :
    CycleRows (Safe:=Safe) first second third1 := by
  exact ⟨sf,ss,st,atFirst,by simpa only [ite_true] using atSecond true,atThird⟩
/-- COMPLETE record comparison at the first unprocessed active bit, with real
routes, all processed records, exact two-write011 update or literal bad-entry
return. Bool false (including virtual mode2) is successful when it matches. -/
private theorem compare_bit {D T P entry good done bad value} (g:Grid D T) (room:D 13 ≤ P)
    (seen : Nat) (fit:D 10+3*seen+3 < D 11)
    (processed:∀ j,j < seen → T (D 10+1+3*j)=some false ∧
      T (D 10+1+3*j+1)=some true ∧ T (D 10+1+3*j+2)=some true)
    (bit : Bool) (cell0:T (D 10+1+3*seen)=some false)
    (cell1:T (D 10+1+3*seen+1)=some bit) (cell2:T (D 10+1+3*seen+2)=some (!bit))
    (code:CompareRows (Safe:=Safe) entry good done bad value) :
    let h:=D 10+1+3*seen
    ∃ t,t ≤ 128*(P+1) ∧
      if bit=value then Path M Safe P t (node entry (D 0) T)
        (node good (D 0) (put (put T (h+2) (some true)) (h+1) (some true)))
      else Path M Safe P t (node entry (D 0) T) (node bad (D 0) T) := by
  intro h
  obtain ⟨enter,first,second,third0,third1,write2,back,ret,rd,rb,route,outRoute,se,sf,ss,st0,st1,sw,sb,enterRow,freeRow,firstRow,secondRow,zeroRow,processedRow,matchRow,writeRow,backRow,stopRow,doneRows,badRows⟩:=code
  have dP:=(mono g 11 13 (by decide) le_rfl).trans room
  have seek:=compare_seek g room seen (by omega) route se enterRow
    (compare_cycle sf ss st1 firstRow secondRow processedRow) processed
  have one:=keep first second h (h+1) T .right (P:=P) (by omega) (by omega) sf
    (by rw [cell0];exact firstRow) rfl
  have two:=keep second (if bit then third1 else third0) (h+1) (h+2) T .right (P:=P) (by omega) (by omega) ss
    (by rw [cell1];exact secondRow bit) rfl
  have thirdSafe:Safe (if bit then third1 else third0):=by cases bit;exact st0;exact st1
  by_cases equal:bit=value
  · have three:=hop (if bit then third1 else third0) write2 (h+2) (h+1) T (some true) .left (P:=P)
      (by omega) (by omega) thirdSafe (by rw [cell2];simpa only [if_pos equal] using matchRow bit) (by simp only [dest];omega)
    let E1:=put T (h+2) (some true)
    have bit1:E1 (h+1)=some bit:=by
      simp only [E1,put,show h+1≠h+2 by omega,if_false]
      exact cell1
    have four:=hop write2 back (h+1) h E1 (some true) .left (P:=P) (by omega) (by omega) sw
      (by rw [bit1];exact writeRow bit) (by simp only [dest];omega)
    let E2:=put E1 (h+1) (some true)
    have g1:=change_some g (h+2) (!bit) true cell2
    have g2:=change_some g1 (h+1) bit true bit1
    change Grid D E2 at g2
    have retreat:=sweepL back E2 (D 10) (3*seen+1) (P:=P) (by omega) sb (by
      intro i lo hi
      obtain ⟨b,hb⟩:=cells g2 10 i (by decide) lo (by change i < D 11;omega)
      rw [hb];exact backRow b)
    rw [show D 10+(3*seen+1)=h by omega] at retreat
    have last:=keep back ret (D 10) (D 10) E2 .stay (P:=P) (by omega) (by omega) sb
      (by rw [blanks g2 10 (by decide)];exact stopRow) rfl
    have finish:=goL g2 outRoute (by decide) room
    have path:=seek.append (one.append (two.append (three.append (four.append (retreat.append (last.append finish))))))
    refine ⟨2*(D 10-D 0+10)+6*seen+7,by omega,?_⟩
    rw [if_pos equal]
    convert path using 1
    omega
  · have three:=keep (if bit then third1 else third0) rb (h+2) (h+2) T .stay (P:=P)
      (by omega) (by omega) thirdSafe (by rw [cell2];simpa only [if_neg equal] using matchRow bit) rfl
    have finish:=retreat_run g room (h+2) (by omega) (by omega) badRows
    have path:=seek.append (one.append (two.append (three.append finish)))
    refine ⟨2*(D 10-D 0+10)+6*seen+8,by omega,?_⟩
    rw [if_neg equal]
    convert path using 1
    omega
end NormalFinalClosure
