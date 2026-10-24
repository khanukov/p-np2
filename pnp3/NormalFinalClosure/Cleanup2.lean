import NormalFinalClosure.RepCounters2
import NormalFinalClosure.SourceCertificates2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["Node","Path","ClearRows","clear_run","keep"]),
    (`PhysicalCallerClosure.UnaryCopy,`PhysicalCallerClosure,["field"]),
    (`NormalFinalClosure.Copy2,`NormalFinalClosure,["paint_field"]),
    (`NormalFinalClosure.Frame2,`NormalFinalClosure,["GuardFrame","D","repImage"]),
    (`NormalFinalClosure.FrameFacts2,`NormalFinalClosure,["rep_grid","d_mono"]),
    (`NormalFinalClosure.RepCounters2,`NormalFinalClosure,["rep_disjoint","rep_field4","rep_field5","rep_field6","rep_field11"]),
    (`NormalFinalClosure.SourceImage2,`NormalFinalClosure,["rep_frame_low","rep_unchanged"]),
    (`NormalFinalClosure.SourceRoute2,`NormalFinalClosure,["LowFrame.room","LowFrame.right","LowFrame.fence","LowFrame.paid","LowFrame.gap","LowFrame.d0"]),
    (`NormalFinalClosure.Navigation2,`NormalFinalClosure,["DToHRows","d_to_h"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing exact whole-cleanup API {name}"
      let some i:=e.getModuleIdxFor? name | throwError "Missing whole-cleanup owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong whole-cleanup owner"
      logInfo m!"whole-final-cleanup-interface|{name}|{ci.type}"
      let aliasName:=(leaf.splitOn ".").getLast!
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac do
    let owner:=`PhysicalCallerClosure.Engine
    let name:=Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") "Node") "mk"
    let e←getEnv
    let some (.ctorInfo ci):=e.find? name | throwError "Missing cleanup Node"
    let some i:=e.getModuleIdxFor? name | throwError "Missing cleanup Node owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong cleanup Node owner"
    closeMainGoal `node (mkConst name (ci.levelParams.map Level.param))
private theorem clear_stack {S z n F r W source T} (_fr:GuardFrame S z n F r W source T)
    (records : List Nat) :
    field (repImage T F r n S S 0 0 0 0 records) (D F r n) 10 (3*r+3)=
      repImage T F r n S S 0 0 0 0 [] := by
  funext i
  have nohole:¬(i=S ∧ S < S):=by omega
  by_cases inside:D F r n 10 < i ∧ i < D F r n 11
  · have bit:i-D F r n 10 ≤ 3*r+3:=by
      change F+9*r+2*n+11 < i ∧ i < F+12*r+2*n+15 at inside
      change i-(F+9*r+2*n+11) ≤ 3*r+3
      omega
    simp only [field,decide_eq_true bit,repImage,if_neg nohole,
      if_neg (rep_disjoint (by decide : 10 ≤ 12) (by decide : 4 ≤ 12) (by decide) inside),
      if_neg (rep_disjoint (by decide : 10 ≤ 12) (by decide : 5 ≤ 12) (by decide) inside),
      if_neg (rep_disjoint (by decide : 10 ≤ 12) (by decide : 6 ≤ 12) (by decide) inside),
      if_neg (rep_disjoint (by decide : 10 ≤ 12) (by decide : 11 ≤ 12) (by decide) inside),
      List.length_nil,Nat.not_lt_zero,if_pos inside,if_false]
  · simp only [field,repImage,inside,if_false]
variable {M : UniformTM} {Safe : Fin M.stateCount → Prop}
private def CleanChain (start verdict : Fin M.stateCount) : Prop :=
  ∃ c5 c6 c11 stack home last : Fin M.stateCount,
    ClearRows (Safe:=Safe) 4 false start c5 ∧ ClearRows (Safe:=Safe) 5 false c5 c6 ∧
    ClearRows (Safe:=Safe) 6 false c6 c11 ∧ ClearRows (Safe:=Safe) 11 false c11 stack ∧
    ClearRows (Safe:=Safe) 10 true stack home ∧ DToHRows (Safe:=Safe) home last ∧ Safe last ∧
    M.step last none=(verdict,none,.stay)
/-- Common real cleanup suffix, with literal terminal stay, full source/frame
restoration and an explicit price. It is parameterized by ACTUAL row proofs,
not a desired result/run, and is shared by all six fixed cleanup entries. -/
private theorem clean_chain {S z n F r W source T} (fr:GuardFrame S z n F r W source T)
    {start verdict : Fin M.stateCount} (code:CleanChain (Safe:=Safe) start verdict)
    (a b c index : Nat) (records : List Nat) :
    ∃ t,t ≤ 512*(D F r n 13+1) ∧ Path M Safe (D F r n 13) t
      (node start (D F r n 0) (repImage T F r n S S a b c index records))
      (node verdict (S+z+2+n+1) (repImage T F r n S S 0 0 0 0 [])) := by
  obtain ⟨s5,s6,s11,stack,home,last,c4,c5,c6,c11,c10,back,sl,stop⟩:=code
  have g:=rep_grid fr S a b c index records
  have p4:=clear_run g (by decide) le_rfl c4
  rw [paint_field g 4 (by decide) false,rep_field4 fr] at p4
  have g4:=rep_grid fr S 0 b c index records
  have p5:=clear_run g4 (by decide) le_rfl c5
  rw [paint_field g4 5 (by decide) false,rep_field5 fr] at p5
  have g5:=rep_grid fr S 0 0 c index records
  have p6:=clear_run g5 (by decide) le_rfl c6
  rw [paint_field g5 6 (by decide) false,rep_field6 fr] at p6
  have g6:=rep_grid fr S 0 0 0 index records
  have p11:=clear_run g6 (by decide) le_rfl c11
  rw [paint_field g6 11 (by decide) false,rep_field11 fr] at p11
  have g11:=rep_grid fr S 0 0 0 0 records
  have p10:=clear_run g11 (by decide) le_rfl c10
  rw [paint_field g11 10 (by decide) true,
    show D F r n 11-D F r n 10-1=3*r+3 by
      change (F+12*r+2*n+15)-(F+9*r+2*n+11)-1=3*r+3
      omega] at p10
  simp only [ite_true] at p10
  rw [clear_stack fr] at p10
  let E:=repImage T F r n S S 0 0 0 0 []
  have low:=rep_frame_low fr S 0 0 0 0 []
  have fit:F+1 ≤ D F r n 13:=by change F+1 ≤ F+13*r+2*n+22;omega
  have retreat:=d_to_h (room low) fit (d0 low) (right low) (fence low) (paid low) (gap low) back
  have bound:=room low
  have atH:E (S+z+2+n+1)=none:=right low
  have stay:=keep last verdict (S+z+2+n+1) (S+z+2+n+1) E .stay (P:=D F r n 13)
    (by omega) (by omega) sl (by rw [atH];exact stop) rfl
  have path:=p4.append (p5.append (p6.append (p11.append (p10.append (retreat.append stay)))))
  refine ⟨(2*(D F r n 5-D F r n 0+4)+2)+((2*(D F r n 6-D F r n 0+5)+2)+
    ((2*(D F r n 7-D F r n 0+6)+2)+((2*(D F r n 12-D F r n 0+11)+2)+
      ((2*(D F r n 11-D F r n 0+10)+2)+(F-(S+z+2+n+1)+2+1))))),?_,?_⟩
  · have costs (j : Nat) (hj:j ≤ 12):2*(D F r n (j+1)-D F r n 0+j)+2 ≤ 64*(D F r n 13+1):=by
      have h:=d_mono F r n (j+1) 13 (by omega) (by decide)
      omega
    have a:2*(D F r n 5-D F r n 0+4)+2 ≤ 64*(D F r n 13+1):=costs 4 (by decide)
    have b:2*(D F r n 6-D F r n 0+5)+2 ≤ 64*(D F r n 13+1):=costs 5 (by decide)
    have c:2*(D F r n 7-D F r n 0+6)+2 ≤ 64*(D F r n 13+1):=costs 6 (by decide)
    have d:2*(D F r n 12-D F r n 0+11)+2 ≤ 64*(D F r n 13+1):=costs 11 (by decide)
    have e:2*(D F r n 11-D F r n 0+10)+2 ≤ 64*(D F r n 13+1):=costs 10 (by decide)
    have Fp:F ≤ D F r n 13:=by change F ≤ F+13*r+2*n+22;omega
    omega
  · exact path
end NormalFinalClosure
