import NormalFinalClosure.BEBit2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["Node","Path","dec_positive"]),
    (`PhysicalCallerClosure.UnaryCopy,`PhysicalCallerClosure,["field_dec"]),
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["Safe2"]),
    (`NormalFinalClosure.Frame2,`NormalFinalClosure,["D","GuardFrame","repImage","GuardFrame.windowRoom"]),
    (`NormalFinalClosure.FrameFacts2,`NormalFinalClosure,["rep_grid","d_mono"]),
    (`NormalFinalClosure.RepCounters2,`NormalFinalClosure,["rep_width","rep_unary6","rep_field6"]),
    (`NormalFinalClosure.IndexImage2,`NormalFinalClosure,["sourceMode","beState"]),
    (`NormalFinalClosure.BECode2,`NormalFinalClosure,["be_dec"]),
    (`NormalFinalClosure.BEDouble2,`NormalFinalClosure,["double_phase"]),
    (`NormalFinalClosure.BEBit2,`NormalFinalClosure,["modeDigit","bit_phase"]),
    (`NormalFinalClosure.Copy2,`NormalFinalClosure,["op_price"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing whole native BE digit API {name}"
      let some i:=e.getModuleIdxFor? name | throwError "Missing whole BE digit owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong whole BE digit owner"
      logInfo m!"whole-native-BE-digit-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous (leaf.splitOn ".").getLast!) name::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac do
    let owner:=`PhysicalCallerClosure.Engine
    let name:=Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") "Node") "mk"
    let e←getEnv
    let some (.ctorInfo ci):=e.find? name | throwError "Missing whole digit Node constructor"
    let some i:=e.getModuleIdxFor? name | throwError "Missing whole digit Node owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong whole digit Node owner"
    closeMainGoal `node (mkConst name (ci.levelParams.map Level.param))
/-- One COMPLETE BE digit iteration: decrement actual length, capped reverse
unary doubling, transfer, optional bit payment, and original-source advance;
every overflow executes full literal reject/H cleanup on the same allocation. -/
private theorem digit_run (k : Nat) {S z n F r W source T}
    (fr:GuardFrame S z n F r W source T) (cursor remaining index : Nat)
    (lo:S-r ≤ cursor) (hi:cursor ≤ S) (ir:index ≤ W) (remainingRoom:remaining+1 ≤ r) :
    let next:=2*index+modeDigit (sourceMode source cursor)
    ∃ t,t ≤ 8192*(W+1)*(D F r n 13+1) ∧
      if next ≤ W then Path (machine2 k) (Safe2 k) (D F r n 13) t
        (node (beState k (sourceMode source cursor)) (D F r n 0)
          (repImage T F r n S cursor (W-index) 0 (remaining+1) index []))
        (node (beState k (sourceMode source (min (cursor+1) S))) (D F r n 0)
          (repImage T F r n S (min (cursor+1) S) (W-next) 0 remaining next []))
      else Path (machine2 k) (Safe2 k) (D F r n 13) t
        (node (beState k (sourceMode source cursor)) (D F r n 0)
          (repImage T F r n S cursor (W-index) 0 (remaining+1) index []))
        (node (machine2 k).reject (S+z+2+n+1) (repImage T F r n S S 0 0 0 0 [])) := by
  intro next
  have wr:=windowRoom fr
  have g:=rep_grid fr cursor (W-index) 0 (remaining+1) index []
  have take:=dec_positive g (by decide) le_rfl (rep_width F r n 6 (by simp))
    (rep_unary6 fr cursor (W-index) 0 (remaining+1) index []) (by omega) remainingRoom
    (be_dec k (sourceMode source cursor))
  rw [field_dec g (by decide) (rep_width F r n 6 (by simp))
    (rep_unary6 fr cursor (W-index) 0 (remaining+1) index []) (by omega) remainingRoom,
    rep_field6 fr,show remaining+1-1=remaining by omega] at take
  obtain ⟨a,ap,double⟩:=double_phase k fr cursor remaining index lo hi ir
  have rP:r ≤ D F r n 13:=by
    have width:=rep_width F r n 6 (by simp)
    have mono:=d_mono F r n 7 13 (by decide) (by decide)
    change D F r n 7=D F r n 6+r+1 at width
    omega
  have p1:=op_price (D F r n) 6 (remaining+1) (D F r n 13)
    (d_mono F r n 6 13 (by decide) (by decide)) (by decide) (by omega)
  have wp:1 ≤ W+1:=by omega
  have lifted:2048*(D F r n 13+1) ≤ 2048*(W+1)*(D F r n 13+1):=by nlinarith
  by_cases ok:2*index ≤ W
  · rw [if_pos ok] at double
    obtain ⟨b,bp,bit⟩:=bit_phase k fr cursor remaining (2*index) lo hi ok
    change (if next ≤ W then _ else _) at bit
    refine ⟨(2*(D F r n 6-D F r n 0+6)+2*(remaining+1)+3)+(a+b),?_,?_⟩
    · nlinarith only [p1,ap,bp,lifted,wp]
    · by_cases good:next ≤ W
      · rw [if_pos good] at bit ⊢
        exact take.append (double.append bit)
      · rw [if_neg good] at bit ⊢
        exact take.append (double.append bit)
  · rw [if_neg ok] at double
    have doom:¬next ≤ W:=by dsimp only [next];omega
    refine ⟨(2*(D F r n 6-D F r n 0+6)+2*(remaining+1)+3)+a,?_,?_⟩
    · nlinarith only [p1,ap,lifted,wp]
    · rw [if_neg doom]
      exact take.append double
end NormalFinalClosure
