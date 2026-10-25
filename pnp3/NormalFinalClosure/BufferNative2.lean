import NormalFinalClosure.BufferCertificates2
import NormalFinalClosure.RepCounters2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["Node","Path"]),
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["Safe2"]),
    (`NormalFinalClosure.Frame2,`NormalFinalClosure,["D","GuardFrame","repImage"]),
    (`NormalFinalClosure.FrameFacts2,`NormalFinalClosure,["rep_grid","d_mono"]),
    (`NormalFinalClosure.BufferImage2,`NormalFinalClosure,["buffer_width","rep_record","rep_free","first_false","rep_append"]),
    (`NormalFinalClosure.BufferAppend2,`NormalFinalClosure,["AppendRows","append_run"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing whole-image physical append API"
      let some i:=e.getModuleIdxFor? name | throwError "Missing physical append owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong physical append owner"
      logInfo m!"whole-prefix-append-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous (leaf.splitOn ".").getLast!) name::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac do
    let owner:=`PhysicalCallerClosure.Engine
    let name:=Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") "Node") "mk"
    let e←getEnv
    let some (.ctorInfo ci):=e.find? name | throwError "Missing prefix append Node constructor"
    let some i:=e.getModuleIdxFor? name | throwError "Missing prefix append Node owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong prefix append Node owner"
    closeMainGoal `node (mkConst name (ci.levelParams.map Level.param))
private theorem append_record (k : Nat) {S z n F r W source T}
    (fr:GuardFrame S z n F r W source T) (cursor a b c index : Nat) (records : List Nat)
    (capacity:records.length ≤ r) (codes:∀ j,j < records.length → records[j]! < 4)
    (code : Nat) (bound:code < 4) (entry out : Fin (machine2 k).stateCount)
    (rows:AppendRows (Safe:=Safe2 k) entry out (Nat.testBit code 1) (Nat.testBit code 0)) :
    ∃ t,t ≤ 128*(D F r n 13+1) ∧ Path (machine2 k) (Safe2 k) (D F r n 13) t
      (node entry (D F r n 0) (repImage T F r n S cursor a b c index records))
      (node out (D F r n 0) (repImage T F r n S cursor a b c index (records++[code]))) := by
  have g:=rep_grid fr cursor a b c index records
  have width:=buffer_width F r n
  have path:=append_run g le_rfl records.length (by omega) (by
    intro j hj
    have cell:=rep_record fr cursor a b c index records j 0 (by omega) hj (by decide)
    simpa only [Nat.add_zero,Nat.sub_zero,first_false _ (codes j hj)] using cell)
    (fun bit hb=>rep_free fr cursor a b c index records records.length bit le_rfl capacity hb) rows
  dsimp only at path
  rw [rep_append fr cursor a b c index records code bound capacity] at path
  refine ⟨2*(D F r n 10-D F r n 0+10)+6*records.length+7,?_,path⟩
  have d10:=d_mono F r n 10 13 (by decide) (by decide)
  have d11:=d_mono F r n 11 13 (by decide) (by decide)
  omega
end NormalFinalClosure
