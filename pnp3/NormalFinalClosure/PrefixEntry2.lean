import NormalFinalClosure.PrefixCode2
import NormalFinalClosure.IndexRun2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["Node","Path","keep"]),
    (`PhysicalCallerClosure.UnaryCopy,`PhysicalCallerClosure,["blanks"]),
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["ns2","Safe2"]),
    (`NormalFinalClosure.Frame2,`NormalFinalClosure,["D","GuardFrame","repImage","GuardFrame.windowRoom"]),
    (`NormalFinalClosure.FrameFacts2,`NormalFinalClosure,["rep_grid","d_mono"]),
    (`NormalFinalClosure.RepCounters2,`NormalFinalClosure,["rep_width","rep_unary5","rep_unary6","rep_field5"]),
    (`NormalFinalClosure.IndexImage2,`NormalFinalClosure,["sourceMode","rep_unary3"]),
    (`NormalFinalClosure.BECode2,`NormalFinalClosure,["beDone","select_safe"]),
    (`NormalFinalClosure.Copy2,`NormalFinalClosure,["copy_run"]),
    (`NormalFinalClosure.PrefixCode2,`NormalFinalClosure,["prefixState","prefixAdvance","prefixCopy","prefixCopyCode","prefix_entry","prefix_advance_code","prefix_virtual_advance"]),
    (`NormalFinalClosure.SourceConsumer2,`NormalFinalClosure,["source_consume"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing connected prefix preparation API"
      let some i:=e.getModuleIdxFor? name | throwError "Missing prefix preparation owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong prefix preparation owner"
      logInfo m!"connected-prefix-preparation-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous (leaf.splitOn ".").getLast!) name::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac do
    let owner:=`PhysicalCallerClosure.Engine
    let name:=Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") "Node") "mk"
    let e←getEnv
    let some (.ctorInfo ci):=e.find? name | throwError "Missing prefix preparation Node constructor"
    let some i:=e.getModuleIdxFor? name | throwError "Missing prefix preparation Node owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong prefix preparation Node owner"
    closeMainGoal `node (mkConst name (ci.levelParams.map Level.param))
private theorem prefix_begin (k : Nat) {S z n F r W source T}
    (fr:GuardFrame S z n F r W source T) (cursor index : Nat) :
    ∃ t,t ≤ 512*(W+1)*(D F r n 13+1) ∧ Path (machine2 k) (Safe2 k) (D F r n 13) t
      (node (beDone k (sourceMode source cursor)) (D F r n 0)
        (repImage T F r n S cursor (W-index) 0 0 index []))
      (node (prefixState k (sourceMode source cursor)) (D F r n 0)
        (repImage T F r n S cursor (W-index) W 0 index [])) := by
  have g:=rep_grid fr cursor (W-index) 0 0 index []
  have fit:=d_mono F r n 0 13 (by decide) (by decide)
  let m:=sourceMode source cursor
  have entry:=keep (beDone k m) (prefixCopy k m) (D F r n 0) (D F r n 0)
    (repImage T F r n S cursor (W-index) 0 0 index []) .stay (P:=D F r n 13) fit fit
    (select_safe k m 1149 2001 2703) (by rw [blanks g 0 (by decide)];exact prefix_entry k m) rfl
  obtain ⟨t,tp,copy⟩:=copy_run g (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    le_rfl (fun j hj=>rep_width F r n j (by rcases hj with h|h|h;exact Or.inl h;exact Or.inr (Or.inr (Or.inl h));exact Or.inr (Or.inr (Or.inr (Or.inl h)))))
    (rep_unary3 fr cursor (W-index) 0 0 index [])
    (rep_unary5 fr cursor (W-index) 0 0 index [])
    (rep_unary6 fr cursor (W-index) 0 0 index []) (windowRoom fr) (prefixCopyCode k m)
  rw [rep_field5 fr] at copy
  refine ⟨1+t,?_,entry.append copy⟩
  have pos:0 < (W+1)*(D F r n 13+1):=by positivity
  nlinarith only [tp,pos]
private theorem prefix_consume (k : Nat) {S z n F r W source T}
    (fr:GuardFrame S z n F r W source T) (cursor a b c index : Nat) (records : List Nat)
    (lo:S-r ≤ cursor) (hi:cursor ≤ S) :
    ∃ t,t ≤ 16*(D F r n 13+1) ∧ Path (machine2 k) (Safe2 k) (D F r n 13) t
      (node (prefixAdvance k (sourceMode source cursor)) (D F r n 0)
        (repImage T F r n S cursor a b c index records))
      (node (prefixState k (sourceMode source (min (cursor+1) S))) (D F r n 0)
        (repImage T F r n S (min (cursor+1) S) a b c index records)) :=
  source_consume k fr cursor a b c index records lo hi (prefixAdvance k) (prefixState k)
    (prefix_advance_code k) (select_safe k 2 1475 2281 3029) (prefix_virtual_advance k)
end NormalFinalClosure
