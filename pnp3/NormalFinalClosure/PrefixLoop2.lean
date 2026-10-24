import NormalFinalClosure.PrefixDigit2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["Node","Path","dec_zero"]),
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["Safe2"]),
    (`NormalFinalClosure.Frame2,`NormalFinalClosure,["D","GuardFrame","repImage"]),
    (`NormalFinalClosure.FrameFacts2,`NormalFinalClosure,["rep_grid","d_mono"]),
    (`NormalFinalClosure.RepCounters2,`NormalFinalClosure,["rep_width","rep_unary5"]),
    (`NormalFinalClosure.IndexImage2,`NormalFinalClosure,["sourceMode"]),
    (`NormalFinalClosure.PrefixCode2,`NormalFinalClosure,["prefixState","compareState","prefix_dec","activeCode"]),
    (`NormalFinalClosure.PrefixDigit2,`NormalFinalClosure,["nextRecord","prefix_digit"]),
    (`NormalFinalClosure.Copy2,`NormalFinalClosure,["op_price"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing complete native prefix recurrence API"
      let some i:=e.getModuleIdxFor? name | throwError "Missing native prefix recurrence owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong native prefix recurrence owner"
      logInfo m!"complete-native-prefix-loop-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous (leaf.splitOn ".").getLast!) name::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac do
    let owner:=`PhysicalCallerClosure.Engine
    let name:=Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") "Node") "mk"
    let e←getEnv
    let some (.ctorInfo ci):=e.find? name | throwError "Missing prefix recurrence Node constructor"
    let some i:=e.getModuleIdxFor? name | throwError "Missing prefix recurrence Node owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong prefix recurrence Node owner"
    closeMainGoal `node (mkConst name (ci.levelParams.map Level.param))
/-- Proof specifications, never machine parameters or one-step instructions. -/
private def prefixGood {S : Nat} (source : Fin S → Bool) : Nat → Nat → Nat → Prop
  | _,0,_=>True
  | cursor,v+1,index=>¬(index=0 ∧ (sourceMode source cursor).val=1) ∧
      prefixGood source (min (cursor+1) S) v (index-1)
private instance prefixGood_decidable {S : Nat} (source : Fin S → Bool) (cursor v index : Nat) :
    Decidable (prefixGood source cursor v index) := by
  induction v generalizing cursor index with
  | zero=>change Decidable True;infer_instance
  | succ v ih=>
    change Decidable (¬(index=0 ∧ (sourceMode source cursor).val=1) ∧
      prefixGood source (min (cursor+1) S) v (index-1))
    have : Decidable (prefixGood source (min (cursor+1) S) v (index-1)):=ih _ _
    infer_instance
private def prefixRecords {S : Nat} (source : Fin S → Bool) : Nat → Nat → Nat → List Nat
  | _,0,_=>[]
  | cursor,v+1,index=>nextRecord (sourceMode source cursor) index::
      prefixRecords source (min (cursor+1) S) v (index-1)
private theorem nextRecord_bound (m : Fin 3) (index : Nat) : nextRecord m index < 4 := by
  dsimp only [nextRecord,activeCode]
  split
  · omega
  · split <;> omega
private theorem extended_codes (records : List Nat) (code : Nat)
    (old:∀ j,j < records.length → records[j]! < 4) (new:code < 4) :
    ∀ j,j < (records++[code]).length → (records++[code])[j]! < 4 := by
  intro j hj
  by_cases h:j < records.length
  · simpa only [List.getElem!_eq_getElem?_getD,List.getElem?_append_left h] using old j h
  · have eq:j=records.length:=by simp only [List.length_append,List.length_cons,List.length_nil] at hj;omega
    subst j
    simpa only [List.getElem!_eq_getElem?_getD,List.getElem?_append_right le_rfl,Nat.sub_self,
      List.getElem?_cons_zero,Option.getD_some] using new
/-- The COMPLETE original-source prefix scan/record loop. All inactive-padding
failure executions terminate literally; success reaches the real compare entry
with every active byte, exact preserved counters/source/beta/exterior and all
3bit records physically installed, never a host-written buffer. -/
private theorem prefix_loop (k : Nat) {S z n F r W source T}
    (fr:GuardFrame S z n F r W source T) (v cursor a index : Nat) (records : List Nat)
    (lo:S-r ≤ cursor) (hi:cursor ≤ S) (ir:index ≤ v) (space:records.length+v ≤ r)
    (codes:∀ j,j < records.length → records[j]! < 4) :
    ∃ t,t ≤ 4096*(v+1)*(D F r n 13+1) ∧
      if prefixGood source cursor v index then Path (machine2 k) (Safe2 k) (D F r n 13) t
        (node (prefixState k (sourceMode source cursor)) (D F r n 0)
          (repImage T F r n S cursor a v 0 index records))
        (node (compareState k (sourceMode source (min (cursor+v) S))) (D F r n 0)
          (repImage T F r n S (min (cursor+v) S) a 0 0 0
            (records++prefixRecords source cursor v index)))
      else Path (machine2 k) (Safe2 k) (D F r n 13) t
        (node (prefixState k (sourceMode source cursor)) (D F r n 0)
          (repImage T F r n S cursor a v 0 index records))
        (node (machine2 k).reject (S+z+2+n+1) (repImage T F r n S S 0 0 0 0 [])) := by
  induction v generalizing cursor index records with
  | zero=>
    have eq:index=0:=by omega
    subst index
    have g:=rep_grid fr cursor a 0 0 0 records
    have step:=dec_zero g (by decide) le_rfl (rep_width F r n 5 (by simp))
      (rep_unary5 fr cursor a 0 0 0 records) (prefix_dec k (sourceMode source cursor))
    refine ⟨2*(D F r n 5-D F r n 0+5)+3,?_,?_⟩
    · have p:=op_price (D F r n) 5 0 (D F r n 13)
        (d_mono F r n 5 13 (by decide) (by decide)) (by decide) (by omega)
      omega
    · simpa only [prefixGood,prefixRecords,ite_true,List.append_nil,Nat.add_zero,
        Nat.min_eq_left hi] using step
  | succ v ih=>
    obtain ⟨aTime,aPrice,headPath⟩:=prefix_digit k fr cursor a v index records lo hi (by omega)
      (by omega) (by omega) codes
    by_cases bad:index=0 ∧ (sourceMode source cursor).val=1
    · rw [if_pos bad] at headPath
      refine ⟨aTime,?_,?_⟩
      · have up:2048*(D F r n 13+1) ≤ 4096*(v+1+1)*(D F r n 13+1):=by nlinarith
        exact aPrice.trans up
      · rw [if_neg (by intro good;exact good.1 bad)]
        exact headPath
    · rw [if_neg bad] at headPath
      obtain ⟨bTime,bPrice,tail⟩:=ih (min (cursor+1) S) (index-1)
        (records++[nextRecord (sourceMode source cursor) index]) (by omega) (by omega) (by omega)
        (by simp only [List.length_append,List.length_cons,List.length_nil];omega)
        (extended_codes records _ codes (nextRecord_bound _ _))
      refine ⟨aTime+bTime,?_,?_⟩
      · nlinarith only [aPrice,bPrice]
      · by_cases good:prefixGood source (min (cursor+1) S) v (index-1)
        · rw [if_pos good] at tail
          rw [if_pos (show prefixGood source cursor (v+1) index from ⟨bad,good⟩)]
          have path:=headPath.append tail
          rw [show min (min (cursor+1) S+v) S=min (cursor+(v+1)) S by omega] at path
          simpa only [prefixRecords,List.append_assoc,List.singleton_append] using path
        · rw [if_neg good] at tail
          rw [if_neg (by intro h;exact good h.2)]
          exact headPath.append tail
end NormalFinalClosure
