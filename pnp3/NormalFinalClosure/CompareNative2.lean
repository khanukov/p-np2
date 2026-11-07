import NormalFinalClosure.CompareStop2
import NormalFinalClosure.PrefixDigit2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["Node","Path"]),
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["Safe2"]),
    (`NormalFinalClosure.Frame2,`NormalFinalClosure,["D","GuardFrame","repImage"]),
    (`NormalFinalClosure.FrameFacts2,`NormalFinalClosure,["rep_grid"]),
    (`NormalFinalClosure.BufferImage2,`NormalFinalClosure,["buffer_width","rep_record","rep_free"]),
    (`NormalFinalClosure.BufferProcess2,`NormalFinalClosure,["rep_process"]),
    (`NormalFinalClosure.BECode2,`NormalFinalClosure,["selectState","select_safe"]),
    (`NormalFinalClosure.IndexImage2,`NormalFinalClosure,["sourceMode"]),
    (`NormalFinalClosure.PrefixCode2,`NormalFinalClosure,["compareState"]),
    (`NormalFinalClosure.NativeCleanup2,`NormalFinalClosure,["start"]),
    (`NormalFinalClosure.CompareSupport2,`NormalFinalClosure,["CompareRows"]),
    (`NormalFinalClosure.CompareKernel2,`NormalFinalClosure,["compare_bit"]),
    (`NormalFinalClosure.CompareStop2,`NormalFinalClosure,["compare_stop"]),
    (`NormalFinalClosure.CompareCertificates2,`NormalFinalClosure,["compare_1506","compare_2312","compare_3030"]),
    (`NormalFinalClosure.SourceConsumer2,`NormalFinalClosure,["source_consume"]),
    (`NormalFinalClosure.SourceAdvance2,`NormalFinalClosure,["AdvanceRows"]),
    (`NormalFinalClosure.AdvanceCertificates2,`NormalFinalClosure,["advance_1597","advance_2403","virtualAdvance_3121"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing full-image comparison API"
      let some i:=e.getModuleIdxFor? name | throwError "Missing full-image comparison owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong full-image comparison owner"
      logInfo m!"full-image-native-comparison-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous (leaf.splitOn ".").getLast!) name::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac do
    let owner:=`PhysicalCallerClosure.Engine
    let name:=Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") "Node") "mk"
    let e←getEnv
    let some (.ctorInfo ci):=e.find? name | throwError "Missing full-image comparison Node constructor"
    let some i:=e.getModuleIdxFor? name | throwError "Missing full-image comparison Node owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong full-image comparison Node owner"
    closeMainGoal `node (mkConst name (ci.levelParams.map Level.param))
private def modeValue (mode : Fin 3) : Bool := decide (mode.val=1)
private def compareAdvance (k : Nat) (m : Fin 3) := selectState k m 1597 2403 3121
private theorem compare_code (k : Nat) (m : Fin 3) :
    CompareRows (Safe:=Safe2 k) (compareState k m) (compareAdvance k m) (start k true m) (start k false m) (modeValue m) := by
  fin_cases m
  · exact compare_1506 k
  · exact compare_2312 k
  · exact compare_3030 k
private theorem advance_code (k : Nat) (b : Bool) :
    AdvanceRows (Safe:=Safe2 k) (compareAdvance k (if b then 1 else 0)) (compareState k) b := by
  cases b
  · exact advance_1597 k
  · exact advance_2403 k
private theorem compare_consume (k : Nat) {S z n F r W source T}
    (fr:GuardFrame S z n F r W source T) (cursor a : Nat) (records : List Nat)
    (lo:S-r ≤ cursor) (hi:cursor ≤ S) :
    ∃ t,t ≤ 16*(D F r n 13+1) ∧ Path (machine2 k) (Safe2 k) (D F r n 13) t
      (node (compareAdvance k (sourceMode source cursor)) (D F r n 0)
        (repImage T F r n S cursor a 0 0 0 records))
      (node (compareState k (sourceMode source (min (cursor+1) S))) (D F r n 0)
        (repImage T F r n S (min (cursor+1) S) a 0 0 0 records)) :=
  source_consume k fr cursor a 0 0 0 records lo hi (compareAdvance k) (compareState k)
    (advance_code k) (select_safe k 2 1597 2403 3121) (virtualAdvance_3121 k)
private theorem processed_cells {S z n F r W source T} (fr:GuardFrame S z n F r W source T)
    (cursor a : Nat) (records : List Nat) (seen : Nat) (cap:records.length ≤ r)
    (past:∀ j,j < seen → j < records.length ∧ records[j]! = 3) :
    ∀ j,j < seen →
      repImage T F r n S cursor a 0 0 0 records (D F r n 10+1+3*j)=some false ∧
      repImage T F r n S cursor a 0 0 0 records (D F r n 10+1+3*j+1)=some true ∧
      repImage T F r n S cursor a 0 0 0 records (D F r n 10+1+3*j+2)=some true := by
  intro j hj
  obtain ⟨stored,code⟩:=past j hj
  have c0:=rep_record fr cursor a 0 0 0 records j 0 (by omega) stored (by decide)
  have c1:=rep_record fr cursor a 0 0 0 records j 1 (by omega) stored (by decide)
  have c2:=rep_record fr cursor a 0 0 0 records j 2 (by omega) stored (by decide)
  rw [code] at c0 c1 c2
  exact ⟨c0,c1,c2⟩
/-- Whole same-table active comparison and exact011 image update. All compared
bytes are physically present records derived from original prefix execution. -/
private theorem compare_record (k : Nat) {S z n F r W source T}
    (fr:GuardFrame S z n F r W source T) (cursor a : Nat) (records : List Nat) (seen : Nat)
    (cap:records.length ≤ r) (past:∀ j,j < seen → j < records.length ∧ records[j]! = 3)
    (stored:seen < records.length) (bit : Bool) (codeAt:records[seen]! = if bit then 2 else 1) :
    ∃ t,t ≤ 128*(D F r n 13+1) ∧
      if bit=modeValue (sourceMode source cursor) then Path (machine2 k) (Safe2 k) (D F r n 13) t
        (node (compareState k (sourceMode source cursor)) (D F r n 0)
          (repImage T F r n S cursor a 0 0 0 records))
        (node (compareAdvance k (sourceMode source cursor)) (D F r n 0)
          (repImage T F r n S cursor a 0 0 0 (records.set seen 3)))
      else Path (machine2 k) (Safe2 k) (D F r n 13) t
        (node (compareState k (sourceMode source cursor)) (D F r n 0)
          (repImage T F r n S cursor a 0 0 0 records))
        (node (start k false (sourceMode source cursor)) (D F r n 0)
          (repImage T F r n S cursor a 0 0 0 records)) := by
  have g:=rep_grid fr cursor a 0 0 0 records
  have width:=buffer_width F r n
  have c0:=rep_record fr cursor a 0 0 0 records seen 0 (by omega) stored (by decide)
  have c1:=rep_record fr cursor a 0 0 0 records seen 1 (by omega) stored (by decide)
  have c2:=rep_record fr cursor a 0 0 0 records seen 2 (by omega) stored (by decide)
  rw [codeAt] at c0 c1 c2
  have cell0:repImage T F r n S cursor a 0 0 0 records (D F r n 10+1+3*seen)=some false:=by cases bit <;> exact c0
  have cell1:repImage T F r n S cursor a 0 0 0 records (D F r n 10+1+3*seen+1)=some bit:=by cases bit <;> exact c1
  have cell2:repImage T F r n S cursor a 0 0 0 records (D F r n 10+1+3*seen+2)=some (!bit):=by cases bit <;> exact c2
  obtain ⟨t,tp,path⟩:=compare_bit g le_rfl seen (by omega) (processed_cells fr cursor a records seen cap past)
    bit cell0 cell1 cell2 (compare_code k (sourceMode source cursor))
  rw [rep_process fr cursor a 0 0 0 records seen (by omega) stored (by rw [codeAt];cases bit <;> decide)] at path
  exact ⟨t,tp,path⟩
private theorem compare_end (k : Nat) {S z n F r W source T}
    (fr:GuardFrame S z n F r W source T) (cursor a : Nat) (records : List Nat) (seen : Nat)
    (cap:records.length ≤ r) (past:∀ j,j < seen → j < records.length ∧ records[j]! = 3)
    (finished:seen=records.length ∨ seen < records.length ∧ records[seen]! = 0) :
    ∃ t,t ≤ 128*(D F r n 13+1) ∧ Path (machine2 k) (Safe2 k) (D F r n 13) t
      (node (compareState k (sourceMode source cursor)) (D F r n 0)
        (repImage T F r n S cursor a 0 0 0 records))
      (node (start k true (sourceMode source cursor)) (D F r n 0)
        (repImage T F r n S cursor a 0 0 0 records)) := by
  have g:=rep_grid fr cursor a 0 0 0 records
  have width:=buffer_width F r n
  have seenRoom:seen ≤ r:=by rcases finished with eq|h <;> omega
  apply compare_stop g le_rfl seen (by omega) (processed_cells fr cursor a records seen cap past) _ (compare_code k (sourceMode source cursor))
  rcases finished with free|⟨stored,zero⟩
  · left
    have cell:=rep_free fr cursor a 0 0 0 records seen 0 (by omega) seenRoom (by decide)
    exact cell
  · right
    have c0:=rep_record fr cursor a 0 0 0 records seen 0 (by omega) stored (by decide)
    have c1:=rep_record fr cursor a 0 0 0 records seen 1 (by omega) stored (by decide)
    have c2:=rep_record fr cursor a 0 0 0 records seen 2 (by omega) stored (by decide)
    rw [zero] at c0 c1 c2
    exact ⟨c0,c1,c2⟩
end NormalFinalClosure
