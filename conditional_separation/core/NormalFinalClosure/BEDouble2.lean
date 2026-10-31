import NormalFinalClosure.BECode2
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
    (`NormalFinalClosure.RepCounters2,`NormalFinalClosure,["rep_width","rep_unary5","rep_unary11","rep_field5","rep_field11"]),
    (`NormalFinalClosure.IndexImage2,`NormalFinalClosure,["sourceMode","sourceMode_physical","sourceMode_virtual","rep_horner"]),
    (`NormalFinalClosure.Horner2,`NormalFinalClosure,["double_loop"]),
    (`NormalFinalClosure.Copy2,`NormalFinalClosure,["transfer_run"]),
    (`NormalFinalClosure.NativeCleanup2,`NormalFinalClosure,["cleanup_physical","cleanup_virtual"]),
    (`NormalFinalClosure.BECode2,`NormalFinalClosure,["selectState","beTaken","doubleState","doublePay","doubleAdd1","doubleAdd2","transferEntry","transferState","transferDone","double_take","double_pay","double_add1","double_add2","transfer_code","double_entry","transfer_entry","select_safe"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing connected native double API {name}"
      let some i:=e.getModuleIdxFor? name | throwError "Missing connected double owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong connected double owner"
      logInfo m!"connected-BE-double-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous (leaf.splitOn ".").getLast!) name::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac do
    let owner:=`PhysicalCallerClosure.Engine
    let name:=Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") "Node") "mk"
    let e←getEnv
    let some (.ctorInfo ci):=e.find? name | throwError "Missing double Node constructor"
    let some i:=e.getModuleIdxFor? name | throwError "Missing double Node owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong double Node owner"
    closeMainGoal `node (mkConst name (ci.levelParams.map Level.param))
/-- Execute the actual cap-aware unary doubling AND the complete transfer back
into I. An overflowing paid decrement executes the real cleanup to reject/H;
no unary value beyond the physical available field is materialized. -/
private theorem double_phase (k : Nat) {S z n F r W source T}
    (fr:GuardFrame S z n F r W source T) (cursor remaining index : Nat)
    (lo:S-r ≤ cursor) (hi:cursor ≤ S) (ir:index ≤ W) :
    ∃ t,t ≤ 2048*(W+1)*(D F r n 13+1) ∧
      if 2*index ≤ W then Path (machine2 k) (Safe2 k) (D F r n 13) t
        (node (beTaken k (sourceMode source cursor)) (D F r n 0)
          (repImage T F r n S cursor (W-index) 0 remaining index []))
        (node (transferDone k (sourceMode source cursor)) (D F r n 0)
          (repImage T F r n S cursor (W-2*index) 0 remaining (2*index) []))
      else Path (machine2 k) (Safe2 k) (D F r n 13) t
        (node (beTaken k (sourceMode source cursor)) (D F r n 0)
          (repImage T F r n S cursor (W-index) 0 remaining index []))
        (node (machine2 k).reject (S+z+2+n+1) (repImage T F r n S S 0 0 0 0 [])) := by
  have wr:=windowRoom fr
  have fit:=d_mono F r n 0 13 (by decide) (by decide)
  let m:=sourceMode source cursor
  let C:=repImage T F r n S cursor (W-index) 0 remaining index []
  have g:=rep_grid fr cursor (W-index) 0 remaining index []
  have entry:=keep (beTaken k m) (doubleState k m) (D F r n 0) (D F r n 0) C .stay
    (P:=D F r n 13) fit fit (select_safe k m 890 1668 2474)
    (by dsimp only [C];rw [blanks g 0 (by decide)];exact double_entry k m) rfl
  obtain ⟨t,tp,body⟩:=double_loop g le_rfl (rep_width F r n 11 (by simp))
    (rep_width F r n 5 (by simp)) (rep_width F r n 4 (by simp))
    (double_take k m) (double_pay k m) (double_add1 k m) (double_add2 k m)
    index 0 (W-index) (by omega) (by omega) (by omega)
  change (if index ≤ W-index then _ else _) at body
  simp only [rep_horner fr,Nat.zero_add] at body
  have pMono:256*(min index (W-index)+1)*(D F r n 13+1) ≤ 256*(W+1)*(D F r n 13+1):=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 256 (by omega))
  by_cases ok:2*index ≤ W
  · rw [if_pos (by omega : index ≤ W-index)] at body
    have sub:W-index-index=W-2*index:=by omega
    rw [sub] at body
    have gr:=rep_grid fr cursor (W-2*index) (2*index) remaining 0 []
    have entry2:=keep (transferEntry k m) (transferState k m) (D F r n 0) (D F r n 0)
      (repImage T F r n S cursor (W-2*index) (2*index) remaining 0 []) .stay
      (P:=D F r n 13) fit fit (select_safe k m 1035 1813 2619)
      (by rw [blanks gr 0 (by decide)];exact transfer_entry k m) rfl
    obtain ⟨u,up,transfer⟩:=transfer_run gr (by decide) (by decide) (by decide) le_rfl
      (rep_width F r n 5 (by simp)) (rep_width F r n 11 (by simp))
      (rep_unary5 fr cursor (W-2*index) (2*index) remaining 0 [])
      (rep_unary11 fr cursor (W-2*index) (2*index) remaining 0 []) (by omega) (transfer_code k m)
    rw [rep_field5 fr,rep_field11 fr,Nat.zero_add] at transfer
    have whole:=entry.append (body.append (entry2.append transfer))
    refine ⟨1+(t+(1+u)),?_,?_⟩
    · have upMono:128*(2*index+1)*(D F r n 13+1) ≤ 128*(W+1)*(D F r n 13+1):=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 128 (by omega))
      have pos:0 < (W+1)*(D F r n 13+1):=by positivity
      nlinarith only [tp,pMono,up,upMono,pos]
    · rw [if_pos ok]
      simpa only [m,C] using whole
  · rw [if_neg (by omega : ¬index ≤ W-index)] at body
    by_cases phys:cursor < S
    · obtain ⟨u,up,cleanup⟩:=cleanup_physical k false fr cursor 0 (2*(W-index)) remaining
        (index-(W-index)-1) [] lo phys
      rw [←sourceMode_physical phys] at cleanup
      have whole:=entry.append (body.append cleanup)
      refine ⟨1+(t+u),?_,?_⟩
      · have mono:1024*(D F r n 13+1) ≤ 1024*(W+1)*(D F r n 13+1):=by nlinarith
        have pos:0 < (W+1)*(D F r n 13+1):=by positivity
        nlinarith only [tp,pMono,up,mono,pos]
      · rw [if_neg ok]
        simpa only [m,C,Bool.false_eq_true,ite_false] using whole
    · have virt:S ≤ cursor:=by omega
      obtain ⟨u,up,cleanup⟩:=cleanup_virtual k false fr cursor 0 (2*(W-index)) remaining
        (index-(W-index)-1) [] virt
      rw [←sourceMode_virtual (source:=source) virt] at cleanup
      have whole:=entry.append (body.append cleanup)
      refine ⟨1+(t+u),?_,?_⟩
      · have mono:1024*(D F r n 13+1) ≤ 1024*(W+1)*(D F r n 13+1):=by nlinarith
        have pos:0 < (W+1)*(D F r n 13+1):=by positivity
        nlinarith only [tp,pMono,up,mono,pos]
      · rw [if_neg ok]
        simpa only [m,C,Bool.false_eq_true,ite_false] using whole
end NormalFinalClosure
