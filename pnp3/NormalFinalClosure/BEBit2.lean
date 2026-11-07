import NormalFinalClosure.BEDouble2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["Node","Path","keep","dec_zero","dec_positive","inc_success"]),
    (`PhysicalCallerClosure.UnaryCopy,`PhysicalCallerClosure,["blanks","field_dec","field_inc"]),
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["ns2","Safe2"]),
    (`NormalFinalClosure.Frame2,`NormalFinalClosure,["D","GuardFrame","repImage","GuardFrame.windowRoom"]),
    (`NormalFinalClosure.FrameFacts2,`NormalFinalClosure,["rep_grid","d_mono"]),
    (`NormalFinalClosure.RepCounters2,`NormalFinalClosure,["rep_width","rep_unary4","rep_unary11","rep_field4","rep_field11"]),
    (`NormalFinalClosure.IndexImage2,`NormalFinalClosure,["sourceMode","sourceMode_physical","sourceMode_virtual","beState","beAdvance","be_advance"]),
    (`NormalFinalClosure.BECode2,`NormalFinalClosure,["transferDone","transfer_zero_exit","bit_pay","bit_add","select_safe"]),
    (`NormalFinalClosure.NativeCleanup2,`NormalFinalClosure,["cleanup_physical"]),
    (`NormalFinalClosure.Copy2,`NormalFinalClosure,["op_price"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing native BE bit API {name}"
      let some i:=e.getModuleIdxFor? name | throwError "Missing BE bit owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong BE bit owner"
      logInfo m!"native-BE-bit-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous (leaf.splitOn ".").getLast!) name::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac do
    let owner:=`PhysicalCallerClosure.Engine
    let name:=Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") "Node") "mk"
    let e←getEnv
    let some (.ctorInfo ci):=e.find? name | throwError "Missing bit Node constructor"
    let some i:=e.getModuleIdxFor? name | throwError "Missing bit Node owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong bit Node owner"
    closeMainGoal `node (mkConst name (ci.levelParams.map Level.param))
private def modeDigit (m : Fin 3) : Nat := if m.val=1 then 1 else 0
/-- The complete literal optional-one payment, increment and next-source read.
Occupied false and virtual EOF both contribute zero, but retain distinct actual
controls/hole behavior. A final one beyond W executes full reject cleanup. -/
private theorem bit_phase (k : Nat) {S z n F r W source T}
    (fr:GuardFrame S z n F r W source T) (cursor remaining index : Nat)
    (lo:S-r ≤ cursor) (hi:cursor ≤ S) (ir:index ≤ W) :
    let next:=index+modeDigit (sourceMode source cursor)
    ∃ t,t ≤ 2048*(D F r n 13+1) ∧
      if next ≤ W then Path (machine2 k) (Safe2 k) (D F r n 13) t
        (node (transferDone k (sourceMode source cursor)) (D F r n 0)
          (repImage T F r n S cursor (W-index) 0 remaining index []))
        (node (beState k (sourceMode source (min (cursor+1) S))) (D F r n 0)
          (repImage T F r n S (min (cursor+1) S) (W-next) 0 remaining next []))
      else Path (machine2 k) (Safe2 k) (D F r n 13) t
        (node (transferDone k (sourceMode source cursor)) (D F r n 0)
          (repImage T F r n S cursor (W-index) 0 remaining index []))
        (node (machine2 k).reject (S+z+2+n+1) (repImage T F r n S S 0 0 0 0 [])) := by
  intro next
  have wr:=windowRoom fr
  have fit:=d_mono F r n 0 13 (by decide) (by decide)
  let m:=sourceMode source cursor
  have g:=rep_grid fr cursor (W-index) 0 remaining index []
  by_cases one:m.val=1
  · have mEq:m=1:=Fin.ext one
    have phys:cursor < S:=by
      by_contra h
      have virtual:=sourceMode_virtual (source:=source) (by omega : S ≤ cursor)
      change m=2 at virtual
      rw [virtual] at one
      norm_num at one
    have value:source ⟨cursor,phys⟩=true:=by
      have hm:=sourceMode_physical (source:=source) phys
      change m=_ at hm
      rw [mEq] at hm
      cases v:source ⟨cursor,phys⟩
      · simp only [v,Bool.false_eq_true,ite_false] at hm
        cases hm
      · rfl
    have nextEq:next=index+1:=by
      change (index+if m.val=1 then 1 else 0)=index+1
      rw [if_pos one]
    by_cases ok:index < W
    · have step:=dec_positive g (by decide) le_rfl (rep_width F r n 4 (by simp))
        (rep_unary4 fr cursor (W-index) 0 remaining index []) (by omega) (by omega) (bit_pay k)
      rw [field_dec g (by decide) (rep_width F r n 4 (by simp))
        (rep_unary4 fr cursor (W-index) 0 remaining index []) (by omega) (by omega),rep_field4 fr] at step
      have g1:=rep_grid fr cursor (W-index-1) 0 remaining index []
      have add:=inc_success g1 (by decide) le_rfl (rep_width F r n 11 (by simp))
        (rep_unary11 fr cursor (W-index-1) 0 remaining index []) (by omega) (bit_add k)
      rw [field_inc g1 (by decide) (rep_width F r n 11 (by simp))
        (rep_unary11 fr cursor (W-index-1) 0 remaining index []) (by omega),rep_field11 fr] at add
      have sub:W-index-1=W-(index+1):=by omega
      rw [sub] at step add
      obtain ⟨u,up,advance⟩:=be_advance k fr cursor (W-(index+1)) 0 remaining (index+1) [] lo hi
      rw [show sourceMode source cursor=1 from mEq] at advance
      have whole:=step.append (add.append advance)
      refine ⟨(2*(D F r n 4-D F r n 0+4)+2*(W-index)+3)+((2*(D F r n 11-D F r n 0+11)+2*index+3)+u),?_,?_⟩
      · have rP:r ≤ D F r n 13:=by
          have w:=rep_width F r n 4 (by simp)
          have d:=d_mono F r n 5 13 (by decide) (by decide)
          change D F r n 5=D F r n 4+r+1 at w
          omega
        have p1:=op_price (D F r n) 4 (W-index) (D F r n 13) (d_mono F r n 4 13 (by decide) (by decide)) (by decide) (by omega)
        have p2:=op_price (D F r n) 11 index (D F r n 13) (d_mono F r n 11 13 (by decide) (by decide)) (by decide) (by omega)
        omega
      · rw [nextEq,if_pos (by omega : index+1 ≤ W),show sourceMode source cursor=1 from mEq]
        exact whole
    · have ix:index=W:=by omega
      rw [ix] at g
      have step:=dec_zero g (by decide) le_rfl (rep_width F r n 4 (by simp))
        (by simpa only [Nat.sub_self] using rep_unary4 fr cursor (W-W) 0 remaining W []) (bit_pay k)
      obtain ⟨u,up,cleanup⟩:=cleanup_physical k false fr cursor (W-W) 0 remaining W [] lo phys
      rw [value] at cleanup
      have whole:=step.append cleanup
      refine ⟨2*(D F r n 4-D F r n 0+4)+3+u,?_,?_⟩
      · have p1:=op_price (D F r n) 4 0 (D F r n 13) (d_mono F r n 4 13 (by decide) (by decide)) (by decide) (by omega)
        omega
      · rw [nextEq,if_neg (by omega : ¬index+1 ≤ W),show sourceMode source cursor=1 from mEq,ix]
        simpa only [Nat.sub_self,Bool.false_eq_true,ite_false] using whole
  · have nextEq:next=index:=by
      change (index+if m.val=1 then 1 else 0)=index
      rw [if_neg one,Nat.add_zero]
    have entry:=keep (transferDone k m) (beAdvance k m) (D F r n 0) (D F r n 0)
      (repImage T F r n S cursor (W-index) 0 remaining index []) .stay (P:=D F r n 13) fit fit
      (select_safe k m 1117 1895 2701) (by rw [blanks g 0 (by decide)];exact transfer_zero_exit k m one) rfl
    obtain ⟨u,up,advance⟩:=be_advance k fr cursor (W-index) 0 remaining index [] lo hi
    have whole:=entry.append advance
    refine ⟨1+u,by omega,?_⟩
    rw [nextEq,if_pos ir]
    exact whole
end NormalFinalClosure
