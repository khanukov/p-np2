import StandardTMBridgeClosure.Tape
namespace StandardTMBridgeClosure
open Pnp3.Complexity.Uniform.V1 Turing Lean Elab Command
run_cmd do
  let e←getEnv
  for (owner,leaf,kind) in [(`StandardTMBridgeClosure.Tape,"At","definition"),
      (`StandardTMBridgeClosure.Tape,"shifted","definition"),
      (`StandardTMBridgeClosure.Tape,"cell","definition"),
      (`StandardTMBridgeClosure.Tape,"cell_at","theorem"),
      (`StandardTMBridgeClosure.Tape,"at_write","theorem"),
      (`StandardTMBridgeClosure.Tape,"at_move","theorem"),
      (`StandardTMBridgeClosure.Tape,"represents_at","theorem"),
      (`StandardTMBridgeClosure.Machine,"phase","definition")] do
    let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "StandardTMBridgeClosure") leaf
    let some ci:=e.find? n | throwError "Missing exact native interface {n}"
    let actual:=match ci with|.thmInfo _=>"theorem"|.defnInfo _=>"definition"|_=>"other"
    unless actual==kind do throwError "Wrong native interface kind"
    let some i:=e.getModuleIdxFor? n | throwError "Missing native owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong native owner"
    logInfo m!"typed-private-interface|{owner}|{n}|kind={kind}|{(repr ci.type).pretty 1000000000}"
    modifyScope fun s=>{s with openDecls:=.explicit (Name.str .anonymous leaf) n::s.openDecls}
private theorem native_step (M : UniformTM) {N B : Nat} (c : Config M.stateCount N B)
    (d : TM0.Cfg (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4)))
    (rel:Represents M c d) (safe:c.state≠M.accept ∧ c.state≠M.reject)
    (room:(M.step c.state (c.tape c.head)).2.2=Move.right → c.head.val+1 < tapeLength N B) :
    ∃ (mid last : TM0.Cfg (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4))),
      TM0.step (compile M) d=some mid ∧ TM0.step (compile M) mid=some last ∧
      Represents M (M.stepConfig c) last ∧
      mid.q=some ((M.step c.state (c.tape c.head)).1,phase (M.step c.state (c.tape c.head)).2.2) ∧
      ∀ i : Int,mid.Tape.nth i=
        if i=0 then (decide (c.head.val=0),(M.step c.state (c.tape c.head)).2.1)
        else cell c.tape ((c.head.val : Int)+i) := by
  obtain ⟨state,tape⟩:=(represents_at M c d).mp rel
  have head:d.Tape.head=(decide (c.head.val=0),c.tape c.head):=by
    simpa only [Tape.nth_zero,Int.add_zero,cell_at] using tape 0
  let a:=M.step c.state (c.tape c.head)
  let W:=d.Tape.write (decide (c.head.val=0),a.2.1)
  let mid : TM0.Cfg (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4)):=⟨some (a.1,phase a.2.2),W⟩
  let last : TM0.Cfg (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4)):=
    ⟨some (a.1,0),shifted c.head a.2.2 W⟩
  have nt:¬(c.state=M.accept ∨ c.state=M.reject):=not_or_intro safe.1 safe.2
  have enter:TM0.step (compile M) d=some mid:=by
    simp [TM0.step,compile,state,head,nt,mid,W,a]
  have leave:TM0.step (compile M) mid=some last:=by
    cases direction:a.2.2 with
    | left=>
      by_cases origin:c.head.val=0
      · simp [TM0.step,compile,mid,last,shifted,W,phase,direction,origin,Tape.write]
      · simp [TM0.step,compile,mid,last,shifted,W,phase,direction,origin,Tape.write]
    | stay=>simp [TM0.step,compile,mid,last,shifted,W,phase,direction,Tape.write_self]
    | right=>simp [TM0.step,compile,mid,last,shifted,W,phase,direction]
  refine ⟨mid,last,enter,leave,?_,rfl,?_⟩
  · apply (represents_at M (M.stepConfig c) last).mpr
    refine ⟨rfl,?_⟩
    exact at_move c.head _ W (at_write c.head c.tape d.Tape tape a.2.1) a.2.2 room
  · intro i
    change (d.Tape.write (decide (c.head.val=0),a.2.1)).nth i=_
    rw [Tape.write_nth]
    by_cases zero:i=0
    · subst i;rfl
    · simpa only [if_neg zero] using tape i
end StandardTMBridgeClosure
