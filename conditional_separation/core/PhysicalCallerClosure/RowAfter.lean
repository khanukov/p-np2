import PhysicalCallerClosure.RoundPay
import PhysicalCallerClosure.RoundShift
import PhysicalCallerClosure.RoundWrite
import PhysicalCallerClosure.NativeCleanup
import PhysicalCallerClosure.CompareStep
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command Tactic
private def select (owner : Name) (leaf kind : String) : TacticM Unit := do
  let e←getEnv
  let n:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure")
  let some ci:=e.find? n | throwError "Missing exact paid-row support {n}"
  let actual:=match ci with | .defnInfo _=>"definition" | .thmInfo _=>"theorem" | .ctorInfo _=>"constructor" | .inductInfo _=>"inductive" | _=>"other"
  unless actual==kind do throwError "Wrong paid-row support kind"
  let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
  unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
  unless e.header.moduleNames[i]! == owner do throwError "Wrong paid-row support owner"
  logInfo m!"paid-row-adapter|{n}|{ci.type}"
  closeMainGoal `select (mkConst n (ci.levelParams.map Level.param))
run_cmd do
  let e←getEnv
  for (owner,leaves) in [(`PhysicalCallerClosure.Engine,["Node","Path","Grid","NativeSafe","embed"]),
      (`PhysicalCallerClosure.RoundFrame,["Exterior"]),
      (`PhysicalCallerClosure.Compare,["flags","command","payEntry","rejectEntry"]),
      (`PhysicalCallerClosure.CompareStep,["terminal","compare_run"]),
      (`PhysicalCallerClosure.RoundGrid,["image_facts"]),(`PhysicalCallerClosure.ResetImage,["extD"]),
      (`PhysicalCallerClosure.RoundPay,["pay_frame"]),(`PhysicalCallerClosure.PaymentIncrement,["nextRow","overflowRow"]),
      (`PhysicalCallerClosure.RoundShift,["shift_frame"]),(`PhysicalCallerClosure.RoundWrite,["write_frame"]),
      (`PhysicalCallerClosure.RoundFrame,["shiftSource"]),(`PhysicalCallerClosure.WriteBits,["written"]),
      (`PhysicalCallerClosure.WriteReset,["writerEntry"]),
      (`PhysicalCallerClosure.Cleanup,["cleanupEntry","finishState"]),(`PhysicalCallerClosure.NativeCleanup,["native_cleanup"]),
      (`PhysicalCallerClosure.RowTape,["d12_lower"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing paid-row term {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong owner"
      logInfo m!"paid-row-open|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac select `PhysicalCallerClosure.Engine "Node.mk" "constructor"
private theorem execute_native {k N B P price H : Nat} {q d : Fin (callerMachine k).stateCount}
    {T U : Nat → Option Bool} (path:Path (callerMachine k) (NativeSafe k) P price (node q H T) (node d H U))
    (fit:P < tapeLength N B) (hH:H < tapeLength N B) :
    (callerMachine k).run price ⟨q,⟨H,hH⟩,fun i=>T i.val⟩=⟨d,⟨H,hH⟩,fun i=>U i.val⟩:=by
  simpa only [embed] using path.execute fit
private theorem frame_shift : ∀ {T E : Nat → Option Bool} {S z n F r M p q : Nat}
    {beta : Fin n → Bool} {bits : Fin 5 → Bool}
    (_frame:Exterior T E S z n F r M p q beta bits (decide (p < S)) (decide (M < S)))
    (_arena:S+z+n+3 < F) (_before:M < S → p+1 < M-1),
    Exterior T (shiftSource T E S p) S z n F r M (p+1) q beta bits (decide (p+1 < S)) (decide (M < S)) := by run_tac select `PhysicalCallerClosure.RoundFrame "Exterior.shift" "theorem"
private theorem after_body (k B R S z n r g W M p q row nodes used rem quota : Nat)
    (a tag result : Fin 3) (source : Fin S → Bool) (T E : Nat → Option Bool)
    (frame:Exterior T E S z n (FixedRawLengthFence.fencePos R) r M p q
      (Pnp3.Core.vecOfNat n row) (flags a tag false) (decide (p < S)) (decide (M < S)))
    (rowBound:row < 2^n) (positive:0 < q)
    (arena:S+z+n+3+q < FixedRawLengthFence.fencePos R) (mp:0 < M)
    (before:M < S → p < M-1) (nextBefore:row+1 < 2^n → M < S → p+1 < M-1)
    (src:∀ i,p < i → ∀ hi:i < S,T i=some (source ⟨i,hi⟩))
    (eof:T S=none) (reg:∀ i,S < i → i < S+z+2 → T i=some false)
    (left:T (S+z+2)=none) (right:T (S+z+n+3)=none)
    (fence:T (FixedRawLengthFence.fencePos R)=some false)
    (endBlank:T (SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12+6)=none)
    (alphaTag:a.val=2 ↔ S ≤ M) (tableTag:tag.val=2 ↔ S ≤ p)
    (av:M < S → T (M-1)=some (decide (a.val=1)))
    (tv:p < S → T p=some (decide (tag.val=1)))
    (fit:SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12+6 < tapeLength R B)
    (hH:S+z+n+3 < tapeLength R B) :
    let F:=FixedRawLengthFence.fencePos R
    let I:=SerializedBody.image E F r n g W (S-min M S) nodes used rem quota
    let c : Config (callerMachine k).stateCount R B:=⟨evalState k (terminal result),⟨S+z+n+3,hH⟩,fun i=>I i.val⟩
    ∃ t,0 < t ∧ t ≤ 256*(SerializedBody.delimiter F r n 12+7) ∧
      if result.val=2 ∨ decide (result.val=1)≠decide (tag.val=1) then
        (callerMachine k).run t c=⟨(callerMachine k).reject,⟨S+z+n+3,hH⟩,
          fun i=>callerImage T S z n F r g W M q (Pnp3.Core.vecOfNat n row) nodes used rem quota i.val⟩
      else if row+1=2^n then
        (callerMachine k).run t c=⟨rowsDone k,⟨S+z+n+3,hH⟩,
          fun i=>callerImage T S z n F r g W M (max 1 (q-1)) (Pnp3.Core.vecOfNat n ((row+1)%(2^n))) nodes used rem quota i.val⟩
      else if q=1 then
        (callerMachine k).run t c=⟨(callerMachine k).reject,⟨S+z+n+3,hH⟩,
          fun i=>callerImage T S z n F r g W M 1 (Pnp3.Core.vecOfNat n ((row+1)%(2^n))) nodes used rem quota i.val⟩
      else ∃ E',Exterior T E' S z n F r M (p+1) (q-1)
        (Pnp3.Core.vecOfNat n (row+1)) (flags a (SerializedBody.sourceMode source (p+1)) false)
        (decide (p+1 < S)) (decide (M < S)) ∧
        (callerMachine k).run t c=⟨resetEntry k a,⟨S+z+n+3,hH⟩,
          fun i=>SerializedBody.image E' F r n g W (S-min M S) nodes used rem quota i.val⟩ := by
  dsimp only
  let F:=FixedRawLengthFence.fencePos R
  let H:=S+z+n+3
  let d:=SerializedBody.delimiter F r n 12
  let I:=SerializedBody.image E F r n g W (S-min M S) nodes used rem quota
  let c : Config (callerMachine k).stateCount R B:=⟨evalState k (terminal result),⟨H,hH⟩,fun i=>I i.val⟩
  have dl:=d12_lower F r n
  have hd:H ≤ d:=by dsimp only [H,d];omega
  obtain ⟨grid,_ts,_registers,_tl,th,_beta,marks,gap,tf,metadata,_last⟩:=image_facts T E S z n F r g W M p q nodes used rem quota
    _ _ _ _ frame arena eof reg left right fence endBlank
  obtain ⟨cmp,_safe,_foot⟩:=compare_run k result a tag false R B H q F (d+6) (extD F r n) I grid rfl rfl le_rfl fit
    positive arena th tf marks gap metadata hH
  have d12:extD F r n 12=d:=rfl
  rw [d12] at cmp
  have cprice:2*(d-H)+39 ≤ 2*d+39:=by omega
  have sourceExists:∀ i,p < i → i < S → ∃ b,T i=some b:=by intro i lo hi;exact ⟨_,src i lo hi⟩
  by_cases bad:result.val=2 ∨ decide (result.val=1)≠decide (tag.val=1)
  · simp only [if_pos bad]
    have control:command k result a tag false=cleanupEntry k false a tag:=by unfold command;rw [if_pos bad];rfl
    rw [control] at cmp
    obtain ⟨price,bound,path⟩:=native_cleanup k false a tag T E S z n F r g W M p q nodes used rem quota _ _ frame positive
      arena mp before sourceExists eof reg left right fence endBlank alphaTag tableTag av tv
    have endEq:=execute_native path fit hH
    refine ⟨2*(d-H)+39+price,by omega,by change 2*(d-H)+39+price ≤ 256*(d+7);have b:price ≤ 64*(d+7):=bound;omega,?_⟩
    rw [UniformTM.run_add,cmp,endEq]
    rfl
  · simp only [if_neg bad]
    have control:command k result a tag false=payEntry k a tag:=by unfold command;rw [if_neg bad];rfl
    rw [control] at cmp
    obtain ⟨U,payTime,payBound,paid,payPath⟩:=pay_frame k a tag T E S z n F r g W M p q row nodes used rem quota frame
      rowBound positive arena eof reg left right fence endBlank
    have payRun:=execute_native payPath fit hH
    have qp:0 < max 1 (q-1):=by omega
    have qa:S+z+n+3+max 1 (q-1) < F:=by omega
    have paySmall:payTime ≤ 6*d+46:=by
      change payTime ≤ 2*q+2*n+2*d+46 at payBound
      have qd:q ≤ d:=by dsimp only [H] at hd;omega
      have nd:n ≤ d:=by dsimp only [H] at hd;omega
      omega
    by_cases last:row+1=2^n
    · simp only [if_pos last]
      have control:overflowRow k a tag=cleanupEntry k true a tag:=by fin_cases a <;> fin_cases tag <;> rfl
      rw [if_pos last,control] at payRun
      obtain ⟨price,bound,path⟩:=native_cleanup k true a tag T U S z n F r g W M p (max 1 (q-1)) nodes used rem quota _ _ paid qp
        qa mp before sourceExists eof reg left right fence endBlank alphaTag tableTag av tv
      have endEq:=execute_native path fit hH
      refine ⟨2*(d-H)+39+payTime+price,by omega,by change 2*(d-H)+39+payTime+price ≤ 256*(d+7);have b:price ≤ 64*(d+7):=bound;omega,?_⟩
      rw [show 2*(d-H)+39+payTime+price=(2*(d-H)+39)+(payTime+price) by omega,UniformTM.run_add,cmp,
        UniformTM.run_add,payRun,endEq]
      rfl
    · simp only [if_neg last]
      have rowNext:row+1 < 2^n:=by omega
      rw [if_neg last] at payRun
      have nextMod:(row+1)%(2^n)=row+1:=Nat.mod_eq_of_lt rowNext
      rw [nextMod] at paid
      rw [nextMod]
      by_cases one:q=1
      · simp only [if_pos one]
        rw [if_pos one] at payRun
        have control:rejectEntry k a tag=cleanupEntry k false a tag:=by fin_cases a <;> fin_cases tag <;> rfl
        rw [control] at payRun
        have qeq:max 1 (q-1)=1:=by omega
        rw [qeq] at paid
        obtain ⟨price,bound,path⟩:=native_cleanup k false a tag T U S z n F r g W M p 1 nodes used rem quota _ _ paid
          (by omega) (by omega) mp before sourceExists eof reg left right fence endBlank alphaTag tableTag av tv
        have endEq:=execute_native path fit hH
        refine ⟨2*(d-H)+39+payTime+price,by omega,by change 2*(d-H)+39+payTime+price ≤ 256*(d+7);have b:price ≤ 64*(d+7):=bound;omega,?_⟩
        rw [show 2*(d-H)+39+payTime+price=(2*(d-H)+39)+(payTime+price) by omega,UniformTM.run_add,cmp,
          UniformTM.run_add,payRun,endEq]
        rfl
      · simp only [if_neg one]
        rw [if_neg one] at payRun
        have qeq:max 1 (q-1)=q-1:=by omega
        have flagEq:flags a tag (decide (q=1))=flags a tag false:=by simp only [decide_eq_false one]
        rw [qeq,flagEq] at paid
        obtain ⟨shiftTime,shiftBound,shiftPath⟩:=shift_frame k a tag T U S z n F r g W M p (q-1) nodes used rem quota _ _ paid
          (by omega) (by omega) (nextBefore rowNext) source src eof reg left right fence endBlank alphaTag tableTag tv
        have shiftRun:=execute_native shiftPath fit hH
        have shifted:=frame_shift paid (by omega) (nextBefore rowNext)
        obtain ⟨nextFrame,writePath⟩:=write_frame k a (SerializedBody.sourceMode source (p+1)) T (shiftSource T U S p)
          S z n F r g W M (p+1) (q-1) nodes used rem quota _ _ _ _ shifted (by omega) (by omega)
          eof reg left right fence endBlank
        have writeRun:=execute_native writePath fit hH
        refine ⟨2*(d-H)+39+payTime+shiftTime+(2*(d-H)+38),by omega,?_,?_⟩
        · change 2*(d-H)+39+payTime+shiftTime+(2*(d-H)+38) ≤ 256*(d+7)
          have sb:shiftTime ≤ 2*H+7:=shiftBound
          omega
        · refine ⟨_,nextFrame,?_⟩
          rw [show 2*(d-H)+39+payTime+shiftTime+(2*(d-H)+38)=
            (2*(d-H)+39)+(payTime+(shiftTime+(2*(d-H)+38))) by omega,
            UniformTM.run_add,cmp,UniformTM.run_add,payRun,UniformTM.run_add,shiftRun,writeRun]
end PhysicalCallerClosure
