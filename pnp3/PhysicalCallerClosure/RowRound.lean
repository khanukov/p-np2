import PhysicalCallerClosure.RowBody
import PhysicalCallerClosure.RoundCost
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
  for (owner,leaves) in [(`PhysicalCallerClosure.RoundFrame,["Exterior"]),
      (`PhysicalCallerClosure.Compare,["flags"]),(`PhysicalCallerClosure.CompareStep,["terminal"]),
      (`PhysicalCallerClosure.RowBody,["row_body"]),(`PhysicalCallerClosure.RowAfter,["after_body"]),
      (`PhysicalCallerClosure.RoundCost,["extent_price","round_price"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing paid-row term {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong owner"
      logInfo m!"paid-row-open|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private def valueTag (b : Bool) : Fin 3:=if b then ⟨1,by decide⟩ else ⟨0,by decide⟩
private theorem tag_terminal (b : Bool) : terminal (valueTag b)=SerializedBody.done b:=by cases b <;> rfl
private theorem tag_test (b : Bool) (tag : Fin 3) :
    (valueTag b).val=2 ∨ decide ((valueTag b).val=1)≠decide (tag.val=1) ↔ b≠decide (tag.val=1):=by
  cases b <;> simp [valueTag]
private theorem valid_round (k B R S z n r g W M p q row nodes used rem quota : Nat)
    (a tag : Fin 3) (source : Fin S → Bool) (T E : Nat → Option Bool)
    (circuit : Pnp3.Models.Circuit n) (tail : List Bool)
    (parsed:decodeCircuitFull n (bitLength n) (SerializedBody.window source M W)=some (circuit,tail)) (cap:circuit.size ≤ g)
    (frame:Exterior T E S z n (FixedRawLengthFence.fencePos R) r M p q
      (Pnp3.Core.vecOfNat n row) (flags a tag false) (decide (p < S)) (decide (M < S)))
    (hr:r ≤ S) (hs:S ≤ R) (hg:g ≤ r) (hw:W ≤ r) (he:bitLength n ≤ r) (ha:S-min M S ≤ r)
    (rowBound:row < 2^n) (positive:0 < q) (arena:S+z+n+3+q < FixedRawLengthFence.fencePos R) (mp:0 < M)
    (before:M < S → p < M-1) (nextBefore:row+1 < 2^n → M < S → p+1 < M-1)
    (src:∀ i,p ≤ i → ∀ hi:i < S,T i=some (source ⟨i,hi⟩))
    (eof:T S=none) (reg:∀ i,S < i → i < S+z+2 → T i=some false)
    (left:T (S+z+2)=none) (right:T (S+z+n+3)=none) (fence:T (FixedRawLengthFence.fencePos R)=some false)
    (endBlank:T (SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12+6)=none)
    (alphaTag:a.val=2 ↔ S ≤ M) (tableTag:tag.val=2 ↔ S ≤ p)
    (av:M < S → T (M-1)=some (decide (a.val=1))) (tv:p < S → T p=some (decide (tag.val=1)))
    (fit:SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12+6 < tapeLength R B)
    (hH:S+z+n+3 < tapeLength R B) :
    let F:=FixedRawLengthFence.fencePos R
    let u:=W-tail.length
    let c : Config (callerMachine k).stateCount R B:=⟨resetEntry k a,⟨S+z+n+3,hH⟩,
      fun i=>SerializedBody.image E F r n g W (S-min M S) nodes used rem quota i.val⟩
    ∃ ready elapsed,ready < elapsed ∧ elapsed ≤ 2147483648*(R+1)^6 ∧
      (callerMachine k).run ready c=⟨evalState k (SerializedBody.entry (SerializedBody.sourceMode source M)),
        ⟨S+z+n+3,hH⟩,fun i=>SerializedBody.prepared E S M F r n g W i.val⟩ ∧
      u ≤ W ∧ tail=(SerializedBody.window source M W).drop u ∧
      if Pnp3.Models.Circuit.eval circuit (Pnp3.Core.vecOfNat n row)≠decide (tag.val=1) then
        (callerMachine k).run elapsed c=⟨(callerMachine k).reject,⟨S+z+n+3,hH⟩,
          fun i=>callerImage T S z n F r g W M q (Pnp3.Core.vecOfNat n row) circuit.size u (W-u) 0 i.val⟩
      else if row+1=2^n then
        (callerMachine k).run elapsed c=⟨rowsDone k,⟨S+z+n+3,hH⟩,
          fun i=>callerImage T S z n F r g W M (max 1 (q-1)) (Pnp3.Core.vecOfNat n ((row+1)%(2^n))) circuit.size u (W-u) 0 i.val⟩
      else if q=1 then
        (callerMachine k).run elapsed c=⟨(callerMachine k).reject,⟨S+z+n+3,hH⟩,
          fun i=>callerImage T S z n F r g W M 1 (Pnp3.Core.vecOfNat n ((row+1)%(2^n))) circuit.size u (W-u) 0 i.val⟩
      else ∃ E',Exterior T E' S z n F r M (p+1) (q-1)
        (Pnp3.Core.vecOfNat n (row+1)) (flags a (SerializedBody.sourceMode source (p+1)) false)
        (decide (p+1 < S)) (decide (M < S)) ∧
        (callerMachine k).run elapsed c=⟨resetEntry k a,⟨S+z+n+3,hH⟩,
          fun i=>SerializedBody.image E' F r n g W (S-min M S) circuit.size u (W-u) 0 i.val⟩ := by
  dsimp only
  let F:=FixedRawLengthFence.fencePos R
  let H:=S+z+n+3
  let c : Config (callerMachine k).stateCount R B:=⟨resetEntry k a,⟨H,hH⟩,
    fun i=>SerializedBody.image E F r n g W (S-min M S) nodes used rem quota i.val⟩
  let b:=Pnp3.Models.Circuit.eval circuit (Pnp3.Core.vecOfNat n row)
  obtain ⟨h,t,resetBound,bodyBound,ready,_first,result⟩:=row_body k a B R S z n r g W M p q source _ _ T E frame
    hr hs hg hw he ha positive arena mp (by intro hm;have be:=before hm;omega)
    (by intro i lo hi;exact src i (by have be:=before (by omega);omega) hi)
    eof reg left right fence endBlank alphaTag fit hH nodes used rem quota
  have spec:(do
      let (circuit,tail) ← decodeCircuitFull n (bitLength n) (SerializedBody.window source M W)
      if circuit.size ≤ g then some ((circuit.size,Pnp3.Models.Circuit.eval circuit (Pnp3.Core.vecOfNat n row)),tail) else none)=
      some ((circuit.size,b),tail):=by
    rw [parsed]
    change (if circuit.size ≤ g then some ((circuit.size,b),tail) else none)=_
    rw [if_pos cap]
  rw [spec] at result
  obtain ⟨used,usedBound,tailEq,callback⟩:=result
  have usedEq:W-tail.length=used:=by
    have len:=congrArg List.length tailEq
    have wl:(SerializedBody.window source M W).length=W:=List.length_ofFn
    rw [List.length_drop,wl] at len
    omega
  obtain ⟨v,vpos,vBound,handler⟩:=after_body k B R S z n r g W M p q row circuit.size used (W-used) 0 a tag (valueTag b) source T E frame
    rowBound positive arena mp before nextBefore (by intro i lo hi;exact src i (by omega) hi)
    eof reg left right fence endBlank alphaTag tableTag av tv fit hH
  rw [tag_terminal] at handler
  simp only [tag_test] at handler
  have compose (v) : (callerMachine k).run (h+t+v) c=(callerMachine k).run v
      ⟨evalState k (SerializedBody.done b),⟨H,hH⟩,
        fun i=>SerializedBody.image E F r n g W (S-min M S) circuit.size used (W-used) 0 i.val⟩:=by
    rw [UniformTM.run_add,callback]
  have total:=round_price R r (SerializedBody.delimiter F r n 12) h t v (by omega)
    (extent_price R S z n r q (by omega) arena) resetBound bodyBound vBound
  refine ⟨h,h+t+v,by omega,total,ready,?_,?_,?_⟩
  · rw [usedEq];exact usedBound
  · rw [usedEq];exact tailEq
  · rw [usedEq]
    by_cases mismatch:b≠decide (tag.val=1)
    · rw [if_pos mismatch] at handler ⊢
      rw [compose]
      exact handler
    · rw [if_neg mismatch] at handler ⊢
      by_cases last:row+1=2^n
      · rw [if_pos last] at handler ⊢
        rw [compose]
        exact handler
      · rw [if_neg last] at handler ⊢
        by_cases one:q=1
        · rw [if_pos one] at handler ⊢
          rw [compose]
          exact handler
        · rw [if_neg one] at handler ⊢
          obtain ⟨E',next,run⟩:=handler
          refine ⟨E',next,?_⟩
          rw [compose]
          exact run
end PhysicalCallerClosure
