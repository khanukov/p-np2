import PhysicalCallerClosure.AllRows
import PhysicalCallerClosure.RowFailure
import PhysicalCallerClosure.CallerFinish
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
  for (owner,leaves) in [(`PhysicalCallerClosure.AllRows,["Layout"]),(`PhysicalCallerClosure.RoundFrame,["Exterior"]),
      (`PhysicalCallerClosure.Compare,["flags"]),(`PhysicalCallerClosure.SourceInitialize,["anchorMode"]),
      (`PhysicalCallerClosure.RowSource,["mode_virtual","mode_value","source_cell"]),
      (`PhysicalCallerClosure.RowFailure,["failure_round"]),(`PhysicalCallerClosure.CallerFinish,["first_endpoint"]),
      (`PhysicalCallerClosure.LoopTimes,["one_price"]),(`PhysicalCallerClosure.RoundCost,["all_price"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing paid-row term {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong owner"
      logInfo m!"paid-row-open|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private theorem invalid_caller (k B R S z n r g W M A Q : Nat) (source : Fin S → Bool) (T E : Nat → Option Bool)
    (layout:Layout B R S z n r g W M A Q source T)
    (frame:Exterior T E S z n (FixedRawLengthFence.fencePos R) r M A Q (Pnp3.Core.vecOfNat n 0)
      (flags (anchorMode source M) (SerializedBody.sourceMode source A) false) (decide (A < S)) (decide (M < S)))
    (failed:(do
      let (circuit,tail) ← decodeCircuitFull n (bitLength n) (SerializedBody.window source M W)
      if circuit.size ≤ g then some ((circuit.size,Pnp3.Models.Circuit.eval circuit (Pnp3.Core.vecOfNat n 0)),tail) else none)=none)
    (hH:S+z+n+3 < tapeLength R B) (initial : Nat) (initialBound:initial ≤ 4096*(R+1)^2)
    (initialEnd:(callerMachine k).run initial
      ⟨oldState k (BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode source M))),⟨S+z+n+3,hH⟩,
        fun i=>SerializedBody.prepared T S M (FixedRawLengthFence.fencePos R) r n g W i.val⟩=
      ⟨resetEntry k (anchorMode source M),⟨S+z+n+3,hH⟩,
        fun i=>SerializedBody.image E (FixedRawLengthFence.fencePos R) r n g W (S-min M S) 0 0 W g i.val⟩) :
    let F:=FixedRawLengthFence.fencePos R
    let H:=S+z+n+3
    let c : Config (callerMachine k).stateCount R B:=
      ⟨oldState k (BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode source M))),⟨H,hH⟩,
        fun i=>SerializedBody.prepared T S M F r n g W i.val⟩
    ∃ t,t ≤ 1099511627776*(R+1)^8 ∧
      (∀ v,v ≤ t → ((callerMachine k).run v c).state≠(callerMachine k).accept) ∧
      (∀ v,v < t → ((callerMachine k).run v c).state≠(callerMachine k).reject ∧ ((callerMachine k).run v c).state≠rowsDone k) ∧
      (callerMachine k).run t c=⟨(callerMachine k).reject,⟨H,hH⟩,
        fun i=>callerImage T S z n F r g W M Q (Pnp3.Core.vecOfNat n 0) 0 0 0 0 i.val⟩ := by
  dsimp only
  let F:=FixedRawLengthFence.fencePos R
  let H:=S+z+n+3
  let c : Config (callerMachine k).stateCount R B:=
    ⟨oldState k (BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode source M))),⟨H,hH⟩,
      fun i=>SerializedBody.prepared T S M F r n g W i.val⟩
  rcases layout with ⟨Rpos,rS,sR,gates,_wp,windowRoom,widthRoom,anchorRoom,aPos,_aS,margin,positive,arena,
    _gamma,_marker,src,eof,reg,left,right,_beta,_marks,_gap,fence,metadata,fit,_room⟩
  have power:0 < 2^n:=Nat.pow_pos (by decide)
  have aTag:(anchorMode source M).val=2 ↔ S ≤ M:=by
    unfold anchorMode
    by_cases hm:M < S
    · rw [if_pos hm,mode_virtual];omega
    · rw [if_neg hm];change 2=2 ↔ S ≤ M;omega
  have av:M < S → T (M-1)=some (decide ((anchorMode source M).val=1)):=by
    intro hm
    unfold anchorMode
    rw [if_pos hm]
    exact source_cell source T A (M-1) src (by omega) (by omega)
  have endBlank:T (SerializedBody.delimiter F r n 12+6)=none:=metadata
    (SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12+6) (by omega) le_rfl
  obtain ⟨elapsed,price,endEq⟩:=failure_round k B R S z n r g W M A Q (anchorMode source M)
    (SerializedBody.sourceMode source A) source T E frame failed rS sR gates windowRoom widthRoom anchorRoom margin aPos
    positive arena src eof reg left right fence endBlank aTag (mode_virtual source A) av
    (source_cell source T A A src le_rfl) fit hH
  have actual:(callerMachine k).run (initial+elapsed) c=
      ⟨(callerMachine k).reject,⟨H,hH⟩,
        fun i=>callerImage T S z n F r g W M Q (Pnp3.Core.vecOfNat n 0) 0 0 0 0 i.val⟩:=by
    rw [UniformTM.run_add,initialEnd,endEq]
  have loopBound:elapsed ≤ Q*(2147483648*(R+1)^6):=by
    have le:=one_price (Q-1) elapsed (2147483648*(R+1)^6) price
    simpa only [show Q-1+1=Q by omega] using le
  have qbound:Q ≤ 3*R+2:=by change S+z+n+3+Q < 3*R+2 at arena;omega
  have totalBound:=all_price R Q Q elapsed initial Rpos qbound le_rfl loopBound initialBound
  obtain ⟨t,bound,eq,first,safe,_work⟩:=first_endpoint c _ actual (Or.inl rfl)
  exact ⟨t,by omega,safe,first,eq⟩
end PhysicalCallerClosure
