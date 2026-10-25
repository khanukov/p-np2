import PhysicalCallerClosure.RowRound
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
private theorem failure_round (k B R S z n r g W M A Q : Nat) (a tag : Fin 3)
    (source : Fin S → Bool) (T E : Nat → Option Bool)
    (frame:Exterior T E S z n (FixedRawLengthFence.fencePos R) r M A Q (Pnp3.Core.vecOfNat n 0)
      (flags a tag false) (decide (A < S)) (decide (M < S)))
    (failed:(do
      let (circuit,tail) ← decodeCircuitFull n (bitLength n) (SerializedBody.window source M W)
      if circuit.size ≤ g then some ((circuit.size,Pnp3.Models.Circuit.eval circuit (Pnp3.Core.vecOfNat n 0)),tail) else none)=none)
    (hr:r ≤ S) (hs:S ≤ R) (hg:g ≤ r) (hw:W ≤ r) (he:bitLength n ≤ r) (ha:S-min M S ≤ r)
    (margin:A+2^n+1 ≤ M) (aPos:2 ≤ A) (positive:0 < Q)
    (arena:S+z+n+3+Q < FixedRawLengthFence.fencePos R)
    (src:∀ i,A ≤ i → ∀ hi:i < S,T i=some (source ⟨i,hi⟩))
    (eof:T S=none) (reg:∀ i,S < i → i < S+z+2 → T i=some false)
    (left:T (S+z+2)=none) (right:T (S+z+n+3)=none) (fence:T (FixedRawLengthFence.fencePos R)=some false)
    (endBlank:T (SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12+6)=none)
    (alphaTag:a.val=2 ↔ S ≤ M) (tableTag:tag.val=2 ↔ S ≤ A)
    (av:M < S → T (M-1)=some (decide (a.val=1))) (tv:A < S → T A=some (decide (tag.val=1)))
    (fit:SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12+6 < tapeLength R B)
    (hH:S+z+n+3 < tapeLength R B) :
    let F:=FixedRawLengthFence.fencePos R
    let c : Config (callerMachine k).stateCount R B:=⟨resetEntry k a,⟨S+z+n+3,hH⟩,
      fun i=>SerializedBody.image E F r n g W (S-min M S) 0 0 W g i.val⟩
    ∃ elapsed,elapsed ≤ 2147483648*(R+1)^6 ∧
      (callerMachine k).run elapsed c=⟨(callerMachine k).reject,⟨S+z+n+3,hH⟩,
        fun i=>callerImage T S z n F r g W M Q (Pnp3.Core.vecOfNat n 0) 0 0 0 0 i.val⟩ := by
  dsimp only
  let F:=FixedRawLengthFence.fencePos R
  let c : Config (callerMachine k).stateCount R B:=⟨resetEntry k a,⟨S+z+n+3,hH⟩,
    fun i=>SerializedBody.image E F r n g W (S-min M S) 0 0 W g i.val⟩
  have power:0 < 2^n:=Nat.pow_pos (by decide)
  obtain ⟨h,t,resetBound,bodyBound,_ready,_first,result⟩:=row_body k a B R S z n r g W M A Q source _ _ T E frame
    hr hs hg hw he ha positive arena (by omega) (by intro _;omega)
    (by intro i lo hi;exact src i (by omega) hi)
    eof reg left right fence endBlank alphaTag fit hH 0 0 W g
  rw [failed] at result
  obtain ⟨v,_vpos,vBound,handler⟩:=after_body k B R S z n r g W M A Q 0 0 0 0 0 a tag ⟨2,by decide⟩ source T E frame
    power positive arena (by omega) (by intro _;omega) (by intro h _;omega)
    (by intro i lo hi;exact src i (by omega) hi) eof reg left right fence endBlank alphaTag tableTag av tv fit hH
  have bad:(⟨2,by decide⟩:Fin 3).val=2 ∨ decide ((⟨2,by decide⟩:Fin 3).val=1)≠decide (tag.val=1):=Or.inl rfl
  rw [if_pos bad] at handler
  have terminalEq:terminal ⟨2,by decide⟩=SerializedBody.machine.reject:=rfl
  rw [terminalEq] at handler
  have total:=round_price R r (SerializedBody.delimiter F r n 12) h t v (by omega)
    (extent_price R S z n r Q (by omega) arena) resetBound bodyBound vBound
  refine ⟨h+t+v,total,?_⟩
  rw [UniformTM.run_add,result]
  exact handler
end PhysicalCallerClosure
