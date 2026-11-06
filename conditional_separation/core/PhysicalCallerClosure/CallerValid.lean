import PhysicalCallerClosure.AllRows
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
  for (owner,leaves) in [(`PhysicalCallerClosure.AllRows,["Layout","iterate"]),
      (`PhysicalCallerClosure.RoundFrame,["Exterior"]),(`PhysicalCallerClosure.Compare,["flags"]),
      (`PhysicalCallerClosure.SourceInitialize,["anchorMode"]),
      (`PhysicalCallerClosure.CallerFinish,["first_endpoint","paid_before_endpoint"]),
      (`PhysicalCallerClosure.RoundCost,["all_price"]),(`PhysicalCallerClosure.CallerTarget,["rowImage"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing paid-row term {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong owner"
      logInfo m!"paid-row-open|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private theorem valid_caller (k B R S z n r g W M A Q : Nat) (source : Fin S → Bool) (T E : Nat → Option Bool)
    (layout:Layout B R S z n r g W M A Q source T) (rpos:1 ≤ R)
    (arena:S+z+n+3+Q < FixedRawLengthFence.fencePos R) (positive:0 < Q)
    (frame:Exterior T E S z n (FixedRawLengthFence.fencePos R) r M A Q (Pnp3.Core.vecOfNat n 0)
      (flags (anchorMode source M) (SerializedBody.sourceMode source A) false) (decide (A < S)) (decide (M < S)))
    (circuit : Pnp3.Models.Circuit n) (tail : List Bool)
    (parsed:decodeCircuitFull n (bitLength n) (SerializedBody.window source M W)=some (circuit,tail)) (cap:circuit.size ≤ g)
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
    let u:=W-tail.length
    let good (i : Nat):=padRead source (A+i)=Pnp3.Models.Circuit.eval circuit (Pnp3.Core.vecOfNat n i)
    ∃ t,t ≤ 1099511627776*(R+1)^8 ∧
      (∀ v,v ≤ t → ((callerMachine k).run v c).state≠(callerMachine k).accept) ∧
      (∀ v,v < t → ((callerMachine k).run v c).state≠(callerMachine k).reject ∧ ((callerMachine k).run v c).state≠rowsDone k) ∧
      u ≤ W ∧ tail=(SerializedBody.window source M W).drop u ∧
      (∃ starts:Fin (min (2^n) Q) → Nat,
        (∀ i,(∀ j,j < i.val → good j) → starts i < t ∧
          (callerMachine k).run (starts i) c=⟨evalState k (SerializedBody.entry (SerializedBody.sourceMode source M)),⟨H,hH⟩,
            fun h=>rowImage T S z n F r g W M A Q i.val source h.val⟩) ∧
        (∀ i j,i.val < j.val → (∀ q,q < j.val → good q) → starts i < starts j)) ∧
      ((2^n ≤ Q ∧ (∀ i,i < 2^n → good i) ∧
        (callerMachine k).run t c=⟨rowsDone k,⟨H,hH⟩,
          fun h=>callerImage T S z n F r g W M (max 1 (Q-2^n)) (Pnp3.Core.vecOfNat n 0) circuit.size u (W-u) 0 h.val⟩) ∨
       (∃ row,row < min (2^n) Q ∧ (∀ j,j < row → good j) ∧ ¬good row ∧
        (callerMachine k).run t c=⟨(callerMachine k).reject,⟨H,hH⟩,
          fun h=>callerImage T S z n F r g W M (max 1 (Q-row)) (Pnp3.Core.vecOfNat n row) circuit.size u (W-u) 0 h.val⟩) ∨
       (Q < 2^n ∧ (∀ j,j < Q → good j) ∧
        (callerMachine k).run t c=⟨(callerMachine k).reject,⟨H,hH⟩,
          fun h=>callerImage T S z n F r g W M 1 (Pnp3.Core.vecOfNat n Q) circuit.size u (W-u) 0 h.val⟩)) := by
  dsimp only
  let F:=FixedRawLengthFence.fencePos R
  let H:=S+z+n+3
  let c : Config (callerMachine k).stateCount R B:=
    ⟨oldState k (BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode source M))),⟨H,hH⟩,
      fun i=>SerializedBody.prepared T S M F r n g W i.val⟩
  let start : Config (callerMachine k).stateCount R B:=⟨resetEntry k (anchorMode source M),⟨H,hH⟩,
    fun i=>SerializedBody.image E F r n g W (S-min M S) 0 0 W g i.val⟩
  let good (i : Nat):=padRead source (A+i)=Pnp3.Models.Circuit.eval circuit (Pnp3.Core.vecOfNat n i)
  obtain ⟨ub,tailEq,elapsed,localStarts,price,paid,order,ending⟩:=iterate k B R S z n r g W M A Q source T layout circuit tail parsed cap
    Q 0 0 0 W g E (by omega) positive (Nat.pow_pos (by decide)) frame
  have transport (v) : (callerMachine k).run (initial+v) c=(callerMachine k).run v start:=by
    rw [UniformTM.run_add,initialEnd]
  let d:=(callerMachine k).run (initial+elapsed) c
  have finish:d.state=(callerMachine k).reject ∨ d.state=rowsDone k:=by
    change ((callerMachine k).run (initial+elapsed) c).state=(callerMachine k).reject ∨
      ((callerMachine k).run (initial+elapsed) c).state=rowsDone k
    rw [transport]
    rcases ending with ⟨_enough,_good,eq⟩|⟨row,_lower,_upper,_prior,_wrong,eq⟩|⟨_few,_prior,eq⟩
    · rw [eq];exact Or.inr rfl
    · rw [eq];exact Or.inl rfl
    · rw [eq];exact Or.inl rfl
  obtain ⟨t,bound,firstEq,first,safe,work⟩:=first_endpoint c d rfl finish
  have endEq:(callerMachine k).run t c=(callerMachine k).run elapsed start:=firstEq.trans (transport elapsed)
  have qbound:Q ≤ 3*R+2:=by change S+z+n+3+Q < 3*R+2 at arena;omega
  have totalBound:=all_price R Q Q elapsed initial rpos qbound le_rfl price initialBound
  let starts (i:Fin (min (2^n) Q)):=initial+localStarts i.val
  have paidAll (i:Fin (min (2^n) Q)) (prior:∀ j,j < i.val → good j) :
      (callerMachine k).run (starts i) c=
        ⟨evalState k (SerializedBody.entry (SerializedBody.sourceMode source M)),⟨H,hH⟩,
          fun h=>rowImage T S z n F r g W M A Q i.val source h.val⟩:=by
    rw [transport]
    exact (paid i.val (by omega) i.isLt (by intro j _lo hi;exact prior j hi)).2
  refine ⟨t,by omega,safe,first,ub,tailEq,?_,?_⟩
  · refine ⟨starts,?_,?_⟩
    · intro i prior
      have run:=paidAll i prior
      exact ⟨paid_before_endpoint c work _ _ _ run,run⟩
    · intro i j lt prior
      exact Nat.add_lt_add_left (order i.val j.val (by omega) lt j.isLt (by intro q _lo hi;exact prior q hi)) initial
  · rcases ending with ⟨enough,goodRows,eq⟩|⟨row,_lower,upper,prior,wrong,eq⟩|⟨few,prior,eq⟩
    · refine Or.inl ⟨enough,?_,endEq.trans eq⟩
      intro i hi;exact goodRows i (by omega) hi
    · refine Or.inr (Or.inl ⟨row,upper,?_,wrong,endEq.trans eq⟩)
      intro j hi;exact prior j (by omega) hi
    · refine Or.inr (Or.inr ⟨few,?_,endEq.trans eq⟩)
      intro j hi;exact prior j (by omega) hi
end PhysicalCallerClosure
