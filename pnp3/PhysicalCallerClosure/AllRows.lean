import PhysicalCallerClosure.LoopTimes
import PhysicalCallerClosure.RowRound
import PhysicalCallerClosure.RowEntry
import PhysicalCallerClosure.RowSource
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
  for (owner,leaves) in [(`PhysicalCallerClosure.RoundFrame,["Exterior"]),(`PhysicalCallerClosure.Compare,["flags"]),
      (`PhysicalCallerClosure.RowRound,["valid_round"]),(`PhysicalCallerClosure.RowEntry,["entry_image"]),
      (`PhysicalCallerClosure.RowSource,["mode_virtual","mode_value","anchor_virtual","anchor_value","source_cell"]),
      (`PhysicalCallerClosure.SourceInitialize,["anchorMode"]),(`PhysicalCallerClosure.CallerTarget,["rowImage"]),(`PhysicalCallerClosure.LoopTimes,["one_price","join_price","prepend_starts"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing paid-row term {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong owner"
      logInfo m!"paid-row-open|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
-- Static physical premises only; no run, evaluation, successful parse or future-result field.
private structure Layout (B R S z n r g W M A Q : Nat) (source : Fin S → Bool) (T : Nat → Option Bool) : Prop where
  rpos : 1 ≤ R
  rS : r ≤ S
  sR : S ≤ R
  gates : g ≤ r
  windowPositive : 0 < W
  windowRoom : W ≤ r
  widthRoom : bitLength n ≤ r
  anchorRoom : S-min M S ≤ r
  tablePositive : 2 ≤ A
  tableStart : A ≤ S
  margin : A+2^n+1 ≤ M
  paid : 0 < Q
  arena : S+z+n+3+Q < FixedRawLengthFence.fencePos R
  gammaHole : T (A-2)=none
  gammaMarker : T (A-1)=some true
  sourceCells : ∀ i,A ≤ i → ∀ hi:i < S,T i=some (source ⟨i,hi⟩)
  eof : T S=none
  registers : ∀ i,S < i → i < S+z+2 → T i=some false
  left : T (S+z+2)=none
  right : T (S+z+n+3)=none
  zeroAssignment : ∀ j:Fin n,T (S+z+n+2-j.val)=some false
  marks : ∀ i,S+z+n+3 < i → i ≤ S+z+n+3+Q → T i=some true
  gap : ∀ i,S+z+n+3+Q < i → i < FixedRawLengthFence.fencePos R → T i=none
  fence : T (FixedRawLengthFence.fencePos R)=some false
  metadataEmpty : ∀ i,SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12 < i →
    i ≤ SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12+6 → T i=none
  fit : SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12+6 < tapeLength R B
  headRoom : S+z+n+3 < tapeLength R B
private theorem run_row (k B R S z n r g W M A Q : Nat) (source : Fin S → Bool) (T : Nat → Option Bool)
    (layout:Layout B R S z n r g W M A Q source T) (circuit : Pnp3.Models.Circuit n) (tail : List Bool)
    (parsed:decodeCircuitFull n (bitLength n) (SerializedBody.window source M W)=some (circuit,tail)) (cap:circuit.size ≤ g)
    (q row nodes used rem quota : Nat) (E : Nat → Option Bool) (qEq:q=Q-row) (positive:0 < q) (rowBound:row < 2^n)
    (frame:Exterior T E S z n (FixedRawLengthFence.fencePos R) r M (A+row) q (Pnp3.Core.vecOfNat n row)
      (flags (anchorMode source M) (SerializedBody.sourceMode source (A+row)) false)
      (decide (A+row < S)) (decide (M < S))) :
    let F:=FixedRawLengthFence.fencePos R
    let u:=W-tail.length
    let a:=anchorMode source M
    let tag:=SerializedBody.sourceMode source (A+row)
    let c : Config (callerMachine k).stateCount R B:=⟨resetEntry k a,⟨S+z+n+3,layout.headRoom⟩,
      fun i=>SerializedBody.image E F r n g W (S-min M S) nodes used rem quota i.val⟩
    ∃ ready elapsed,ready < elapsed ∧ elapsed ≤ 2147483648*(R+1)^6 ∧
      (callerMachine k).run ready c=⟨evalState k (SerializedBody.entry (SerializedBody.sourceMode source M)),
        ⟨S+z+n+3,layout.headRoom⟩,fun i=>rowImage T S z n F r g W M A Q row source i.val⟩ ∧
      u ≤ W ∧ tail=(SerializedBody.window source M W).drop u ∧
      if Pnp3.Models.Circuit.eval circuit (Pnp3.Core.vecOfNat n row)≠decide (tag.val=1) then
        (callerMachine k).run elapsed c=⟨(callerMachine k).reject,⟨S+z+n+3,layout.headRoom⟩,
          fun i=>callerImage T S z n F r g W M q (Pnp3.Core.vecOfNat n row) circuit.size u (W-u) 0 i.val⟩
      else if row+1=2^n then
        (callerMachine k).run elapsed c=⟨rowsDone k,⟨S+z+n+3,layout.headRoom⟩,
          fun i=>callerImage T S z n F r g W M (max 1 (q-1)) (Pnp3.Core.vecOfNat n ((row+1)%(2^n))) circuit.size u (W-u) 0 i.val⟩
      else if q=1 then
        (callerMachine k).run elapsed c=⟨(callerMachine k).reject,⟨S+z+n+3,layout.headRoom⟩,
          fun i=>callerImage T S z n F r g W M 1 (Pnp3.Core.vecOfNat n ((row+1)%(2^n))) circuit.size u (W-u) 0 i.val⟩
      else ∃ E',Exterior T E' S z n F r M ((A+row)+1) (q-1)
        (Pnp3.Core.vecOfNat n (row+1)) (flags a (SerializedBody.sourceMode source ((A+row)+1)) false)
        (decide ((A+row)+1 < S)) (decide (M < S)) ∧
        (callerMachine k).run elapsed c=⟨resetEntry k a,⟨S+z+n+3,layout.headRoom⟩,
          fun i=>SerializedBody.image E' F r n g W (S-min M S) circuit.size u (W-u) 0 i.val⟩ := by
  dsimp only
  let F:=FixedRawLengthFence.fencePos R
  have rowQ:row < Q:=by omega
  have margin:=layout.margin
  have boundA:=layout.tablePositive
  have pBefore:M < S → A+row < M-1:=by intro _;omega
  have nextBefore:row+1 < 2^n → M < S → A+row+1 < M-1:=by intro h _;omega
  have aTag:(anchorMode source M).val=2 ↔ S ≤ M:=by
    unfold anchorMode
    by_cases hm:M < S
    · rw [if_pos hm,mode_virtual];omega
    · rw [if_neg hm];change 2=2 ↔ S ≤ M;omega
  have aBit:decide ((anchorMode source M).val=1)=(if M < S then padRead source (M-1) else false):=by
    unfold anchorMode
    by_cases hm:M < S
    · rw [if_pos hm,if_pos hm,mode_value]
    · rw [if_neg hm,if_neg hm];rfl
  have av:M < S → T (M-1)=some (decide ((anchorMode source M).val=1)):=by
    intro hm
    rw [aBit,if_pos hm]
    unfold padRead
    rw [dif_pos (show M-1 < S by omega)]
    exact layout.sourceCells _ (by omega) (by omega)
  have arena:S+z+n+3+(q) < F:=by have a:=layout.arena;omega
  have endBlank:T (SerializedBody.delimiter F r n 12+6)=none:=layout.metadataEmpty (SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12+6) (by omega) le_rfl
  obtain ⟨ready,e,readyBefore,price,entry,usedBound,tailEq,step⟩:=valid_round k B R S z n r g W M (A+row) (q) row nodes used rem quota
    (anchorMode source M) (SerializedBody.sourceMode source (A+row)) source T E circuit tail parsed cap frame
    layout.rS layout.sR layout.gates layout.windowRoom layout.widthRoom layout.anchorRoom rowBound positive arena
    (by omega) pBefore nextBefore (by intro i lo hi;exact layout.sourceCells i (by omega) hi)
    layout.eof layout.registers layout.left layout.right layout.fence endBlank aTag (mode_virtual source (A+row)) av
    (source_cell source T A (A+row) layout.sourceCells (by omega)) layout.fit layout.headRoom
  have maxEq:max 1 (Q-row)=q:=by omega
  have canonical:=entry_image T E S z n F r g W M A Q row source (anchorMode source M)
    (SerializedBody.sourceMode source (A+row)) (by omega) (by rwa [maxEq]) aTag (mode_virtual source (A+row)) aBit (mode_value source (A+row))
  rw [canonical] at entry
  exact ⟨ready,e,readyBefore,price,entry,usedBound,tailEq,step⟩
private theorem iterate (k B R S z n r g W M A Q : Nat) (source : Fin S → Bool) (T : Nat → Option Bool)
    (layout:Layout B R S z n r g W M A Q source T) (circuit : Pnp3.Models.Circuit n) (tail : List Bool)
    (parsed:decodeCircuitFull n (bitLength n) (SerializedBody.window source M W)=some (circuit,tail)) (cap:circuit.size ≤ g) :
    ∀ (q row nodes used rem quota : Nat) (E : Nat → Option Bool),q=Q-row → 0 < q → row < 2^n →
    Exterior T E S z n (FixedRawLengthFence.fencePos R) r M (A+row) q (Pnp3.Core.vecOfNat n row)
      (flags (anchorMode source M) (SerializedBody.sourceMode source (A+row)) false)
      (decide (A+row < S)) (decide (M < S)) →
    let F:=FixedRawLengthFence.fencePos R
    let H:=S+z+n+3
    let c : Config (callerMachine k).stateCount R B:=⟨resetEntry k (anchorMode source M),⟨H,layout.headRoom⟩,
      fun i=>SerializedBody.image E F r n g W (S-min M S) nodes used rem quota i.val⟩
    let good (i : Nat):=padRead source (A+i)=Pnp3.Models.Circuit.eval circuit (Pnp3.Core.vecOfNat n i)
    let u:=W-tail.length
    u ≤ W ∧ tail=(SerializedBody.window source M W).drop u ∧
    ∃ (elapsed : Nat) (starts : Nat → Nat),elapsed ≤ q*(2147483648*(R+1)^6) ∧
      (∀ i,row ≤ i → i < min (2^n) Q → (∀ j,row ≤ j → j < i → good j) →
        starts i < elapsed ∧ (callerMachine k).run (starts i) c=
          ⟨evalState k (SerializedBody.entry (SerializedBody.sourceMode source M)),⟨H,layout.headRoom⟩,
            fun h=>rowImage T S z n F r g W M A Q i source h.val⟩) ∧
      (∀ i j,row ≤ i → i < j → j < min (2^n) Q → (∀ v,row ≤ v → v < j → good v) → starts i < starts j) ∧
      ((2^n ≤ Q ∧ (∀ j,row ≤ j → j < 2^n → good j) ∧
        (callerMachine k).run elapsed c=⟨rowsDone k,⟨H,layout.headRoom⟩,
          fun h=>callerImage T S z n F r g W M (max 1 (Q-2^n)) (Pnp3.Core.vecOfNat n 0) circuit.size u (W-u) 0 h.val⟩) ∨
       (∃ badRow,row ≤ badRow ∧ badRow < min (2^n) Q ∧ (∀ j,row ≤ j → j < badRow → good j) ∧ ¬good badRow ∧
        (callerMachine k).run elapsed c=⟨(callerMachine k).reject,⟨H,layout.headRoom⟩,
          fun h=>callerImage T S z n F r g W M (max 1 (Q-badRow)) (Pnp3.Core.vecOfNat n badRow) circuit.size u (W-u) 0 h.val⟩) ∨
       (Q < 2^n ∧ (∀ j,row ≤ j → j < Q → good j) ∧
        (callerMachine k).run elapsed c=⟨(callerMachine k).reject,⟨H,layout.headRoom⟩,
          fun h=>callerImage T S z n F r g W M 1 (Pnp3.Core.vecOfNat n Q) circuit.size u (W-u) 0 h.val⟩)) := by
  intro q
  induction q with
  | zero => intro row nodes used rem quota E _qEq positive;omega
  | succ q ih =>
    intro row nodes used rem quota E qEq positive rowBound frame
    dsimp only
    let F:=FixedRawLengthFence.fencePos R
    let H:=S+z+n+3
    let c : Config (callerMachine k).stateCount R B:=⟨resetEntry k (anchorMode source M),⟨H,layout.headRoom⟩,
      fun i=>SerializedBody.image E F r n g W (S-min M S) nodes used rem quota i.val⟩
    let good (i : Nat):=padRead source (A+i)=Pnp3.Models.Circuit.eval circuit (Pnp3.Core.vecOfNat n i)
    have rowQ:row < Q:=by omega
    obtain ⟨ready,e,readyBefore,price,entry,usedBound,tailEq,step⟩:=run_row k B R S z n r g W M A Q source T layout circuit tail parsed cap
      (q+1) row nodes used rem quota E qEq positive rowBound frame
    have maxEq:max 1 (Q-row)=q+1:=by omega
    have startEq: (callerMachine k).run ready c=
        ⟨evalState k (SerializedBody.entry (SerializedBody.sourceMode source M)),⟨H,layout.headRoom⟩,
          fun h=>rowImage T S z n F r g W M A Q row source h.val⟩:=entry
    have payCount:q*(2147483648*(R+1)^6)+(2147483648*(R+1)^6)=(q+1)*(2147483648*(R+1)^6):=by ring
    -- Remaining proof is the actual paid recursion over q, not over the possibly huge 2^n.
    by_cases bad:¬good row
    · have mismatch:Pnp3.Models.Circuit.eval circuit (Pnp3.Core.vecOfNat n row)≠decide ((SerializedBody.sourceMode source (A+row)).val=1):=by
        rw [mode_value]
        exact Ne.symm bad
      rw [if_pos mismatch] at step
      refine ⟨usedBound,tailEq,e,(fun _=>ready),?_,?_,?_,Or.inr (Or.inl ?_)⟩
      · exact one_price q e (2147483648*(R+1)^6) price
      · intro i lo hi prefixGood
        have eq:i=row:=by
          by_contra ne
          exact bad (prefixGood row le_rfl (by omega))
        subst i
        exact ⟨readyBefore,startEq⟩
      · intro i j lo lt _hi prefixGood
        exact False.elim (bad (prefixGood row le_rfl (by omega)))
      · refine ⟨row,le_rfl,by omega,?_,bad,?_⟩
        · intro j lo hi;omega
        · rw [maxEq];exact step
    · have current:good row:=of_not_not bad
      have agrees:¬Pnp3.Models.Circuit.eval circuit (Pnp3.Core.vecOfNat n row)≠decide ((SerializedBody.sourceMode source (A+row)).val=1):=by
        rw [mode_value]
        exact not_not.mpr current.symm
      rw [if_neg agrees] at step
      by_cases last:row+1=2^n
      · rw [if_pos last] at step
        have stop:∀ i,row ≤ i → i < min (2^n) Q → i=row:=by intro i lo hi;omega
        refine ⟨usedBound,tailEq,e,(fun _=>ready),?_,?_,?_,Or.inl ?_⟩
        · exact one_price q e (2147483648*(R+1)^6) price
        · intro i lo hi _prefix;have eq:=stop i lo hi;subst i;exact ⟨readyBefore,startEq⟩
        · intro i j lo lt hi _prefix;have eq:=stop j (by omega) hi;omega
        · refine ⟨by omega,?_,?_⟩
          · intro j lo hi
            have eq:j=row:=by omega
            subst j
            exact current
          · have count:max 1 ((q+1)-1)=max 1 (Q-2^n):=by omega
            rw [last,Nat.mod_self,count] at step
            exact step
      · rw [if_neg last] at step
        have rowNext:row+1 < 2^n:=by omega
        by_cases zero:q=0
        · subst q
          rw [if_pos (show 0+1=1 by rfl)] at step
          have qIs:Q=row+1:=by omega
          have stop:∀ i,row ≤ i → i < min (2^n) Q → i=row:=by intro i lo hi;omega
          refine ⟨usedBound,tailEq,e,(fun _=>ready),?_,?_,?_,Or.inr (Or.inr ?_)⟩
          · simpa using price
          · intro i lo hi _prefix;have eq:=stop i lo hi;subst i;exact ⟨readyBefore,startEq⟩
          · intro i j lo lt hi _prefix;have eq:=stop j (by omega) hi;omega
          · refine ⟨by omega,?_,?_⟩
            · intro j lo hi
              have eq:j=row:=by omega
              subst j
              exact current
            · rw [Nat.mod_eq_of_lt rowNext,←qIs] at step
              exact step
        · rw [if_neg (show ¬q+1=1 by omega)] at step
          obtain ⟨E',nextFrame,nextRun⟩:=step
          have qnext:q=Q-(row+1):=by omega
          have posq:0 < q:=by omega
          have pEq:A+row+1=A+(row+1):=by omega
          have subEq:q+1-1=q:=by omega
          rw [pEq,subEq] at nextFrame
          obtain ⟨usedBound',tailEq',endTime,restStarts,restPrice,restPaid,restOrder,restEnd⟩:=ih (row+1)
            circuit.size (W-tail.length) (W-(W-tail.length)) 0 E' qnext posq rowNext nextFrame
          have transport (v) : (callerMachine k).run (e+v) c=(callerMachine k).run v
              ⟨resetEntry k (anchorMode source M),⟨H,layout.headRoom⟩,
                fun i=>SerializedBody.image E' F r n g W (S-min M S) circuit.size (W-tail.length) (W-(W-tail.length)) 0 i.val⟩:=by
            rw [UniformTM.run_add,nextRun]
          obtain ⟨starts,paidAll,orderAll⟩:=prepend_starts c
            ⟨resetEntry k (anchorMode source M),⟨H,layout.headRoom⟩,
              fun i=>SerializedBody.image E' F r n g W (S-min M S) circuit.size (W-tail.length) (W-(W-tail.length)) 0 i.val⟩
            (fun i=>⟨evalState k (SerializedBody.entry (SerializedBody.sourceMode source M)),⟨H,layout.headRoom⟩,
              fun h=>rowImage T S z n F r g W M A Q i source h.val⟩)
            good row (min (2^n) Q) ready e endTime restStarts nextRun startEq readyBefore restPaid restOrder
          refine ⟨usedBound',tailEq',e+endTime,starts,join_price q e endTime (2147483648*(R+1)^6) price restPrice,paidAll,orderAll,?_⟩
          rcases restEnd with done|mismatch|shortage
          · rcases done with ⟨enough,prior,finish⟩
            refine Or.inl ⟨enough,?_,?_⟩
            · intro j lo hi
              by_cases eq:j=row
              · subst j;exact current
              · exact prior j (by omega) hi
            · rw [transport];exact finish
          · rcases mismatch with ⟨badRow,lower,upper,prior,wrong,finish⟩
            refine Or.inr (Or.inl ⟨badRow,by omega,upper,?_,wrong,?_⟩)
            · intro j lo hi
              by_cases eq:j=row
              · subst j;exact current
              · exact prior j (by omega) hi
            · rw [transport];exact finish
          · rcases shortage with ⟨few,prior,finish⟩
            refine Or.inr (Or.inr ⟨few,?_,?_⟩)
            · intro j lo hi
              by_cases eq:j=row
              · subst j;exact current
              · exact prior j (by omega) hi
            · rw [transport];exact finish
end PhysicalCallerClosure
