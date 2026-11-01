import NormalFinalClosure.Target2
import NormalFinalClosure.Prefix2
import NormalFinalClosure.Consequences
import NormalFinalClosure.PrefixSemantics
import NormalFinalClosure.RowsDone
import NormalFinalClosure.RawFrameN2
import NormalFinalClosure.GuardExecution2
import NormalFinalClosure.RawComposition2
import NormalFinalClosure.Arithmetic
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for leaf in ["liftOld","oldM"] do
    let n:=Name.str (Name.str (Name.num `_private.NormalFinalClosure.Machine 0) "NormalFinalClosure") leaf
    let some (.defnInfo ci):=e.find? n | throwError "Missing exact original finite inclusion"
    let some i:=e.getModuleIdxFor? n | throwError "Missing inclusion owner"
    unless i.toNat < e.header.moduleNames.size && e.header.moduleNames[i]! == `NormalFinalClosure.Machine do throwError "Wrong inclusion owner"
    logInfo m!"raw-final-inclusion|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private theorem old_value (k : Nat) (q : Fin (RawCallerClosure.machine k).stateCount) : (old2 k q).val=q.val := by
  dsimp only [old2,old,liftOld,oldM]
private theorem old_injective (k : Nat) : Function.Injective (old2 k) := by
  intro q s eq
  have vals:=congrArg (fun t : Fin (machine2 k).stateCount=>t.val) eq
  change (old2 k q).val=(old2 k s).val at vals
  rw [old_value,old_value] at vals
  exact Fin.ext vals
private theorem accept_map (k : Nat) : old2 k (RawCallerClosure.machine k).accept=(machine2 k).accept := rfl
private theorem reject_map (k : Nat) : old2 k (RawCallerClosure.machine k).reject=(machine2 k).reject := rfl
private theorem prefix_price (k N : Nat) : RawCallerClosure.deadline k N ≤ 17592186044416*(k+1)*(N+1)^8 := by
  change 4398046511104*(k+1)*(N+1)^8 ≤ 17592186044416*(k+1)*(N+1)^8
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
private theorem inherited_raw_reject : ∀ k,
    RawCallerClosure.old k (CertificateGuardClosure.machine k).reject=(RawCallerClosure.machine k).reject := by
  run_tac do
    let e←getEnv
    let n:=Name.str (Name.str (Name.num `_private.RawCallerClosure.Rows 0) "RawCallerClosure") "old_reject"
    let some (.thmInfo ci):=e.find? n | throwError "Missing exact sealed reject inclusion"
    let some i:=e.getModuleIdxFor? n | throwError "Missing reject owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == `RawCallerClosure.Rows do throwError "Wrong reject owner"
    logInfo m!"raw-final-reject-inclusion|{n}|{ci.type}"
    closeMainGoal `inherited_raw_reject (mkConst n (ci.levelParams.map Level.param))
private theorem normalReject : ∀ (k B R a m z n r : Nat) (x : Bitstring a) (w : Bitstring m)
    (T : Nat → Option Bool) (hH:a+m+z+2+n+1 < tapeLength R B)
    (c : Config (RawCallerClosure.machine k).stateCount R B) (t : Nat),
    m=a+1 → contentHeader? (Fin.append x w)=some (n,2*z+1) →
    RawCallerClosure.Target.RowsResult k B R (a+m) z n r (n^k+k) (Cursor.Target.W k n)
      (Cursor.Target.M k n z) (9+2*z) (2^n) (Fin.append x w) T hH c t →
    ((RawCallerClosure.machine k).run t c).state=(RawCallerClosure.machine k).reject →
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=false := by
  run_tac do
    let owner:=`NormalFinalClosure.Consequences
    let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "NormalFinalClosure") "normal_reject_false"
    let e←getEnv
    let some (.thmInfo ci):=e.find? n | throwError "Missing exact normal reject theorem"
    let some i:=e.getModuleIdxFor? n | throwError "Missing reject theorem owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong normal reject theorem owner"
    logInfo m!"raw-final-normal-reject|{n}|{ci.type}"
    closeMainGoal `normalReject (mkConst n (ci.levelParams.map Level.param))
private theorem doneResult : ∀ (k B R S z n r g W M A : Nat) (source : Fin S → Bool)
    (T : Nat → Option Bool) (hH:S+z+2+n+1 < tapeLength R B)
    (c : Config (RawCallerClosure.machine k).stateCount R B) (t : Nat),
    RawCallerClosure.Target.RowsResult k B R S z n r g W M A (2^n) source T hH c t →
    ((RawCallerClosure.machine k).run t c).state≠(RawCallerClosure.machine k).reject →
    ∃ (circuit:Pnp3.Models.Circuit n) (tail:List Bool),
      decodeCircuitFull n (bitLength n) (SerializedBody.window source M W)=some (circuit,tail) ∧
      circuit.size ≤ g ∧ W-tail.length ≤ W ∧ tail=(SerializedBody.window source M W).drop (W-tail.length) ∧
      (∀ j,j < 2^n → padRead source (A+j)=circuit.eval (Pnp3.Core.vecOfNat n j)) ∧
      (RawCallerClosure.machine k).run t c=
        ⟨RawCallerClosure.callerState k (PhysicalCallerClosure.rowsDone k),⟨S+z+2+n+1,hH⟩,
          fun i=>PhysicalCallerClosure.callerImage T S z n (FixedRawLengthFence.fencePos R) r g W M 1
            (Pnp3.Core.vecOfNat n 0) circuit.size (W-tail.length) (W-(W-tail.length)) 0 i.val⟩ := by
  run_tac do
    let owner:=`NormalFinalClosure.RowsDone
    let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "NormalFinalClosure") "rows_done"
    let e←getEnv
    let some (.thmInfo ci):=e.find? n | throwError "Missing exact SAME endpoint inversion"
    let some i:=e.getModuleIdxFor? n | throwError "Missing SAME endpoint owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong SAME endpoint owner"
    logInfo m!"raw-final-SAME-rowsDone|{n}|{ci.type}"
    closeMainGoal `doneResult (mkConst n (ci.levelParams.map Level.param))
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`NormalFinalClosure.RawFrameN2,`NormalFinalClosure,["normalImage","frame_at_N"]),
    (`NormalFinalClosure.RawComposition2,`NormalFinalClosure,["compose_guard","min_lt_implies","recovered_position","zero_bound"]),
    (`NormalFinalClosure.Arithmetic,`NormalFinalClosure,["guard_price","delimiter_bound"]),
    (`NormalFinalClosure.Frame2,`NormalFinalClosure,["D","PrefixAt","GuardFrame"]),
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["Safe2"]),
    (`NormalFinalClosure.Activation2,`NormalFinalClosure,["oldNotDone"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing connected original raw FINAL API"
      let some i:=e.getModuleIdxFor? name | throwError "Missing original raw FINAL owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong original raw FINAL owner"
      logInfo m!"connected-original-raw-FINAL-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) name::st.openDecls}
private theorem raw_room (k N P : Nat) (bound:P+1 ≤ 64*(N+1)) :
    P < tapeLength N (RawCallerClosure.allocation k N) := by
  have power:N+1 ≤ (N+1)^8:=by
    have h:=Nat.pow_le_pow_right (show 1 ≤ N+1 by omega) (show 1 ≤ 8 by decide)
    simpa only [pow_one] using h
  have factor:64 ≤ 1099511627776*(k+1):=by omega
  have fit:=Nat.mul_le_mul factor power
  change P < N+1099511627776*(k+1)*(N+1)^8+1
  omega
private theorem safe_not_old (k : Nat) (q : Fin (RawCallerClosure.machine k).stateCount)
    (s : Fin (machine2 k).stateCount) (safe:Safe2 k s) : s≠old2 k q := by
  intro eq
  have value:=congrArg (fun t:Fin (machine2 k).stateCount=>t.val) eq
  change s.val=(old2 k q).val at value
  rw [old_value] at value
  change (RawCallerClosure.machine k).stateCount ≤ s.val at safe
  have bound:=q.isLt
  omega
/-- Exact frozen full raw NORMAL FINAL target. Remaining goals are deliberately
ordinary OPEN goals, never an assumed prepared normalizer/guard result. -/
theorem normal_raw (k : Nat) : Target2.Raw k := by
  intro N y B O C oldC rows virtual
  obtain ⟨pre,d,_prelude,_preLe,price,_guardHistory,safe,first,outcome⟩:=RawCallerClosure.raw k N y
  have hist:∀ u,u ≤ d → (machine2 k).run u C=config2 k (O.run u oldC) :=
    raw_prefix2 k N B d y (fun u hu=>(first u hu).2.1)
  have prior:∀ u,u < d → ((machine2 k).run u C).state≠(machine2 k).accept ∧
      ((machine2 k).run u C).state≠(machine2 k).reject ∧
      ∀ b,((machine2 k).run u C).state≠old2 k (virtual b) := by
    intro u hu
    have states:=congrArg (fun c : Config (machine2 k).stateCount N B=>c.state) (hist u hu.le)
    change ((machine2 k).run u C).state=old2 k (O.run u oldC).state at states
    refine ⟨?_,?_,?_⟩
    · intro bad
      exact safe u hu.le (old_injective k (states.symm.trans (bad.trans (accept_map k).symm)))
    · intro bad
      exact (first u hu).1 (old_injective k (states.symm.trans (bad.trans (reject_map k).symm)))
    · intro b bad
      exact (first u hu).2.2 b (old_injective k (states.symm.trans bad))
  rcases outcome with ⟨_time,reject,finish,falseLanguage⟩|⟨_time,hit,finish⟩|normal
  · refine ⟨d,d,le_rfl,price.trans (prefix_price k N),hist,safe,first,prior,Or.inr (Or.inl ?_)⟩
    refine ⟨rfl,?_,falseLanguage,hist d le_rfl⟩
    have state:=congrArg Config.state finish
    change (O.run d oldC).state=RawCallerClosure.old k _ at state
    rw [reject,inherited_raw_reject] at state
    exact state
  · refine ⟨d,d,le_rfl,price.trans (prefix_price k N),hist,safe,first,prior,Or.inl ?_⟩
    refine ⟨rfl,?_,hist d le_rfl⟩
    obtain ⟨b,hb⟩:=hit
    refine ⟨b,?_⟩
    have state:=congrArg Config.state finish
    change (O.run d oldC).state=RawCallerClosure.old k _ at state
    rw [hb] at state
    exact state
  · -- Same original decoded source, actual old all-row endpoint and SAME time d.
    rcases normal with ⟨a,m,x,w,hN,decoded,word,length,n,z,tag,gamma,header,
      physical,ell,window,capacity,arena,hH,bodyEntry,allRows⟩
    by_cases rejected:(O.run d oldC).state=O.reject
    · have falseRelation:=normalReject k B N a m z n _ x w _ hH oldC d length header allRows rejected
      have falseLanguage:encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y=false := by
        simp only [encodedRelationLanguage,decoded]
        exact falseRelation
      exact ⟨d,d,le_rfl,price.trans (prefix_price k N),hist,safe,first,prior,
        Or.inr (Or.inl ⟨rfl,rejected,falseLanguage,hist d le_rfl⟩)⟩
    · obtain ⟨circuit,tail,bodyDecoded,size,_used,_tailEq,tableGood,atRowsDone⟩:=
        doneResult k B N (a+m) z n _ (n^k+k) (Cursor.Target.W k n) (Cursor.Target.M k n z)
          (9+2*z) (Fin.append x w) _ hH oldC d allRows rejected
      have original_iff:=rows_prefix_rho k a m n z x w length header tag circuit tail bodyDecoded size tableGood
      have atState:=congrArg Config.state atRowsDone
      have atHead:=congrArg Config.head atRowsDone
      let S:=a+m
      let F:=FixedRawLengthFence.fencePos N
      let r:=S-min (9+2*z+2^n) S
      let W:=Cursor.Target.W k n
      have pairSize:2*a+1+m=N:=hN
      have SN:S ≤ N:=by dsimp only [S];omega
      have rN:r ≤ N:=(Nat.sub_le S _).trans SN
      have sourcePosition:9+2*z+2^n < S:=min_lt_implies _ S physical
      have zN:z ≤ N:=(zero_bound S z (2^n) sourcePosition).trans SN
      have Pbound:D F r n 13+1 ≤ 64*(N+1):=by
        change SerializedBody.delimiter (3*N+2) r n 12+6+1 ≤ 64*(N+1)
        exact delimiter_bound N S z n r SN zN rN arena
      have fit:D F r n 13 < tapeLength N B:=raw_room k N (D F r n 13) Pbound
      -- Exact proof label of the reached parent image; no runtime installation.
      let actualTape:=normalImage k N x w z n circuit.size (W-tail.length) (W-(W-tail.length))
      have endpoint:(O.run d oldC)=
          ⟨rows,⟨S+z+2+n+1,hH⟩,fun i=>actualTape i.val⟩:=atRowsDone
      have frame:=frame_at_N k N x w hN gamma header capacity arena physical ell window
        circuit.size (W-tail.length) (W-(W-tail.length))
      obtain ⟨u,answer,positive,up,correct,nativePrefix,_footprint,finish⟩:=compose_guard k N B S z n F r W
        (Fin.append x w) actualTape frame fit hH d C oldC (hist d le_rfl) endpoint
      change (O.run d oldC).state=rows at atState
      change (O.run d oldC).head=⟨S+z+2+n+1,hH⟩ at atHead
      have pEq:S-r=9+2*z+2^n:=recovered_position _ S physical
      have correctPrefix:answer=true ↔ Target.PrefixOK (Fin.append x w) n z W:=by
        unfold PrefixAt at correct
        rw [pEq] at correct
        exact correct
      have answerRho:answer=PartAEndpoint.thresholdContentWitnessRelation k a m x w:=by
        apply Bool.eq_iff_iff.mpr
        exact correctPrefix.trans original_iff.symm
      have answerLanguage:answer=encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y:=by
        simp only [encodedRelationLanguage,decoded]
        exact answerRho
      have tailSafe:=nativePrefix
      have complete:=finish
      have atd:((machine2 k).run d C).state=old2 k rows:=by
        have eq:=congrArg Config.state (hist d le_rfl)
        change ((machine2 k).run d C).state=old2 k (O.run d oldC).state at eq
        exact eq.trans (congrArg (old2 k) atState)
      have atdSafe:((machine2 k).run d C).state≠(machine2 k).accept ∧
          ((machine2 k).run d C).state≠(machine2 k).reject ∧
          ∀ b,((machine2 k).run d C).state≠old2 k (virtual b):=by
        refine ⟨?_,?_,?_⟩
        · intro bad
          have same:=old_injective k (atd.symm.trans (bad.trans (accept_map k).symm))
          exact safe d le_rfl (atState.trans same)
        · intro bad
          have same:=old_injective k (atd.symm.trans (bad.trans (reject_map k).symm))
          exact rejected (atState.trans same)
        · intro b bad
          have same:=old_injective k (atd.symm.trans bad)
          exact oldNotDone k _ same.symm
      have fullPrior:∀ v,v < d+u → ((machine2 k).run v C).state≠(machine2 k).accept ∧
          ((machine2 k).run v C).state≠(machine2 k).reject ∧
          ∀ b,((machine2 k).run v C).state≠old2 k (virtual b):=by
        intro v hv
        by_cases early:v < d
        · exact prior v early
        · rcases tailSafe (v-d) (by omega) with zero|native
          · have eq:v=d:=by omega
            subst v
            exact atdSafe
          · rw [show d+(v-d)=v by omega] at native
            refine ⟨?_,?_,fun b=>safe_not_old k (virtual b) _ native⟩
            · intro bad
              exact safe_not_old k O.accept _ native (bad.trans (accept_map k).symm)
            · intro bad
              exact safe_not_old k O.reject _ native (bad.trans (reject_map k).symm)
      refine ⟨d,d+u,by omega,guard_price k N r (D F r n 13) u d rN Pbound price up,
        hist,safe,first,fullPrior,Or.inr (Or.inr ?_)⟩
      exact ⟨a,m,x,w,hN,decoded,word,length,n,z,tag,gamma,header,physical,ell,window,atState,hH,
        atHead,answer,answerLanguage,answerRho,correctPrefix,complete⟩
end NormalFinalClosure
