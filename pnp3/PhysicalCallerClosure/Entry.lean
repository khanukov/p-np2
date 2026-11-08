import PhysicalCallerClosure.EntryTarget
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Tactic
private theorem old_injective : ∀ k,Function.Injective (oldState k) := by
  run_tac do
    let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.Rows 0) "PhysicalCallerClosure") "old_injective"
    let e←getEnv
    let some (.thmInfo ci):=e.find? n | throwError "Missing exact old injection theorem"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat<e.header.moduleNames.size do throwError "Owner index outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.Rows do throwError "Wrong injection owner"
    logInfo m!"caller-adapter|theorem|{n}|{ci.type}"
    closeMainGoal `old_injective (mkConst n (ci.levelParams.map Level.param))
private theorem initial_old {k N B : Nat} (y : Bitstring N) :
    initialConfig (callerMachine k) B y=
      ⟨oldState k (initialConfig (BodyIngress.machine k) B y).state,
        (initialConfig (BodyIngress.machine k) B y).head,(initialConfig (BodyIngress.machine k) B y).tape⟩ := rfl
private theorem before_entry_no_reject {k N B h : Nat}
    (c : Config (BodyIngress.machine k).stateCount N B) (mode : Fin 3)
    (last:((BodyIngress.machine k).run h c).state=BodyIngress.body k (SerializedBody.entry mode)) :
    ∀ u,u ≤ h → ((BodyIngress.machine k).run u c).state≠(BodyIngress.machine k).reject := by
  have distinct:BodyIngress.body k (SerializedBody.entry mode)≠(BodyIngress.machine k).reject := by
    intro bad
    have values:=congrArg Fin.val bad
    have entryVal:(BodyIngress.body k (SerializedBody.entry mode)).val=(CarryWindow.machine k).stateCount+(4+mode.val) := by
      fin_cases mode <;> rfl
    rw [entryVal] at values
    change (CarryWindow.machine k).stateCount+(4+mode.val)=(CarryWindow.machine k).reject.val at values
    have bound:=(CarryWindow.machine k).reject.isLt
    omega
  intro u hu bad
  have fixed:=(BodyIngress.machine k).run_reject ((BodyIngress.machine k).run u c) bad (h-u)
  rw [←UniformTM.run_add,show u+(h-u)=h by omega] at fixed
  exact distinct (last.symm.trans ((congrArg Config.state fixed).trans bad))
/-- RAW execution on the new caller through the first old-entry cut, before any reset row. -/
theorem caller_raw_entry (k : Nat) : RawEntry k := by
  intro a m x w accepted
  obtain ⟨pr,parsed,z,hH,gamma,normal⟩:=raw_first k x w accepted
  refine ⟨pr,parsed,z,hH,gamma,?_⟩
  dsimp only at normal ⊢
  intro physical ellFits wFits
  obtain ⟨h,t,hp,_tp,_total,entry,first,safe,_early,_result⟩:=normal physical ellFits wFits
  let c:=initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
  have transportPrefix:=caller_prefix (k:=k) (t:=h) c first
  have transported (u : Nat) (hu:u ≤ h) :
      (callerMachine k).run u
          (initialConfig (callerMachine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))=
        ⟨oldState k ((BodyIngress.machine k).run u c).state,
          ((BodyIngress.machine k).run u c).head,((BodyIngress.machine k).run u c).tape⟩ := by
    rw [initial_old]
    exact transportPrefix u hu
  refine ⟨h,hp,?_,?_,?_⟩
  · rw [transported h le_rfl,entry]
  · intro u hu mode bad
    rw [transported u (by omega)] at bad
    exact first u hu mode (old_injective k bad)
  · intro u hu
    rw [transported u hu]
    exact ⟨fun bad=>(safe u (by omega)) (old_injective k bad),
      fun bad=>before_entry_no_reject c _ (congrArg Config.state entry) u hu (old_injective k bad)⟩
#print axioms caller_raw_entry
end PhysicalCallerClosure
