import UniformClassBridgeClosure.Target
namespace UniformClassBridgeClosure
open Pnp3.Complexity.Uniform.V1 Turing Lean Elab Command
run_cmd do
  let e←getEnv
  for (owner,leaf) in [(`StandardTMBridgeClosure.Simulation,"ready_reflect"),
      (`StandardTMBridgeClosure.Simulation,"steps_prefix"),
      (`StandardTMBridgeClosure.Facts,"ready_halt"),(`StandardTMBridgeClosure.Clock,"overhead")] do
    let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "StandardTMBridgeClosure") leaf
    let some (.thmInfo ci):=e.find? n | throwError "Missing exact theorem interface {n}"
    let some i:=e.getModuleIdxFor? n | throwError "Interface owner missing"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong interface owner"
    logInfo m!"typed-private-interface|{owner}|{n}|kind=theorem|{(repr ci.type).pretty 1000000000}"
    modifyScope fun s=>{s with openDecls:=.explicit (Name.str .anonymous leaf) n::s.openDecls}
private theorem trace_eq (M : UniformTM) (n : Nat)
    (s : TM0.Cfg (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4))) :
    Ordinary.trace (StandardTMBridgeClosure.compile M) n s=StandardTMBridgeClosure.steps M n s := by
  induction n generalizing s with
  | zero=>rfl
  | succ n ih=>simp only [Ordinary.trace,StandardTMBridgeClosure.steps,ih]
/-- Leastness is obtained by proof-only strong induction, not executable
choose/find data. Both wrong-terminal branches are excluded by absorption. -/
private theorem first_source (M : UniformTM) (B N : Nat) (y : Bitstring N) (answer : Bool)
    (h:DecidesWithin M B y answer) :
    ∃ t,t ≤ B ∧ (M.run t (initialConfig M B y)).state=(if answer then M.accept else M.reject) ∧
      ∀ u,u < t → (M.run u (initialConfig M B y)).state≠M.accept ∧
        (M.run u (initialConfig M B y)).state≠M.reject := by
  classical
  let C:=initialConfig M B y
  have ending:(M.run B C).state=(if answer then M.accept else M.reject):=by
    have decided:DecidesAt M B B y answer:=(decidesAt_budget_iff_decidesWithin M y answer).2 h
    cases answer <;> exact decided
  have search:∀ s,(M.run s C).state=(if answer then M.accept else M.reject) →
      ∃ t,t ≤ s ∧ (M.run t C).state=(if answer then M.accept else M.reject) ∧
        ∀ u,u < t → (M.run u C).state≠M.accept ∧ (M.run u C).state≠M.reject := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih=>
      intro hs
      by_cases earlier:∃ u,u < s ∧ ((M.run u C).state=M.accept ∨ (M.run u C).state=M.reject)
      · obtain ⟨u,us,terminal⟩:=earlier
        have frozen:M.run s C=M.run u C:=by
          rw [show s=u+(s-u) by omega,M.run_add]
          rcases terminal with accepted|rejected
          · exact M.run_accept _ accepted _
          · exact M.run_reject _ rejected _
        have correct:(M.run u C).state=(if answer then M.accept else M.reject):=
          (congrArg Config.state frozen).symm.trans hs
        obtain ⟨t,tu,te,safe⟩:=ih u us correct
        exact ⟨t,tu.trans us.le,te,safe⟩
      · refine ⟨s,le_rfl,hs,fun u us=>⟨?_,?_⟩⟩
        · intro eq;exact earlier ⟨u,us,Or.inl eq⟩
        · intro eq;exact earlier ⟨u,us,Or.inr eq⟩
  exact search B ending
/-- Unconditional operational transfer from actual versioned within-clock
semantics to genuine library execution. No firstness or room caller premise. -/
theorem operational : Target.Transfer := by
  intro M c N y answer h
  obtain ⟨t,ht,ending,safe⟩:=first_source M (polyClock c N) N y answer h
  have room:∀ u,u < t →
      (M.step (M.run u (initialConfig M (polyClock c N) y)).state
        ((M.run u (initialConfig M (polyClock c N) y)).tape (M.run u (initialConfig M (polyClock c N) y)).head)).2.2=Move.right →
      (M.run u (initialConfig M (polyClock c N) y)).head.val+1 < tapeLength N (polyClock c N):=
    fun u hu _=>M.run_initialConfig_right_room y ht u hu
  obtain ⟨macros,mids⟩:=StandardTMBridgeClosure.simulation M N (polyClock c N) t y safe room
  obtain ⟨last,run,rep⟩:=macros t le_rfl
  have trace:Ordinary.trace (StandardTMBridgeClosure.compile M) (1+2*t)
      (TM0.init (StandardTMBridgeClosure.encode (List.ofFn y)))=some last:=by rw [trace_eq];exact run
  have price:1+2*t ≤ N^(4*c+4)+(4*c+4):=by
    have bound:=overhead c N
    unfold polyClock at ht bound
    omega
  have label:last.q=some ((if answer then M.accept else M.reject),0):=
    rep.1.trans (congrArg (fun q=>some (q,0)) ending)
  have halted:TM0.step (StandardTMBridgeClosure.compile M) last=none:=
    (ready_halt M last _ label).mpr (by cases answer <;> simp)
  have first:∀ j,j < 1+2*t → ∀ v,
      Ordinary.trace (StandardTMBridgeClosure.compile M) j
        (TM0.init (StandardTMBridgeClosure.encode (List.ofFn y)))=some v →
      v.q≠some (M.accept,0) ∧ v.q≠some (M.reject,0):=by
    intro j jt v hv
    rw [trace_eq] at hv
    constructor
    · intro bad
      obtain ⟨u,ut,eq⟩:=ready_reflect M N (polyClock c N) t y safe room j jt v hv M.accept bad
      exact (safe u ut).1 eq.symm
    · intro bad
      obtain ⟨u,ut,eq⟩:=ready_reflect M N (polyClock c N) t y safe room j jt v hv M.reject bad
      exact (safe u ut).2 eq.symm
  refine ⟨?_,t,last,ht,price,ending,trace,rep,?_,?_,?_⟩
  · refine ⟨?_,1+2*t,last,price,trace,?_,halted,first⟩
    · intro eq;exact M.accept_ne_reject (congrArg Prod.fst (Option.some.inj eq))
    · cases answer <;> exact label
  · intro u hu
    obtain ⟨v,run,rep⟩:=macros u hu
    exact ⟨v,by rw [trace_eq];exact run,rep⟩
  · intro u hu
    obtain ⟨v,run,control,tape⟩:=mids u hu
    exact ⟨v,by rw [trace_eq];exact run,control,tape⟩
  · intro j hj
    obtain ⟨v,hv⟩:=steps_prefix M (1+2*t) j _ last run hj
    exact ⟨v,by rw [trace_eq];exact hv⟩
#print axioms operational
end UniformClassBridgeClosure
