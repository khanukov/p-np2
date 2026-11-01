import PhysicalCallerClosure.RoundTarget
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion Pnp4.AlgorithmsToLowerBounds
open Lean Elab Tactic in
private def exactTerm (owner : Name) (leaf : String) : TacticM Unit := do
  let env ← getEnv
  let n:=(leaf.splitOn ".").foldl Name.str
    (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure")
  let some (.thmInfo ci):=env.find? n | throwError "Missing expected theorem: {n}"
  let some i:=env.getModuleIdxFor? n | throwError "No owner: {n}"
  unless i.toNat<env.header.moduleNames.size do throwError "Owner index out of range"
  unless env.header.moduleNames[i]! == owner do throwError "Wrong owner: {n}"
  logInfo m!"ordinary-private|{owner}|theorem|{n}|{ci.type}"
  closeMainGoal `exactTerm (mkConst n (ci.levelParams.map Level.param))
private theorem body_injective : ∀ k,Function.Injective (BodyIngress.body k) := by
  run_tac exactTerm `PhysicalCallerClosure.Embedding "body_injective"
private theorem before_entry_no_done : ∀ {k N B e : Nat} (c : Config (BodyIngress.machine k).stateCount N B)
    (mode : Fin 3),((BodyIngress.machine k).run e c).state=BodyIngress.body k (SerializedBody.entry mode) →
    ∀ u,u ≤ e → ∀ b,((BodyIngress.machine k).run u c).state≠BodyIngress.body k (SerializedBody.done b) := by
  run_tac exactTerm `PhysicalCallerClosure.Stability "before_entry_no_done"
private theorem total_clock (R e t : Nat) (a:e ≤ 1073741824*(R+1)^3)
    (b:t ≤ 1073741824*(R+1)^6) : e+t ≤ 2147483648*(R+1)^6 := by
  have powers : (R+1)^3 ≤ (R+1)^6:=Nat.pow_le_pow_right (by omega) (by decide)
  nlinarith
/-- Actual literal installer and complete BODY on the same table and allocation. -/
theorem installed_body (k : Nat) : InstalledBody k := by
  unfold InstalledBody
  intro R S z n p g W Q source beta T pos sr nr physical
  dsimp only
  intro gf wf ef positive arena src eof reg sep right betaCells marks gap fence
    delims bank0 bank1 bank2 bank34 bank5 fresh fit hd hh
  let r:=S-p
  let L:=S+z+2
  let H:=L+n+1
  let F:=FixedRawLengthFence.fencePos R
  let B:=FixedRawLengthFence.allocation R
  let M:=p+bitLength W+W
  let c : Config (BodyIngress.machine k).stateCount R B:=
    ⟨BodyIngress.old k (CarryWindow.ready k),⟨SerializedBody.delimiter F r n 0,hd⟩,fun i=>T i.val⟩
  obtain ⟨e,eprice,entry,_foot,safe,_first⟩:=FullIngressClosure.body k
    R S z n p g W Q source beta T pos sr nr physical gf wf ef positive arena src eof reg sep right
    betaCells marks gap fence delims bank0 bank1 bank2 bank34 bank5 fresh fit hd hh
  let initial : Config SerializedBody.machine.stateCount R B:=
    ⟨SerializedBody.entry (SerializedBody.sourceMode source M),⟨H,hh⟩,
      fun i=>SerializedBody.prepared T S M F r n g W i.val⟩
  change (BodyIngress.machine k).run e c=BodyIngress.bodyConfig k initial at entry
  have before:=before_entry_no_done c (SerializedBody.sourceMode source M) (congrArg Config.state entry)
  have sourceM (i : Nat) (lo:M ≤ i) (hi:i<S) : T i=some (source ⟨i,hi⟩):=src i (by dsimp only [M] at lo;omega) hi
  obtain ⟨t,tprice,noAccept,early,result⟩:=ambient_body B R S z n r g W M Q source beta T
    (Nat.sub_le _ _) sr gf wf ef (by dsimp only [M,r];omega) positive arena sourceM eof reg sep
    betaCells right marks gap fence fit hh
  change (∀ u,u ≤ t → (SerializedBody.machine.run u initial).state≠SerializedBody.machine.accept) at noAccept
  change (∀ u,u<t → (SerializedBody.machine.run u initial).state≠SerializedBody.machine.reject ∧
    (SerializedBody.machine.run u initial).state≠SerializedBody.done false ∧
    (SerializedBody.machine.run u initial).state≠SerializedBody.done true) at early
  have after (u : Nat) : (BodyIngress.machine k).run (e+u) c=
      BodyIngress.bodyConfig k (SerializedBody.machine.run u initial) := by
    rw [UniformTM.run_add,entry,body_run]
  refine ⟨e,t,eprice,tprice,total_clock R e t eprice tprice,?_,?_,?_⟩
  · intro u hu bad
    by_cases pre:u<e
    · exact (safe u (by omega)).1 bad
    · rw [show u=e+(u-e) by omega,after] at bad
      apply noAccept (u-e) (by omega)
      apply body_injective k
      exact bad
  · intro u hu
    by_cases pre:u<e
    · exact ⟨(safe u (by omega)).2,before u (by omega) false,before u (by omega) true⟩
    · have prior:=early (u-e) (by omega)
      rw [show u=e+(u-e) by omega,after]
      exact ⟨fun bad=>prior.1 (body_injective k bad),
        fun bad=>prior.2.1 (body_injective k bad),fun bad=>prior.2.2 (body_injective k bad)⟩
  · dsimp only at result ⊢
    generalize hs : (do
      let (circuit,tail) ← decodeCircuitFull n (bitLength n) (SerializedBody.window source M W)
      if circuit.size ≤ g then some ((circuit.size,Pnp3.Models.Circuit.eval circuit beta),tail) else none)=spec at result ⊢
    cases spec with
    | none=>rw [after,result];rfl
    | some pair=>
      rcases pair with ⟨⟨size,b⟩,tail⟩
      obtain ⟨consumed,hw,tail,done⟩:=result
      exact ⟨consumed,hw,tail,by rw [after,done];rfl⟩
end PhysicalCallerClosure
