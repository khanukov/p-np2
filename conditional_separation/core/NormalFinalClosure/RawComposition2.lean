import NormalFinalClosure.GuardExecution2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`NormalFinalClosure.Frame2,`NormalFinalClosure,["D","GuardFrame","PrefixAt"]),
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["Safe2"]),
    (`NormalFinalClosure.GuardExecution2,`NormalFinalClosure,["guard_run"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing actual raw guard composition API"
      let some i:=e.getModuleIdxFor? name | throwError "Missing raw guard composition owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong raw guard composition owner"
      logInfo m!"actual-raw-guard-composition-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) name::st.openDecls}
private theorem config_constructor (k N B : Nat) (q : Fin (RawCallerClosure.machine k).stateCount)
    (head : Fin (tapeLength N B)) (tape : Fin (tapeLength N B) → Option Bool) :
    config2 k (⟨q,head,tape⟩:Config (RawCallerClosure.machine k).stateCount N B)=⟨old2 k q,head,tape⟩ := rfl
/-- Same actual prefix endpoint and SAME allocation: compose one real activation
and every native row at witnessed time d. T is merely the already reached whole
old tape; this theorem neither installs nor reconstructs any runtime operand. -/
private theorem compose_guard (k N B S z n F r W : Nat) (source : Fin S → Bool) (T : Nat → Option Bool)
    (fr:GuardFrame S z n F r W source T) (fit:D F r n 13 < tapeLength N B)
    (hH:S+z+2+n+1 < tapeLength N B) (d : Nat)
    (C : Config (machine2 k).stateCount N B) (oldC : Config (RawCallerClosure.machine k).stateCount N B)
    (history:(machine2 k).run d C=config2 k ((RawCallerClosure.machine k).run d oldC))
    (endpoint:(RawCallerClosure.machine k).run d oldC=
      ⟨RawCallerClosure.callerState k (PhysicalCallerClosure.rowsDone k),⟨S+z+2+n+1,hH⟩,fun i=>T i.val⟩) :
    ∃ (u : Nat) (answer : Bool),0 < u ∧ u ≤ 1048576*(r+1)^4*(D F r n 13+1)^2 ∧
      (answer=true ↔ PrefixAt source (S-r) W) ∧
      (∀ v,v < u → v=0 ∨ Safe2 k ((machine2 k).run (d+v) C).state) ∧
      (∀ v,v ≤ u → ((machine2 k).run (d+v) C).head.val ≤ D F r n 13 ∧
        ∀ i:Fin (tapeLength N B),D F r n 13 < i.val → ((machine2 k).run (d+v) C).tape i=T i.val) ∧
      (machine2 k).run (d+u) C=
        ⟨if answer then (machine2 k).accept else (machine2 k).reject,⟨S+z+2+n+1,hH⟩,
          Target.cleared ((RawCallerClosure.machine k).run d oldC).tape F r n⟩ := by
  obtain ⟨u,answer,positive,price,correct,guardPrefix,footprint,finish⟩:=guard_run k N B S z n F r W source T fr fit hH
  have transport:∀ v,(machine2 k).run (d+v) C=
      (machine2 k).run v
        (⟨old2 k (RawCallerClosure.callerState k (PhysicalCallerClosure.rowsDone k)),⟨S+z+2+n+1,hH⟩,fun i=>T i.val⟩:Config (machine2 k).stateCount N B):=by
    intro v
    rw [(machine2 k).run_add,history,endpoint,config_constructor]
  refine ⟨u,answer,positive,price,correct,?_,?_,?_⟩
  · intro v hv
    rw [transport v]
    exact guardPrefix v hv
  · intro v hv
    rw [transport v]
    exact footprint v hv
  · rw [transport u,endpoint]
    exact finish
private theorem min_lt_implies (A S : Nat) (h:min A S < S) : A < S := by omega
private theorem recovered_position (A S : Nat) (h:min A S < S) : S-(S-min A S)=A := by omega
private theorem zero_bound (S z Q : Nat) (h:9+2*z+Q < S) : z ≤ S := by omega
end NormalFinalClosure
