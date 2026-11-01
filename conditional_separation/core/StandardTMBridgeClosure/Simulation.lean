import StandardTMBridgeClosure.Native
namespace StandardTMBridgeClosure
open Pnp3.Complexity.Uniform.V1 Turing Lean Elab Command
run_cmd do
  let e←getEnv
  for (owner,leaf) in [(`StandardTMBridgeClosure.Tape,"boot"),(`StandardTMBridgeClosure.Tape,"steps_add"),
      (`StandardTMBridgeClosure.Native,"native_step")] do
    let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "StandardTMBridgeClosure") leaf
    let some (.thmInfo ci):=e.find? n | throwError "Missing exact simulation theorem {n}"
    let some i:=e.getModuleIdxFor? n | throwError "Missing simulation owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong simulation owner"
    logInfo m!"typed-private-interface|{owner}|{n}|kind=theorem|{(repr ci.type).pretty 1000000000}"
    modifyScope fun s=>{s with openDecls:=.explicit (Name.str .anonymous leaf) n::s.openDecls}
/-- Actual write/move simulation from the library initialization, with a whole
midpoint tape after every write. No source terminal is padded by library steps. -/
theorem simulation (M : UniformTM) : Target.Simulation M := by
  intro N B t y c start safe room
  have macroRun (u : Nat) (ut:u ≤ t) :
      ∃ v,steps M (1+2*u) start=some v ∧ Represents M (M.run u c) v := by
    induction u with
    | zero=>simpa only [Nat.mul_zero,Nat.add_zero,UniformTM.run] using boot M N B y
    | succ u ih=>
      obtain ⟨v,trace,rep⟩:=ih (by omega)
      obtain ⟨mid,last,enter,leave,lastRep,_midq,_midt⟩:=
        native_step M (M.run u c) v rep (safe u (by omega)) (room u (by omega))
      have two:steps M 2 v=some last:=by simp only [steps,enter,leave,Option.bind_some]
      have add:=steps_add M (1+2*u) 2 start
      rw [trace,Option.bind_some,two] at add
      refine ⟨last,?_,lastRep⟩
      rw [show 1+2*(u+1)=(1+2*u)+2 by omega]
      exact add
  refine ⟨macroRun,?_⟩
  intro u ut s a
  obtain ⟨v,trace,rep⟩:=macroRun u ut.le
  obtain ⟨mid,last,enter,_leave,_lastRep,midq,midt⟩:=native_step M s v rep (safe u ut) (room u ut)
  refine ⟨mid,?_,midq,?_⟩
  · have add:=steps_add M (1+2*u) 1 start
    have one:steps M 1 v=some mid:=by simp only [steps,enter,Option.bind_some]
    rw [trace,Option.bind_some,one] at add
    rw [show 2+2*u=(1+2*u)+1 by omega]
    exact add
  · exact midt
private theorem steps_prefix (M : UniformTM) (n j : Nat)
    (c d : TM0.Cfg (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4)))
    (trace:steps M n c=some d) (bound:j ≤ n) : ∃ v,steps M j c=some v := by
  induction n generalizing c j with
  | zero=>
    have jz:j=0:=by omega
    subst j
    exact ⟨c,rfl⟩
  | succ n ih=>
    cases j with
    | zero=>exact ⟨c,rfl⟩
    | succ j=>
      cases edge:TM0.step (compile M) c with
      | none=>simp only [steps,edge,Option.bind_none] at trace;cases trace
      | some next=>
        have rest:steps M n next=some d:=by simpa only [steps,edge,Option.bind_some] using trace
        obtain ⟨v,hv⟩:=ih (j:=j) (c:=next) rest (by omega)
        exact ⟨v,by simpa only [steps,edge,Option.bind_some] using hv⟩
private theorem ready_reflect (M : UniformTM) (N B t : Nat) (y : Bitstring N)
    (safe:∀ u,u < t → (M.run u (initialConfig M B y)).state≠M.accept ∧
      (M.run u (initialConfig M B y)).state≠M.reject)
    (room:∀ u,u < t → (M.step (M.run u (initialConfig M B y)).state
      ((M.run u (initialConfig M B y)).tape (M.run u (initialConfig M B y)).head)).2.2=Move.right →
      (M.run u (initialConfig M B y)).head.val+1 < tapeLength N B)
    (j : Nat) (jt:j < 1+2*t)
    (v : TM0.Cfg (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4)))
    (trace:steps M j (TM0.init (encode (List.ofFn y)))=some v) (q : Fin M.stateCount)
    (ready:v.q=some (q,0)) :
    ∃ u,u < t ∧ q=(M.run u (initialConfig M B y)).state := by
  obtain ⟨macros,mids⟩:=simulation M N B t y safe room
  by_cases zero:j=0
  · subst j
    have eq:TM0.init (encode (List.ofFn y))=v:=Option.some.inj trace
    rw [←eq] at ready
    cases ready
  · let u:=(j-1)/2
    have remainder:=Nat.mod_lt (j-1) (by decide : 0 < 2)
    have decomposition:=Nat.mod_add_div (j-1) 2
    have parity:j=1+2*u ∨ j=2+2*u:=by dsimp only [u];omega
    rcases parity with atMacro|middle
    · have ut:u < t:=by omega
      obtain ⟨d,hd,rep⟩:=macros u ut.le
      rw [atMacro,hd] at trace
      have eq:d=v:=Option.some.inj trace
      have controls:=rep.1.symm.trans (eq ▸ ready)
      have values:=congrArg (fun x : Option (Fin M.stateCount × Fin 4)=>x.map Prod.fst) controls
      have qeq:(M.run u (initialConfig M B y)).state=q:=by simpa only [Option.map_some,Option.some.injEq] using values
      exact ⟨u,ut,qeq.symm⟩
    · have ut:u < t:=by omega
      obtain ⟨d,hd,control,_tape⟩:=mids u ut
      rw [middle,hd] at trace
      have eq:d=v:=Option.some.inj trace
      have both:=Option.some.inj (control.symm.trans (eq ▸ ready))
      have phases:=congrArg Prod.snd both
      cases direction:(M.step (M.run u (initialConfig M B y)).state
        ((M.run u (initialConfig M B y)).tape (M.run u (initialConfig M B y)).head)).2.2 <;>
        simp only [direction] at phases <;> cases phases
end StandardTMBridgeClosure
