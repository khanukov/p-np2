import NormalFinalClosure.Decision2
import NormalFinalClosure.Activation2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`NormalFinalClosure.Frame2,`NormalFinalClosure,["D","GuardFrame","PrefixAt","repImage"]),
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["ns2","Safe2"]),
    (`NormalFinalClosure.Decision2,`NormalFinalClosure,["native_guard"]),
    (`NormalFinalClosure.FrameFacts2,`NormalFinalClosure,["clean_image"]),
    (`NormalFinalClosure.Activation2,`NormalFinalClosure,["activate_config"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing entire physical guard execution API"
      let some i:=e.getModuleIdxFor? name | throwError "Missing entire guard execution owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong entire guard execution owner"
      logInfo m!"entire-physical-guard-execution-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous (leaf.splitOn ".").getLast!) name::st.openDecls}
/-- The whole guard from FIRST old rowsDone, including its actual activation
row. Native per-prefix control and full head/exterior footprint are retained
for raw composition; no LIVE callback is executed at a padded deadline. -/
private theorem guard_run (k N B S z n F r W : Nat) (source : Fin S → Bool) (T : Nat → Option Bool)
    (fr:GuardFrame S z n F r W source T) (fit:D F r n 13 < tapeLength N B)
    (hH:S+z+2+n+1 < tapeLength N B) :
    let initial : Config (machine2 k).stateCount N B:=
      ⟨old2 k (RawCallerClosure.callerState k (PhysicalCallerClosure.rowsDone k)),⟨S+z+2+n+1,hH⟩,fun i=>T i.val⟩
    ∃ (t : Nat) (answer : Bool),0 < t ∧ t ≤ 1048576*(r+1)^4*(D F r n 13+1)^2 ∧
      (answer=true ↔ PrefixAt source (S-r) W) ∧
      (∀ u,u < t → u=0 ∨ Safe2 k ((machine2 k).run u initial).state) ∧
      (∀ u,u ≤ t → ((machine2 k).run u initial).head.val ≤ D F r n 13 ∧
        ∀ i:Fin (tapeLength N B),D F r n 13 < i.val → ((machine2 k).run u initial).tape i=T i.val) ∧
      (machine2 k).run t initial=
        ⟨if answer then (machine2 k).accept else (machine2 k).reject,⟨S+z+2+n+1,hH⟩,
          Target.cleared (fun i:Fin (tapeLength N B)=>T i.val) F r n⟩ := by
  intro initial
  obtain ⟨t,answer,price,correct,path⟩:=native_guard k S z n F r W source T fr
  let entered : Config (machine2 k).stateCount N B:=⟨ns2 k 1,⟨S+z+2+n+1,hH⟩,fun i=>T i.val⟩
  have one:(machine2 k).run 1 initial=entered:=by
    change (machine2 k).stepConfig initial=entered
    exact activate_config k N B ⟨S+z+2+n+1,hH⟩ (fun i=>T i.val)
  have execute:=path.execute fit
  change (machine2 k).run t entered=
    ⟨if answer then (machine2 k).accept else (machine2 k).reject,⟨S+z+2+n+1,hH⟩,
      fun i=>repImage T F r n S S 0 0 0 0 [] i.val⟩ at execute
  rw [clean_image N B S F r n T] at execute
  refine ⟨1+t,answer,by omega,by omega,correct,?_,?_,?_⟩
  · intro u hu
    by_cases zero:u=0
    · exact Or.inl zero
    · right
      have safe:=path.safe_prefix fit (u-1) (by omega)
      change Safe2 k ((machine2 k).run (u-1) entered).state at safe
      rw [show u=1+(u-1) by omega,(machine2 k).run_add,one]
      exact safe
  · intro u hu
    by_cases zero:u=0
    · subst u
      have bound:=path.bounds.1
      change S+z+2+n+1 ≤ D F r n 13 at bound
      exact ⟨bound,fun _ _=>rfl⟩
    · have fp:=path.footprint fit (u-1) (by omega)
      change ((machine2 k).run (u-1) entered).head.val ≤ D F r n 13 ∧
        ∀ i:Fin (tapeLength N B),D F r n 13 < i.val → ((machine2 k).run (u-1) entered).tape i=T i.val at fp
      rw [show u=1+(u-1) by omega,(machine2 k).run_add,one]
      exact fp
  · rw [(machine2 k).run_add,one]
    exact execute
end NormalFinalClosure
