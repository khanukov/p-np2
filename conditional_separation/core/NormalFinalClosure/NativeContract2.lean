import NormalFinalClosure.FrameFacts2
import NormalFinalClosure.Rows2Code
import NormalFinalClosure.Support
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`NormalFinalClosure.Frame2,`NormalFinalClosure,["D","GuardFrame","PrefixAt","repImage"]),
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["ns2","Safe2"]),
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["Node","Path"])] do
    for leaf in leaves do
      let n:=Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns) leaf
      let some ci:=e.find? n | throwError "Missing exact native execution component"
      let some i:=e.getModuleIdxFor? n | throwError "Missing native execution component owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong native execution component owner"
      logInfo m!"native-guard-implementation-component|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac do
    let owner:=`PhysicalCallerClosure.Engine
    let n:=Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") "Node") "mk"
    let e←getEnv
    let some (.ctorInfo ci):=e.find? n | throwError "Missing exact native Node constructor"
    let some i:=e.getModuleIdxFor? n | throwError "Missing Node owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong Node owner"
    logInfo m!"native-guard-Node-constructor|{n}|{ci.type}"
    closeMainGoal `node (mkConst n (ci.levelParams.map Level.param))
/-- The physical proof API to be IMPLEMENTED. The Path inductive charges actual
literal rows, supplies every-prefix head room/control safety/exterior, and has no
prophecy/run/evaluation field in its static caller frame. It is stronger than the
already frozen GuardBody contract and does not replace full Target2.Raw. -/
private def NativeGuard (k : Nat) : Prop :=
  ∀ (S z n F r W : Nat) (source : Fin S → Bool) (T : Nat → Option Bool),
    GuardFrame S z n F r W source T →
    ∃ (t : Nat) (answer : Bool),
      t+1 ≤ 1048576*(r+1)^4*(D F r n 13+1)^2 ∧
      (answer=true ↔ PrefixAt source (S-r) W) ∧
      Path (machine2 k) (Safe2 k) (D F r n 13) t
        (node (ns2 k 1) (S+z+2+n+1) T)
        (node (if answer then (machine2 k).accept else (machine2 k).reject)
          (S+z+2+n+1) (repImage T F r n S S 0 0 0 0 []))
end NormalFinalClosure
