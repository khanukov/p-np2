import VirtualFinalClosure.CleanupReplayRows
import VirtualFinalClosure.ArithmeticReplay
namespace VirtualFinalClosure.CleanupReplay
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.CleanupReplayRows","VirtualFinalClosure.CleanupReplayRows","effective","actualRow",(1:Nat)),
      ("VirtualFinalClosure.ArithmeticReplay","VirtualFinalClosure.ArithmeticReplay","lift","lift",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","phase","phase",0) ] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong phase2 whole-Config term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique phase2 whole-Config term {mod}/{key}"
private theorem step_lift (k : Nat) {N B : Nat} (m : Fin 144) (c : Config (Cursor.machine k).stateCount N B)
    (ph : phase m.val=2) (lower : 798+93*k ≤ c.state.val) (noReady : c.state.val≠936+93*k)
    (afterLo : 798+93*k ≤ ((Cursor.machine k).stepConfig c).state.val) :
    (machine k).stepConfig (lift k m c)=lift k m ((Cursor.machine k).stepConfig c):=by
  have row:=actualRow k c.state m (c.tape c.head) ph lower noReady afterLo
  have hs:=congrArg Prod.fst row
  have hw:=congrArg (fun a=>a.2.1) row
  have hd:=congrArg (fun a=>a.2.2) row
  dsimp only at hw hd
  apply Config.ext_parts
  · exact hs
  · dsimp only [UniformTM.stepConfig,lift]
    rw [hd]
  · funext i
    dsimp only [UniformTM.stepConfig,lift]
    rw [hw]
/-- Actual EVERY-TIME phase2 replay on the same dependent allocation, including
both literal head clamps. The original Ready row is excluded until the real cut;
source, dirty-bank writes, elapsed witnesses and flag/bad metadata all agree. -/
private theorem run_lift (k : Nat) {N B : Nat} (m : Fin 144) (c : Config (Cursor.machine k).stateCount N B)
    (t : Nat) (ph : phase m.val=2)
    (range : ∀ u,u ≤ t → 798+93*k ≤ ((Cursor.machine k).run u c).state.val)
    (before : ∀ u,u < t → ((Cursor.machine k).run u c).state.val≠936+93*k) :
    ∀ u,u ≤ t → (machine k).run u (lift k m c)=lift k m ((Cursor.machine k).run u c):=by
  intro u hu
  induction u with
  | zero=>rfl
  | succ u ih=>
    have earlier:=ih (by omega)
    change (machine k).stepConfig ((machine k).run u (lift k m c))=
      lift k m ((Cursor.machine k).stepConfig ((Cursor.machine k).run u c))
    rw [earlier]
    exact step_lift k m ((Cursor.machine k).run u c) ph (range u (by omega)) (before u (by omega)) (range (u+1) hu)
#print axioms step_lift
#print axioms run_lift
end VirtualFinalClosure.CleanupReplay
