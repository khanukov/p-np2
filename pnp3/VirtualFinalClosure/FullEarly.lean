import VirtualFinalClosure.FullEarlyRows
import VirtualFinalClosure.ArithmeticReplay
namespace VirtualFinalClosure.FullEarly
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.FullEarlyRows","VirtualFinalClosure.FullEarlyRows","effective","actualRow",(1:Nat)),
      ("VirtualFinalClosure.ArithmeticReplay","VirtualFinalClosure.ArithmeticReplay","lift","lift",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","phase","phase",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong actual same-budget replay interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual same-budget replay interface {mod}/{key}"
private theorem step_lift (k : Nat) {N B : Nat} (m : Fin 144) (c : Config (Cursor.machine k).stateCount N B)
    (no430 : c.state.val≠430+93*k) (lower : 98 ≤ c.state.val) (upper : c.state.val < 798+93*k)
    (no250 : c.state.val≠250) (no304 : c.state.val≠304) (no613 : c.state.val≠613+93*k)
    (afterLo : 98 ≤ ((Cursor.machine k).stepConfig c).state.val)
    (afterHi : ((Cursor.machine k).stepConfig c).state.val ≤ 798+93*k) :
    (machine k).stepConfig (lift k m c)=lift k m ((Cursor.machine k).stepConfig c) := by
  have row:=actualRow k c.state m (c.tape c.head) no430 lower upper no250 no304 no613 afterLo afterHi
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
/-- Every-time actual replay projection with CONSTANT metadata, justified by
actual active-row equality in the region. Neither a passive flag theorem nor
an endpoint-only tape rewrite is used. -/
private theorem run_lift (k : Nat) {N B : Nat} (m : Fin 144) (c : Config (Cursor.machine k).stateCount N B)
    (t : Nat) (range : ∀ u,u ≤ t → 98 ≤ ((Cursor.machine k).run u c).state.val ∧
      ((Cursor.machine k).run u c).state.val ≤ 798+93*k)
    (before : ∀ u,u < t → ((Cursor.machine k).run u c).state.val < 798+93*k ∧
      ((Cursor.machine k).run u c).state.val≠250 ∧ ((Cursor.machine k).run u c).state.val≠304 ∧ ((Cursor.machine k).run u c).state.val≠613+93*k ∧
      ((Cursor.machine k).run u c).state.val≠430+93*k) :
    ∀ u,u ≤ t → (machine k).run u (lift k m c)=lift k m ((Cursor.machine k).run u c) := by
  intro u hu
  induction u with
  | zero=>rfl
  | succ u ih=>
    have earlier:=ih (by omega)
    change (machine k).stepConfig ((machine k).run u (lift k m c))=
      lift k m ((Cursor.machine k).stepConfig ((Cursor.machine k).run u c))
    rw [earlier]
    exact step_lift k m ((Cursor.machine k).run u c) (before u (by omega)).2.2.2.2 (range u (by omega)).1 (before u (by omega)).1
      (before u (by omega)).2.1 (before u (by omega)).2.2.1 (before u (by omega)).2.2.2.1
      (range (u+1) hu).1 (range (u+1) hu).2
#print axioms step_lift
#print axioms run_lift
end VirtualFinalClosure.FullEarly
