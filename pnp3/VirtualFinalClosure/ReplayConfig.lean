import VirtualFinalClosure.ReplayPlain
namespace VirtualFinalClosure.ReplayConfig
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.ReplayPlain","VirtualFinalClosure.ReplayPlain","step_plain","plainStep",(1:Nat)),
      ("VirtualFinalClosure.BaseCursorRows","VirtualFinalClosure.BaseCursorRows","base_row","baseRow",1),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","table_value","tableValue",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong actual same-budget replay interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual same-budget replay interface {mod}/{key}"
private def lift (k : Nat) {N B : Nat} (m : Fin 144) (c : Config (Cursor.machine k).stateCount N B) :
    Config (machine k).stateCount N B := ⟨control k (tableControl k c.state.val) m,c.head,c.tape⟩
private def lift_type : ∀ k,{N B : Nat} → Fin 144 → Config (Cursor.machine k).stateCount N B →
    Config (machine k).stateCount N B := lift
private theorem actual_row (k : Nat) (q : Fin (Cursor.machine k).stateCount) (m : Fin 144) (b : Option Bool)
    (lower : 98 ≤ q.val) (upper : q.val < 201)
    (afterLo : 98 ≤ ((Cursor.machine k).step q b).1.val)
    (afterHi : ((Cursor.machine k).step q b).1.val ≤ 201) :
    (machine k).step (control k (tableControl k q.val) m) b=
      (control k (tableControl k ((Cursor.machine k).step q b).1.val) m,((Cursor.machine k).step q b).2) := by
  have base:=baseRow k q b upper
  have incoming : 473 ≤ (tableControl k q.val).val ∧ (tableControl k q.val).val < 576 := by
    rw [tableValue k q.val q.isLt]
    omega
  have outgoing : 473 ≤ ((CertificateGuardClosure.machine k).step (tableControl k q.val) b).1.val ∧
      ((CertificateGuardClosure.machine k).step (tableControl k q.val) b).1.val ≤ 576 := by
    rw [base]
    dsimp only
    rw [tableValue k ((Cursor.machine k).step q b).1.val ((Cursor.machine k).step q b).1.isLt]
    omega
  have row:=plainStep k (tableControl k q.val) m.val b m.isLt incoming.1 incoming.2 outgoing
  rw [base] at row
  exact row
/-- Whole Config, one actual SAME-budget edge; both head clamps and every tape
cell agree because the actual literal symbol and direction agree. -/
private theorem step_lift (k : Nat) {N B : Nat} (m : Fin 144) (c : Config (Cursor.machine k).stateCount N B)
    (lower : 98 ≤ c.state.val) (upper : c.state.val < 201)
    (afterLo : 98 ≤ ((Cursor.machine k).stepConfig c).state.val)
    (afterHi : ((Cursor.machine k).stepConfig c).state.val ≤ 201) :
    (machine k).stepConfig (lift k m c)=lift k m ((Cursor.machine k).stepConfig c) := by
  have row:=actual_row k c.state m (c.tape c.head) lower upper afterLo afterHi
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
      ((Cursor.machine k).run u c).state.val ≤ 201)
    (before : ∀ u,u < t → ((Cursor.machine k).run u c).state.val < 201) :
    ∀ u,u ≤ t → (machine k).run u (lift k m c)=lift k m ((Cursor.machine k).run u c) := by
  intro u hu
  induction u with
  | zero=>rfl
  | succ u ih=>
    have earlier:=ih (by omega)
    change (machine k).stepConfig ((machine k).run u (lift k m c))=
      lift k m ((Cursor.machine k).stepConfig ((Cursor.machine k).run u c))
    rw [earlier]
    exact step_lift k m ((Cursor.machine k).run u c) (range u (by omega)).1 (before u (by omega))
      (range (u+1) hu).1 (range (u+1) hu).2
#print axioms lift_type
#print axioms actual_row
#print axioms step_lift
#print axioms run_lift
end VirtualFinalClosure.ReplayConfig
