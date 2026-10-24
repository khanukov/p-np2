import VirtualFinalClosure.Wire
namespace VirtualFinalClosure.Native
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic Meta
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,theoremKind) in [
      ("VirtualFinalClosure.Wire","VirtualFinalClosure.Wire","native_step","expanded",true),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","pack","np",false),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","resolve","resolveCode",false),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","changeMeta","changeMode",false),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","encodeMeta","encodeMode",false),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","tailStep","tailStep",false),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","symbol","writeSymbol",false),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","direction","moveDirection",false),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","romPin","rom",false)] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      let correct:=match ci with | .thmInfo _=>theoremKind | .defnInfo _=>!theoremKind | _=>false
      unless correct do throwError "Wrong selected native term kind {n}"
      logInfo m!"private-term|{n}|isTheorem={theoremKind}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique native row term {mod}/{key}"
private def pack_type : ∀ k,Nat → Nat → Fin (machine k).stateCount := np
private def rom_type : Array (Nat × Nat × Nat × Nat) := rom
/-- Assign an ordinary Eq.refl proof term; the declaration kernel checks
its full expected equality. No evaluator, option/transparency change or trusted
certificate is used. This avoids recursive elaborator normalization of the ROM. -/
private def ordinaryKernelRefl : TacticM Unit := do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  unless !target.hasMVar && target.isAppOfArity ``Eq 3 do
    throwError "Fully elaborated equality required for ordinary kernel reflexivity"
  match target.getAppArgs.toList with
  | [_,left,_] =>
    let proof ← mkEqRefl left
    goal.assign proof
    replaceMainGoal []
  | _ => throwError "Unexpected equality arity"
private def readCode (b : Option Bool) : Nat :=
  match b with | none=>0 | some false=>1 | some true=>2
private theorem resolve_small (k target m : Nat) (bound : target<239) :
    resolveCode k target m=(CertificateGuardClosure.machine k).stateCount+target := by
  interval_cases target <;> rfl
private theorem changed_bound (op m : Nat) : changeMode op m<144 := by
  dsimp only [changeMode]
  split <;> change _%144<144 <;> exact Nat.mod_lt _ (by decide)
private theorem op0 (m : Nat) (hm : m<144) : changeMode 0 m=m := by
  change m%144=m
  exact Nat.mod_eq_of_lt hm
private def evalTail (k m : Nat) (row : Nat × Nat × Nat × Nat) : Nat × Nat × Option Bool × Move :=
  let next:=changeMode row.2.2.2 m
  (resolveCode k row.1 next,next,writeSymbol row.2.1 m,moveDirection row.2.2.1)
private def tailWith (codes : Array (Nat × Nat × Nat × Nat)) (k q m : Nat) (b : Option Bool) :
    Nat × Nat × Option Bool × Move :=
  let sym:=readCode b
  evalTail k m (codes[q*3+sym]?.getD (239,0,1,5))
private theorem tail_def (k q m : Nat) (b : Option Bool) : tailStep k q m b=tailWith rom k q m b := by run_tac ordinaryKernelRefl
private theorem literal_row (k q m target write direction op : Nat) (b : Option Bool)
    (hq : q<239) (hm : m<144) (ht : target<239)
    (cell : rom[q*3+readCode b]?=
      some (target,write,direction,op)) :
    (machine k).step (np k ((CertificateGuardClosure.machine k).stateCount+q) m) b=
      (np k ((CertificateGuardClosure.machine k).stateCount+target) (changeMode op m),
        writeSymbol write m,moveDirection direction) := by
  rw [expanded k q m b hq hm,tail_def]
  generalize hc : rom=codes at cell ⊢
  have selected : (codes[q*3+readCode b]?).getD
      (239,0,1,5)=(target,write,direction,op) :=
    congrArg (fun x : Option (Nat × Nat × Nat × Nat)=>x.getD (239,0,1,5)) cell
  have evaluation : tailWith codes k q m b=evalTail k m (target,write,direction,op) := by
    dsimp only [tailWith]
    rw [selected]
  rw [evaluation]
  dsimp only [evalTail]
  rw [resolve_small k target (changeMode op m) ht]
  have ha : (CertificateGuardClosure.machine k).stateCount+target ≠ (CertificateGuardClosure.machine k).accept.val := by
    have h:=(CertificateGuardClosure.machine k).accept.isLt;omega
  have hr : (CertificateGuardClosure.machine k).stateCount+target ≠ (CertificateGuardClosure.machine k).reject.val := by
    have h:=(CertificateGuardClosure.machine k).reject.isLt;omega
  rw [if_neg (by tauto : ¬(_ ∨ _))]
private theorem cell_0 : rom[0]?=some (1,0,0,0) := by run_tac ordinaryKernelRefl
private theorem cell_356 : rom[356]?=some (118,2,0,0) := by run_tac ordinaryKernelRefl
private theorem cell_715 : rom[715]?=some (239,1,1,5) := by run_tac ordinaryKernelRefl
private theorem cell_716 : rom[716]?=some (239,2,1,5) := by run_tac ordinaryKernelRefl
#print axioms pack_type
#print axioms rom_type
#print axioms resolve_small
#print axioms changed_bound
#print axioms literal_row
#print axioms cell_0
#print axioms cell_356
#print axioms cell_715
#print axioms cell_716
end VirtualFinalClosure.Native
