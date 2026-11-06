import SuffixCap.Kernel
import VirtualFinalClosure.Native
namespace VirtualFinalClosure.CountedRows
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic Meta
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (key,aliasName,kind) in [("codes","codes",(0:Nat)),("lookup","lookup",1),("decode_row","decodeRow",1)] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith "_private.SuffixCap.Rows." && n.toString.endsWith (".SuffixCap."++key)
    match found with
    | [(n,ci)]=>
      let actual : Nat:=match ci with | .thmInfo _=>1 | .defnInfo _=>0 | _=>9
      unless actual=kind do throwError "Wrong counted row interface {n}"
      logInfo m!"private-term|{n}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique counted row interface {key}"
  let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith "_private.VirtualFinalClosure.Native." && n.toString.endsWith ".VirtualFinalClosure.Native.ordinaryKernelRefl"
  match found with
  | [(n,.defnInfo ci)]=>
    logInfo m!"private-term|{n}|kind=definition|type={ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit `kernelRefl n::st.openDecls}
  | _=>throwError "Nonunique counted entry reflexivity interface"
private theorem entry (k : Nat) (b : Option Bool) :
    (Cursor.machine k).step (Cursor.q k 58) b=(Cursor.q k 64,b,.stay):=by
  cases b with
  | none=>run_tac kernelRefl
  | some v=>exact (SuffixCap.entry_rows k v).1
private theorem empty (k : Nat) :
    (Cursor.machine k).step (Cursor.q k 64) none=(Cursor.q k 40,none,.stay):=by
  have got : (codes k)[0]?=some 361:=by rw [lookup k 0 (by omega)];rfl
  exact decodeRow k 64 361 none (by omega) (by omega) (by omega) (by omega) (by omega) got
/-- Exhaustive native counting rows. The EOF route65..67 is not part of the
physical source58 branch, and the literal graph proves it is never entered. -/
private theorem row (k i : Nat) (b : Option Bool)
    (allowed : i=58 ∨ i=64 ∨ 68≤ i ∧ i<98) :
    ((Cursor.machine k).step (Cursor.q k i) b).1.val=40 ∨
      ((Cursor.machine k).step (Cursor.q k i) b).1.val=64 ∨
      68≤((Cursor.machine k).step (Cursor.q k i) b).1.val ∧
        ((Cursor.machine k).step (Cursor.q k i) b).1.val≤98:=by
  rcases allowed with rfl|rfl|⟨lo,hi⟩
  · rw [entry]
    right;left
    change 64%Cursor.stateCount k=64
    exact Nat.mod_eq_of_lt (by unfold Cursor.stateCount;omega)
  · cases b with
    | none=>rw [empty];left;exact Nat.mod_eq_of_lt (by unfold Cursor.stateCount;omega)
    | some v=>
      rw [(SuffixCap.entry_rows k v).2]
      cases v <;> simp only [Bool.false_eq_true,ite_false,ite_true,Cursor.q]
      all_goals rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount;omega)]
      all_goals omega
  · interval_cases i
    all_goals cases b
    all_goals try (rename_i v;cases v)
    run_tac do
      let env ← getEnv
      let pins:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith "_private.SuffixCap.Rows."
      for g in ← getGoals do
        setGoals [g]
        withMainContext do
          let target ← instantiateMVars (← g.getType)
          let some call:=target.find? (fun e=>e.isAppOfArity ``UniformTM.step 3)
            | throwError "Missing fully applied native counting step"
          let [_,state,bit]:=call.getAppArgs.toList
            | throwError "Unexpected native counting step arity"
          unless state.isAppOfArity ``Cursor.q 2 do throwError "Counting source is not Cursor.q"
          let [_,idx]:=state.getAppArgs.toList | throwError "Unexpected Cursor.q arity"
          let some i ← getNatValue? (← whnf idx) | throwError "Counting index is not literal"
          let sym ← do
            let bit ← whnf bit
            if bit.isAppOfArity ``Option.none 1 then pure 0 else
              if bit.isAppOfArity ``Option.some 2 then
                match bit.getAppArgs.toList with
                | [_,v]=>
                  if v.isConstOf ``Bool.false then pure 1 else
                    if v.isConstOf ``Bool.true then pure 2 else throwError "Nonliteral SomeBool"
                | _=>throwError "Unexpected Some arity"
              else throwError "Nonliteral counting symbol"
          let key:=".SuffixCap.pin_"++toString i++"_"++toString sym
          let found:=pins.filter fun (n,_)=>n.toString.endsWith key
          let [(n,.thmInfo ci)]:=found | throwError "Nonunique counted literal row {key}"
          logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
          let id:=mkIdent n
          let kv:=mkIdent `k
          evalTactic (← `(tactic| rw [$id:ident $kv:ident]))
          evalTactic (← `(tactic| dsimp only [Cursor.q]))
          evalTactic (← `(tactic| rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount;omega)]))
          evalTactic (← `(tactic| omega))
#print axioms entry
#print axioms empty
#print axioms row
end VirtualFinalClosure.CountedRows
