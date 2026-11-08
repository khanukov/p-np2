import VirtualFinalClosure.SourceReturn
namespace VirtualFinalClosure.ModeRows
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.Wire","VirtualFinalClosure.Wire","native_step","expanded",(1:Nat)),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","tail_def","tailDef",1),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","tailWith","tailWith",0),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","evalTail","evalTail",0),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","readCode","readCode",0),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","op0","mode0",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","pack","pack",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","romPin","rom",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","resolve","resolveCode",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","changeMeta","changeMode",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","symbol","writeSymbol",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","direction","moveDirection",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","mode","sourceMode",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","flag","flag",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","phase","phase",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","seen","seen",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","bad","bad",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","encodeMeta","encodeMode",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","cellTac","cellTac",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0)] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong finite mode row declaration {n}"
      logInfo m!"private-term|{n}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique finite mode row term {mod}/{key}"
private theorem resolved_row (k q m code target write direction op : Nat) (b : Option Bool)
    (hq : q<239) (hm : m<144)
    (cell : rom[q*3+readCode b]?=some (code,write,direction,op))
    (resolution : resolveCode k code (changeMode op m)=(CertificateGuardClosure.machine k).stateCount+target) :
    (machine k).step (nc k q m) b=
      (nc k target (changeMode op m),writeSymbol write m,moveDirection direction) := by
  dsimp only [nc]
  rw [expanded k q m b hq hm,tailDef]
  generalize hc : rom=codes at cell ⊢
  have selected : (codes[q*3+readCode b]?).getD (239,0,1,5)=(code,write,direction,op) :=
    congrArg (fun x : Option (Nat × Nat × Nat × Nat)=>x.getD (239,0,1,5)) cell
  have evaluation : tailWith codes k q m b=evalTail k m (code,write,direction,op) := by
    dsimp only [tailWith]
    rw [selected]
  rw [evaluation]
  dsimp only [evalTail]
  rw [resolution]
  have ha : (CertificateGuardClosure.machine k).stateCount+target ≠ (CertificateGuardClosure.machine k).accept.val := by
    have h:=(CertificateGuardClosure.machine k).accept.isLt;omega
  have hr : (CertificateGuardClosure.machine k).stateCount+target ≠ (CertificateGuardClosure.machine k).reject.val := by
    have h:=(CertificateGuardClosure.machine k).reject.isLt;omega
  rw [if_neg (by tauto : ¬(_ ∨ _))]
private theorem find_first (k m : Nat) (hm : m<144) (eof : sourceMode m=2) :
    (machine k).step (nc k 17 m) none=(nc k 18 m,none,.stay) := by
  have resolution : resolveCode k 241 (changeMode 0 m)=(CertificateGuardClosure.machine k).stateCount+18 := by
    rw [mode0 m hm]
    change _+(if sourceMode m=2 then 18 else 19)=_
    rw [if_pos eof]
  have row:=resolved_row k 17 m 241 18 0 1 0 none (by decide) hm (by run_tac cellTac 51) resolution
  rw [mode0 m hm] at row
  exact row
private theorem find_later (k m : Nat) (hm : m<144) (occupied : sourceMode m≠2) :
    (machine k).step (nc k 17 m) none=(nc k 19 m,none,.stay) := by
  have resolution : resolveCode k 241 (changeMode 0 m)=(CertificateGuardClosure.machine k).stateCount+19 := by
    rw [mode0 m hm]
    change _+(if sourceMode m=2 then 18 else 19)=_
    rw [if_neg occupied]
  have row:=resolved_row k 17 m 241 19 0 1 0 none (by decide) hm (by run_tac cellTac 51) resolution
  rw [mode0 m hm] at row
  exact row
private theorem carried_write (m : Nat) (b : Bool) (bit : sourceMode m=(if b then 1 else 0)) :
    writeSymbol 3 m=some b := by
  cases b <;> dsimp only [writeSymbol] <;> rw [bit] <;> decide
private theorem lifted_mode (m : Nat) (b : Bool) :
    sourceMode (changeMode (if b then 2 else 1) m)=(if b then 1 else 0) := by
  cases b
  · change sourceMode (changeMode 1 m)=0
    dsimp only [changeMode,sourceMode,encodeMode,flag,phase,seen,bad]
    omega
  · change sourceMode (changeMode 2 m)=1
    dsimp only [changeMode,sourceMode,encodeMode,flag,phase,seen,bad]
    omega
private theorem changed_bound (m : Nat) (b : Bool) : changeMode (if b then 2 else 1) m<144 := by
  cases b <;> dsimp only [changeMode] <;> exact Nat.mod_lt _ (by decide)
#print axioms resolved_row
#print axioms find_first
#print axioms find_later
#print axioms carried_write
#print axioms lifted_mode
#print axioms changed_bound
end VirtualFinalClosure.ModeRows
