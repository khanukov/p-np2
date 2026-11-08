import VirtualFinalClosure.MarkerState
namespace VirtualFinalClosure.MetaFields
open Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for key in ["flag","mode","phase","seen","bad","encodeMeta","changeMeta"] do
    let found:=env.constants.toList.filter fun (name,_)=>
      name.toString.startsWith "_private.VirtualFinalClosure.ElasticMachine." &&
      name.toString.endsWith (".VirtualFinalClosure.Elastic."++key)
    match found with
    | [(name,.defnInfo ci)]=>
      logInfo m!"private-term|{name}|kind=definition|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous key) name::st.openDecls}
    | _=>throwError "Nonunique actual finite-mode component {key}"
private theorem reconstruct (m : Nat) (hm : m < 144) :
    m=flag m+4*mode m+12*phase m+36*seen m+72*bad m := by
  dsimp only [flag,mode,phase,seen,bad]
  omega
private theorem determined (m v : Nat) (hm : m < 144) (hv : v < 144)
    (f : flag m=flag v) (b : mode m=mode v) (p : phase m=phase v)
    (s : seen m=seen v) (d : bad m=bad v) : m=v := by
  rw [reconstruct m hm,reconstruct v hv,f,b,p,s,d]
/-- Native metadata operations preserve the actual paid-table accumulator.
This is a finite-control fact, not the still-open whole paid-orbit invariant. -/
private theorem flag_preserved (m op : Nat) : flag (changeMeta op m)=flag m := by
  dsimp only [changeMeta]
  split <;> dsimp only [flag,encodeMeta,mode,phase,seen,bad] <;> omega
#print axioms reconstruct
#print axioms determined
#print axioms flag_preserved
end VirtualFinalClosure.MetaFields
