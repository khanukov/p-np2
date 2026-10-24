import VirtualFinalClosure.GenericRoutes
import VirtualFinalClosure.ModeRows
namespace VirtualFinalClosure.GuardForwardRows
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","literal_row","literalRow",1),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","op0","mode0",1),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","changed_bound","changedBound",1),
      ("VirtualFinalClosure.ModeRows","VirtualFinalClosure.ModeRows","resolved_row","resolvedRow",1),
      ("VirtualFinalClosure.ModeRows","VirtualFinalClosure.ModeRows","carried_write","carriedWrite",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","mode","sourceMode",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","resolve","resolveCode",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","changeMeta","changeMode",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","cellTac","cellTac",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0) ] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong literal elastic grow row term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique literal elastic grow row term {mod}/{key}"
private theorem row158_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 158 m) (none)=(nc k 159 m,none,.left) := by
  have row:=literalRow k 158 m 159 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 474)
  rw [mode0 m hm] at row
  exact row
private theorem row159_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 159 m) (some false)=(nc k 160 m,some false,.left) := by
  have row:=literalRow k 159 m 160 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 478)
  rw [mode0 m hm] at row
  exact row
private theorem row160_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 160 m) (none)=(nc k 160 m,none,.left) := by
  have row:=literalRow k 160 m 160 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 480)
  rw [mode0 m hm] at row
  exact row
private theorem row160_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 160 m) (some true)=(nc k 161 m,some true,.left) := by
  have row:=literalRow k 160 m 161 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 482)
  rw [mode0 m hm] at row
  exact row
private theorem row161_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 161 m) (none)=(nc k 162 m,none,.left) := by
  have row:=literalRow k 161 m 162 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 483)
  rw [mode0 m hm] at row
  exact row
private theorem row161_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 161 m) (some true)=(nc k 161 m,some true,.left) := by
  have row:=literalRow k 161 m 161 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 485)
  rw [mode0 m hm] at row
  exact row
private theorem row162_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 162 m) (none)=(nc k 163 m,none,.stay) := by
  have row:=literalRow k 162 m 163 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 486)
  rw [mode0 m hm] at row
  exact row
private theorem row162_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 162 m) (some false)=(nc k 162 m,some false,.left) := by
  have row:=literalRow k 162 m 162 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 487)
  rw [mode0 m hm] at row
  exact row
private theorem row162_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 162 m) (some true)=(nc k 162 m,some true,.left) := by
  have row:=literalRow k 162 m 162 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 488)
  rw [mode0 m hm] at row
  exact row
private theorem row163_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 163 m) (none)=(nc k 164 m,none,.left) := by
  have row:=literalRow k 163 m 164 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 489)
  rw [mode0 m hm] at row
  exact row
private theorem row164_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 164 m) (none)=(nc k 165 m,none,.stay) := by
  have row:=literalRow k 164 m 165 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 492)
  rw [mode0 m hm] at row
  exact row
private theorem row164_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 164 m) (some false)=(nc k 164 m,some false,.left) := by
  have row:=literalRow k 164 m 164 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 493)
  rw [mode0 m hm] at row
  exact row
private theorem row164_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 164 m) (some true)=(nc k 164 m,some true,.left) := by
  have row:=literalRow k 164 m 164 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 494)
  rw [mode0 m hm] at row
  exact row
private theorem row166_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 166 m) (none)=(nc k 172 m,none,.stay) := by
  have row:=literalRow k 166 m 172 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 498)
  rw [mode0 m hm] at row
  exact row
private theorem row167_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 167 m) (none)=(nc k 168 m,none,.left) := by
  have row:=literalRow k 167 m 168 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 501)
  rw [mode0 m hm] at row
  exact row
private theorem row168_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 168 m) (none)=(nc k 169 m,none,.stay) := by
  have row:=literalRow k 168 m 169 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 504)
  rw [mode0 m hm] at row
  exact row
private theorem row168_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 168 m) (some false)=(nc k 168 m,some false,.left) := by
  have row:=literalRow k 168 m 168 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 505)
  rw [mode0 m hm] at row
  exact row
private theorem row168_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 168 m) (some true)=(nc k 168 m,some true,.left) := by
  have row:=literalRow k 168 m 168 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 506)
  rw [mode0 m hm] at row
  exact row
private theorem row170_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 170 m) (none)=(nc k 172 (changeMode 3 m),none,.stay) := by
  have row:=literalRow k 170 m 172 0 1 3 (none) (by decide) hm (by decide) (by run_tac cellTac 510)
  exact row
private theorem row170_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 170 m) (some false)=(nc k 171 (changeMode 1 m),none,.right) := by
  have row:=literalRow k 170 m 171 0 2 1 (some false) (by decide) hm (by decide) (by run_tac cellTac 511)
  exact row
private theorem row170_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 170 m) (some true)=(nc k 171 (changeMode 2 m),none,.right) := by
  have row:=literalRow k 170 m 171 0 2 2 (some true) (by decide) hm (by decide) (by run_tac cellTac 512)
  exact row
private theorem row171_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 171 m) (none)=(nc k 172 m,none,.stay) := by
  have row:=literalRow k 171 m 172 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 513)
  rw [mode0 m hm] at row
  exact row
private theorem row171_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 171 m) (some false)=(nc k 171 m,some false,.right) := by
  have row:=literalRow k 171 m 171 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 514)
  rw [mode0 m hm] at row
  exact row
private theorem row171_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 171 m) (some true)=(nc k 171 m,some true,.right) := by
  have row:=literalRow k 171 m 171 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 515)
  rw [mode0 m hm] at row
  exact row
private theorem row172_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 172 m) (none)=(nc k 173 m,none,.right) := by
  have row:=literalRow k 172 m 173 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 516)
  rw [mode0 m hm] at row
  exact row
private theorem row173_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 173 m) (none)=(nc k 174 m,none,.stay) := by
  have row:=literalRow k 173 m 174 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 519)
  rw [mode0 m hm] at row
  exact row
private theorem row173_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 173 m) (some false)=(nc k 173 m,some false,.right) := by
  have row:=literalRow k 173 m 173 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 520)
  rw [mode0 m hm] at row
  exact row
private theorem row173_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 173 m) (some true)=(nc k 173 m,some true,.right) := by
  have row:=literalRow k 173 m 173 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 521)
  rw [mode0 m hm] at row
  exact row
private theorem row174_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 174 m) (none)=(nc k 175 m,none,.right) := by
  have row:=literalRow k 174 m 175 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 522)
  rw [mode0 m hm] at row
  exact row
private theorem row175_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 175 m) (none)=(nc k 176 m,none,.stay) := by
  have row:=literalRow k 175 m 176 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 525)
  rw [mode0 m hm] at row
  exact row
private theorem row175_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 175 m) (some false)=(nc k 175 m,some false,.right) := by
  have row:=literalRow k 175 m 175 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 526)
  rw [mode0 m hm] at row
  exact row
private theorem row175_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 175 m) (some true)=(nc k 175 m,some true,.right) := by
  have row:=literalRow k 175 m 175 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 527)
  rw [mode0 m hm] at row
  exact row
private theorem row176_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 176 m) (none)=(nc k 177 m,none,.right) := by
  have row:=literalRow k 176 m 177 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 528)
  rw [mode0 m hm] at row
  exact row
private theorem row177_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 177 m) (none)=(nc k 178 m,none,.right) := by
  have row:=literalRow k 177 m 178 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 531)
  rw [mode0 m hm] at row
  exact row
private theorem row177_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 177 m) (some true)=(nc k 177 m,some true,.right) := by
  have row:=literalRow k 177 m 177 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 533)
  rw [mode0 m hm] at row
  exact row
private theorem row178_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 178 m) (none)=(nc k 178 m,none,.right) := by
  have row:=literalRow k 178 m 178 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 534)
  rw [mode0 m hm] at row
  exact row
private theorem row178_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 178 m) (some false)=(nc k 179 m,some false,.right) := by
  have row:=literalRow k 178 m 179 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 535)
  rw [mode0 m hm] at row
  exact row
private theorem row162 (k m : Nat) (hm : m < 144) (b : Bool) :
    (machine k).step (nc k 162 m) (some b)=(nc k 162 m,some b,.left) := by
  cases b
  · exact row162_1 k m hm
  · exact row162_2 k m hm
private theorem row164 (k m : Nat) (hm : m < 144) (b : Bool) :
    (machine k).step (nc k 164 m) (some b)=(nc k 164 m,some b,.left) := by
  cases b
  · exact row164_1 k m hm
  · exact row164_2 k m hm
private theorem row168 (k m : Nat) (hm : m < 144) (b : Bool) :
    (machine k).step (nc k 168 m) (some b)=(nc k 168 m,some b,.left) := by
  cases b
  · exact row168_1 k m hm
  · exact row168_2 k m hm
private theorem row171 (k m : Nat) (hm : m < 144) (b : Bool) :
    (machine k).step (nc k 171 m) (some b)=(nc k 171 m,some b,.right) := by
  cases b
  · exact row171_1 k m hm
  · exact row171_2 k m hm
private theorem row173 (k m : Nat) (hm : m < 144) (b : Bool) :
    (machine k).step (nc k 173 m) (some b)=(nc k 173 m,some b,.right) := by
  cases b
  · exact row173_1 k m hm
  · exact row173_2 k m hm
private theorem row175 (k m : Nat) (hm : m < 144) (b : Bool) :
    (machine k).step (nc k 175 m) (some b)=(nc k 175 m,some b,.right) := by
  cases b
  · exact row175_1 k m hm
  · exact row175_2 k m hm
private theorem dispatch (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 165 m) none=(nc k (if sourceMode m=2 then 166 else 167) m,none,.stay) := by
  have resolution : resolveCode k 245 (changeMode 0 m)=
      (CertificateGuardClosure.machine k).stateCount+(if sourceMode m=2 then 166 else 167):=by
    rw [mode0 m hm];rfl
  have row:=resolvedRow k 165 m 245 (if sourceMode m=2 then 166 else 167) 0 1 0 none
    (by decide) hm (by run_tac cellTac 495) resolution
  rw [mode0 m hm] at row
  exact row
private theorem restore (k m : Nat) (hm : m < 144) (b : Bool)
    (bit : sourceMode m=(if b then 1 else 0)) :
    (machine k).step (nc k 169 m) none=(nc k 170 m,some b,.right) := by
  have row:=literalRow k 169 m 170 3 2 0 none (by decide) hm (by decide) (by run_tac cellTac 507)
  rw [mode0 m hm,carriedWrite m b bit] at row
  exact row
private theorem lift (k m : Nat) (hm : m < 144) (b : Bool) :
    (machine k).step (nc k 170 m) (some b)=
      (nc k 171 (changeMode (if b then 2 else 1) m),none,.right) := by
  cases b
  · exact row170_1 k m hm
  · exact row170_2 k m hm
#print axioms row158_0
#print axioms row159_1
#print axioms row160_0
#print axioms row160_2
#print axioms row161_0
#print axioms row161_2
#print axioms row162_0
#print axioms row162_1
#print axioms row162_2
#print axioms row163_0
#print axioms row164_0
#print axioms row164_1
#print axioms row164_2
#print axioms row166_0
#print axioms row167_0
#print axioms row168_0
#print axioms row168_1
#print axioms row168_2
#print axioms row170_0
#print axioms row170_1
#print axioms row170_2
#print axioms row171_0
#print axioms row171_1
#print axioms row171_2
#print axioms row172_0
#print axioms row173_0
#print axioms row173_1
#print axioms row173_2
#print axioms row174_0
#print axioms row175_0
#print axioms row175_1
#print axioms row175_2
#print axioms row176_0
#print axioms row177_0
#print axioms row177_2
#print axioms row178_0
#print axioms row178_1
#print axioms row162
#print axioms row164
#print axioms row168
#print axioms row171
#print axioms row173
#print axioms row175
#print axioms dispatch
#print axioms restore
#print axioms lift
end VirtualFinalClosure.GuardForwardRows
