import VirtualFinalClosure.GenericRoutes
import VirtualFinalClosure.ModeRows
import VirtualFinalClosure.GuardFlags
namespace VirtualFinalClosure.GuardFinishRows
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
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","symbol","writeSymbol",0) ] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong literal elastic grow row term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique literal elastic grow row term {mod}/{key}"
private theorem row187_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 187 m) (none)=(nc k 188 m,none,.left) := by
  have row:=literalRow k 187 m 188 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 561)
  rw [mode0 m hm] at row
  exact row
private theorem row188_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 188 m) (some false)=(nc k 189 m,some false,.left) := by
  have row:=literalRow k 188 m 189 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 565)
  rw [mode0 m hm] at row
  exact row
private theorem row189_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 189 m) (none)=(nc k 189 m,none,.left) := by
  have row:=literalRow k 189 m 189 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 567)
  rw [mode0 m hm] at row
  exact row
private theorem row189_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 189 m) (some true)=(nc k 190 m,some true,.left) := by
  have row:=literalRow k 189 m 190 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 569)
  rw [mode0 m hm] at row
  exact row
private theorem row190_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 190 m) (none)=(nc k 191 m,none,.left) := by
  have row:=literalRow k 190 m 191 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 570)
  rw [mode0 m hm] at row
  exact row
private theorem row190_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 190 m) (some true)=(nc k 190 m,some true,.left) := by
  have row:=literalRow k 190 m 190 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 572)
  rw [mode0 m hm] at row
  exact row
private theorem row191_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 191 m) (none)=(nc k 192 m,none,.stay) := by
  have row:=literalRow k 191 m 192 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 573)
  rw [mode0 m hm] at row
  exact row
private theorem row191_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 191 m) (some false)=(nc k 191 m,some false,.left) := by
  have row:=literalRow k 191 m 191 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 574)
  rw [mode0 m hm] at row
  exact row
private theorem row191_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 191 m) (some true)=(nc k 191 m,some true,.left) := by
  have row:=literalRow k 191 m 191 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 575)
  rw [mode0 m hm] at row
  exact row
private theorem row192_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 192 m) (none)=(nc k 193 m,none,.left) := by
  have row:=literalRow k 192 m 193 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 576)
  rw [mode0 m hm] at row
  exact row
private theorem row193_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 193 m) (none)=(nc k 194 m,none,.stay) := by
  have row:=literalRow k 193 m 194 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 579)
  rw [mode0 m hm] at row
  exact row
private theorem row193_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 193 m) (some false)=(nc k 193 m,some false,.left) := by
  have row:=literalRow k 193 m 193 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 580)
  rw [mode0 m hm] at row
  exact row
private theorem row193_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 193 m) (some true)=(nc k 193 m,some true,.left) := by
  have row:=literalRow k 193 m 193 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 581)
  rw [mode0 m hm] at row
  exact row
private theorem row195_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 195 m) (none)=(nc k 196 m,none,.left) := by
  have row:=literalRow k 195 m 196 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 585)
  rw [mode0 m hm] at row
  exact row
private theorem row196_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 196 m) (none)=(nc k 197 m,none,.stay) := by
  have row:=literalRow k 196 m 197 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 588)
  rw [mode0 m hm] at row
  exact row
private theorem row196_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 196 m) (some false)=(nc k 196 m,some false,.left) := by
  have row:=literalRow k 196 m 196 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 589)
  rw [mode0 m hm] at row
  exact row
private theorem row196_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 196 m) (some true)=(nc k 196 m,some true,.left) := by
  have row:=literalRow k 196 m 196 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 590)
  rw [mode0 m hm] at row
  exact row
private theorem row198_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 198 m) (none)=(nc k 231 m,none,.stay) := by
  have row:=literalRow k 198 m 231 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 594)
  rw [mode0 m hm] at row
  exact row
private theorem row198_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 198 m) (some false)=(nc k 198 m,some false,.right) := by
  have row:=literalRow k 198 m 198 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 595)
  rw [mode0 m hm] at row
  exact row
private theorem row198_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 198 m) (some true)=(nc k 198 (changeMode 5 m),some true,.right) := by
  have row:=literalRow k 198 m 198 2 2 5 (some true) (by decide) hm (by decide) (by run_tac cellTac 596)
  exact row
private theorem row223_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 223 m) (none)=(nc k 224 m,none,.left) := by
  have row:=literalRow k 223 m 224 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 669)
  rw [mode0 m hm] at row
  exact row
private theorem row224_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 224 m) (some false)=(nc k 225 m,some false,.left) := by
  have row:=literalRow k 224 m 225 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 673)
  rw [mode0 m hm] at row
  exact row
private theorem row225_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 225 m) (none)=(nc k 225 m,none,.left) := by
  have row:=literalRow k 225 m 225 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 675)
  rw [mode0 m hm] at row
  exact row
private theorem row225_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 225 m) (some true)=(nc k 226 m,some true,.left) := by
  have row:=literalRow k 225 m 226 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 677)
  rw [mode0 m hm] at row
  exact row
private theorem row226_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 226 m) (none)=(nc k 227 m,none,.left) := by
  have row:=literalRow k 226 m 227 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 678)
  rw [mode0 m hm] at row
  exact row
private theorem row226_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 226 m) (some true)=(nc k 226 m,some true,.left) := by
  have row:=literalRow k 226 m 226 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 680)
  rw [mode0 m hm] at row
  exact row
private theorem row227_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 227 m) (none)=(nc k 228 m,none,.stay) := by
  have row:=literalRow k 227 m 228 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 681)
  rw [mode0 m hm] at row
  exact row
private theorem row227_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 227 m) (some false)=(nc k 227 m,some false,.left) := by
  have row:=literalRow k 227 m 227 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 682)
  rw [mode0 m hm] at row
  exact row
private theorem row227_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 227 m) (some true)=(nc k 227 m,some true,.left) := by
  have row:=literalRow k 227 m 227 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 683)
  rw [mode0 m hm] at row
  exact row
private theorem row228_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 228 m) (none)=(nc k 229 m,none,.left) := by
  have row:=literalRow k 228 m 229 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 684)
  rw [mode0 m hm] at row
  exact row
private theorem row229_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 229 m) (none)=(nc k 230 m,none,.stay) := by
  have row:=literalRow k 229 m 230 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 687)
  rw [mode0 m hm] at row
  exact row
private theorem row229_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 229 m) (some false)=(nc k 229 m,some false,.left) := by
  have row:=literalRow k 229 m 229 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 688)
  rw [mode0 m hm] at row
  exact row
private theorem row229_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 229 m) (some true)=(nc k 229 m,some true,.left) := by
  have row:=literalRow k 229 m 229 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 689)
  rw [mode0 m hm] at row
  exact row
private theorem row230_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 230 m) (none)=(nc k 194 (changeMode 5 m),none,.stay) := by
  have row:=literalRow k 230 m 194 0 1 5 (none) (by decide) hm (by decide) (by run_tac cellTac 690)
  exact row
private theorem row231_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 231 m) (none)=(nc k 232 m,none,.right) := by
  have row:=literalRow k 231 m 232 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 693)
  rw [mode0 m hm] at row
  exact row
private theorem row232_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 232 m) (none)=(nc k 233 m,none,.stay) := by
  have row:=literalRow k 232 m 233 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 696)
  rw [mode0 m hm] at row
  exact row
private theorem row232_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 232 m) (some false)=(nc k 232 m,some false,.right) := by
  have row:=literalRow k 232 m 232 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 697)
  rw [mode0 m hm] at row
  exact row
private theorem row232_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 232 m) (some true)=(nc k 232 m,some true,.right) := by
  have row:=literalRow k 232 m 232 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 698)
  rw [mode0 m hm] at row
  exact row
private theorem row233_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 233 m) (none)=(nc k 234 m,none,.right) := by
  have row:=literalRow k 233 m 234 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 699)
  rw [mode0 m hm] at row
  exact row
private theorem row234_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 234 m) (none)=(nc k 235 m,none,.stay) := by
  have row:=literalRow k 234 m 235 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 702)
  rw [mode0 m hm] at row
  exact row
private theorem row234_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 234 m) (some false)=(nc k 234 m,some false,.right) := by
  have row:=literalRow k 234 m 234 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 703)
  rw [mode0 m hm] at row
  exact row
private theorem row234_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 234 m) (some true)=(nc k 234 m,some true,.right) := by
  have row:=literalRow k 234 m 234 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 704)
  rw [mode0 m hm] at row
  exact row
private theorem row235_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 235 m) (none)=(nc k 236 m,none,.right) := by
  have row:=literalRow k 235 m 236 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 705)
  rw [mode0 m hm] at row
  exact row
private theorem row236_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 236 m) (none)=(nc k 237 m,none,.right) := by
  have row:=literalRow k 236 m 237 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 708)
  rw [mode0 m hm] at row
  exact row
private theorem row236_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 236 m) (some true)=(nc k 236 m,some true,.right) := by
  have row:=literalRow k 236 m 236 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 710)
  rw [mode0 m hm] at row
  exact row
private theorem row237_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 237 m) (none)=(nc k 237 m,none,.right) := by
  have row:=literalRow k 237 m 237 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 711)
  rw [mode0 m hm] at row
  exact row
private theorem row237_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 237 m) (some false)=(nc k 238 m,some false,.right) := by
  have row:=literalRow k 237 m 238 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 712)
  rw [mode0 m hm] at row
  exact row
private theorem row191 (k m : Nat) (hm : m < 144) (b : Bool) :
    (machine k).step (nc k 191 m) (some b)=(nc k 191 m,some b,.left) := by
  cases b
  · exact row191_1 k m hm
  · exact row191_2 k m hm
private theorem row193 (k m : Nat) (hm : m < 144) (b : Bool) :
    (machine k).step (nc k 193 m) (some b)=(nc k 193 m,some b,.left) := by
  cases b
  · exact row193_1 k m hm
  · exact row193_2 k m hm
private theorem row196 (k m : Nat) (hm : m < 144) (b : Bool) :
    (machine k).step (nc k 196 m) (some b)=(nc k 196 m,some b,.left) := by
  cases b
  · exact row196_1 k m hm
  · exact row196_2 k m hm
private theorem row227 (k m : Nat) (hm : m < 144) (b : Bool) :
    (machine k).step (nc k 227 m) (some b)=(nc k 227 m,some b,.left) := by
  cases b
  · exact row227_1 k m hm
  · exact row227_2 k m hm
private theorem row229 (k m : Nat) (hm : m < 144) (b : Bool) :
    (machine k).step (nc k 229 m) (some b)=(nc k 229 m,some b,.left) := by
  cases b
  · exact row229_1 k m hm
  · exact row229_2 k m hm
private theorem row232 (k m : Nat) (hm : m < 144) (b : Bool) :
    (machine k).step (nc k 232 m) (some b)=(nc k 232 m,some b,.right) := by
  cases b
  · exact row232_1 k m hm
  · exact row232_2 k m hm
private theorem row234 (k m : Nat) (hm : m < 144) (b : Bool) :
    (machine k).step (nc k 234 m) (some b)=(nc k 234 m,some b,.right) := by
  cases b
  · exact row234_1 k m hm
  · exact row234_2 k m hm
private theorem dispatch (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 194 m) none=(nc k (if sourceMode m=2 then 231 else 195) m,none,.stay) := by
  have resolution : resolveCode k 246 (changeMode 0 m)=
      (CertificateGuardClosure.machine k).stateCount+(if sourceMode m=2 then 231 else 195):=by
    rw [mode0 m hm];rfl
  have row:=resolvedRow k 194 m 246 (if sourceMode m=2 then 231 else 195) 0 1 0 none
    (by decide) hm (by run_tac cellTac 582) resolution
  rw [mode0 m hm] at row
  exact row
private theorem restore (k m : Nat) (hm : m < 144) (b : Bool)
    (bit : sourceMode m=(if b then 1 else 0)) :
    (machine k).step (nc k 197 m) none=(nc k 198 (changeMode 8 m),some b,.right) := by
  have row:=literalRow k 197 m 198 3 2 8 none (by decide) hm (by decide) (by run_tac cellTac 591)
  rw [carriedWrite m b bit] at row
  exact row
private theorem scan (k m : Nat) (hm : m < 144) (b : Bool) :
    (machine k).step (nc k 198 m) (some b)=
      (nc k 198 (changeMode (if b then 5 else 0) m),some b,.right) := by
  cases b
  · have h:=row198_1 k m hm
    simpa only [Bool.false_eq_true,if_false,mode0 m hm] using h
  · exact row198_2 k m hm
#print axioms row187_0
#print axioms row188_1
#print axioms row189_0
#print axioms row189_2
#print axioms row190_0
#print axioms row190_2
#print axioms row191_0
#print axioms row191_1
#print axioms row191_2
#print axioms row192_0
#print axioms row193_0
#print axioms row193_1
#print axioms row193_2
#print axioms row195_0
#print axioms row196_0
#print axioms row196_1
#print axioms row196_2
#print axioms row198_0
#print axioms row198_1
#print axioms row198_2
#print axioms row223_0
#print axioms row224_1
#print axioms row225_0
#print axioms row225_2
#print axioms row226_0
#print axioms row226_2
#print axioms row227_0
#print axioms row227_1
#print axioms row227_2
#print axioms row228_0
#print axioms row229_0
#print axioms row229_1
#print axioms row229_2
#print axioms row230_0
#print axioms row231_0
#print axioms row232_0
#print axioms row232_1
#print axioms row232_2
#print axioms row233_0
#print axioms row234_0
#print axioms row234_1
#print axioms row234_2
#print axioms row235_0
#print axioms row236_0
#print axioms row236_2
#print axioms row237_0
#print axioms row237_1
#print axioms row191
#print axioms row193
#print axioms row196
#print axioms row227
#print axioms row229
#print axioms row232
#print axioms row234
#print axioms dispatch
#print axioms restore
#print axioms scan
end VirtualFinalClosure.GuardFinishRows
