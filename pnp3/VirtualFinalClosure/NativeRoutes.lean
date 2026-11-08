import VirtualFinalClosure.GenericRoutes
import VirtualFinalClosure.ModeRows
namespace VirtualFinalClosure.NativeRoutes
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("SmallIngress.Runtime","SmallIngress","Node","GNode",(2:Nat)),
      ("SmallIngress.Runtime","SmallIngress","Node.mk","node",3),
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",2),
      ("VirtualFinalClosure.GenericRoutes","VirtualFinalClosure.GenericRoutes","left_route","leftRoute",1),
      ("VirtualFinalClosure.GenericRoutes","VirtualFinalClosure.GenericRoutes","right_route","rightRoute",1),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","literal_row","literalRow",1),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","op0","mode0",1),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","cellTac","cellTac",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",0)] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong literal framed route declaration {n}"
      logInfo m!"private-term|{n}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique native route interface {mod}/{key}"
private theorem row31_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 31 m) (none)=(nc k 32 m,none,.left) := by
  have rr:=literalRow k 31 m 32 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 93)
  rw [mode0 m hm] at rr
  exact rr
private theorem row32_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 32 m) (some false)=(nc k 33 m,some false,.left) := by
  have rr:=literalRow k 32 m 33 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 97)
  rw [mode0 m hm] at rr
  exact rr
private theorem row33_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 33 m) (none)=(nc k 33 m,none,.left) := by
  have rr:=literalRow k 33 m 33 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 99)
  rw [mode0 m hm] at rr
  exact rr
private theorem row33_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 33 m) (some true)=(nc k 34 m,some true,.left) := by
  have rr:=literalRow k 33 m 34 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 101)
  rw [mode0 m hm] at rr
  exact rr
private theorem row34_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 34 m) (none)=(nc k 35 m,none,.left) := by
  have rr:=literalRow k 34 m 35 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 102)
  rw [mode0 m hm] at rr
  exact rr
private theorem row34_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 34 m) (some true)=(nc k 34 m,some true,.left) := by
  have rr:=literalRow k 34 m 34 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 104)
  rw [mode0 m hm] at rr
  exact rr
private theorem row35_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 35 m) (none)=(nc k 36 m,none,.stay) := by
  have rr:=literalRow k 35 m 36 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 105)
  rw [mode0 m hm] at rr
  exact rr
private theorem row35_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 35 m) (some false)=(nc k 35 m,some false,.left) := by
  have rr:=literalRow k 35 m 35 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 106)
  rw [mode0 m hm] at rr
  exact rr
private theorem row35_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 35 m) (some true)=(nc k 35 m,some true,.left) := by
  have rr:=literalRow k 35 m 35 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 107)
  rw [mode0 m hm] at rr
  exact rr
private theorem row36_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 36 m) (none)=(nc k 37 m,none,.left) := by
  have rr:=literalRow k 36 m 37 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 108)
  rw [mode0 m hm] at rr
  exact rr
private theorem row37_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 37 m) (none)=(nc k 38 m,none,.stay) := by
  have rr:=literalRow k 37 m 38 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 111)
  rw [mode0 m hm] at rr
  exact rr
private theorem row37_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 37 m) (some false)=(nc k 37 m,some false,.left) := by
  have rr:=literalRow k 37 m 37 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 112)
  rw [mode0 m hm] at rr
  exact rr
private theorem row37_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 37 m) (some true)=(nc k 37 m,some true,.left) := by
  have rr:=literalRow k 37 m 37 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 113)
  rw [mode0 m hm] at rr
  exact rr
private theorem row38_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 38 m) (none)=(nc k 39 m,none,.left) := by
  have rr:=literalRow k 38 m 39 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 114)
  rw [mode0 m hm] at rr
  exact rr
private theorem row39_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 39 m) (none)=(nc k 40 m,none,.stay) := by
  have rr:=literalRow k 39 m 40 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 117)
  rw [mode0 m hm] at rr
  exact rr
private theorem row39_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 39 m) (some false)=(nc k 39 m,some false,.left) := by
  have rr:=literalRow k 39 m 39 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 118)
  rw [mode0 m hm] at rr
  exact rr
private theorem row39_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 39 m) (some true)=(nc k 39 m,some true,.left) := by
  have rr:=literalRow k 39 m 39 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 119)
  rw [mode0 m hm] at rr
  exact rr
private theorem row41_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 41 m) (none)=(nc k 42 m,none,.right) := by
  have rr:=literalRow k 41 m 42 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 123)
  rw [mode0 m hm] at rr
  exact rr
private theorem row42_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 42 m) (none)=(nc k 43 m,none,.stay) := by
  have rr:=literalRow k 42 m 43 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 126)
  rw [mode0 m hm] at rr
  exact rr
private theorem row42_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 42 m) (some false)=(nc k 42 m,some false,.right) := by
  have rr:=literalRow k 42 m 42 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 127)
  rw [mode0 m hm] at rr
  exact rr
private theorem row42_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 42 m) (some true)=(nc k 42 m,some true,.right) := by
  have rr:=literalRow k 42 m 42 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 128)
  rw [mode0 m hm] at rr
  exact rr
private theorem row43_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 43 m) (none)=(nc k 44 m,none,.right) := by
  have rr:=literalRow k 43 m 44 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 129)
  rw [mode0 m hm] at rr
  exact rr
private theorem row44_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 44 m) (none)=(nc k 45 m,none,.stay) := by
  have rr:=literalRow k 44 m 45 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 132)
  rw [mode0 m hm] at rr
  exact rr
private theorem row44_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 44 m) (some false)=(nc k 44 m,some false,.right) := by
  have rr:=literalRow k 44 m 44 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 133)
  rw [mode0 m hm] at rr
  exact rr
private theorem row44_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 44 m) (some true)=(nc k 44 m,some true,.right) := by
  have rr:=literalRow k 44 m 44 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 134)
  rw [mode0 m hm] at rr
  exact rr
private theorem row45_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 45 m) (none)=(nc k 46 m,none,.right) := by
  have rr:=literalRow k 45 m 46 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 135)
  rw [mode0 m hm] at rr
  exact rr
private theorem row46_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 46 m) (none)=(nc k 47 m,none,.stay) := by
  have rr:=literalRow k 46 m 47 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 138)
  rw [mode0 m hm] at rr
  exact rr
private theorem row46_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 46 m) (some false)=(nc k 46 m,some false,.right) := by
  have rr:=literalRow k 46 m 46 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 139)
  rw [mode0 m hm] at rr
  exact rr
private theorem row46_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 46 m) (some true)=(nc k 46 m,some true,.right) := by
  have rr:=literalRow k 46 m 46 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 140)
  rw [mode0 m hm] at rr
  exact rr
private theorem row47_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 47 m) (none)=(nc k 48 m,none,.right) := by
  have rr:=literalRow k 47 m 48 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 141)
  rw [mode0 m hm] at rr
  exact rr
private theorem row48_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 48 m) (none)=(nc k 49 m,none,.right) := by
  have rr:=literalRow k 48 m 49 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 144)
  rw [mode0 m hm] at rr
  exact rr
private theorem row48_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 48 m) (some true)=(nc k 48 m,some true,.right) := by
  have rr:=literalRow k 48 m 48 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 146)
  rw [mode0 m hm] at rr
  exact rr
private theorem row49_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 49 m) (none)=(nc k 49 m,none,.right) := by
  have rr:=literalRow k 49 m 49 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 147)
  rw [mode0 m hm] at rr
  exact rr
private theorem row49_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 49 m) (some false)=(nc k 52 m,some false,.right) := by
  have rr:=literalRow k 49 m 52 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 148)
  rw [mode0 m hm] at rr
  exact rr
private theorem row51_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 51 m) (none)=(nc k 231 m,none,.stay) := by
  have rr:=literalRow k 51 m 231 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 153)
  rw [mode0 m hm] at rr
  exact rr
private theorem row51_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 51 m) (some false)=(nc k 51 m,some false,.right) := by
  have rr:=literalRow k 51 m 51 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 154)
  rw [mode0 m hm] at rr
  exact rr
private theorem row51_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 51 m) (some true)=(nc k 51 m,some true,.right) := by
  have rr:=literalRow k 51 m 51 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 155)
  rw [mode0 m hm] at rr
  exact rr
private theorem row231_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 231 m) (none)=(nc k 232 m,none,.right) := by
  have rr:=literalRow k 231 m 232 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 693)
  rw [mode0 m hm] at rr
  exact rr
private theorem row232_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 232 m) (none)=(nc k 233 m,none,.stay) := by
  have rr:=literalRow k 232 m 233 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 696)
  rw [mode0 m hm] at rr
  exact rr
private theorem row232_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 232 m) (some false)=(nc k 232 m,some false,.right) := by
  have rr:=literalRow k 232 m 232 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 697)
  rw [mode0 m hm] at rr
  exact rr
private theorem row232_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 232 m) (some true)=(nc k 232 m,some true,.right) := by
  have rr:=literalRow k 232 m 232 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 698)
  rw [mode0 m hm] at rr
  exact rr
private theorem row233_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 233 m) (none)=(nc k 234 m,none,.right) := by
  have rr:=literalRow k 233 m 234 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 699)
  rw [mode0 m hm] at rr
  exact rr
private theorem row234_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 234 m) (none)=(nc k 235 m,none,.stay) := by
  have rr:=literalRow k 234 m 235 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 702)
  rw [mode0 m hm] at rr
  exact rr
private theorem row234_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 234 m) (some false)=(nc k 234 m,some false,.right) := by
  have rr:=literalRow k 234 m 234 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 703)
  rw [mode0 m hm] at rr
  exact rr
private theorem row234_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 234 m) (some true)=(nc k 234 m,some true,.right) := by
  have rr:=literalRow k 234 m 234 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 704)
  rw [mode0 m hm] at rr
  exact rr
private theorem row235_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 235 m) (none)=(nc k 236 m,none,.right) := by
  have rr:=literalRow k 235 m 236 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 705)
  rw [mode0 m hm] at rr
  exact rr
private theorem row236_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 236 m) (none)=(nc k 237 m,none,.right) := by
  have rr:=literalRow k 236 m 237 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 708)
  rw [mode0 m hm] at rr
  exact rr
private theorem row236_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 236 m) (some true)=(nc k 236 m,some true,.right) := by
  have rr:=literalRow k 236 m 236 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 710)
  rw [mode0 m hm] at rr
  exact rr
private theorem row237_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 237 m) (none)=(nc k 237 m,none,.right) := by
  have rr:=literalRow k 237 m 237 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 711)
  rw [mode0 m hm] at rr
  exact rr
private theorem row237_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 237 m) (some false)=(nc k 238 m,some false,.right) := by
  have rr:=literalRow k 237 m 238 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 712)
  rw [mode0 m hm] at rr
  exact rr
private theorem row35 (k m : Nat) (hm : m<144) (b : Bool) :
    (machine k).step (nc k 35 m) (some b)=(nc k 35 m,some b,.left) := by
  cases b
  · exact row35_1 k m hm
  · exact row35_2 k m hm
private theorem row37 (k m : Nat) (hm : m<144) (b : Bool) :
    (machine k).step (nc k 37 m) (some b)=(nc k 37 m,some b,.left) := by
  cases b
  · exact row37_1 k m hm
  · exact row37_2 k m hm
private theorem row39 (k m : Nat) (hm : m<144) (b : Bool) :
    (machine k).step (nc k 39 m) (some b)=(nc k 39 m,some b,.left) := by
  cases b
  · exact row39_1 k m hm
  · exact row39_2 k m hm
private theorem row42 (k m : Nat) (hm : m<144) (b : Bool) :
    (machine k).step (nc k 42 m) (some b)=(nc k 42 m,some b,.right) := by
  cases b
  · exact row42_1 k m hm
  · exact row42_2 k m hm
private theorem row44 (k m : Nat) (hm : m<144) (b : Bool) :
    (machine k).step (nc k 44 m) (some b)=(nc k 44 m,some b,.right) := by
  cases b
  · exact row44_1 k m hm
  · exact row44_2 k m hm
private theorem row46 (k m : Nat) (hm : m<144) (b : Bool) :
    (machine k).step (nc k 46 m) (some b)=(nc k 46 m,some b,.right) := by
  cases b
  · exact row46_1 k m hm
  · exact row46_2 k m hm
private theorem row51 (k m : Nat) (hm : m<144) (b : Bool) :
    (machine k).step (nc k 51 m) (some b)=(nc k 51 m,some b,.right) := by
  cases b
  · exact row51_1 k m hm
  · exact row51_2 k m hm
private theorem row232 (k m : Nat) (hm : m<144) (b : Bool) :
    (machine k).step (nc k 232 m) (some b)=(nc k 232 m,some b,.right) := by
  cases b
  · exact row232_1 k m hm
  · exact row232_2 k m hm
private theorem row234 (k m : Nat) (hm : m<144) (b : Bool) :
    (machine k).step (nc k 234 m) (some b)=(nc k 234 m,some b,.right) := by
  cases b
  · exact row234_1 k m hm
  · exact row234_2 k m hm
private theorem done_to_source (k P m S L H Q F : Nat) (T : Nat → Option Bool)
    (hm : m<144) (fr : Frame T S L H Q F) (fit : F+1 ≤ P) :
    GPath (M:=machine k) P (F-S+3) (C k 31 m (F+1) T) (C k 38 m S T) := by
  exact leftRoute (M:=machine k) (nc k 31 m) (nc k 32 m) (nc k 33 m) (nc k 34 m)
    (nc k 35 m) (nc k 36 m) (nc k 37 m) (nc k 38 m) P S L H Q F T fr fit
    (row31_0 k m hm) (row32_1 k m hm) (row33_0 k m hm) (row33_2 k m hm)
    (row34_0 k m hm) (row34_2 k m hm) (row35_0 k m hm) (row35 k m hm)
    (row36_0 k m hm) (row37_0 k m hm) (row37 k m hm)
private theorem keep_to_paid (k P m S L H Q F : Nat) (T : Nat → Option Bool)
    (hm : m<144) (fr : Frame T S L H Q F) (gap : H+Q+1 < F) (fit : F+1 ≤ P) :
    GPath (M:=machine k) P (F-S+3) (C k 43 m S T) (C k 52 m (F+1) T) := by
  exact rightRoute (M:=machine k) (nc k 43 m) (nc k 44 m) (nc k 45 m) (nc k 46 m)
    (nc k 47 m) (nc k 48 m) (nc k 49 m) (nc k 52 m) P S L H Q F T fr gap fit
    (row43_0 k m hm) (row44_0 k m hm) (row44 k m hm) (row45_0 k m hm)
    (row46_0 k m hm) (row46 k m hm) (row47_0 k m hm) (row48_0 k m hm)
    (row48_2 k m hm) (row49_0 k m hm) (row49_1 k m hm)
private theorem finish_to_paid (k P m S L H Q F : Nat) (T : Nat → Option Bool)
    (hm : m<144) (fr : Frame T S L H Q F) (gap : H+Q+1 < F) (fit : F+1 ≤ P) :
    GPath (M:=machine k) P (F-S+3) (C k 231 m S T) (C k 238 m (F+1) T) := by
  exact rightRoute (M:=machine k) (nc k 231 m) (nc k 232 m) (nc k 233 m) (nc k 234 m)
    (nc k 235 m) (nc k 236 m) (nc k 237 m) (nc k 238 m) P S L H Q F T fr gap fit
    (row231_0 k m hm) (row232_0 k m hm) (row232 k m hm) (row233_0 k m hm)
    (row234_0 k m hm) (row234 k m hm) (row235_0 k m hm) (row236_0 k m hm)
    (row236_2 k m hm) (row237_0 k m hm) (row237_1 k m hm)
#print axioms done_to_source
#print axioms keep_to_paid
#print axioms finish_to_paid
end VirtualFinalClosure.NativeRoutes
