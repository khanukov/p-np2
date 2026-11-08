import VirtualFinalClosure.BankRoute
namespace VirtualFinalClosure.GuardCross
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.BankRoute","VirtualFinalClosure.BankRoute","right","bankRight",(1:Nat)),
      ("VirtualFinalClosure.BankRoute","VirtualFinalClosure.BankRoute","left","bankLeft",(1:Nat)),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",(1:Nat)),
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",(2:Nat)),
      ("SmallIngress.Runtime","SmallIngress","Node.mk","node",(3:Nat)),
      ("SmallIngress.Runtime","SmallIngress","put","put",(0:Nat)),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","literal_row","literalRow",(1:Nat)),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","op0","mode0",1),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","cellTac","cellTac",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong literal elastic grow row term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique literal elastic grow row term {mod}/{key}"
private theorem row89_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 89 m) (none)=(nc k 90 m,none,.right) := by
  have row:=literalRow k 89 m 90 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 267)
  rw [mode0 m hm] at row
  exact row
private theorem row90_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 90 m) (none)=(nc k 91 m,none,.stay) := by
  have row:=literalRow k 90 m 91 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 270)
  rw [mode0 m hm] at row
  exact row
private theorem row90_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 90 m) (some false)=(nc k 90 m,some false,.right) := by
  have row:=literalRow k 90 m 90 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 271)
  rw [mode0 m hm] at row
  exact row
private theorem row90_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 90 m) (some true)=(nc k 90 m,some true,.right) := by
  have row:=literalRow k 90 m 90 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 272)
  rw [mode0 m hm] at row
  exact row
private theorem row91_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 91 m) (none)=(nc k 92 m,none,.right) := by
  have row:=literalRow k 91 m 92 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 273)
  rw [mode0 m hm] at row
  exact row
private theorem row92_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 92 m) (none)=(nc k 93 m,none,.stay) := by
  have row:=literalRow k 92 m 93 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 276)
  rw [mode0 m hm] at row
  exact row
private theorem row92_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 92 m) (some false)=(nc k 92 m,some false,.right) := by
  have row:=literalRow k 92 m 92 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 277)
  rw [mode0 m hm] at row
  exact row
private theorem row92_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 92 m) (some true)=(nc k 92 m,some true,.right) := by
  have row:=literalRow k 92 m 92 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 278)
  rw [mode0 m hm] at row
  exact row
private theorem row97_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 97 m) (none)=(nc k 98 m,none,.right) := by
  have row:=literalRow k 97 m 98 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 291)
  rw [mode0 m hm] at row
  exact row
private theorem row98_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 98 m) (none)=(nc k 99 m,none,.stay) := by
  have row:=literalRow k 98 m 99 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 294)
  rw [mode0 m hm] at row
  exact row
private theorem row98_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 98 m) (some false)=(nc k 98 m,some false,.right) := by
  have row:=literalRow k 98 m 98 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 295)
  rw [mode0 m hm] at row
  exact row
private theorem row98_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 98 m) (some true)=(nc k 98 m,some true,.right) := by
  have row:=literalRow k 98 m 98 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 296)
  rw [mode0 m hm] at row
  exact row
private theorem row103_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 103 m) (none)=(nc k 104 m,none,.right) := by
  have row:=literalRow k 103 m 104 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 309)
  rw [mode0 m hm] at row
  exact row
private theorem row104_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 104 m) (none)=(nc k 105 m,none,.stay) := by
  have row:=literalRow k 104 m 105 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 312)
  rw [mode0 m hm] at row
  exact row
private theorem row104_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 104 m) (some false)=(nc k 104 m,some false,.right) := by
  have row:=literalRow k 104 m 104 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 313)
  rw [mode0 m hm] at row
  exact row
private theorem row104_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 104 m) (some true)=(nc k 104 m,some true,.right) := by
  have row:=literalRow k 104 m 104 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 314)
  rw [mode0 m hm] at row
  exact row
private theorem row105_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 105 m) (none)=(nc k 106 m,none,.right) := by
  have row:=literalRow k 105 m 106 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 315)
  rw [mode0 m hm] at row
  exact row
private theorem row106_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 106 m) (none)=(nc k 107 m,none,.stay) := by
  have row:=literalRow k 106 m 107 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 318)
  rw [mode0 m hm] at row
  exact row
private theorem row106_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 106 m) (some false)=(nc k 106 m,some false,.right) := by
  have row:=literalRow k 106 m 106 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 319)
  rw [mode0 m hm] at row
  exact row
private theorem row106_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 106 m) (some true)=(nc k 106 m,some true,.right) := by
  have row:=literalRow k 106 m 106 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 320)
  rw [mode0 m hm] at row
  exact row
private theorem row111_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 111 m) (none)=(nc k 112 m,none,.left) := by
  have row:=literalRow k 111 m 112 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 333)
  rw [mode0 m hm] at row
  exact row
private theorem row112_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 112 m) (none)=(nc k 113 m,none,.stay) := by
  have row:=literalRow k 112 m 113 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 336)
  rw [mode0 m hm] at row
  exact row
private theorem row112_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 112 m) (some false)=(nc k 112 m,some false,.left) := by
  have row:=literalRow k 112 m 112 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 337)
  rw [mode0 m hm] at row
  exact row
private theorem row112_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 112 m) (some true)=(nc k 112 m,some true,.left) := by
  have row:=literalRow k 112 m 112 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 338)
  rw [mode0 m hm] at row
  exact row
private theorem row119_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 119 m) (none)=(nc k 120 m,none,.left) := by
  have row:=literalRow k 119 m 120 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 357)
  rw [mode0 m hm] at row
  exact row
private theorem row120_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 120 m) (none)=(nc k 99 m,none,.stay) := by
  have row:=literalRow k 120 m 99 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 360)
  rw [mode0 m hm] at row
  exact row
private theorem row120_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 120 m) (some false)=(nc k 120 m,some false,.left) := by
  have row:=literalRow k 120 m 120 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 361)
  rw [mode0 m hm] at row
  exact row
private theorem row120_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 120 m) (some true)=(nc k 120 m,some true,.left) := by
  have row:=literalRow k 120 m 120 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 362)
  rw [mode0 m hm] at row
  exact row
private theorem row121_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 121 m) (none)=(nc k 122 m,none,.right) := by
  have row:=literalRow k 121 m 122 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 363)
  rw [mode0 m hm] at row
  exact row
private theorem row122_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 122 m) (none)=(nc k 123 m,none,.stay) := by
  have row:=literalRow k 122 m 123 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 366)
  rw [mode0 m hm] at row
  exact row
private theorem row122_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 122 m) (some false)=(nc k 122 m,some false,.right) := by
  have row:=literalRow k 122 m 122 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 367)
  rw [mode0 m hm] at row
  exact row
private theorem row122_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 122 m) (some true)=(nc k 122 m,some true,.right) := by
  have row:=literalRow k 122 m 122 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 368)
  rw [mode0 m hm] at row
  exact row
private theorem row127_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 127 m) (none)=(nc k 128 m,none,.left) := by
  have row:=literalRow k 127 m 128 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 381)
  rw [mode0 m hm] at row
  exact row
private theorem row128_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 128 m) (none)=(nc k 129 m,none,.stay) := by
  have row:=literalRow k 128 m 129 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 384)
  rw [mode0 m hm] at row
  exact row
private theorem row128_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 128 m) (some false)=(nc k 128 m,some false,.left) := by
  have row:=literalRow k 128 m 128 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 385)
  rw [mode0 m hm] at row
  exact row
private theorem row128_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 128 m) (some true)=(nc k 128 m,some true,.left) := by
  have row:=literalRow k 128 m 128 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 386)
  rw [mode0 m hm] at row
  exact row
private theorem row132_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 132 m) (none)=(nc k 133 m,none,.right) := by
  have row:=literalRow k 132 m 133 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 396)
  rw [mode0 m hm] at row
  exact row
private theorem row133_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 133 m) (none)=(nc k 123 m,none,.stay) := by
  have row:=literalRow k 133 m 123 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 399)
  rw [mode0 m hm] at row
  exact row
private theorem row133_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 133 m) (some false)=(nc k 133 m,some false,.right) := by
  have row:=literalRow k 133 m 133 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 400)
  rw [mode0 m hm] at row
  exact row
private theorem row133_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 133 m) (some true)=(nc k 133 m,some true,.right) := by
  have row:=literalRow k 133 m 133 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 401)
  rw [mode0 m hm] at row
  exact row
private theorem row134_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 134 m) (none)=(nc k 135 m,none,.left) := by
  have row:=literalRow k 134 m 135 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 402)
  rw [mode0 m hm] at row
  exact row
private theorem row135_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 135 m) (none)=(nc k 136 m,none,.stay) := by
  have row:=literalRow k 135 m 136 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 405)
  rw [mode0 m hm] at row
  exact row
private theorem row135_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 135 m) (some false)=(nc k 135 m,some false,.left) := by
  have row:=literalRow k 135 m 135 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 406)
  rw [mode0 m hm] at row
  exact row
private theorem row135_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 135 m) (some true)=(nc k 135 m,some true,.left) := by
  have row:=literalRow k 135 m 135 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 407)
  rw [mode0 m hm] at row
  exact row
private theorem row137_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 137 m) (none)=(nc k 138 m,none,.right) := by
  have row:=literalRow k 137 m 138 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 411)
  rw [mode0 m hm] at row
  exact row
private theorem row138_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 138 m) (none)=(nc k 139 m,none,.stay) := by
  have row:=literalRow k 138 m 139 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 414)
  rw [mode0 m hm] at row
  exact row
private theorem row138_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 138 m) (some false)=(nc k 138 m,some false,.right) := by
  have row:=literalRow k 138 m 138 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 415)
  rw [mode0 m hm] at row
  exact row
private theorem row138_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 138 m) (some true)=(nc k 138 m,some true,.right) := by
  have row:=literalRow k 138 m 138 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 416)
  rw [mode0 m hm] at row
  exact row
private theorem row139_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 139 m) (none)=(nc k 140 m,none,.right) := by
  have row:=literalRow k 139 m 140 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 417)
  rw [mode0 m hm] at row
  exact row
private theorem row140_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 140 m) (none)=(nc k 141 m,none,.stay) := by
  have row:=literalRow k 140 m 141 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 420)
  rw [mode0 m hm] at row
  exact row
private theorem row140_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 140 m) (some false)=(nc k 140 m,some false,.right) := by
  have row:=literalRow k 140 m 140 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 421)
  rw [mode0 m hm] at row
  exact row
private theorem row140_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 140 m) (some true)=(nc k 140 m,some true,.right) := by
  have row:=literalRow k 140 m 140 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 422)
  rw [mode0 m hm] at row
  exact row
private theorem row145_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 145 m) (none)=(nc k 146 m,none,.left) := by
  have row:=literalRow k 145 m 146 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 435)
  rw [mode0 m hm] at row
  exact row
private theorem row146_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 146 m) (none)=(nc k 147 m,none,.stay) := by
  have row:=literalRow k 146 m 147 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 438)
  rw [mode0 m hm] at row
  exact row
private theorem row146_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 146 m) (some false)=(nc k 146 m,some false,.left) := by
  have row:=literalRow k 146 m 146 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 439)
  rw [mode0 m hm] at row
  exact row
private theorem row146_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 146 m) (some true)=(nc k 146 m,some true,.left) := by
  have row:=literalRow k 146 m 146 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 440)
  rw [mode0 m hm] at row
  exact row
private theorem row147_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 147 m) (none)=(nc k 148 m,none,.left) := by
  have row:=literalRow k 147 m 148 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 441)
  rw [mode0 m hm] at row
  exact row
private theorem row148_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 148 m) (none)=(nc k 149 m,none,.stay) := by
  have row:=literalRow k 148 m 149 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 444)
  rw [mode0 m hm] at row
  exact row
private theorem row148_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 148 m) (some false)=(nc k 148 m,some false,.left) := by
  have row:=literalRow k 148 m 148 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 445)
  rw [mode0 m hm] at row
  exact row
private theorem row148_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 148 m) (some true)=(nc k 148 m,some true,.left) := by
  have row:=literalRow k 148 m 148 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 446)
  rw [mode0 m hm] at row
  exact row
private theorem row152_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 152 m) (none)=(nc k 153 m,none,.left) := by
  have row:=literalRow k 152 m 153 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 456)
  rw [mode0 m hm] at row
  exact row
private theorem row153_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 153 m) (none)=(nc k 154 m,none,.stay) := by
  have row:=literalRow k 153 m 154 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 459)
  rw [mode0 m hm] at row
  exact row
private theorem row153_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 153 m) (some false)=(nc k 153 m,some false,.left) := by
  have row:=literalRow k 153 m 153 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 460)
  rw [mode0 m hm] at row
  exact row
private theorem row153_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 153 m) (some true)=(nc k 153 m,some true,.left) := by
  have row:=literalRow k 153 m 153 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 461)
  rw [mode0 m hm] at row
  exact row
private theorem row154_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 154 m) (none)=(nc k 155 m,none,.left) := by
  have row:=literalRow k 154 m 155 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 462)
  rw [mode0 m hm] at row
  exact row
private theorem row155_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 155 m) (none)=(nc k 156 m,none,.stay) := by
  have row:=literalRow k 155 m 156 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 465)
  rw [mode0 m hm] at row
  exact row
private theorem row155_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 155 m) (some false)=(nc k 155 m,some false,.left) := by
  have row:=literalRow k 155 m 155 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 466)
  rw [mode0 m hm] at row
  exact row
private theorem row155_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 155 m) (some true)=(nc k 155 m,some true,.left) := by
  have row:=literalRow k 155 m 155 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 467)
  rw [mode0 m hm] at row
  exact row
private theorem row156_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 156 m) (none)=(nc k 157 m,none,.left) := by
  have row:=literalRow k 156 m 157 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 468)
  rw [mode0 m hm] at row
  exact row
private theorem row157_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 157 m) (none)=(nc k 158 m,none,.stay) := by
  have row:=literalRow k 157 m 158 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 471)
  rw [mode0 m hm] at row
  exact row
private theorem row157_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 157 m) (some false)=(nc k 157 m,some false,.left) := by
  have row:=literalRow k 157 m 157 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 472)
  rw [mode0 m hm] at row
  exact row
private theorem row157_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 157 m) (some true)=(nc k 157 m,some true,.left) := by
  have row:=literalRow k 157 m 157 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 473)
  rw [mode0 m hm] at row
  exact row
private theorem row179_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 179 m) (none)=(nc k 180 m,none,.right) := by
  have row:=literalRow k 179 m 180 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 537)
  rw [mode0 m hm] at row
  exact row
private theorem row180_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 180 m) (none)=(nc k 181 m,none,.stay) := by
  have row:=literalRow k 180 m 181 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 540)
  rw [mode0 m hm] at row
  exact row
private theorem row180_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 180 m) (some false)=(nc k 180 m,some false,.right) := by
  have row:=literalRow k 180 m 180 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 541)
  rw [mode0 m hm] at row
  exact row
private theorem row180_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 180 m) (some true)=(nc k 180 m,some true,.right) := by
  have row:=literalRow k 180 m 180 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 542)
  rw [mode0 m hm] at row
  exact row
private theorem row181_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 181 m) (none)=(nc k 182 m,none,.right) := by
  have row:=literalRow k 181 m 182 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 543)
  rw [mode0 m hm] at row
  exact row
private theorem row182_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 182 m) (none)=(nc k 93 m,none,.stay) := by
  have row:=literalRow k 182 m 93 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 546)
  rw [mode0 m hm] at row
  exact row
private theorem row182_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 182 m) (some false)=(nc k 182 m,some false,.right) := by
  have row:=literalRow k 182 m 182 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 547)
  rw [mode0 m hm] at row
  exact row
private theorem row182_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 182 m) (some true)=(nc k 182 m,some true,.right) := by
  have row:=literalRow k 182 m 182 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 548)
  rw [mode0 m hm] at row
  exact row
private theorem row183_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 183 m) (none)=(nc k 184 m,none,.left) := by
  have row:=literalRow k 183 m 184 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 549)
  rw [mode0 m hm] at row
  exact row
private theorem row184_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 184 m) (none)=(nc k 185 m,none,.stay) := by
  have row:=literalRow k 184 m 185 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 552)
  rw [mode0 m hm] at row
  exact row
private theorem row184_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 184 m) (some false)=(nc k 184 m,some false,.left) := by
  have row:=literalRow k 184 m 184 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 553)
  rw [mode0 m hm] at row
  exact row
private theorem row184_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 184 m) (some true)=(nc k 184 m,some true,.left) := by
  have row:=literalRow k 184 m 184 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 554)
  rw [mode0 m hm] at row
  exact row
private theorem row185_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 185 m) (none)=(nc k 186 m,none,.left) := by
  have row:=literalRow k 185 m 186 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 555)
  rw [mode0 m hm] at row
  exact row
private theorem row186_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 186 m) (none)=(nc k 187 m,none,.stay) := by
  have row:=literalRow k 186 m 187 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 558)
  rw [mode0 m hm] at row
  exact row
private theorem row186_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 186 m) (some false)=(nc k 186 m,some false,.left) := by
  have row:=literalRow k 186 m 186 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 559)
  rw [mode0 m hm] at row
  exact row
private theorem row186_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 186 m) (some true)=(nc k 186 m,some true,.left) := by
  have row:=literalRow k 186 m 186 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 560)
  rw [mode0 m hm] at row
  exact row
private theorem row199_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 199 m) (none)=(nc k 200 m,none,.left) := by
  have row:=literalRow k 199 m 200 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 597)
  rw [mode0 m hm] at row
  exact row
private theorem row200_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 200 m) (none)=(nc k 201 m,none,.stay) := by
  have row:=literalRow k 200 m 201 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 600)
  rw [mode0 m hm] at row
  exact row
private theorem row200_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 200 m) (some false)=(nc k 200 m,some false,.left) := by
  have row:=literalRow k 200 m 200 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 601)
  rw [mode0 m hm] at row
  exact row
private theorem row200_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 200 m) (some true)=(nc k 200 m,some true,.left) := by
  have row:=literalRow k 200 m 200 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 602)
  rw [mode0 m hm] at row
  exact row
private theorem row201_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 201 m) (none)=(nc k 202 m,none,.left) := by
  have row:=literalRow k 201 m 202 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 603)
  rw [mode0 m hm] at row
  exact row
private theorem row202_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 202 m) (none)=(nc k 203 m,none,.stay) := by
  have row:=literalRow k 202 m 203 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 606)
  rw [mode0 m hm] at row
  exact row
private theorem row202_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 202 m) (some false)=(nc k 202 m,some false,.left) := by
  have row:=literalRow k 202 m 202 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 607)
  rw [mode0 m hm] at row
  exact row
private theorem row202_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 202 m) (some true)=(nc k 202 m,some true,.left) := by
  have row:=literalRow k 202 m 202 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 608)
  rw [mode0 m hm] at row
  exact row
private theorem row203_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 203 m) (none)=(nc k 204 m,none,.left) := by
  have row:=literalRow k 203 m 204 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 609)
  rw [mode0 m hm] at row
  exact row
private theorem row204_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 204 m) (none)=(nc k 223 m,none,.stay) := by
  have row:=literalRow k 204 m 223 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 612)
  rw [mode0 m hm] at row
  exact row
private theorem row204_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 204 m) (some false)=(nc k 204 m,some false,.left) := by
  have row:=literalRow k 204 m 204 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 613)
  rw [mode0 m hm] at row
  exact row
private theorem row204_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 204 m) (some true)=(nc k 204 m,some true,.left) := by
  have row:=literalRow k 204 m 204 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 614)
  rw [mode0 m hm] at row
  exact row
private theorem row205_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 205 m) (none)=(nc k 206 m,none,.left) := by
  have row:=literalRow k 205 m 206 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 615)
  rw [mode0 m hm] at row
  exact row
private theorem row206_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 206 m) (none)=(nc k 207 m,none,.stay) := by
  have row:=literalRow k 206 m 207 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 618)
  rw [mode0 m hm] at row
  exact row
private theorem row206_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 206 m) (some false)=(nc k 206 m,some false,.left) := by
  have row:=literalRow k 206 m 206 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 619)
  rw [mode0 m hm] at row
  exact row
private theorem row206_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 206 m) (some true)=(nc k 206 m,some true,.left) := by
  have row:=literalRow k 206 m 206 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 620)
  rw [mode0 m hm] at row
  exact row
private theorem row207_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 207 m) (none)=(nc k 208 m,none,.left) := by
  have row:=literalRow k 207 m 208 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 621)
  rw [mode0 m hm] at row
  exact row
private theorem row208_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 208 m) (none)=(nc k 209 m,none,.stay) := by
  have row:=literalRow k 208 m 209 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 624)
  rw [mode0 m hm] at row
  exact row
private theorem row208_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 208 m) (some false)=(nc k 208 m,some false,.left) := by
  have row:=literalRow k 208 m 208 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 625)
  rw [mode0 m hm] at row
  exact row
private theorem row208_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 208 m) (some true)=(nc k 208 m,some true,.left) := by
  have row:=literalRow k 208 m 208 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 626)
  rw [mode0 m hm] at row
  exact row
private theorem row209_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 209 m) (none)=(nc k 210 m,none,.left) := by
  have row:=literalRow k 209 m 210 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 627)
  rw [mode0 m hm] at row
  exact row
private theorem row210_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 210 m) (none)=(nc k 211 m,none,.stay) := by
  have row:=literalRow k 210 m 211 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 630)
  rw [mode0 m hm] at row
  exact row
private theorem row210_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 210 m) (some false)=(nc k 210 m,some false,.left) := by
  have row:=literalRow k 210 m 210 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 631)
  rw [mode0 m hm] at row
  exact row
private theorem row210_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 210 m) (some true)=(nc k 210 m,some true,.left) := by
  have row:=literalRow k 210 m 210 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 632)
  rw [mode0 m hm] at row
  exact row
private theorem row211_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 211 m) (none)=(nc k 212 m,none,.left) := by
  have row:=literalRow k 211 m 212 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 633)
  rw [mode0 m hm] at row
  exact row
private theorem row212_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 212 m) (none)=(nc k 223 m,none,.stay) := by
  have row:=literalRow k 212 m 223 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 636)
  rw [mode0 m hm] at row
  exact row
private theorem row212_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 212 m) (some false)=(nc k 212 m,some false,.left) := by
  have row:=literalRow k 212 m 212 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 637)
  rw [mode0 m hm] at row
  exact row
private theorem row212_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 212 m) (some true)=(nc k 212 m,some true,.left) := by
  have row:=literalRow k 212 m 212 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 638)
  rw [mode0 m hm] at row
  exact row
private theorem row213_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 213 m) (none)=(nc k 214 m,none,.left) := by
  have row:=literalRow k 213 m 214 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 639)
  rw [mode0 m hm] at row
  exact row
private theorem row214_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 214 m) (none)=(nc k 215 m,none,.stay) := by
  have row:=literalRow k 214 m 215 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 642)
  rw [mode0 m hm] at row
  exact row
private theorem row214_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 214 m) (some false)=(nc k 214 m,some false,.left) := by
  have row:=literalRow k 214 m 214 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 643)
  rw [mode0 m hm] at row
  exact row
private theorem row214_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 214 m) (some true)=(nc k 214 m,some true,.left) := by
  have row:=literalRow k 214 m 214 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 644)
  rw [mode0 m hm] at row
  exact row
private theorem row215_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 215 m) (none)=(nc k 216 m,none,.left) := by
  have row:=literalRow k 215 m 216 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 645)
  rw [mode0 m hm] at row
  exact row
private theorem row216_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 216 m) (none)=(nc k 217 m,none,.stay) := by
  have row:=literalRow k 216 m 217 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 648)
  rw [mode0 m hm] at row
  exact row
private theorem row216_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 216 m) (some false)=(nc k 216 m,some false,.left) := by
  have row:=literalRow k 216 m 216 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 649)
  rw [mode0 m hm] at row
  exact row
private theorem row216_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 216 m) (some true)=(nc k 216 m,some true,.left) := by
  have row:=literalRow k 216 m 216 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 650)
  rw [mode0 m hm] at row
  exact row
private theorem row217_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 217 m) (none)=(nc k 218 m,none,.left) := by
  have row:=literalRow k 217 m 218 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 651)
  rw [mode0 m hm] at row
  exact row
private theorem row218_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 218 m) (none)=(nc k 219 m,none,.stay) := by
  have row:=literalRow k 218 m 219 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 654)
  rw [mode0 m hm] at row
  exact row
private theorem row218_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 218 m) (some false)=(nc k 218 m,some false,.left) := by
  have row:=literalRow k 218 m 218 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 655)
  rw [mode0 m hm] at row
  exact row
private theorem row218_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 218 m) (some true)=(nc k 218 m,some true,.left) := by
  have row:=literalRow k 218 m 218 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 656)
  rw [mode0 m hm] at row
  exact row
private theorem row219_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 219 m) (none)=(nc k 220 m,none,.left) := by
  have row:=literalRow k 219 m 220 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 657)
  rw [mode0 m hm] at row
  exact row
private theorem row220_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 220 m) (none)=(nc k 221 m,none,.stay) := by
  have row:=literalRow k 220 m 221 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 660)
  rw [mode0 m hm] at row
  exact row
private theorem row220_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 220 m) (some false)=(nc k 220 m,some false,.left) := by
  have row:=literalRow k 220 m 220 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 661)
  rw [mode0 m hm] at row
  exact row
private theorem row220_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 220 m) (some true)=(nc k 220 m,some true,.left) := by
  have row:=literalRow k 220 m 220 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 662)
  rw [mode0 m hm] at row
  exact row
private theorem row221_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 221 m) (none)=(nc k 222 m,none,.left) := by
  have row:=literalRow k 221 m 222 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 663)
  rw [mode0 m hm] at row
  exact row
private theorem row222_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 222 m) (none)=(nc k 223 m,none,.stay) := by
  have row:=literalRow k 222 m 223 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 666)
  rw [mode0 m hm] at row
  exact row
private theorem row222_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 222 m) (some false)=(nc k 222 m,some false,.left) := by
  have row:=literalRow k 222 m 222 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 667)
  rw [mode0 m hm] at row
  exact row
private theorem row222_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 222 m) (some true)=(nc k 222 m,some true,.left) := by
  have row:=literalRow k 222 m 222 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 668)
  rw [mode0 m hm] at row
  exact row
/-- Literal frozen guardStart crossing, through observed occupied banks. -/
private theorem guardStart (k P m F width n : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (fit : F+5*width+n+7 ≤ P)
    (blank : ∀ j,j ≤ 6 → T (SerializedBody.delimiter F width n j)=none)
    (occupied : ∀ j,j < 6 → ∀ i,SerializedBody.delimiter F width n j < i →
      i < SerializedBody.delimiter F width n (j+1) → ∃ b,T i=some b) :
    GPath (M:=machine k) P ((width+2)+(n+2)) (C k 89 m (SerializedBody.delimiter F width n 0) T)
      (C k 93 m (SerializedBody.delimiter F width n 2) T) := by
  have addr0 : (SerializedBody.delimiter F width n 0)+width+1=SerializedBody.delimiter F width n 1:=by dsimp only [SerializedBody.delimiter];omega
  have p0:=bankRight (nc k 89 m) (nc k 90 m) (nc k 91 m)
    P (SerializedBody.delimiter F width n 0) width T
    (by dsimp only [SerializedBody.delimiter];omega)
    (blank 0 (by decide))
    (by rw [addr0];exact blank 1 (by decide))
    (by intro i lo hi;rw [addr0] at hi;exact occupied 0 (by decide) i lo hi)
    (row89_0 k m hm)
    (by
      intro b
      cases b
      · exact row90_1 k m hm
      · exact row90_2 k m hm)
    (row90_0 k m hm)
  rw [addr0] at p0
  have addr1 : (SerializedBody.delimiter F width n 1)+n+1=SerializedBody.delimiter F width n 2:=by dsimp only [SerializedBody.delimiter];omega
  have p1:=bankRight (nc k 91 m) (nc k 92 m) (nc k 93 m)
    P (SerializedBody.delimiter F width n 1) n T
    (by dsimp only [SerializedBody.delimiter];omega)
    (blank 1 (by decide))
    (by rw [addr1];exact blank 2 (by decide))
    (by intro i lo hi;rw [addr1] at hi;exact occupied 1 (by decide) i lo hi)
    (row91_0 k m hm)
    (by
      intro b
      cases b
      · exact row92_1 k m hm
      · exact row92_2 k m hm)
    (row92_0 k m hm)
  rw [addr1] at p1
  exact (joinPath p0 p1)
/-- Literal frozen ellPaid crossing, through observed occupied banks. -/
private theorem ellPaid (k P m F width n : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (fit : F+5*width+n+7 ≤ P)
    (blank : ∀ j,j ≤ 6 → T (SerializedBody.delimiter F width n j)=none)
    (occupied : ∀ j,j < 6 → ∀ i,SerializedBody.delimiter F width n j < i →
      i < SerializedBody.delimiter F width n (j+1) → ∃ b,T i=some b) :
    GPath (M:=machine k) P ((width+2)) (C k 97 m (SerializedBody.delimiter F width n 2) T)
      (C k 99 m (SerializedBody.delimiter F width n 3) T) := by
  have addr0 : (SerializedBody.delimiter F width n 2)+width+1=SerializedBody.delimiter F width n 3:=by dsimp only [SerializedBody.delimiter];omega
  have p0:=bankRight (nc k 97 m) (nc k 98 m) (nc k 99 m)
    P (SerializedBody.delimiter F width n 2) width T
    (by dsimp only [SerializedBody.delimiter];omega)
    (blank 2 (by decide))
    (by rw [addr0];exact blank 3 (by decide))
    (by intro i lo hi;rw [addr0] at hi;exact occupied 2 (by decide) i lo hi)
    (row97_0 k m hm)
    (by
      intro b
      cases b
      · exact row98_1 k m hm
      · exact row98_2 k m hm)
    (row98_0 k m hm)
  rw [addr0] at p0
  exact p0
/-- Literal frozen doubleQuotaRoute crossing, through observed occupied banks. -/
private theorem doubleQuotaRoute (k P m F width n : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (fit : F+5*width+n+7 ≤ P)
    (blank : ∀ j,j ≤ 6 → T (SerializedBody.delimiter F width n j)=none)
    (occupied : ∀ j,j < 6 → ∀ i,SerializedBody.delimiter F width n j < i →
      i < SerializedBody.delimiter F width n (j+1) → ∃ b,T i=some b) :
    GPath (M:=machine k) P ((width+2)+(width+2)) (C k 103 m (SerializedBody.delimiter F width n 3) T)
      (C k 107 m (SerializedBody.delimiter F width n 5) T) := by
  have addr0 : (SerializedBody.delimiter F width n 3)+width+1=SerializedBody.delimiter F width n 4:=by dsimp only [SerializedBody.delimiter];omega
  have p0:=bankRight (nc k 103 m) (nc k 104 m) (nc k 105 m)
    P (SerializedBody.delimiter F width n 3) width T
    (by dsimp only [SerializedBody.delimiter];omega)
    (blank 3 (by decide))
    (by rw [addr0];exact blank 4 (by decide))
    (by intro i lo hi;rw [addr0] at hi;exact occupied 3 (by decide) i lo hi)
    (row103_0 k m hm)
    (by
      intro b
      cases b
      · exact row104_1 k m hm
      · exact row104_2 k m hm)
    (row104_0 k m hm)
  rw [addr0] at p0
  have addr1 : (SerializedBody.delimiter F width n 4)+width+1=SerializedBody.delimiter F width n 5:=by dsimp only [SerializedBody.delimiter];omega
  have p1:=bankRight (nc k 105 m) (nc k 106 m) (nc k 107 m)
    P (SerializedBody.delimiter F width n 4) width T
    (by dsimp only [SerializedBody.delimiter];omega)
    (blank 4 (by decide))
    (by rw [addr1];exact blank 5 (by decide))
    (by intro i lo hi;rw [addr1] at hi;exact occupied 4 (by decide) i lo hi)
    (row105_0 k m hm)
    (by
      intro b
      cases b
      · exact row106_1 k m hm
      · exact row106_2 k m hm)
    (row106_0 k m hm)
  rw [addr1] at p1
  exact (joinPath p0 p1)
/-- Literal frozen doubleTo4 crossing, through observed occupied banks. -/
private theorem doubleTo4 (k P m F width n : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (fit : F+5*width+n+7 ≤ P)
    (blank : ∀ j,j ≤ 6 → T (SerializedBody.delimiter F width n j)=none)
    (occupied : ∀ j,j < 6 → ∀ i,SerializedBody.delimiter F width n j < i →
      i < SerializedBody.delimiter F width n (j+1) → ∃ b,T i=some b) :
    GPath (M:=machine k) P ((width+2)) (C k 111 m (SerializedBody.delimiter F width n 5) T)
      (C k 113 m (SerializedBody.delimiter F width n 4) T) := by
  have addr0 : (SerializedBody.delimiter F width n 4)+width+1=SerializedBody.delimiter F width n 5:=by dsimp only [SerializedBody.delimiter];omega
  have p0:=bankLeft (nc k 111 m) (nc k 112 m) (nc k 113 m)
    P (SerializedBody.delimiter F width n 4) width T
    (by dsimp only [SerializedBody.delimiter];omega)
    (blank 4 (by decide))
    (by rw [addr0];exact blank 5 (by decide))
    (by intro i lo hi;rw [addr0] at hi;exact occupied 4 (by decide) i lo hi)
    (row111_0 k m hm)
    (by
      intro b
      cases b
      · exact row112_1 k m hm
      · exact row112_2 k m hm)
    (row112_0 k m hm)
  rw [addr0] at p0
  exact p0
/-- Literal frozen doubleBack3 crossing, through observed occupied banks. -/
private theorem doubleBack3 (k P m F width n : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (fit : F+5*width+n+7 ≤ P)
    (blank : ∀ j,j ≤ 6 → T (SerializedBody.delimiter F width n j)=none)
    (occupied : ∀ j,j < 6 → ∀ i,SerializedBody.delimiter F width n j < i →
      i < SerializedBody.delimiter F width n (j+1) → ∃ b,T i=some b) :
    GPath (M:=machine k) P ((width+2)) (C k 119 m (SerializedBody.delimiter F width n 4) T)
      (C k 99 m (SerializedBody.delimiter F width n 3) T) := by
  have addr0 : (SerializedBody.delimiter F width n 3)+width+1=SerializedBody.delimiter F width n 4:=by dsimp only [SerializedBody.delimiter];omega
  have p0:=bankLeft (nc k 119 m) (nc k 120 m) (nc k 99 m)
    P (SerializedBody.delimiter F width n 3) width T
    (by dsimp only [SerializedBody.delimiter];omega)
    (blank 3 (by decide))
    (by rw [addr0];exact blank 4 (by decide))
    (by intro i lo hi;rw [addr0] at hi;exact occupied 3 (by decide) i lo hi)
    (row119_0 k m hm)
    (by
      intro b
      cases b
      · exact row120_1 k m hm
      · exact row120_2 k m hm)
    (row120_0 k m hm)
  rw [addr0] at p0
  exact p0
/-- Literal frozen transferAtD3 crossing, through observed occupied banks. -/
private theorem transferAtD3 (k P m F width n : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (fit : F+5*width+n+7 ≤ P)
    (blank : ∀ j,j ≤ 6 → T (SerializedBody.delimiter F width n j)=none)
    (occupied : ∀ j,j < 6 → ∀ i,SerializedBody.delimiter F width n j < i →
      i < SerializedBody.delimiter F width n (j+1) → ∃ b,T i=some b) :
    GPath (M:=machine k) P ((width+2)) (C k 121 m (SerializedBody.delimiter F width n 3) T)
      (C k 123 m (SerializedBody.delimiter F width n 4) T) := by
  have addr0 : (SerializedBody.delimiter F width n 3)+width+1=SerializedBody.delimiter F width n 4:=by dsimp only [SerializedBody.delimiter];omega
  have p0:=bankRight (nc k 121 m) (nc k 122 m) (nc k 123 m)
    P (SerializedBody.delimiter F width n 3) width T
    (by dsimp only [SerializedBody.delimiter];omega)
    (blank 3 (by decide))
    (by rw [addr0];exact blank 4 (by decide))
    (by intro i lo hi;rw [addr0] at hi;exact occupied 3 (by decide) i lo hi)
    (row121_0 k m hm)
    (by
      intro b
      cases b
      · exact row122_1 k m hm
      · exact row122_2 k m hm)
    (row122_0 k m hm)
  rw [addr0] at p0
  exact p0
/-- Literal frozen transferTo3 crossing, through observed occupied banks. -/
private theorem transferTo3 (k P m F width n : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (fit : F+5*width+n+7 ≤ P)
    (blank : ∀ j,j ≤ 6 → T (SerializedBody.delimiter F width n j)=none)
    (occupied : ∀ j,j < 6 → ∀ i,SerializedBody.delimiter F width n j < i →
      i < SerializedBody.delimiter F width n (j+1) → ∃ b,T i=some b) :
    GPath (M:=machine k) P ((width+2)) (C k 127 m (SerializedBody.delimiter F width n 4) T)
      (C k 129 m (SerializedBody.delimiter F width n 3) T) := by
  have addr0 : (SerializedBody.delimiter F width n 3)+width+1=SerializedBody.delimiter F width n 4:=by dsimp only [SerializedBody.delimiter];omega
  have p0:=bankLeft (nc k 127 m) (nc k 128 m) (nc k 129 m)
    P (SerializedBody.delimiter F width n 3) width T
    (by dsimp only [SerializedBody.delimiter];omega)
    (blank 3 (by decide))
    (by rw [addr0];exact blank 4 (by decide))
    (by intro i lo hi;rw [addr0] at hi;exact occupied 3 (by decide) i lo hi)
    (row127_0 k m hm)
    (by
      intro b
      cases b
      · exact row128_1 k m hm
      · exact row128_2 k m hm)
    (row128_0 k m hm)
  rw [addr0] at p0
  exact p0
/-- Literal frozen transferBack4 crossing, through observed occupied banks. -/
private theorem transferBack4 (k P m F width n : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (fit : F+5*width+n+7 ≤ P)
    (blank : ∀ j,j ≤ 6 → T (SerializedBody.delimiter F width n j)=none)
    (occupied : ∀ j,j < 6 → ∀ i,SerializedBody.delimiter F width n j < i →
      i < SerializedBody.delimiter F width n (j+1) → ∃ b,T i=some b) :
    GPath (M:=machine k) P ((width+2)) (C k 132 m (SerializedBody.delimiter F width n 3) T)
      (C k 123 m (SerializedBody.delimiter F width n 4) T) := by
  have addr0 : (SerializedBody.delimiter F width n 3)+width+1=SerializedBody.delimiter F width n 4:=by dsimp only [SerializedBody.delimiter];omega
  have p0:=bankRight (nc k 132 m) (nc k 133 m) (nc k 123 m)
    P (SerializedBody.delimiter F width n 3) width T
    (by dsimp only [SerializedBody.delimiter];omega)
    (blank 3 (by decide))
    (by rw [addr0];exact blank 4 (by decide))
    (by intro i lo hi;rw [addr0] at hi;exact occupied 3 (by decide) i lo hi)
    (row132_0 k m hm)
    (by
      intro b
      cases b
      · exact row133_1 k m hm
      · exact row133_2 k m hm)
    (row133_0 k m hm)
  rw [addr0] at p0
  exact p0
/-- Literal frozen transferDone4 crossing, through observed occupied banks. -/
private theorem transferDone4 (k P m F width n : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (fit : F+5*width+n+7 ≤ P)
    (blank : ∀ j,j ≤ 6 → T (SerializedBody.delimiter F width n j)=none)
    (occupied : ∀ j,j < 6 → ∀ i,SerializedBody.delimiter F width n j < i →
      i < SerializedBody.delimiter F width n (j+1) → ∃ b,T i=some b) :
    GPath (M:=machine k) P ((width+2)) (C k 134 m (SerializedBody.delimiter F width n 4) T)
      (C k 136 m (SerializedBody.delimiter F width n 3) T) := by
  have addr0 : (SerializedBody.delimiter F width n 3)+width+1=SerializedBody.delimiter F width n 4:=by dsimp only [SerializedBody.delimiter];omega
  have p0:=bankLeft (nc k 134 m) (nc k 135 m) (nc k 136 m)
    P (SerializedBody.delimiter F width n 3) width T
    (by dsimp only [SerializedBody.delimiter];omega)
    (blank 3 (by decide))
    (by rw [addr0];exact blank 4 (by decide))
    (by intro i lo hi;rw [addr0] at hi;exact occupied 3 (by decide) i lo hi)
    (row134_0 k m hm)
    (by
      intro b
      cases b
      · exact row135_1 k m hm
      · exact row135_2 k m hm)
    (row135_0 k m hm)
  rw [addr0] at p0
  exact p0
/-- Literal frozen indexBitOne crossing, through observed occupied banks. -/
private theorem indexBitOne (k P m F width n : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (fit : F+5*width+n+7 ≤ P)
    (blank : ∀ j,j ≤ 6 → T (SerializedBody.delimiter F width n j)=none)
    (occupied : ∀ j,j < 6 → ∀ i,SerializedBody.delimiter F width n j < i →
      i < SerializedBody.delimiter F width n (j+1) → ∃ b,T i=some b) :
    GPath (M:=machine k) P ((width+2)+(width+2)) (C k 137 m (SerializedBody.delimiter F width n 3) T)
      (C k 141 m (SerializedBody.delimiter F width n 5) T) := by
  have addr0 : (SerializedBody.delimiter F width n 3)+width+1=SerializedBody.delimiter F width n 4:=by dsimp only [SerializedBody.delimiter];omega
  have p0:=bankRight (nc k 137 m) (nc k 138 m) (nc k 139 m)
    P (SerializedBody.delimiter F width n 3) width T
    (by dsimp only [SerializedBody.delimiter];omega)
    (blank 3 (by decide))
    (by rw [addr0];exact blank 4 (by decide))
    (by intro i lo hi;rw [addr0] at hi;exact occupied 3 (by decide) i lo hi)
    (row137_0 k m hm)
    (by
      intro b
      cases b
      · exact row138_1 k m hm
      · exact row138_2 k m hm)
    (row138_0 k m hm)
  rw [addr0] at p0
  have addr1 : (SerializedBody.delimiter F width n 4)+width+1=SerializedBody.delimiter F width n 5:=by dsimp only [SerializedBody.delimiter];omega
  have p1:=bankRight (nc k 139 m) (nc k 140 m) (nc k 141 m)
    P (SerializedBody.delimiter F width n 4) width T
    (by dsimp only [SerializedBody.delimiter];omega)
    (blank 4 (by decide))
    (by rw [addr1];exact blank 5 (by decide))
    (by intro i lo hi;rw [addr1] at hi;exact occupied 4 (by decide) i lo hi)
    (row139_0 k m hm)
    (by
      intro b
      cases b
      · exact row140_1 k m hm
      · exact row140_2 k m hm)
    (row140_0 k m hm)
  rw [addr1] at p1
  exact (joinPath p0 p1)
/-- Literal frozen indexTo3 crossing, through observed occupied banks. -/
private theorem indexTo3 (k P m F width n : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (fit : F+5*width+n+7 ≤ P)
    (blank : ∀ j,j ≤ 6 → T (SerializedBody.delimiter F width n j)=none)
    (occupied : ∀ j,j < 6 → ∀ i,SerializedBody.delimiter F width n j < i →
      i < SerializedBody.delimiter F width n (j+1) → ∃ b,T i=some b) :
    GPath (M:=machine k) P ((width+2)+(width+2)) (C k 145 m (SerializedBody.delimiter F width n 5) T)
      (C k 149 m (SerializedBody.delimiter F width n 3) T) := by
  have addr0 : (SerializedBody.delimiter F width n 4)+width+1=SerializedBody.delimiter F width n 5:=by dsimp only [SerializedBody.delimiter];omega
  have p0:=bankLeft (nc k 145 m) (nc k 146 m) (nc k 147 m)
    P (SerializedBody.delimiter F width n 4) width T
    (by dsimp only [SerializedBody.delimiter];omega)
    (blank 4 (by decide))
    (by rw [addr0];exact blank 5 (by decide))
    (by intro i lo hi;rw [addr0] at hi;exact occupied 4 (by decide) i lo hi)
    (row145_0 k m hm)
    (by
      intro b
      cases b
      · exact row146_1 k m hm
      · exact row146_2 k m hm)
    (row146_0 k m hm)
  rw [addr0] at p0
  have addr1 : (SerializedBody.delimiter F width n 3)+width+1=SerializedBody.delimiter F width n 4:=by dsimp only [SerializedBody.delimiter];omega
  have p1:=bankLeft (nc k 147 m) (nc k 148 m) (nc k 149 m)
    P (SerializedBody.delimiter F width n 3) width T
    (by dsimp only [SerializedBody.delimiter];omega)
    (blank 3 (by decide))
    (by rw [addr1];exact blank 4 (by decide))
    (by intro i lo hi;rw [addr1] at hi;exact occupied 3 (by decide) i lo hi)
    (row147_0 k m hm)
    (by
      intro b
      cases b
      · exact row148_1 k m hm
      · exact row148_2 k m hm)
    (row148_0 k m hm)
  rw [addr1] at p1
  exact (joinPath p0 p1)
/-- Literal frozen advanceD3 crossing, through observed occupied banks. -/
private theorem advanceD3 (k P m F width n : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (fit : F+5*width+n+7 ≤ P)
    (blank : ∀ j,j ≤ 6 → T (SerializedBody.delimiter F width n j)=none)
    (occupied : ∀ j,j < 6 → ∀ i,SerializedBody.delimiter F width n j < i →
      i < SerializedBody.delimiter F width n (j+1) → ∃ b,T i=some b) :
    GPath (M:=machine k) P ((width+2)+(n+2)+(width+2)) (C k 152 m (SerializedBody.delimiter F width n 3) T)
      (C k 158 m (SerializedBody.delimiter F width n 0) T) := by
  have addr0 : (SerializedBody.delimiter F width n 2)+width+1=SerializedBody.delimiter F width n 3:=by dsimp only [SerializedBody.delimiter];omega
  have p0:=bankLeft (nc k 152 m) (nc k 153 m) (nc k 154 m)
    P (SerializedBody.delimiter F width n 2) width T
    (by dsimp only [SerializedBody.delimiter];omega)
    (blank 2 (by decide))
    (by rw [addr0];exact blank 3 (by decide))
    (by intro i lo hi;rw [addr0] at hi;exact occupied 2 (by decide) i lo hi)
    (row152_0 k m hm)
    (by
      intro b
      cases b
      · exact row153_1 k m hm
      · exact row153_2 k m hm)
    (row153_0 k m hm)
  rw [addr0] at p0
  have addr1 : (SerializedBody.delimiter F width n 1)+n+1=SerializedBody.delimiter F width n 2:=by dsimp only [SerializedBody.delimiter];omega
  have p1:=bankLeft (nc k 154 m) (nc k 155 m) (nc k 156 m)
    P (SerializedBody.delimiter F width n 1) n T
    (by dsimp only [SerializedBody.delimiter];omega)
    (blank 1 (by decide))
    (by rw [addr1];exact blank 2 (by decide))
    (by intro i lo hi;rw [addr1] at hi;exact occupied 1 (by decide) i lo hi)
    (row154_0 k m hm)
    (by
      intro b
      cases b
      · exact row155_1 k m hm
      · exact row155_2 k m hm)
    (row155_0 k m hm)
  rw [addr1] at p1
  have addr2 : (SerializedBody.delimiter F width n 0)+width+1=SerializedBody.delimiter F width n 1:=by dsimp only [SerializedBody.delimiter];omega
  have p2:=bankLeft (nc k 156 m) (nc k 157 m) (nc k 158 m)
    P (SerializedBody.delimiter F width n 0) width T
    (by dsimp only [SerializedBody.delimiter];omega)
    (blank 0 (by decide))
    (by rw [addr2];exact blank 1 (by decide))
    (by intro i lo hi;rw [addr2] at hi;exact occupied 0 (by decide) i lo hi)
    (row156_0 k m hm)
    (by
      intro b
      cases b
      · exact row157_1 k m hm
      · exact row157_2 k m hm)
    (row157_0 k m hm)
  rw [addr2] at p2
  exact (joinPath (joinPath p0 p1) p2)
/-- Literal frozen advanceAtD0 crossing, through observed occupied banks. -/
private theorem advanceAtD0 (k P m F width n : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (fit : F+5*width+n+7 ≤ P)
    (blank : ∀ j,j ≤ 6 → T (SerializedBody.delimiter F width n j)=none)
    (occupied : ∀ j,j < 6 → ∀ i,SerializedBody.delimiter F width n j < i →
      i < SerializedBody.delimiter F width n (j+1) → ∃ b,T i=some b) :
    GPath (M:=machine k) P ((width+2)+(n+2)) (C k 179 m (SerializedBody.delimiter F width n 0) T)
      (C k 93 m (SerializedBody.delimiter F width n 2) T) := by
  have addr0 : (SerializedBody.delimiter F width n 0)+width+1=SerializedBody.delimiter F width n 1:=by dsimp only [SerializedBody.delimiter];omega
  have p0:=bankRight (nc k 179 m) (nc k 180 m) (nc k 181 m)
    P (SerializedBody.delimiter F width n 0) width T
    (by dsimp only [SerializedBody.delimiter];omega)
    (blank 0 (by decide))
    (by rw [addr0];exact blank 1 (by decide))
    (by intro i lo hi;rw [addr0] at hi;exact occupied 0 (by decide) i lo hi)
    (row179_0 k m hm)
    (by
      intro b
      cases b
      · exact row180_1 k m hm
      · exact row180_2 k m hm)
    (row180_0 k m hm)
  rw [addr0] at p0
  have addr1 : (SerializedBody.delimiter F width n 1)+n+1=SerializedBody.delimiter F width n 2:=by dsimp only [SerializedBody.delimiter];omega
  have p1:=bankRight (nc k 181 m) (nc k 182 m) (nc k 93 m)
    P (SerializedBody.delimiter F width n 1) n T
    (by dsimp only [SerializedBody.delimiter];omega)
    (blank 1 (by decide))
    (by rw [addr1];exact blank 2 (by decide))
    (by intro i lo hi;rw [addr1] at hi;exact occupied 1 (by decide) i lo hi)
    (row181_0 k m hm)
    (by
      intro b
      cases b
      · exact row182_1 k m hm
      · exact row182_2 k m hm)
    (row182_0 k m hm)
  rw [addr1] at p1
  exact (joinPath p0 p1)
/-- Literal frozen guardDoneD2 crossing, through observed occupied banks. -/
private theorem guardDoneD2 (k P m F width n : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (fit : F+5*width+n+7 ≤ P)
    (blank : ∀ j,j ≤ 6 → T (SerializedBody.delimiter F width n j)=none)
    (occupied : ∀ j,j < 6 → ∀ i,SerializedBody.delimiter F width n j < i →
      i < SerializedBody.delimiter F width n (j+1) → ∃ b,T i=some b) :
    GPath (M:=machine k) P ((n+2)+(width+2)) (C k 183 m (SerializedBody.delimiter F width n 2) T)
      (C k 187 m (SerializedBody.delimiter F width n 0) T) := by
  have addr0 : (SerializedBody.delimiter F width n 1)+n+1=SerializedBody.delimiter F width n 2:=by dsimp only [SerializedBody.delimiter];omega
  have p0:=bankLeft (nc k 183 m) (nc k 184 m) (nc k 185 m)
    P (SerializedBody.delimiter F width n 1) n T
    (by dsimp only [SerializedBody.delimiter];omega)
    (blank 1 (by decide))
    (by rw [addr0];exact blank 2 (by decide))
    (by intro i lo hi;rw [addr0] at hi;exact occupied 1 (by decide) i lo hi)
    (row183_0 k m hm)
    (by
      intro b
      cases b
      · exact row184_1 k m hm
      · exact row184_2 k m hm)
    (row184_0 k m hm)
  rw [addr0] at p0
  have addr1 : (SerializedBody.delimiter F width n 0)+width+1=SerializedBody.delimiter F width n 1:=by dsimp only [SerializedBody.delimiter];omega
  have p1:=bankLeft (nc k 185 m) (nc k 186 m) (nc k 187 m)
    P (SerializedBody.delimiter F width n 0) width T
    (by dsimp only [SerializedBody.delimiter];omega)
    (blank 0 (by decide))
    (by rw [addr1];exact blank 1 (by decide))
    (by intro i lo hi;rw [addr1] at hi;exact occupied 0 (by decide) i lo hi)
    (row185_0 k m hm)
    (by
      intro b
      cases b
      · exact row186_1 k m hm
      · exact row186_2 k m hm)
    (row186_0 k m hm)
  rw [addr1] at p1
  exact (joinPath p0 p1)
/-- Literal frozen abortD3 crossing, through observed occupied banks. -/
private theorem abortD3 (k P m F width n : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (fit : F+5*width+n+7 ≤ P)
    (blank : ∀ j,j ≤ 6 → T (SerializedBody.delimiter F width n j)=none)
    (occupied : ∀ j,j < 6 → ∀ i,SerializedBody.delimiter F width n j < i →
      i < SerializedBody.delimiter F width n (j+1) → ∃ b,T i=some b) :
    GPath (M:=machine k) P ((width+2)+(n+2)+(width+2)) (C k 199 m (SerializedBody.delimiter F width n 3) T)
      (C k 223 m (SerializedBody.delimiter F width n 0) T) := by
  have addr0 : (SerializedBody.delimiter F width n 2)+width+1=SerializedBody.delimiter F width n 3:=by dsimp only [SerializedBody.delimiter];omega
  have p0:=bankLeft (nc k 199 m) (nc k 200 m) (nc k 201 m)
    P (SerializedBody.delimiter F width n 2) width T
    (by dsimp only [SerializedBody.delimiter];omega)
    (blank 2 (by decide))
    (by rw [addr0];exact blank 3 (by decide))
    (by intro i lo hi;rw [addr0] at hi;exact occupied 2 (by decide) i lo hi)
    (row199_0 k m hm)
    (by
      intro b
      cases b
      · exact row200_1 k m hm
      · exact row200_2 k m hm)
    (row200_0 k m hm)
  rw [addr0] at p0
  have addr1 : (SerializedBody.delimiter F width n 1)+n+1=SerializedBody.delimiter F width n 2:=by dsimp only [SerializedBody.delimiter];omega
  have p1:=bankLeft (nc k 201 m) (nc k 202 m) (nc k 203 m)
    P (SerializedBody.delimiter F width n 1) n T
    (by dsimp only [SerializedBody.delimiter];omega)
    (blank 1 (by decide))
    (by rw [addr1];exact blank 2 (by decide))
    (by intro i lo hi;rw [addr1] at hi;exact occupied 1 (by decide) i lo hi)
    (row201_0 k m hm)
    (by
      intro b
      cases b
      · exact row202_1 k m hm
      · exact row202_2 k m hm)
    (row202_0 k m hm)
  rw [addr1] at p1
  have addr2 : (SerializedBody.delimiter F width n 0)+width+1=SerializedBody.delimiter F width n 1:=by dsimp only [SerializedBody.delimiter];omega
  have p2:=bankLeft (nc k 203 m) (nc k 204 m) (nc k 223 m)
    P (SerializedBody.delimiter F width n 0) width T
    (by dsimp only [SerializedBody.delimiter];omega)
    (blank 0 (by decide))
    (by rw [addr2];exact blank 1 (by decide))
    (by intro i lo hi;rw [addr2] at hi;exact occupied 0 (by decide) i lo hi)
    (row203_0 k m hm)
    (by
      intro b
      cases b
      · exact row204_1 k m hm
      · exact row204_2 k m hm)
    (row204_0 k m hm)
  rw [addr2] at p2
  exact (joinPath (joinPath p0 p1) p2)
/-- Literal frozen abortD4 crossing, through observed occupied banks. -/
private theorem abortD4 (k P m F width n : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (fit : F+5*width+n+7 ≤ P)
    (blank : ∀ j,j ≤ 6 → T (SerializedBody.delimiter F width n j)=none)
    (occupied : ∀ j,j < 6 → ∀ i,SerializedBody.delimiter F width n j < i →
      i < SerializedBody.delimiter F width n (j+1) → ∃ b,T i=some b) :
    GPath (M:=machine k) P ((width+2)+(width+2)+(n+2)+(width+2)) (C k 205 m (SerializedBody.delimiter F width n 4) T)
      (C k 223 m (SerializedBody.delimiter F width n 0) T) := by
  have addr0 : (SerializedBody.delimiter F width n 3)+width+1=SerializedBody.delimiter F width n 4:=by dsimp only [SerializedBody.delimiter];omega
  have p0:=bankLeft (nc k 205 m) (nc k 206 m) (nc k 207 m)
    P (SerializedBody.delimiter F width n 3) width T
    (by dsimp only [SerializedBody.delimiter];omega)
    (blank 3 (by decide))
    (by rw [addr0];exact blank 4 (by decide))
    (by intro i lo hi;rw [addr0] at hi;exact occupied 3 (by decide) i lo hi)
    (row205_0 k m hm)
    (by
      intro b
      cases b
      · exact row206_1 k m hm
      · exact row206_2 k m hm)
    (row206_0 k m hm)
  rw [addr0] at p0
  have addr1 : (SerializedBody.delimiter F width n 2)+width+1=SerializedBody.delimiter F width n 3:=by dsimp only [SerializedBody.delimiter];omega
  have p1:=bankLeft (nc k 207 m) (nc k 208 m) (nc k 209 m)
    P (SerializedBody.delimiter F width n 2) width T
    (by dsimp only [SerializedBody.delimiter];omega)
    (blank 2 (by decide))
    (by rw [addr1];exact blank 3 (by decide))
    (by intro i lo hi;rw [addr1] at hi;exact occupied 2 (by decide) i lo hi)
    (row207_0 k m hm)
    (by
      intro b
      cases b
      · exact row208_1 k m hm
      · exact row208_2 k m hm)
    (row208_0 k m hm)
  rw [addr1] at p1
  have addr2 : (SerializedBody.delimiter F width n 1)+n+1=SerializedBody.delimiter F width n 2:=by dsimp only [SerializedBody.delimiter];omega
  have p2:=bankLeft (nc k 209 m) (nc k 210 m) (nc k 211 m)
    P (SerializedBody.delimiter F width n 1) n T
    (by dsimp only [SerializedBody.delimiter];omega)
    (blank 1 (by decide))
    (by rw [addr2];exact blank 2 (by decide))
    (by intro i lo hi;rw [addr2] at hi;exact occupied 1 (by decide) i lo hi)
    (row209_0 k m hm)
    (by
      intro b
      cases b
      · exact row210_1 k m hm
      · exact row210_2 k m hm)
    (row210_0 k m hm)
  rw [addr2] at p2
  have addr3 : (SerializedBody.delimiter F width n 0)+width+1=SerializedBody.delimiter F width n 1:=by dsimp only [SerializedBody.delimiter];omega
  have p3:=bankLeft (nc k 211 m) (nc k 212 m) (nc k 223 m)
    P (SerializedBody.delimiter F width n 0) width T
    (by dsimp only [SerializedBody.delimiter];omega)
    (blank 0 (by decide))
    (by rw [addr3];exact blank 1 (by decide))
    (by intro i lo hi;rw [addr3] at hi;exact occupied 0 (by decide) i lo hi)
    (row211_0 k m hm)
    (by
      intro b
      cases b
      · exact row212_1 k m hm
      · exact row212_2 k m hm)
    (row212_0 k m hm)
  rw [addr3] at p3
  exact (joinPath (joinPath (joinPath p0 p1) p2) p3)
/-- Literal frozen abortD5 crossing, through observed occupied banks. -/
private theorem abortD5 (k P m F width n : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (fit : F+5*width+n+7 ≤ P)
    (blank : ∀ j,j ≤ 6 → T (SerializedBody.delimiter F width n j)=none)
    (occupied : ∀ j,j < 6 → ∀ i,SerializedBody.delimiter F width n j < i →
      i < SerializedBody.delimiter F width n (j+1) → ∃ b,T i=some b) :
    GPath (M:=machine k) P ((width+2)+(width+2)+(width+2)+(n+2)+(width+2)) (C k 213 m (SerializedBody.delimiter F width n 5) T)
      (C k 223 m (SerializedBody.delimiter F width n 0) T) := by
  have addr0 : (SerializedBody.delimiter F width n 4)+width+1=SerializedBody.delimiter F width n 5:=by dsimp only [SerializedBody.delimiter];omega
  have p0:=bankLeft (nc k 213 m) (nc k 214 m) (nc k 215 m)
    P (SerializedBody.delimiter F width n 4) width T
    (by dsimp only [SerializedBody.delimiter];omega)
    (blank 4 (by decide))
    (by rw [addr0];exact blank 5 (by decide))
    (by intro i lo hi;rw [addr0] at hi;exact occupied 4 (by decide) i lo hi)
    (row213_0 k m hm)
    (by
      intro b
      cases b
      · exact row214_1 k m hm
      · exact row214_2 k m hm)
    (row214_0 k m hm)
  rw [addr0] at p0
  have addr1 : (SerializedBody.delimiter F width n 3)+width+1=SerializedBody.delimiter F width n 4:=by dsimp only [SerializedBody.delimiter];omega
  have p1:=bankLeft (nc k 215 m) (nc k 216 m) (nc k 217 m)
    P (SerializedBody.delimiter F width n 3) width T
    (by dsimp only [SerializedBody.delimiter];omega)
    (blank 3 (by decide))
    (by rw [addr1];exact blank 4 (by decide))
    (by intro i lo hi;rw [addr1] at hi;exact occupied 3 (by decide) i lo hi)
    (row215_0 k m hm)
    (by
      intro b
      cases b
      · exact row216_1 k m hm
      · exact row216_2 k m hm)
    (row216_0 k m hm)
  rw [addr1] at p1
  have addr2 : (SerializedBody.delimiter F width n 2)+width+1=SerializedBody.delimiter F width n 3:=by dsimp only [SerializedBody.delimiter];omega
  have p2:=bankLeft (nc k 217 m) (nc k 218 m) (nc k 219 m)
    P (SerializedBody.delimiter F width n 2) width T
    (by dsimp only [SerializedBody.delimiter];omega)
    (blank 2 (by decide))
    (by rw [addr2];exact blank 3 (by decide))
    (by intro i lo hi;rw [addr2] at hi;exact occupied 2 (by decide) i lo hi)
    (row217_0 k m hm)
    (by
      intro b
      cases b
      · exact row218_1 k m hm
      · exact row218_2 k m hm)
    (row218_0 k m hm)
  rw [addr2] at p2
  have addr3 : (SerializedBody.delimiter F width n 1)+n+1=SerializedBody.delimiter F width n 2:=by dsimp only [SerializedBody.delimiter];omega
  have p3:=bankLeft (nc k 219 m) (nc k 220 m) (nc k 221 m)
    P (SerializedBody.delimiter F width n 1) n T
    (by dsimp only [SerializedBody.delimiter];omega)
    (blank 1 (by decide))
    (by rw [addr3];exact blank 2 (by decide))
    (by intro i lo hi;rw [addr3] at hi;exact occupied 1 (by decide) i lo hi)
    (row219_0 k m hm)
    (by
      intro b
      cases b
      · exact row220_1 k m hm
      · exact row220_2 k m hm)
    (row220_0 k m hm)
  rw [addr3] at p3
  have addr4 : (SerializedBody.delimiter F width n 0)+width+1=SerializedBody.delimiter F width n 1:=by dsimp only [SerializedBody.delimiter];omega
  have p4:=bankLeft (nc k 221 m) (nc k 222 m) (nc k 223 m)
    P (SerializedBody.delimiter F width n 0) width T
    (by dsimp only [SerializedBody.delimiter];omega)
    (blank 0 (by decide))
    (by rw [addr4];exact blank 1 (by decide))
    (by intro i lo hi;rw [addr4] at hi;exact occupied 0 (by decide) i lo hi)
    (row221_0 k m hm)
    (by
      intro b
      cases b
      · exact row222_1 k m hm
      · exact row222_2 k m hm)
    (row222_0 k m hm)
  rw [addr4] at p4
  exact (joinPath (joinPath (joinPath (joinPath p0 p1) p2) p3) p4)
#print axioms row89_0
#print axioms row90_0
#print axioms row90_1
#print axioms row90_2
#print axioms row91_0
#print axioms row92_0
#print axioms row92_1
#print axioms row92_2
#print axioms row97_0
#print axioms row98_0
#print axioms row98_1
#print axioms row98_2
#print axioms row103_0
#print axioms row104_0
#print axioms row104_1
#print axioms row104_2
#print axioms row105_0
#print axioms row106_0
#print axioms row106_1
#print axioms row106_2
#print axioms row111_0
#print axioms row112_0
#print axioms row112_1
#print axioms row112_2
#print axioms row119_0
#print axioms row120_0
#print axioms row120_1
#print axioms row120_2
#print axioms row121_0
#print axioms row122_0
#print axioms row122_1
#print axioms row122_2
#print axioms row127_0
#print axioms row128_0
#print axioms row128_1
#print axioms row128_2
#print axioms row132_0
#print axioms row133_0
#print axioms row133_1
#print axioms row133_2
#print axioms row134_0
#print axioms row135_0
#print axioms row135_1
#print axioms row135_2
#print axioms row137_0
#print axioms row138_0
#print axioms row138_1
#print axioms row138_2
#print axioms row139_0
#print axioms row140_0
#print axioms row140_1
#print axioms row140_2
#print axioms row145_0
#print axioms row146_0
#print axioms row146_1
#print axioms row146_2
#print axioms row147_0
#print axioms row148_0
#print axioms row148_1
#print axioms row148_2
#print axioms row152_0
#print axioms row153_0
#print axioms row153_1
#print axioms row153_2
#print axioms row154_0
#print axioms row155_0
#print axioms row155_1
#print axioms row155_2
#print axioms row156_0
#print axioms row157_0
#print axioms row157_1
#print axioms row157_2
#print axioms row179_0
#print axioms row180_0
#print axioms row180_1
#print axioms row180_2
#print axioms row181_0
#print axioms row182_0
#print axioms row182_1
#print axioms row182_2
#print axioms row183_0
#print axioms row184_0
#print axioms row184_1
#print axioms row184_2
#print axioms row185_0
#print axioms row186_0
#print axioms row186_1
#print axioms row186_2
#print axioms row199_0
#print axioms row200_0
#print axioms row200_1
#print axioms row200_2
#print axioms row201_0
#print axioms row202_0
#print axioms row202_1
#print axioms row202_2
#print axioms row203_0
#print axioms row204_0
#print axioms row204_1
#print axioms row204_2
#print axioms row205_0
#print axioms row206_0
#print axioms row206_1
#print axioms row206_2
#print axioms row207_0
#print axioms row208_0
#print axioms row208_1
#print axioms row208_2
#print axioms row209_0
#print axioms row210_0
#print axioms row210_1
#print axioms row210_2
#print axioms row211_0
#print axioms row212_0
#print axioms row212_1
#print axioms row212_2
#print axioms row213_0
#print axioms row214_0
#print axioms row214_1
#print axioms row214_2
#print axioms row215_0
#print axioms row216_0
#print axioms row216_1
#print axioms row216_2
#print axioms row217_0
#print axioms row218_0
#print axioms row218_1
#print axioms row218_2
#print axioms row219_0
#print axioms row220_0
#print axioms row220_1
#print axioms row220_2
#print axioms row221_0
#print axioms row222_0
#print axioms row222_1
#print axioms row222_2
#print axioms guardStart
#print axioms ellPaid
#print axioms doubleQuotaRoute
#print axioms doubleTo4
#print axioms doubleBack3
#print axioms transferAtD3
#print axioms transferTo3
#print axioms transferBack4
#print axioms transferDone4
#print axioms indexBitOne
#print axioms indexTo3
#print axioms advanceD3
#print axioms advanceAtD0
#print axioms guardDoneD2
#print axioms abortD3
#print axioms abortD4
#print axioms abortD5
end VirtualFinalClosure.GuardCross
