import VirtualFinalClosure.PaintPath
namespace VirtualFinalClosure.GrowRows
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","literal_row","literalRow",(1:Nat)),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","op0","mode0",1),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","cellTac","cellTac",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong literal elastic grow row term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique literal elastic grow row term {mod}/{key}"
private theorem r052_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 52 m) (none)=(nc k 53 m,none,.right) := by
  have row:=literalRow k 52 m 53 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 156)
  rw [mode0 m hm] at row
  exact row
private theorem r053_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 53 m) (none)=(nc k 54 m,none,.stay) := by
  have row:=literalRow k 53 m 54 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 159)
  rw [mode0 m hm] at row
  exact row
private theorem r053_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 53 m) (some false)=(nc k 53 m,some false,.right) := by
  have row:=literalRow k 53 m 53 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 160)
  rw [mode0 m hm] at row
  exact row
private theorem r053_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 53 m) (some true)=(nc k 53 m,some false,.right) := by
  have row:=literalRow k 53 m 53 1 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 161)
  rw [mode0 m hm] at row
  exact row
private theorem r054_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 54 m) (none)=(nc k 55 m,none,.right) := by
  have row:=literalRow k 54 m 55 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 162)
  rw [mode0 m hm] at row
  exact row
private theorem r055_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 55 m) (none)=(nc k 56 m,none,.stay) := by
  have row:=literalRow k 55 m 56 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 165)
  rw [mode0 m hm] at row
  exact row
private theorem r055_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 55 m) (some false)=(nc k 55 m,none,.right) := by
  have row:=literalRow k 55 m 55 0 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 166)
  rw [mode0 m hm] at row
  exact row
private theorem r055_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 55 m) (some true)=(nc k 55 m,none,.right) := by
  have row:=literalRow k 55 m 55 0 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 167)
  rw [mode0 m hm] at row
  exact row
private theorem r056_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 56 m) (none)=(nc k 57 m,none,.right) := by
  have row:=literalRow k 56 m 57 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 168)
  rw [mode0 m hm] at row
  exact row
private theorem r057_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 57 m) (none)=(nc k 58 m,none,.stay) := by
  have row:=literalRow k 57 m 58 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 171)
  rw [mode0 m hm] at row
  exact row
private theorem r057_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 57 m) (some false)=(nc k 57 m,none,.right) := by
  have row:=literalRow k 57 m 57 0 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 172)
  rw [mode0 m hm] at row
  exact row
private theorem r057_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 57 m) (some true)=(nc k 57 m,none,.right) := by
  have row:=literalRow k 57 m 57 0 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 173)
  rw [mode0 m hm] at row
  exact row
private theorem r058_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 58 m) (none)=(nc k 59 m,none,.right) := by
  have row:=literalRow k 58 m 59 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 174)
  rw [mode0 m hm] at row
  exact row
private theorem r059_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 59 m) (none)=(nc k 60 m,none,.stay) := by
  have row:=literalRow k 59 m 60 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 177)
  rw [mode0 m hm] at row
  exact row
private theorem r059_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 59 m) (some false)=(nc k 59 m,none,.right) := by
  have row:=literalRow k 59 m 59 0 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 178)
  rw [mode0 m hm] at row
  exact row
private theorem r059_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 59 m) (some true)=(nc k 59 m,none,.right) := by
  have row:=literalRow k 59 m 59 0 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 179)
  rw [mode0 m hm] at row
  exact row
private theorem r060_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 60 m) (none)=(nc k 61 m,none,.right) := by
  have row:=literalRow k 60 m 61 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 180)
  rw [mode0 m hm] at row
  exact row
private theorem r061_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 61 m) (none)=(nc k 62 m,none,.stay) := by
  have row:=literalRow k 61 m 62 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 183)
  rw [mode0 m hm] at row
  exact row
private theorem r061_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 61 m) (some false)=(nc k 61 m,none,.right) := by
  have row:=literalRow k 61 m 61 0 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 184)
  rw [mode0 m hm] at row
  exact row
private theorem r061_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 61 m) (some true)=(nc k 61 m,none,.right) := by
  have row:=literalRow k 61 m 61 0 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 185)
  rw [mode0 m hm] at row
  exact row
private theorem r062_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 62 m) (none)=(nc k 63 m,none,.right) := by
  have row:=literalRow k 62 m 63 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 186)
  rw [mode0 m hm] at row
  exact row
private theorem r063_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 63 m) (none)=(nc k 64 m,none,.stay) := by
  have row:=literalRow k 63 m 64 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 189)
  rw [mode0 m hm] at row
  exact row
private theorem r063_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 63 m) (some false)=(nc k 63 m,none,.right) := by
  have row:=literalRow k 63 m 63 0 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 190)
  rw [mode0 m hm] at row
  exact row
private theorem r063_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 63 m) (some true)=(nc k 63 m,none,.right) := by
  have row:=literalRow k 63 m 63 0 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 191)
  rw [mode0 m hm] at row
  exact row
private theorem r064_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 64 m) (none)=(nc k 65 m,none,.left) := by
  have row:=literalRow k 64 m 65 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 192)
  rw [mode0 m hm] at row
  exact row
private theorem r065_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 65 m) (none)=(nc k 65 m,none,.left) := by
  have row:=literalRow k 65 m 65 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 195)
  rw [mode0 m hm] at row
  exact row
private theorem r065_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 65 m) (some false)=(nc k 66 m,some false,.left) := by
  have row:=literalRow k 65 m 66 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 196)
  rw [mode0 m hm] at row
  exact row
private theorem r065_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 65 m) (some true)=(nc k 66 m,some true,.left) := by
  have row:=literalRow k 65 m 66 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 197)
  rw [mode0 m hm] at row
  exact row
private theorem r066_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 66 m) (none)=(nc k 67 m,none,.stay) := by
  have row:=literalRow k 66 m 67 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 198)
  rw [mode0 m hm] at row
  exact row
private theorem r066_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 66 m) (some false)=(nc k 66 m,some false,.left) := by
  have row:=literalRow k 66 m 66 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 199)
  rw [mode0 m hm] at row
  exact row
private theorem r066_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 66 m) (some true)=(nc k 66 m,some true,.left) := by
  have row:=literalRow k 66 m 66 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 200)
  rw [mode0 m hm] at row
  exact row
private theorem r067_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 67 m) (none)=(nc k 68 m,none,.right) := by
  have row:=literalRow k 67 m 68 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 201)
  rw [mode0 m hm] at row
  exact row
private theorem r068_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 68 m) (none)=(nc k 74 m,none,.stay) := by
  have row:=literalRow k 68 m 74 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 204)
  rw [mode0 m hm] at row
  exact row
private theorem r068_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 68 m) (some false)=(nc k 69 m,some true,.right) := by
  have row:=literalRow k 68 m 69 2 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 205)
  rw [mode0 m hm] at row
  exact row
private theorem r068_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 68 m) (some true)=(nc k 68 m,some true,.right) := by
  have row:=literalRow k 68 m 68 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 206)
  rw [mode0 m hm] at row
  exact row
private theorem r069_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 69 m) (none)=(nc k 70 m,none,.stay) := by
  have row:=literalRow k 69 m 70 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 207)
  rw [mode0 m hm] at row
  exact row
private theorem r069_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 69 m) (some false)=(nc k 69 m,some false,.right) := by
  have row:=literalRow k 69 m 69 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 208)
  rw [mode0 m hm] at row
  exact row
private theorem r069_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 69 m) (some true)=(nc k 69 m,some true,.right) := by
  have row:=literalRow k 69 m 69 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 209)
  rw [mode0 m hm] at row
  exact row
private theorem r070_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 70 m) (none)=(nc k 71 m,none,.right) := by
  have row:=literalRow k 70 m 71 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 210)
  rw [mode0 m hm] at row
  exact row
private theorem r071_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 71 m) (none)=(nc k 72 m,some false,.left) := by
  have row:=literalRow k 71 m 72 1 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 213)
  rw [mode0 m hm] at row
  exact row
private theorem r071_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 71 m) (some false)=(nc k 71 m,some false,.right) := by
  have row:=literalRow k 71 m 71 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 214)
  rw [mode0 m hm] at row
  exact row
private theorem r071_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 71 m) (some true)=(nc k 71 m,some true,.right) := by
  have row:=literalRow k 71 m 71 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 215)
  rw [mode0 m hm] at row
  exact row
private theorem r072_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 72 m) (none)=(nc k 73 m,none,.stay) := by
  have row:=literalRow k 72 m 73 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 216)
  rw [mode0 m hm] at row
  exact row
private theorem r072_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 72 m) (some false)=(nc k 72 m,some false,.left) := by
  have row:=literalRow k 72 m 72 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 217)
  rw [mode0 m hm] at row
  exact row
private theorem r072_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 72 m) (some true)=(nc k 72 m,some true,.left) := by
  have row:=literalRow k 72 m 72 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 218)
  rw [mode0 m hm] at row
  exact row
private theorem r073_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 73 m) (none)=(nc k 66 m,none,.left) := by
  have row:=literalRow k 73 m 66 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 219)
  rw [mode0 m hm] at row
  exact row
private theorem r074_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 74 m) (none)=(nc k 75 m,none,.right) := by
  have row:=literalRow k 74 m 75 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 222)
  rw [mode0 m hm] at row
  exact row
private theorem r075_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 75 m) (none)=(nc k 76 m,none,.stay) := by
  have row:=literalRow k 75 m 76 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 225)
  rw [mode0 m hm] at row
  exact row
private theorem r075_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 75 m) (some false)=(nc k 75 m,some false,.right) := by
  have row:=literalRow k 75 m 75 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 226)
  rw [mode0 m hm] at row
  exact row
private theorem r075_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 75 m) (some true)=(nc k 75 m,some true,.right) := by
  have row:=literalRow k 75 m 75 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 227)
  rw [mode0 m hm] at row
  exact row
private theorem r076_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 76 m) (none)=(nc k 77 m,none,.left) := by
  have row:=literalRow k 76 m 77 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 228)
  rw [mode0 m hm] at row
  exact row
private theorem r077_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 77 m) (some false)=(nc k 78 m,none,.left) := by
  have row:=literalRow k 77 m 78 0 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 232)
  rw [mode0 m hm] at row
  exact row
private theorem r078_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 78 m) (none)=(nc k 79 m,none,.stay) := by
  have row:=literalRow k 78 m 79 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 234)
  rw [mode0 m hm] at row
  exact row
private theorem r078_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 78 m) (some false)=(nc k 78 m,some true,.left) := by
  have row:=literalRow k 78 m 78 2 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 235)
  rw [mode0 m hm] at row
  exact row
private theorem r078_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 78 m) (some true)=(nc k 78 m,some true,.left) := by
  have row:=literalRow k 78 m 78 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 236)
  rw [mode0 m hm] at row
  exact row
private theorem r079_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 79 m) (none)=(nc k 80 m,some true,.left) := by
  have row:=literalRow k 79 m 80 2 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 237)
  rw [mode0 m hm] at row
  exact row
private theorem r080_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 80 m) (none)=(nc k 81 m,none,.stay) := by
  have row:=literalRow k 80 m 81 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 240)
  rw [mode0 m hm] at row
  exact row
private theorem r080_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 80 m) (some false)=(nc k 80 m,some true,.left) := by
  have row:=literalRow k 80 m 80 2 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 241)
  rw [mode0 m hm] at row
  exact row
private theorem r080_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 80 m) (some true)=(nc k 80 m,some true,.left) := by
  have row:=literalRow k 80 m 80 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 242)
  rw [mode0 m hm] at row
  exact row
private theorem r081_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 81 m) (none)=(nc k 82 m,none,.left) := by
  have row:=literalRow k 81 m 82 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 243)
  rw [mode0 m hm] at row
  exact row
private theorem r082_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 82 m) (some false)=(nc k 83 m,some false,.left) := by
  have row:=literalRow k 82 m 83 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 247)
  rw [mode0 m hm] at row
  exact row
private theorem r083_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 83 m) (none)=(nc k 83 m,none,.left) := by
  have row:=literalRow k 83 m 83 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 249)
  rw [mode0 m hm] at row
  exact row
private theorem r083_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 83 m) (some true)=(nc k 84 m,some true,.left) := by
  have row:=literalRow k 83 m 84 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 251)
  rw [mode0 m hm] at row
  exact row
private theorem r084_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 84 m) (none)=(nc k 85 m,none,.left) := by
  have row:=literalRow k 84 m 85 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 252)
  rw [mode0 m hm] at row
  exact row
private theorem r084_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 84 m) (some true)=(nc k 84 m,some true,.left) := by
  have row:=literalRow k 84 m 84 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 254)
  rw [mode0 m hm] at row
  exact row
private theorem r085_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 85 m) (none)=(nc k 86 m,none,.stay) := by
  have row:=literalRow k 85 m 86 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 255)
  rw [mode0 m hm] at row
  exact row
private theorem r085_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 85 m) (some false)=(nc k 85 m,some false,.left) := by
  have row:=literalRow k 85 m 85 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 256)
  rw [mode0 m hm] at row
  exact row
private theorem r085_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 85 m) (some true)=(nc k 85 m,some false,.left) := by
  have row:=literalRow k 85 m 85 1 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 257)
  rw [mode0 m hm] at row
  exact row
private theorem r086_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 86 m) (none)=(nc k 87 m,none,.left) := by
  have row:=literalRow k 86 m 87 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 258)
  rw [mode0 m hm] at row
  exact row
private theorem r087_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 87 m) (none)=(nc k 88 m,none,.stay) := by
  have row:=literalRow k 87 m 88 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 261)
  rw [mode0 m hm] at row
  exact row
private theorem r087_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 87 m) (some false)=(nc k 87 m,some false,.left) := by
  have row:=literalRow k 87 m 87 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 262)
  rw [mode0 m hm] at row
  exact row
private theorem r087_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 87 m) (some true)=(nc k 87 m,some true,.left) := by
  have row:=literalRow k 87 m 87 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 263)
  rw [mode0 m hm] at row
  exact row
#print axioms r052_0
#print axioms r053_0
#print axioms r053_1
#print axioms r053_2
#print axioms r054_0
#print axioms r055_0
#print axioms r055_1
#print axioms r055_2
#print axioms r056_0
#print axioms r057_0
#print axioms r057_1
#print axioms r057_2
#print axioms r058_0
#print axioms r059_0
#print axioms r059_1
#print axioms r059_2
#print axioms r060_0
#print axioms r061_0
#print axioms r061_1
#print axioms r061_2
#print axioms r062_0
#print axioms r063_0
#print axioms r063_1
#print axioms r063_2
#print axioms r064_0
#print axioms r065_0
#print axioms r065_1
#print axioms r065_2
#print axioms r066_0
#print axioms r066_1
#print axioms r066_2
#print axioms r067_0
#print axioms r068_0
#print axioms r068_1
#print axioms r068_2
#print axioms r069_0
#print axioms r069_1
#print axioms r069_2
#print axioms r070_0
#print axioms r071_0
#print axioms r071_1
#print axioms r071_2
#print axioms r072_0
#print axioms r072_1
#print axioms r072_2
#print axioms r073_0
#print axioms r074_0
#print axioms r075_0
#print axioms r075_1
#print axioms r075_2
#print axioms r076_0
#print axioms r077_1
#print axioms r078_0
#print axioms r078_1
#print axioms r078_2
#print axioms r079_0
#print axioms r080_0
#print axioms r080_1
#print axioms r080_2
#print axioms r081_0
#print axioms r082_1
#print axioms r083_0
#print axioms r083_2
#print axioms r084_0
#print axioms r084_2
#print axioms r085_0
#print axioms r085_1
#print axioms r085_2
#print axioms r086_0
#print axioms r087_0
#print axioms r087_1
#print axioms r087_2
end VirtualFinalClosure.GrowRows
