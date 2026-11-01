import VirtualFinalClosure.UnaryPath
namespace VirtualFinalClosure.GuardUnary
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.UnaryPath","VirtualFinalClosure.UnaryPath","decrement","decrement",(1:Nat)),
      ("VirtualFinalClosure.UnaryPath","VirtualFinalClosure.UnaryPath","increment","increment",(1:Nat)),
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
private theorem row93_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 93 m) (none)=(nc k 94 m,none,.right) := by
  have row:=literalRow k 93 m 94 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 279)
  rw [mode0 m hm] at row
  exact row
private theorem row94_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 94 m) (none)=(nc k 95 m,none,.left) := by
  have row:=literalRow k 94 m 95 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 282)
  rw [mode0 m hm] at row
  exact row
private theorem row94_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 94 m) (some false)=(nc k 95 m,some false,.left) := by
  have row:=literalRow k 94 m 95 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 283)
  rw [mode0 m hm] at row
  exact row
private theorem row94_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 94 m) (some true)=(nc k 94 m,some true,.right) := by
  have row:=literalRow k 94 m 94 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 284)
  rw [mode0 m hm] at row
  exact row
private theorem row95_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 95 m) (none)=(nc k 183 m,none,.stay) := by
  have row:=literalRow k 95 m 183 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 285)
  rw [mode0 m hm] at row
  exact row
private theorem row95_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 95 m) (some true)=(nc k 96 m,some false,.left) := by
  have row:=literalRow k 95 m 96 1 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 287)
  rw [mode0 m hm] at row
  exact row
private theorem row96_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 96 m) (none)=(nc k 97 m,none,.stay) := by
  have row:=literalRow k 96 m 97 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 288)
  rw [mode0 m hm] at row
  exact row
private theorem row96_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 96 m) (some false)=(nc k 96 m,some false,.left) := by
  have row:=literalRow k 96 m 96 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 289)
  rw [mode0 m hm] at row
  exact row
private theorem row96_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 96 m) (some true)=(nc k 96 m,some true,.left) := by
  have row:=literalRow k 96 m 96 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 290)
  rw [mode0 m hm] at row
  exact row
private theorem row99_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 99 m) (none)=(nc k 100 m,none,.right) := by
  have row:=literalRow k 99 m 100 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 297)
  rw [mode0 m hm] at row
  exact row
private theorem row100_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 100 m) (none)=(nc k 101 m,none,.left) := by
  have row:=literalRow k 100 m 101 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 300)
  rw [mode0 m hm] at row
  exact row
private theorem row100_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 100 m) (some false)=(nc k 101 m,some false,.left) := by
  have row:=literalRow k 100 m 101 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 301)
  rw [mode0 m hm] at row
  exact row
private theorem row100_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 100 m) (some true)=(nc k 100 m,some true,.right) := by
  have row:=literalRow k 100 m 100 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 302)
  rw [mode0 m hm] at row
  exact row
private theorem row101_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 101 m) (none)=(nc k 121 m,none,.stay) := by
  have row:=literalRow k 101 m 121 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 303)
  rw [mode0 m hm] at row
  exact row
private theorem row101_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 101 m) (some true)=(nc k 102 m,some false,.left) := by
  have row:=literalRow k 101 m 102 1 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 305)
  rw [mode0 m hm] at row
  exact row
private theorem row102_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 102 m) (none)=(nc k 103 m,none,.stay) := by
  have row:=literalRow k 102 m 103 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 306)
  rw [mode0 m hm] at row
  exact row
private theorem row102_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 102 m) (some false)=(nc k 102 m,some false,.left) := by
  have row:=literalRow k 102 m 102 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 307)
  rw [mode0 m hm] at row
  exact row
private theorem row102_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 102 m) (some true)=(nc k 102 m,some true,.left) := by
  have row:=literalRow k 102 m 102 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 308)
  rw [mode0 m hm] at row
  exact row
private theorem row107_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 107 m) (none)=(nc k 108 m,none,.right) := by
  have row:=literalRow k 107 m 108 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 321)
  rw [mode0 m hm] at row
  exact row
private theorem row108_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 108 m) (none)=(nc k 109 m,none,.left) := by
  have row:=literalRow k 108 m 109 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 324)
  rw [mode0 m hm] at row
  exact row
private theorem row108_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 108 m) (some false)=(nc k 109 m,some false,.left) := by
  have row:=literalRow k 108 m 109 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 325)
  rw [mode0 m hm] at row
  exact row
private theorem row108_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 108 m) (some true)=(nc k 108 m,some true,.right) := by
  have row:=literalRow k 108 m 108 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 326)
  rw [mode0 m hm] at row
  exact row
private theorem row109_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 109 m) (none)=(nc k 213 m,none,.stay) := by
  have row:=literalRow k 109 m 213 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 327)
  rw [mode0 m hm] at row
  exact row
private theorem row109_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 109 m) (some true)=(nc k 110 m,some false,.left) := by
  have row:=literalRow k 109 m 110 1 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 329)
  rw [mode0 m hm] at row
  exact row
private theorem row110_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 110 m) (none)=(nc k 111 m,none,.stay) := by
  have row:=literalRow k 110 m 111 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 330)
  rw [mode0 m hm] at row
  exact row
private theorem row110_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 110 m) (some false)=(nc k 110 m,some false,.left) := by
  have row:=literalRow k 110 m 110 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 331)
  rw [mode0 m hm] at row
  exact row
private theorem row110_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 110 m) (some true)=(nc k 110 m,some true,.left) := by
  have row:=literalRow k 110 m 110 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 332)
  rw [mode0 m hm] at row
  exact row
private theorem row113_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 113 m) (none)=(nc k 114 m,none,.right) := by
  have row:=literalRow k 113 m 114 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 339)
  rw [mode0 m hm] at row
  exact row
private theorem row114_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 114 m) (none)=(nc k 205 m,none,.stay) := by
  have row:=literalRow k 114 m 205 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 342)
  rw [mode0 m hm] at row
  exact row
private theorem row114_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 114 m) (some false)=(nc k 115 m,some true,.left) := by
  have row:=literalRow k 114 m 115 2 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 343)
  rw [mode0 m hm] at row
  exact row
private theorem row114_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 114 m) (some true)=(nc k 114 m,some true,.right) := by
  have row:=literalRow k 114 m 114 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 344)
  rw [mode0 m hm] at row
  exact row
private theorem row115_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 115 m) (none)=(nc k 116 m,none,.stay) := by
  have row:=literalRow k 115 m 116 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 345)
  rw [mode0 m hm] at row
  exact row
private theorem row115_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 115 m) (some false)=(nc k 115 m,some false,.left) := by
  have row:=literalRow k 115 m 115 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 346)
  rw [mode0 m hm] at row
  exact row
private theorem row115_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 115 m) (some true)=(nc k 115 m,some true,.left) := by
  have row:=literalRow k 115 m 115 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 347)
  rw [mode0 m hm] at row
  exact row
private theorem row116_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 116 m) (none)=(nc k 117 m,none,.right) := by
  have row:=literalRow k 116 m 117 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 348)
  rw [mode0 m hm] at row
  exact row
private theorem row117_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 117 m) (none)=(nc k 205 m,none,.stay) := by
  have row:=literalRow k 117 m 205 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 351)
  rw [mode0 m hm] at row
  exact row
private theorem row117_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 117 m) (some false)=(nc k 118 m,some true,.left) := by
  have row:=literalRow k 117 m 118 2 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 352)
  rw [mode0 m hm] at row
  exact row
private theorem row117_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 117 m) (some true)=(nc k 117 m,some true,.right) := by
  have row:=literalRow k 117 m 117 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 353)
  rw [mode0 m hm] at row
  exact row
private theorem row118_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 118 m) (none)=(nc k 119 m,none,.stay) := by
  have row:=literalRow k 118 m 119 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 354)
  rw [mode0 m hm] at row
  exact row
private theorem row118_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 118 m) (some false)=(nc k 118 m,some false,.left) := by
  have row:=literalRow k 118 m 118 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 355)
  rw [mode0 m hm] at row
  exact row
private theorem row118_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 118 m) (some true)=(nc k 118 m,some true,.left) := by
  have row:=literalRow k 118 m 118 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 356)
  rw [mode0 m hm] at row
  exact row
private theorem row123_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 123 m) (none)=(nc k 124 m,none,.right) := by
  have row:=literalRow k 123 m 124 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 369)
  rw [mode0 m hm] at row
  exact row
private theorem row124_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 124 m) (none)=(nc k 125 m,none,.left) := by
  have row:=literalRow k 124 m 125 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 372)
  rw [mode0 m hm] at row
  exact row
private theorem row124_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 124 m) (some false)=(nc k 125 m,some false,.left) := by
  have row:=literalRow k 124 m 125 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 373)
  rw [mode0 m hm] at row
  exact row
private theorem row124_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 124 m) (some true)=(nc k 124 m,some true,.right) := by
  have row:=literalRow k 124 m 124 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 374)
  rw [mode0 m hm] at row
  exact row
private theorem row125_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 125 m) (none)=(nc k 134 m,none,.stay) := by
  have row:=literalRow k 125 m 134 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 375)
  rw [mode0 m hm] at row
  exact row
private theorem row125_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 125 m) (some true)=(nc k 126 m,some false,.left) := by
  have row:=literalRow k 125 m 126 1 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 377)
  rw [mode0 m hm] at row
  exact row
private theorem row126_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 126 m) (none)=(nc k 127 m,none,.stay) := by
  have row:=literalRow k 126 m 127 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 378)
  rw [mode0 m hm] at row
  exact row
private theorem row126_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 126 m) (some false)=(nc k 126 m,some false,.left) := by
  have row:=literalRow k 126 m 126 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 379)
  rw [mode0 m hm] at row
  exact row
private theorem row126_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 126 m) (some true)=(nc k 126 m,some true,.left) := by
  have row:=literalRow k 126 m 126 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 380)
  rw [mode0 m hm] at row
  exact row
private theorem row129_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 129 m) (none)=(nc k 130 m,none,.right) := by
  have row:=literalRow k 129 m 130 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 387)
  rw [mode0 m hm] at row
  exact row
private theorem row130_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 130 m) (none)=(nc k 199 m,none,.stay) := by
  have row:=literalRow k 130 m 199 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 390)
  rw [mode0 m hm] at row
  exact row
private theorem row130_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 130 m) (some false)=(nc k 131 m,some true,.left) := by
  have row:=literalRow k 130 m 131 2 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 391)
  rw [mode0 m hm] at row
  exact row
private theorem row130_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 130 m) (some true)=(nc k 130 m,some true,.right) := by
  have row:=literalRow k 130 m 130 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 392)
  rw [mode0 m hm] at row
  exact row
private theorem row131_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 131 m) (none)=(nc k 132 m,none,.stay) := by
  have row:=literalRow k 131 m 132 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 393)
  rw [mode0 m hm] at row
  exact row
private theorem row131_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 131 m) (some false)=(nc k 131 m,some false,.left) := by
  have row:=literalRow k 131 m 131 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 394)
  rw [mode0 m hm] at row
  exact row
private theorem row131_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 131 m) (some true)=(nc k 131 m,some true,.left) := by
  have row:=literalRow k 131 m 131 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 395)
  rw [mode0 m hm] at row
  exact row
private theorem row141_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 141 m) (none)=(nc k 142 m,none,.right) := by
  have row:=literalRow k 141 m 142 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 423)
  rw [mode0 m hm] at row
  exact row
private theorem row142_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 142 m) (none)=(nc k 143 m,none,.left) := by
  have row:=literalRow k 142 m 143 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 426)
  rw [mode0 m hm] at row
  exact row
private theorem row142_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 142 m) (some false)=(nc k 143 m,some false,.left) := by
  have row:=literalRow k 142 m 143 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 427)
  rw [mode0 m hm] at row
  exact row
private theorem row142_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 142 m) (some true)=(nc k 142 m,some true,.right) := by
  have row:=literalRow k 142 m 142 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 428)
  rw [mode0 m hm] at row
  exact row
private theorem row143_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 143 m) (none)=(nc k 213 m,none,.stay) := by
  have row:=literalRow k 143 m 213 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 429)
  rw [mode0 m hm] at row
  exact row
private theorem row143_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 143 m) (some true)=(nc k 144 m,some false,.left) := by
  have row:=literalRow k 143 m 144 1 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 431)
  rw [mode0 m hm] at row
  exact row
private theorem row144_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 144 m) (none)=(nc k 145 m,none,.stay) := by
  have row:=literalRow k 144 m 145 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 432)
  rw [mode0 m hm] at row
  exact row
private theorem row144_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 144 m) (some false)=(nc k 144 m,some false,.left) := by
  have row:=literalRow k 144 m 144 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 433)
  rw [mode0 m hm] at row
  exact row
private theorem row144_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 144 m) (some true)=(nc k 144 m,some true,.left) := by
  have row:=literalRow k 144 m 144 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 434)
  rw [mode0 m hm] at row
  exact row
private theorem row149_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 149 m) (none)=(nc k 150 m,none,.right) := by
  have row:=literalRow k 149 m 150 0 2 0 (none) (by decide) hm (by decide) (by run_tac cellTac 447)
  rw [mode0 m hm] at row
  exact row
private theorem row150_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 150 m) (none)=(nc k 199 m,none,.stay) := by
  have row:=literalRow k 150 m 199 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 450)
  rw [mode0 m hm] at row
  exact row
private theorem row150_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 150 m) (some false)=(nc k 151 m,some true,.left) := by
  have row:=literalRow k 150 m 151 2 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 451)
  rw [mode0 m hm] at row
  exact row
private theorem row150_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 150 m) (some true)=(nc k 150 m,some true,.right) := by
  have row:=literalRow k 150 m 150 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 452)
  rw [mode0 m hm] at row
  exact row
private theorem row151_0 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 151 m) (none)=(nc k 152 m,none,.stay) := by
  have row:=literalRow k 151 m 152 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 453)
  rw [mode0 m hm] at row
  exact row
private theorem row151_1 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 151 m) (some false)=(nc k 151 m,some false,.left) := by
  have row:=literalRow k 151 m 151 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 454)
  rw [mode0 m hm] at row
  exact row
private theorem row151_2 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 151 m) (some true)=(nc k 151 m,some true,.left) := by
  have row:=literalRow k 151 m 151 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 455)
  rw [mode0 m hm] at row
  exact row
/-- Literal ellDec macro from the frozen ROM, including width0. -/
private theorem ellDec (k P m base width value : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (hv : value ≤ width) (fit : base+width+1 ≤ P)
    (sep : T base=none) (last : T (base+width+1)=none)
    (digits : ∀ i,base < i → i < base+width+1 → T i=some (decide (i ≤ base+value))) :
    GPath (M:=machine k) P (2*value+3) (C k 93 m base T)
      (node (if value=0 then nc k 183 m else nc k 97 m) base
        (if value=0 then T else put T (base+value) (some false))) := by
  apply decrement (nc k 93 m) (nc k 94 m) (nc k 95 m) (nc k 96 m) (nc k 97 m) (nc k 183 m) P base width value T
    (row93_0 k m hm) (row94_2 k m hm) _ (row95_0 k m hm)
    (row95_2 k m hm) _ (row96_0 k m hm) hv fit sep last digits
  · intro b hb;rcases hb with rfl|rfl
    · exact row94_0 k m hm
    · exact row94_1 k m hm
  · intro b;cases b
    · exact row96_1 k m hm
    · exact row96_2 k m hm
/-- Literal doubleDec3 macro from the frozen ROM, including width0. -/
private theorem doubleDec3 (k P m base width value : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (hv : value ≤ width) (fit : base+width+1 ≤ P)
    (sep : T base=none) (last : T (base+width+1)=none)
    (digits : ∀ i,base < i → i < base+width+1 → T i=some (decide (i ≤ base+value))) :
    GPath (M:=machine k) P (2*value+3) (C k 99 m base T)
      (node (if value=0 then nc k 121 m else nc k 103 m) base
        (if value=0 then T else put T (base+value) (some false))) := by
  apply decrement (nc k 99 m) (nc k 100 m) (nc k 101 m) (nc k 102 m) (nc k 103 m) (nc k 121 m) P base width value T
    (row99_0 k m hm) (row100_2 k m hm) _ (row101_0 k m hm)
    (row101_2 k m hm) _ (row102_0 k m hm) hv fit sep last digits
  · intro b hb;rcases hb with rfl|rfl
    · exact row100_0 k m hm
    · exact row100_1 k m hm
  · intro b;cases b
    · exact row102_1 k m hm
    · exact row102_2 k m hm
/-- Literal doubleQuota macro from the frozen ROM, including width0. -/
private theorem doubleQuota (k P m base width value : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (hv : value ≤ width) (fit : base+width+1 ≤ P)
    (sep : T base=none) (last : T (base+width+1)=none)
    (digits : ∀ i,base < i → i < base+width+1 → T i=some (decide (i ≤ base+value))) :
    GPath (M:=machine k) P (2*value+3) (C k 107 m base T)
      (node (if value=0 then nc k 213 m else nc k 111 m) base
        (if value=0 then T else put T (base+value) (some false))) := by
  apply decrement (nc k 107 m) (nc k 108 m) (nc k 109 m) (nc k 110 m) (nc k 111 m) (nc k 213 m) P base width value T
    (row107_0 k m hm) (row108_2 k m hm) _ (row109_0 k m hm)
    (row109_2 k m hm) _ (row110_0 k m hm) hv fit sep last digits
  · intro b hb;rcases hb with rfl|rfl
    · exact row108_0 k m hm
    · exact row108_1 k m hm
  · intro b;cases b
    · exact row110_1 k m hm
    · exact row110_2 k m hm
/-- Literal transferDec4 macro from the frozen ROM, including width0. -/
private theorem transferDec4 (k P m base width value : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (hv : value ≤ width) (fit : base+width+1 ≤ P)
    (sep : T base=none) (last : T (base+width+1)=none)
    (digits : ∀ i,base < i → i < base+width+1 → T i=some (decide (i ≤ base+value))) :
    GPath (M:=machine k) P (2*value+3) (C k 123 m base T)
      (node (if value=0 then nc k 134 m else nc k 127 m) base
        (if value=0 then T else put T (base+value) (some false))) := by
  apply decrement (nc k 123 m) (nc k 124 m) (nc k 125 m) (nc k 126 m) (nc k 127 m) (nc k 134 m) P base width value T
    (row123_0 k m hm) (row124_2 k m hm) _ (row125_0 k m hm)
    (row125_2 k m hm) _ (row126_0 k m hm) hv fit sep last digits
  · intro b hb;rcases hb with rfl|rfl
    · exact row124_0 k m hm
    · exact row124_1 k m hm
  · intro b;cases b
    · exact row126_1 k m hm
    · exact row126_2 k m hm
/-- Literal indexQuota macro from the frozen ROM, including width0. -/
private theorem indexQuota (k P m base width value : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (hv : value ≤ width) (fit : base+width+1 ≤ P)
    (sep : T base=none) (last : T (base+width+1)=none)
    (digits : ∀ i,base < i → i < base+width+1 → T i=some (decide (i ≤ base+value))) :
    GPath (M:=machine k) P (2*value+3) (C k 141 m base T)
      (node (if value=0 then nc k 213 m else nc k 145 m) base
        (if value=0 then T else put T (base+value) (some false))) := by
  apply decrement (nc k 141 m) (nc k 142 m) (nc k 143 m) (nc k 144 m) (nc k 145 m) (nc k 213 m) P base width value T
    (row141_0 k m hm) (row142_2 k m hm) _ (row143_0 k m hm)
    (row143_2 k m hm) _ (row144_0 k m hm) hv fit sep last digits
  · intro b hb;rcases hb with rfl|rfl
    · exact row142_0 k m hm
    · exact row142_1 k m hm
  · intro b;cases b
    · exact row144_1 k m hm
    · exact row144_2 k m hm
/-- Literal doubleInc4a macro; full-bank outcome is a live guard branch. -/
private theorem doubleInc4a (k P m base width value : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (hv : value ≤ width) (fit : base+width+1 ≤ P)
    (sep : T base=none) (last : T (base+width+1)=none)
    (digits : ∀ i,base < i → i < base+width+1 → T i=some (decide (i ≤ base+value))) :
    GPath (M:=machine k) P (if value < width then 2*value+3 else value+2) (C k 113 m base T)
      (if value < width then node (nc k 116 m) base (put T (base+value+1) (some true))
       else node (nc k 205 m) (base+width+1) T) := by
  apply increment (nc k 113 m) (nc k 114 m) (nc k 115 m) (nc k 116 m) (nc k 205 m) P base width value T
    (row113_0 k m hm) (row114_2 k m hm) (row114_1 k m hm) (row114_0 k m hm)
    _ (row115_0 k m hm) hv fit sep last digits
  intro b;cases b
  · exact row115_1 k m hm
  · exact row115_2 k m hm
/-- Literal doubleInc4b macro; full-bank outcome is a live guard branch. -/
private theorem doubleInc4b (k P m base width value : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (hv : value ≤ width) (fit : base+width+1 ≤ P)
    (sep : T base=none) (last : T (base+width+1)=none)
    (digits : ∀ i,base < i → i < base+width+1 → T i=some (decide (i ≤ base+value))) :
    GPath (M:=machine k) P (if value < width then 2*value+3 else value+2) (C k 116 m base T)
      (if value < width then node (nc k 119 m) base (put T (base+value+1) (some true))
       else node (nc k 205 m) (base+width+1) T) := by
  apply increment (nc k 116 m) (nc k 117 m) (nc k 118 m) (nc k 119 m) (nc k 205 m) P base width value T
    (row116_0 k m hm) (row117_2 k m hm) (row117_1 k m hm) (row117_0 k m hm)
    _ (row118_0 k m hm) hv fit sep last digits
  intro b;cases b
  · exact row118_1 k m hm
  · exact row118_2 k m hm
/-- Literal transferInc3 macro; full-bank outcome is a live guard branch. -/
private theorem transferInc3 (k P m base width value : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (hv : value ≤ width) (fit : base+width+1 ≤ P)
    (sep : T base=none) (last : T (base+width+1)=none)
    (digits : ∀ i,base < i → i < base+width+1 → T i=some (decide (i ≤ base+value))) :
    GPath (M:=machine k) P (if value < width then 2*value+3 else value+2) (C k 129 m base T)
      (if value < width then node (nc k 132 m) base (put T (base+value+1) (some true))
       else node (nc k 199 m) (base+width+1) T) := by
  apply increment (nc k 129 m) (nc k 130 m) (nc k 131 m) (nc k 132 m) (nc k 199 m) P base width value T
    (row129_0 k m hm) (row130_2 k m hm) (row130_1 k m hm) (row130_0 k m hm)
    _ (row131_0 k m hm) hv fit sep last digits
  intro b;cases b
  · exact row131_1 k m hm
  · exact row131_2 k m hm
/-- Literal indexInc3 macro; full-bank outcome is a live guard branch. -/
private theorem indexInc3 (k P m base width value : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (hv : value ≤ width) (fit : base+width+1 ≤ P)
    (sep : T base=none) (last : T (base+width+1)=none)
    (digits : ∀ i,base < i → i < base+width+1 → T i=some (decide (i ≤ base+value))) :
    GPath (M:=machine k) P (if value < width then 2*value+3 else value+2) (C k 149 m base T)
      (if value < width then node (nc k 152 m) base (put T (base+value+1) (some true))
       else node (nc k 199 m) (base+width+1) T) := by
  apply increment (nc k 149 m) (nc k 150 m) (nc k 151 m) (nc k 152 m) (nc k 199 m) P base width value T
    (row149_0 k m hm) (row150_2 k m hm) (row150_1 k m hm) (row150_0 k m hm)
    _ (row151_0 k m hm) hv fit sep last digits
  intro b;cases b
  · exact row151_1 k m hm
  · exact row151_2 k m hm
#print axioms row93_0
#print axioms row94_0
#print axioms row94_1
#print axioms row94_2
#print axioms row95_0
#print axioms row95_2
#print axioms row96_0
#print axioms row96_1
#print axioms row96_2
#print axioms row99_0
#print axioms row100_0
#print axioms row100_1
#print axioms row100_2
#print axioms row101_0
#print axioms row101_2
#print axioms row102_0
#print axioms row102_1
#print axioms row102_2
#print axioms row107_0
#print axioms row108_0
#print axioms row108_1
#print axioms row108_2
#print axioms row109_0
#print axioms row109_2
#print axioms row110_0
#print axioms row110_1
#print axioms row110_2
#print axioms row113_0
#print axioms row114_0
#print axioms row114_1
#print axioms row114_2
#print axioms row115_0
#print axioms row115_1
#print axioms row115_2
#print axioms row116_0
#print axioms row117_0
#print axioms row117_1
#print axioms row117_2
#print axioms row118_0
#print axioms row118_1
#print axioms row118_2
#print axioms row123_0
#print axioms row124_0
#print axioms row124_1
#print axioms row124_2
#print axioms row125_0
#print axioms row125_2
#print axioms row126_0
#print axioms row126_1
#print axioms row126_2
#print axioms row129_0
#print axioms row130_0
#print axioms row130_1
#print axioms row130_2
#print axioms row131_0
#print axioms row131_1
#print axioms row131_2
#print axioms row141_0
#print axioms row142_0
#print axioms row142_1
#print axioms row142_2
#print axioms row143_0
#print axioms row143_2
#print axioms row144_0
#print axioms row144_1
#print axioms row144_2
#print axioms row149_0
#print axioms row150_0
#print axioms row150_1
#print axioms row150_2
#print axioms row151_0
#print axioms row151_1
#print axioms row151_2
#print axioms ellDec
#print axioms doubleDec3
#print axioms doubleQuota
#print axioms transferDec4
#print axioms indexQuota
#print axioms doubleInc4a
#print axioms doubleInc4b
#print axioms transferInc3
#print axioms indexInc3
end VirtualFinalClosure.GuardUnary
