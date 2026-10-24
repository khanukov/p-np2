import InputRead.Machine
namespace InputRead.Prototype
open Pnp3.Complexity.Uniform.V1
def dump (name : String) (M : UniformTM) : IO Unit := do
  IO.println s!"machine|{name}|{M.stateCount}|{M.start.val}|{M.accept.val}|{M.reject.val}"
  for i in List.range M.stateCount do
    if h : i < M.stateCount then
      for b in [none, some false, some true] do
        let a := M.step ⟨i,h⟩ b
        let sym := match b with | none => 0 | some false => 1 | some true => 2
        let out := match a.2.1 with | none => 0 | some false => 1 | some true => 2
        let mv := match a.2.2 with | .left => -1 | .stay => 0 | .right => 1
        IO.println s!"row|{name}|{i}|{sym}|{a.1.val}|{out}|{mv}"
#eval dump "reader" machine
#eval dump "raw" rawMachine
end InputRead.Prototype
