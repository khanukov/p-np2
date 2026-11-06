import VirtualLeaf.Raw
namespace CanonicalLeaf
open Pnp3.Complexity.Uniform.V1
set_option maxRecDepth 10000
/-- Same finite controls as the valid forward reader; exactly two occupied extra2 rows change. -/
private def rows (k : Nat) (s : Fin (VirtualLeaf.machine k).stateCount) (b : Option Bool) :
    Fin (VirtualLeaf.machine k).stateCount × Option Bool × Move :=
  match b with
  | none => (VirtualLeaf.machine k).step s none
  | some v => if s=VirtualLeaf.extra k ⟨2,by decide⟩ then
      (VirtualLeaf.extra k ⟨if v then 5 else 4,by cases v <;> decide⟩,some v,.right)
    else (VirtualLeaf.machine k).step s (some v)
def machine (k : Nat) : UniformTM where
  stateCount := (VirtualLeaf.machine k).stateCount
  start := (VirtualLeaf.machine k).start
  accept := (VirtualLeaf.machine k).accept
  reject := (VirtualLeaf.machine k).reject
  accept_ne_reject := (VirtualLeaf.machine k).accept_ne_reject
  rawStep := rows k
/-- Real mode2 on the unchanged repaired-base control embedding. -/
def entry (k : Nat) : Fin (machine k).stateCount := VirtualLeaf.embed k (VirtualLeaf.entry k)
/-- WORK leaf-result controls, encoding size1 and the actual read value. -/
def result (k : Nat) (b : Bool) : Fin (machine k).stateCount := VirtualLeaf.result k b
#eval do
  for k in [0,1,2,64] do
    let M:=machine k
    IO.println s!"meta|{k}|{M.stateCount}|{M.start.val}|{M.accept.val}|{M.reject.val}|{(entry k).val}"
    for q in List.finRange M.stateCount do
      for b in [none,some false,some true] do
        let a:=M.step q b
        let s:Nat:=match b with | none => 0 | some false => 1 | some true => 2
        let w:Nat:=match a.2.1 with | none => 0 | some false => 1 | some true => 2
        let d:Int:=match a.2.2 with | .left => -1 | .stay => 0 | .right => 1
        IO.println s!"row|{k}|{q.val}|{s}|{a.1.val}|{w}|{d}"
end CanonicalLeaf
