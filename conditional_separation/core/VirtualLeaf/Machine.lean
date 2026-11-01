import RawPrelude.Raw
import IngressRepair.Runtime
namespace VirtualLeaf
set_option maxRecDepth 10000
open Pnp3.Complexity.Uniform.V1
/-- Injective identity-on-index control embedding; no tape or head change. -/
def embed (k : Nat) (s : Fin (IngressRepair.machine k).stateCount) :
    Fin ((IngressRepair.machine k).stateCount+8) := ⟨s.val,by omega⟩
def extra (k : Nat) (j : Fin 8) : Fin ((IngressRepair.machine k).stateCount+8) :=
  ⟨(IngressRepair.machine k).stateCount+j.val,by omega⟩
def entry (k : Nat) : Fin (IngressRepair.machine k).stateCount :=
  IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.mReady k ⟨2,by decide⟩)
def result (k : Nat) (b : Bool) : Fin ((IngressRepair.machine k).stateCount+8) :=
  extra k ⟨if b then 7 else 6,by cases b <;> decide⟩
private def rows (k : Nat) (s : Fin ((IngressRepair.machine k).stateCount+8)) (b : Option Bool) :
    Fin ((IngressRepair.machine k).stateCount+8) × Option Bool × Move :=
  if h : s.val < (IngressRepair.machine k).stateCount then
    let old : Fin (IngressRepair.machine k).stateCount := ⟨s.val,h⟩
    if old=entry k ∧ b=none then (extra k ⟨0,by decide⟩,none,.stay)
    else let a:=(IngressRepair.machine k).step old b; (embed k a.1,a.2)
  else
    match s.val-(IngressRepair.machine k).stateCount,b with
    | 0,none => (extra k ⟨1,by decide⟩,none,.stay)
    | 1,none => (extra k ⟨2,by decide⟩,none,.left)
    | 2,some v => (extra k ⟨2,by decide⟩,some v,.left)
    | 2,none => (extra k ⟨3,by decide⟩,none,.right)
    | 3,some v => (extra k ⟨if v then 5 else 4,by cases v <;> decide⟩,some v,.right)
    | 3,none => (embed k (IngressRepair.machine k).reject,none,.stay)
    | 4,some v => (extra k ⟨4,by decide⟩,some v,.right)
    | 5,some v => (extra k ⟨5,by decide⟩,some v,.right)
    | 4,none => (result k false,some false,.stay)
    | 5,none => (result k true,some true,.stay)
    | 6,v => (result k false,v,.stay)
    | 7,v => (result k true,v,.stay)
    | _,v => (embed k (IngressRepair.machine k).reject,v,.stay)
/-- Local candidate: exactly eight extra controls; only old mode2/none is intercepted. -/
def machine (k : Nat) : UniformTM where
  stateCount := (IngressRepair.machine k).stateCount+8
  start := embed k (IngressRepair.machine k).start
  accept := embed k (IngressRepair.machine k).accept
  reject := embed k (IngressRepair.machine k).reject
  accept_ne_reject := by
    intro h; apply (IngressRepair.machine k).accept_ne_reject
    apply Fin.ext
    exact congrArg (fun q : Fin ((IngressRepair.machine k).stateCount+8) => q.val) h
  rawStep := rows k
def config (k : Nat) {N B : Nat} (c : Config (IngressRepair.machine k).stateCount N B) :
    Config (machine k).stateCount N B := ⟨embed k c.state,c.head,c.tape⟩
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
end VirtualLeaf
