import CanonicalLeaf.Raw
import PostWeight.Raw
namespace CarryWindow
open Pnp3.Complexity.Uniform.V1
set_option maxRecDepth 10000
/-- Injective old-control embedding; the tape and its dependent allocation are unchanged. -/
def embed (k : Nat) (s : Fin (CanonicalLeaf.machine k).stateCount) :
    Fin ((CanonicalLeaf.machine k).stateCount+25) := ⟨s.val,by omega⟩
/-- Fixed 25-control extension, independent of every input operand. -/
def extra (k : Nat) (j : Fin 25) : Fin ((CanonicalLeaf.machine k).stateCount+25) :=
  ⟨(CanonicalLeaf.machine k).stateCount+j.val,by omega⟩
private def oldq (k i : Nat) : Fin (CanonicalLeaf.machine k).stateCount :=
  VirtualLeaf.embed k (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k i))
private def liftAction (k : Nat) (a : Fin (CanonicalLeaf.machine k).stateCount × Option Bool × Move) :=
  (embed k a.1,a.2)
private def native (k : Nat) (j : Fin 25) (b : Option Bool) :
    Fin ((CanonicalLeaf.machine k).stateCount+25) × Option Bool × Move :=
  let go (i : Fin 25) (w : Option Bool) (d : Move) := (extra k i,w,d)
  let no := (embed k (CanonicalLeaf.machine k).reject,b,Move.stay)
  match j.val,b with
  | 0,some v => go 0 (some v) .left
  | 0,none => go 1 none .left
  | 1,some _ => go 1 (some false) .left
  | 1,none => go 2 none .right
  | 2,some v => go 2 (some v) .right
  | 2,none => go 3 none .right
  | 3,some v => go 3 (some v) .right
  | 3,none => go 4 none .right
  | 4,some v => go 4 (some v) .right
  | 4,none => go 5 none .stay
  | 5,none => go 6 none .right
  | 6,some true => go 6 (some true) .right
  | 6,b => go 7 b .left
  | 7,some true => go 8 (some false) .left
  | 7,none => go 22 none .left
  | 8,some v => go 8 (some v) .left
  | 8,none => go 9 none .left
  | 9,some v => go 9 (some v) .left
  | 9,none => go 10 none .left
  | 10,some v => go 10 (some v) .left
  | 10,none => go 11 none .left
  | 11,some v => go 11 (some v) .left
  | 11,none => go 12 none .right
  | 12,some true => go 12 (some true) .right
  | 12,some false => go 13 (some true) .left
  | 13,some v => go 13 (some v) .left
  | 13,none => go 2 none .right
  | 22,some v => go 22 (some v) .left
  | 22,none => go 23 none .stay
  | 23,none => liftAction k ((CanonicalLeaf.machine k).step (oldq k (430+93*k)) none)
  | 24,b => go 24 b .stay
  | _,_ => no
private def rows (k : Nat) (s : Fin ((CanonicalLeaf.machine k).stateCount+25)) (b : Option Bool) :=
  if h : s.val < (CanonicalLeaf.machine k).stateCount then
    let q : Fin (CanonicalLeaf.machine k).stateCount := ⟨s.val,h⟩
    if q=oldq k (430+93*k) ∧ b=none then (extra k 0,none,Move.left)
    else if q=oldq k (613+93*k) ∧ b=none then (extra k 24,none,Move.stay)
    else liftAction k ((CanonicalLeaf.machine k).step q b)
  else native k ⟨s.val-(CanonicalLeaf.machine k).stateCount,by omega⟩ b
private def extend (M : UniformTM)
    (step : Fin (M.stateCount+25) → Option Bool → Fin (M.stateCount+25) × Option Bool × Move) : UniformTM where
  stateCount := M.stateCount+25
  start := ⟨M.start.val,by omega⟩
  accept := ⟨M.accept.val,by omega⟩
  reject := ⟨M.reject.val,by omega⟩
  accept_ne_reject := by
    intro h
    apply M.accept_ne_reject
    apply Fin.ext
    exact congrArg (fun s : Fin (M.stateCount+25) => s.val) h
  rawStep := step
/-- Candidate literal carry/window family, extending the repaired canonical leaf. -/
def machine (k : Nat) : UniformTM := extend (CanonicalLeaf.machine k) (rows k)
/-- Whole-Config embedding, retaining the exact tape and head. -/
def config (k : Nat) {N B : Nat} (c : Config (CanonicalLeaf.machine k).stateCount N B) :
    Config (machine k).stateCount N B := ⟨embed k c.state,c.head,c.tape⟩
/-- Nonverdict endpoint before the destructive source selector. -/
def ready (k : Nat) : Fin (machine k).stateCount := extra k 24
#eval do
  for k in ([0,1,2,64] : List Nat) do
    let M:=machine k
    IO.println s!"meta|{k}|{M.stateCount}|{M.start.val}|{M.accept.val}|{M.reject.val}"
    let ids : List Nat := [138] ++ (List.range 184).map (fun i => 288+430+93*k+i) ++
      (List.range 25).map (fun i => (CanonicalLeaf.machine k).stateCount+i)
    for i in ids do
      let q : Fin M.stateCount:=⟨i%M.stateCount,Nat.mod_lt _ (Nat.zero_lt_of_lt M.start.isLt)⟩
      for b in [none,some false,some true] do
        let a:=M.step q b
        let s:Nat:=match b with | none => 0 | some false => 1 | some true => 2
        let w:Nat:=match a.2.1 with | none => 0 | some false => 1 | some true => 2
        let d:Int:=match a.2.2 with | .left => -1 | .stay => 0 | .right => 1
        IO.println s!"row|{k}|{q.val}|{s}|{a.1.val}|{w}|{d}"
end CarryWindow
