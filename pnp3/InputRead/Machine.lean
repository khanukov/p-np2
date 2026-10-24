import Body.Raw

/-! Infrastructure. Physical streaming cursor, installed BEFORE the first increment.
The current source bit is lifted into one of three finite modes: false, true, EOF.
EOF is sticky virtual false; the zero register is never read as serialized data.
This is a connected table-cursor stage, not a serialized input-node evaluator. -/
namespace InputRead
open Pnp3.Complexity.Uniform.V1

def q (i : Nat) : Fin 41 := ⟨i % 41, Nat.mod_lt _ (by decide)⟩
def ready (mode : Fin 3) : Fin 41 := q (8+8*mode.val+3)
def result (mode : Fin 3) : Bool := mode.val == 1

def rows (s : Fin 41) (b : Option Bool) : Fin 41 × Option Bool × Move :=
  match s.val, b with
  | 0, none => (q 1, none, .right)
  | 1, some true => (q 1, some false, .right)
  | 1, none => (q 2, none, .stay)
  | 2, none => (q 3, none, .left)
  | 3, some b => (q 3, some b, .left)
  | 3, none => (q 4, none, .left)
  | 4, some false => (q 4, some false, .left)
  | 4, none => (q 5, none, .left)
  | 5, some b => (q 5, some b, .left)
  | 5, none => (q 6, none, .right)
  | 6, some true => (q 7, some true, .right)
  | 7, some false => (q 8, none, .right)
  | 7, some true => (q 16, none, .right)
  | 7, none => (q 25, none, .right)
  | 32, some b => (q 32, some b, .left)
  | 33, some b => (q 33, some b, .left)
  | 32, none => (q 7, some false, .right)
  | 33, none => (q 7, some true, .right)
  | 35, some false => (q 35, some false, .left)
  | 36, some false => (q 36, some false, .left)
  | 35, none => (q 37, none, .left)
  | 36, none => (q 38, none, .left)
  | 37, some b => (q 37, some b, .left)
  | 38, some b => (q 38, some b, .left)
  | 37, none => (q 39, some false, .stay)
  | 38, none => (q 39, some true, .stay)
  | i, b =>
    if 8 ≤ i ∧ i < 32 then
      let mode := (i-8)/8
      let base := 8+8*mode
      match (i-8)%8, b with
      | 0, some b => (q base, some b, .right)
      | 0, none => (q (base+1), none, .right)
      | 1, some false => (q (base+1), some false, .right)
      | 1, none => (q (base+2), none, .right)
      | 2, some b => (q (base+2), some b, .right)
      | 2, none => (q (base+3), none, .stay)
      | 3, none => (q (base+4), none, .left)
      | 4, some true => (q (base+4), some false, .left)
      | 4, some false => (q (base+5), some true, .right)
      | 4, none => (q (if mode < 2 then 35+mode else 39), none, .left)
      | 5, some b => (q (base+5), some b, .right)
      | 5, none => (q (if mode < 2 then base+6 else base+3), none,
          if mode < 2 then .left else .stay)
      | 6, some b => (q (base+6), some b, .left)
      | 6, none => (q (base+7), none, .left)
      | 7, some false => (q (base+7), some false, .left)
      | 7, none => (q (32+mode), none, .left)
      | _, b => (q 40, b, .stay)
    else (q 40, b, .stay)

def machine : UniformTM where
  stateCount := 41
  start := q 0
  accept := q 39
  reject := q 40
  accept_ne_reject := by decide
  rawStep := rows

def rawMachine : UniformTM := FixedRawLengthFence.prefixed.seq machine

/-- Proof-side exact clock, never consulted by a row. -/
def readClock (n z suffix : Nat) : Nat := 2*n+2*z+2*suffix+11

end InputRead
