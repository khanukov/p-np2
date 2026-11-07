import InputRead.Raw
namespace Stream
open Pnp3.Complexity.Uniform.V1

def q (i : Nat) : Fin 64 := ⟨i % 64, Nat.mod_lt _ (by decide)⟩
def unpaid (mode : Fin 3) : Fin 64 := q (11+8*mode.val)
def paid (mode : Fin 3) : Fin 64 := q (43+4*mode.val)
def rows (s : Fin 64) (b : Option Bool) : Fin 64 × Option Bool × Move :=
  match s.val,b with
  | 11,none => (q 41,none,.right)
  | 19,none => (q 45,none,.right)
  | 27,none => (q 49,none,.right)
  | 37,none => (q 56,some false,.right)
  | 38,none => (q 56,some true,.right)
  | 28,none => (q 54,none,.left)
  | 54,some false => (q 54,some false,.left)
  | 54,none => (q 57,none,.stay)
  | 56,some b => (q 58,some b,.stay)
  | 56,none => (q 57,none,.stay)
  | 57,b => (q 57,b,.stay)
  | 58,b => (q 58,b,.stay)
  | i,b =>
    if 41 ≤ i ∧ i < 53 then
      let mode := (i-41)/4
      let base := 41+4*mode
      match (i-41)%4,b with
      | 0,some true => (q base,some true,.right)
      | 0,none => (q (base+1),some true,.left)
      | 1,some true => (q (base+1),some true,.left)
      | 1,none => (q (base+2),none,.stay)
      | 2,none => (q (12+8*mode),none,.left)
      | _,b => (q 40,b,.stay)
    else
      let a := InputRead.rows (InputRead.q i) b
      (q a.1.val,a.2)

/-- Work exits 57/58 are inert field ingress states, never content acceptance. -/
def machine : UniformTM where
  stateCount := 64
  start := q 0
  accept := q 39
  reject := q 40
  accept_ne_reject := by decide
  rawStep := rows
def rawMachine : UniformTM := FixedRawLengthFence.prefixed.seq machine
end Stream
