import Complexity.Uniform.V1.FixedRawLengthFenceCountdown

/-! Infrastructure. Symbol driven unary installation and repeated binary increment.
The work accept means counter overflow, never a content verdict. -/
namespace Body
open Pnp3.Complexity.Uniform.V1

def q (i : Nat) : Fin 9 := ⟨i % 9, Nat.mod_lt _ (by decide)⟩
/-- Start at the blank preceding actual unary marks. Ready is the right blank.
Seed rejects a false fence instead of consuming it. Carry uses the left blank;
return finds the right blank. Width and value occur in no transition. -/
def raw (s : Fin 9) (b : Option Bool) : Fin 9 × Option Bool × Move :=
  match s.val, b with
  | 0, none => (q 1, none, .right)
  | 1, some true => (q 1, some false, .right)
  | 1, none => (q 2, none, .stay)
  | 2, none => (q 3, none, .left)
  | 3, some true => (q 3, some false, .left)
  | 3, some false => (q 4, some true, .right)
  | 3, none => (q 7, none, .right)
  | 4, some b => (q 4, some b, .right)
  | 4, none => (q 2, none, .stay)
  | _, b => (q 8, b, .stay)

def machine : UniformTM where
  stateCount := 9
  start := q 0
  accept := q 7
  reject := q 8
  accept_ne_reject := by decide
  rawStep := raw

/-- Fixed raw-origin table. Both component accept states are work handoffs. -/
def rawMachine : UniformTM := FixedRawLengthFence.prefixed.seq machine

/-- Little endian list, physically stored with its least significant bit at the right.
Leading false digits are retained, including after the increment. -/
def inc : List Bool → List Bool × Bool
  | [] => ([], true)
  | false :: bs => (true :: bs, false)
  | true :: bs => let r := inc bs; (false :: r.1, r.2)

def value : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * value bs

/-- Exact variable cost of one physical increment from Ready through return.
The overflow route exits at the left blank; it does not silently reenter. -/
def carryClock : List Bool → Nat → Nat
  | [], _ => 1
  | false :: _, r => r + 2
  | true :: bs, r => 1 + carryClock bs (r+1)

def roundClock (bs : List Bool) : Nat := 1 + carryClock bs 0
end Body
