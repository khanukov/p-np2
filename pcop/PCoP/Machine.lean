import PCoP.Basic

/-!
# The machine model and the class P

A deterministic single-tape Turing machine in the style of Sipser
(*Introduction to the Theory of Computation*, Def. 3.3), with three
deliberate design choices.  Each choice removes a known formalization
pitfall for "P is closed under complement"; see `pcop/README.md` for the
full discussion.

1. **Finite control is concrete.**  States are `Fin k` for an explicit
   `k : Nat`.  A machine is finite data: `k`, a start state, a halting
   table, and a transition table on `Fin k × Sym` (a finite domain).
   Finiteness of control is load-bearing: with an infinite state type a
   "machine" could smuggle arbitrary information through its state space
   and the class below would degenerate.

2. **Acceptance is a halting verdict, not a distinguished state.**
   `halted q = some b` means `q` is a halting state with output `b`
   (`b = true`: accepting halting state, `b = false`: rejecting halting
   state).  This is exactly Sipser's decider — the halting states are
   partitioned into accepting and rejecting — and it makes the classical
   complement construction ("swap which halting states accept") sound.
   Halting configurations are fixed points of the step function, so the
   verdict is stable in time (`output_mono`): *when* you sample the
   machine after it halts does not matter.

3. **The clock is part of the class, not of the machine.**  A machine
   has no `runTime` field.  The class `P` requires the existence of a
   polynomially bounded time bound `T` by which the machine has halted
   on every input.  The time bound therefore cannot act as a hidden
   advice channel.

The tape is one-way infinite (`Nat`-indexed); a `left` move at cell `0`
stays put (Sipser's convention, realized by truncated subtraction).  The
tape alphabet is `Option Bool`: `some b` is the bit `b`, `none` is the
blank, so the input is blank-delimited and the machine can detect where
the input ends.
-/

namespace PCoP

/-- Head movement. -/
inductive Move : Type
  | left
  | stay
  | right

/-- Tape symbol: `none` is the blank, `some b` is the bit `b`. -/
abbrev Sym : Type := Option Bool

/-- A deterministic single-tape Turing machine with finite control.

* `k` — number of control states (the states are `Fin k`);
* `q0` — the initial state;
* `halted q` — `some b` iff `q` is a halting state with verdict `b`
  (`true` = accept, `false` = reject); `none` iff `q` is a running state;
* `step q s` — for a running state `q` reading symbol `s`: the next
  state, the symbol to write, and the head move.  (On halting states the
  machine does not move; the value of `step` there is irrelevant because
  the semantics below never consults it.) -/
structure TM : Type where
  k : Nat
  q0 : Fin k
  halted : Fin k → Option Bool
  step : Fin k → Sym → Fin k × Sym × Move

/-- A configuration of a machine with `k` control states.

The type is parameterized by the *number of states* only, so machines
that share `k` (for example, a machine and its complement machine below)
share their configuration type on the nose. -/
structure Config (k : Nat) : Type where
  q : Fin k
  head : Nat
  tape : Nat → Sym

/-- Head movement on a one-way infinite tape; a `left` move at cell `0`
stays (truncated subtraction). -/
def moveHead (h : Nat) : Move → Nat
  | .left => h - 1
  | .stay => h
  | .right => h + 1

/-- Write symbol `s` at position `h`. -/
def writeTape (tape : Nat → Sym) (h : Nat) (s : Sym) : Nat → Sym :=
  fun i => if i = h then s else tape i

@[simp] theorem writeTape_self (tape : Nat → Sym) (h : Nat) :
    writeTape tape h (tape h) = tape := by
  funext i
  by_cases hi : i = h <;> simp [writeTape, hi]

namespace TM

/-- One step of the machine.  Halting configurations are fixed points. -/
def stepConfig (M : TM) (c : Config M.k) : Config M.k :=
  match M.halted c.q with
  | some _ => c
  | none =>
      let r := M.step c.q (c.tape c.head)
      { q := r.1, head := moveHead c.head r.2.2, tape := writeTape c.tape c.head r.2.1 }

/-- Run the machine for `t` steps. -/
def run (M : TM) (c : Config M.k) : Nat → Config M.k
  | 0 => c
  | t + 1 => M.stepConfig (M.run c t)

@[simp] theorem run_zero (M : TM) (c : Config M.k) : M.run c 0 = c := rfl

theorem run_succ (M : TM) (c : Config M.k) (t : Nat) :
    M.run c (t + 1) = M.stepConfig (M.run c t) := rfl

/-- A halting configuration is a fixed point of the step function. -/
theorem stepConfig_of_halted (M : TM) {c : Config M.k} {b : Bool}
    (h : M.halted c.q = some b) : M.stepConfig c = c := by
  unfold stepConfig
  rw [h]

/-- In a running state, one step applies the transition table. -/
theorem stepConfig_running (M : TM) (c : Config M.k)
    (h : M.halted c.q = none) :
    M.stepConfig c =
      { q := (M.step c.q (c.tape c.head)).1,
        head := moveHead c.head (M.step c.q (c.tape c.head)).2.2,
        tape := writeTape c.tape c.head (M.step c.q (c.tape c.head)).2.1 } := by
  unfold stepConfig
  rw [h]

/-- Once halted, the configuration never changes again. -/
theorem run_of_halted (M : TM) {c : Config M.k} {b : Bool} (t : Nat)
    (h : M.halted (M.run c t).q = some b) (s : Nat) :
    M.run c (t + s) = M.run c t := by
  induction s with
  | zero => rfl
  | succ s ih =>
      have : M.run c (t + (s + 1)) = M.stepConfig (M.run c (t + s)) := rfl
      rw [this, ih, M.stepConfig_of_halted h]

/-- The blank-delimited initial tape: cells `0..n-1` carry the input
bits, every other cell is blank. -/
def initTape {n : Nat} (x : Bitstring n) : Nat → Sym :=
  fun i => if h : i < n then some (x ⟨i, h⟩) else none

/-- The initial configuration on input `x`. -/
def initConfig (M : TM) {n : Nat} (x : Bitstring n) : Config M.k :=
  { q := M.q0, head := 0, tape := initTape x }

/-- The observable output after `t` steps: the halting verdict of the
current state (`none` = still running). -/
def output (M : TM) {n : Nat} (x : Bitstring n) (t : Nat) : Option Bool :=
  M.halted (M.run (M.initConfig x) t).q

/-- **Robustness of the clock semantics.**  The output is monotone in
time: once the machine has halted with verdict `b`, it reports `b` at
every later time as well.  Consequently the exact sampling moment is
irrelevant — any time bound at which the machine has halted yields the
same verdict.  (This is the model-design property whose absence makes
exact-clock acceptance semantics so hostile to the complement proof.) -/
theorem output_mono (M : TM) {n : Nat} (x : Bitstring n) {t t' : Nat}
    (htt' : t ≤ t') {b : Bool} (hb : M.output x t = some b) :
    M.output x t' = some b := by
  rcases Nat.exists_eq_add_of_le htt' with ⟨s, rfl⟩
  unfold output at hb ⊢
  rw [M.run_of_halted t hb s]
  exact hb

end TM

/-- `M` decides `L` within time bound `T`: on every input of length `n`,
after `T n` steps the machine has halted and its verdict is `L n x`. -/
def DecidesWithin (M : TM) (T : Nat → Nat) (L : Language) : Prop :=
  ∀ (n : Nat) (x : Bitstring n), M.output x (T n) = some (L n x)

/-- A time bound is polynomially bounded: `T n ≤ n ^ c + c` for some `c`. -/
def PolyBounded (T : Nat → Nat) : Prop :=
  ∃ c : Nat, ∀ n : Nat, T n ≤ n ^ c + c

/-- **The class P**: languages decided by some Turing machine within some
polynomially bounded time bound. -/
def P (L : Language) : Prop :=
  ∃ (M : TM) (T : Nat → Nat), PolyBounded T ∧ DecidesWithin M T L

/-- Deciding within a time bound is monotone in the bound (a direct
consequence of `output_mono`): enlarging the clock never changes the
verdict. -/
theorem DecidesWithin.mono {M : TM} {T T' : Nat → Nat} {L : Language}
    (h : DecidesWithin M T L) (hT : ∀ n, T n ≤ T' n) :
    DecidesWithin M T' L :=
  fun n x => M.output_mono x (hT n) (h n x)

end PCoP
