import PCoP.Complement

/-!
# Inhabitation witnesses: PARITY ∈ P (by an explicit machine)

A complexity class defined in a fresh model deserves evidence that it is
not degenerate.  This file provides two witnesses:

* `const_in_P`: the constant languages are in `P` (a one-state machine
  that halts immediately);
* `parity_in_P`: the parity language is in `P`, decided by an explicit
  4-state machine that scans the input left to right, maintains the
  running parity in its finite control, and halts with the verdict upon
  reading the first blank — with a proved time bound of `n + 1` steps.

The blank-delimited tape alphabet (`Sym = Option Bool`) is what makes
`parityTM` possible at all: the machine detects the end of the input by
reading a blank.  In a model whose blank coincides with the bit `0`,
no machine can even locate the end of its input.

Together with `P_closed_under_complement` this yields the (equally
explicit) corollary `parity_complement_in_P` — with the *same* `n + 1`
time bound.
-/

namespace PCoP

/-! ## The constant languages -/

/-- A one-state machine that is already halted with verdict `b`. -/
def constTM (b : Bool) : TM where
  k := 1
  q0 := ⟨0, Nat.zero_lt_one⟩
  halted := fun _ => some b
  step := fun q _ => (q, none, Move.stay)

theorem const_in_P (b : Bool) : P (fun _ _ => b) := by
  refine ⟨constTM b, fun _ => 0, ⟨0, fun n => ?_⟩, fun n x => rfl⟩
  simp

/-! ## The parity machine -/

/-- Running state carrying the parity accumulated so far:
`rs false = 0`, `rs true = 1`. -/
def rs (p : Bool) : Fin 4 :=
  if p then ⟨1, by omega⟩ else ⟨0, by omega⟩

/-- Halting state carrying the final verdict:
`hs false = 2`, `hs true = 3`. -/
def hs (v : Bool) : Fin 4 :=
  if v then ⟨3, by omega⟩ else ⟨2, by omega⟩

/-- Halting table: states `0, 1` are running; state `2` halts with
verdict `false`, state `3` halts with verdict `true`. -/
def parityHalted (q : Fin 4) : Option Bool :=
  if q.val < 2 then none else some (q.val == 3)

/-- Transition table.  In a running state with parity `p`:
reading a bit `b`, flip the parity accordingly and move right;
reading the blank (end of input), enter the halting state with
verdict `p`. -/
def parityStep (q : Fin 4) (s : Sym) : Fin 4 × Sym × Move :=
  let p : Bool := q.val == 1
  match s with
  | some b => (rs (Bool.xor p b), some b, Move.right)
  | none => (hs p, none, Move.stay)

/-- The 4-state parity machine. -/
def parityTM : TM where
  k := 4
  q0 := rs false
  halted := parityHalted
  step := parityStep

/-- Parity of the first `t` input bits (bits beyond the input length
count as `false`; the language below only uses `t = n`). -/
def parityAux {n : Nat} (x : Bitstring n) : Nat → Bool
  | 0 => false
  | t + 1 => Bool.xor (parityAux x t) (if h : t < n then x ⟨t, h⟩ else false)

/-- The parity language: `L n x = true` iff `x` has an odd number of
`true` bits. -/
def parityL : Language := fun n x => parityAux x n

/-! ### Table lemmas -/

@[simp] theorem parityHalted_rs (p : Bool) : parityHalted (rs p) = none := by
  cases p <;> rfl

@[simp] theorem parityHalted_hs (v : Bool) : parityHalted (hs v) = some v := by
  cases v <;> rfl

@[simp] theorem parityStep_some (p b : Bool) :
    parityStep (rs p) (some b) = (rs (Bool.xor p b), some b, Move.right) := by
  cases p <;> rfl

@[simp] theorem parityStep_none (p : Bool) :
    parityStep (rs p) none = (hs p, none, Move.stay) := by
  cases p <;> rfl

@[simp] theorem initTape_lt {n : Nat} (x : Bitstring n) {i : Nat} (h : i < n) :
    TM.initTape x i = some (x ⟨i, h⟩) := by
  simp [TM.initTape, h]

@[simp] theorem initTape_not_lt {n : Nat} (x : Bitstring n) {i : Nat} (h : ¬ i < n) :
    TM.initTape x i = none := by
  simp [TM.initTape, h]

/-! ### The run invariant -/

/-- After `t ≤ n` steps, the machine is in the running state carrying
the parity of the first `t` bits, its head is at cell `t`, and the tape
is unchanged. -/
theorem parity_run_invariant {n : Nat} (x : Bitstring n) :
    ∀ t, t ≤ n →
      parityTM.run (parityTM.initConfig x) t =
        { q := rs (parityAux x t), head := t, tape := TM.initTape x } := by
  intro t
  induction t with
  | zero =>
      intro _
      rfl
  | succ t ih =>
      intro h
      have htn : t < n := Nat.lt_of_succ_le h
      have ht : t ≤ n := Nat.le_of_lt htn
      have haux : parityAux x (t + 1) = Bool.xor (parityAux x t) (x ⟨t, htn⟩) := by
        show Bool.xor (parityAux x t) (if h : t < n then x ⟨t, h⟩ else false)
          = Bool.xor (parityAux x t) (x ⟨t, htn⟩)
        rw [dif_pos htn]
      have hstep : parityTM.step (rs (parityAux x t)) (TM.initTape x t)
          = (rs (Bool.xor (parityAux x t) (x ⟨t, htn⟩)), some (x ⟨t, htn⟩), Move.right) := by
        rw [initTape_lt x htn]
        exact parityStep_some (parityAux x t) (x ⟨t, htn⟩)
      rw [TM.run_succ, ih ht,
        parityTM.stepConfig_running
          { q := rs (parityAux x t), head := t, tape := TM.initTape x }
          (parityHalted_rs (parityAux x t))]
      show ({ q := (parityTM.step (rs (parityAux x t)) (TM.initTape x t)).1,
              head := moveHead t (parityTM.step (rs (parityAux x t)) (TM.initTape x t)).2.2,
              tape := writeTape (TM.initTape x) t
                (parityTM.step (rs (parityAux x t)) (TM.initTape x t)).2.1 } : Config 4)
          = { q := rs (parityAux x (t + 1)), head := t + 1, tape := TM.initTape x }
      rw [hstep]
      show ({ q := rs (Bool.xor (parityAux x t) (x ⟨t, htn⟩)), head := t + 1,
              tape := writeTape (TM.initTape x) t (some (x ⟨t, htn⟩)) } : Config 4)
          = { q := rs (parityAux x (t + 1)), head := t + 1, tape := TM.initTape x }
      rw [← haux, ← initTape_lt x htn, writeTape_self]

/-! ### PARITY ∈ P -/

/-- The parity language is in `P`, with the explicit time bound `n + 1`. -/
theorem parity_in_P : P parityL := by
  refine ⟨parityTM, fun n => n + 1, ⟨1, fun n => by simp⟩, ?_⟩
  intro n x
  unfold TM.output
  rw [TM.run_succ, parity_run_invariant x n (Nat.le_refl n),
    parityTM.stepConfig_running
      { q := rs (parityAux x n), head := n, tape := TM.initTape x }
      (parityHalted_rs (parityAux x n))]
  show parityTM.halted (parityTM.step (rs (parityAux x n)) (TM.initTape x n)).1
      = some (parityL n x)
  rw [initTape_not_lt x (Nat.lt_irrefl n)]
  show parityHalted (parityStep (rs (parityAux x n)) none).1 = some (parityL n x)
  rw [parityStep_none]
  exact parityHalted_hs (parityAux x n)

/-- The complement of parity is in `P` — with the same time bound, via
the complement machine. -/
theorem parity_complement_in_P : P parityL.complement :=
  P_closed_under_complement parityL parity_in_P

end PCoP
