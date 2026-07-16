import PCoP.Machine

/-!
# P is closed under complement

The classical textbook argument (Sipser, Thm.-level exercise): given a
decider for `L`, *swap which halting states count as accepting*.  In this
model the swap is literal: the complement machine has the same states,
the same start state, the same transition table, and the negated halting
verdict table.

The two formal facts that make the argument go through — and which an
acceptance-by-distinguished-state, exact-clock model does *not* provide —
are isolated as lemmas:

* `stepConfig_complement` / `run_complement`: the run of the machine is
  completely unaffected by the verdict relabeling (the dynamics never
  consult the verdicts, only *whether* a state is halting, which the
  negation preserves);
* the complement machine halts at exactly the same time, so the *same*
  time bound `T` witnesses membership of the complement — the complement
  costs zero extra time.
-/

namespace PCoP

namespace TM

/-- The complement machine: identical dynamics, negated verdicts.
This is precisely "swap the accepting and rejecting halting states". -/
def complement (M : TM) : TM :=
  { M with halted := fun q => (M.halted q).map (fun b => !b) }

@[simp] theorem complement_k (M : TM) : M.complement.k = M.k := rfl

@[simp] theorem complement_q0 (M : TM) : M.complement.q0 = M.q0 := rfl

@[simp] theorem complement_step (M : TM) : M.complement.step = M.step := rfl

@[simp] theorem complement_halted (M : TM) (q : Fin M.k) :
    M.complement.halted q = (M.halted q).map (fun b => !b) := rfl

/-- The verdict relabeling does not affect a single step: the step
function only asks whether the current state is halting, and `Option.map`
preserves `none`-ness. -/
theorem stepConfig_complement (M : TM) (c : Config M.k) :
    M.complement.stepConfig c = M.stepConfig c := by
  unfold stepConfig
  cases h : M.halted c.q <;> simp [h]

/-- The verdict relabeling does not affect the run. -/
theorem run_complement (M : TM) (c : Config M.k) (t : Nat) :
    M.complement.run c t = M.run c t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [run_succ, run_succ, ih, stepConfig_complement]

/-- The output of the complement machine is the negated output of the
original machine, at every time. -/
theorem output_complement (M : TM) {n : Nat} (x : Bitstring n) (t : Nat) :
    M.complement.output x t = (M.output x t).map (fun b => !b) := by
  unfold output
  rw [show M.complement.initConfig x = M.initConfig x from rfl, run_complement]
  rfl

end TM

/-- If `M` decides `L` within `T`, then the complement machine decides
the complement language within the *same* time bound `T`. -/
theorem DecidesWithin.complement {M : TM} {T : Nat → Nat} {L : Language}
    (h : DecidesWithin M T L) :
    DecidesWithin M.complement T L.complement := by
  intro n x
  rw [TM.output_complement, h n x]
  rfl

/-- **Main theorem: P is closed under complement.** -/
theorem P_closed_under_complement (L : Language) (hL : P L) :
    P L.complement := by
  obtain ⟨M, T, hT, hM⟩ := hL
  exact ⟨M.complement, T, hT, hM.complement⟩

/-- **P = coP**, stated as an equivalence: a language is in `P` iff its
complement is. -/
theorem P_eq_coP (L : Language) : P L ↔ P L.complement := by
  constructor
  · exact P_closed_under_complement L
  · intro h
    have := P_closed_under_complement L.complement h
    rwa [Language.complement_complement] at this

end PCoP
