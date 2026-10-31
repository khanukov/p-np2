import Complexity.Uniform.V1.FixedPairParserAmbient

/-!
# Generic bounded budget transport for `UniformTM`

This module compares executions of one fixed `UniformTM` on the same input
and for the same number of transitions, but with two different tape-budget
indices.  It reuses the dependent `Fin` embedding and guarded blank-extension
simulation from `FixedPairParserAmbient`; none of the results below assumes
anything about the fixed pair parser.

The essential boundary fact is deliberately explicit.  Starting at head
zero, after `r` transitions the head value is at most `r`.  Thus, at every
pre-step time `r < s` of a run with `s ≤ C`, the smaller allocation has strict
right room.  The final configuration may reach its last cell when `N = 0`
and `s = C`; no further simulated transition is requested there.
-/

namespace Pnp3.Complexity.Uniform.V1

/-- A head move changes the numeric address by at most one to the right. -/
private theorem moveHead_val_le_succ {length : Nat}
    (head : Fin length) (move : Move) :
    (moveHead head move).val ≤ head.val + 1 := by
  cases move with
  | left =>
      simp only [moveHead]
      omega
  | stay =>
      simp [moveHead]
  | right =>
      simp only [moveHead]
      split
      · rfl
      · omega

/-- One transition increases the numeric head address by at most one. -/
theorem UniformTM.stepConfig_head_le_succ (M : UniformTM)
    {N budget : Nat} (c : Config M.stateCount N budget) :
    (M.stepConfig c).head.val ≤ c.head.val + 1 := by
  change
    (moveHead c.head
      (M.step c.state (c.tape c.head)).2.2).val ≤ c.head.val + 1
  exact moveHead_val_le_succ c.head _

/-- Machine-independent head-speed bound from an arbitrary configuration. -/
theorem UniformTM.run_head_le (M : UniformTM)
    {N budget steps : Nat} (c : Config M.stateCount N budget) :
    (M.run steps c).head.val ≤ c.head.val + steps := by
  induction steps with
  | zero =>
      simp [UniformTM.run]
  | succ steps ih =>
      change
        (M.stepConfig (M.run steps c)).head.val ≤
          c.head.val + (steps + 1)
      calc
        (M.stepConfig (M.run steps c)).head.val ≤
            (M.run steps c).head.val + 1 :=
          M.stepConfig_head_le_succ _
        _ ≤ (c.head.val + steps) + 1 := Nat.add_le_add_right ih 1
        _ = c.head.val + (steps + 1) := by omega

/-- From the canonical initial head zero, the head value is at most the
elapsed number of transitions. -/
theorem UniformTM.run_initialConfig_head_le (M : UniformTM)
    {N budget steps : Nat} (y : Bitstring N) :
    (M.run steps (initialConfig M budget y)).head.val ≤ steps := by
  simpa [initialConfig] using
    (M.run_head_le (steps := steps) (c := initialConfig M budget y))

/-- Every configuration used as a pre-step of a run of length `s ≤ C` has
strict room for a right move in the smaller `N + C + 1` allocation. -/
theorem UniformTM.run_initialConfig_right_room (M : UniformTM)
    {N C s : Nat} (y : Bitstring N) (hs : s ≤ C) :
    ∀ r, r < s →
      (M.run r (initialConfig M C y)).head.val + 1 < tapeLength N C := by
  intro r hrs
  have hhead :=
    M.run_initialConfig_head_le (budget := C) (steps := r) y
  simp only [tapeLength]
  omega

/-- A bounded run from canonical initial configurations is a genuine
blank-extension simulation across budgets.  The two configurations retain
their separate dependent budget indices; no cast is used. -/
theorem UniformTM.run_initialConfig_extension (M : UniformTM)
    {N C B s : Nat} (y : Bitstring N) (hs : s ≤ C) (hCB : C ≤ B) :
    FixedPairParser.ConfigExtension hCB
      (M.run s (initialConfig M C y))
      (M.run s (initialConfig M B y)) := by
  exact FixedPairParser.run_extension M hCB
    (FixedPairParser.initialConfig_extension M hCB y) s
    (M.run_initialConfig_right_room y hs)

/-- In particular, bounded executions have literally equal finite controls
across the two budget indices. -/
theorem UniformTM.run_initialConfig_state_eq (M : UniformTM)
    {N C B s : Nat} (y : Bitstring N) (hs : s ≤ C) (hCB : C ≤ B) :
    (M.run s (initialConfig M C y)).state =
      (M.run s (initialConfig M B y)).state :=
  (M.run_initialConfig_extension y hs hCB).1

/-- Exact-time acceptance is invariant under a sufficient budget increase. -/
theorem UniformTM.acceptsAt_budget_iff (M : UniformTM)
    {N C B s : Nat} (y : Bitstring N) (hs : s ≤ C) (hCB : C ≤ B) :
    AcceptsAt M C s y ↔ AcceptsAt M B s y := by
  unfold AcceptsAt
  rw [M.run_initialConfig_state_eq y hs hCB]

/-- Forward exact-time acceptance transport. -/
theorem UniformTM.acceptsAt_budget_mono (M : UniformTM)
    {N C B s : Nat} (y : Bitstring N) (hs : s ≤ C) (hCB : C ≤ B) :
    AcceptsAt M C s y → AcceptsAt M B s y :=
  (M.acceptsAt_budget_iff y hs hCB).1

/-- Exact-time literal rejection is invariant under a sufficient budget
increase. -/
theorem UniformTM.rejectsAt_budget_iff (M : UniformTM)
    {N C B s : Nat} (y : Bitstring N) (hs : s ≤ C) (hCB : C ≤ B) :
    RejectsAt M C s y ↔ RejectsAt M B s y := by
  unfold RejectsAt
  rw [M.run_initialConfig_state_eq y hs hCB]

/-- Forward exact-time literal-rejection transport. -/
theorem UniformTM.rejectsAt_budget_mono (M : UniformTM)
    {N C B s : Nat} (y : Bitstring N) (hs : s ≤ C) (hCB : C ≤ B) :
    RejectsAt M C s y → RejectsAt M B s y :=
  (M.rejectsAt_budget_iff y hs hCB).1

/-- Exact-time Boolean decision is invariant under a sufficient budget
increase.  The false branch remains literal rejection. -/
theorem UniformTM.decidesAt_budget_iff (M : UniformTM)
    {N C B s : Nat} (y : Bitstring N) (answer : Bool)
    (hs : s ≤ C) (hCB : C ≤ B) :
    DecidesAt M C s y answer ↔ DecidesAt M B s y answer := by
  cases answer with
  | false =>
      simpa [DecidesAt] using (M.rejectsAt_budget_iff y hs hCB)
  | true =>
      simpa [DecidesAt] using (M.acceptsAt_budget_iff y hs hCB)

/-- Required composition handoff: exact decision transports from a small
budget to any larger ambient budget when the elapsed run fits in the small
budget. -/
theorem UniformTM.decidesAt_budget_mono
    (M : UniformTM) {N C B s : Nat} (y : Bitstring N) (answer : Bool)
    (hs : s ≤ C) (hCB : C ≤ B) :
    DecidesAt M C s y answer → DecidesAt M B s y answer :=
  (M.decidesAt_budget_iff y answer hs hCB).1

/-- A small-budget within-time acceptance witness remains a valid witness in
the larger budget. -/
theorem UniformTM.acceptsWithin_budget_mono (M : UniformTM)
    {N C B : Nat} (y : Bitstring N) (hCB : C ≤ B) :
    AcceptsWithin M C y → AcceptsWithin M B y := by
  rintro ⟨s, hs, haccept⟩
  exact ⟨s, Nat.le_trans hs hCB,
    M.acceptsAt_budget_mono y hs hCB haccept⟩

/-- A small-budget within-time literal-rejection witness remains a valid
witness in the larger budget. -/
theorem UniformTM.rejectsWithin_budget_mono (M : UniformTM)
    {N C B : Nat} (y : Bitstring N) (hCB : C ≤ B) :
    RejectsWithin M C y → RejectsWithin M B y := by
  rintro ⟨s, hs, hreject⟩
  exact ⟨s, Nat.le_trans hs hCB,
    M.rejectsAt_budget_mono y hs hCB hreject⟩

/-- `DecidesWithin` is monotone because its existing witness time is at most
`C`, so exact-time budget transport applies and that same time is at most
`B`. -/
theorem UniformTM.decidesWithin_budget_mono (M : UniformTM)
    {N C B : Nat} (y : Bitstring N) (answer : Bool) (hCB : C ≤ B) :
    DecidesWithin M C y answer → DecidesWithin M B y answer := by
  cases answer with
  | false =>
      change RejectsWithin M C y → RejectsWithin M B y
      exact M.rejectsWithin_budget_mono y hCB
  | true =>
      change AcceptsWithin M C y → AcceptsWithin M B y
      exact M.acceptsWithin_budget_mono y hCB

end Pnp3.Complexity.Uniform.V1
