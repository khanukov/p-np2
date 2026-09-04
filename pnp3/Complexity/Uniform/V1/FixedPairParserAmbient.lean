import Complexity.Uniform.V1.FixedPairParserCorrectness

/-!
# Ambient-budget execution of the fixed pair parser

This module compares the already-proved exact-clock execution with execution
of the same fixed machine on a larger, dependently indexed tape.  In
particular, it never casts a `Config` between budgets.  Instead it embeds tape
indices by preserving their natural-number values and relates two separately
typed configurations pointwise.
-/

namespace Pnp3.Complexity.Uniform.V1.FixedPairParser

open PairEncoding

/-! ## Explicit maps between the two tape domains -/

/-- Increasing the budget weakly increases the allocated tape length. -/
private theorem tapeLength_mono_budget {N C B : Nat} (hCB : C ≤ B) :
    tapeLength N C ≤ tapeLength N B := by
  unfold tapeLength
  omega

/-- The canonical inclusion of a smaller-budget tape into a larger-budget
tape.  It preserves the underlying natural-number address. -/
def tapeEmbed {N C B : Nat} (hCB : C ≤ B) :
    Fin (tapeLength N C) → Fin (tapeLength N B) :=
  fun i => ⟨i.val, lt_of_lt_of_le i.isLt (tapeLength_mono_budget hCB)⟩

@[simp] theorem tapeEmbed_val {N C B : Nat} (hCB : C ≤ B)
    (i : Fin (tapeLength N C)) :
    (tapeEmbed hCB i).val = i.val :=
  rfl

theorem tapeEmbed_injective {N C B : Nat} (hCB : C ≤ B) :
    Function.Injective (tapeEmbed hCB :
      Fin (tapeLength N C) → Fin (tapeLength N B)) := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg
    (fun x : Fin (tapeLength N B) => x.val) hij
  exact hval

/-- Partial projection from a larger allocation.  Addresses outside the
smaller allocation have no projection. -/
def tapeProject {N C B : Nat} (_hCB : C ≤ B)
    (j : Fin (tapeLength N B)) : Option (Fin (tapeLength N C)) :=
  if hj : j.val < tapeLength N C then some ⟨j.val, hj⟩ else none

@[simp] theorem tapeProject_tapeEmbed {N C B : Nat} (hCB : C ≤ B)
    (i : Fin (tapeLength N C)) :
    tapeProject hCB (tapeEmbed hCB i) = some i := by
  simp [tapeProject]

theorem tapeProject_eq_none_iff {N C B : Nat} (hCB : C ≤ B)
    (j : Fin (tapeLength N B)) :
    tapeProject hCB j = none ↔ tapeLength N C ≤ j.val := by
  unfold tapeProject
  split <;> simp_all

theorem tapeEmbed_tapeProject_of_eq_some {N C B : Nat} (hCB : C ≤ B)
    (j : Fin (tapeLength N B)) (i : Fin (tapeLength N C))
    (hproject : tapeProject hCB j = some i) :
    tapeEmbed hCB i = j := by
  unfold tapeProject at hproject
  split at hproject
  · simp only [Option.some.injEq] at hproject
    apply Fin.ext
    simpa [tapeEmbed] using congrArg Fin.val hproject.symm
  · simp at hproject

/-! ## A cross-budget configuration relation -/

/-- `large` is the blank extension of `small`.  Equality of heads is stated
through `tapeEmbed`; equality of tapes is only asked at embedded addresses;
the genuinely new addresses are required to be blank. -/
def ConfigExtension {k N C B : Nat} (hCB : C ≤ B)
    (small : Config k N C) (large : Config k N B) : Prop :=
  small.state = large.state ∧
  large.head = tapeEmbed hCB small.head ∧
  (∀ i : Fin (tapeLength N C),
    large.tape (tapeEmbed hCB i) = small.tape i) ∧
  (∀ j : Fin (tapeLength N B),
    tapeLength N C ≤ j.val → large.tape j = none)

/-- Initial input cells and blank padding agree across allocations. -/
theorem initialConfig_extension (M : UniformTM) {N C B : Nat}
    (hCB : C ≤ B) (y : Bitstring N) :
    ConfigExtension hCB
      (initialConfig M C y) (initialConfig M B y) := by
  constructor
  · rfl
  constructor
  · apply Fin.ext
    rfl
  constructor
  · intro i
    simp [initialConfig, tapeEmbed]
  · intro j hj
    have hnot : ¬ j.val < N := by
      unfold tapeLength at hj
      omega
    simp [initialConfig, hnot]

/-- Literal initial tape behavior in the ambient domain.  This distinguishes
an input zero, `some false`, from the blank symbol `none`. -/
theorem ambient_initial_tape_behavior {N B : Nat} (y : Bitstring N) :
    (∀ i : Fin N,
      (initialConfig machine B y).tape
        ⟨i.val, Nat.lt_of_lt_of_le i.isLt
          (Nat.le_add_right N (B + 1))⟩ = some (y i)) ∧
    (∀ j : Fin (tapeLength N B), N ≤ j.val →
      (initialConfig machine B y).tape j = none) := by
  constructor
  · intro i
    exact initialConfig_tape_input machine y i
  · intro j hj
    exact initialConfig_tape_padding machine y j hj

/-! ## One-step and run simulation -/

/-- Head movement commutes with allocation inclusion whenever a right move
would not hit the smaller allocation's boundary. -/
theorem moveHead_tapeEmbed {N C B : Nat} (hCB : C ≤ B)
    (i : Fin (tapeLength N C)) (move : Move)
    (hroom : i.val + 1 < tapeLength N C) :
    moveHead (tapeEmbed hCB i) move =
      tapeEmbed hCB (moveHead i move) := by
  have hlarge : i.val + 1 < tapeLength N B :=
    lt_of_lt_of_le hroom (tapeLength_mono_budget hCB)
  cases move with
  | left =>
      apply Fin.ext
      rfl
  | stay =>
      apply Fin.ext
      rfl
  | right =>
      apply Fin.ext
      simp [moveHead, hroom, hlarge]

/-- One public machine step preserves the cross-budget relation.  The only
boundary premise is on the smaller head; no equality between dependent
`Config` types is asserted or used. -/
theorem stepConfig_extension (M : UniformTM) {N C B : Nat}
    (hCB : C ≤ B)
    {small : Config M.stateCount N C}
    {large : Config M.stateCount N B}
    (hrel : ConfigExtension hCB small large)
    (hroom : small.head.val + 1 < tapeLength N C) :
    ConfigExtension hCB (M.stepConfig small) (M.stepConfig large) := by
  rcases hrel with ⟨hstate, hhead, hlow, hextra⟩
  have hscan : large.tape large.head = small.tape small.head := by
    rw [hhead]
    exact hlow small.head
  have haction :
      M.step large.state (large.tape large.head) =
        M.step small.state (small.tape small.head) := by
    rw [← hstate, hscan]
  constructor
  · change
      (M.step small.state (small.tape small.head)).1 =
        (M.step large.state (large.tape large.head)).1
    exact congrArg Prod.fst haction.symm
  constructor
  · change
      moveHead large.head
          (M.step large.state (large.tape large.head)).2.2 =
        tapeEmbed hCB
          (moveHead small.head
            (M.step small.state (small.tape small.head)).2.2)
    rw [haction, hhead]
    exact moveHead_tapeEmbed hCB small.head _ hroom
  constructor
  · intro i
    change
      (if tapeEmbed hCB i = large.head then
          (M.step large.state (large.tape large.head)).2.1
        else large.tape (tapeEmbed hCB i)) =
      (if i = small.head then
          (M.step small.state (small.tape small.head)).2.1
        else small.tape i)
    rw [haction]
    by_cases hi : i = small.head
    · subst i
      rw [if_pos hhead.symm, if_pos rfl]
    · have hne : tapeEmbed hCB i ≠ large.head := by
        intro heq
        apply hi
        apply tapeEmbed_injective hCB
        exact heq.trans hhead
      rw [if_neg hne, if_neg hi]
      exact hlow i
  · intro j hj
    have hjne : j ≠ large.head := by
      intro heq
      have hval : j.val = small.head.val := by
        calc
          j.val = large.head.val := congrArg Fin.val heq
          _ = (tapeEmbed hCB small.head).val := congrArg Fin.val hhead
          _ = small.head.val := rfl
      exact (Nat.not_lt_of_ge hj) (hval.trans_lt small.head.isLt)
    change
      (if j = large.head then
          (M.step large.state (large.tape large.head)).2.1
        else large.tape j) = none
    rw [if_neg hjne]
    exact hextra j hj

/-- Iterated version of `stepConfig_extension`. -/
theorem run_extension (M : UniformTM) {N C B : Nat}
    (hCB : C ≤ B)
    {small₀ : Config M.stateCount N C}
    {large₀ : Config M.stateCount N B}
    (h₀ : ConfigExtension hCB small₀ large₀)
    (steps : Nat)
    (hroom : ∀ s, s < steps →
      (M.run s small₀).head.val + 1 < tapeLength N C) :
    ConfigExtension hCB (M.run steps small₀) (M.run steps large₀) := by
  induction steps with
  | zero =>
      simpa [UniformTM.run] using h₀
  | succ steps ih =>
      have hprev : ConfigExtension hCB
          (M.run steps small₀) (M.run steps large₀) :=
        ih (fun s hs => hroom s (Nat.lt_trans hs (Nat.lt_succ_self steps)))
      have hstep := stepConfig_extension M hCB hprev
        (hroom steps (Nat.lt_succ_self steps))
      simpa only [UniformTM.run] using hstep

/-! ## The parser never approaches either allocation boundary -/

/-- Before its first terminal time, the exact-budget parser head is always in
the input segment `0..N`. -/
private theorem exact_head_le_input_before_clock {N : Nat} (y : Bitstring N)
    (steps : Nat) (hsteps : steps < clock N) :
    (machine.run steps (exactInitial y)).head.val ≤ N := by
  cases N with
  | zero =>
      have hs : steps = 0 := by
        simp [clock] at hsteps
        omega
      subst steps
      rfl
  | succ N =>
      by_cases hs0 : steps = 0
      · subst steps
        change 0 ≤ N + 1
        exact Nat.zero_le _
      · by_cases hforward : steps ≤ N + 1
        · obtain ⟨r, hr⟩ : ∃ r, steps = r + 1 :=
            ⟨steps - 1, by omega⟩
          subst steps
          have hInv := run_forward y r hforward
          rw [hInv.2.1]
          omega
        · let j := steps - (N + 1 + 1)
          have hj : j < N + 1 := by
            dsimp [j]
            simp [clock] at hsteps
            omega
          have htime : steps = (N + 1) + 1 + j := by
            dsimp [j]
            omega
          rw [htime]
          have hInv := run_back y (by omega) j hj
          rw [hInv.2.1]
          omega

/-- The head bound including the literal deadline. -/
theorem exact_head_le_input_through_clock {N : Nat} (y : Bitstring N)
    (steps : Nat) (hsteps : steps ≤ clock N) :
    (machine.run steps (exactInitial y)).head.val ≤ N := by
  by_cases hlt : steps < clock N
  · exact exact_head_le_input_before_clock y steps hlt
  · have heq : steps = clock N := by omega
    subst steps
    have hzero := head_zero_at_clock y
    change (machine.run (clock N) (exactInitial y)).head.val = 0 at hzero
    omega

/-- The exact parser has genuine room for a right move at every configuration
through its clock.  This is stronger than the strict pre-clock fact needed by
`run_extension`; it makes the boundary premise available to later
composition without dependent transport or unchecked monotonicity. -/
theorem exact_head_right_room_through_clock {N : Nat} (y : Bitstring N)
    (steps : Nat) (hsteps : steps ≤ clock N) :
    (machine.run steps (exactInitial y)).head.val + 1 <
      tapeLength N (clock N) := by
  have hhead := exact_head_le_input_through_clock y steps hsteps
  unfold tapeLength clock
  omega

/-- Every exact-allocation cell outside the raw input remains blank throughout
the complete parser trace. -/
private theorem exact_padding_blank_through_clock {N : Nat} (y : Bitstring N)
    (steps : Nat) (hsteps : steps ≤ clock N)
    (i : Fin (tapeLength N (clock N))) (hi : N ≤ i.val) :
    (machine.run steps (exactInitial y)).tape i = none := by
  by_cases hs0 : steps = 0
  · subst steps
    exact initialConfig_tape_padding machine y i hi
  · by_cases hforward : steps ≤ N
    · obtain ⟨r, hr⟩ : ∃ r, steps = r + 1 :=
          ⟨steps - 1, by omega⟩
      subst steps
      have hInv := run_forward y r hforward
      rw [hInv.2.2]
      simp [erasedZeroTape, exactInitial, initialConfig,
        Nat.not_lt_of_ge hi]
    · by_cases hfinal : steps = clock N
      · subst steps
        change
          (machine.run (clock N)
            (initialConfig machine (clock N) y)).tape i = none
        rw [tape_restored_at_clock y]
        exact initialConfig_tape_padding machine y i hi
      · have hN : 0 < N := by
          simp [clock] at hsteps hforward hfinal
          omega
        have hlt : steps < clock N := by
          omega
        have hbase : N + 1 ≤ steps := by
          omega
        let j := steps - (N + 1)
        have hj : j < N := by
          dsimp [j]
          unfold clock at hlt
          omega
        have htime : N + 1 + j = steps := by
          dsimp [j]
          exact Nat.add_sub_of_le hbase
        rw [← htime]
        have hInv := run_back y hN j hj
        rw [hInv.2.2]
        simp [erasedZeroTape, exactInitial, initialConfig,
          Nat.not_lt_of_ge hi]

/-! ## Ambient trace, final configuration, and semantics -/

/-- At every time through the deadline, ambient execution is the blank tape
extension of exact-budget execution.  This is the principal trace theorem. -/
theorem ambient_run_extension {N B : Nat} (y : Bitstring N)
    (hB : clock N ≤ B) (steps : Nat) (hsteps : steps ≤ clock N) :
    ConfigExtension hB
      (machine.run steps (initialConfig machine (clock N) y))
      (machine.run steps (initialConfig machine B y)) := by
  apply run_extension machine hB (initialConfig_extension machine hB y)
  intro s hs
  exact exact_head_right_room_through_clock y s
    (Nat.le_trans (Nat.le_of_lt hs) hsteps)


/-- Every genuinely new ambient address stays blank throughout the parser
trace.  This is the fourth field of `ConfigExtension`, exposed directly for
later machines that reserve the ambient suffix. -/
theorem ambient_extra_cells_blank_through_clock {N B : Nat}
    (y : Bitstring N) (hB : clock N ≤ B)
    (steps : Nat) (hsteps : steps ≤ clock N)
    (j : Fin (tapeLength N B))
    (hj : tapeLength N (clock N) ≤ j.val) :
    (machine.run steps (initialConfig machine B y)).tape j = none := by
  exact (ambient_run_extension y hB steps hsteps).2.2.2 j hj

/-- Strong blank-padding invariant: at every time through the deadline, every
ambient cell outside the raw input is blank.  This includes both padding in
the exact allocation and every cell added by the ambient budget. -/
theorem ambient_padding_blank_through_clock {N B : Nat} (y : Bitstring N)
    (hB : clock N ≤ B) (steps : Nat) (hsteps : steps ≤ clock N)
    (j : Fin (tapeLength N B)) (hjN : N ≤ j.val) :
    (machine.run steps (initialConfig machine B y)).tape j = none := by
  have hrel := ambient_run_extension y hB steps hsteps
  by_cases hj : j.val < tapeLength N (clock N)
  · let i : Fin (tapeLength N (clock N)) := ⟨j.val, hj⟩
    have hembed : tapeEmbed hB i = j := by
      apply Fin.ext
      rfl
    rw [← hembed, hrel.2.2.1 i]
    exact exact_padding_blank_through_clock y steps hsteps i hjN
  · exact hrel.2.2.2 j (Nat.le_of_not_gt hj)

/-- Allocation does not change either literal verdict predicate at any time
through the parser deadline. -/
theorem ambient_acceptsAt_iff_exact {N B : Nat} (y : Bitstring N)
    (hB : clock N ≤ B) (steps : Nat) (hsteps : steps ≤ clock N) :
    AcceptsAt machine B steps y ↔
      AcceptsAt machine (clock N) steps y := by
  have hstate := (ambient_run_extension y hB steps hsteps).1
  change
    (machine.run steps (initialConfig machine B y)).state = machine.accept ↔
      (machine.run steps
        (initialConfig machine (clock N) y)).state = machine.accept
  rw [← hstate]

theorem ambient_rejectsAt_iff_exact {N B : Nat} (y : Bitstring N)
    (hB : clock N ≤ B) (steps : Nat) (hsteps : steps ≤ clock N) :
    RejectsAt machine B steps y ↔
      RejectsAt machine (clock N) steps y := by
  have hstate := (ambient_run_extension y hB steps hsteps).1
  change
    (machine.run steps (initialConfig machine B y)).state = machine.reject ↔
      (machine.run steps
        (initialConfig machine (clock N) y)).state = machine.reject
  rw [← hstate]

private theorem config_ext_any {k N B : Nat} {c d : Config k N B}
    (hstate : c.state = d.state) (hhead : c.head = d.head)
    (htape : c.tape = d.tape) : c = d := by
  cases c with
  | mk cs ch ct =>
      cases d with
      | mk ds dh dt =>
          change cs = ds at hstate
          change ch = dh at hhead
          change ct = dt at htape
          subst ds
          subst dh
          subst dt
          rfl

/-- Exact ambient final state, head, and the entire ambient tape. -/
private theorem ambient_run_initialConfig_fields {N B : Nat} (y : Bitstring N)
    (hB : clock N ≤ B) :
    let c₀ := initialConfig machine B y
    let cF := machine.run (clock N) c₀
    cF.state = expectedFinalState y ∧
      cF.head.val = 0 ∧
      cF.tape = c₀.tape := by
  dsimp
  have hrun := ambient_run_extension y hB (clock N) (Nat.le_refl _)
  have hinit := initialConfig_extension machine hB y
  have hexact := run_initialConfig_fields y
  change
    (machine.run (clock N)
      (initialConfig machine (clock N) y)).state = expectedFinalState y ∧
    (machine.run (clock N)
      (initialConfig machine (clock N) y)).head.val = 0 ∧
    (machine.run (clock N)
      (initialConfig machine (clock N) y)).tape =
        (initialConfig machine (clock N) y).tape at hexact
  rcases hrun with ⟨hstate, hhead, hlow, hextra⟩
  constructor
  · exact hstate.symm.trans hexact.1
  constructor
  · have hval := congrArg Fin.val hhead
    simp only [tapeEmbed_val] at hval
    exact hval.trans hexact.2.1
  · funext j
    by_cases hj : j.val < tapeLength N (clock N)
    · let i : Fin (tapeLength N (clock N)) := ⟨j.val, hj⟩
      have hembed : tapeEmbed hB i = j := by
        apply Fin.ext
        rfl
      rw [← hembed, hlow i, hexact.2.2, ← hinit.2.2.1 i]
    · have hjge : tapeLength N (clock N) ≤ j.val :=
        Nat.le_of_not_gt hj
      rw [hextra j hjge, hinit.2.2.2 j hjge]

/-- Full ambient configuration equality.  The record update changes only the
literal final control; head zero and every ambient tape cell are restored. -/
theorem ambient_run_initialConfig_exact {N B : Nat} (y : Bitstring N)
    (hB : clock N ≤ B) :
    machine.run (clock N) (initialConfig machine B y) =
      { initialConfig machine B y with state := expectedFinalState y } := by
  have h := ambient_run_initialConfig_fields y hB
  apply config_ext_any
  · exact h.1
  · apply Fin.ext
    exact h.2.1
  · exact h.2.2

/-- Literal accepting branch of the full final-configuration theorem. -/
theorem ambient_run_initialConfig_accept {N B : Nat} (y : Bitstring N)
    (hB : clock N ≤ B) (p : DecodedPair)
    (hdecode : decodePair y = some p) :
    machine.run (clock N) (initialConfig machine B y) =
      { initialConfig machine B y with state := qAccept } := by
  simpa [expectedFinalState, hdecode] using
    ambient_run_initialConfig_exact y hB

/-- Literal rejecting branch of the full final-configuration theorem. -/
theorem ambient_run_initialConfig_reject {N B : Nat} (y : Bitstring N)
    (hB : clock N ≤ B) (hdecode : decodePair y = none) :
    machine.run (clock N) (initialConfig machine B y) =
      { initialConfig machine B y with state := qReject } := by
  simpa [expectedFinalState, hdecode] using
    ambient_run_initialConfig_exact y hB

/-- The final control is stated literally, rather than hidden in a Boolean
decision predicate. -/
theorem ambient_final_literal_state {N B : Nat} (y : Bitstring N)
    (hB : clock N ≤ B) :
    (machine.run (clock N) (initialConfig machine B y)).state =
      match decodePair y with
      | some _ => qAccept
      | none => qReject := by
  simpa [expectedFinalState] using
    (ambient_run_initialConfig_fields y hB).1

private theorem ambient_head_zero_at_clock {N B : Nat} (y : Bitstring N)
    (hB : clock N ≤ B) :
    (machine.run (clock N)
      (initialConfig machine B y)).head.val = 0 :=
  (ambient_run_initialConfig_fields y hB).2.1

/-- The final head as an actual ambient-domain `Fin`, not merely a value
projection. -/
theorem ambient_head_literal_zero_at_clock {N B : Nat} (y : Bitstring N)
    (hB : clock N ≤ B) :
    (machine.run (clock N) (initialConfig machine B y)).head =
      (⟨0, by simp [tapeLength]⟩ : Fin (tapeLength N B)) := by
  apply Fin.ext
  exact ambient_head_zero_at_clock y hB

theorem ambient_tape_restored_at_clock {N B : Nat} (y : Bitstring N)
    (hB : clock N ≤ B) :
    (machine.run (clock N) (initialConfig machine B y)).tape =
      (initialConfig machine B y).tape :=
  (ambient_run_initialConfig_fields y hB).2.2

/-- Pointwise final tape contract: the raw input is restored, and every cell
from `N` onward (including all newly allocated cells) is blank. -/
theorem ambient_final_tape_behavior {N B : Nat} (y : Bitstring N)
    (hB : clock N ≤ B) :
    let cF := machine.run (clock N) (initialConfig machine B y)
    (∀ i : Fin N,
      cF.tape
        ⟨i.val, Nat.lt_of_lt_of_le i.isLt
          (Nat.le_add_right N (B + 1))⟩ = some (y i)) ∧
    (∀ j : Fin (tapeLength N B), N ≤ j.val → cF.tape j = none) := by
  dsimp
  have htape := ambient_tape_restored_at_clock y hB
  constructor
  · intro i
    rw [htape]
    exact initialConfig_tape_input machine y i
  · intro j hj
    rw [htape]
    exact initialConfig_tape_padding machine y j hj

/-- Ambient execution has no public terminal before the exact parser clock. -/
private theorem ambient_noEarlyTerminal_initialConfig {N B : Nat} (y : Bitstring N)
    (hB : clock N ≤ B) (steps : Nat) (hsteps : steps < clock N) :
    let c := machine.run steps (initialConfig machine B y)
    c.state ≠ machine.accept ∧ c.state ≠ machine.reject := by
  dsimp
  have hrel := ambient_run_extension y hB steps (Nat.le_of_lt hsteps)
  have hexact := noEarlyTerminal_initialConfig y steps hsteps
  constructor
  · intro hterminal
    exact hexact.1 (hrel.1.trans hterminal)
  · intro hterminal
    exact hexact.2 (hrel.1.trans hterminal)

theorem ambient_no_public_terminal_before_clock {N B : Nat}
    (y : Bitstring N) (hB : clock N ≤ B)
    (steps : Nat) (hsteps : steps < clock N) :
    ¬ AcceptsAt machine B steps y ∧ ¬ RejectsAt machine B steps y := by
  simpa [AcceptsAt, RejectsAt] using
    ambient_noEarlyTerminal_initialConfig y hB steps hsteps

theorem ambient_acceptsAt_clock_iff_decodePair_some {N B : Nat}
    (y : Bitstring N) (hB : clock N ≤ B) :
    AcceptsAt machine B (clock N) y ↔
      ∃ p : DecodedPair, decodePair y = some p := by
  have hstate := (ambient_run_extension y hB (clock N) (Nat.le_refl _)).1
  change
    (machine.run (clock N) (initialConfig machine B y)).state =
        machine.accept ↔ _
  rw [← hstate]
  simpa [AcceptsAt] using acceptsAt_clock_iff_decodePair_some y

theorem ambient_rejectsAt_clock_iff_decodePair_none {N B : Nat}
    (y : Bitstring N) (hB : clock N ≤ B) :
    RejectsAt machine B (clock N) y ↔ decodePair y = none := by
  have hstate := (ambient_run_extension y hB (clock N) (Nat.le_refl _)).1
  change
    (machine.run (clock N) (initialConfig machine B y)).state =
        machine.reject ↔ _
  rw [← hstate]
  simpa [RejectsAt] using rejectsAt_clock_iff_decodePair_none y

/-- The within-ambient-budget theorem uses `clock N` itself as its witness.
It deliberately does not misuse the exact-deadline/within theorem at budget
`B`, whose exact deadline would be `B`. -/
theorem ambient_decidesWithin {N B : Nat} (y : Bitstring N)
    (hB : clock N ≤ B) :
    DecidesWithin machine B y (decodePair y).isSome := by
  cases hdecode : decodePair y with
  | none =>
      change RejectsWithin machine B y
      exact ⟨clock N, hB,
        (ambient_rejectsAt_clock_iff_decodePair_none y hB).2 hdecode⟩
  | some p =>
      change AcceptsWithin machine B y
      exact ⟨clock N, hB,
        (ambient_acceptsAt_clock_iff_decodePair_some y hB).2 ⟨p, hdecode⟩⟩

end Pnp3.Complexity.Uniform.V1.FixedPairParser
