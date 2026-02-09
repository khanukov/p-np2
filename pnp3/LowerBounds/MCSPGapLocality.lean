import Core.BooleanBasics
import Models.Model_PartialMCSP
import Complexity.Promise

/-!
  pnp3/LowerBounds/MCSPGapLocality.lean

  MCSP gap lower bound for local functions.

  Core result: no function that depends on at most 2^n/2 coordinates
  can correctly solve the Gap Partial MCSP promise problem.

  ## Proof overview

  The input to Gap Partial MCSP is `mask ++ values` (length N = 2·2ⁿ).
  A "local" function depends on at most 2ⁿ/2 coordinates ("alive").

  We construct two inputs `x_yes` and `x_no` that **agree on all alive
  coordinates** but land on opposite sides of the promise:

  * `x_yes` — mask is ON only at alive mask positions, values = false
    → partially undefined partial function →
    `Circuit.const false` is consistent → YES instance.
  * `x_no`  — all mask bits are ON → fully defined function with high
    circuit complexity → NO instance (by Shannon counting).

  Since f depends only on alive coordinates, `f(x_yes) = f(x_no)`.
  But correctness forces `f(x_yes) = true` and `f(x_no) = false`. ⊥

  ## Remaining axiom

  `exists_hard_function_with_constraints` is a Shannon counting axiom:
  among Boolean functions constrained to be false on ≤ 2^n/2 positions,
  at least one has circuit complexity ≥ sNO.
-/

namespace Pnp3
namespace LowerBounds

open Core
open Complexity
open ComplexityInterfaces
open Models

/-!
  ### Shannon counting axiom
-/

/--
  Shannon counting: there exists a total Boolean function on `p.n` variables
  that (1) outputs `false` at every position in a given constraint set, and
  (2) has circuit complexity ≥ `p.sNO`.

  The constraint set has at most `Partial.tableLen p.n / 2` elements, leaving
  at least `2^(p.n) / 2` free positions. The number of Boolean functions over
  those free positions is `2^(2^(p.n)/2)`, while the number of circuits of
  size `< p.sNO` is at most `(p.n + p.sNO)^O(p.sNO)`. For `p.n ≥ 8` and
  small `p.sNO`, the former dwarfs the latter, so a hard function exists.
-/
axiom exists_hard_function_with_constraints
    (p : GapPartialMCSPParams)
    (constrained : Finset (Fin (Partial.tableLen p.n)))
    (h_constrained_small : constrained.card ≤ Partial.tableLen p.n / 2) :
    ∃ (g : Core.BitVec (Partial.tableLen p.n)),
      (∀ i ∈ constrained, g i = false) ∧
      PartialMCSP_NO p (totalTableToPartial g)

/-!
  ### Input construction helpers
-/

/-- Build a BitVec (inputLen n) from mask and value components. -/
def buildInput {n : Nat} (mask vals : Core.BitVec (Partial.tableLen n)) :
    Core.BitVec (Partial.inputLen n) :=
  fun i =>
    if h : (i : Nat) < Partial.tableLen n then
      mask ⟨i, h⟩
    else
      have h2 : (i : Nat) - Partial.tableLen n < Partial.tableLen n := by
        have hlt : (i : Nat) < Partial.inputLen n := i.2
        have hge : Partial.tableLen n ≤ (i : Nat) := Nat.le_of_not_gt h
        have : (i : Nat) < Partial.tableLen n + Partial.tableLen n := by
          simpa [Partial.inputLen, two_mul] using hlt
        omega
      vals ⟨(i : Nat) - Partial.tableLen n, h2⟩

/-- The mask part of buildInput is the given mask. -/
lemma buildInput_maskPart {n : Nat} (mask vals : Core.BitVec (Partial.tableLen n)) :
    Partial.maskPart (buildInput mask vals) = mask := by
  funext i
  simp [Partial.maskPart, Partial.maskIndex, buildInput, i.2]

/-- The value part of buildInput is the given vals. -/
lemma buildInput_valPart {n : Nat} (mask vals : Core.BitVec (Partial.tableLen n)) :
    Partial.valPart (buildInput mask vals) = vals := by
  funext i
  simp only [Partial.valPart, Partial.valIndex, buildInput]
  have hge : ¬ (Partial.tableLen n + ↑i) < Partial.tableLen n := by omega
  simp [hge]

/-- decodePartial of buildInput when all masks are true gives totalTableToPartial. -/
lemma decodePartial_buildInput_allTrue {n : Nat} (vals : Core.BitVec (Partial.tableLen n)) :
    decodePartial (buildInput (fun _ => true) vals) = totalTableToPartial vals := by
  funext i
  simp [decodePartial, buildInput_maskPart, buildInput_valPart,
    totalTableToPartial]

/-!
  ### Position maps
-/

/-- Map a table index to its mask position in the input. -/
def tableMaskPos {n : Nat} (j : Fin (Partial.tableLen n)) : Fin (Partial.inputLen n) :=
  Partial.maskIndex j

/-- Map a table index to its value position in the input. -/
def tableValPos {n : Nat} (j : Fin (Partial.tableLen n)) : Fin (Partial.inputLen n) :=
  Partial.valIndex j

/-- tableValPos is injective. -/
lemma tableValPos_injective {n : Nat} : Function.Injective (@tableValPos n) := by
  intro a b h
  simp [tableValPos, Partial.valIndex, Fin.ext_iff] at h
  exact Fin.ext (by omega)

/-!
  ### Helper lemmas for the YES case
-/

/-- Circuit.const false is consistent with any partial function whose defined values
    are all `false`. -/
lemma const_false_consistent_of_vals_false {n : Nat}
    (T : PartialTruthTable n)
    (h : ∀ j, T j = none ∨ T j = some false) :
    is_consistent (Circuit.const false) T := by
  intro x
  cases hTx : T (assignmentIndex x) with
  | none => trivial
  | some b =>
    have := h (assignmentIndex x)
    cases this with
    | inl h_none => simp [hTx] at h_none
    | inr h_false =>
      simp [hTx] at h_false
      subst h_false
      simp [Circuit.eval]

/-!
  ### Main existence lemma

  We construct YES and NO instances that agree on all alive coordinates.
-/

/--
  For any alive set with |alive| ≤ tableLen/2, there exist a YES instance and
  a NO instance that agree on all alive coordinates.

  Construction:
  - x_yes: mask[j] = true iff mask position j ∈ alive, values = false
    → partial function undefined at free mask positions
    → Circuit.const false is consistent at all defined positions (all false)
    → YES (since `p.sYES ≥ 1`)

  - x_no: mask[j] = true for all j, values = hard function g
    → fully defined function = g
    → g has high circuit complexity → NO

  Agreement: at alive mask positions, both have mask = true; at alive value
  positions, x_yes has value = false and x_no has g[j] = false (constrained
  by Shannon counting on table indices whose value position is alive).
-/
theorem exists_yes_no_agreeing_on_alive
    (p : GapPartialMCSPParams)
    (alive : Finset (Fin (partialInputLen p)))
    (h_small : alive.card ≤ Partial.tableLen p.n / 2) :
    ∃ (x_yes x_no : Core.BitVec (partialInputLen p)),
      (∀ i ∈ alive, x_yes i = x_no i) ∧
      x_yes ∈ (GapPartialMCSPPromise p).Yes ∧
      x_no ∈ (GapPartialMCSPPromise p).No := by
  classical
  -- The "constrained" set: table indices j whose VALUE position is alive.
  -- At these positions, the hard function g must be false (to agree with x_yes).
  let constrained : Finset (Fin (Partial.tableLen p.n)) :=
    Finset.univ.filter (fun j => tableValPos j ∈ alive)
  -- Bound: |constrained| ≤ |alive| ≤ tableLen / 2
  -- (tableValPos is injective, so the image in alive has size ≤ |alive|)
  have h_constrained_small : constrained.card ≤ Partial.tableLen p.n / 2 := by
    calc constrained.card
        ≤ alive.card := by
          -- The image of constrained under tableValPos is a subset of alive
          have h_img_sub : Finset.image tableValPos constrained ⊆ alive := by
            intro i hi
            simp only [constrained, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
              true_and] at hi
            obtain ⟨j, hj, rfl⟩ := hi
            exact hj
          calc constrained.card
            = (Finset.image tableValPos constrained).card := by
                rw [Finset.card_image_of_injective constrained tableValPos_injective]
            _ ≤ alive.card := Finset.card_le_card h_img_sub
      _ ≤ Partial.tableLen p.n / 2 := h_small
  -- Get a hard function g that is false on all constrained positions
  obtain ⟨g, hg_false, hg_no⟩ :=
    exists_hard_function_with_constraints p constrained h_constrained_small
  -- Define mask for x_yes: true only at alive mask positions
  let mask_yes : Core.BitVec (Partial.tableLen p.n) :=
    fun j => if tableMaskPos j ∈ alive then true else false
  -- x_yes: mask = mask_yes, values = all false
  let x_yes : Core.BitVec (partialInputLen p) :=
    buildInput mask_yes (fun _ => false)
  -- x_no: mask = all true, values = g
  let x_no : Core.BitVec (partialInputLen p) :=
    buildInput (fun _ => true) g
  refine ⟨x_yes, x_no, ?agree, ?yes_mem, ?no_mem⟩
  case agree =>
    -- Show x_yes and x_no agree on all alive positions
    intro i hi
    -- Position i is either a mask position (i < tableLen) or value position (i ≥ tableLen)
    by_cases h_lt : (i : Nat) < Partial.tableLen p.n
    · -- i is a mask position at table index j = ⟨i, h_lt⟩
      -- x_yes[i] = mask_yes[j] = true (since tableMaskPos j = i ∈ alive)
      -- x_no[i] = true (all masks are true)
      simp only [x_yes, x_no, buildInput, h_lt]
      have h_eq : tableMaskPos ⟨i, h_lt⟩ = i := by
        apply Fin.ext; simp [tableMaskPos, Partial.maskIndex]
      simp [mask_yes, h_eq, hi]
    · -- i is a value position: i = tableLen + j for some j
      have h_val : Partial.tableLen p.n ≤ (i : Nat) := Nat.le_of_not_gt h_lt
      have h_i_lt : (i : Nat) < Partial.inputLen p.n := i.2
      have h_j_lt : (i : Nat) - Partial.tableLen p.n < Partial.tableLen p.n := by
        have : (i : Nat) < Partial.tableLen p.n + Partial.tableLen p.n := by
          simpa [Partial.inputLen, two_mul, partialInputLen] using h_i_lt
        omega
      -- Both x_yes and x_no take the else branch, evaluating the value function at j
      simp only [x_yes, x_no, buildInput, h_lt]
      -- x_yes value at j = false, x_no value at j = g j
      -- Since tableValPos j = i ∈ alive, j ∈ constrained, so g j = false
      have h_i_is_valpos : tableValPos ⟨(i : Nat) - Partial.tableLen p.n, h_j_lt⟩ = i := by
        apply Fin.ext
        simp [tableValPos, Partial.valIndex]
        omega
      have h_j_in_constrained :
          ⟨(i : Nat) - Partial.tableLen p.n, h_j_lt⟩ ∈ constrained := by
        simp only [constrained, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [h_i_is_valpos]
        exact hi
      have h_gj_false : g ⟨(i : Nat) - Partial.tableLen p.n, h_j_lt⟩ = false :=
        hg_false _ h_j_in_constrained
      -- Now both sides should evaluate to the same value
      simp [h_gj_false]
  case yes_mem =>
    -- x_yes is a YES instance
    show gapPartialMCSP_Language p (partialInputLen p) x_yes = true
    rw [gapPartialMCSP_language_true_iff_yes]
    -- decodePartial of x_yes: defined only where mask_yes = true, with value false
    have h_decode : decodePartial x_yes =
        fun j => if mask_yes j then some false else none := by
      funext j
      simp [x_yes, decodePartial, buildInput_maskPart, buildInput_valPart]
    -- Circuit.const false is consistent and has size 1 ≤ sYES
    refine ⟨Circuit.const false, ?_, ?_⟩
    · simp [Circuit.size]
      exact p.sYES_pos
    · rw [h_decode]
      apply const_false_consistent_of_vals_false
      intro j
      by_cases hm : mask_yes j
      · right; simp [hm]
      · left; simp [hm]
  case no_mem =>
    -- x_no is a NO instance
    show gapPartialMCSP_Language p (partialInputLen p) x_no = false
    apply gapPartialMCSP_language_false_of_no
    -- decodePartial of x_no with all masks true and values = g is totalTableToPartial g
    rw [show decodePartial x_no = totalTableToPartial g from by
      simp [x_no, decodePartial_buildInput_allTrue]]
    exact hg_no

/--
  No local function can solve the Gap Partial MCSP promise problem.

  If `f` depends on at most `2^n / 2` coordinates (the "alive" set) and
  correctly decides the Gap Partial MCSP promise, we derive a contradiction.
-/
theorem no_local_function_solves_mcsp {p : GapPartialMCSPParams}
    (f : Core.BitVec (partialInputLen p) → Bool)
    (alive : Finset (Fin (partialInputLen p)))
    (h_small : alive.card ≤ Partial.tableLen p.n / 2)
    (h_local : ∀ x y : Core.BitVec (partialInputLen p),
      (∀ i ∈ alive, x i = y i) → f x = f y)
    (h_correct : SolvesPromise (GapPartialMCSPPromise p) f) :
    False := by
  -- Get YES and NO instances agreeing on alive
  obtain ⟨x_yes, x_no, h_agree, h_in_yes, h_in_no⟩ :=
    exists_yes_no_agreeing_on_alive p alive h_small
  -- By locality, f gives the same answer on both
  have h_eq : f x_yes = f x_no := h_local x_yes x_no h_agree
  -- But correctness demands different answers
  have h_true : f x_yes = true := h_correct.1 x_yes h_in_yes
  have h_false : f x_no = false := h_correct.2 x_no h_in_no
  -- Contradiction: true = false
  rw [h_true] at h_eq
  exact absurd h_eq (by rw [h_false]; decide)

end LowerBounds
end Pnp3
