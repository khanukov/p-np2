import Core.BooleanBasics
import Models.Model_PartialMCSP
import Complexity.Promise
import Counting.ShannonCounting

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

  ## Shannon counting (formerly an axiom, now proved)

  `exists_hard_function_with_constraints` was formerly a Shannon counting axiom.
  It is now a theorem proved in `Counting.ShannonCounting` via pigeonhole:
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
  ### Shannon counting (proved in Counting.ShannonCounting)

  `Counting.exists_hard_function_with_constraints` is now a theorem, not an axiom.
  We re-export it here under the same name so downstream files are unaffected.
-/

/-- Shannon counting: there exists a hard function consistent with constraints.
    Proved via pigeonhole in `Counting.ShannonCounting`. -/
theorem exists_hard_function_with_constraints
    (p : GapPartialMCSPParams)
    (constrained : Finset (Fin (Partial.tableLen p.n)))
    (h_constrained_small : constrained.card ≤ Partial.tableLen p.n / 2) :
    ∃ (g : Core.BitVec (Partial.tableLen p.n)),
      (∀ i ∈ constrained, g i = false) ∧
      PartialMCSP_NO p (totalTableToPartial g) :=
  Counting.exists_hard_function_with_constraints p constrained h_constrained_small

/--
Counting-slack wrapper for constrained hardness.

This theorem isolates the exact future target hypothesis

`circuitCountBound < 2^(tableLen - |constrained|)`.
-/
theorem exists_hard_function_with_constraints_of_countingSlack
    (p : GapPartialMCSPParams)
    (constrained : Finset (Fin (Partial.tableLen p.n)))
    (hSlack :
      Models.circuitCountBound p.n (p.sNO - 1) <
        2 ^ (Partial.tableLen p.n - constrained.card)) :
    ∃ (g : Core.BitVec (Partial.tableLen p.n)),
      (∀ i ∈ constrained, g i = false) ∧
      PartialMCSP_NO p (totalTableToPartial g) := by
  exact Counting.exists_hard_function_with_constraints_of_countingSlack
    p constrained hSlack

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
  ### Value-coordinate interfaces
-/

/-- Semantic truth-table coordinate sets for the value-only locality route. -/
abbrev ValueCoordinateSet (p : GapPartialMCSPParams) :=
  Finset (Fin (Partial.tableLen p.n))

/-- Agreement of two encoded inputs on semantic value coordinates only. -/
def AgreeOnValues {p : GapPartialMCSPParams}
    (S : ValueCoordinateSet p)
    (x y : Core.BitVec (partialInputLen p)) : Prop :=
  ∀ i ∈ S, Partial.valPart x i = Partial.valPart y i

/--
Canonical encoded inputs are treated as the valid representatives of their
decoded partial tables.
-/
def ValidEncoding (p : GapPartialMCSPParams)
    (x : Core.BitVec (partialInputLen p)) : Prop :=
  x = encodePartial (decodePartial x)

/-- Every canonical `encodePartial` output is a valid encoded input. -/
lemma validEncoding_encodePartial
    (p : GapPartialMCSPParams)
    (T : PartialTruthTable p.n) :
    ValidEncoding p (encodePartial T) := by
  simp [ValidEncoding, decodePartial_encodePartial]

/-- Total-table encodings are valid encoded inputs. -/
lemma validEncoding_encodeTotalAsPartial
    (p : GapPartialMCSPParams)
    (table : Core.BitVec (Partial.tableLen p.n)) :
    ValidEncoding p (encodeTotalAsPartial table) := by
  simpa [encodeTotalAsPartial] using
    validEncoding_encodePartial p (totalTableToPartial table)

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
  Generalized YES/NO pair construction from a *constrained-hardness oracle*.

  This statement isolates the mathematically essential object for the
  anti-locality contradiction:
  for every constrained set of table coordinates with cardinality at most
  `|alive|`, there exists a hard function `g` that is forced to be `false` on
  those coordinates and still lands in the NO side.

  Compared with `exists_yes_no_agreeing_on_alive`, this theorem does **not**
  assume any fixed fraction bound such as `|alive| ≤ tableLen/2`; that
  quantitative hypothesis is only one sufficient way to instantiate the oracle
  (via Shannon counting in the previous theorem).
-/
theorem exists_yes_no_agreeing_on_alive_of_constrainedHardness
    (p : GapPartialMCSPParams)
    (alive : Finset (Fin (partialInputLen p)))
    (hHard :
      ∀ constrained : Finset (Fin (Partial.tableLen p.n)),
        constrained.card ≤ alive.card →
          ∃ (g : Core.BitVec (Partial.tableLen p.n)),
            (∀ i ∈ constrained, g i = false) ∧
            PartialMCSP_NO p (totalTableToPartial g)) :
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
  have h_constrained_le_alive : constrained.card ≤ alive.card := by
    -- The image of constrained under tableValPos is a subset of alive.
    have h_img_sub : Finset.image tableValPos constrained ⊆ alive := by
      intro i hi
      simp only [constrained, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and] at hi
      obtain ⟨j, hj, rfl⟩ := hi
      exact hj
    have h_card_img :
        constrained.card = (Finset.image tableValPos constrained).card := by
      rw [Finset.card_image_of_injective constrained tableValPos_injective]
    calc
      constrained.card = (Finset.image tableValPos constrained).card := h_card_img
      _ ≤ alive.card := Finset.card_le_card h_img_sub
  -- Get a hard function g that is false on all constrained positions using the
  -- external constrained-hardness oracle.
  obtain ⟨g, hg_false, hg_no⟩ := hHard constrained h_constrained_le_alive
  -- Define mask for x_yes: true only at alive mask positions
  let mask_yes : Core.BitVec (Partial.tableLen p.n) :=
    fun j => if tableMaskPos j ∈ alive then true else false
  -- x_yes: mask = mask_yes, values = all false
  let x_yes : Core.BitVec (partialInputLen p) :=
    buildInput mask_yes (fun _ => false)
  -- x_no: mask = all true, values = g
  let x_no : Core.BitVec (partialInputLen p) :=
    buildInput (fun _ => true) g
  refine ⟨x_yes, x_no, ?_, ?_, ?_⟩
  ·
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
  ·
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
  ·
    -- x_no is a NO instance
    show gapPartialMCSP_Language p (partialInputLen p) x_no = false
    apply gapPartialMCSP_language_false_of_no
    -- decodePartial of x_no with all masks true and values = g is totalTableToPartial g
    rw [show decodePartial x_no = totalTableToPartial g from by
      simp [x_no, decodePartial_buildInput_allTrue]]
    exact hg_no

/--
Counting-slack instantiation of the generalized YES/NO construction.

This is the direct-slack instantiation of the generalized constrained-hardness
consumer: locality on `alive` yields monotone slack for every constrained value
coordinate subset of `alive`, and Shannon counting is consumed without any
half-table adapter.
-/
theorem exists_yes_no_agreeing_on_alive_of_countingSlack
    (p : GapPartialMCSPParams)
    (alive : Finset (Fin (partialInputLen p)))
    (hSlackAlive :
      Models.circuitCountBound p.n (p.sNO - 1) <
        2 ^ (Partial.tableLen p.n - alive.card)) :
    ∃ (x_yes x_no : Core.BitVec (partialInputLen p)),
      (∀ i ∈ alive, x_yes i = x_no i) ∧
      x_yes ∈ (GapPartialMCSPPromise p).Yes ∧
      x_no ∈ (GapPartialMCSPPromise p).No := by
  apply exists_yes_no_agreeing_on_alive_of_constrainedHardness p alive
  intro constrained h_constrained_le_alive
  have hSlackConstrained :
      Models.circuitCountBound p.n (p.sNO - 1) <
        2 ^ (Partial.tableLen p.n - constrained.card) := by
    have hExpMono :
        Partial.tableLen p.n - alive.card ≤ Partial.tableLen p.n - constrained.card := by
      exact Nat.sub_le_sub_left h_constrained_le_alive (Partial.tableLen p.n)
    exact lt_of_lt_of_le hSlackAlive (Nat.pow_le_pow_right (by decide : 0 < 2) hExpMono)
  exact exists_hard_function_with_constraints_of_countingSlack p constrained
    hSlackConstrained

/--
Promise-valid YES/NO pair construction using only value-coordinate agreement.

The produced witnesses are canonical encodings, live on the promise domain, and
agree only on semantic truth-table values indexed by `S`.
-/
theorem exists_yes_no_agreeing_on_values_of_countingSlack
    (p : GapPartialMCSPParams)
    (S : ValueCoordinateSet p)
    (hSlack :
      Models.circuitCountBound p.n (p.sNO - 1) <
        2 ^ (Partial.tableLen p.n - S.card)) :
    ∃ (x_yes x_no : Core.BitVec (partialInputLen p)),
      AgreeOnValues S x_yes x_no ∧
      ValidEncoding p x_yes ∧
      ValidEncoding p x_no ∧
      x_yes ∈ (GapPartialMCSPPromise p).Yes ∧
      x_no ∈ (GapPartialMCSPPromise p).No := by
  obtain ⟨g, hg_false, hg_no⟩ :=
    exists_hard_function_with_constraints_of_countingSlack p S hSlack
  let T_yes : PartialTruthTable p.n :=
    fun i => if i ∈ S then some false else none
  let x_yes : Core.BitVec (partialInputLen p) := encodePartial T_yes
  let x_no : Core.BitVec (partialInputLen p) := encodeTotalAsPartial g
  refine ⟨x_yes, x_no, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have h_yes_val : Partial.valPart x_yes i = false := by
      simp [x_yes, T_yes, Partial.valPart, encodePartial, Partial.valIndex, hi]
    have h_no_val : Partial.valPart x_no i = g i := by
      simp [x_no, encodeTotalAsPartial, totalTableToPartial,
        Partial.valPart, encodePartial, Partial.valIndex]
    rw [h_yes_val, h_no_val, hg_false i hi]
  · exact validEncoding_encodePartial p T_yes
  · exact validEncoding_encodeTotalAsPartial p g
  · show gapPartialMCSP_Language p (partialInputLen p) x_yes = true
    rw [gapPartialMCSP_language_true_iff_yes]
    rw [show decodePartial x_yes = T_yes from by
      simp [x_yes, decodePartial_encodePartial]]
    refine ⟨Circuit.const false, ?_, ?_⟩
    · simp [Circuit.size]
      exact p.sYES_pos
    · apply const_false_consistent_of_vals_false
      intro i
      by_cases hi : i ∈ S
      · right
        simp [T_yes, hi]
      · left
        simp [T_yes, hi]
  · show gapPartialMCSP_Language p (partialInputLen p) x_no = false
    apply gapPartialMCSP_language_false_of_no
    rw [show decodePartial x_no = totalTableToPartial g from by
      simp [x_no, decodePartial_encodeTotal]]
    exact hg_no

/--
Given a valid center and semantic coordinates `S`, counting slack yields a
valid NO-completion agreeing with the center on the value coordinates in `S`.
-/
theorem exists_no_completion_agreeing_on_values_of_countingSlack
    (p : GapPartialMCSPParams)
    (x_center : Core.BitVec (partialInputLen p))
    (S : ValueCoordinateSet p)
    (hSlack :
      Models.circuitCountBound p.n (p.sNO - 1) <
        2 ^ (Partial.tableLen p.n - S.card)) :
    ∃ x_no : Core.BitVec (partialInputLen p),
      AgreeOnValues S x_center x_no ∧
      ValidEncoding p x_no ∧
      x_no ∈ (GapPartialMCSPPromise p).No := by
  let centerValues : Core.BitVec (Partial.tableLen p.n) := Partial.valPart x_center
  obtain ⟨g, hg_match, hg_no⟩ :=
    Counting.exists_hard_function_with_value_constraints_of_countingSlack
      p S centerValues hSlack
  let x_no : Core.BitVec (partialInputLen p) := encodeTotalAsPartial g
  refine ⟨x_no, ?_, ?_, ?_⟩
  · intro i hi
    have h_no_val : Partial.valPart x_no i = g i := by
      simp [x_no, encodeTotalAsPartial, totalTableToPartial,
        Partial.valPart, encodePartial, Partial.valIndex]
    calc
      Partial.valPart x_center i = centerValues i := by rfl
      _ = g i := by symm; exact hg_match i hi
      _ = Partial.valPart x_no i := h_no_val.symm
  · exact validEncoding_encodeTotalAsPartial p g
  · apply gapPartialMCSP_no_of_large
    simpa [x_no, decodePartial_encodeTotal] using hg_no

/--
  For any alive set with |alive| ≤ tableLen/2, there exist a YES instance and
  a NO instance that agree on all alive coordinates.

  This is the Shannon-counting instantiation of the generalized constrained
  hardness theorem `exists_yes_no_agreeing_on_alive_of_constrainedHardness`.
-/
theorem exists_yes_no_agreeing_on_alive
    (p : GapPartialMCSPParams)
    (alive : Finset (Fin (partialInputLen p)))
    (h_small : alive.card ≤ Partial.tableLen p.n / 2) :
    ∃ (x_yes x_no : Core.BitVec (partialInputLen p)),
      (∀ i ∈ alive, x_yes i = x_no i) ∧
      x_yes ∈ (GapPartialMCSPPromise p).Yes ∧
      x_no ∈ (GapPartialMCSPPromise p).No := by
  apply exists_yes_no_agreeing_on_alive_of_constrainedHardness p alive
  intro constrained h_constrained_le_alive
  exact exists_hard_function_with_constraints p constrained
    (le_trans h_constrained_le_alive h_small)

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

/--
Value-only / promise-only anti-locality consumer.

This version asks for locality only on canonical encoded inputs lying on the
promise domain, and only with respect to semantic truth-table value
coordinates.
-/
theorem no_value_local_function_solves_mcsp_of_countingSlack
    {p : GapPartialMCSPParams}
    (f : Core.BitVec (partialInputLen p) → Bool)
    (S : ValueCoordinateSet p)
    (hSlack :
      Models.circuitCountBound p.n (p.sNO - 1) <
        2 ^ (Partial.tableLen p.n - S.card))
    (hLocal :
      ∀ x y : Core.BitVec (partialInputLen p),
        x ∈ (GapPartialMCSPPromise p).Yes →
        y ∈ (GapPartialMCSPPromise p).No →
        ValidEncoding p x →
        ValidEncoding p y →
        AgreeOnValues S x y →
        f x = f y)
    (hCorrect : SolvesPromise (GapPartialMCSPPromise p) f) :
    False := by
  obtain ⟨x_yes, x_no, hAgree, hValidYes, hValidNo, hInYes, hInNo⟩ :=
    exists_yes_no_agreeing_on_values_of_countingSlack p S hSlack
  have h_eq : f x_yes = f x_no :=
    hLocal x_yes x_no hInYes hInNo hValidYes hValidNo hAgree
  have h_true : f x_yes = true := hCorrect.1 x_yes hInYes
  have h_false : f x_no = false := hCorrect.2 x_no hInNo
  rw [h_true] at h_eq
  exact absurd h_eq (by rw [h_false]; decide)

/--
One-sided value/promise consumer.

This is the certificate shape closer to the theorem-minimal route: choose one
valid YES center `x_yes`, one semantic coordinate set `S`, and prove that every
valid promise-relevant completion agreeing with `x_yes` on `S` is accepted.
Counting then manufactures a NO-completion inside the same value subcube.
-/
theorem no_one_sided_value_local_function_solves_mcsp_of_countingSlack
    {p : GapPartialMCSPParams}
    (f : Core.BitVec (partialInputLen p) → Bool)
    (x_yes : Core.BitVec (partialInputLen p))
    (S : ValueCoordinateSet p)
    (hYes : x_yes ∈ (GapPartialMCSPPromise p).Yes)
    (hValidYes : ValidEncoding p x_yes)
    (hSlack :
      Models.circuitCountBound p.n (p.sNO - 1) <
        2 ^ (Partial.tableLen p.n - S.card))
    (hStable :
      ∀ z : Core.BitVec (partialInputLen p),
        (z ∈ (GapPartialMCSPPromise p).Yes ∨ z ∈ (GapPartialMCSPPromise p).No) →
        ValidEncoding p z →
        AgreeOnValues S x_yes z →
        f z = true)
    (hCorrect : SolvesPromise (GapPartialMCSPPromise p) f) :
    False := by
  let _ := hYes
  let _ := hValidYes
  obtain ⟨x_no, hAgree, hValidNo, hInNo⟩ :=
    exists_no_completion_agreeing_on_values_of_countingSlack p x_yes S hSlack
  have h_accepts_no : f x_no = true :=
    hStable x_no (Or.inr hInNo) hValidNo hAgree
  have h_rejects_no : f x_no = false := hCorrect.2 x_no hInNo
  exact Bool.false_ne_true (h_rejects_no.symm.trans h_accepts_no)

end LowerBounds
end Pnp3
