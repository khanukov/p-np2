import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Models.Model_PartialMCSP
import Counting.CircuitCounting

/-!
  pnp3/Counting/ShannonCounting.lean

  Shannon counting argument: most Boolean functions require large circuits.

  Given a set of "constrained" positions (where the function must output false),
  we show that there exists a total Boolean function that:
  (1) outputs false on all constrained positions, and
  (2) cannot be computed by any circuit of size < sNO.
-/

namespace Pnp3
namespace Counting

open Core
open Models

/-!
  ### Constrained partial table
-/

/-- Partial table: false at constrained positions, undefined elsewhere. -/
def constrainedPartial {n : Nat} (constrained : Finset (Fin (Partial.tableLen n))) :
    PartialFunction n :=
  fun i => if i ∈ constrained then some false else none

/-- The undefined positions of constrainedPartial are exactly the complement. -/
lemma undefinedPositions_constrainedPartial {n : Nat}
    (constrained : Finset (Fin (Partial.tableLen n))) :
    undefinedPositions (constrainedPartial constrained) = Finset.univ \ constrained := by
  ext i
  constructor
  · intro hi
    simp only [undefinedPositions, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro hmem
    simp [constrainedPartial, hmem] at hi
  · intro hi
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hi
    simp only [undefinedPositions, Finset.mem_filter, Finset.mem_univ, true_and]
    simp [constrainedPartial, hi]

/-- The number of undefined positions in constrainedPartial. -/
lemma undefinedCount_constrainedPartial {n : Nat}
    (constrained : Finset (Fin (Partial.tableLen n))) :
    undefinedCount (constrainedPartial constrained) =
      Partial.tableLen n - constrained.card := by
  simp only [undefinedCount, undefinedPositions_constrainedPartial]
  rw [Finset.card_sdiff (Finset.subset_univ _)]
  simp

/-- A consistent total function maps constrained positions to false. -/
lemma consistentTotal_constrainedPartial_false {n : Nat}
    {constrained : Finset (Fin (Partial.tableLen n))}
    {f : TotalFunction n}
    (hf : consistentTotal (constrainedPartial constrained) f) :
    ∀ i ∈ constrained, f i = false := by
  intro i hi
  have := hf i
  simp [constrainedPartial, hi] at this
  exact this

/-!
  ### Circuit-to-table map
-/

/-- The truth table computed by a circuit. -/
noncomputable def circuitToTable {n : Nat} (C : Circuit n) : TotalFunction n :=
  fun j => Circuit.eval C (assignmentIndex_surjective j).choose

/-- If a circuit computes a truth table, the table equals circuitToTable. -/
lemma circuitComputes_eq_circuitToTable {n : Nat} (C : Circuit n)
    (g : Core.BitVec (Partial.tableLen n))
    (h : circuitComputes C g) :
    g = circuitToTable C := by
  funext j
  let x := (assignmentIndex_surjective j).choose
  have hx : assignmentIndex x = j := (assignmentIndex_surjective j).choose_spec
  -- circuitComputes: C.eval x = truthTableFunction g x = g (assignmentIndex x) = g j
  have h1 : C.eval x = g j := by
    have := h x
    -- truthTableFunction g x = g (assignmentIndex x) by rfl
    change C.eval x = g (assignmentIndex x) at this
    rw [hx] at this
    exact this
  -- circuitToTable C j = C.eval x
  show g j = Circuit.eval C x
  exact h1.symm

/-!
  ### Easy functions and consistent functions
-/

/-- The set of total functions computable by circuits of size ≤ s. -/
noncomputable def easyFunctions (n s : Nat) : Finset (TotalFunction n) :=
  (circuitsOfSizeAtMost n s).image circuitToTable

/-- The number of easy functions is at most circuitCountBound. -/
lemma card_easyFunctions_le (n s : Nat) :
    (easyFunctions n s).card ≤ circuitCountBound n s :=
  le_trans Finset.card_image_le (card_circuitsOfSizeAtMost_le n s)

/-!
  ### Raw YES-input counting

  On the full input cube `BitVec (partialInputLen p)`, a YES-input is any raw
  encoding whose decoded partial table is consistent with some easy total
  function.
-/

/-- Raw YES-inputs on the fixed slice `partialInputLen p`. -/
noncomputable def yesInputSet (p : GapPartialMCSPParams) :
    Finset (Core.BitVec (partialInputLen p)) :=
  @Finset.filter _ (fun x => gapPartialMCSP_Language p (partialInputLen p) x = true)
    (Classical.decPred _) Finset.univ

/-- Union of raw encodings consistent with some easy total function. -/
noncomputable def easyRawEncodingUnion (p : GapPartialMCSPParams) :
    Finset (Core.BitVec (partialInputLen p)) :=
  (easyFunctions p.n p.sYES).biUnion fun g =>
    rawEncodingsConsistentWithTotal g

private lemma consistentWith_circuitToTable_of_is_consistent
    {p : GapPartialMCSPParams}
    {x : Core.BitVec (partialInputLen p)}
    {C : Circuit p.n}
    (hCons : is_consistent C (decodePartial x)) :
    consistentWithTotal (decodePartial x) (circuitToTable C) := by
  intro i
  let a : Core.BitVec p.n := (assignmentIndex_surjective i).choose
  have ha : assignmentIndex a = i := (assignmentIndex_surjective i).choose_spec
  have hAt := hCons a
  rw [ha] at hAt
  cases hTi : decodePartial x i with
  | none =>
      trivial
  | some b =>
      have hEval : C.eval a = b := by
        simpa [hTi] using hAt
      show b = circuitToTable C i
      simpa [circuitToTable, a] using hEval.symm

/-- Every raw YES-input is covered by some easy total function. -/
lemma yesInputSet_subset_easyRawEncodingUnion (p : GapPartialMCSPParams) :
    yesInputSet p ⊆ easyRawEncodingUnion p := by
  classical
  intro x hx
  have hLang : gapPartialMCSP_Language p (partialInputLen p) x = true := by
    simpa [yesInputSet] using hx
  have hYes : PartialMCSP_YES p (decodePartial x) :=
    (gapPartialMCSP_language_true_iff_yes p x).1 hLang
  rcases hYes with ⟨C, hSize, hCons⟩
  have hmemC : C ∈ circuitsOfSizeAtMost p.n p.sYES :=
    mem_circuitsOfSizeAtMost C p.sYES hSize
  have hmemG : circuitToTable C ∈ easyFunctions p.n p.sYES :=
    Finset.mem_image.mpr ⟨C, hmemC, rfl⟩
  change x ∈ (easyFunctions p.n p.sYES).biUnion
      (fun g => rawEncodingsConsistentWithTotal g)
  refine Finset.mem_biUnion.mpr ⟨circuitToTable C, hmemG, ?_⟩
  simpa [rawEncodingsConsistentWithTotal] using
    (consistentWith_circuitToTable_of_is_consistent (x := x) hCons)

/-- Raw YES-inputs are bounded by easy functions times `3^(2^n)`. -/
theorem card_yesInputSet_le_easyFunctions_mul_three_pow
    (p : GapPartialMCSPParams) :
    (yesInputSet p).card ≤
      (easyFunctions p.n p.sYES).card * 3 ^ Partial.tableLen p.n := by
  classical
  have hsubset := yesInputSet_subset_easyRawEncodingUnion p
  refine le_trans (Finset.card_le_card hsubset) ?_
  calc
    (easyRawEncodingUnion p).card
        ≤ ∑ g ∈ easyFunctions p.n p.sYES,
            (rawEncodingsConsistentWithTotal g).card := by
              exact Finset.card_biUnion_le
    _ = ∑ g ∈ easyFunctions p.n p.sYES, 3 ^ Partial.tableLen p.n := by
          refine Finset.sum_congr rfl ?_
          intro g hg
          simp [card_rawEncodingsConsistentWithTotal_eq_three_pow]
    _ = (easyFunctions p.n p.sYES).card * 3 ^ Partial.tableLen p.n := by
          simp

/-- Raw YES-inputs are bounded by `circuitCountBound * 3^(2^n)`. -/
theorem card_yesInputSet_le_circuitCountBound_mul_three_pow
    (p : GapPartialMCSPParams) :
    (yesInputSet p).card ≤
      circuitCountBound p.n p.sYES * 3 ^ Partial.tableLen p.n := by
  calc
    (yesInputSet p).card
        ≤ (easyFunctions p.n p.sYES).card * 3 ^ Partial.tableLen p.n :=
          card_yesInputSet_le_easyFunctions_mul_three_pow p
    _ ≤ circuitCountBound p.n p.sYES * 3 ^ Partial.tableLen p.n := by
          exact Nat.mul_le_mul_right _ (card_easyFunctions_le p.n p.sYES)

/-- The set of consistent total functions as a Finset. -/
noncomputable def consistentFinset {n : Nat} (T : PartialFunction n) :
    Finset (TotalFunction n) :=
  @Finset.filter _ (fun f => consistentTotal T f) (Classical.decPred _) Finset.univ

/-- consistentFinset cardinality equals 2^(undefinedCount). -/
lemma card_consistentFinset {n : Nat} (T : PartialFunction n) :
    (consistentFinset T).card = 2 ^ (undefinedCount T) := by
  classical
  have : (consistentFinset T).card =
      Fintype.card {f : TotalFunction n // consistentTotal T f} := by
    unfold consistentFinset
    rw [← Fintype.card_subtype]
  rw [this, card_consistentTotal]

/-!
  ### Helper lemmas
-/

private lemma half_le_sub_of_le_half {m k : Nat} (hk : k ≤ m / 2) :
    m / 2 ≤ m - k := by omega

/-- PartialMCSP_NO via circuitComputes for total tables. -/
lemma partialMCSP_NO_iff_no_small_circuit (p : GapPartialMCSPParams)
    (g : Core.BitVec (Partial.tableLen p.n)) :
    PartialMCSP_NO p (totalTableToPartial g) ↔
      ∀ C : Circuit p.n, circuitComputes C g → p.sNO ≤ C.size := by
  simp only [PartialMCSP_NO]
  constructor
  · intro h C hcomp; exact h C ((is_consistent_total_iff C g).mpr hcomp)
  · intro h C hcons; exact h C ((is_consistent_total_iff C g).mp hcons)

/-!
  ### Main theorem
-/

/-- Shannon counting: there exists a hard function consistent with constraints. -/
theorem exists_hard_function_with_constraints
    (p : GapPartialMCSPParams)
    (constrained : Finset (Fin (Partial.tableLen p.n)))
    (h_constrained_small : constrained.card ≤ Partial.tableLen p.n / 2) :
    ∃ (g : Core.BitVec (Partial.tableLen p.n)),
      (∀ i ∈ constrained, g i = false) ∧
      PartialMCSP_NO p (totalTableToPartial g) := by
  classical
  let T := constrainedPartial constrained
  have h_undef : undefinedCount T = Partial.tableLen p.n - constrained.card :=
    undefinedCount_constrainedPartial constrained
  have h_half_le : Partial.tableLen p.n / 2 ≤ undefinedCount T := by
    rw [h_undef]; exact half_le_sub_of_le_half h_constrained_small
  have h_cons_card : (consistentFinset T).card = 2 ^ undefinedCount T :=
    card_consistentFinset T
  have h_easy_card : (easyFunctions p.n (p.sNO - 1)).card ≤ circuitCountBound p.n (p.sNO - 1) :=
    card_easyFunctions_le p.n (p.sNO - 1)
  have h_bound : (easyFunctions p.n (p.sNO - 1)).card < (consistentFinset T).card := by
    calc (easyFunctions p.n (p.sNO - 1)).card
        ≤ circuitCountBound p.n (p.sNO - 1) := h_easy_card
      _ < 2 ^ (Partial.tableLen p.n / 2) := p.circuit_bound_ok
      _ ≤ 2 ^ undefinedCount T := Nat.pow_le_pow_right (by norm_num) h_half_le
      _ = (consistentFinset T).card := h_cons_card.symm
  have h_not_sub : ¬(consistentFinset T ⊆ easyFunctions p.n (p.sNO - 1)) := by
    intro hsub
    exact absurd (Finset.card_le_card hsub) (not_le.mpr h_bound)
  rw [Finset.not_subset] at h_not_sub
  obtain ⟨f, hf_cons, hf_not_easy⟩ := h_not_sub
  have hf_consistent : consistentTotal T f := by
    unfold consistentFinset at hf_cons
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf_cons
    exact hf_cons
  have hf_false : ∀ i ∈ constrained, f i = false :=
    consistentTotal_constrainedPartial_false hf_consistent
  refine ⟨f, hf_false, ?_⟩
  rw [partialMCSP_NO_iff_no_small_circuit]
  intro C hcomp
  by_contra h_small
  push_neg at h_small
  have h_le : C.size ≤ p.sNO - 1 := by omega
  have hmem : C ∈ circuitsOfSizeAtMost p.n (p.sNO - 1) :=
    mem_circuitsOfSizeAtMost C (p.sNO - 1) h_le
  have heq := circuitComputes_eq_circuitToTable C f hcomp
  exact hf_not_easy (Finset.mem_image.mpr ⟨C, hmem, heq.symm⟩)

end Counting
end Pnp3
