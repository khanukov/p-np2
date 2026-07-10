import Pnp4.Frontier.OneTapeMagnification.Counting
import Mathlib.Tactic

/-!
# Fixed-bipartition sparsity for exact MCSP slices

For a finite set `E \subseteq A \times B`, consider the Boolean membership row
seen after fixing the `A` coordinate.  Every nonempty row is witnessed by at
least one pair in `E`, while all unwitnessed coordinates share the single
empty row.  Consequently there are at most `|E| + 1` distinct rows.

The MCSP instantiation below is deliberately finite and non-asymptotic.  It
defines the semantic exact-MCSP YES-set by filtering on `HasCircuit`, proves
that this exact set is contained in `Counting.easyTablesByCode`, and only then
uses the codec cardinality bound.  The code-image superset is never identified
with the semantic YES-set.

This module controls membership matrices for one fixed bipartition.  It does
not formalize communication protocols, crossing sequences, a one-tape time
lower bound, or a no-go theorem for adaptive or many-cut arguments.
-/

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification
namespace CommunicationSparsity

open StreamingMagnification
open StreamingMagnification.TotalSearch

section SparseRows

variable {A B : Type*}
variable [Fintype A] [Fintype B]
variable [DecidableEq A] [DecidableEq B]

/-- The Boolean membership row obtained by fixing the left coordinate. -/
def membershipRow (E : Finset (A × B)) (a : A) : B → Bool :=
  fun b => decide ((a, b) ∈ E)

/-- All distinct membership rows of a finite bipartite relation. -/
def membershipRows (E : Finset (A × B)) : Finset (B → Bool) :=
  Finset.univ.image (membershipRow E)

/-- Left coordinates that occur in at least one pair of `E`. -/
def rowSupport (E : Finset (A × B)) : Finset A :=
  E.image Prod.fst

omit [Fintype A] [Fintype B] in
theorem membershipRow_eq_false_of_not_mem_rowSupport
    (E : Finset (A × B)) (a : A)
    (ha : a ∉ rowSupport E) :
    membershipRow E a = fun _ => false := by
  funext b
  simp only [membershipRow]
  apply decide_eq_false
  intro hab
  apply ha
  exact Finset.mem_image.mpr ⟨(a, b), hab, rfl⟩

/--
A finite relation has at most one empty row plus one row per relation member.

The bound is intentionally about distinct rows, not about a protocol or a
Turing-machine transcript.  Those interpretations require separate model
lemmas.
-/
theorem sparse_membership_row_count_le_card_add_one
    (E : Finset (A × B)) :
    (membershipRows E).card ≤ E.card + 1 := by
  let emptyRow : B → Bool := fun _ => false
  have hRows :
      membershipRows E ⊆
        (rowSupport E).image (membershipRow E) ∪ {emptyRow} := by
    intro row hrow
    rcases Finset.mem_image.mp hrow with ⟨a, _haUniv, rfl⟩
    by_cases ha : a ∈ rowSupport E
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    · apply Finset.mem_union_right
      have hEmpty : membershipRow E a = emptyRow :=
        membershipRow_eq_false_of_not_mem_rowSupport E a ha
      simp [hEmpty]
  calc
    (membershipRows E).card ≤
        ((rowSupport E).image (membershipRow E) ∪ {emptyRow}).card :=
      Finset.card_le_card hRows
    _ ≤ ((rowSupport E).image (membershipRow E)).card +
        ({emptyRow} : Finset (B → Bool)).card :=
      Finset.card_union_le
        ((rowSupport E).image (membershipRow E)) {emptyRow}
    _ = ((rowSupport E).image (membershipRow E)).card + 1 := by simp
    _ ≤ (rowSupport E).card + 1 :=
      Nat.add_le_add_right Finset.card_image_le 1
    _ ≤ E.card + 1 :=
      Nat.add_le_add_right Finset.card_image_le 1

/-- The direct cardinality consequence of a fixed-length description bound. -/
theorem sparse_membership_row_count_le_two_pow_add_one
    (E : Finset (A × B)) (descriptionBits : Nat)
    (hCard : E.card ≤ 2 ^ descriptionBits) :
    (membershipRows E).card ≤ 2 ^ descriptionBits + 1 :=
  le_trans (sparse_membership_row_count_le_card_add_one E)
    (Nat.add_le_add_right hCard 1)

/-- A power-of-two relaxation convenient for encoding a row identifier. -/
theorem sparse_membership_row_count_le_two_pow_succ
    (E : Finset (A × B)) (descriptionBits : Nat)
    (hCard : E.card ≤ 2 ^ descriptionBits) :
    (membershipRows E).card ≤ 2 ^ (descriptionBits + 1) := by
  have hPow : 1 ≤ 2 ^ descriptionBits :=
    Nat.one_le_pow descriptionBits 2 (by decide)
  calc
    (membershipRows E).card ≤ 2 ^ descriptionBits + 1 :=
      sparse_membership_row_count_le_two_pow_add_one E descriptionBits hCard
    _ ≤ 2 ^ (descriptionBits + 1) := by
      rw [pow_succ]
      omega

end SparseRows

section FixedSplit

variable {A B X : Type*}
variable [Fintype A] [Fintype B] [Fintype X]
variable [DecidableEq A] [DecidableEq B] [DecidableEq X]

/-- Transport a finite set through one fixed bipartition equivalence. -/
def splitPairs (split : A × B ≃ X) (E : Finset X) :
    Finset (A × B) :=
  E.map split.symm.toEmbedding

omit [Fintype A] [Fintype B] [Fintype X]
  [DecidableEq A] [DecidableEq B] [DecidableEq X] in
@[simp]
theorem mem_splitPairs
    (split : A × B ≃ X) (E : Finset X) (pair : A × B) :
    pair ∈ splitPairs split E ↔ split pair ∈ E := by
  simp [splitPairs]

omit [Fintype A] [Fintype B] [Fintype X]
  [DecidableEq A] [DecidableEq B] [DecidableEq X] in
@[simp]
theorem card_splitPairs
    (split : A × B ≃ X) (E : Finset X) :
    (splitPairs split E).card = E.card := by
  simp [splitPairs]

/-- Distinct membership rows after transporting `E` through a fixed split. -/
def splitMembershipRows (split : A × B ≃ X) (E : Finset X) :
    Finset (B → Bool) :=
  membershipRows (splitPairs split E)

omit [Fintype X] [DecidableEq X] in
theorem split_membership_row_count_le_card_add_one
    (split : A × B ≃ X) (E : Finset X) :
    (splitMembershipRows split E).card ≤ E.card + 1 := by
  simpa [splitMembershipRows] using
    (sparse_membership_row_count_le_card_add_one (splitPairs split E))

end FixedSplit

/-! ## Exact standard-DAG MCSP instantiation -/

/--
The semantic exact-MCSP YES-set at one finite truth-table length.

This definition is noncomputable only because it uses classical filtering of
the proposition `HasCircuit`.  Its membership theorem below is exact.
-/
noncomputable def semanticEasyTables (n threshold : Nat) :
    Finset (TruthTable n) := by
  classical
  exact (Finset.univ : Finset (TruthTable n)).filter (HasCircuit n threshold)

@[simp]
theorem mem_semanticEasyTables
    {n threshold : Nat} {table : TruthTable n} :
    table ∈ semanticEasyTables n threshold ↔
      HasCircuit n threshold table := by
  classical
  simp [semanticEasyTables]

/-- The exact semantic YES-set is contained in the codec-image superset. -/
theorem semanticEasyTables_subset_easyTablesByCode
    (n threshold : Nat) :
    semanticEasyTables n threshold ⊆
      Counting.easyTablesByCode n threshold := by
  intro table htable
  exact Counting.mem_easyTablesByCode_of_hasCircuit
    (mem_semanticEasyTables.mp htable)

section MCSPFixedSplit

variable {A B : Type*}
variable [Fintype A] [Fintype B]
variable [DecidableEq A] [DecidableEq B]

/--
Any table family contained in the codec-image superset has few rows under a
fixed bipartition.  The hypothesis is explicit so that callers cannot mistake
the superset itself for exact MCSP.
-/
theorem split_rows_card_le_two_pow_codeLength_add_one_of_subset_easyTablesByCode
    {n threshold : Nat}
    (split : A × B ≃ TruthTable n)
    (E : Finset (TruthTable n))
    (hSubset : E ⊆ Counting.easyTablesByCode n threshold) :
    (splitMembershipRows split E).card ≤
      2 ^ DAGCodec.codeLength n threshold + 1 := by
  have hCard : E.card ≤ 2 ^ DAGCodec.codeLength n threshold :=
    le_trans (Finset.card_le_card hSubset)
      (Counting.card_easyTablesByCode_le n threshold)
  exact le_trans (split_membership_row_count_le_card_add_one split E)
    (Nat.add_le_add_right hCard 1)

/-- Power-of-two relaxation of the explicit-subset row bound. -/
theorem split_rows_card_le_two_pow_codeLength_succ_of_subset_easyTablesByCode
    {n threshold : Nat}
    (split : A × B ≃ TruthTable n)
    (E : Finset (TruthTable n))
    (hSubset : E ⊆ Counting.easyTablesByCode n threshold) :
    (splitMembershipRows split E).card ≤
      2 ^ (DAGCodec.codeLength n threshold + 1) := by
  have hPow : 1 ≤ 2 ^ DAGCodec.codeLength n threshold :=
    Nat.one_le_pow (DAGCodec.codeLength n threshold) 2 (by decide)
  calc
    (splitMembershipRows split E).card ≤
        2 ^ DAGCodec.codeLength n threshold + 1 :=
      split_rows_card_le_two_pow_codeLength_add_one_of_subset_easyTablesByCode
        split E hSubset
    _ ≤ 2 ^ (DAGCodec.codeLength n threshold + 1) := by
      rw [pow_succ]
      omega

/--
Exact-MCSP specialization of the fixed-bipartition row bound.

The left-hand side uses `semanticEasyTables`, whose membership is exactly
`HasCircuit`; the proof reaches the code bound only through the proved subset
relation.
-/
theorem semantic_mcsp_split_row_count_le_two_pow_codeLength_add_one
    (n threshold : Nat)
    (split : A × B ≃ TruthTable n) :
    (splitMembershipRows split (semanticEasyTables n threshold)).card ≤
      2 ^ DAGCodec.codeLength n threshold + 1 :=
  split_rows_card_le_two_pow_codeLength_add_one_of_subset_easyTablesByCode
    split (semanticEasyTables n threshold)
    (semanticEasyTables_subset_easyTablesByCode n threshold)

/-- Power-of-two relaxation of the exact semantic MCSP row bound. -/
theorem semantic_mcsp_split_row_count_le_two_pow_codeLength_succ
    (n threshold : Nat)
    (split : A × B ≃ TruthTable n) :
    (splitMembershipRows split (semanticEasyTables n threshold)).card ≤
      2 ^ (DAGCodec.codeLength n threshold + 1) :=
  split_rows_card_le_two_pow_codeLength_succ_of_subset_easyTablesByCode
    split (semanticEasyTables n threshold)
    (semanticEasyTables_subset_easyTablesByCode n threshold)

end MCSPFixedSplit

end CommunicationSparsity
end OneTapeMagnification
end Frontier
end Pnp4
