import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.UnambiguousFamilyBarrier
import Pnp4.Frontier.OneTapeMagnification.WeightedPRGSupport

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Black-box barriers for unambiguous aggregation

The canonical timed-alpha family has much more structure than an arbitrary
unambiguous family.  This file isolates two arguments that cannot exploit that
structure.

First, a deterministic adaptive tree that sees only the acceptance bit of a
chosen component must inspect every component on its all-zero path, even when
the promised bit vector has Hamming weight at most one.  Thus a canonical-alpha
selector cannot be obtained by black-box adaptive search through component
predicates.

Second, disjointness alone gives no cancellation of pseudorandomness errors.
A two-component disjoint family and a normalized generator attain the triangle
bound exactly: both component errors are `1/4`, with the same sign, while the
aggregate error is `1/2`.

Neither statement rules out a selector or cancellation identity that uses the
specific one-tape transition geometry.  Instead, they identify exactly what a
successful aggregate theorem must use beyond accepted-alpha uniqueness.
-/

/-! ## Adaptive black-box component search -/

/-- A deterministic adaptive tree whose oracle is a vector of component
acceptance bits.  The `false` child is listed first. -/
inductive ComponentQueryTree (Index : Type*) where
  | answer : Bool -> ComponentQueryTree Index
  | query : Index -> ComponentQueryTree Index -> ComponentQueryTree Index ->
      ComponentQueryTree Index

namespace ComponentQueryTree

/-- Evaluate an adaptive component-query tree. -/
def eval {Index : Type*} :
    ComponentQueryTree Index -> (Index -> Bool) -> Bool
  | .answer value, _ => value
  | .query index ifFalse ifTrue, bits =>
      if bits index then eval ifTrue bits else eval ifFalse bits

/-- Component indices queried on the all-zero execution path. -/
def zeroPathQueries {Index : Type*} : ComponentQueryTree Index -> List Index
  | .answer _ => []
  | .query index ifFalse _ => index :: zeroPathQueries ifFalse

/-- Maximum number of component queries on a root-to-leaf path. -/
def depth {Index : Type*} : ComponentQueryTree Index -> Nat
  | .answer _ => 0
  | .query _ ifFalse ifTrue => 1 + max (depth ifFalse) (depth ifTrue)

/-- The promise vector with exactly one accepting component. -/
def singletonBits {Index : Type*} [DecidableEq Index]
    (chosen : Index) : Index -> Bool :=
  fun index => decide (index = chosen)

/-- If the all-zero path omits `chosen`, the tree has exactly the same
execution on the all-zero vector and on the singleton vector at `chosen`. -/
theorem eval_zero_eq_eval_singleton_of_not_mem
    {Index : Type*} [DecidableEq Index]
    (tree : ComponentQueryTree Index) (chosen : Index)
    (homit : chosen ∉ tree.zeroPathQueries) :
    tree.eval (fun _ => false) = tree.eval (singletonBits chosen) := by
  induction tree with
  | answer value => rfl
  | query index ifFalse ifTrue ihFalse _ihTrue =>
      simp only [zeroPathQueries, List.mem_cons, not_or] at homit
      have hindex : index ≠ chosen := by
        intro heq
        exact homit.1 heq.symm
      simp [eval, singletonBits, hindex, ihFalse homit.2]

/-- Minimal correctness promise for an exact unambiguous OR: reject the zero
vector and accept every vector containing exactly one `true` bit. -/
def ComputesPromisedUnambiguousOr {Index : Type*} [DecidableEq Index]
    (tree : ComponentQueryTree Index) : Prop :=
  tree.eval (fun _ => false) = false ∧
    ∀ chosen, tree.eval (singletonBits chosen) = true

/-- Exact black-box aggregation forces every component onto the all-zero
query path. -/
theorem mem_zeroPathQueries_of_computesPromisedUnambiguousOr
    {Index : Type*} [DecidableEq Index]
    (tree : ComponentQueryTree Index)
    (hcorrect : tree.ComputesPromisedUnambiguousOr)
    (chosen : Index) :
    chosen ∈ tree.zeroPathQueries := by
  by_contra homit
  have heq := tree.eval_zero_eq_eval_singleton_of_not_mem chosen homit
  rw [hcorrect.1, hcorrect.2 chosen] at heq
  contradiction

/-- The all-zero path length is bounded by the ordinary tree depth. -/
theorem zeroPathQueries_length_le_depth
    {Index : Type*} (tree : ComponentQueryTree Index) :
    tree.zeroPathQueries.length ≤ tree.depth := by
  induction tree with
  | answer value => simp [zeroPathQueries, depth]
  | query index ifFalse ifTrue ihFalse _ihTrue =>
      simp only [zeroPathQueries, List.length_cons, depth]
      omega

/-- A deterministic adaptive black-box selector for a promised unambiguous
union has worst-case depth at least the number of components. -/
theorem card_le_depth_of_computesPromisedUnambiguousOr
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (tree : ComponentQueryTree Index)
    (hcorrect : tree.ComputesPromisedUnambiguousOr) :
    Fintype.card Index ≤ tree.depth := by
  have hsubset : (Finset.univ : Finset Index) ⊆
      tree.zeroPathQueries.toFinset := by
    intro chosen _
    exact List.mem_toFinset.mpr
      (tree.mem_zeroPathQueries_of_computesPromisedUnambiguousOr
        hcorrect chosen)
  calc
    Fintype.card Index = (Finset.univ : Finset Index).card := by simp
    _ <= tree.zeroPathQueries.toFinset.card := Finset.card_le_card hsubset
    _ <= tree.zeroPathQueries.length :=
      List.toFinset_card_le tree.zeroPathQueries
    _ <= tree.depth := tree.zeroPathQueries_length_le_depth

end ComponentQueryTree

/-! ## Sharp failure of cancellation from disjointness -/

/-- Two disjoint singleton components occupying the `false` half of a
four-point Boolean square. -/
def twoDisjointComponents (index : Bool) (input : Bool × Bool) : Bool :=
  !input.1 && decide (input.2 = index)

/-- Their coherent aggregate. -/
def twoDisjointComponentAggregate (input : Bool × Bool) : Bool :=
  !input.1

/-- A normalized two-seed generator supported on the rejected half. -/
def rejectedHalfGenerator (seed : Bool) : Bool × Bool :=
  (true, seed)

/-- Each component is literally one singleton of the four-point input space. -/
theorem twoDisjointComponents_eq_singleton (index : Bool) :
    twoDisjointComponents index =
      fun input => decide (input = (false, index)) := by
  funext input
  rcases input with ⟨first, second⟩
  cases first <;> cases second <;> cases index <;>
    decide

/-- Distinct components have disjoint accepting fibers. -/
theorem twoDisjointComponents_disjoint
    {left right : Bool} (hne : left ≠ right) (input : Bool × Bool) :
    ¬ (twoDisjointComponents left input = true ∧
      twoDisjointComponents right input = true) := by
  rintro ⟨hleft, hright⟩
  simp [twoDisjointComponents] at hleft hright
  have hleftIndex : input.2 = left := hleft.2
  have hrightIndex : input.2 = right := hright.2
  exact hne (hleftIndex.symm.trans hrightIndex)

/-- Existential aggregation is exactly the aggregate predicate. -/
theorem exists_twoDisjointComponents_eq_true_iff
    (input : Bool × Bool) :
    (∃ index, twoDisjointComponents index input = true) ↔
      twoDisjointComponentAggregate input = true := by
  rcases input with ⟨first, second⟩
  cases first <;> cases second <;>
    simp [twoDisjointComponents, twoDisjointComponentAggregate]

/-- Each component has uniform mass exactly one quarter. -/
theorem uniformPredicateAverage_twoDisjointComponents
    (index : Bool) :
    uniformPredicateAverage (twoDisjointComponents index) = (1 : Rat) / 4 := by
  rw [twoDisjointComponents_eq_singleton]
  norm_num [uniformPredicateAverage, boolIndicator, Fintype.card_prod]

/-- The rejected-half generator gives every component weighted mass zero. -/
theorem weightedGeneratorAverage_twoDisjointComponents_eq_zero
    (index : Bool) :
    weightedGeneratorAverage rejectedHalfGenerator (fun _ => (1 : Rat))
      (twoDisjointComponents index) = 0 := by
  apply weightedGeneratorAverage_eq_zero_of_support_rejects
  intro seed
  simp [rejectedHalfGenerator, twoDisjointComponents]

/-- Consequently every component error is exactly one quarter. -/
theorem twoDisjointComponent_error_eq_quarter (index : Bool) :
    abs (uniformPredicateAverage (twoDisjointComponents index) -
      weightedGeneratorAverage rejectedHalfGenerator (fun _ => (1 : Rat))
        (twoDisjointComponents index)) = (1 : Rat) / 4 := by
  rw [uniformPredicateAverage_twoDisjointComponents,
    weightedGeneratorAverage_twoDisjointComponents_eq_zero]
  norm_num

/-- The aggregate has uniform mass one half. -/
theorem uniformPredicateAverage_twoDisjointComponentAggregate :
    uniformPredicateAverage twoDisjointComponentAggregate = (1 : Rat) / 2 := by
  unfold uniformPredicateAverage
  rw [Fintype.sum_prod_type]
  norm_num [twoDisjointComponentAggregate, boolIndicator, Fintype.card_prod]

/-- The rejected-half generator also gives the aggregate mass zero. -/
theorem weightedGeneratorAverage_twoDisjointComponentAggregate_eq_zero :
    weightedGeneratorAverage rejectedHalfGenerator (fun _ => (1 : Rat))
      twoDisjointComponentAggregate = 0 := by
  apply weightedGeneratorAverage_eq_zero_of_support_rejects
  intro seed
  simp [rejectedHalfGenerator, twoDisjointComponentAggregate]

/-- The aggregate error is exactly the sum of the two component errors.
Hence disjointness supplies no cancellation beyond the triangle inequality. -/
theorem twoDisjointComponent_aggregate_error_eq_sum_errors :
    abs (uniformPredicateAverage twoDisjointComponentAggregate -
        weightedGeneratorAverage rejectedHalfGenerator (fun _ => (1 : Rat))
          twoDisjointComponentAggregate) =
      ∑ index : Bool,
        abs (uniformPredicateAverage (twoDisjointComponents index) -
          weightedGeneratorAverage rejectedHalfGenerator
            (fun _ => (1 : Rat)) (twoDisjointComponents index)) := by
  rw [uniformPredicateAverage_twoDisjointComponentAggregate,
    weightedGeneratorAverage_twoDisjointComponentAggregate_eq_zero]
  simp only [twoDisjointComponent_error_eq_quarter]
  norm_num

end OneTapeMagnification
end Frontier
end Pnp4
