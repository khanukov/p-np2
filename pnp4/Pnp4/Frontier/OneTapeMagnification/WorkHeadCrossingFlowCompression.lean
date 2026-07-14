import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Sym.Card
import Pnp4.Frontier.OneTapeMagnification.OnlineCanonicalCutExtraction

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Flow-normalized work-head crossing profiles

The literal all-bucket carrier from `OnlineCanonicalCutExtraction` treats its
crossing counters as independent coordinates.  Counters arising from one
actual one-tape trajectory are not independent.  This file records two exact
geometric constraints.

* Across every boundary, right crossings minus left crossings are fixed by
  the initial and final side of the work head.  From the blank initial head,
  the total crossing count is therefore twice the number of left crossings,
  plus the indicator that the final head lies to the right of the boundary.
* The full-bucket coordinates name distinct physical boundaries, so the sum
  of all their crossing counts is at most the trajectory horizon.

The first constraint gives a lossless endpoint-plus-half-counter encoding of
every geometry-consistent counter state.  Its explicit ambient cardinality is

`(T + 1) * (T / 2 + 1) ^ (b * (T / b))`,

while the sum constraint also embeds the counter portion into a stars-and-bars
carrier of size `choose (T + b * (T / b)) T`.  These are genuine
reachable-profile refinements of the independent-coordinate product, but
they are not a bounded-width online canonicalizer: they still retain one
normalized counter for every full-bucket boundary and do not include the
machine configuration needed to generate the trajectory.
-/

/-! ## Exact directional flow across one boundary -/

/-- Number of rightward crossings of `boundary` in the forward streaming
run. -/
def streamingWorkBoundaryRightCrossingCountFrom
    (machine : DeterministicMachine) (input : List Bool) :
    Configuration machine.State → Nat → Nat → Nat
  | _, 0, _ => 0
  | config, steps + 1, boundary =>
      (if config.workHead = boundary ∧
          (step machine input config).workHead = boundary + 1 then 1 else 0) +
        streamingWorkBoundaryRightCrossingCountFrom machine input
          (step machine input config) steps boundary

/-- Number of leftward crossings of `boundary` in the forward streaming
run. -/
def streamingWorkBoundaryLeftCrossingCountFrom
    (machine : DeterministicMachine) (input : List Bool) :
    Configuration machine.State → Nat → Nat → Nat
  | _, 0, _ => 0
  | config, steps + 1, boundary =>
      (if config.workHead = boundary + 1 ∧
          (step machine input config).workHead = boundary then 1 else 0) +
        streamingWorkBoundaryLeftCrossingCountFrom machine input
          (step machine input config) steps boundary

/-- One legal work-head step conserves the side indicator after accounting
for its directional flow across a fixed boundary. -/
private theorem workHead_step_boundary_flow
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) (boundary : Nat) :
    (if boundary < config.workHead then 1 else 0) +
        (if config.workHead = boundary ∧
            (step machine input config).workHead = boundary + 1 then 1 else 0) =
      (if boundary < (step machine input config).workHead then 1 else 0) +
        (if config.workHead = boundary + 1 ∧
            (step machine input config).workHead = boundary then 1 else 0) := by
  rcases workHead_step_cases machine input config with hleft | hstay | hright
  · rw [hleft]
    split_ifs <;> omega
  · rw [hstay]
    split_ifs <;> omega
  · rw [hright]
    split_ifs <;> omega

/-- Discrete conservation of work-head flow across one boundary. -/
theorem streamingWorkBoundary_directional_flow
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) (steps boundary : Nat) :
    (if boundary < config.workHead then 1 else 0) +
        streamingWorkBoundaryRightCrossingCountFrom machine input config
          steps boundary =
      (if boundary < (runFrom machine input config steps).workHead then 1 else 0) +
        streamingWorkBoundaryLeftCrossingCountFrom machine input config
          steps boundary := by
  induction steps generalizing config with
  | zero =>
      simp [streamingWorkBoundaryRightCrossingCountFrom,
        streamingWorkBoundaryLeftCrossingCountFrom]
  | succ steps ih =>
      simp only [streamingWorkBoundaryRightCrossingCountFrom,
        streamingWorkBoundaryLeftCrossingCountFrom, runFrom]
      have hstep := workHead_step_boundary_flow machine input config boundary
      have htail := ih (step machine input config)
      omega

/-- The undirected streaming count splits exactly into its rightward and
leftward parts. -/
theorem streamingWorkBoundaryCrossingCountFrom_eq_right_add_left
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) (steps boundary : Nat) :
    streamingWorkBoundaryCrossingCountFrom machine input config
        steps boundary =
      streamingWorkBoundaryRightCrossingCountFrom machine input config
          steps boundary +
        streamingWorkBoundaryLeftCrossingCountFrom machine input config
          steps boundary := by
  induction steps generalizing config with
  | zero =>
      simp [streamingWorkBoundaryCrossingCountFrom,
        streamingWorkBoundaryRightCrossingCountFrom,
        streamingWorkBoundaryLeftCrossingCountFrom]
  | succ steps ih =>
      simp only [streamingWorkBoundaryCrossingCountFrom,
        streamingWorkBoundaryRightCrossingCountFrom,
        streamingWorkBoundaryLeftCrossingCountFrom]
      rw [ih]
      rcases workHead_step_cases machine input config with hleft | hstay | hright
      · rw [hleft]
        simp only [CrossesWorkBoundary]
        split_ifs <;> omega
      · rw [hstay]
        simp only [CrossesWorkBoundary]
        split_ifs <;> omega
      · rw [hright]
        simp only [CrossesWorkBoundary]
        split_ifs <;> omega

/-- From the blank initial head, every boundary count consists of paired
return crossings plus one possible unpaired right crossing determined by the
final work-head position. -/
theorem workBoundaryCrossingCount_eq_two_mul_left_add_endpoint
    (machine : DeterministicMachine) (input : List Bool)
    (steps boundary : Nat) :
    workBoundaryCrossingCount machine input steps boundary =
      2 * streamingWorkBoundaryLeftCrossingCountFrom machine input
          (initialConfiguration machine) steps boundary +
        (if boundary < workHeadTrajectory machine input steps then 1 else 0) := by
  unfold workBoundaryCrossingCount
  rw [← streamingWorkBoundaryCrossingCountFrom_eq]
  have hsplit := streamingWorkBoundaryCrossingCountFrom_eq_right_add_left
    machine input (initialConfiguration machine) steps boundary
  have hflow := streamingWorkBoundary_directional_flow
    machine input (initialConfiguration machine) steps boundary
  change
    (if boundary < 0 then 1 else 0) +
        streamingWorkBoundaryRightCrossingCountFrom machine input
          (initialConfiguration machine) steps boundary =
      (if boundary < workHeadTrajectory machine input steps then 1 else 0) +
        streamingWorkBoundaryLeftCrossingCountFrom machine input
          (initialConfiguration machine) steps boundary at hflow
  simp only [Nat.not_lt_zero, if_false, zero_add] at hflow
  omega

/-- The parity profile of all boundary counts is the prefix cut out by the
final work-head position. -/
theorem workBoundaryCrossingCount_mod_two_eq_endpoint
    (machine : DeterministicMachine) (input : List Bool)
    (steps boundary : Nat) :
    workBoundaryCrossingCount machine input steps boundary % 2 =
      if boundary < workHeadTrajectory machine input steps then 1 else 0 := by
  rw [workBoundaryCrossingCount_eq_two_mul_left_add_endpoint]
  split_ifs <;> omega

/-- Division by two is a lossless normalization once the final work-head
position supplies the forced parity bit. -/
theorem two_mul_workBoundaryCrossingCount_div_two_add_endpoint
    (machine : DeterministicMachine) (input : List Bool)
    (steps boundary : Nat) :
    2 * (workBoundaryCrossingCount machine input steps boundary / 2) +
        (if boundary < workHeadTrajectory machine input steps then 1 else 0) =
      workBoundaryCrossingCount machine input steps boundary := by
  have hmod := workBoundaryCrossingCount_mod_two_eq_endpoint
    machine input steps boundary
  have hdiv := Nat.mod_add_div
    (workBoundaryCrossingCount machine input steps boundary) 2
  omega

/-! ## Full-bucket geometry and a normalized finite carrier -/

/-- All full-bucket coordinates of one actual pass are a subset of the
distinct physical boundaries, so their aggregate crossing count is at most
the horizon. -/
theorem sum_onePassAllFullBucketCutCounters_le_horizon
    (machine : DeterministicMachine) (input : List Bool) (T b : Nat) :
    (∑ bucket : Fin (T / b), ∑ offset : Fin b,
      (onePassAllFullBucketCutCounters machine input T b bucket offset).val) ≤
        T := by
  let crossings := actualWorkBoundaryCrossingProfile machine input T
  calc
    (∑ bucket : Fin (T / b), ∑ offset : Fin b,
        (onePassAllFullBucketCutCounters machine input T b bucket offset).val) =
        ∑ bucket : Fin (T / b), ∑ offset : Fin b,
          crossings (fullBucketBoundary bucket offset) := by
            apply Finset.sum_congr rfl
            intro bucket _
            apply Finset.sum_congr rfl
            intro offset _
            exact onePassAllFullBucketCutCounters_apply_val_eq_actual
              machine input T b bucket offset
    _ = ∑ boundary ∈ fullBucketBoundaries T b, crossings boundary := by
      rw [sum_fullBucketBoundaries_eq_coordinates crossings]
      exact (Fintype.sum_prod_type
        (fun p : Fin (T / b) × Fin b =>
          crossings (fullBucketBoundary p.1 p.2))).symm
    _ ≤ ∑ boundary : Fin T, crossings boundary :=
      sum_fullBucketBoundaries_le_total crossings
    _ ≤ T := by
      simpa [crossings, actualWorkBoundaryCrossingProfile] using
        sum_workBoundaryCrossingCount_le_steps machine input T

/-- The final blank-start work-head position, stored in its exact reachable
range. -/
def finalWorkHeadAtHorizon
    (machine : DeterministicMachine) (input : List Bool) (T : Nat) :
    Fin (T + 1) :=
  ⟨workHeadTrajectory machine input T, by
    have h := workHeadTrajectory_le_time machine input T
    omega⟩

/-- Endpoint paired with the literal all-full-bucket counter vector. -/
abbrev EndpointAllFullBucketCounterState (T b : Nat) :=
  Fin (T + 1) × AllFullBucketCounterVectors T b

/-- Exact geometry constraints used below.  The parity constraint is the
per-boundary flow law; the sum constraint is the global one-crossing-per-step
budget. -/
abbrev GeometryConsistentAllFullBucketCounterState (T b : Nat) :=
  { state : EndpointAllFullBucketCounterState T b //
    (∀ bucket : Fin (T / b), ∀ offset : Fin b,
      (state.2 bucket offset).val % 2 =
        if (fullBucketBoundary bucket offset).val < state.1.val then 1 else 0) ∧
    (∑ bucket : Fin (T / b), ∑ offset : Fin b,
      (state.2 bucket offset).val) ≤ T }

/-- The actual one-pass endpoint/counter state satisfies both exact geometry
constraints. -/
def actualGeometryConsistentAllFullBucketCounterState
    (machine : DeterministicMachine) (input : List Bool) (T b : Nat) :
    GeometryConsistentAllFullBucketCounterState T b :=
  ⟨(finalWorkHeadAtHorizon machine input T,
      onePassAllFullBucketCutCounters machine input T b), by
    constructor
    · intro bucket offset
      rw [onePassAllFullBucketCutCounters_apply_val_eq_actual]
      exact workBoundaryCrossingCount_mod_two_eq_endpoint machine input T
        (fullBucketBoundary bucket offset).val
    · exact sum_onePassAllFullBucketCutCounters_le_horizon
        machine input T b⟩

/-- Endpoint plus one half-counter for every full-bucket boundary.  This is
the finite ambient carrier used for the lossless normalization theorem. -/
abbrev EndpointHalfFullBucketCounterCarrier (T b : Nat) :=
  Fin (T + 1) ×
    (Fin (T / b) → Fin b → Fin (T / 2 + 1))

/-- Exact ambient cardinality of the endpoint-plus-half-counter carrier. -/
theorem card_endpointHalfFullBucketCounterCarrier (T b : Nat) :
    Fintype.card (EndpointHalfFullBucketCounterCarrier T b) =
      (T + 1) * (T / 2 + 1) ^ (b * (T / b)) := by
  simp only [EndpointHalfFullBucketCounterCarrier, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fun]
  rw [← Nat.pow_mul]

/-- Normalize every geometry-consistent exact counter by retaining its
quotient by two alongside the common final endpoint. -/
def normalizeGeometryConsistentAllFullBucketCounterState {T b : Nat}
    (state : GeometryConsistentAllFullBucketCounterState T b) :
    EndpointHalfFullBucketCounterCarrier T b :=
  (state.1.1, fun bucket offset =>
    ⟨(state.1.2 bucket offset).val / 2, by
      have hcounter : (state.1.2 bucket offset).val ≤ T := by
        exact Nat.le_of_lt_succ (state.1.2 bucket offset).isLt
      have hhalf : (state.1.2 bucket offset).val / 2 ≤ T / 2 :=
        Nat.div_le_div_right hcounter
      omega⟩)

/-- The normalized coordinate and endpoint reconstruct every exact
geometry-consistent counter. -/
theorem geometryConsistent_counter_eq_two_mul_normalized_add_endpoint
    {T b : Nat} (state : GeometryConsistentAllFullBucketCounterState T b)
    (bucket : Fin (T / b)) (offset : Fin b) :
    (state.1.2 bucket offset).val =
      2 *
          ((normalizeGeometryConsistentAllFullBucketCounterState state).2
            bucket offset).val +
        (if (fullBucketBoundary bucket offset).val < state.1.1.val
          then 1 else 0) := by
  have hmod := state.2.1 bucket offset
  have hdiv := Nat.mod_add_div (state.1.2 bucket offset).val 2
  change
    (state.1.2 bucket offset).val =
      2 * ((state.1.2 bucket offset).val / 2) +
        (if (fullBucketBoundary bucket offset).val < state.1.1.val
          then 1 else 0)
  omega

/-- Endpoint-plus-half-counter normalization is lossless on the exact
geometry-consistent subtype. -/
theorem normalizeGeometryConsistentAllFullBucketCounterState_injective
    {T b : Nat} :
    Function.Injective
      (normalizeGeometryConsistentAllFullBucketCounterState (T := T) (b := b)) := by
  intro left right hnormalized
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg
      (fun state : EndpointHalfFullBucketCounterCarrier T b => state.1)
      hnormalized
  · funext bucket offset
    apply Fin.ext
    have hendpoint : left.1.1.val = right.1.1.val := by
      simpa [normalizeGeometryConsistentAllFullBucketCounterState] using
        congrArg (fun state => state.1.val) hnormalized
    have hhalf :
        (left.1.2 bucket offset).val / 2 =
          (right.1.2 bucket offset).val / 2 := by
      simpa [normalizeGeometryConsistentAllFullBucketCounterState] using
        congrArg (fun state => (state.2 bucket offset).val) hnormalized
    have hleft :=
      geometryConsistent_counter_eq_two_mul_normalized_add_endpoint
        left bucket offset
    have hright :=
      geometryConsistent_counter_eq_two_mul_normalized_add_endpoint
        right bucket offset
    change
      (left.1.2 bucket offset).val =
        2 * ((left.1.2 bucket offset).val / 2) +
          (if (fullBucketBoundary bucket offset).val < left.1.1.val
            then 1 else 0) at hleft
    change
      (right.1.2 bucket offset).val =
        2 * ((right.1.2 bucket offset).val / 2) +
          (if (fullBucketBoundary bucket offset).val < right.1.1.val
            then 1 else 0) at hright
    rw [hendpoint] at hleft
    omega

/-- Explicit upper bound on the endpoint/counter states obeying the exact
one-tape flow and crossing-budget constraints. -/
theorem card_geometryConsistentAllFullBucketCounterState_le (T b : Nat) :
    Fintype.card (GeometryConsistentAllFullBucketCounterState T b) ≤
      (T + 1) * (T / 2 + 1) ^ (b * (T / b)) := by
  rw [← card_endpointHalfFullBucketCounterCarrier T b]
  exact Fintype.card_le_of_injective
    normalizeGeometryConsistentAllFullBucketCounterState
    normalizeGeometryConsistentAllFullBucketCounterState_injective

/-- The global crossing budget survives normalization: the sum of all live
half-counters is at most half the horizon. -/
theorem sum_normalizedGeometryConsistentCounters_le_half
    {T b : Nat} (state : GeometryConsistentAllFullBucketCounterState T b) :
    (∑ bucket : Fin (T / b), ∑ offset : Fin b,
      ((normalizeGeometryConsistentAllFullBucketCounterState state).2
        bucket offset).val) ≤ T / 2 := by
  rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
  have hdouble :
      2 * (∑ bucket : Fin (T / b), ∑ offset : Fin b,
        ((normalizeGeometryConsistentAllFullBucketCounterState state).2
          bucket offset).val) ≤
        ∑ bucket : Fin (T / b), ∑ offset : Fin b,
          (state.1.2 bucket offset).val := by
    calc
      2 * (∑ bucket : Fin (T / b), ∑ offset : Fin b,
          ((normalizeGeometryConsistentAllFullBucketCounterState state).2
            bucket offset).val) =
          ∑ bucket : Fin (T / b), ∑ offset : Fin b,
            2 * ((normalizeGeometryConsistentAllFullBucketCounterState state).2
              bucket offset).val := by
                simp only [Finset.mul_sum]
      _ ≤ ∑ bucket : Fin (T / b), ∑ offset : Fin b,
          (state.1.2 bucket offset).val := by
            apply Finset.sum_le_sum
            intro bucket _
            apply Finset.sum_le_sum
            intro offset _
            have hreconstruct :=
              geometryConsistent_counter_eq_two_mul_normalized_add_endpoint
                state bucket offset
            omega
  have := hdouble.trans state.2.2
  simpa [Nat.mul_comm] using this

/-! ## A stars-and-bars bound for the global crossing budget -/

/-- A finite vector of bounded counters whose total mass is at most `T`. -/
abbrev TotalBudgetCounterVector (index : Type) [Fintype index] (T : Nat) :=
  { counters : index → Fin (T + 1) //
    (∑ i : index, (counters i).val) ≤ T }

/-- Encode a total-budget vector as a multiset of exactly `T` tokens.  Tokens
`some i` record coordinate mass and `none` records unused budget. -/
noncomputable def totalBudgetCounterVectorToSym
    {index : Type} [Fintype index] [DecidableEq index] {T : Nat}
    (counters : TotalBudgetCounterVector index T) : Sym (Option index) T := by
  classical
  let used : Multiset (Option index) :=
    ∑ i : index,
      Multiset.replicate (counters.1 i).val (some i)
  let encoded := used + Multiset.replicate
    (T - ∑ i : index, (counters.1 i).val) none
  refine ⟨encoded, ?_⟩
  simp only [encoded, used, Multiset.card_add, Multiset.card_sum,
    Multiset.card_replicate]
  omega

/-- Multiplicity of every named token recovers the original coordinate, so
the slack-token encoding is injective. -/
theorem totalBudgetCounterVectorToSym_injective
    {index : Type} [Fintype index] [DecidableEq index] {T : Nat} :
    Function.Injective
      (totalBudgetCounterVectorToSym (index := index) (T := T)) := by
  classical
  intro left right hencoded
  apply Subtype.ext
  funext i
  apply Fin.ext
  have hcount := congrArg
    (fun encoded : Sym (Option index) T =>
      Multiset.count (some i) (encoded : Multiset (Option index)))
    hencoded
  simpa [totalBudgetCounterVectorToSym, Multiset.count_sum',
    Multiset.count_replicate] using hcount

/-- Generic stars-and-bars upper bound for a finite total-budget counter
vector. -/
theorem card_totalBudgetCounterVector_le_choose
    (index : Type) [Fintype index] [DecidableEq index] (T : Nat) :
    Fintype.card (TotalBudgetCounterVector index T) ≤
      Nat.choose (Fintype.card index + T) T := by
  calc
    Fintype.card (TotalBudgetCounterVector index T) ≤
        Fintype.card (Sym (Option index) T) :=
      Fintype.card_le_of_injective totalBudgetCounterVectorToSym
        totalBudgetCounterVectorToSym_injective
    _ = Nat.choose (Fintype.card index + T) T := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (Sym.card_sym_eq_choose (α := Option index) T)

/-- The all-full-bucket counter vectors obeying only the exact global
crossing budget. -/
abbrev BudgetedAllFullBucketCounterVectors (T b : Nat) :=
  { counters : AllFullBucketCounterVectors T b //
    (∑ bucket : Fin (T / b), ∑ offset : Fin b,
      (counters bucket offset).val) ≤ T }

/-- Flatten a nested full-bucket vector to its product-coordinate form. -/
def budgetedAllFullBucketCounterVectorsToTotal {T b : Nat}
    (counters : BudgetedAllFullBucketCounterVectors T b) :
    TotalBudgetCounterVector (Fin (T / b) × Fin b) T :=
  ⟨fun coordinate => counters.1 coordinate.1 coordinate.2, by
    rw [Fintype.sum_prod_type]
    exact counters.2⟩

theorem budgetedAllFullBucketCounterVectorsToTotal_injective {T b : Nat} :
    Function.Injective
      (budgetedAllFullBucketCounterVectorsToTotal (T := T) (b := b)) := by
  intro left right hflat
  apply Subtype.ext
  funext bucket offset
  have hvalues := congrArg Subtype.val hflat
  exact congrFun hvalues (bucket, offset)

/-- Stars-and-bars upper bound for all exact full-bucket counter vectors
obeying the one-tape crossing budget. -/
theorem card_budgetedAllFullBucketCounterVectors_le_choose (T b : Nat) :
    Fintype.card (BudgetedAllFullBucketCounterVectors T b) ≤
      Nat.choose (T + b * (T / b)) T := by
  calc
    Fintype.card (BudgetedAllFullBucketCounterVectors T b) ≤
        Fintype.card
          (TotalBudgetCounterVector (Fin (T / b) × Fin b) T) :=
      Fintype.card_le_of_injective
        budgetedAllFullBucketCounterVectorsToTotal
        budgetedAllFullBucketCounterVectorsToTotal_injective
    _ ≤ Nat.choose
        (Fintype.card (Fin (T / b) × Fin b) + T) T :=
      card_totalBudgetCounterVector_le_choose
        (Fin (T / b) × Fin b) T
    _ = Nat.choose (T + b * (T / b)) T := by
      simp [Fintype.card_prod, Nat.mul_comm, Nat.add_comm]

/-- The stars-and-bars carrier is bounded by one bit for each star-or-bar
position. -/
theorem choose_fullBucketCrossingBudget_le_two_pow (T b : Nat) :
    Nat.choose (T + b * (T / b)) T ≤
      2 ^ (T + b * (T / b)) := by
  by_cases hzero : T + b * (T / b) = 0
  · have hT : T = 0 := by omega
    subst T
    simp
  · exact Nat.le_of_lt
      (Nat.choose_le_two_pow (T + b * (T / b)) T
        (Nat.pos_of_ne_zero hzero))

/-- Full buckets cover at most `T` distinct boundaries, so the bit-scale
stars-and-bars carrier is at most `2^(2*T)`. -/
theorem two_pow_fullBucketCrossingBudget_le_two_pow_two_mul (T b : Nat) :
    2 ^ (T + b * (T / b)) ≤ 2 ^ (2 * T) := by
  apply Nat.pow_le_pow_right (by decide : 0 < 2)
  have hcovered : b * (T / b) ≤ T := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self T b
  omega

/-- Consequently the total-budget all-counter carrier has an explicit
linear-in-`T` logarithmic bound. -/
theorem card_budgetedAllFullBucketCounterVectors_le_two_pow_two_mul
    (T b : Nat) :
    Fintype.card (BudgetedAllFullBucketCounterVectors T b) ≤
      2 ^ (2 * T) :=
  (card_budgetedAllFullBucketCounterVectors_le_choose T b).trans
    ((choose_fullBucketCrossingBudget_le_two_pow T b).trans
      (two_pow_fullBucketCrossingBudget_le_two_pow_two_mul T b))

/-- Counter profiles satisfying both the global budget and the existence of
one endpoint inducing every coordinate parity. -/
abbrev GeometryConsistentAllFullBucketCounterVector (T b : Nat) :=
  { counters : AllFullBucketCounterVectors T b //
    (∑ bucket : Fin (T / b), ∑ offset : Fin b,
      (counters bucket offset).val) ≤ T ∧
    ∃ endpoint : Fin (T + 1),
      ∀ bucket : Fin (T / b), ∀ offset : Fin b,
        (counters bucket offset).val % 2 =
          if (fullBucketBoundary bucket offset).val < endpoint.val
            then 1 else 0 }

/-- Forgetting parity embeds a geometry-consistent profile into the global
budget carrier. -/
def geometryConsistentCounterVectorToBudgeted {T b : Nat}
    (counters : GeometryConsistentAllFullBucketCounterVector T b) :
    BudgetedAllFullBucketCounterVectors T b :=
  ⟨counters.1, counters.2.1⟩

theorem geometryConsistentCounterVectorToBudgeted_injective {T b : Nat} :
    Function.Injective
      (geometryConsistentCounterVectorToBudgeted (T := T) (b := b)) := by
  intro left right h
  apply Subtype.ext
  exact congrArg
    (fun counters : BudgetedAllFullBucketCounterVectors T b => counters.1) h

/-- Select one witnessing endpoint and attach it to a geometry-consistent
counter profile.  The selected endpoint need not be unique in a final
uncovered remainder; injectivity comes from retaining the whole profile. -/
noncomputable def geometryConsistentCounterVectorToEndpointState {T b : Nat}
    (counters : GeometryConsistentAllFullBucketCounterVector T b) :
    GeometryConsistentAllFullBucketCounterState T b := by
  classical
  let endpoint := Classical.choose counters.2.2
  refine ⟨(endpoint, counters.1), ?_⟩
  exact ⟨Classical.choose_spec counters.2.2, counters.2.1⟩

theorem geometryConsistentCounterVectorToEndpointState_injective
    {T b : Nat} :
    Function.Injective
      (geometryConsistentCounterVectorToEndpointState (T := T) (b := b)) := by
  intro left right h
  apply Subtype.ext
  have hstates := congrArg Subtype.val h
  exact congrArg Prod.snd hstates

/-- Combined reachable-profile bound: flow parity supplies the
endpoint-plus-half-counter term, while the total crossing budget supplies
the stars-and-bars term. -/
theorem card_geometryConsistentAllFullBucketCounterVector_le_min
    (T b : Nat) :
    Fintype.card (GeometryConsistentAllFullBucketCounterVector T b) ≤
      min (Nat.choose (T + b * (T / b)) T)
        ((T + 1) * (T / 2 + 1) ^ (b * (T / b))) := by
  apply Nat.le_min.mpr
  constructor
  · exact
      (Fintype.card_le_of_injective geometryConsistentCounterVectorToBudgeted
        geometryConsistentCounterVectorToBudgeted_injective).trans
        (card_budgetedAllFullBucketCounterVectors_le_choose T b)
  · exact
      (Fintype.card_le_of_injective
        geometryConsistentCounterVectorToEndpointState
        geometryConsistentCounterVectorToEndpointState_injective).trans
        (card_geometryConsistentAllFullBucketCounterState_le T b)

/-- In particular, the exact geometry-consistent reachable-profile carrier
has at most `2^(2*T)` states, independently of the bucket scale.  This is a
carrier-size statement, not an online transition implementation. -/
theorem card_geometryConsistentAllFullBucketCounterVector_le_two_pow_two_mul
    (T b : Nat) :
    Fintype.card (GeometryConsistentAllFullBucketCounterVector T b) ≤
      2 ^ (2 * T) :=
  (Fintype.card_le_of_injective geometryConsistentCounterVectorToBudgeted
    geometryConsistentCounterVectorToBudgeted_injective).trans
    (card_budgetedAllFullBucketCounterVectors_le_two_pow_two_mul T b)

/-- The actual all-bucket one-pass counter vector belongs to the combined
geometry-consistent profile carrier. -/
def actualGeometryConsistentAllFullBucketCounterVector
    (machine : DeterministicMachine) (input : List Bool) (T b : Nat) :
    GeometryConsistentAllFullBucketCounterVector T b :=
  ⟨onePassAllFullBucketCutCounters machine input T b, by
    constructor
    · exact sum_onePassAllFullBucketCutCounters_le_horizon
        machine input T b
    · refine ⟨finalWorkHeadAtHorizon machine input T, ?_⟩
      intro bucket offset
      rw [onePassAllFullBucketCutCounters_apply_val_eq_actual]
      exact workBoundaryCrossingCount_mod_two_eq_endpoint machine input T
        (fullBucketBoundary bucket offset).val⟩

end OneTapeMagnification
end Frontier
end Pnp4
