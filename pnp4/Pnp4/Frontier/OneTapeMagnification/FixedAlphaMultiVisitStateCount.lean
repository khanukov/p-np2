import Mathlib.Data.Nat.Log
import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.FullBlockValidatorStateCount
import Pnp4.Frontier.OneTapeMagnification.PaddedLocalReplayState
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedVisitStreamingVerifier
import Pnp4.Frontier.OneTapeMagnification.InPlaceTwoWindowBlockFold

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Homogeneous carrier for the full fixed-alpha multi-visit validator

The single-visit phase already has a finite streaming carrier.  Padding its
slab to width `2 * b` makes that carrier independent of the advertised
block.  A full block-ordered traversal additionally needs a block cursor, a
visit cursor, and the rolling two-window state (two Boolean flags and `2 * b`
bounded crossing counters).

This file packages precisely those fields in one homogeneous ambient carrier
and computes its exact cardinality, including one global reject sink.  It
also gives an explicit base-two bit budget using `Nat.clog 2`; this is the
finite arithmetic statement behind the informal
`2 ^ O(b * log (T * q))` estimate.

The carrier and its cardinality are not by themselves a transition system.
In particular, the remaining compiler obligation is to thread the
single-visit verifier through every visit and block while preserving the
fixed/adaptive read-once query order.
-/

/-- Product presentation of the rolling state used by the actual in-place
two-window fold. -/
def inPlaceTwoWindowFoldStateEquiv (H b : Nat) :
    InPlaceTwoWindowFoldState H b ≃
      Bool × Bool × BoundedCrossingCounterVector H (b + b) where
  toFun state :=
    (state.allBlockVisitsValid, state.allClosedCutsValid, state.counters)
  invFun fields :=
    { allBlockVisitsValid := fields.1
      allClosedCutsValid := fields.2.1
      counters := fields.2.2 }
  left_inv state := by cases state; rfl
  right_inv fields := by rcases fields with ⟨left, right, counters⟩; rfl

/-- Explicit finite instance for the rolling fold state.  It is kept as a
named definition rather than a global instance so downstream modules can
control instance synthesis. -/
def inPlaceTwoWindowFoldStateFintype (H b : Nat) :
    Fintype (InPlaceTwoWindowFoldState H b) :=
  Fintype.ofEquiv
    (Bool × Bool × BoundedCrossingCounterVector H (b + b))
    (inPlaceTwoWindowFoldStateEquiv H b).symm

/-- The rolling flags and two counter windows have exactly
`4 * (H + 1)^(2*b)` states. -/
theorem card_inPlaceTwoWindowFoldState (H b : Nat) :
    letI := inPlaceTwoWindowFoldStateFintype H b
    Fintype.card (InPlaceTwoWindowFoldState H b) =
      4 * (H + 1) ^ (2 * b) := by
  letI := inPlaceTwoWindowFoldStateFintype H b
  rw [Fintype.card_congr (inPlaceTwoWindowFoldStateEquiv H b)]
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fun,
    Fintype.card_fin]
  rw [show b + b = 2 * b by omega]
  ring

/-- Running-only presentation obtained by extending the earlier full-block
carrier with the three traversal cursors and the two persistent fold flags.
This is the literal product requested by the local replay architecture; the
richer phase carrier below additionally retains completed endpoints and
explicit local failure modes. -/
abbrev FixedAlphaMultiVisitRunningLiveState
    (machine : DeterministicMachine) (H b : Nat) :=
  Fin (H / b + 1) ×
    Fin (H + 1) ×
      Fin (H + 1) ×
        Bool × Bool × CachedFullBlockReplayState machine H b

abbrev FixedAlphaMultiVisitRunningValidatorState
    (machine : DeterministicMachine) (H b : Nat) :=
  Unit ⊕ FixedAlphaMultiVisitRunningLiveState machine H b

/-- Exact cardinality of the running homogeneous carrier.  The two
`Fin (H + 1)` factors are respectively the visit and within-visit phase
cursors. -/
theorem card_fixedAlphaMultiVisitRunningValidatorState
    (machine : DeterministicMachine) (H b : Nat) :
    letI := (cachedInputMachine machine).stateFintype
    Fintype.card
        (FixedAlphaMultiVisitRunningValidatorState machine H b) =
      1 +
        (H / b + 1) * (H + 1) * (H + 1) * 4 *
          (((1 + 3 *
                @Fintype.card machine.State machine.stateFintype) *
              (H + 1) * (2 * b) * 2 ^ (2 * b)) *
            (H + 1) ^ (2 * b)) := by
  letI := (cachedInputMachine machine).stateFintype
  change Fintype.card
      (Unit ⊕
        (Fin (H / b + 1) ×
          Fin (H + 1) ×
            Fin (H + 1) ×
              Bool × Bool × CachedFullBlockReplayState machine H b)) = _
  rw [Fintype.card_sum, Fintype.card_unit, Fintype.card_prod,
    Fintype.card_prod, Fintype.card_prod, Fintype.card_prod,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    Fintype.card_bool,
    card_cachedFullBlockReplayState]
  ring

/-- Pad every width-dependent payload of the streaming phase.  Failure tags
and the bounded remaining-step index do not depend on the slab width. -/
def padFiniteCachedVisitStreamingState
    {State : Type} {H w W : Nat} (h : w ≤ W) :
    FiniteCachedVisitStreamingState State H w →
      FiniteCachedVisitStreamingState State H W
  | .running remaining live =>
      .running remaining (padLocalReplayState h live)
  | .completed final =>
      .completed (padFiniteLocalFinalState h final)
  | .rejected failure => .rejected failure

theorem padFiniteLocalFinalState_injective_for_streaming
    {State : Type} {H w W : Nat} (h : w ≤ W) :
    Function.Injective
      (padFiniteLocalFinalState (State := State) (H := H) h) := by
  intro left right heq
  cases left with
  | mk leftControl leftInput leftWork leftSlab =>
      cases right with
      | mk rightControl rightInput rightWork rightSlab =>
          simp only [padFiniteLocalFinalState,
            FiniteLocalFinalState.mk.injEq] at heq ⊢
          exact ⟨heq.1, heq.2.1, heq.2.2.1,
            padWorkSlab_injective h heq.2.2.2⟩

/-- Phase padding is lossless, so the shorter advertised-block phase embeds
in the homogeneous `2*b` phase carrier. -/
theorem padFiniteCachedVisitStreamingState_injective
    {State : Type} {H w W : Nat} (h : w ≤ W) :
    Function.Injective
      (padFiniteCachedVisitStreamingState (State := State) (H := H) h) := by
  intro left right heq
  cases left with
  | running leftRemaining leftLive =>
      cases right with
      | running rightRemaining rightLive =>
          simp only [padFiniteCachedVisitStreamingState,
            FiniteCachedVisitStreamingState.running.injEq] at heq ⊢
          exact ⟨heq.1, padLocalReplayState_injective h heq.2⟩
      | completed rightFinal => cases heq
      | rejected rightFailure => cases heq
  | completed leftFinal =>
      cases right with
      | running rightRemaining rightLive => cases heq
      | completed rightFinal =>
          simp only [padFiniteCachedVisitStreamingState,
            FiniteCachedVisitStreamingState.completed.injEq] at heq ⊢
          exact padFiniteLocalFinalState_injective_for_streaming h heq
      | rejected rightFailure => cases heq
  | rejected leftFailure =>
      cases right with
      | running rightRemaining rightLive => cases heq
      | completed rightFinal => cases heq
      | rejected rightFailure =>
          simpa only [padFiniteCachedVisitStreamingState,
            FiniteCachedVisitStreamingState.rejected.injEq] using heq

/-- Pad the phase carrier of a named advertised block to the uniform width
`2*b`. -/
def padAdvertisedFiniteCachedVisitStreamingState
    {State : Type} {T b H : Nat} (hb : 0 < b)
    (offsets : CanonicalCutOffsets T b) (block : Fin (T / b + 1)) :
    FiniteCachedVisitStreamingState State H
        (advertisedBlockWidth offsets block) →
      FiniteCachedVisitStreamingState State H (2 * b) :=
  padFiniteCachedVisitStreamingState
    (advertisedBlockWidth_le_two_mul hb offsets block)

theorem padAdvertisedFiniteCachedVisitStreamingState_injective
    {State : Type} {T b H : Nat} (hb : 0 < b)
    (offsets : CanonicalCutOffsets T b) (block : Fin (T / b + 1)) :
    Function.Injective
      (padAdvertisedFiniteCachedVisitStreamingState
        (State := State) (H := H) hb offsets block) :=
  padFiniteCachedVisitStreamingState_injective
    (advertisedBlockWidth_le_two_mul hb offsets block)

/-- Cardinal version of the explicit lossless padding map. -/
theorem advertisedFiniteCachedVisitStreamingState_card_le_padded
    (State : Type) [Fintype State] {T b : Nat} (H : Nat) (hb : 0 < b)
    (offsets : CanonicalCutOffsets T b) (block : Fin (T / b + 1)) :
    Fintype.card
        (FiniteCachedVisitStreamingState State H
          (advertisedBlockWidth offsets block)) ≤
      Fintype.card
        (FiniteCachedVisitStreamingState State H (2 * b)) := by
  exact Fintype.card_le_of_injective
    (padAdvertisedFiniteCachedVisitStreamingState
      (State := State) (H := H) hb offsets block)
    (padAdvertisedFiniteCachedVisitStreamingState_injective
      hb offsets block)

/-- One homogeneous live state for a block-ordered fixed-alpha traversal.

* `Fin (H / b + 1)` is the advertised-block cursor;
* `Fin (H + 1)` is a uniform visit cursor (including an end position);
* `FiniteCachedVisitStreamingState ... H (2*b)` is the padded single-visit
  phase, including its bounded remaining-step index and retained endpoint;
* `InPlaceTwoWindowFoldState H b` contains the rolling flags and counters.
-/
abbrev FixedAlphaMultiVisitLiveState
    (machine : DeterministicMachine) (H b : Nat) :=
  Fin (H / b + 1) ×
    Fin (H + 1) ×
      FiniteCachedVisitStreamingState
        (cachedInputMachine machine).State H (2 * b) ×
        InPlaceTwoWindowFoldState H b

/-- Add one permanent global reject sink. -/
abbrev FixedAlphaMultiVisitValidatorState
    (machine : DeterministicMachine) (H b : Nat) :=
  Unit ⊕ FixedAlphaMultiVisitLiveState machine H b

/-- Exact size of the padded phase carrier used in the global formula. -/
def cachedPaddedVisitPhaseCard
    (machine : DeterministicMachine) (H b : Nat) : Nat :=
  (H + 1) *
      ((1 + 3 * @Fintype.card machine.State machine.stateFintype) *
        (H + 1) * (2 * b) * 2 ^ (2 * b)) +
    (1 + 3 * @Fintype.card machine.State machine.stateFintype) *
      (H + 1) * (H + 1) * 2 ^ (2 * b) + 6

/-- The phase formula can be factored into one slab/cached-control term plus
the six explicit local failure modes. -/
theorem cachedPaddedVisitPhaseCard_eq_factored
    (machine : DeterministicMachine) (H b : Nat) :
    cachedPaddedVisitPhaseCard machine H b =
      (1 + 3 * @Fintype.card machine.State machine.stateFintype) *
          (H + 1) * (H + 1) * (2 * b + 1) * 2 ^ (2 * b) + 6 := by
  unfold cachedPaddedVisitPhaseCard
  ring

/-- Exact cardinality of the homogeneous multi-visit carrier, including the
global reject sink. -/
theorem card_fixedAlphaMultiVisitValidatorState
    (machine : DeterministicMachine) (H b : Nat) :
    letI := (cachedInputMachine machine).stateFintype
    letI := inPlaceTwoWindowFoldStateFintype H b
    Fintype.card (FixedAlphaMultiVisitValidatorState machine H b) =
      1 +
        (H / b + 1) * (H + 1) *
          cachedPaddedVisitPhaseCard machine H b *
            (4 * (H + 1) ^ (2 * b)) := by
  letI := (cachedInputMachine machine).stateFintype
  letI := inPlaceTwoWindowFoldStateFintype H b
  change Fintype.card
      (Unit ⊕
        (Fin (H / b + 1) ×
          Fin (H + 1) ×
            FiniteCachedVisitStreamingState
              (cachedInputMachine machine).State H (2 * b) ×
              InPlaceTwoWindowFoldState H b)) = _
  rw [Fintype.card_sum, Fintype.card_unit, Fintype.card_prod,
    Fintype.card_prod, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin,
    card_cachedFiniteVisitStreamingState machine H (2 * b),
    card_inPlaceTwoWindowFoldState]
  unfold cachedPaddedVisitPhaseCard
  ring

/-- A short helper for composing independently encoded finite factors. -/
theorem mul_le_two_pow_add
    {left right leftBits rightBits : Nat}
    (hleft : left ≤ 2 ^ leftBits)
    (hright : right ≤ 2 ^ rightBits) :
    left * right ≤ 2 ^ (leftBits + rightBits) := by
  calc
    left * right ≤ 2 ^ leftBits * 2 ^ rightBits :=
      Nat.mul_le_mul hleft hright
    _ = 2 ^ (leftBits + rightBits) := by rw [pow_add]

/-- Every positive-size finite factor fits in its ceiling-logarithmic number
of bits.  The statement is also valid at zero. -/
theorem le_two_pow_clog_two (size : Nat) :
    size ≤ 2 ^ Nat.clog 2 size :=
  Nat.le_pow_clog (by decide) size

/-- Explicit bit budget for the factored padded single-visit phase. -/
def cachedPaddedVisitPhaseBitBudget
    (machine : DeterministicMachine) (H b : Nat) : Nat :=
  3 +
    ((((Nat.clog 2
          (1 + 3 * @Fintype.card machine.State machine.stateFintype) +
        Nat.clog 2 (H + 1)) +
      Nat.clog 2 (H + 1)) +
      Nat.clog 2 (2 * b + 1)) +
      2 * b)

/-- The padded single-visit phase fits in the displayed explicit bit budget.
The leading three bits absorb the `+ 6` failure constructors. -/
theorem cachedPaddedVisitPhaseCard_le_two_pow
    (machine : DeterministicMachine) (H b : Nat) :
    cachedPaddedVisitPhaseCard machine H b ≤
      2 ^ cachedPaddedVisitPhaseBitBudget machine H b := by
  let controlCard :=
    1 + 3 * @Fintype.card machine.State machine.stateFintype
  let core :=
    controlCard * (H + 1) * (H + 1) * (2 * b + 1) * 2 ^ (2 * b)
  have hcontrol : controlCard ≤ 2 ^ Nat.clog 2 controlCard :=
    le_two_pow_clog_two controlCard
  have hhorizon : H + 1 ≤ 2 ^ Nat.clog 2 (H + 1) :=
    le_two_pow_clog_two (H + 1)
  have hwidth : 2 * b + 1 ≤ 2 ^ Nat.clog 2 (2 * b + 1) :=
    le_two_pow_clog_two (2 * b + 1)
  have hcore1 := mul_le_two_pow_add hcontrol hhorizon
  have hcore2 := mul_le_two_pow_add hcore1 hhorizon
  have hcore3 := mul_le_two_pow_add hcore2 hwidth
  have hcore : core ≤
      2 ^ ((((Nat.clog 2 controlCard + Nat.clog 2 (H + 1)) +
        Nat.clog 2 (H + 1)) + Nat.clog 2 (2 * b + 1)) + 2 * b) := by
    exact mul_le_two_pow_add hcore3 (le_refl (2 ^ (2 * b)))
  have hcorePositive : 0 < core := by
    dsimp [core, controlCard]
    positivity
  have hcorePos : 1 ≤ core := hcorePositive
  rw [cachedPaddedVisitPhaseCard_eq_factored]
  change core + 6 ≤ 2 ^ cachedPaddedVisitPhaseBitBudget machine H b
  calc
    core + 6 ≤ 8 * core := by omega
    _ ≤ 2 ^ (3 +
        ((((Nat.clog 2 controlCard + Nat.clog 2 (H + 1)) +
          Nat.clog 2 (H + 1)) + Nat.clog 2 (2 * b + 1)) + 2 * b)) := by
      exact mul_le_two_pow_add (by decide : 8 ≤ 2 ^ 3) hcore
    _ = 2 ^ cachedPaddedVisitPhaseBitBudget machine H b := by
      rfl

/-- Explicit bit budget for the rolling two-window flags and counters. -/
def inPlaceTwoWindowFoldBitBudget (H b : Nat) : Nat :=
  2 + Nat.clog 2 (H + 1) * (2 * b)

theorem inPlaceTwoWindowFoldCard_le_two_pow (H b : Nat) :
    4 * (H + 1) ^ (2 * b) ≤
      2 ^ inPlaceTwoWindowFoldBitBudget H b := by
  have hhorizon : H + 1 ≤ 2 ^ Nat.clog 2 (H + 1) :=
    le_two_pow_clog_two (H + 1)
  have hpow : (H + 1) ^ (2 * b) ≤
      2 ^ (Nat.clog 2 (H + 1) * (2 * b)) := by
    calc
      (H + 1) ^ (2 * b) ≤
          (2 ^ Nat.clog 2 (H + 1)) ^ (2 * b) :=
        Nat.pow_le_pow_left hhorizon (2 * b)
      _ = 2 ^ (Nat.clog 2 (H + 1) * (2 * b)) := by
        exact (Nat.pow_mul 2 (Nat.clog 2 (H + 1)) (2 * b)).symm
  exact mul_le_two_pow_add (by decide : 4 ≤ 2 ^ 2) hpow

/-- Total bit budget for block cursor, visit cursor, padded phase, rolling
state, and one extra bit for the global reject sink. -/
def fixedAlphaMultiVisitValidatorBitBudget
    (machine : DeterministicMachine) (H b : Nat) : Nat :=
  ((((Nat.clog 2 (H / b + 1) + Nat.clog 2 (H + 1)) +
      cachedPaddedVisitPhaseBitBudget machine H b) +
      inPlaceTwoWindowFoldBitBudget H b) + 1)

/-- Concrete power-of-two upper bound for the complete homogeneous carrier.
No asymptotic library is needed: every logarithmic factor is displayed as a
`Nat.clog 2`, and every `b`-fold counter vector contributes its explicit
multiple of that ceiling logarithm. -/
theorem card_fixedAlphaMultiVisitValidatorState_le_two_pow
    (machine : DeterministicMachine) (H b : Nat) :
    letI := (cachedInputMachine machine).stateFintype
    letI := inPlaceTwoWindowFoldStateFintype H b
    Fintype.card (FixedAlphaMultiVisitValidatorState machine H b) ≤
      2 ^ fixedAlphaMultiVisitValidatorBitBudget machine H b := by
  letI := (cachedInputMachine machine).stateFintype
  letI := inPlaceTwoWindowFoldStateFintype H b
  rw [card_fixedAlphaMultiVisitValidatorState]
  let liveCard :=
    (H / b + 1) * (H + 1) *
      cachedPaddedVisitPhaseCard machine H b *
        (4 * (H + 1) ^ (2 * b))
  have hblocks : H / b + 1 ≤ 2 ^ Nat.clog 2 (H / b + 1) :=
    le_two_pow_clog_two (H / b + 1)
  have hvisits : H + 1 ≤ 2 ^ Nat.clog 2 (H + 1) :=
    le_two_pow_clog_two (H + 1)
  have hlive1 := mul_le_two_pow_add hblocks hvisits
  have hlive2 := mul_le_two_pow_add hlive1
    (cachedPaddedVisitPhaseCard_le_two_pow machine H b)
  have hlive : liveCard ≤
      2 ^ (((Nat.clog 2 (H / b + 1) + Nat.clog 2 (H + 1)) +
        cachedPaddedVisitPhaseBitBudget machine H b) +
        inPlaceTwoWindowFoldBitBudget H b) := by
    exact mul_le_two_pow_add hlive2
      (inPlaceTwoWindowFoldCard_le_two_pow H b)
  change 1 + liveCard ≤ _
  calc
    1 + liveCard ≤
        2 ^ (((Nat.clog 2 (H / b + 1) + Nat.clog 2 (H + 1)) +
            cachedPaddedVisitPhaseBitBudget machine H b) +
            inPlaceTwoWindowFoldBitBudget H b) +
          2 ^ (((Nat.clog 2 (H / b + 1) + Nat.clog 2 (H + 1)) +
            cachedPaddedVisitPhaseBitBudget machine H b) +
            inPlaceTwoWindowFoldBitBudget H b) := by
      exact Nat.add_le_add
        (Nat.one_le_pow _ 2 (by decide)) hlive
    _ = 2 ^ fixedAlphaMultiVisitValidatorBitBudget machine H b := by
      unfold fixedAlphaMultiVisitValidatorBitBudget
      rw [pow_succ]
      ring

end OneTapeMagnification
end Frontier
end Pnp4
