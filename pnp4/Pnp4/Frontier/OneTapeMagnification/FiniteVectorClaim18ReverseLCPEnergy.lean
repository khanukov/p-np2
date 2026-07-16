import Pnp4.Frontier.OneTapeMagnification.FiniteSignedReverseLCPFourierKernel
import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredPointMassCliqueObstruction
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Signed-coordinate Claim 18 and reverse-LCP energy

The square-moment calculation underlying CLTW Claim 18 is coordinatewise.
Consequently it remains exact for a finite rational coordinate family with
arbitrary signed rational coordinate weights.  The signed form is the one
compatible with a reverse-LCP square drop: give the parent coordinate weight
`+1` and every child coordinate weight `-1`.

This file also records the precise obstruction for the structured source used
by the selector route.  At cutoff `2*m`, its first high homogeneous layer has
degree `2*m+1`, while the base source is only `(4*m+1)`-wise independent.
CLTW orthogonality at that layer would require `4*m+2`-wise independence.  At
`m = 0`, two singleton characters already witness the missing Gram zero.
-/

noncomputable section

open scoped BigOperators symmDiff

open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open FiniteBooleanOneRoundFoolingBound
open FiniteBooleanFourierEnergy
open FiniteUnambiguousFBDD
open FiniteBooleanFullIndependenceRestriction
open FiniteSignedReverseLCPTelescope
open DPTWStructuredFieldCoordinatePrimitive
open DPTWFiniteFieldKWiseSeed
open GaloisBilinearTensorBridge
open DPTWStructuredUnbiasedDualCode
open DPTWStructuredMaskRank
open DPTWStructuredPointMassCliqueObstruction

namespace FiniteVectorClaim18

/-- Exact signed-coordinate version of the square-moment identity underlying
CLTW Claim 18.  Taking every coordinate weight to be one is the finite
Euclidean/Hilbert-valued version.  Allowing negative weights is stronger and
preserves parent-minus-children energy drops before any scalarization or
triangle inequality. -/
theorem homogeneousPolynomial_restriction_signedCoordinateSecondMoment_eq
    {n k : Nat} {DSeed TSeed Coordinate : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    [Fintype Coordinate]
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool)
    (p : Rat) (weight : Coordinate -> Rat)
    (coefficient : Coordinate -> Finset (Fin n) -> Rat)
    (hDOrthogonal :
      forall alpha, alpha ∈ degreeSupports n k ->
        forall beta, beta ∈ degreeSupports n k -> alpha ≠ beta ->
          finiteAverage (fun d : DSeed =>
            character alpha (D d) * character beta (D d)) = 0)
    (hTMask : forall alpha, alpha ∈ degreeSupports n k ->
      finiteAverage (fun t : TSeed =>
        maskAllZeroIndicator alpha (T t)) = p ^ k) :
    finiteAverage (fun seed : DSeed × TSeed =>
        ∑ coordinate : Coordinate,
          weight coordinate *
            (finiteAverage (fun uniform : Fin n -> Bool =>
              homogeneousPolynomial k (coefficient coordinate)
                (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2) =
      p ^ k * ∑ coordinate : Coordinate,
        weight coordinate *
          ∑ alpha in degreeSupports n k,
            (coefficient coordinate alpha) ^ 2 := by
  rw [finiteAverage_fintype_sum]
  calc
    (∑ coordinate : Coordinate,
        finiteAverage (fun seed : DSeed × TSeed =>
          weight coordinate *
            (finiteAverage (fun uniform : Fin n -> Bool =>
              homogeneousPolynomial k (coefficient coordinate)
                (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2)) =
      ∑ coordinate : Coordinate,
        weight coordinate *
          finiteAverage (fun seed : DSeed × TSeed =>
            (finiteAverage (fun uniform : Fin n -> Bool =>
              homogeneousPolynomial k (coefficient coordinate)
                (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2) := by
          apply Finset.sum_congr rfl
          intro coordinate _
          rw [finiteAverage_const_mul]
    _ = ∑ coordinate : Coordinate,
        weight coordinate *
          (p ^ k * ∑ alpha in degreeSupports n k,
            (coefficient coordinate alpha) ^ 2) := by
          apply Finset.sum_congr rfl
          intro coordinate _
          rw [homogeneousPolynomial_restriction_secondMoment_eq
            D T p (coefficient coordinate) hDOrthogonal hTMask]
    _ = p ^ k * ∑ coordinate : Coordinate,
        weight coordinate *
          ∑ alpha in degreeSupports n k,
            (coefficient coordinate alpha) ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro coordinate _
          ring

/-- Parent-minus-children specialization.  This is the exact local form that
can be inserted into a reverse-LCP energy drop.  There is no factor depending
on the number of children. -/
theorem homogeneousPolynomial_restriction_squareDrop_eq
    {n k : Nat} {DSeed TSeed Child : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    [DecidableEq Child]
    (children : Finset Child)
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool)
    (p : Rat) (parentCoefficient : Finset (Fin n) -> Rat)
    (childCoefficient : Child -> Finset (Fin n) -> Rat)
    (hDOrthogonal :
      forall alpha, alpha ∈ degreeSupports n k ->
        forall beta, beta ∈ degreeSupports n k -> alpha ≠ beta ->
          finiteAverage (fun d : DSeed =>
            character alpha (D d) * character beta (D d)) = 0)
    (hTMask : forall alpha, alpha ∈ degreeSupports n k ->
      finiteAverage (fun t : TSeed =>
        maskAllZeroIndicator alpha (T t)) = p ^ k) :
    finiteAverage (fun seed : DSeed × TSeed =>
      (finiteAverage (fun uniform : Fin n -> Bool =>
        homogeneousPolynomial k parentCoefficient
          (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2 -
        ∑ child in children,
          (finiteAverage (fun uniform : Fin n -> Bool =>
            homogeneousPolynomial k (childCoefficient child)
              (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2) =
      p ^ k *
        ((∑ alpha in degreeSupports n k,
            (parentCoefficient alpha) ^ 2) -
          ∑ child in children,
            ∑ alpha in degreeSupports n k,
              (childCoefficient child alpha) ^ 2) := by
  rw [finiteAverage_sub, finiteAverage_finset_sum]
  rw [homogeneousPolynomial_restriction_secondMoment_eq
    D T p parentCoefficient hDOrthogonal hTMask]
  have hchildren :
      (∑ child in children,
        finiteAverage (fun seed : DSeed × TSeed =>
          (finiteAverage (fun uniform : Fin n -> Bool =>
            homogeneousPolynomial k (childCoefficient child)
              (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2)) =
        p ^ k * ∑ child in children,
          ∑ alpha in degreeSupports n k,
            (childCoefficient child alpha) ^ 2 := by
    calc
      (∑ child in children,
          finiteAverage (fun seed : DSeed × TSeed =>
            (finiteAverage (fun uniform : Fin n -> Bool =>
              homogeneousPolynomial k (childCoefficient child)
                (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2)) =
        ∑ child in children,
        p ^ k * ∑ alpha in degreeSupports n k,
          (childCoefficient child alpha) ^ 2 := by
            apply Finset.sum_congr rfl
            intro child _
            rw [homogeneousPolynomial_restriction_secondMoment_eq
              D T p (childCoefficient child) hDOrthogonal hTMask]
      _ = p ^ k * ∑ child in children,
          ∑ alpha in degreeSupports n k,
            (childCoefficient child alpha) ^ 2 := by
              rw [Finset.mul_sum]
  rw [hchildren]
  ring

/-! ## Global one-degree reverse-LCP telescope -/

/-- The coefficient of one homogeneous Fourier support in a reverse-LCP
suffix cone, expressed as the signed mass of the atomic coefficients below
that cone. -/
noncomputable def reverseLCPConeCoefficient
    {n : Nat} {Index Alphabet : Type*}
    [Fintype Index] [DecidableEq Alphabet]
    (trace : Index -> List Alphabet)
    (atomCoefficient : Index -> Finset (Fin n) -> Rat)
    (key : List Alphabet) (support : Finset (Fin n)) : Rat :=
  suffixConeMass trace (fun index => atomCoefficient index support) key

/-- Coefficientwise global reverse-trie telescope on one homogeneous degree.
The local parent-minus-children square drops sum to the root degree energy
with coefficient exactly one. -/
theorem sum_reverseLCPConeCoefficientSquareDrops_eq_rootDegreeEnergy
    {n k : Nat} {Index Alphabet : Type*}
    [Fintype Index] [DecidableEq Alphabet]
    (trace : Index -> List Alphabet)
    (atomCoefficient : Index -> Finset (Fin n) -> Rat) :
    (∑ key ∈ realizedLCSKeys trace,
        ((∑ support ∈ degreeSupports n k,
            (reverseLCPConeCoefficient trace atomCoefficient key support) ^ 2) -
          ∑ symbol ∈ nextSuffixSymbols trace key,
            ∑ support ∈ degreeSupports n k,
              (reverseLCPConeCoefficient trace atomCoefficient
                (symbol :: key) support) ^ 2)) =
      ∑ support ∈ degreeSupports n k,
        (∑ index : Index, atomCoefficient index support) ^ 2 := by
  classical
  calc
    (∑ key ∈ realizedLCSKeys trace,
        ((∑ support ∈ degreeSupports n k,
            (reverseLCPConeCoefficient trace atomCoefficient key support) ^ 2) -
          ∑ symbol ∈ nextSuffixSymbols trace key,
            ∑ support ∈ degreeSupports n k,
              (reverseLCPConeCoefficient trace atomCoefficient
                (symbol :: key) support) ^ 2)) =
      ∑ key ∈ realizedLCSKeys trace,
        ∑ support ∈ degreeSupports n k,
          ((reverseLCPConeCoefficient trace atomCoefficient key support) ^ 2 -
            ∑ symbol ∈ nextSuffixSymbols trace key,
              (reverseLCPConeCoefficient trace atomCoefficient
                (symbol :: key) support) ^ 2) := by
        apply Finset.sum_congr rfl
        intro key _
        rw [Finset.sum_sub_distrib]
        congr 1
        rw [Finset.sum_comm]
    _ = ∑ support ∈ degreeSupports n k,
        ∑ key ∈ realizedLCSKeys trace,
          ((reverseLCPConeCoefficient trace atomCoefficient key support) ^ 2 -
            ∑ symbol ∈ nextSuffixSymbols trace key,
              (reverseLCPConeCoefficient trace atomCoefficient
                (symbol :: key) support) ^ 2) := by
          rw [Finset.sum_comm]
    _ = ∑ support ∈ degreeSupports n k,
        (∑ index : Index, atomCoefficient index support) ^ 2 := by
          apply Finset.sum_congr rfl
          intro support _
          exact sum_suffixSquareDrops_realizedLCSKeys_eq_totalWeight_sq
            trace (fun index => atomCoefficient index support)

/-- Premise-explicit global Claim-18 identity on one degree.  Summing all
realized reverse-LCP parent-minus-children moments produces exactly
`p^k` times the root degree energy.  There is no factor depending on the
number of keys, children, or trace length. -/
theorem homogeneousPolynomial_restriction_globalReverseLCPEnergy_eq
    {n k : Nat} {Index Alphabet DSeed TSeed : Type*}
    [Fintype Index] [DecidableEq Alphabet]
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (trace : Index -> List Alphabet)
    (atomCoefficient : Index -> Finset (Fin n) -> Rat)
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool)
    (p : Rat)
    (hDOrthogonal :
      forall alpha, alpha ∈ degreeSupports n k ->
        forall beta, beta ∈ degreeSupports n k -> alpha ≠ beta ->
          finiteAverage (fun d : DSeed =>
            character alpha (D d) * character beta (D d)) = 0)
    (hTMask : forall alpha, alpha ∈ degreeSupports n k ->
      finiteAverage (fun t : TSeed =>
        maskAllZeroIndicator alpha (T t)) = p ^ k) :
    finiteAverage (fun seed : DSeed × TSeed =>
      ∑ key ∈ realizedLCSKeys trace,
        ((finiteAverage (fun uniform : Fin n -> Bool =>
            homogeneousPolynomial k
              (reverseLCPConeCoefficient trace atomCoefficient key)
              (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2 -
          ∑ symbol ∈ nextSuffixSymbols trace key,
            (finiteAverage (fun uniform : Fin n -> Bool =>
              homogeneousPolynomial k
                (reverseLCPConeCoefficient trace atomCoefficient
                  (symbol :: key))
                (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2)) =
      p ^ k *
        ∑ support ∈ degreeSupports n k,
          (∑ index : Index, atomCoefficient index support) ^ 2 := by
  rw [finiteAverage_finset_sum]
  calc
    (∑ key ∈ realizedLCSKeys trace,
        finiteAverage (fun seed : DSeed × TSeed =>
          (finiteAverage (fun uniform : Fin n -> Bool =>
              homogeneousPolynomial k
                (reverseLCPConeCoefficient trace atomCoefficient key)
                (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2 -
            ∑ symbol ∈ nextSuffixSymbols trace key,
              (finiteAverage (fun uniform : Fin n -> Bool =>
                homogeneousPolynomial k
                  (reverseLCPConeCoefficient trace atomCoefficient
                    (symbol :: key))
                  (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2)) =
      ∑ key ∈ realizedLCSKeys trace,
        p ^ k *
          ((∑ support ∈ degreeSupports n k,
              (reverseLCPConeCoefficient trace atomCoefficient key support) ^ 2) -
            ∑ symbol ∈ nextSuffixSymbols trace key,
              ∑ support ∈ degreeSupports n k,
                (reverseLCPConeCoefficient trace atomCoefficient
                  (symbol :: key) support) ^ 2) := by
        apply Finset.sum_congr rfl
        intro key _
        exact homogeneousPolynomial_restriction_squareDrop_eq
          (nextSuffixSymbols trace key) D T p
          (reverseLCPConeCoefficient trace atomCoefficient key)
          (fun symbol =>
            reverseLCPConeCoefficient trace atomCoefficient (symbol :: key))
          hDOrthogonal hTMask
    _ = p ^ k *
        ∑ key ∈ realizedLCSKeys trace,
          ((∑ support ∈ degreeSupports n k,
              (reverseLCPConeCoefficient trace atomCoefficient key support) ^ 2) -
            ∑ symbol ∈ nextSuffixSymbols trace key,
              ∑ support ∈ degreeSupports n k,
                (reverseLCPConeCoefficient trace atomCoefficient
                  (symbol :: key) support) ^ 2) := by
          rw [Finset.mul_sum]
    _ = p ^ k *
        ∑ support ∈ degreeSupports n k,
          (∑ index : Index, atomCoefficient index support) ^ 2 := by
          rw [sum_reverseLCPConeCoefficientSquareDrops_eq_rootDegreeEnergy]

/-- Named form of the global one-degree reverse-LCP moment, for concise
corollaries. -/
noncomputable def globalReverseLCPHomogeneousMoment
    {n k : Nat} {Index Alphabet DSeed TSeed : Type*}
    [Fintype Index] [DecidableEq Alphabet]
    [Fintype DSeed] [Fintype TSeed]
    (trace : Index -> List Alphabet)
    (atomCoefficient : Index -> Finset (Fin n) -> Rat)
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool) : Rat :=
  finiteAverage (fun seed : DSeed × TSeed =>
    ∑ key ∈ realizedLCSKeys trace,
      ((finiteAverage (fun uniform : Fin n -> Bool =>
          homogeneousPolynomial k
            (reverseLCPConeCoefficient trace atomCoefficient key)
            (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2 -
        ∑ symbol ∈ nextSuffixSymbols trace key,
          (finiteAverage (fun uniform : Fin n -> Bool =>
            homogeneousPolynomial k
              (reverseLCPConeCoefficient trace atomCoefficient
                (symbol :: key))
              (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2))

/-- If the atomic coefficients sum to the Fourier coefficients of a root
function, the exact global telescope is `p^k * degreeEnergy k root`. -/
theorem globalReverseLCPHomogeneousMoment_eq_degreeEnergy
    {n k : Nat} {Index Alphabet DSeed TSeed : Type*}
    [Fintype Index] [DecidableEq Alphabet]
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (trace : Index -> List Alphabet)
    (atomCoefficient : Index -> Finset (Fin n) -> Rat)
    (root : (Fin n -> Bool) -> Rat)
    (hrootCoefficient : forall support,
      support ∈ degreeSupports n k ->
        (∑ index : Index, atomCoefficient index support) =
          coefficient root support)
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool)
    (p : Rat)
    (hDOrthogonal :
      forall alpha, alpha ∈ degreeSupports n k ->
        forall beta, beta ∈ degreeSupports n k -> alpha ≠ beta ->
          finiteAverage (fun d : DSeed =>
            character alpha (D d) * character beta (D d)) = 0)
    (hTMask : forall alpha, alpha ∈ degreeSupports n k ->
      finiteAverage (fun t : TSeed =>
        maskAllZeroIndicator alpha (T t)) = p ^ k) :
    globalReverseLCPHomogeneousMoment
        (k := k) trace atomCoefficient D T =
      p ^ k * degreeEnergy k root := by
  unfold globalReverseLCPHomogeneousMoment
  rw [homogeneousPolynomial_restriction_globalReverseLCPEnergy_eq
    trace atomCoefficient D T p hDOrthogonal hTMask]
  unfold degreeEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro support hsupport
  rw [hrootCoefficient support hsupport]

/-- Pure first-high-homogeneous-block corollary.  Degree-`2m+1` Gram
orthogonality bounds the `k × k` square-drop block at
`k = 2m+1` by `p^(2m+1)`.  This does not remove the mixed `k × ℓ` terms
with `ℓ ≥ 2m+2` from the square of the full high tail. -/
theorem globalReverseLCP_firstHighLayer_le_pow
    {n m : Nat} {Index Alphabet DSeed TSeed : Type*}
    [Fintype Index] [DecidableEq Alphabet]
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (trace : Index -> List Alphabet)
    (atomCoefficient : Index -> Finset (Fin n) -> Rat)
    (root : (Fin n -> Bool) -> Rat)
    (hrootCoefficient : forall support,
      support ∈ degreeSupports n (2 * m + 1) ->
        (∑ index : Index, atomCoefficient index support) =
          coefficient root support)
    (hrootBounded : forall input, |root input| ≤ 1)
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool)
    (p : Rat) (hp : 0 ≤ p)
    (hDOrthogonal :
      forall alpha, alpha ∈ degreeSupports n (2 * m + 1) ->
        forall beta, beta ∈ degreeSupports n (2 * m + 1) -> alpha ≠ beta ->
          finiteAverage (fun d : DSeed =>
            character alpha (D d) * character beta (D d)) = 0)
    (hTMask : forall alpha, alpha ∈ degreeSupports n (2 * m + 1) ->
      finiteAverage (fun t : TSeed =>
        maskAllZeroIndicator alpha (T t)) = p ^ (2 * m + 1)) :
    globalReverseLCPHomogeneousMoment
        (k := 2 * m + 1) trace atomCoefficient D T ≤
      p ^ (2 * m + 1) := by
  rw [globalReverseLCPHomogeneousMoment_eq_degreeEnergy
    trace atomCoefficient root hrootCoefficient D T p
      hDOrthogonal hTMask]
  calc
    p ^ (2 * m + 1) * degreeEnergy (2 * m + 1) root ≤
        p ^ (2 * m + 1) * 1 :=
      mul_le_mul_of_nonneg_left
        (degreeEnergy_le_one root hrootBounded)
        (pow_nonneg hp _)
    _ = p ^ (2 * m + 1) := by ring

/-- Atomic accepted-point Fourier coefficients sum to the Fourier
coefficient of the uFBDD acceptance indicator. -/
theorem sum_acceptedPointCoefficients_eq_acceptanceCoefficient
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (support : Finset (Fin n)) :
    (∑ accepted : B.AcceptedModel,
        coefficient (B.ratAcceptedPointIndicator accepted) support) =
      coefficient B.ratAcceptanceIndicator support := by
  symm
  calc
    coefficient B.ratAcceptanceIndicator support =
        coefficient
          (fun input => ∑ accepted : B.AcceptedModel,
            B.ratAcceptedPointIndicator accepted input) support := by
      congr 1
      funext input
      exact B.ratAcceptanceIndicator_eq_sum_acceptedPoints input
    _ = ∑ accepted : B.AcceptedModel,
        coefficient (B.ratAcceptedPointIndicator accepted) support := by
      exact FiniteUnambiguousFBDD.coefficient_fintype_sum
        (fun accepted input => B.ratAcceptedPointIndicator accepted input)
        support

theorem abs_ratAcceptanceIndicator_le_one
    {n : Nat} (B : FiniteUnambiguousFBDD n) (input : Fin n -> Bool) :
    |B.ratAcceptanceIndicator input| ≤ (1 : Rat) := by
  classical
  by_cases haccepts : B.Accepts input <;>
    simp [FiniteUnambiguousFBDD.ratAcceptanceIndicator, haccepts]

/-- Canonical accepted-model specialization of the pure first-high-degree
coefficient block.  It bounds the coefficient-defined homogeneous moment;
no identification with the complete residual high-tail LCP charge is claimed
here. -/
theorem canonicalAcceptedModelReverseLCP_firstHighLayer_le_pow
    {n m : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (B : FiniteUnambiguousFBDD n)
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool)
    (p : Rat) (hp : 0 ≤ p)
    (hDOrthogonal :
      forall alpha, alpha ∈ degreeSupports n (2 * m + 1) ->
        forall beta, beta ∈ degreeSupports n (2 * m + 1) -> alpha ≠ beta ->
          finiteAverage (fun d : DSeed =>
            character alpha (D d) * character beta (D d)) = 0)
    (hTMask : forall alpha, alpha ∈ degreeSupports n (2 * m + 1) ->
      finiteAverage (fun t : TSeed =>
        maskAllZeroIndicator alpha (T t)) = p ^ (2 * m + 1)) :
    globalReverseLCPHomogeneousMoment
        (k := 2 * m + 1)
        B.canonicalInputLabelledFullTrace
        (fun accepted support =>
          coefficient (B.ratAcceptedPointIndicator accepted) support)
        D T ≤
      p ^ (2 * m + 1) := by
  exact globalReverseLCP_firstHighLayer_le_pow
    B.canonicalInputLabelledFullTrace
    (fun accepted support =>
      coefficient (B.ratAcceptedPointIndicator accepted) support)
    B.ratAcceptanceIndicator
    (fun support _ =>
      sum_acceptedPointCoefficients_eq_acceptanceCoefficient B support)
    (abs_ratAcceptanceIndicator_le_one B)
    D T p hp hDOrthogonal hTMask

/-! ## Strongest exact identity for the actual structured source -/

/-- The diagonal mask-survival term in the exact structured second moment. -/
noncomputable def structuredDiagonalMaskEnergy
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (f : (Fin (2 ^ n) -> Bool) -> Rat) : Rat :=
  ∑ support ∈ highDegreeSupports (2 ^ n) (2 * m),
    (coefficient f support) ^ 2 *
      finiteAverage
        (fun seed : Fin (structuredIndependence m * n) -> Bool =>
          maskAllZeroIndicator support
            ((structuredDyadicPrimitive n m tailBits hn htail).generate seed))

/-- Before any scalarization, triangle inequality, or absolute value, the
actual structured source has this exact signed-coordinate identity.  The
first term is diagonal energy; every failure of Claim-18 orthogonality is
isolated in the signed dual-code alias term. -/
theorem structured_highTail_restriction_signedCoordinateSecondMoment_eq
    {Coordinate : Type*} [Fintype Coordinate]
    (n m tailBits : Nat) (hn : 0 < n) (htail : tailBits ≤ n)
    (weight : Coordinate -> Rat)
    (family : Coordinate -> (Fin (2 ^ n) -> Bool) -> Rat) :
    finiteAverage
        (fun seed :
            (Fin (structuredIndependence m * n) -> Bool) ×
              (Fin (structuredIndependence m * n) -> Bool) =>
          ∑ coordinate : Coordinate,
            weight coordinate *
              (finiteAverage (fun uniform : Fin (2 ^ n) -> Bool =>
                ratHighDegreeFourierTail (family coordinate) (2 * m)
                  (maskedInput
                    ((structuredUnbiasedPrimitive n m hn).generate seed.1)
                    ((structuredDyadicPrimitive n m tailBits hn htail).generate
                      seed.2)
                    uniform))) ^ 2) =
      ∑ coordinate : Coordinate,
        weight coordinate *
          (structuredDiagonalMaskEnergy n m tailBits hn htail
              (family coordinate) +
            structuredDualFarPairCorrelation n m tailBits (2 * m)
              hn htail (family coordinate)) := by
  rw [finiteAverage_fintype_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  rw [finiteAverage_const_mul]
  rw [structured_highTail_restriction_secondMoment_eq_diagonal_add_dual]
  unfold structuredDiagonalMaskEnergy
  congr

/-! ## The one-order-short obstruction is already visible on four coordinates -/

/-- The two singleton supports used by the smallest counterexample. -/
def singletonSupport0 : Finset FourCoordinate := {0}

def singletonSupport1 : Finset FourCoordinate := {1}

theorem singletonSupport0_symmDiff_singletonSupport1 :
    singletonSupport0 ∆ singletonSupport1 = support01 := by
  decide

/-- For `m = 0` the structured base source is only one-wise independent.
The symmetric difference of two distinct degree-one supports is the
degree-one dual word `{0,1}`, so their Gram entry is one rather than zero. -/
theorem structuredDegreeOne_singletonPairAverage_eq_one :
    finiteAverage
        (fun seed : Fin (structuredIndependence 0 * 2) -> Bool =>
          character singletonSupport0
              ((structuredUnbiasedPrimitive 2 0 (by omega)).generate seed) *
            character singletonSupport1
              ((structuredUnbiasedPrimitive 2 0 (by omega)).generate seed)) =
      1 := by
  have hdual :
      IsStructuredDualSupport 2 (structuredIndependence 0) (by omega)
        (singletonSupport0 ∆ singletonSupport1) := by
    rw [singletonSupport0_symmDiff_singletonSupport1]
    simpa [structuredIndependence] using
      (isStructuredDualSupport_degreeOne_of_even_card
        2 (by omega) support01 (by decide))
  rw [structuredUnbiasedPrimitive_characterPairAverage_eq_dualIndicator]
  simp [hdual]

/-- Hence the degree-one Gram-orthogonality premise needed by Claim 18 is
false for the actual first structured source.  This is the minimal finite
failure: it uses two distinct singleton Fourier supports. -/
theorem not_structuredDegreeOne_gramOrthogonal :
    ¬ (forall alpha, alpha ∈ degreeSupports (2 ^ 2) 1 ->
        forall beta, beta ∈ degreeSupports (2 ^ 2) 1 -> alpha ≠ beta ->
          finiteAverage
              (fun seed : Fin (structuredIndependence 0 * 2) -> Bool =>
                character alpha
                    ((structuredUnbiasedPrimitive 2 0 (by omega)).generate seed) *
                  character beta
                    ((structuredUnbiasedPrimitive 2 0 (by omega)).generate seed)) =
            0) := by
  intro horthogonal
  have hzero := horthogonal singletonSupport0 (by decide)
    singletonSupport1 (by decide) (by decide)
  rw [structuredDegreeOne_singletonPairAverage_eq_one] at hzero
  norm_num at hzero

/-- The same obstruction survives the full two-coordinate structured mask.
The exact restricted-character pair moment is `1/4`; the corresponding
off-diagonal moment would be zero under the Claim-18 orthogonality premise. -/
theorem structuredDegreeOne_singletonRestrictedPairMoment_eq_quarter :
    finiteAverage
        (fun seed :
            (Fin (structuredIndependence 0 * 2) -> Bool) ×
              (Fin (structuredIndependence 0 * 2) -> Bool) =>
          restrictedCharacterAverage singletonSupport0
              ((structuredUnbiasedPrimitive 2 0 (by omega)).generate seed.1)
              ((structuredDyadicPrimitive 2 0 2 (by omega) (by omega)).generate
                seed.2) *
            restrictedCharacterAverage singletonSupport1
              ((structuredUnbiasedPrimitive 2 0 (by omega)).generate seed.1)
              ((structuredDyadicPrimitive 2 0 2 (by omega) (by omega)).generate
                seed.2)) =
      1 / 4 := by
  have hdual :
      IsStructuredDualSupport 2 (structuredIndependence 0) (by omega)
        (singletonSupport0 ∆ singletonSupport1) := by
    rw [singletonSupport0_symmDiff_singletonSupport1]
    simpa [structuredIndependence] using
      (isStructuredDualSupport_degreeOne_of_even_card
        2 (by omega) support01 (by decide))
  rw [structuredUnbiasedPrimitive_restrictedCharacterPairMoment_eq]
  rw [if_pos hdual]
  rw [structuredDyadicPrimitive_fullMaskSurvival_exact]
  · norm_num [structuredIndependence]
  · decide

/-! ## Exact off-by-one witness at the first nontrivial cutoff -/

abbrev SixteenCoordinate := Fin (2 ^ 4)

abbrev SixteenField := GaloisField 2 4

/-- `GF(16)^*` contains an element of order five because its order is
`16 - 1 = 15`. -/
theorem exists_fifthRootUnit :
    ∃ root : SixteenFieldˣ, orderOf root = 5 := by
  have hfieldCard : Fintype.card SixteenField = 16 := by
    simpa using binaryGaloisField_card 4 (by omega)
  have hdiv : 5 ∣ Fintype.card SixteenFieldˣ := by
    rw [Fintype.card_units, hfieldCard]
    norm_num
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact exists_prime_orderOf_dvd_card 5 hdiv

noncomputable def fifthRootUnit : SixteenFieldˣ :=
  Classical.choose exists_fifthRootUnit

theorem fifthRootUnit_order : orderOf fifthRootUnit = 5 :=
  Classical.choose_spec exists_fifthRootUnit

theorem fifthRoot_isPrimitiveRoot :
    IsPrimitiveRoot (fifthRootUnit : SixteenField) 5 := by
  rw [IsPrimitiveRoot.coe_units_iff]
  simpa [fifthRootUnit_order] using
    (IsPrimitiveRoot.orderOf fifthRootUnit)

/-- Encode a field element by the truth-table coordinate which decodes to
it.  Unlike a hard-coded polynomial-basis numbering, this definition is
valid for the classically chosen basis used by the structured primitive. -/
noncomputable def sixteenFieldIndex
    (value : SixteenField) : SixteenCoordinate :=
  StreamingMagnification.FixedBitstringCodec.rank
    (gfTwoBoolCoordinates 4 (by omega) value)

theorem sixteenFieldIndex_injective : Function.Injective sixteenFieldIndex := by
  intro left right hequal
  apply (gfTwoBoolCoordinates 4 (by omega)).injective
  exact StreamingMagnification.FixedBitstringCodec.rank_injective hequal

@[simp]
theorem structuredTruthTableNode_sixteenFieldIndex
    (value : SixteenField) :
    structuredTruthTableNode 4 (by omega) (sixteenFieldIndex value) = value := by
  unfold structuredTruthTableNode sixteenFieldIndex
  rw [← StreamingMagnification.FixedBitstringCodec.unrank_eq_lexInput,
    StreamingMagnification.FixedBitstringCodec.unrank_rank,
    Equiv.symm_apply_apply]

/-- The five fifth roots of unity, transported to truth-table coordinates. -/
noncomputable def fifthRootIndexSet : Finset SixteenCoordinate :=
  (Finset.range 5).image (fun exponent =>
    sixteenFieldIndex ((fifthRootUnit : SixteenField) ^ exponent))

theorem fifthRootIndexSet_card : fifthRootIndexSet.card = 5 := by
  classical
  unfold fifthRootIndexSet
  rw [Finset.card_image_of_injOn]
  · simp
  · intro left hleft right hright hequal
    apply fifthRoot_isPrimitiveRoot.injOn_pow hleft hright
    exact sixteenFieldIndex_injective hequal

theorem sixteenFieldIndex_zero_not_mem_fifthRootIndexSet :
    sixteenFieldIndex (0 : SixteenField) ∉ fifthRootIndexSet := by
  classical
  intro hmem
  rw [fifthRootIndexSet, Finset.mem_image] at hmem
  obtain ⟨exponent, _, hequal⟩ := hmem
  have hfieldEqual :
      (fifthRootUnit : SixteenField) ^ exponent = 0 :=
    sixteenFieldIndex_injective hequal
  exact (pow_ne_zero exponent fifthRootUnit.ne_zero) hfieldEqual

/-- A basis-independent six-point dual word: zero together with all fifth
roots of unity. -/
noncomputable def offByOneDualWord : Finset SixteenCoordinate :=
  insert (sixteenFieldIndex (0 : SixteenField)) fifthRootIndexSet

theorem offByOneDualWord_card : offByOneDualWord.card = 6 := by
  classical
  rw [offByOneDualWord,
    Finset.card_insert_of_not_mem
      sixteenFieldIndex_zero_not_mem_fifthRootIndexSet,
    fifthRootIndexSet_card]

theorem sum_fifthRootIndexSet_node_pow (exponent : Nat) :
    (∑ index ∈ fifthRootIndexSet,
        structuredTruthTableNode 4 (by omega) index ^ exponent) =
      ∑ power ∈ Finset.range 5,
        ((fifthRootUnit : SixteenField) ^ power) ^ exponent := by
  classical
  have hinjective : Set.InjOn
      (fun power : Nat =>
        sixteenFieldIndex ((fifthRootUnit : SixteenField) ^ power))
      (Finset.range 5) := by
    intro left hleft right hright hequal
    apply fifthRoot_isPrimitiveRoot.injOn_pow hleft hright
    exact sixteenFieldIndex_injective hequal
  unfold fifthRootIndexSet
  rw [Finset.sum_image hinjective]
  apply Finset.sum_congr rfl
  intro power _
  rw [structuredTruthTableNode_sixteenFieldIndex]

theorem offByOneDualWord_powerSum_eq_zero (exponent : Fin 5) :
    structuredSupportPowerSum 4 (by omega) offByOneDualWord exponent.val = 0 := by
  classical
  unfold structuredSupportPowerSum offByOneDualWord
  rw [Finset.sum_insert sixteenFieldIndex_zero_not_mem_fifthRootIndexSet,
    structuredTruthTableNode_sixteenFieldIndex,
    sum_fifthRootIndexSet_node_pow]
  by_cases hzero : exponent.val = 0
  · simp [hzero]
    have hchar : (2 : SixteenField) = 0 :=
      CharP.cast_eq_zero SixteenField 2
    calc
      (1 : SixteenField) + 5 = 6 := by norm_num
      _ = 3 * 2 := by norm_num
      _ = 0 := by rw [hchar, mul_zero]
  · have hpositive : 0 < exponent.val := Nat.pos_of_ne_zero hzero
    have hcases : exponent.val = 1 ∨ exponent.val = 2 ∨
        exponent.val = 3 ∨ exponent.val = 4 := by
      omega
    have hcoprime : exponent.val.Coprime 5 := by
      rcases hcases with h | h | h | h
      · simpa [h] using (by decide : Nat.Coprime 1 5)
      · simpa [h] using (by decide : Nat.Coprime 2 5)
      · simpa [h] using (by decide : Nat.Coprime 3 5)
      · simpa [h] using (by decide : Nat.Coprime 4 5)
    have hprimitive :
        IsPrimitiveRoot
          ((fifthRootUnit : SixteenField) ^ exponent.val) 5 :=
      fifthRoot_isPrimitiveRoot.pow_of_coprime exponent.val hcoprime
    rw [zero_pow hzero]
    rw [zero_add]
    convert hprimitive.geom_sum_eq_zero (by omega) using 1
    apply Finset.sum_congr rfl
    intro power _
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]

theorem offByOneDualWord_isStructuredDualSupport :
    IsStructuredDualSupport 4 (structuredIndependence 1) (by omega)
      offByOneDualWord := by
  rw [isStructuredDualSupport_iff_powerSums_eq_zero]
  simpa [structuredIndependence] using offByOneDualWord_powerSum_eq_zero

/-- Choose one half of the six-point word.  Only existence and cardinality
matter; the construction is independent of the arbitrary field basis. -/
noncomputable def offByOneLeft : Finset SixteenCoordinate :=
  Classical.choose
    (Finset.exists_subset_card_eq
      (s := offByOneDualWord) (n := 3)
        (by rw [offByOneDualWord_card]; omega))

theorem offByOneLeft_subset : offByOneLeft ⊆ offByOneDualWord :=
  (Classical.choose_spec
    (Finset.exists_subset_card_eq
      (s := offByOneDualWord) (n := 3)
        (by rw [offByOneDualWord_card]; omega))).1

theorem offByOneLeft_card : offByOneLeft.card = 3 :=
  (Classical.choose_spec
    (Finset.exists_subset_card_eq
      (s := offByOneDualWord) (n := 3)
        (by rw [offByOneDualWord_card]; omega))).2

noncomputable def offByOneRight : Finset SixteenCoordinate :=
  offByOneDualWord \ offByOneLeft

theorem offByOneRight_card : offByOneRight.card = 3 := by
  rw [offByOneRight, Finset.card_sdiff offByOneLeft_subset,
    offByOneDualWord_card, offByOneLeft_card]

theorem offByOneLeft_disjoint_offByOneRight :
    Disjoint offByOneLeft offByOneRight := by
  exact Finset.disjoint_sdiff

theorem offByOneLeft_symmDiff_offByOneRight :
    offByOneLeft ∆ offByOneRight = offByOneDualWord := by
  rw [Finset.symmDiff_eq_union offByOneLeft_disjoint_offByOneRight]
  exact Finset.union_sdiff_of_subset offByOneLeft_subset

theorem offByOneLeft_mem_degreeSupports :
    offByOneLeft ∈ degreeSupports (2 ^ 4) 3 := by
  rw [mem_degreeSupports]
  exact offByOneLeft_card

theorem offByOneRight_mem_degreeSupports :
    offByOneRight ∈ degreeSupports (2 ^ 4) 3 := by
  rw [mem_degreeSupports]
  exact offByOneRight_card

theorem offByOneLeft_ne_offByOneRight : offByOneLeft ≠ offByOneRight := by
  intro hequal
  obtain ⟨index, hindex⟩ : offByOneLeft.Nonempty :=
    Finset.card_pos.mp (by rw [offByOneLeft_card]; omega)
  have hnotRight : index ∉ offByOneRight :=
    Finset.disjoint_left.mp offByOneLeft_disjoint_offByOneRight hindex
  exact hnotRight (hequal ▸ hindex)

/-- The first high layer at `m = 1` has degree three.  These two distinct
degree-three characters have base Gram entry one because their six-point
symmetric difference is a dual word for the five-wise source. -/
theorem offByOne_degreeThree_characterPairAverage_eq_one :
    finiteAverage
        (fun seed : Fin (structuredIndependence 1 * 4) -> Bool =>
          character offByOneLeft
              ((structuredUnbiasedPrimitive 4 1 (by omega)).generate seed) *
            character offByOneRight
              ((structuredUnbiasedPrimitive 4 1 (by omega)).generate seed)) =
      1 := by
  have hdual :
      IsStructuredDualSupport 4 (structuredIndependence 1) (by omega)
        (offByOneLeft ∆ offByOneRight) := by
    rw [offByOneLeft_symmDiff_offByOneRight]
    exact offByOneDualWord_isStructuredDualSupport
  rw [structuredUnbiasedPrimitive_characterPairAverage_eq_dualIndicator]
  simp [hdual]

/-- Exact `4m+1` versus `2(2m+1)` obstruction at `m = 1`: the actual
five-wise source is not Gram-orthogonal on the first high homogeneous layer
of degree three. -/
theorem not_structuredDegreeThree_gramOrthogonal :
    ¬ (forall alpha, alpha ∈ degreeSupports (2 ^ 4) 3 ->
        forall beta, beta ∈ degreeSupports (2 ^ 4) 3 -> alpha ≠ beta ->
          finiteAverage
              (fun seed : Fin (structuredIndependence 1 * 4) -> Bool =>
                character alpha
                    ((structuredUnbiasedPrimitive 4 1 (by omega)).generate seed) *
                  character beta
                    ((structuredUnbiasedPrimitive 4 1 (by omega)).generate seed)) =
            0) := by
  intro horthogonal
  have hzero := horthogonal offByOneLeft offByOneLeft_mem_degreeSupports
    offByOneRight offByOneRight_mem_degreeSupports
      offByOneLeft_ne_offByOneRight
  rw [offByOne_degreeThree_characterPairAverage_eq_one] at hzero
  norm_num at hzero

end FiniteVectorClaim18

end

end OneTapeMagnification
end Frontier
end Pnp4
