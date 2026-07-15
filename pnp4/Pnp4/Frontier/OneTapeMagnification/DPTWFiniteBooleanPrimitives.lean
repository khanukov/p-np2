import Pnp4.Frontier.OneTapeMagnification.DPTWZeroTailJointLocality
import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanBoundedIndependence
import Pnp4.Frontier.OneTapeMagnification.WeightedPRGSupport
import Pnp4.Frontier.OneTapeMagnification.DPTWUnambiguousFBDDHybridBridge
import Pnp4.Frontier.StreamingMagnification.FixedBitstringCodec
import Complexity.PsubsetPpolyInternal.Simulation

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Exact finite Boolean primitives for the DPTW restriction recursion

The DPTW/Forbes--Kelley recursion needs two finite sources on the truth-table
coordinates.  The `A` source is unbiased on every small cylinder and the `B`
source has false-bit mass `p` on every small cylinder (equivalently, true-bit
marginal `1-p`).  This file gives a fully specified finite source for dyadic
`p` and a semantically exact `DPTWCoordinatePrimitive` package.  The source
map is concrete, but the joint circuit wrapper uses noncomputable truth-table
synthesis and has no useful small-gate bound.

The construction here deliberately uses an independent `blockBits`-bit coin
for every output coordinate.  Thus its seed length is

`2^n * blockBits`,

not the `O(k * (n + log(1/p)))` seed length of the polynomial-evaluation
construction cited in DPTW Claim 3.11.  It closes the exact finite probability
and coordinate-circuit interfaces without hiding that remaining quantitative
compression step.
-/

open scoped BigOperators

open Pnp3.ComplexityInterfaces
open Pnp3.ComplexityInterfaces.DagCircuit
open StreamingMagnification
open StreamingMagnification.StandardDAG
open StreamingMagnification.TotalSearch
open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open FiniteBooleanBoundedIndependence

namespace DPTWFiniteBooleanPrimitives

/-! ## Flat tapes as independent coordinate blocks -/

/-- A flat Boolean tape of length `coordinates * blockBits` is exactly one
`blockBits`-bit tape for every coordinate. -/
def finiteBitTapeBlockEquiv (coordinates blockBits : Nat) :
    FiniteBitTape (coordinates * blockBits) ≃
      (Fin coordinates -> FiniteBitTape blockBits) where
  toFun := fun seed coordinate bit => seed (finProdFinEquiv (coordinate, bit))
  invFun := fun blocks index =>
    blocks (finProdFinEquiv.symm index).1 (finProdFinEquiv.symm index).2
  left_inv seed := by
    funext index
    exact congrArg seed (finProdFinEquiv.apply_symm_apply index)
  right_inv blocks := by
    funext coordinate bit
    have hpair := finProdFinEquiv.symm_apply_apply (coordinate, bit)
    exact congrArg (fun pair => blocks pair.1 pair.2) hpair

@[simp]
theorem finiteBitTapeBlockEquiv_apply
    (coordinates blockBits : Nat)
    (seed : FiniteBitTape (coordinates * blockBits))
    (coordinate : Fin coordinates) (bit : Fin blockBits) :
    finiteBitTapeBlockEquiv coordinates blockBits seed coordinate bit =
      seed (finProdFinEquiv (coordinate, bit)) :=
  rfl

/-- Rational finite averages are invariant under a finite equivalence. -/
theorem finiteAverage_comp_equiv
    {Input Output : Type*} [Fintype Input] [Fintype Output]
    (equiv : Input ≃ Output) (f : Output -> Rat) :
    finiteAverage (fun input => f (equiv input)) = finiteAverage f := by
  unfold finiteAverage
  have hsum :
      (∑ input : Input, f (equiv input)) = ∑ output : Output, f output :=
    Fintype.sum_equiv equiv _ _ (fun _ => rfl)
  rw [hsum, Fintype.card_congr equiv]

/-! ## One exact dyadic coin -/

/-- Interpret a `blockBits`-bit uniform block as a Boolean coin whose false
set is the initial interval `[0, falseCount)`. -/
def dyadicCoin (blockBits falseCount : Nat)
    (block : FiniteBitTape blockBits) : Bool :=
  decide (falseCount ≤
    (StreamingMagnification.FixedBitstringCodec.rank block).val)

@[simp]
theorem dyadicCoin_eq_false_iff
    (blockBits falseCount : Nat) (block : FiniteBitTape blockBits) :
    dyadicCoin blockBits falseCount block = false ↔
      (StreamingMagnification.FixedBitstringCodec.rank block).val <
        falseCount := by
  simp [dyadicCoin]

@[simp]
theorem dyadicCoin_eq_true_iff
    (blockBits falseCount : Nat) (block : FiniteBitTape blockBits) :
    dyadicCoin blockBits falseCount block = true ↔
      falseCount ≤
        (StreamingMagnification.FixedBitstringCodec.rank block).val := by
  simp [dyadicCoin]

/-- The exact rational false mass of the dyadic coin. -/
def dyadicFalseMass (blockBits falseCount : Nat) : Rat :=
  (falseCount : Rat) / (2 : Rat) ^ blockBits

private theorem sum_fin_indicator_lt
    {size cutoff : Nat} (hcutoff : cutoff ≤ size) :
    (∑ index : Fin size, if index.val < cutoff then (1 : Rat) else 0) =
      cutoff := by
  rw [Fin.sum_univ_eq_sum_range
    (fun index => if index < cutoff then (1 : Rat) else 0) size]
  calc
    (∑ index ∈ Finset.range size,
        if index < cutoff then (1 : Rat) else 0) =
      (∑ index ∈ Finset.range cutoff,
          if index < cutoff then (1 : Rat) else 0) +
        ∑ index ∈ Finset.Ico cutoff size,
          if index < cutoff then (1 : Rat) else 0 :=
      (Finset.sum_range_add_sum_Ico _ hcutoff).symm
    _ = (∑ _index ∈ Finset.range cutoff, (1 : Rat)) + 0 := by
      congr 1
      · apply Finset.sum_congr rfl
        intro index hindex
        simp [Finset.mem_range.mp hindex]
      · apply Finset.sum_eq_zero
        intro index hindex
        have hge := (Finset.mem_Ico.mp hindex).1
        simp [Nat.not_lt.mpr hge]
    _ = cutoff := by simp

private theorem sum_fin_indicator_ge
    {size cutoff : Nat} (hcutoff : cutoff ≤ size) :
    (∑ index : Fin size, if cutoff ≤ index.val then (1 : Rat) else 0) =
      ((size - cutoff : Nat) : Rat) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun index => if cutoff ≤ index then (1 : Rat) else 0) size]
  calc
    (∑ index ∈ Finset.range size,
        if cutoff ≤ index then (1 : Rat) else 0) =
      (∑ index ∈ Finset.range cutoff,
          if cutoff ≤ index then (1 : Rat) else 0) +
        ∑ index ∈ Finset.Ico cutoff size,
          if cutoff ≤ index then (1 : Rat) else 0 :=
      (Finset.sum_range_add_sum_Ico _ hcutoff).symm
    _ = 0 + ∑ _index ∈ Finset.Ico cutoff size, (1 : Rat) := by
      congr 1
      · apply Finset.sum_eq_zero
        intro index hindex
        have hlt := Finset.mem_range.mp hindex
        simp [Nat.not_le.mpr hlt]
      · apply Finset.sum_congr rfl
        intro index hindex
        have hge := (Finset.mem_Ico.mp hindex).1
        simp [hge]
    _ = ((size - cutoff : Nat) : Rat) := by
      simp [Nat.card_Ico, hcutoff]

/-- A single uniform block realizes the advertised false mass exactly. -/
theorem finiteAverage_dyadicCoin_false
    (blockBits falseCount : Nat) (hcount : falseCount ≤ 2 ^ blockBits) :
    finiteAverage (fun block : FiniteBitTape blockBits =>
      if dyadicCoin blockBits falseCount block = false then (1 : Rat)
      else 0) = dyadicFalseMass blockBits falseCount := by
  unfold finiteAverage dyadicFalseMass
  have hsum :
      (∑ block : FiniteBitTape blockBits,
          if dyadicCoin blockBits falseCount block = false then (1 : Rat)
          else 0) =
        ∑ index : Fin (2 ^ blockBits),
          if index.val < falseCount then (1 : Rat) else 0 := by
    apply Fintype.sum_equiv
      (StreamingMagnification.FixedBitstringCodec.equiv blockBits)
    intro block
    simp [dyadicCoin_eq_false_iff]
  rw [hsum, sum_fin_indicator_lt hcount]
  simp [Fintype.card_bool]

/-- The complementary true mass is exactly `1 - p`. -/
theorem finiteAverage_dyadicCoin_true
    (blockBits falseCount : Nat) (hcount : falseCount ≤ 2 ^ blockBits) :
    finiteAverage (fun block : FiniteBitTape blockBits =>
      if dyadicCoin blockBits falseCount block = true then (1 : Rat)
      else 0) = 1 - dyadicFalseMass blockBits falseCount := by
  unfold finiteAverage dyadicFalseMass
  have hsum :
      (∑ block : FiniteBitTape blockBits,
          if dyadicCoin blockBits falseCount block = true then (1 : Rat)
          else 0) =
        ∑ index : Fin (2 ^ blockBits),
          if falseCount ≤ index.val then (1 : Rat) else 0 := by
    apply Fintype.sum_equiv
      (StreamingMagnification.FixedBitstringCodec.equiv blockBits)
    intro block
    simp [dyadicCoin_eq_true_iff]
  rw [hsum, sum_fin_indicator_ge hcount]
  simp [Fintype.card_bool]
  have hpow : (0 : Rat) < (2 : Rat) ^ blockBits := by positivity
  field_simp [ne_of_gt hpow]

/-- Uniform averaging of an independent finite product factorizes. -/
theorem finiteAverage_pi_prod
    {Index Coin : Type*} [Fintype Index] [DecidableEq Index]
    [Fintype Coin] [Nonempty Coin]
    (weight : Index -> Coin -> Rat) :
    finiteAverage (fun sample : Index -> Coin =>
      ∏ index, weight index (sample index)) =
      ∏ index, finiteAverage (weight index) := by
  unfold finiteAverage
  rw [← Fintype.prod_sum]
  simp only [Fintype.card_fun]
  rw [Finset.prod_div_distrib]
  simp

/-! ## The independent dyadic coordinate source -/

/-- One independent dyadic coin per output coordinate, stored in the flat
seed layout consumed by `DPTWCoordinatePrimitive`. -/
def dyadicProductSource (coordinates blockBits falseCount : Nat) :
    FiniteBitTape (coordinates * blockBits) -> Fin coordinates -> Bool :=
  fun seed coordinate =>
    dyadicCoin blockBits falseCount
      (finiteBitTapeBlockEquiv coordinates blockBits seed coordinate)

private theorem localPatternIndicator_eq_prod
    {coordinates blockBits falseCount : Nat}
    (support : Finset (Fin coordinates))
    (pattern : LocalAssignment support)
    (blocks : Fin coordinates -> FiniteBitTape blockBits) :
    localPatternIndicator support pattern
        (fun coordinate =>
          dyadicCoin blockBits falseCount (blocks coordinate)) =
      ∏ coordinate : support,
        if dyadicCoin blockBits falseCount (blocks coordinate) =
            pattern coordinate then (1 : Rat) else 0 := by
  unfold localPatternIndicator
  by_cases hpattern :
      restrictAssignment support
          (fun coordinate =>
            dyadicCoin blockBits falseCount (blocks coordinate)) = pattern
  · rw [if_pos hpattern]
    apply Eq.symm
    apply Finset.prod_eq_one
    intro coordinate _
    have hcoordinate := congrFun hpattern coordinate
    simp only [restrictAssignment] at hcoordinate
    simp [hcoordinate]
  · rw [if_neg hpattern]
    apply Eq.symm
    rw [Finset.prod_eq_zero_iff]
    have hexists : ∃ coordinate : support,
        dyadicCoin blockBits falseCount (blocks coordinate) ≠
          pattern coordinate := by
      by_contra hnone
      push_neg at hnone
      apply hpattern
      funext coordinate
      exact hnone coordinate
    obtain ⟨coordinate, hcoordinate⟩ := hexists
    refine ⟨coordinate, Finset.mem_univ _, ?_⟩
    simp [hcoordinate]

/-- The flat dyadic product source has the full product cylinder law, hence
is `q`-wise false-biased for every `q`. -/
theorem dyadicProductSource_isKWisePatternFalseBiased
    (coordinates blockBits falseCount q : Nat)
    (hcount : falseCount ≤ 2 ^ blockBits) :
    IsKWisePatternFalseBiased q
      (dyadicFalseMass blockBits falseCount)
      (dyadicProductSource coordinates blockBits falseCount) := by
  intro support _hcard pattern
  calc
    finiteAverage (fun seed : FiniteBitTape (coordinates * blockBits) =>
        localPatternIndicator support pattern
          (dyadicProductSource coordinates blockBits falseCount seed)) =
      finiteAverage (fun blocks : Fin coordinates -> FiniteBitTape blockBits =>
        localPatternIndicator support pattern
          (fun coordinate =>
            dyadicCoin blockBits falseCount (blocks coordinate))) := by
        simpa [dyadicProductSource] using
          (finiteAverage_comp_equiv
            (finiteBitTapeBlockEquiv coordinates blockBits)
            (fun blocks : Fin coordinates -> FiniteBitTape blockBits =>
              localPatternIndicator support pattern
                (fun coordinate =>
                  dyadicCoin blockBits falseCount (blocks coordinate))))
    _ = finiteAverage (fun blocks : Fin coordinates -> FiniteBitTape blockBits =>
        ∏ coordinate : support,
          if dyadicCoin blockBits falseCount (blocks coordinate) =
              pattern coordinate then (1 : Rat) else 0) := by
        apply finiteAverage_congr
        intro blocks
        exact localPatternIndicator_eq_prod support pattern blocks
    _ = ∏ coordinate : support,
        finiteAverage (fun block : FiniteBitTape blockBits =>
          if dyadicCoin blockBits falseCount block = pattern coordinate
            then (1 : Rat) else 0) := by
      let localWeight : support -> FiniteBitTape blockBits -> Rat :=
        fun coordinate block =>
          if dyadicCoin blockBits falseCount block = pattern coordinate
            then 1 else 0
      let weight : Fin coordinates -> FiniteBitTape blockBits -> Rat :=
        fun coordinate block =>
          if hcoordinate : coordinate ∈ support then
            localWeight ⟨coordinate, hcoordinate⟩ block
          else 1
      calc
        finiteAverage (fun blocks : Fin coordinates -> FiniteBitTape blockBits =>
            ∏ coordinate : support,
              if dyadicCoin blockBits falseCount (blocks coordinate) =
                  pattern coordinate then (1 : Rat) else 0) =
          finiteAverage (fun blocks : Fin coordinates -> FiniteBitTape blockBits =>
            ∏ coordinate, weight coordinate (blocks coordinate)) := by
              apply finiteAverage_congr
              intro blocks
              simpa [localWeight, weight] using
                (Finset.prod_attach_eq_prod_dite support
                  (fun coordinate : support =>
                    localWeight coordinate (blocks coordinate)))
        _ = ∏ coordinate, finiteAverage (weight coordinate) :=
          finiteAverage_pi_prod weight
        _ = ∏ coordinate : support,
            finiteAverage (localWeight coordinate) := by
          calc
            (∏ coordinate, finiteAverage (weight coordinate)) =
                ∏ coordinate,
                  if hcoordinate : coordinate ∈ support then
                    finiteAverage (localWeight ⟨coordinate, hcoordinate⟩)
                  else 1 := by
              apply Finset.prod_congr rfl
              intro coordinate _
              by_cases hcoordinate : coordinate ∈ support
              · simp [weight, hcoordinate]
              · simp [weight, hcoordinate, finiteAverage_one]
            _ = ∏ coordinate : support,
                finiteAverage (localWeight coordinate) := by
              symm
              exact Finset.prod_attach_eq_prod_dite support
                (fun coordinate : support =>
                  finiteAverage (localWeight coordinate))
        _ = _ := by rfl
    _ = localPatternProductMass
        (dyadicFalseMass blockBits falseCount) pattern := by
      unfold localPatternProductMass
      apply Finset.prod_congr rfl
      intro coordinate _
      cases hvalue : pattern coordinate
      · simpa [hvalue] using
          finiteAverage_dyadicCoin_false blockBits falseCount hcount
      · simpa [hvalue] using
          finiteAverage_dyadicCoin_true blockBits falseCount hcount

/-! ## The unbiased `A` specialization -/

/-- For a positive block length, the first half of the block cube has mass
exactly `1/2`. -/
theorem dyadicFalseMass_half (blockBits : Nat) (hpositive : 0 < blockBits) :
    dyadicFalseMass blockBits (2 ^ (blockBits - 1)) = (1 : Rat) / 2 := by
  obtain ⟨rest, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpositive)
  simp only [dyadicFalseMass, pow_succ]
  have hpow : (2 : Rat) ^ rest ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [hpow]

/-- At false mass `1/2`, the biased product cylinder mass is the uniform
cylinder mass. -/
theorem localPatternProductMass_half
    {coordinates : Nat} {support : Finset (Fin coordinates)}
    (pattern : LocalAssignment support) :
    localPatternProductMass ((1 : Rat) / 2) pattern =
      1 / (2 : Rat) ^ support.card := by
  unfold localPatternProductMass
  have hterm : ∀ coordinate : support,
      (if pattern coordinate then 1 - (1 : Rat) / 2 else (1 : Rat) / 2) =
        (1 : Rat) / 2 := by
    intro coordinate
    cases pattern coordinate <;> norm_num
  simp_rw [hterm]
  simp [one_div]

/-- The half-threshold product source is unbiased on every cylinder. -/
theorem dyadicHalfProductSource_isKWisePatternUnbiased
    (coordinates blockBits q : Nat) (hpositive : 0 < blockBits) :
    IsKWisePatternUnbiased q
      (dyadicProductSource coordinates blockBits (2 ^ (blockBits - 1))) := by
  intro support hcard pattern
  have hcount : 2 ^ (blockBits - 1) ≤ 2 ^ blockBits := by
    exact Nat.pow_le_pow_right (by omega : 0 < (2 : Nat))
      (by omega : blockBits - 1 ≤ blockBits)
  have hbiased :=
    dyadicProductSource_isKWisePatternFalseBiased
      coordinates blockBits (2 ^ (blockBits - 1)) q hcount
      support hcard pattern
  rw [dyadicFalseMass_half blockBits hpositive] at hbiased
  rw [hbiased]
  exact localPatternProductMass_half pattern

/-! ## A constant-free semantic coordinate compiler -/

/-- One constant-free gate computing Boolean negation. -/
def paperNotHead : DagCircuit 1 where
  gates := 1
  gate := fun _ => DagGate.not (DagWire.input (0 : Fin 1))
  output := DagWire.gate (0 : Fin 1)

/-- One constant-free gate computing Boolean conjunction. -/
def paperAndHead : DagCircuit 2 where
  gates := 1
  gate := fun _ =>
    DagGate.and (DagWire.input (0 : Fin 2)) (DagWire.input (1 : Fin 2))
  output := DagWire.gate (0 : Fin 1)

/-- One constant-free gate computing Boolean disjunction. -/
def paperOrHead : DagCircuit 2 where
  gates := 1
  gate := fun _ =>
    DagGate.or (DagWire.input (0 : Fin 2)) (DagWire.input (1 : Fin 2))
  output := DagWire.gate (0 : Fin 1)

@[simp] theorem eval_paperNotHead (input : Bitstring 1) :
    DagCircuit.eval paperNotHead input = !(input 0) := by
  rw [DagCircuit.eval.eq_1]
  change DagCircuit.eval.evalGateAt paperNotHead input 0 _ = _
  rw [DagCircuit.eval.evalGateAt.eq_1]
  rfl

@[simp] theorem eval_paperAndHead (input : Bitstring 2) :
    DagCircuit.eval paperAndHead input = (input 0 && input 1) := by
  rw [DagCircuit.eval.eq_1]
  change DagCircuit.eval.evalGateAt paperAndHead input 0 _ = _
  rw [DagCircuit.eval.evalGateAt.eq_1]
  rfl

@[simp] theorem eval_paperOrHead (input : Bitstring 2) :
    DagCircuit.eval paperOrHead input = (input 0 || input 1) := by
  rw [DagCircuit.eval.eq_1]
  change DagCircuit.eval.evalGateAt paperOrHead input 0 _ = _
  rw [DagCircuit.eval.evalGateAt.eq_1]
  rfl

theorem paperNotHead_noConst :
    ∀ gate, noConstDAGGate (paperNotHead.gate gate) := by
  intro gate
  fin_cases gate
  trivial

theorem paperAndHead_noConst :
    ∀ gate, noConstDAGGate (paperAndHead.gate gate) := by
  intro gate
  fin_cases gate
  trivial

theorem paperOrHead_noConst :
    ∀ gate, noConstDAGGate (paperOrHead.gate gate) := by
  intro gate
  fin_cases gate
  trivial

private def binaryHeadInputs {inputBits : Nat}
    (left right : DagCircuit inputBits) : Fin 2 -> DagCircuit inputBits :=
  fun index => Fin.cases left (fun _ => right) index

@[simp] private theorem binaryHeadInputs_zero {inputBits : Nat}
    (left right : DagCircuit inputBits) :
    binaryHeadInputs left right (0 : Fin 2) = left := rfl

@[simp] private theorem binaryHeadInputs_one {inputBits : Nat}
    (left right : DagCircuit inputBits) :
    binaryHeadInputs left right (1 : Fin 2) = right := rfl

private abbrev TreeCircuit (inputBits : Nat) :=
  Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit inputBits

/-- Exact gate cost of the constant-free recursive tree compiler below. -/
def paperTreeGateCost {inputBits : Nat} : TreeCircuit inputBits -> Nat
  | .var _ => 0
  | .const _ => 2
  | .not child => paperTreeGateCost child + 1
  | .and left right =>
      paperTreeGateCost left + paperTreeGateCost right + 1
  | .or left right =>
      paperTreeGateCost left + paperTreeGateCost right + 1

/-- Compile a tree circuit to the frozen DAG representation while replacing
Boolean constants by the existing two-gate constant-free gadgets. -/
noncomputable def paperTreeDAG (inputBits : Nat) (hpositive : 0 < inputBits) :
    TreeCircuit inputBits -> DagCircuit inputBits
  | .var index => inputProj index
  | .const value => paperBasisConstantDAG inputBits hpositive value
  | .not child =>
      substInputs paperNotHead (fun _ => paperTreeDAG inputBits hpositive child)
  | .and left right =>
      substInputs paperAndHead
        (binaryHeadInputs
          (paperTreeDAG inputBits hpositive left)
          (paperTreeDAG inputBits hpositive right))
  | .or left right =>
      substInputs paperOrHead
        (binaryHeadInputs
          (paperTreeDAG inputBits hpositive left)
          (paperTreeDAG inputBits hpositive right))

/-- Exact semantics of the constant-free tree compiler. -/
theorem eval_paperTreeDAG
    {inputBits : Nat} (hpositive : 0 < inputBits)
    (circuit : TreeCircuit inputBits) (input : Bitstring inputBits) :
    DagCircuit.eval (paperTreeDAG inputBits hpositive circuit) input =
      Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.eval circuit input := by
  induction circuit with
  | var index => rfl
  | const value =>
      simp [paperTreeDAG,
        Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.eval]
  | not child ih =>
      simp [paperTreeDAG,
        Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.eval, ih]
  | and left right ihLeft ihRight =>
      rw [paperTreeDAG, eval_substInputs, eval_paperAndHead]
      change
        (DagCircuit.eval (paperTreeDAG inputBits hpositive left) input &&
          DagCircuit.eval (paperTreeDAG inputBits hpositive right) input) =
        (Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.eval left input &&
          Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.eval right input)
      rw [ihLeft, ihRight]
  | or left right ihLeft ihRight =>
      rw [paperTreeDAG, eval_substInputs, eval_paperOrHead]
      change
        (DagCircuit.eval (paperTreeDAG inputBits hpositive left) input ||
          DagCircuit.eval (paperTreeDAG inputBits hpositive right) input) =
        (Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.eval left input ||
          Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.eval right input)
      rw [ihLeft, ihRight]

/-- Every gate produced by the tree compiler is in the constant-free paper
basis. -/
theorem paperTreeDAG_noConst
    {inputBits : Nat} (hpositive : 0 < inputBits)
    (circuit : TreeCircuit inputBits) :
    ∀ gate,
      noConstDAGGate ((paperTreeDAG inputBits hpositive circuit).gate gate) := by
  induction circuit with
  | var index =>
      intro gate
      exact Fin.elim0 gate
  | const value =>
      exact paperBasisConstantDAG_noConst inputBits hpositive value
  | not child ih =>
      apply substInputs_noConst
      · exact paperNotHead_noConst
      · intro index
        fin_cases index
        exact ih
  | and left right ihLeft ihRight =>
      apply substInputs_noConst
      · exact paperAndHead_noConst
      · intro index
        fin_cases index
        · exact ihLeft
        · exact ihRight
  | or left right ihLeft ihRight =>
      apply substInputs_noConst
      · exact paperOrHead_noConst
      · intro index
        fin_cases index
        · exact ihLeft
        · exact ihRight

/-- The recursive cost above is the exact number of internal DAG gates. -/
@[simp]
theorem paperTreeDAG_gates
    {inputBits : Nat} (hpositive : 0 < inputBits)
    (circuit : TreeCircuit inputBits) :
    (paperTreeDAG inputBits hpositive circuit).gates =
      paperTreeGateCost circuit := by
  induction circuit with
  | var index => rfl
  | const value => rfl
  | not child ih =>
      simp [paperTreeDAG, paperTreeGateCost, substInputs,
        substInputsWithBundle, bundleOfFamily_gates, ih, paperNotHead]
  | and left right ihLeft ihRight =>
      simp [paperTreeDAG, paperTreeGateCost, substInputs,
        substInputsWithBundle, bundleOfFamily_gates, binaryHeadInputs,
        paperAndHead, ihLeft, ihRight, Fin.sum_univ_succ]
  | or left right ihLeft ihRight =>
      simp [paperTreeDAG, paperTreeGateCost, substInputs,
        substInputsWithBundle, bundleOfFamily_gates, binaryHeadInputs,
        paperOrHead, ihLeft, ihRight, Fin.sum_univ_succ]
/-- A constant-free DAG for an arbitrary Boolean function on a fixed positive
input length.  This semantic truth-table compiler is finite but intentionally
does not claim the small gate count of the DPTW finite-field coordinate map. -/
noncomputable def paperTruthTableDAG
    (inputBits : Nat) (hpositive : 0 < inputBits)
    (function : Bitstring inputBits -> Bool) : DagCircuit inputBits :=
  paperTreeDAG inputBits hpositive
    (Pnp3.Internal.PsubsetPpoly.Simulation.Boolcube.Circuit.truthTableCircuit
      function)

@[simp]
theorem eval_paperTruthTableDAG
    (inputBits : Nat) (hpositive : 0 < inputBits)
    (function : Bitstring inputBits -> Bool) (input : Bitstring inputBits) :
    DagCircuit.eval (paperTruthTableDAG inputBits hpositive function) input =
      function input := by
  rw [paperTruthTableDAG, eval_paperTreeDAG]
  exact
    Pnp3.Internal.PsubsetPpoly.Simulation.Boolcube.Circuit.eval_truthTableCircuit
      function input

theorem paperTruthTableDAG_noConst
    (inputBits : Nat) (hpositive : 0 < inputBits)
    (function : Bitstring inputBits -> Bool) :
    ∀ gate,
      noConstDAGGate
        ((paperTruthTableDAG inputBits hpositive function).gate gate) :=
  paperTreeDAG_noConst hpositive _

/-- Flat standard-DAG form of the semantic constant-free compiler. -/
noncomputable def paperTruthTableCircuit
    (inputBits : Nat) (hpositive : 0 < inputBits)
    (function : Bitstring inputBits -> Bool) : FlatCircuit inputBits :=
  FlatCircuit.ofDag (paperTruthTableDAG inputBits hpositive function)

theorem paperTruthTableCircuit_usesOnlyAndOrNot
    (inputBits : Nat) (hpositive : 0 < inputBits)
    (function : Bitstring inputBits -> Bool) :
    (paperTruthTableCircuit inputBits hpositive function).UsesOnlyAndOrNot := by
  apply ofDag_usesOnlyAndOrNot_of_noConst
  exact paperTruthTableDAG_noConst inputBits hpositive function

/-- Exact (semantic, not asymptotically small) gate count of the generic
truth-table compiler. -/
theorem paperTruthTableCircuit_gateCount
    (inputBits : Nat) (hpositive : 0 < inputBits)
    (function : Bitstring inputBits -> Bool) :
    (paperTruthTableCircuit inputBits hpositive function).gateCount =
      paperTreeGateCost
        (Pnp3.Internal.PsubsetPpoly.Simulation.Boolcube.Circuit.truthTableCircuit
          function) := by
  exact paperTreeDAG_gates hpositive _

@[simp]
theorem eval_paperTruthTableCircuit
    (inputBits : Nat) (hpositive : 0 < inputBits)
    (function : Bitstring inputBits -> Bool) (input : Bitstring inputBits) :
    (paperTruthTableCircuit inputBits hpositive function).eval input =
      function input := by
  change DagCircuit.eval
    ((FlatCircuit.ofDag
      (paperTruthTableDAG inputBits hpositive function)).toDag) input = _
  rw [FlatCircuit.toDag_ofDag]
  exact eval_paperTruthTableDAG inputBits hpositive function input

/-! ## Packaging an actual coordinate primitive -/

/-- The Boolean function on joint `(seed,index)` inputs associated to an
arbitrary truth-table generator. -/
def jointCoordinateFunction {n seedBits : Nat}
    (generate : FiniteBitTape seedBits -> TruthTable n)
    (input : Bitstring (seedBits + n)) : Bool :=
  generate
    (fun seedIndex => input (Fin.castAdd n seedIndex))
    (StreamingMagnification.FixedBitstringCodec.rank
      (fun inputIndex => input (Fin.natAdd seedBits inputIndex)))

/-- Every explicit finite generator has a genuine constant-free joint
coordinate circuit at positive joint input length.  The construction is
semantic; downstream quantitative uses must separately bound its gate count. -/
noncomputable def coordinatePrimitiveOfGenerate
    {n seedBits : Nat} (hpositive : 0 < seedBits + n)
    (generate : FiniteBitTape seedBits -> TruthTable n) :
    DPTWCoordinatePrimitive n seedBits where
  generate := generate
  jointCircuit := paperTruthTableCircuit (seedBits + n) hpositive
    (jointCoordinateFunction generate)
  usesOnlyAndOrNot :=
    paperTruthTableCircuit_usesOnlyAndOrNot (seedBits + n) hpositive _
  jointCircuit_eval := by
    intro seed index
    rw [eval_paperTruthTableCircuit]
    unfold jointCoordinateFunction
    have hseed :
        (fun seedIndex =>
          Fin.addCases seed (lexInput n index)
            (Fin.castAdd n seedIndex)) = seed := by
      funext seedIndex
      simp
    have hinput :
        (fun inputIndex =>
          Fin.addCases seed (lexInput n index)
            (Fin.natAdd seedBits inputIndex)) = lexInput n index := by
      funext inputIndex
      simp
    rw [hseed, hinput,
      StreamingMagnification.FixedBitstringCodec.rank_lexInput]

/-- Exact gate identity for the generic primitive wrapper.  It deliberately
exposes that this fallback uses the semantic truth-table compiler rather than
the small finite-field coordinate circuit of DPTW Claim 3.11. -/
theorem coordinatePrimitiveOfGenerate_jointCircuit_gateCount
    {n seedBits : Nat} (hpositive : 0 < seedBits + n)
    (generate : FiniteBitTape seedBits -> TruthTable n) :
    (coordinatePrimitiveOfGenerate hpositive generate).jointCircuit.gateCount =
      paperTreeGateCost
        (Pnp3.Internal.PsubsetPpoly.Simulation.Boolcube.Circuit.truthTableCircuit
          (jointCoordinateFunction generate)) := by
  exact paperTruthTableCircuit_gateCount (seedBits + n) hpositive _

/-- The explicit dyadic product source as a `DPTWCoordinatePrimitive`. -/
noncomputable def dyadicProductPrimitive
    (n blockBits falseCount : Nat) (hpositive : 0 < blockBits) :
    DPTWCoordinatePrimitive n ((2 ^ n) * blockBits) :=
  coordinatePrimitiveOfGenerate (by
    have hseed : 0 < (2 ^ n) * blockBits := Nat.mul_pos (pow_pos (by omega) _) hpositive
    omega)
    (dyadicProductSource (2 ^ n) blockBits falseCount)

@[simp]
theorem dyadicProductPrimitive_generate
    (n blockBits falseCount : Nat) (hpositive : 0 < blockBits) :
    (dyadicProductPrimitive n blockBits falseCount hpositive).generate =
      dyadicProductSource (2 ^ n) blockBits falseCount :=
  rfl

/-- Exact `A` law needed by the one-round theorem, with substantially more
independence than required. -/
theorem dyadicHalfProductPrimitive_patternUnbiased
    (n blockBits q : Nat) (hpositive : 0 < blockBits) :
    IsKWisePatternUnbiased q
      (dyadicProductPrimitive n blockBits (2 ^ (blockBits - 1))
        hpositive).generate := by
  exact dyadicHalfProductSource_isKWisePatternUnbiased
    (2 ^ n) blockBits q hpositive

/-- Exact `B` law needed by the one-round theorem. -/
theorem dyadicProductPrimitive_patternFalseBiased
    (n blockBits falseCount q : Nat) (hpositive : 0 < blockBits)
    (hcount : falseCount ≤ 2 ^ blockBits) :
    IsKWisePatternFalseBiased q (dyadicFalseMass blockBits falseCount)
      (dyadicProductPrimitive n blockBits falseCount hpositive).generate := by
  exact dyadicProductSource_isKWisePatternFalseBiased
    (2 ^ n) blockBits falseCount q hcount

/-! ## Exact marginal and the complete finite A/B package -/

/-- The true marginal of one dyadic product coordinate is exactly `1-p`. -/
theorem dyadicProductSource_uniformCoordinateMarginal
    (coordinates blockBits falseCount : Nat)
    (hcount : falseCount ≤ 2 ^ blockBits)
    (coordinate : Fin coordinates) :
    uniformPredicateAverage (fun seed :
        FiniteBitTape (coordinates * blockBits) =>
      dyadicProductSource coordinates blockBits falseCount seed coordinate) =
      1 - dyadicFalseMass blockBits falseCount := by
  let support : Finset (Fin coordinates) := {coordinate}
  let pattern : LocalAssignment support := fun _ => true
  have hpattern :=
    dyadicProductSource_isKWisePatternFalseBiased
      coordinates blockBits falseCount 1 hcount
      support (by simp [support]) pattern
  calc
    uniformPredicateAverage (fun seed :
        FiniteBitTape (coordinates * blockBits) =>
      dyadicProductSource coordinates blockBits falseCount seed coordinate) =
      finiteAverage (fun seed : FiniteBitTape (coordinates * blockBits) =>
        localPatternIndicator support pattern
          (dyadicProductSource coordinates blockBits falseCount seed)) := by
      unfold uniformPredicateAverage finiteAverage
      congr 1
      apply Finset.sum_congr rfl
      intro seed _
      unfold boolIndicator localPatternIndicator
      dsimp only
      cases hvalue :
          dyadicProductSource coordinates blockBits falseCount seed coordinate
      · rw [if_neg (by simp)]
        rw [if_neg]
        intro hequal
        have hcoordinate := congrFun hequal
          (⟨coordinate, by simp [support]⟩ : support)
        change
          dyadicProductSource coordinates blockBits falseCount seed coordinate =
            true at hcoordinate
        rw [hvalue] at hcoordinate
        contradiction
      · rw [if_pos (by simp)]
        rw [if_pos]
        funext localCoordinate
        have hmem := localCoordinate.property
        change (localCoordinate : Fin coordinates) ∈
          ({coordinate} : Finset (Fin coordinates)) at hmem
        have heq : (localCoordinate : Fin coordinates) = coordinate :=
          Finset.mem_singleton.mp hmem
        change dyadicProductSource coordinates blockBits falseCount seed
          localCoordinate = true
        rw [heq, hvalue]
    _ = localPatternProductMass
        (dyadicFalseMass blockBits falseCount) pattern := hpattern
    _ = 1 - dyadicFalseMass blockBits falseCount := by
      simp [localPatternProductMass, support, pattern]

/-- The primitive wrapper preserves the exact true marginal. -/
theorem dyadicProductPrimitive_uniformCoordinateMarginal
    (n blockBits falseCount : Nat) (hpositive : 0 < blockBits)
    (hcount : falseCount ≤ 2 ^ blockBits)
    (coordinate : Fin (2 ^ n)) :
    uniformPredicateAverage (fun seed :
        FiniteBitTape ((2 ^ n) * blockBits) =>
      (dyadicProductPrimitive n blockBits falseCount hpositive).generate
        seed coordinate) =
      1 - dyadicFalseMass blockBits falseCount := by
  exact dyadicProductSource_uniformCoordinateMarginal
    (2 ^ n) blockBits falseCount hcount coordinate

/-- The exact finite lower-layer input consumed by the current one-round and
zero-tail theorems.  Both primitives use the same explicit seed length
`2^n * blockBits`; `A` is `4m`-wise pattern-unbiased, `B` is `2m`-wise
false-biased with mass `p`, and every `B` coordinate has true marginal
`1-p`. -/
theorem dyadicDPTWPair_exactLaws
    (n blockBits falseCount m : Nat) (hpositive : 0 < blockBits)
    (hcount : falseCount ≤ 2 ^ blockBits) :
    IsKWisePatternUnbiased (4 * m)
        (dyadicProductPrimitive n blockBits (2 ^ (blockBits - 1))
          hpositive).generate ∧
      IsKWisePatternFalseBiased (2 * m)
        (dyadicFalseMass blockBits falseCount)
        (dyadicProductPrimitive n blockBits falseCount hpositive).generate ∧
      ∀ coordinate : Fin (2 ^ n),
        uniformPredicateAverage (fun seed :
            FiniteBitTape ((2 ^ n) * blockBits) =>
          (dyadicProductPrimitive n blockBits falseCount hpositive).generate
            seed coordinate) =
          1 - dyadicFalseMass blockBits falseCount := by
  refine ⟨?_, ?_, ?_⟩
  · exact dyadicHalfProductPrimitive_patternUnbiased
      n blockBits (4 * m) hpositive
  · exact dyadicProductPrimitive_patternFalseBiased
      n blockBits falseCount (2 * m) hpositive hcount
  · exact dyadicProductPrimitive_uniformCoordinateMarginal
      n blockBits falseCount hpositive hcount

/-! ## Direct instantiation of the concrete hybrid theorem -/

/-- The existing concrete uFBDD hybrid theorem instantiated with the explicit
dyadic A/B pair above.  This closes all finite probability premises and keeps
the two honest quantitative defects visible in the chosen primitives:
`2^n * blockBits` seed bits per primitive block and the semantic joint-circuit
gate cost recorded by `coordinatePrimitiveOfGenerate_jointCircuit_gateCount`.
-/
theorem abs_uniformAverage_sub_dyadicZeroTailAverage_le
    {n m : Nat} (B : FiniteUnambiguousFBDD (2 ^ n))
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hunambiguous : B.IsUnambiguous)
    (hreadsAll : ∀ input (path : B.AcceptingPath input),
      path.walk.queryVars = Finset.univ)
    (blockBits falseCount : Nat) (hpositive : 0 < blockBits)
    (hcount : falseCount ≤ 2 ^ blockBits)
    (levelsAfterFirst : Nat)
    (test : TruthTable n -> Bool)
    (hTest : ∀ input,
      B.ratAcceptanceIndicator input = boolIndicator (test input)) :
    let a := dyadicProductPrimitive n blockBits
      (2 ^ (blockBits - 1)) hpositive
    let b := dyadicProductPrimitive n blockBits falseCount hpositive
    let p := dyadicFalseMass blockBits falseCount
    |finiteAverage B.ratAcceptanceIndicator -
        uniformPredicateAverage
          (fun pair : TruthTable n ×
              FiniteBitTape
                ((levelsAfterFirst + 1) *
                  (((2 ^ n) * blockBits) + ((2 ^ n) * blockBits))) =>
            test (dptwZeroTailGenerate a b levelsAfterFirst pair.2))| ≤
      ((levelsAfterFirst + 1 : Nat) : Rat) *
          (Fintype.card B.Vertex : Rat) * p ^ m +
        (2 ^ n : Rat) * (1 - p) ^ (levelsAfterFirst + 1) := by
  dsimp only
  have hlaws := dyadicDPTWPair_exactLaws
    n blockBits falseCount m hpositive hcount
  apply FiniteAffineRestrictionHybrid.abs_uniformAverage_sub_dptwZeroTailAverage_le
    B hreadOnce hunambiguous hreadsAll
      (dyadicProductPrimitive n blockBits (2 ^ (blockBits - 1)) hpositive)
      (dyadicProductPrimitive n blockBits falseCount hpositive)
      levelsAfterFirst (dyadicFalseMass blockBits falseCount)
  · unfold dyadicFalseMass
    positivity
  · exact hlaws.1
  · exact hlaws.2.1
  · exact hTest
  · exact hlaws.2.2

end DPTWFiniteBooleanPrimitives

end OneTapeMagnification
end Frontier
end Pnp4
