import Pnp4.Frontier.OneTapeMagnification.DPTWStructuredFieldCoordinatePrimitive
import Pnp4.Frontier.OneTapeMagnification.DPTWUnambiguousFBDDHybridBridge

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Structured finite-field DPTW hybrid capstone

This module instantiates the finite unambiguous-FBDD hybrid with the common-
seed structured `GF(2^d)` coordinate primitives.  It also packages the exact
zero-tail joint circuit as a genuine nonuniform `DAGLocalGenerator` at a fully
displayed standard-DAG threshold.

No lower-bound source or target contract is introduced here.  The
architecture-dependent loss is the honest vertex-cardinality factor of the
input unambiguous FBDD; the explicit level multiplier and survivor term also
remain in the final estimate.
-/

noncomputable section

open StreamingMagnification
open StreamingMagnification.TotalSearch
open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open DPTWStructuredFieldCoordinatePrimitive

namespace DPTWStructuredHybridCapstone

/-! ## Closed-form budgets -/

/-- Horner/zero-prefix budget shared by the two structured primitives before
the final prefix decoder is added. -/
def structuredPrimitiveHornerGateBudget (d m : Nat) : Nat :=
  (4 * m) * (d * (6 + 6 * (d * d)))

/-- Full joint `(all level seeds, one truth-table coordinate)` circuit budget.
The `5 * levelsAfterFirst` term is the exact cost of the recursive Boolean
heads `a XOR (b AND tail)`. -/
def structuredZeroTailJointGateBudget
    (d m tailBits levelsAfterFirst : Nat) : Nat :=
  (levelsAfterFirst + 1) *
      (2 * structuredPrimitiveHornerGateBudget d m + 5 + tailBits) +
    5 * levelsAfterFirst

/-- Full fixed-seed standard-DAG threshold.  The last term is the exact
two-gate-per-seed-bit hardwiring cost for `2 * (levelsAfterFirst + 1)` common
primitive seed blocks, each of length `(4*m+1)*d`. -/
def structuredZeroTailHardwiredGateBudget
    (d m tailBits levelsAfterFirst : Nat) : Nat :=
  structuredZeroTailJointGateBudget d m tailBits levelsAfterFirst +
    4 * (levelsAfterFirst + 1) * ((4 * m + 1) * d)

/-! ## Joint circuit and exact hardwiring -/

/-- The common-seed structured zero-tail circuit before fixing its seed. -/
def structuredZeroTailJointCircuit
    (d m tailBits levelsAfterFirst : Nat)
    (hd : 0 < d) (htail : tailBits <= d) :=
  dptwZeroTailJointCircuit
    (structuredUnbiasedPrimitive d m hd)
    (structuredDyadicPrimitive d m tailBits hd htail)
    levelsAfterFirst

/-- Exact DPTW gate identity for the structured joint circuit. -/
theorem structuredZeroTailJointCircuit_gateCount
    (d m tailBits levelsAfterFirst : Nat)
    (hd : 0 < d) (htail : tailBits <= d) :
    (structuredZeroTailJointCircuit d m tailBits levelsAfterFirst
        hd htail).gateCount =
      (levelsAfterFirst + 1) *
          ((structuredUnbiasedPrimitive d m hd).jointCircuit.gateCount +
            (structuredDyadicPrimitive d m tailBits hd htail).jointCircuit.gateCount) +
        5 * levelsAfterFirst := by
  exact dptwZeroTailJointCircuit_gateCount
    (structuredUnbiasedPrimitive d m hd)
    (structuredDyadicPrimitive d m tailBits hd htail)
    levelsAfterFirst

/-- Closed polynomial gate bound for the entire common-seed joint circuit. -/
theorem structuredZeroTailJointCircuit_gateCount_le
    (d m tailBits levelsAfterFirst : Nat)
    (hd : 0 < d) (htail : tailBits <= d) :
    (structuredZeroTailJointCircuit d m tailBits levelsAfterFirst
        hd htail).gateCount <=
      structuredZeroTailJointGateBudget d m tailBits levelsAfterFirst := by
  have ha :
      (structuredUnbiasedPrimitive d m hd).jointCircuit.gateCount <=
        structuredPrimitiveHornerGateBudget d m + 3 := by
    simpa [structuredUnbiasedPrimitive,
      structuredPrimitiveHornerGateBudget] using
      (structuredDyadicPrimitive_jointCircuit_gateCount_le
        d m 1 hd (by omega : 1 <= d))
  have hb :
      (structuredDyadicPrimitive d m tailBits hd htail).jointCircuit.gateCount <=
        structuredPrimitiveHornerGateBudget d m + (2 + tailBits) := by
    simpa [structuredPrimitiveHornerGateBudget] using
      (structuredDyadicPrimitive_jointCircuit_gateCount_le
        d m tailBits hd htail)
  calc
    (structuredZeroTailJointCircuit d m tailBits levelsAfterFirst
        hd htail).gateCount =
        (levelsAfterFirst + 1) *
            ((structuredUnbiasedPrimitive d m hd).jointCircuit.gateCount +
              (structuredDyadicPrimitive d m tailBits hd htail).jointCircuit.gateCount) +
          5 * levelsAfterFirst :=
      structuredZeroTailJointCircuit_gateCount
        d m tailBits levelsAfterFirst hd htail
    _ <= (levelsAfterFirst + 1) *
            ((structuredPrimitiveHornerGateBudget d m + 3) +
              (structuredPrimitiveHornerGateBudget d m + (2 + tailBits))) +
          5 * levelsAfterFirst := by
      exact Nat.add_le_add_right
        (Nat.mul_le_mul_left (levelsAfterFirst + 1)
          (Nat.add_le_add ha hb)) (5 * levelsAfterFirst)
    _ = structuredZeroTailJointGateBudget
          d m tailBits levelsAfterFirst := by
      unfold structuredZeroTailJointGateBudget
      ring

/-- Exact standard-DAG gate count after fixing every common-seed bit. -/
theorem structuredZeroTailHardwired_gateCount
    (d m tailBits levelsAfterFirst : Nat)
    (hd : 0 < d) (htail : tailBits <= d)
    (seed : FiniteBitTape
      ((levelsAfterFirst + 1) *
        (structuredIndependence m * d + structuredIndependence m * d))) :
    (hardwireSeedCircuit hd
      (structuredZeroTailJointCircuit d m tailBits levelsAfterFirst hd htail)
      seed).gateCount =
      (levelsAfterFirst + 1) *
          ((structuredUnbiasedPrimitive d m hd).jointCircuit.gateCount +
            (structuredDyadicPrimitive d m tailBits hd htail).jointCircuit.gateCount) +
        5 * levelsAfterFirst +
        2 * ((levelsAfterFirst + 1) *
          (structuredIndependence m * d + structuredIndependence m * d)) := by
  exact dptwZeroTailHardwired_gateCount hd
    (structuredUnbiasedPrimitive d m hd)
    (structuredDyadicPrimitive d m tailBits hd htail)
    levelsAfterFirst seed

/-- Closed standard-DAG bound for every fixed seed. -/
theorem structuredZeroTailHardwired_gateCount_le
    (d m tailBits levelsAfterFirst : Nat)
    (hd : 0 < d) (htail : tailBits <= d)
    (seed : FiniteBitTape
      ((levelsAfterFirst + 1) *
        (structuredIndependence m * d + structuredIndependence m * d))) :
    (hardwireSeedCircuit hd
      (structuredZeroTailJointCircuit d m tailBits levelsAfterFirst hd htail)
      seed).gateCount <=
      structuredZeroTailHardwiredGateBudget
        d m tailBits levelsAfterFirst := by
  rw [structuredZeroTailHardwired_gateCount
    d m tailBits levelsAfterFirst hd htail seed]
  calc
    (levelsAfterFirst + 1) *
          ((structuredUnbiasedPrimitive d m hd).jointCircuit.gateCount +
            (structuredDyadicPrimitive d m tailBits hd htail).jointCircuit.gateCount) +
        5 * levelsAfterFirst +
        2 * ((levelsAfterFirst + 1) *
          (structuredIndependence m * d + structuredIndependence m * d)) =
      (structuredZeroTailJointCircuit d m tailBits levelsAfterFirst
          hd htail).gateCount +
        2 * ((levelsAfterFirst + 1) *
          (structuredIndependence m * d + structuredIndependence m * d)) := by
      rw [structuredZeroTailJointCircuit_gateCount]
    _ <= structuredZeroTailJointGateBudget d m tailBits levelsAfterFirst +
        2 * ((levelsAfterFirst + 1) *
          (structuredIndependence m * d + structuredIndependence m * d)) :=
      Nat.add_le_add_right
        (structuredZeroTailJointCircuit_gateCount_le
          d m tailBits levelsAfterFirst hd htail) _
    _ = structuredZeroTailHardwiredGateBudget
          d m tailBits levelsAfterFirst := by
      unfold structuredZeroTailHardwiredGateBudget structuredIndependence
      ring

/-! ## A genuine generator at the displayed threshold -/

/-- The exact threshold produced by the generic DPTW hardwiring wrapper,
before weakening to the closed budget above. -/
def structuredZeroTailRawThreshold
    (d m tailBits levelsAfterFirst : Nat)
    (hd : 0 < d) (htail : tailBits <= d) : Nat :=
  (structuredZeroTailJointCircuit d m tailBits levelsAfterFirst
      hd htail).gateCount +
    2 * ((levelsAfterFirst + 1) *
      (structuredIndependence m * d + structuredIndependence m * d))

/-- The generic exact-threshold generator, retained internally to transfer
its fixed-seed circuit witness to the displayed closed threshold. -/
def structuredZeroTailRawDAGLocalGenerator
    (d m tailBits levelsAfterFirst : Nat)
    (hd : 0 < d) (htail : tailBits <= d) :
    DAGLocalGenerator d
      (structuredZeroTailRawThreshold d m tailBits levelsAfterFirst
        hd htail) := by
  unfold structuredZeroTailRawThreshold structuredZeroTailJointCircuit
  exact dptwZeroTailDAGLocalGenerator hd
    (structuredUnbiasedPrimitive d m hd)
    (structuredDyadicPrimitive d m tailBits hd htail)
    levelsAfterFirst

@[simp]
theorem structuredZeroTailRawDAGLocalGenerator_seedBits
    (d m tailBits levelsAfterFirst : Nat)
    (hd : 0 < d) (htail : tailBits <= d) :
    (structuredZeroTailRawDAGLocalGenerator
      d m tailBits levelsAfterFirst hd htail).seedBits =
      (levelsAfterFirst + 1) *
        (structuredIndependence m * d + structuredIndependence m * d) := by
  rfl

theorem structuredZeroTailRawDAGLocalGenerator_generate
    (d m tailBits levelsAfterFirst : Nat)
    (hd : 0 < d) (htail : tailBits <= d)
    (seed : FiniteBitTape
      ((levelsAfterFirst + 1) *
        (structuredIndependence m * d + structuredIndependence m * d))) :
    (structuredZeroTailRawDAGLocalGenerator
        d m tailBits levelsAfterFirst hd htail).generate seed =
      dptwZeroTailGenerate
        (structuredUnbiasedPrimitive d m hd)
        (structuredDyadicPrimitive d m tailBits hd htail)
        levelsAfterFirst seed := by
  exact dptwZeroTailDAGLocalGenerator_generate hd
    (structuredUnbiasedPrimitive d m hd)
    (structuredDyadicPrimitive d m tailBits hd htail)
    levelsAfterFirst seed

theorem structuredZeroTailRawThreshold_le
    (d m tailBits levelsAfterFirst : Nat)
    (hd : 0 < d) (htail : tailBits <= d) :
    structuredZeroTailRawThreshold d m tailBits levelsAfterFirst hd htail <=
      structuredZeroTailHardwiredGateBudget
        d m tailBits levelsAfterFirst := by
  unfold structuredZeroTailRawThreshold
  calc
    (structuredZeroTailJointCircuit d m tailBits levelsAfterFirst
          hd htail).gateCount +
        2 * ((levelsAfterFirst + 1) *
          (structuredIndependence m * d + structuredIndependence m * d)) <=
      structuredZeroTailJointGateBudget d m tailBits levelsAfterFirst +
        2 * ((levelsAfterFirst + 1) *
          (structuredIndependence m * d + structuredIndependence m * d)) :=
      Nat.add_le_add_right
        (structuredZeroTailJointCircuit_gateCount_le
          d m tailBits levelsAfterFirst hd htail) _
    _ = structuredZeroTailHardwiredGateBudget
          d m tailBits levelsAfterFirst := by
      unfold structuredZeroTailHardwiredGateBudget structuredIndependence
      ring

/-- The final nonuniform local generator is typed directly at the displayed
closed standard-DAG threshold.  Its semantic generator is definitionally the
paper's zero-tail recurrence. -/
def structuredZeroTailDAGLocalGenerator
    (d m tailBits levelsAfterFirst : Nat)
    (hd : 0 < d) (htail : tailBits <= d) :
    DAGLocalGenerator d
      (structuredZeroTailHardwiredGateBudget
        d m tailBits levelsAfterFirst) where
  seedBits := (levelsAfterFirst + 1) *
    (structuredIndependence m * d + structuredIndependence m * d)
  generate := dptwZeroTailGenerate
    (structuredUnbiasedPrimitive d m hd)
    (structuredDyadicPrimitive d m tailBits hd htail)
    levelsAfterFirst
  image_easy := fun seed => by
    rcases (structuredZeroTailRawDAGLocalGenerator
        d m tailBits levelsAfterFirst hd htail).image_easy seed with
      ⟨circuit, hsize, hbasis, hcomputes⟩
    refine ⟨circuit,
      hsize.trans (structuredZeroTailRawThreshold_le
        d m tailBits levelsAfterFirst hd htail), hbasis, ?_⟩
    rw [structuredZeroTailRawDAGLocalGenerator_generate] at hcomputes
    exact hcomputes

@[simp]
theorem structuredZeroTailDAGLocalGenerator_seedBits
    (d m tailBits levelsAfterFirst : Nat)
    (hd : 0 < d) (htail : tailBits <= d) :
    (structuredZeroTailDAGLocalGenerator
      d m tailBits levelsAfterFirst hd htail).seedBits =
      (levelsAfterFirst + 1) *
        (structuredIndependence m * d + structuredIndependence m * d) := by
  rfl

/-- The common seed length in fully expanded form. -/
theorem structuredZeroTailDAGLocalGenerator_seedBits_eq
    (d m tailBits levelsAfterFirst : Nat)
    (hd : 0 < d) (htail : tailBits <= d) :
    (structuredZeroTailDAGLocalGenerator
      d m tailBits levelsAfterFirst hd htail).seedBits =
      2 * (levelsAfterFirst + 1) * ((4 * m + 1) * d) := by
  rw [structuredZeroTailDAGLocalGenerator_seedBits]
  unfold structuredIndependence
  ring

@[simp]
theorem structuredZeroTailDAGLocalGenerator_generate
    (d m tailBits levelsAfterFirst : Nat)
    (hd : 0 < d) (htail : tailBits <= d)
    (seed : FiniteBitTape
      ((levelsAfterFirst + 1) *
        (structuredIndependence m * d + structuredIndependence m * d))) :
    (structuredZeroTailDAGLocalGenerator
        d m tailBits levelsAfterFirst hd htail).generate seed =
      dptwZeroTailGenerate
        (structuredUnbiasedPrimitive d m hd)
        (structuredDyadicPrimitive d m tailBits hd htail)
        levelsAfterFirst seed := by
  rfl

/-! ## Fully instantiated finite hybrid -/

/-- The concrete unambiguous-FBDD hybrid for the structured common-seed
finite-field generator.  All bounded-independence and marginal premises are
discharged internally; the only semantic hypotheses are exactly those of the
existing program-level bridge. -/
theorem abs_uniformAverage_sub_structuredZeroTailGeneratorAverage_le
    {d m : Nat} (B : FiniteUnambiguousFBDD (2 ^ d))
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hunambiguous : B.IsUnambiguous)
    (hreadsAll : forall input (path : B.AcceptingPath input),
      path.walk.queryVars = Finset.univ)
    (tailBits : Nat) (hd : 0 < d) (htail : tailBits <= d)
    (levelsAfterFirst : Nat)
    (test : TruthTable d -> Bool)
    (hTest : forall input,
      B.ratAcceptanceIndicator input = boolIndicator (test input)) :
    let generator := structuredZeroTailDAGLocalGenerator
      d m tailBits levelsAfterFirst hd htail
    let p : Rat := 1 / (2 : Rat) ^ tailBits
    |finiteAverage B.ratAcceptanceIndicator -
        uniformPredicateAverage
          (fun pair : TruthTable d × FiniteBitTape generator.seedBits =>
            test (generator.generate pair.2))| <=
      ((levelsAfterFirst + 1 : Nat) : Rat) *
          (Fintype.card B.Vertex : Rat) * p ^ m +
        (2 ^ d : Rat) * (1 - p) ^ (levelsAfterFirst + 1) := by
  dsimp only
  have hlaws := structuredDPTWPair_exactLaws
    d m tailBits hd htail
  apply FiniteAffineRestrictionHybrid.abs_uniformAverage_sub_dptwZeroTailAverage_le
    B hreadOnce hunambiguous hreadsAll
      (structuredUnbiasedPrimitive d m hd)
      (structuredDyadicPrimitive d m tailBits hd htail)
      levelsAfterFirst (1 / (2 : Rat) ^ tailBits)
  · positivity
  · exact hlaws.1
  · exact hlaws.2.1
  · exact hTest
  · exact hlaws.2.2

/-- Seed-only presentation of the structured hybrid.  The extra uniformly
sampled truth table in the program-level product average is unused, so finite
product averaging removes it exactly. -/
theorem abs_uniformAverage_sub_structuredZeroTailGeneratorSeedAverage_le
    {d m : Nat} (B : FiniteUnambiguousFBDD (2 ^ d))
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hunambiguous : B.IsUnambiguous)
    (hreadsAll : forall input (path : B.AcceptingPath input),
      path.walk.queryVars = Finset.univ)
    (tailBits : Nat) (hd : 0 < d) (htail : tailBits <= d)
    (levelsAfterFirst : Nat)
    (test : TruthTable d -> Bool)
    (hTest : forall input,
      B.ratAcceptanceIndicator input = boolIndicator (test input)) :
    let generator := structuredZeroTailDAGLocalGenerator
      d m tailBits levelsAfterFirst hd htail
    let p : Rat := 1 / (2 : Rat) ^ tailBits
    |finiteAverage B.ratAcceptanceIndicator -
        uniformPredicateAverage
          (fun seed : FiniteBitTape generator.seedBits =>
            test (generator.generate seed))| <=
      ((levelsAfterFirst + 1 : Nat) : Rat) *
          (Fintype.card B.Vertex : Rat) * p ^ m +
        (2 ^ d : Rat) * (1 - p) ^ (levelsAfterFirst + 1) := by
  dsimp only
  let generator := structuredZeroTailDAGLocalGenerator
    d m tailBits levelsAfterFirst hd htail
  have hignore :
      uniformPredicateAverage
          (fun pair : Prod (TruthTable d) (FiniteBitTape generator.seedBits) =>
            test (generator.generate pair.2)) =
        uniformPredicateAverage
          (fun seed : FiniteBitTape generator.seedBits =>
            test (generator.generate seed)) := by
    exact uniformPredicateAverage_prod_ignore_left
      (Left := TruthTable d)
      (Right := FiniteBitTape generator.seedBits)
      (fun seed => test (generator.generate seed))
  have h :=
    abs_uniformAverage_sub_structuredZeroTailGeneratorAverage_le
      (d := d) (m := m)
      B hreadOnce hunambiguous hreadsAll tailBits hd htail
        levelsAfterFirst test hTest
  dsimp only at h
  change
    |finiteAverage B.ratAcceptanceIndicator -
        uniformPredicateAverage
          (fun pair : Prod (TruthTable d) (FiniteBitTape generator.seedBits) =>
            test (generator.generate pair.2))| <= _ at h
  rw [hignore] at h
  exact h

#print axioms structuredZeroTailJointCircuit_gateCount_le
#print axioms structuredZeroTailHardwired_gateCount_le
#print axioms structuredZeroTailRawThreshold_le
#print axioms structuredZeroTailDAGLocalGenerator
#print axioms abs_uniformAverage_sub_structuredZeroTailGeneratorAverage_le
#print axioms abs_uniformAverage_sub_structuredZeroTailGeneratorSeedAverage_le

end DPTWStructuredHybridCapstone

end

end OneTapeMagnification
end Frontier
end Pnp4
