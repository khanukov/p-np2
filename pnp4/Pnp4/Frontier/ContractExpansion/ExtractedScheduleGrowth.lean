import Pnp4.Frontier.ContractExpansion.NoSolverContrapositive

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-!
# Polynomial-schedule reconciliation

Block 9d of the downstream decision→search extraction.

The exact-schedule contrapositive (#1510) gives `NoExtractedScheduleSolver →
¬ PpolyDAG`, but the no-solver hypothesis is stated at the *weird extracted*
schedule `extractedSolverSizeBound codec c`.  For a clean public statement we want
the standard polynomial target `NoPolynomialBoundedSearchSolver` (no solver at any
`(instanceBits n)^d + d`).  This file bridges the two **under explicit polynomial
growth assumptions** on the codec (`witnessBits` and `treeMCSPPrefixM` polynomial in
the truth-table length `tableLen n`):

* a small `PolyBoundedInTable` API (poly-bounded in `tableLen n`, closed under
  `+`, `*`, `^const`, constants) with a conversion to the `T^d + d` shape;
* `BoundedSearchSolver` monotonicity in its size schedule;
* under the growth assumptions, `extractedSolverSizeBound codec c` is polynomial in
  `tableLen n`, hence `NoPolynomialBoundedSearchSolver → NoExtractedScheduleSolver`;
* combined with #1510: `NoPolynomialBoundedSearchSolver + growth → ¬ PpolyDAG`.

Scope discipline — polynomial reconciliation only:

* the growth assumptions and the no-poly-solver hypothesis are **explicit**;
* **no** `SearchMCSPMagnificationContract`, `VerifiedNPDAGLowerBoundSource`,
  NP-membership, endpoint, or `P ≠ NP` consequence.
-/

variable {threshold : Nat → Nat}

private theorem one_le_tableLen (n : Nat) : 1 ≤ Pnp3.Models.Partial.tableLen n :=
  Nat.one_le_two_pow

/-! ### A small "polynomially bounded in `tableLen`" API -/

/-- `f` is polynomially bounded in the truth-table length `tableLen n`.  Phrased with
`(tableLen n + 1)^k` (base `≥ 2`) so the closure lemmas have no edge cases. -/
def PolyBoundedInTable (f : Nat → Nat) : Prop :=
  ∃ k : Nat, ∀ n : Nat, f n ≤ (Pnp3.Models.Partial.tableLen n + 1) ^ k

namespace PolyBoundedInTable

theorem of_le {f g : Nat → Nat} (hfg : ∀ n, f n ≤ g n) (hg : PolyBoundedInTable g) :
    PolyBoundedInTable f := by
  obtain ⟨k, hk⟩ := hg
  exact ⟨k, fun n => le_trans (hfg n) (hk n)⟩

theorem const (c : Nat) : PolyBoundedInTable (fun _ => c) := by
  refine ⟨c, fun n => ?_⟩
  calc c ≤ 2 ^ c := Nat.le_of_lt (Nat.lt_two_pow_self)
    _ ≤ (Pnp3.Models.Partial.tableLen n + 1) ^ c :=
        Nat.pow_le_pow_left (by have := one_le_tableLen n; omega) c

theorem tableLen_pow (k : Nat) :
    PolyBoundedInTable (fun n => (Pnp3.Models.Partial.tableLen n) ^ k) :=
  ⟨k, fun n => Nat.pow_le_pow_left (Nat.le_succ (Pnp3.Models.Partial.tableLen n)) k⟩

theorem add {f g : Nat → Nat} (hf : PolyBoundedInTable f) (hg : PolyBoundedInTable g) :
    PolyBoundedInTable (fun n => f n + g n) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨max a b + 1, fun n => ?_⟩
  have hT : 2 ≤ Pnp3.Models.Partial.tableLen n + 1 := by have := one_le_tableLen n; omega
  have h1 : f n ≤ (Pnp3.Models.Partial.tableLen n + 1) ^ (max a b) :=
    le_trans (ha n) (Nat.pow_le_pow_right (by omega) (le_max_left a b))
  have h2 : g n ≤ (Pnp3.Models.Partial.tableLen n + 1) ^ (max a b) :=
    le_trans (hb n) (Nat.pow_le_pow_right (by omega) (le_max_right a b))
  calc f n + g n ≤ (Pnp3.Models.Partial.tableLen n + 1) ^ (max a b)
          + (Pnp3.Models.Partial.tableLen n + 1) ^ (max a b) := by omega
    _ = 2 * (Pnp3.Models.Partial.tableLen n + 1) ^ (max a b) := by ring
    _ ≤ (Pnp3.Models.Partial.tableLen n + 1) * (Pnp3.Models.Partial.tableLen n + 1) ^ (max a b) :=
        Nat.mul_le_mul_right _ hT
    _ = (Pnp3.Models.Partial.tableLen n + 1) ^ (max a b + 1) := (pow_succ' _ _).symm

theorem mul {f g : Nat → Nat} (hf : PolyBoundedInTable f) (hg : PolyBoundedInTable g) :
    PolyBoundedInTable (fun n => f n * g n) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨a + b, fun n => ?_⟩
  calc f n * g n ≤ (Pnp3.Models.Partial.tableLen n + 1) ^ a
          * (Pnp3.Models.Partial.tableLen n + 1) ^ b := Nat.mul_le_mul (ha n) (hb n)
    _ = (Pnp3.Models.Partial.tableLen n + 1) ^ (a + b) := (pow_add _ _ _).symm

theorem pow {f : Nat → Nat} (hf : PolyBoundedInTable f) (c : Nat) :
    PolyBoundedInTable (fun n => (f n) ^ c) := by
  obtain ⟨a, ha⟩ := hf
  refine ⟨a * c, fun n => ?_⟩
  calc (f n) ^ c ≤ ((Pnp3.Models.Partial.tableLen n + 1) ^ a) ^ c :=
        Nat.pow_le_pow_left (ha n) c
    _ = (Pnp3.Models.Partial.tableLen n + 1) ^ (a * c) := by rw [← pow_mul]

/-- `(T+1)^k ≤ T^(2k) + 2^k` for `T ≥ 1`. -/
private theorem pow_succ_le (T k : Nat) (hT : 1 ≤ T) :
    (T + 1) ^ k ≤ T ^ (2 * k) + 2 ^ k := by
  rcases Nat.lt_or_ge T 2 with hT2 | hT2
  · interval_cases T
    · show (2 : Nat) ^ k ≤ 1 ^ (2 * k) + 2 ^ k
      rw [Nat.one_pow]; omega
  · have h2T : 2 ^ k ≤ T ^ k := Nat.pow_le_pow_left hT2 k
    calc (T + 1) ^ k ≤ (2 * T) ^ k := Nat.pow_le_pow_left (by omega) k
      _ = 2 ^ k * T ^ k := by rw [mul_pow]
      _ ≤ T ^ k * T ^ k := Nat.mul_le_mul h2T (le_refl _)
      _ = T ^ (2 * k) := by rw [← pow_add, two_mul]
      _ ≤ T ^ (2 * k) + 2 ^ k := Nat.le_add_right _ _

/-- Convert a `(tableLen n + 1)^k` bound to the standard `T^d + d` shape. -/
theorem powAdd {f : Nat → Nat} (hf : PolyBoundedInTable f) :
    ∃ d, ∀ n, f n ≤ (Pnp3.Models.Partial.tableLen n) ^ d + d := by
  obtain ⟨k, hk⟩ := hf
  refine ⟨2 * k + 2 ^ k, fun n => ?_⟩
  have hT : 1 ≤ Pnp3.Models.Partial.tableLen n := one_le_tableLen n
  have hstep := pow_succ_le (Pnp3.Models.Partial.tableLen n) k hT
  have hmono : (Pnp3.Models.Partial.tableLen n) ^ (2 * k)
      ≤ (Pnp3.Models.Partial.tableLen n) ^ (2 * k + 2 ^ k) :=
    Nat.pow_le_pow_right hT (Nat.le_add_right (2 * k) (2 ^ k))
  calc f n ≤ (Pnp3.Models.Partial.tableLen n + 1) ^ k := hk n
    _ ≤ (Pnp3.Models.Partial.tableLen n) ^ (2 * k) + 2 ^ k := hstep
    _ ≤ (Pnp3.Models.Partial.tableLen n) ^ (2 * k + 2 ^ k) + (2 * k + 2 ^ k) :=
        Nat.add_le_add hmono (Nat.le_add_left (2 ^ k) (2 * k))

end PolyBoundedInTable

/-! ### Growth assumptions and the polynomial bridge -/

/-- Explicit polynomial growth assumptions for a codec: both the witness length and
the parser's ambient length are polynomial in the truth-table length. -/
structure TreeMCSPExtractionGrowthAssumptions
    (codec : TreeCircuitWitnessCodec threshold) where
  witness_poly : PolyBoundedInTable (codec.witnessBits)
  ambient_poly : PolyBoundedInTable (treeMCSPPrefixM codec)

/-- Under the growth assumptions, the extracted size schedule is polynomial in the
truth-table length. -/
theorem polyBoundedInTable_extractedSolverSizeBound
    (codec : TreeCircuitWitnessCodec threshold)
    (hGrowth : TreeMCSPExtractionGrowthAssumptions codec)
    (c : Nat) :
    PolyBoundedInTable (extractedSolverSizeBound codec c) := by
  have hW := hGrowth.witness_poly
  have hM := hGrowth.ambient_poly
  have :=
    (hW.mul
      (((hM.pow c).add (PolyBoundedInTable.const c)).add
        ((PolyBoundedInTable.const 2).mul hM))).add (PolyBoundedInTable.const 1)
  exact this

/-- Monotonicity of `BoundedSearchSolver` in its size schedule: a solver at a smaller
schedule is a solver at any larger one. -/
theorem nonempty_boundedSearchSolver_mono_sizeBound
    {problem : SearchMCSPCompressionProblem} {C : CircuitFamilyClass}
    {small big : Nat → Nat}
    (h : Nonempty (BoundedSearchSolver problem C small))
    (hle : ∀ n, small n ≤ big n) :
    Nonempty (BoundedSearchSolver problem C big) := by
  obtain ⟨s⟩ := h
  exact ⟨{ outputCircuit := s.outputCircuit
           size_le := fun n i => le_trans (s.size_le n i) (hle n)
           solves := s.solves }⟩

/-- The standard polynomial weak lower-bound target: no bounded search solver exists
at any polynomial schedule `(instanceBits n)^d + d`. -/
def NoPolynomialBoundedSearchSolver
    (codec : TreeCircuitWitnessCodec threshold) : Prop :=
  ∀ d : Nat,
    ¬ Nonempty
      (BoundedSearchSolver (treeProblem codec) C_DAG
        (fun n => (Pnp3.Models.Partial.tableLen n) ^ d + d))

/-- Under the growth assumptions, no polynomial-schedule solver implies no
extracted-schedule solver. -/
theorem noExtractedScheduleSolver_of_noPolynomial
    (codec : TreeCircuitWitnessCodec threshold)
    (hGrowth : TreeMCSPExtractionGrowthAssumptions codec)
    (hNoPoly : NoPolynomialBoundedSearchSolver codec) :
    NoExtractedScheduleSolver codec := by
  intro c hSolver
  obtain ⟨d, hd⟩ := (polyBoundedInTable_extractedSolverSizeBound codec hGrowth c).powAdd
  exact hNoPoly d (nonempty_boundedSearchSolver_mono_sizeBound hSolver hd)

/-- **Polynomial-target contrapositive.**  Under the growth assumptions, no
polynomial-size bounded search solver implies the prefix-extension language is not in
`PpolyDAG`. -/
theorem not_PpolyDAG_prefixExtension_of_noPolynomialBoundedSearchSolver
    (codec : TreeCircuitWitnessCodec threshold)
    (hGrowth : TreeMCSPExtractionGrowthAssumptions codec)
    (hNoPoly : NoPolynomialBoundedSearchSolver codec) :
    ¬ Pnp3.ComplexityInterfaces.PpolyDAG
        (PrefixExtensionLanguage (treeMCSPConcretePrefixParser threshold codec)) :=
  not_PpolyDAG_prefixExtension_of_noExtractedScheduleSolver codec
    (noExtractedScheduleSolver_of_noPolynomial codec hGrowth hNoPoly)

end ContractExpansion
end Frontier
end Pnp4
