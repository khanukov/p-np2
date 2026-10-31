import Pnp4.Frontier.ContractExpansion.WitnessGrowthReduction

namespace Pnp4
namespace Frontier
namespace ContractExpansion

/-!
# Concrete polynomial thresholds and their growth

Block 13a of the downstream extraction effort.

After the concrete codec (#1522) and its conditional source instantiation (#1523),
the codec/growth leg reduces to the single arithmetic premise
`PolyBoundedInTable threshold` for the chosen `threshold : Nat → Nat`.  This file
discharges that premise for the canonical polynomial thresholds, so that — for these
thresholds — the growth input is **closed** (no longer a hypothesis).

`PolyBoundedInTable f` means `∃ k, ∀ n, f n ≤ (tableLen n + 1) ^ k`; since
`n ≤ tableLen n` (as `n < 2 ^ n`), the identity and every fixed polynomial are
polynomially bounded in the truth-table length.

Scope discipline — threshold growth lemmas only:

* **no** source wrapper / `VerifiedNPDAGLowerBoundSource` packaging is added here;
* **no** `NoPolynomialBoundedSearchSolver` / lower-bound proof, **no** NP-verifier
  construction, **no** `SearchMCSPMagnificationContract` change, **no** endpoint.
-/

/-- Linear threshold `n`. -/
def thresholdLinear (n : Nat) : Nat := n

/-- Quadratic threshold `n²`. -/
def thresholdQuadratic (n : Nat) : Nat := n ^ 2

/-- General polynomial threshold `nᵏ + k`. -/
def thresholdPoly (k n : Nat) : Nat := n ^ k + k

/-- The identity is polynomially bounded in the truth-table length: `n ≤ tableLen n`. -/
theorem polyBoundedInTable_id : PolyBoundedInTable (fun n => n) :=
  PolyBoundedInTable.of_le (fun _ => Nat.le_of_lt Nat.lt_two_pow_self) polyBoundedInTable_tableLen

/-- The linear threshold is polynomially bounded in the truth-table length. -/
theorem polyBoundedInTable_thresholdLinear : PolyBoundedInTable thresholdLinear :=
  polyBoundedInTable_id

/-- The quadratic threshold is polynomially bounded in the truth-table length. -/
theorem polyBoundedInTable_thresholdQuadratic : PolyBoundedInTable thresholdQuadratic := by
  show PolyBoundedInTable (fun n => n ^ 2)
  exact polyBoundedInTable_id.pow 2

/-- Every fixed polynomial threshold `nᵏ + k` is polynomially bounded in the
truth-table length. -/
theorem polyBoundedInTable_thresholdPoly (k : Nat) :
    PolyBoundedInTable (thresholdPoly k) := by
  show PolyBoundedInTable (fun n => n ^ k + k)
  exact (polyBoundedInTable_id.pow k).add (PolyBoundedInTable.const k)

end ContractExpansion
end Frontier
end Pnp4
