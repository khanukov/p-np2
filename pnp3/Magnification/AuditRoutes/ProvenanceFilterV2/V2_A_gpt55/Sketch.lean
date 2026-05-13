import Complexity.Interfaces

/-!
# ProvenanceFilter v2 / V2-A / gpt55 — Phase 1 sketch

Progress classification: side-track audit design sketch.  This file only states
one candidate `Prop` and one smoke theorem so that the shape is visible to Lean.
It does not claim any exclusion result, does not promote any guard, and
introduces no lower-bound source or bridge.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace ProvenanceFilterV2
namespace V2_A_gpt55

open Pnp3.ComplexityInterfaces

namespace FormulaShape

/-- Number of syntactic NOT gates in a formula. -/
def notGateCount {n : Nat} : FormulaCircuit n → Nat
  | .const _ => 0
  | .input _ => 0
  | .not c => notGateCount c + 1
  | .and c₁ c₂ => notGateCount c₁ + notGateCount c₂
  | .or c₁ c₂ => notGateCount c₁ + notGateCount c₂

/-- Number of syntactic AND gates in a formula. -/
def andGateCount {n : Nat} : FormulaCircuit n → Nat
  | .const _ => 0
  | .input _ => 0
  | .not c => andGateCount c
  | .and c₁ c₂ => andGateCount c₁ + andGateCount c₂ + 1
  | .or c₁ c₂ => andGateCount c₁ + andGateCount c₂

/-- Number of syntactic OR gates in a formula. -/
def orGateCount {n : Nat} : FormulaCircuit n → Nat
  | .const _ => 0
  | .input _ => 0
  | .not c => orGateCount c
  | .and c₁ c₂ => orGateCount c₁ + orGateCount c₂
  | .or c₁ c₂ => orGateCount c₁ + orGateCount c₂ + 1

/-- Total number of non-input Boolean gates tracked by this shape sketch. -/
def booleanGateCount {n : Nat} (c : FormulaCircuit n) : Nat :=
  notGateCount c + andGateCount c + orGateCount c

end FormulaShape

open FormulaShape

/--
**Excludes NOGO-000001.**  The first conjunct keeps the old useful part of the
support-diversity idea: the family must use an unbounded number of syntactic
input coordinates along the length axis.  A singleton or fixed-slice
truth-table hardwiring witness for one Partial-MCSP slice has bounded active
coordinates, so this Phase-1 sketch would reject that witness shape before any
route could pair it with an overbroad uniform provenance predicate.  This is
only a paper sketch: it records the intended obstruction against
`OverbroadUniformProvenance`-style leakage and deliberately does not state a
Lean exclusion theorem.

**Excludes NOGO-000004/000005.**  Prefix-AND-on-log-width passes a pure support
cardinality test because its support is unbounded but sublinear.  This V2-A
shape also inspects gate mix.  Whenever at least two variables are active, it
requires the displayed formula to contain both a NOT gate and an OR gate.  The
canonical `prefixAnd` family is monotone conjunction syntax, so its OR and NOT
counts are zero even though its support cardinality grows; hence the intended
filter distinguishes the prefix-AND specialization from honest non-monotone
formula families.

**Excludes NOGO-000006.**  The arbitrary all-essential log-width payload witness
is packaged as `rename (ttFormula (F n))`.  The truth-table constructor is a
decision-tree / DNF-like expansion whose AND/OR/NOT gate counts grow like the
truth-table size in `2 ^ widthFn n`, while the support is only `widthFn n`.  The
linear shape cap `booleanGateCount ≤ 16 * support + 16`, together with the
linear depth cap, is meant to reject that ttFormula-like syntax for all large
log-width payloads.  This is not support-cardinality-only: two formulas with the
same support size can differ on this predicate because their gate counts, gate
mix, and depth differ.

**Non-vacuity.**  The intended honest admitted family is parity, represented by
a balanced XOR formula over all active inputs using the standard expansion
`xor a b = (a ∧ ¬ b) ∨ (¬ a ∧ b)`.  A balanced parity tree has full unbounded
support, has NOT and OR gates as soon as at least two variables are present, and
has linearly many Boolean gates with logarithmic (therefore certainly linear)
depth relative to its support.  Thus the constants in this sketch are chosen so
that a reasonably shared-subformula-free formula implementation of parity is
expected to fit the cap, even though the exponential ttFormula implementation of
the same Boolean function would not.

**Self-attack.**  The strongest attack is formula rebalancing or formula
rewriting by the adversary: an arbitrary payload might sometimes be expressed by
a small, mixed-gate, shallow formula that satisfies this shape predicate even
though it was chosen adversarially at each length.  In particular, this filter
attacks the concrete ttFormula decision-tree syntax from NOGO-000006, not the
semantic possibility that some all-essential payload family has concise formulas
with parity-like statistics.  Phase 2 would therefore have to decide whether the
filter should be syntax-sensitive by design or strengthened with a coherence
condition; this Phase 1 file intentionally does not take that step.
-/
def ProvenanceFilter_v2_V2_A_gpt55
    {L : Language} (w : InPpolyFormula L) : Prop :=
  (∀ B : Nat, ∃ n : Nat, B < (FormulaCircuit.support (w.family n)).card) ∧
  (∀ n : Nat,
    booleanGateCount (w.family n) ≤
      16 * (FormulaCircuit.support (w.family n)).card + 16) ∧
  (∀ n : Nat,
    FormulaCircuit.depth (w.family n) ≤
      8 * (FormulaCircuit.support (w.family n)).card + 8) ∧
  (∀ n : Nat,
    2 ≤ (FormulaCircuit.support (w.family n)).card →
      0 < orGateCount (w.family n) ∧ 0 < notGateCount (w.family n))

/-- Phase 1 only — Lean smoke that the predicate elaborates.
    Phase 2 will replace this with real exclusion/self-attack theorems. -/
theorem v2_A_gpt55_phase1_loaded : True := trivial

end V2_A_gpt55
end ProvenanceFilterV2
end AuditRoutes
end Magnification
end Pnp3
