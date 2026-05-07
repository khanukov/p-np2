import Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.Sketch
import Magnification.AuditRoutes.LogWidthAdversary.RenameSupport
import Mathlib.Tactic

/-!
# ProvenanceFilter v2 / V2-A / gpt55 — Phase 2 filter

Progress classification: side-track audit formalization.  V2-A inspects the
syntax of the displayed `FormulaCircuit` family in an `InPpolyFormula` record;
it does not introduce, reduce, or promote any `P != NP` source obligation.

The Phase-2 predicate below keeps the Phase-1 bounded/unbounded shape checks and
adds one deliberately sharp V2-A gate-shape clause: every displayed formula must
be **AND-free**.  This makes the self-attack kernel-checkable against the two
currently formalized hardwiring syntaxes whose root construction necessarily
uses AND gates (`prefixAnd` and `ttFormula`).  Non-vacuity is supplied by an
honest monotone OR family in `NonVacuity.lean`.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace ProvenanceFilterV2
namespace V2_A_gpt55

open Pnp3.ComplexityInterfaces

namespace FormulaShape

/-- Renaming only rewires leaves, so it preserves the number of AND gates. -/
theorem andGateCount_rename {m n : Nat} (σ : Fin m → Fin n)
    (c : FormulaCircuit m) :
    andGateCount (Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename σ c) = andGateCount c := by
  induction c with
  | const b => simp [Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename, andGateCount]
  | input i => simp [Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename, andGateCount]
  | not c ih => simp [Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename, andGateCount, ih]
  | and c₁ c₂ ih₁ ih₂ => simp [Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename, andGateCount, ih₁, ih₂]
  | or c₁ c₂ ih₁ ih₂ => simp [Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename, andGateCount, ih₁, ih₂]

/-- Renaming only rewires leaves, so it preserves the number of OR gates. -/
theorem orGateCount_rename {m n : Nat} (σ : Fin m → Fin n)
    (c : FormulaCircuit m) :
    orGateCount (Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename σ c) = orGateCount c := by
  induction c with
  | const b => simp [Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename, orGateCount]
  | input i => simp [Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename, orGateCount]
  | not c ih => simp [Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename, orGateCount, ih]
  | and c₁ c₂ ih₁ ih₂ => simp [Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename, orGateCount, ih₁, ih₂]
  | or c₁ c₂ ih₁ ih₂ => simp [Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename, orGateCount, ih₁, ih₂]

/-- Renaming only rewires leaves, so it preserves the number of NOT gates. -/
theorem notGateCount_rename {m n : Nat} (σ : Fin m → Fin n)
    (c : FormulaCircuit m) :
    notGateCount (Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename σ c) = notGateCount c := by
  induction c with
  | const b => simp [Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename, notGateCount]
  | input i => simp [Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename, notGateCount]
  | not c ih => simp [Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename, notGateCount, ih]
  | and c₁ c₂ ih₁ ih₂ => simp [Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename, notGateCount, ih₁, ih₂]
  | or c₁ c₂ ih₁ ih₂ => simp [Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename, notGateCount, ih₁, ih₂]

/-- Boolean-gate count is invariant under input renaming. -/
theorem booleanGateCount_rename {m n : Nat} (σ : Fin m → Fin n)
    (c : FormulaCircuit m) :
    booleanGateCount (Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename σ c) = booleanGateCount c := by
  simp [booleanGateCount, notGateCount_rename, andGateCount_rename,
    orGateCount_rename]

/-- `ttFormula` on a positive number of variables always introduces AND gates. -/
theorem one_le_andGateCount_ttFormula_succ {k : Nat}
    (f : Bitstring (k + 1) → Bool) :
    1 ≤ andGateCount (Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.ttFormula f) := by
  unfold Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.ttFormula
  simp [andGateCount]
  omega

end FormulaShape

open FormulaShape

/--
Phase-2 V2-A formula-shape predicate.

* The first conjunct accepts either unbounded support or the named constant-false
  smoke family used for non-vacuity.
* The second and third conjuncts keep the Phase-1 linear size/depth sanity caps.
* The final conjunct is the Phase-2 self-attack hook: accepted displayed
  formulas must be AND-free at every length.  This is intentionally syntactic;
  it is a proposal-level audit predicate, not an accepted provenance guard.
-/
def ProvenanceFilter_v2_V2_A_gpt55_phase2
    {L : Language} (w : InPpolyFormula L) : Prop :=
  ((∀ B : Nat, ∃ n : Nat, B < (FormulaCircuit.support (w.family n)).card) ∨
    (∀ n : Nat, w.family n = FormulaCircuit.const false)) ∧
  (∀ n : Nat,
    booleanGateCount (w.family n) ≤
      16 * (FormulaCircuit.support (w.family n)).card + 16) ∧
  (∀ n : Nat,
    FormulaCircuit.depth (w.family n) ≤
      8 * (FormulaCircuit.support (w.family n)).card + 8) ∧
  (∀ n : Nat, andGateCount (w.family n) = 0)

/-- Compatibility alias used by the Phase-2 theorem files. -/
abbrev ProvenanceFilter_v2_V2_A_gpt55_Filter
    {L : Language} (w : InPpolyFormula L) : Prop :=
  ProvenanceFilter_v2_V2_A_gpt55_phase2 w

end V2_A_gpt55
end ProvenanceFilterV2
end AuditRoutes
end Magnification
end Pnp3
