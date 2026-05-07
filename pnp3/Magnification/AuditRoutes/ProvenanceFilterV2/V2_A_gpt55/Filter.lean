import Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.Sketch
import Magnification.AuditRoutes.LogWidthAdversary.RenameSupport
import Mathlib.Tactic

/-!
# ProvenanceFilter v2 / V2-A / gpt55 — Phase 2 filter

Progress classification: side-track audit formalization.  V2-A inspects the
syntax of the displayed `FormulaCircuit` family in an `InPpolyFormula` record;
it does not introduce, reduce, or promote any `P != NP` source obligation.

This Phase-2 predicate deliberately restores the Phase-1 formula-shape sketch:
unbounded support, a linear Boolean-gate cap, a linear depth cap, and a mixed
OR/NOT-gate requirement once at least two variables are syntactically active.
The proof files below self-attack this concrete syntactic shape against the
currently formalized hardwiring witnesses.
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
    andGateCount (Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename σ c) =
      andGateCount c := by
  induction c with
  | const b => simp [Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename, andGateCount]
  | input i => simp [Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename, andGateCount]
  | not c ih => simp [Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename, andGateCount, ih]
  | and c₁ c₂ ih₁ ih₂ => simp [Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename, andGateCount, ih₁, ih₂]
  | or c₁ c₂ ih₁ ih₂ => simp [Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename, andGateCount, ih₁, ih₂]

/-- Renaming only rewires leaves, so it preserves the number of OR gates. -/
theorem orGateCount_rename {m n : Nat} (σ : Fin m → Fin n)
    (c : FormulaCircuit m) :
    orGateCount (Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename σ c) =
      orGateCount c := by
  induction c with
  | const b => simp [Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename, orGateCount]
  | input i => simp [Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename, orGateCount]
  | not c ih => simp [Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename, orGateCount, ih]
  | and c₁ c₂ ih₁ ih₂ => simp [Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename, orGateCount, ih₁, ih₂]
  | or c₁ c₂ ih₁ ih₂ => simp [Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename, orGateCount, ih₁, ih₂]

/-- Renaming only rewires leaves, so it preserves the number of NOT gates. -/
theorem notGateCount_rename {m n : Nat} (σ : Fin m → Fin n)
    (c : FormulaCircuit m) :
    notGateCount (Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename σ c) =
      notGateCount c := by
  induction c with
  | const b => simp [Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename, notGateCount]
  | input i => simp [Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename, notGateCount]
  | not c ih => simp [Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename, notGateCount, ih]
  | and c₁ c₂ ih₁ ih₂ => simp [Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename, notGateCount, ih₁, ih₂]
  | or c₁ c₂ ih₁ ih₂ => simp [Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename, notGateCount, ih₁, ih₂]

/-- Boolean-gate count is invariant under input renaming. -/
theorem booleanGateCount_rename {m n : Nat} (σ : Fin m → Fin n)
    (c : FormulaCircuit m) :
    booleanGateCount (Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.FormulaCircuit.rename σ c) =
      booleanGateCount c := by
  simp [booleanGateCount, notGateCount_rename, andGateCount_rename,
    orGateCount_rename]


/-- Exact NOT-gate count of `ttFormula`, independent of the payload. -/
theorem notGateCount_ttFormula
    {k : Nat} (f : Bitstring k → Bool) :
    notGateCount (Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.ttFormula f) =
      2 ^ k - 1 := by
  induction k with
  | zero =>
      simp [Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.ttFormula,
        notGateCount]
  | succ k ih =>
      unfold Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.ttFormula
      simp [notGateCount, notGateCount_rename,
        ih (fun x : Bitstring k => f (Fin.cases false x)),
        ih (fun x : Bitstring k => f (Fin.cases true x))]
      have hpow : 1 ≤ 2 ^ k := Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
      omega

/-- Exact AND-gate count of `ttFormula`, independent of the payload. -/
theorem andGateCount_ttFormula
    {k : Nat} (f : Bitstring k → Bool) :
    andGateCount (Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.ttFormula f) =
      2 ^ (k + 1) - 2 := by
  induction k with
  | zero =>
      simp [Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.ttFormula,
        andGateCount]
  | succ k ih =>
      unfold Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.ttFormula
      simp [andGateCount, andGateCount_rename,
        ih (fun x : Bitstring k => f (Fin.cases false x)),
        ih (fun x : Bitstring k => f (Fin.cases true x))]
      have hpow : 1 ≤ 2 ^ k := Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
      omega

/-- Exact OR-gate count of `ttFormula`, independent of the payload. -/
theorem orGateCount_ttFormula
    {k : Nat} (f : Bitstring k → Bool) :
    orGateCount (Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.ttFormula f) =
      2 ^ k - 1 := by
  induction k with
  | zero =>
      simp [Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.ttFormula,
        orGateCount]
  | succ k ih =>
      unfold Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.ttFormula
      simp [orGateCount, orGateCount_rename,
        ih (fun x : Bitstring k => f (Fin.cases false x)),
        ih (fun x : Bitstring k => f (Fin.cases true x))]
      have hpow : 1 ≤ 2 ^ k := Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
      omega

/-- `ttFormula` has an exact Boolean-gate count independent of its payload. -/
theorem booleanGateCount_ttFormula
    {k : Nat} (f : Bitstring k → Bool) :
    booleanGateCount (Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.ttFormula f) =
      4 * (2 ^ k - 1) := by
  simp [booleanGateCount, notGateCount_ttFormula, andGateCount_ttFormula,
    orGateCount_ttFormula]
  omega

end FormulaShape

open FormulaShape

/--
Phase-2 V2-A formula-shape predicate, restored from the Phase-1 sketch.

The predicate is syntactic: it inspects support cardinality, total Boolean-gate
count, depth, and whether the displayed formula has both OR and NOT gates once
the active support has size at least two.  It remains a proposal-level audit
object rather than an accepted provenance guard.
-/
def ProvenanceFilter_v2_V2_A_gpt55_phase2
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

/-- Compatibility alias used by the Phase-2 theorem files. -/
abbrev ProvenanceFilter_v2_V2_A_gpt55_Filter
    {L : Language} (w : InPpolyFormula L) : Prop :=
  ProvenanceFilter_v2_V2_A_gpt55_phase2 w

end V2_A_gpt55
end ProvenanceFilterV2
end AuditRoutes
end Magnification
end Pnp3
