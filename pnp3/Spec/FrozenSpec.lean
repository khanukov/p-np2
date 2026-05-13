import Complexity.Interfaces

/-!
# FrozenSpec — independent reference semantics (stage 1)

Research Governance v0.1, PR 10 (`Engineering Execution Plan v0.2.1`).

This module records "shape-pinning" reference definitions for a small,
finite subset of the trust root. Each reference is paired with an
equivalence theorem asserting that the active definition in
`Pnp3.ComplexityInterfaces` (or `Pnp3.Models`) matches the reference.

**Stage 1 (this file): shape-level pinning only.**
The references below are deliberately written in terms of fields
(for `DagCircuit.size`) or constructors (for `FormulaCircuit.size`)
of the underlying types, *not* in terms of the active size functions.
The equivalence theorems are therefore `rfl`/`trivial`-witnesses;
their value is in tripping a build error if the active definitions
ever drift away from the recorded shape.

**Stage 2 (deferred): independent semantic reference.**
Future work introduces `FrozenSpec.P_ref` / `FrozenSpec.NP_ref` /
`FrozenSpec.PpolyDAG_ref` from first-principles Turing-machine /
circuit-family semantics, then proves their equivalence to the
active interface. These are NOT defined in stage 1; introducing them
as `:= ComplexityInterfaces.P` (or analogous) is **explicitly
forbidden** (Plan v0.2.1 amendments ② and ③).

Import policy: this file imports only `Complexity.Interfaces`. It
**must not** import `Magnification.*`, `LowerBounds.*`,
`ThirdPartyFacts.*`, or `Barrier.*`. The whole point is to give the
trust root a second name independent of the audit/cleanup surface.
-/

namespace Pnp3
namespace FrozenSpec

open ComplexityInterfaces

/-! ## DagCircuit size — field-based reference -/

/--
Reference `DagCircuit.size` defined directly in terms of the
`DagCircuit` structure's field, without calling the active
`ComplexityInterfaces.DagCircuit.size`.
-/
def DagCircuit_size_ref {n : Nat} (C : DagCircuit n) : Nat :=
  C.gates + 1

/--
Shape-pinning equivalence: the active size is definitionally equal
to the reference. If the active definition's body ever changes
shape (e.g. someone adds an `output` adjustment or shifts the
constant), this `rfl` proof breaks.
-/
theorem DagCircuit_size_matches_ref
    {n : Nat} (C : DagCircuit n) :
    DagCircuit.size C = DagCircuit_size_ref C := rfl

/-! ## FormulaCircuit size — constructor-based reference -/

/--
Reference `FormulaCircuit.size` defined by recursion on the
`FormulaCircuit` inductive's constructors, without calling the
active `ComplexityInterfaces.FormulaCircuit.size`.
-/
def FormulaCircuit_size_ref {n : Nat} :
    FormulaCircuit n → Nat
  | .const _      => 1
  | .input _      => 1
  | .not c        => FormulaCircuit_size_ref c + 1
  | .and c₁ c₂    =>
      FormulaCircuit_size_ref c₁ + FormulaCircuit_size_ref c₂ + 1
  | .or  c₁ c₂    =>
      FormulaCircuit_size_ref c₁ + FormulaCircuit_size_ref c₂ + 1

/--
Shape-pinning equivalence: the active size matches the
constructor-by-constructor reference. Proved by structural induction
(`rfl` on each branch).
-/
theorem FormulaCircuit_size_matches_ref
    {n : Nat} (c : FormulaCircuit n) :
    FormulaCircuit.size c = FormulaCircuit_size_ref c := by
  induction c with
  | const b      => rfl
  | input i      => rfl
  | not c ih     => simp [FormulaCircuit.size, FormulaCircuit_size_ref, ih]
  | and c₁ c₂ ih₁ ih₂ =>
      simp [FormulaCircuit.size, FormulaCircuit_size_ref, ih₁, ih₂]
  | or  c₁ c₂ ih₁ ih₂ =>
      simp [FormulaCircuit.size, FormulaCircuit_size_ref, ih₁, ih₂]

/-! ## NP_not_subset_PpolyDAG — existential shape pin -/

/--
Reference shape for `NP_not_subset_PpolyDAG`.

Written as the explicit existential `∃ L, NP L ∧ ¬ PpolyDAG L`,
matching the active definition at
`pnp3/Complexity/Interfaces.lean:616`. This is **not** an
independent semantics for `NP` / `PpolyDAG`; it pins the
*existential* shape so that a future drift of the active definition
to (e.g.) a universal `∀ L, NP L → ¬ PpolyDAG L` shape would trip
this proof.

`P_ref` / `NP_ref` / `PpolyDAG_ref` from independent first-
principles semantics are stage-2 work and intentionally absent here
(Plan v0.2.1 amendment ②).
-/
abbrev NP_not_subset_PpolyDAG_ref : Prop :=
  ∃ L, NP L ∧ ¬ PpolyDAG L

/--
Shape-pinning equivalence (stage 1).
-/
theorem NP_not_subset_PpolyDAG_matches_ref :
    ComplexityInterfaces.NP_not_subset_PpolyDAG ↔
      NP_not_subset_PpolyDAG_ref := Iff.rfl

end FrozenSpec
end Pnp3
