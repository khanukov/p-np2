import Complexity.Simulation.TM_Encoding
import Complexity.PsubsetPpolyDAG_Internal
import Complexity.PsubsetPpolyInternal.Simulation

namespace Pnp3
namespace Complexity
namespace Simulation

open ComplexityInterfaces
open ArchiveStraightLineAdapter

/--
Constructive contract for a compiler from polynomial-time TMs to
`StraightLineCircuit` families.

`compile M c hRun n` must produce an `n`-input circuit computing `M.accepts` on
length-`n` inputs, with a global polynomial size bound depending only on `c`.
-/
structure PolyTMToStraightLineCompiler where
  degree : TM → Nat → Nat
  compile :
    (M : TM) →
    (c : Nat) →
    (hRun : ∀ n, M.runTime n ≤ n ^ c + c) →
    (n : Nat) →
    StraightLineCircuit n
  size_bound :
    ∀ (M : TM) (c : Nat)
      (hRun : ∀ n, M.runTime n ≤ n ^ c + c) (n : Nat),
      (toDag (compile M c hRun n)).size ≤ n ^ (degree M c) + degree M c
  correct :
    ∀ (M : TM) (c : Nat)
      (hRun : ∀ n, M.runTime n ≤ n ^ c + c)
      (n : Nat) (x : Bitstring n),
      Pnp3.Internal.PsubsetPpoly.StraightLine.eval (compile M c hRun n) x =
        TM.accepts M n x

namespace InternalCompiler

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.Simulation

/-!
`polyTMToStraightLineCompiler_internal` is blocked only by two internal
semantic lemmas:
1. straight runtime specification (`runtimeConfig` really simulates `TM.run`);
2. agreement between archive DAG semantics and internal straight semantics
   (used when packaging into `PpolyStraightLine`/`PpolyDAG`).

Once these are proved in `PsubsetPpolyInternal`, the compiler below is fully
constructive and closes Step 10.
-/

/-- Pending internal semantic blocker: straight runtime configuration spec. -/
def RuntimeSpecProvider : Prop :=
  ∀ (M : TM) (n : Nat),
    StraightConfig.Spec (sc := StraightConfig.runtimeConfig M n)
      (f := fun x => M.run (n := n) x)

/-- Stronger internal blocker: one-step straight simulation spec. -/
def StepSpecProvider : Prop :=
  ∀ (M : TM) (n : Nat)
    (sc : StraightConfig M n)
    (f : Bitstring n → TM.Configuration (M := M) n),
    StraightConfig.Spec (sc := sc) (f := f) →
      StraightConfig.Spec (sc := StraightConfig.step M sc)
        (f := fun x => TM.stepConfig (M := M) (f x))

theorem runtimeSpecProvider_of_stepSpec
    (hStep : StepSpecProvider) :
    RuntimeSpecProvider := by
  intro M n
  exact StraightConfig.runtimeConfig_spec_of_step_spec (M := M) (n := n)
    (hStep := hStep M n)

theorem degree_bound_main_term (c n : Nat) :
    n ^ (c + 4) ≤ n ^ (c + 5) := by
  cases n with
  | zero =>
      simp
  | succ n =>
      exact Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)

/--
Assemble a compiler once the runtime straight simulation contract is available.

This packaging is independent from how `RuntimeSpecProvider` is obtained
(direct `step` proof, `stepCompiled` proof, or any future internal route).
-/
noncomputable def polyTMToStraightLineCompiler_of_runtimeSpec
    (hRuntime : RuntimeSpecProvider) :
    PolyTMToStraightLineCompiler where
  degree := fun _ c => c + 5
  compile := fun M c hRun n => StraightConfig.acceptCircuit M n
  size_bound := by
    intro M c hRun n
    have hGates :
        (StraightConfig.acceptCircuit M n).gates ≤
          StraightConfig.gatePolyBound M c n :=
      StraightConfig.straightAcceptCircuit_le_gatePolyBound
        (M := M) (c := c) hRun n
    have hSize :
        (toDag (StraightConfig.acceptCircuit M n)).size ≤
          StraightConfig.gatePolyBound M c n + 1 := by
      simpa [size_toDag, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using Nat.add_le_add_right hGates 1
    have hPow :
        StraightConfig.gatePolyBound M c n + 1 ≤ n ^ (c + 5) + (c + 5) := by
      have hMain : n ^ (c + 4) ≤ n ^ (c + 5) := degree_bound_main_term c n
      have hAdd :
          n ^ (c + 4) + (c + 4) + 1 ≤ n ^ (c + 5) + (c + 5) := by
        omega
      simpa [StraightConfig.gatePolyBound, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAdd
    exact Nat.le_trans hSize hPow
  correct := by
    intro M c hRun n x
    have hSpec :
        StraightConfig.Spec (sc := StraightConfig.runtimeConfig M n)
          (f := fun y => M.run (n := n) y) :=
      hRuntime M n
    exact StraightConfig.straightAcceptCircuit_spec (M := M) (n := n) hSpec x

/--
Alternative blocker contract on the `stepCompiled` branch:
wire-level one-step semantics for `stepCompiled` imply runtime simulation spec.
-/
def StepCompiledSemanticsProvider : Prop :=
  ∀ (M : TM) (n : Nat), StraightConfig.StepCompiledSemantics M n

theorem runtimeSpec_of_stepCompiledSemantics
    (hSem : StepCompiledSemanticsProvider) :
    ∀ (M : TM) (n : Nat),
      StraightConfig.Spec
        (sc := Nat.iterate (StraightConfig.stepCompiled M) (M.runTime n)
          (StraightConfig.initialStraightConfig M n))
        (f := fun x => M.run (n := n) x) := by
  intro M n
  exact StraightConfig.runtime_spec_of_stepCompiledProvider (M := M) (n := n) (hSem := hSem M n)

/-- Low-level contracts currently needed to instantiate `StepCompiledSemanticsProvider`. -/
def StepCompiledContracts : Prop :=
  Pnp3.Internal.PsubsetPpoly.StraightLine.CompileTreeWireSemantics ∧
  Pnp3.Internal.PsubsetPpoly.StraightLine.AppendWireSemantics

/--
Split variant of `StepCompiledContracts` that isolates the hard append-right
obligation at gate level.

This mirrors the refactoring in `TreeToStraight`: `AppendWireSemantics` can be
assembled from `appendWireSemantics_left` and `AppendGateRightSemantics`.
-/
def StepCompiledContractsSplit : Prop :=
  Pnp3.Internal.PsubsetPpoly.StraightLine.CompileTreeWireSemantics ∧
  Pnp3.Internal.PsubsetPpoly.StraightLine.AppendGateRightSemantics

theorem stepCompiledContracts_of_split
    (hSplit : StepCompiledContractsSplit) :
    StepCompiledContracts := by
  rcases hSplit with ⟨hCompile, hAppendGateRight⟩
  refine ⟨hCompile, ?_⟩
  exact Pnp3.Internal.PsubsetPpoly.StraightLine.appendWireSemantics_of_gateContracts
    hAppendGateRight

/--
Internal assembly helper: recover `StepCompiledContracts` from only the
gate-level append-right contract.

This packages the theorem `compileTreeWireSemantics_of_gateContracts` from
`TreeToStraight` together with `appendWireSemantics_of_gateContracts`.
-/
theorem stepCompiledContracts_of_appendGateRight
    (hAppendGateRight : Pnp3.Internal.PsubsetPpoly.StraightLine.AppendGateRightSemantics) :
    StepCompiledContracts := by
  refine ⟨?_, ?_⟩
  · exact Pnp3.Internal.PsubsetPpoly.StraightLine.compileTreeWireSemantics_of_gateContracts
      hAppendGateRight
  · exact Pnp3.Internal.PsubsetPpoly.StraightLine.appendWireSemantics_of_gateContracts
      hAppendGateRight

theorem stepCompiledSemanticsProvider_of_contracts
    (hContracts : StepCompiledContracts) :
    StepCompiledSemanticsProvider := by
  rcases hContracts with ⟨hCompile, hAppend⟩
  intro M n
  exact StraightConfig.stepCompiled_semantics_of_core_contracts hCompile hAppend M n

theorem stepCompiledSemanticsProvider_of_splitContracts
    (hSplit : StepCompiledContractsSplit) :
    StepCompiledSemanticsProvider :=
  stepCompiledSemanticsProvider_of_contracts
    (stepCompiledContracts_of_split hSplit)

theorem runtimeSpec_of_stepCompiledContracts
    (hContracts : StepCompiledContracts) :
    ∀ (M : TM) (n : Nat),
      StraightConfig.Spec
        (sc := Nat.iterate (StraightConfig.stepCompiled M) (M.runTime n)
          (StraightConfig.initialStraightConfig M n))
        (f := fun x => M.run (n := n) x) := by
  exact runtimeSpec_of_stepCompiledSemantics
    (stepCompiledSemanticsProvider_of_contracts hContracts)

/--
Split-contract variant of `runtimeSpec_of_stepCompiledContracts`.

This theorem closes the runtime-spec assembly point directly from the split
contract surface (`CompileTreeWireSemantics ∧ AppendGateRightSemantics`).
-/
theorem runtimeSpec_of_splitContracts
    (hSplit : StepCompiledContractsSplit) :
    ∀ (M : TM) (n : Nat),
      StraightConfig.Spec
        (sc := Nat.iterate (StraightConfig.stepCompiled M) (M.runTime n)
          (StraightConfig.initialStraightConfig M n))
        (f := fun x => M.run (n := n) x) :=
  runtimeSpec_of_stepCompiledSemantics
    (stepCompiledSemanticsProvider_of_splitContracts hSplit)

/-- Pending internal semantic blocker: `eval` compatibility of two interfaces. -/
def EvalAgreement : Prop :=
  ∀ {n : Nat} (C : StraightLineCircuit n) (x : Bitstring n),
    ArchiveStraightLineAdapter.eval C x =
      Pnp3.Internal.PsubsetPpoly.StraightLine.eval C x

/--
Compiler assembly from the two remaining internal blockers.

This definition is axiom-free; all assumptions are explicit local hypotheses.
-/
noncomputable def polyTMToStraightLineCompiler_of_blocks
    (hStep : StepSpecProvider) :
    PolyTMToStraightLineCompiler :=
  polyTMToStraightLineCompiler_of_runtimeSpec
    (runtimeSpecProvider_of_stepSpec hStep)

/--
Step-10 target shape: internal compiler assembled from a pure runtime contract.

As soon as `RuntimeSpecProvider` is proved inside `pnp3` without extra
parameters, this definition becomes the final closed compiler constant.
-/
noncomputable def polyTMToStraightLineCompiler_internal
    (hRuntime : RuntimeSpecProvider) :
    PolyTMToStraightLineCompiler :=
  polyTMToStraightLineCompiler_of_runtimeSpec hRuntime

end InternalCompiler

/--
Main reduction theorem: a constructive TM→straight-line compiler closes
`P_subset_PpolyStraightLine`.
-/
theorem P_subset_PpolyStraightLine_of_compiler
    (compiler : PolyTMToStraightLineCompiler)
    (hEvalAgree : InternalCompiler.EvalAgreement) :
    P_subset_PpolyStraightLine := by
  intro L hPL
  rcases exists_poly_tm_for_P (L := L) hPL with ⟨M, c, hRun, hCorrect⟩
  refine ⟨({
    polyBound := fun n => n ^ (compiler.degree M c) + compiler.degree M c
    polyBound_poly := ⟨compiler.degree M c, by
      intro n
      exact Nat.le_refl _⟩
    family := fun n => compiler.compile M c hRun n
    family_size_le := by
      intro n
      exact compiler.size_bound M c hRun n
    correct := by
      intro n x
      calc
        eval (compiler.compile M c hRun n) x =
            Pnp3.Internal.PsubsetPpoly.StraightLine.eval
              (compiler.compile M c hRun n) x :=
          hEvalAgree (C := compiler.compile M c hRun n) (x := x)
        _ = TM.accepts M n x := compiler.correct M c hRun n x
        _ = L n x := hCorrect n x
  } : InPpolyStraightLine L), trivial⟩

/-- Canonical DAG inclusion obtained from a constructive TM compiler. -/
theorem P_subset_PpolyDAG_of_compiler
    (compiler : PolyTMToStraightLineCompiler)
    (hEvalAgree : InternalCompiler.EvalAgreement) :
    P_subset_PpolyDAG :=
  P_subset_PpolyDAG_of_P_subset_PpolyStraightLine
    (P_subset_PpolyStraightLine_of_compiler compiler hEvalAgree)

/--
Step-11 pre-assembly from runtime-spec closure + evaluation agreement.

This theorem is fully constructive modulo the two explicitly tracked internal
blockers and removes all packaging boilerplate at call-sites.
-/
theorem P_subset_PpolyDAG_of_runtimeSpec
    (hRuntime : InternalCompiler.RuntimeSpecProvider)
    (hEvalAgree : InternalCompiler.EvalAgreement) :
    P_subset_PpolyDAG :=
  P_subset_PpolyDAG_of_compiler
    (compiler := InternalCompiler.polyTMToStraightLineCompiler_internal hRuntime)
    hEvalAgree

/-- Step-11 pre-assembly from one-step `step` simulation + eval agreement. -/
theorem P_subset_PpolyDAG_of_stepSpec
    (hStep : InternalCompiler.StepSpecProvider)
    (hEvalAgree : InternalCompiler.EvalAgreement) :
    P_subset_PpolyDAG :=
  P_subset_PpolyDAG_of_runtimeSpec
    (hRuntime := InternalCompiler.runtimeSpecProvider_of_stepSpec hStep)
    hEvalAgree

/--
Public re-export of the split-contract runtime statement.

This theorem keeps downstream modules in the `Complexity.Simulation` namespace
without requiring them to depend directly on `InternalCompiler` internals.
-/
theorem runtimeSpec_iterated_of_splitContracts
    (hSplit : InternalCompiler.StepCompiledContractsSplit) :
    ∀ (M : TM) (n : Nat),
      Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.Spec
        (sc := Nat.iterate (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.stepCompiled M)
          (M.runTime n) (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.initialStraightConfig M n))
        (f := fun x => M.run (n := n) x) := by
  exact InternalCompiler.runtimeSpec_of_splitContracts hSplit

/--
Public bridge: from gate-level append-right contract to the full
`StepCompiledContracts` package.

This theorem re-exports the internal assembly helper so downstream modules can
depend on a stable namespace (`Complexity.Simulation`) without opening
`InternalCompiler` internals.
-/
theorem stepCompiledContracts_of_appendGateRight
    (hAppendGateRight : Pnp3.Internal.PsubsetPpoly.StraightLine.AppendGateRightSemantics) :
    InternalCompiler.StepCompiledContracts :=
  InternalCompiler.stepCompiledContracts_of_appendGateRight hAppendGateRight

/--
Public bridge: derive `StepCompiledSemanticsProvider` from gate-level append
contract.
-/
theorem stepCompiledSemanticsProvider_of_appendGateRight
    (hAppendGateRight : Pnp3.Internal.PsubsetPpoly.StraightLine.AppendGateRightSemantics) :
    InternalCompiler.StepCompiledSemanticsProvider :=
  InternalCompiler.stepCompiledSemanticsProvider_of_contracts
    (stepCompiledContracts_of_appendGateRight hAppendGateRight)

/-- Minimal contract bundle that closes the internal `P ⊆ P/poly` route. -/
def PsubsetPpolyInternalContracts : Prop :=
  InternalCompiler.RuntimeSpecProvider ∧ InternalCompiler.EvalAgreement

/--
Step-11 contract closure theorem: once the two remaining internal contracts are
available, `P_subset_PpolyDAG` follows immediately.
-/
theorem proved_P_subset_PpolyDAG_of_contracts
    (hContracts : PsubsetPpolyInternalContracts) :
    P_subset_PpolyDAG := by
  rcases hContracts with ⟨hRuntime, hEvalAgree⟩
  exact P_subset_PpolyDAG_of_runtimeSpec hRuntime hEvalAgree

/-- Short alias used by final wrappers to avoid carrying inclusion hypotheses. -/
theorem dagInclusion_from_compiler
    (compiler : PolyTMToStraightLineCompiler)
    (hEvalAgree : InternalCompiler.EvalAgreement) :
    P_subset_PpolyDAG :=
  P_subset_PpolyDAG_of_compiler compiler hEvalAgree

abbrev P_subset_PpolyLegacyStraight_of_compiler :=
  P_subset_PpolyStraightLine_of_compiler

abbrev PolyTMToLegacyCompiler := PolyTMToStraightLineCompiler

end Simulation
end Complexity
end Pnp3
