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

/--
Iterated-runtime variant of the straight runtime contract.

This shape is produced naturally by `stepCompiled` semantics.
-/
def RuntimeSpecProviderIterated : Prop :=
  ∀ (M : TM) (n : Nat),
    StraightConfig.Spec
      (sc := Nat.iterate (StraightConfig.stepCompiledTruthTable M) (M.runTime n)
        (StraightConfig.initialStraightConfig M n))
      (f := fun x => M.run (n := n) x)

/-- Bridge contract identifying `runtimeConfig` with iterated `stepCompiled`. -/
def RuntimeConfigEqStepCompiled : Prop :=
  ∀ (M : TM) (n : Nat),
    StraightConfig.runtimeConfig M n =
      Nat.iterate (StraightConfig.stepCompiledTruthTable M) (M.runTime n)
        (StraightConfig.initialStraightConfig M n)

/--
Bridge from iterated-runtime form to `RuntimeSpecProvider`, assuming
configuration equality at `runTime`.
-/
theorem runtimeSpecProvider_of_iterated_eq
    (hIter : RuntimeSpecProviderIterated)
    (hCfgEq : RuntimeConfigEqStepCompiled) :
    RuntimeSpecProvider := by
  intro M n
  have hEq := hCfgEq M n
  simpa only [hEq] using hIter M n

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
        (sc := Nat.iterate (StraightConfig.stepCompiledTruthTable M) (M.runTime n)
          (StraightConfig.initialStraightConfig M n))
        (f := fun x => M.run (n := n) x) := by
  intro M n
  exact StraightConfig.runtime_spec_of_stepCompiledProvider (M := M) (n := n) (hSem := hSem M n)

/-- The same theorem packaged in `RuntimeSpecProviderIterated` form. -/
theorem runtimeSpecProviderIterated_of_stepCompiledSemantics
    (hSem : StepCompiledSemanticsProvider) :
    RuntimeSpecProviderIterated :=
  runtimeSpec_of_stepCompiledSemantics hSem

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

/--
Closed internal witness for one-step compiled contracts.

This is the assumption-free package needed by the `stepCompiled` assembly path.
-/
theorem stepCompiledContracts_internal : StepCompiledContracts := by
  refine ⟨?_, ?_⟩
  · exact Pnp3.Internal.PsubsetPpoly.StraightLine.compileTreeWireSemantics
  · exact Pnp3.Internal.PsubsetPpoly.StraightLine.appendWireSemantics

theorem stepCompiledSemanticsProvider_of_contracts
    (hContracts : StepCompiledContracts) :
    StepCompiledSemanticsProvider := by
  rcases hContracts with ⟨hCompile, hAppend⟩
  intro M n
  exact StraightConfig.stepCompiled_semantics_of_core_contracts hCompile hAppend M n

/-- Closed internal witness for step-compiled semantic provider. -/
theorem stepCompiledSemanticsProvider_internal : StepCompiledSemanticsProvider :=
  stepCompiledSemanticsProvider_of_contracts stepCompiledContracts_internal

theorem stepCompiledSemanticsProvider_of_splitContracts
    (hSplit : StepCompiledContractsSplit) :
    StepCompiledSemanticsProvider :=
  stepCompiledSemanticsProvider_of_contracts
    (stepCompiledContracts_of_split hSplit)

theorem runtimeSpec_of_stepCompiledContracts
    (hContracts : StepCompiledContracts) :
    ∀ (M : TM) (n : Nat),
      StraightConfig.Spec
        (sc := Nat.iterate (StraightConfig.stepCompiledTruthTable M) (M.runTime n)
          (StraightConfig.initialStraightConfig M n))
        (f := fun x => M.run (n := n) x) := by
  exact runtimeSpec_of_stepCompiledSemantics
    (stepCompiledSemanticsProvider_of_contracts hContracts)

/-- Closed internal iterated runtime spec on the `stepCompiled` path. -/
theorem runtimeSpec_iterated_internal :
    ∀ (M : TM) (n : Nat),
      StraightConfig.Spec
        (sc := Nat.iterate (StraightConfig.stepCompiledTruthTable M) (M.runTime n)
          (StraightConfig.initialStraightConfig M n))
        (f := fun x => M.run (n := n) x) :=
  runtimeSpec_of_stepCompiledContracts stepCompiledContracts_internal

/--
Closed iterated-runtime witness in bundled form.
-/
theorem runtimeSpecProviderIterated_internal :
    RuntimeSpecProviderIterated :=
  runtimeSpec_iterated_internal

/--
Bridge helper: closes `RuntimeSpecProvider` from internal iterated witness once
the runtime-config equality bridge is provided.
-/
theorem runtimeSpecProvider_internal_of_runtimeEq
    (hCfgEq : RuntimeConfigEqStepCompiled) :
    RuntimeSpecProvider :=
  runtimeSpecProvider_of_iterated_eq runtimeSpecProviderIterated_internal hCfgEq

/--
Closed internal runtime witness in canonical iterated form.
-/
theorem runtimeSpecProvider_internal_iterated :
    RuntimeSpecProviderIterated :=
  runtimeSpecProviderIterated_internal

/--
Split-contract variant of `runtimeSpec_of_stepCompiledContracts`.

This theorem closes the runtime-spec assembly point directly from the split
contract surface (`CompileTreeWireSemantics ∧ AppendGateRightSemantics`).
-/
theorem runtimeSpec_of_splitContracts
    (hSplit : StepCompiledContractsSplit) :
    ∀ (M : TM) (n : Nat),
      StraightConfig.Spec
        (sc := Nat.iterate (StraightConfig.stepCompiledTruthTable M) (M.runTime n)
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

/--
Bridge variant of the internal compiler assembled from iterated runtime closure
plus the configuration-equality bridge.
-/
noncomputable def polyTMToStraightLineCompiler_internal_of_runtimeEq
    (hCfgEq : RuntimeConfigEqStepCompiled) :
    PolyTMToStraightLineCompiler :=
  polyTMToStraightLineCompiler_of_runtimeSpec
    (runtimeSpecProvider_internal_of_runtimeEq hCfgEq)

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

/--
Internal runtime-spec route that avoids the global evaluator-agreement contract
by using the specialized acceptance-circuit evaluator bridge proved in
`PsubsetPpolyInternal/Simulation.lean`.
-/
theorem P_subset_PpolyDAG_of_runtimeSpec_internal
    (hRuntime : InternalCompiler.RuntimeSpecProvider) :
    P_subset_PpolyDAG := by
  refine P_subset_PpolyDAG_of_P_subset_PpolyStraightLine ?_
  intro L hPL
  rcases exists_poly_tm_for_P (L := L) hPL with ⟨M, c, hRun, hCorrect⟩
  refine ⟨({
    polyBound := fun n => n ^ (c + 5) + (c + 5)
    polyBound_poly := ⟨c + 5, by
      intro n
      exact Nat.le_refl _⟩
    family := fun n => Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuit M n
    family_size_le := by
      intro n
      have hGates :
          (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuit M n).gates ≤
            Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.gatePolyBound M c n :=
        Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.straightAcceptCircuit_le_gatePolyBound
          (M := M) (c := c) hRun n
      have hSize :
          (toDag (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuit M n)).size ≤
            Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.gatePolyBound M c n + 1 := by
        simpa [size_toDag, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          Nat.add_le_add_right hGates 1
      have hMain : n ^ (c + 4) ≤ n ^ (c + 5) := InternalCompiler.degree_bound_main_term c n
      have hPow :
          Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.gatePolyBound M c n + 1 ≤
            n ^ (c + 5) + (c + 5) := by
        have hAdd :
            n ^ (c + 4) + (c + 4) + 1 ≤ n ^ (c + 5) + (c + 5) := by
          omega
        simpa [Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.gatePolyBound,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAdd
      exact Nat.le_trans hSize hPow
    correct := by
      intro n x
      have hSpec :
          Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.Spec
            (sc := Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfig M n)
            (f := fun y => M.run (n := n) y) :=
        hRuntime M n
      calc
        eval (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuit M n) x =
            Pnp3.Internal.PsubsetPpoly.StraightLine.eval
              (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuit M n) x :=
          Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuit_archive_eval_eq_internal
            (M := M) (n := n) (x := x)
        _ = TM.accepts M n x :=
          Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.straightAcceptCircuit_spec
            (M := M) (n := n) hSpec x
        _ = L n x := hCorrect n x
  } : InPpolyStraightLine L), trivial⟩

/--
Step-11 bridge: derive `P ⊆ PpolyDAG` from iterated runtime closure and
runtime-config equality bridge.
-/
theorem P_subset_PpolyDAG_of_iteratedRuntime
    (hRuntimeIter : InternalCompiler.RuntimeSpecProviderIterated)
    (hCfgEq : InternalCompiler.RuntimeConfigEqStepCompiled)
    (hEvalAgree : InternalCompiler.EvalAgreement) :
    P_subset_PpolyDAG :=
  P_subset_PpolyDAG_of_runtimeSpec
    (hRuntime := InternalCompiler.runtimeSpecProvider_of_iterated_eq hRuntimeIter hCfgEq)
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
        (sc := Nat.iterate (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.stepCompiledTruthTable M)
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
Public closed witness for one-step compiled contracts.
-/
theorem stepCompiledContracts_internal :
    InternalCompiler.StepCompiledContracts :=
  InternalCompiler.stepCompiledContracts_internal

/--
Public bridge: derive `StepCompiledSemanticsProvider` from gate-level append
contract.
-/
theorem stepCompiledSemanticsProvider_of_appendGateRight
    (hAppendGateRight : Pnp3.Internal.PsubsetPpoly.StraightLine.AppendGateRightSemantics) :
    InternalCompiler.StepCompiledSemanticsProvider :=
  InternalCompiler.stepCompiledSemanticsProvider_of_contracts
    (stepCompiledContracts_of_appendGateRight hAppendGateRight)

/--
Public closed iterated runtime-spec witness on the `stepCompiled` path.
-/
theorem runtimeSpec_iterated_internal :
    ∀ (M : TM) (n : Nat),
      Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.Spec
        (sc := Nat.iterate (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.stepCompiledTruthTable M)
          (M.runTime n) (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.initialStraightConfig M n))
        (f := fun x => M.run (n := n) x) :=
  InternalCompiler.runtimeSpec_iterated_internal

/--
Closed correctness statement for acceptance circuits built from the compiled
runtime configuration (`stepCompiled`-iterated path).
-/
theorem acceptCircuitCompiled_correct_internal :
    ∀ (M : TM) (n : Nat),
      Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.Spec
        (sc := Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiled M n)
        (f := fun y => M.run (n := n) y) →
      ∀ (x : Bitstring n),
        Pnp3.Internal.PsubsetPpoly.StraightLine.eval
          (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuitCompiled M n) x =
          TM.accepts M n x := by
  intro M n hRun x
  exact
    Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuitCompiled_spec_of_runSpec
      (M := M) (n := n) hRun x

/--
Residual correctness contract for acceptance circuits extracted from
`runtimeConfigCompiled`.
-/
def CompiledRuntimeAcceptCorrectness : Prop :=
  ∀ (M : TM) (n : Nat) (x : Bitstring n),
    Pnp3.Internal.PsubsetPpoly.StraightLine.eval
      (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuitCompiled M n) x =
      TM.accepts M n x

/--
Closed internal correctness witness for acceptance circuits extracted from
`runtimeConfigCompiled`.
-/
theorem compiledRuntimeAcceptCorrectness_internal :
    CompiledRuntimeAcceptCorrectness := by
  intro M n x
  have hRunIter :
      Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.Spec
        (sc := Nat.iterate
          (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.stepCompiledTruthTable M)
          (M.runTime n)
          (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.initialStraightConfig M n))
        (f := fun y => M.run (n := n) y) :=
    runtimeSpec_iterated_internal M n
  have hRun :
      Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.Spec
        (sc := Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiled M n)
        (f := fun y => M.run (n := n) y) := by
    simpa [Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiled,
      Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.stepCompiled] using hRunIter
  exact acceptCircuitCompiled_correct_internal M n hRun x

/--
Residual evaluator-agreement contract restricted to the compiled-runtime
acceptance-circuit family.
-/
def CompiledAcceptCircuitEvalAgreement : Prop :=
  ∀ (M : TM) (n : Nat) (x : Bitstring n),
    ArchiveStraightLineAdapter.eval
      (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuitCompiled M n) x =
      Pnp3.Internal.PsubsetPpoly.StraightLine.eval
        (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuitCompiled M n) x

/--
Residual size-bound contract restricted to the compiled-runtime acceptance
circuit family.
-/
def CompiledAcceptCircuitSizeBound : Prop :=
  ∀ (M : TM) (c : Nat)
    (_hRun : ∀ n, M.runTime n ≤ n ^ c + c),
    ∃ k, ∀ n,
      (toDag (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuitCompiled M n)).size ≤
        n ^ k + k

/--
Narrower evaluator-agreement contract: only the acceptance output wire of the
compiled runtime circuit needs agreement between archive and internal
semantics.
-/
def CompiledAcceptOutputWireAgreement : Prop :=
  ∀ (M : TM) (n : Nat) (x : Bitstring n),
    ArchiveStraightLineAdapter.evalWire
      (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiled M n).circuit x
      ((Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiled M n).state M.accept) =
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
      (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiled M n).circuit x
      ((Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiled M n).state M.accept)

/--
Wire-level archive/internal evaluator agreement for the whole compiled runtime
circuit. This is stronger than what is needed for acceptance output only.
-/
def CompiledRuntimeWireEvalAgreement : Prop :=
  ∀ (M : TM) (n : Nat) (x : Bitstring n)
    (i : Fin (n + (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiled M n).circuit.gates)),
    ArchiveStraightLineAdapter.evalWire
      (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiled M n).circuit x i =
    Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire
      (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiled M n).circuit x i

/--
Narrower size contract: polynomial DAG-size bound for the compiled runtime
base circuit (before output redirection).
-/
def CompiledRuntimeCircuitSizeBound : Prop :=
  ∀ (M : TM) (c : Nat)
    (_hRun : ∀ n, M.runTime n ≤ n ^ c + c),
    ∃ k, ∀ n,
      (toDag (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiled M n).circuit).size ≤
        n ^ k + k

/--
Relaxed size-bound variant (one-degree slack). Useful as an intermediate
target when proving tight size bounds is inconvenient.
-/
def CompiledRuntimeCircuitSizeBoundLoose : Prop :=
  ∀ (M : TM) (c : Nat)
    (_hRun : ∀ n, M.runTime n ≤ n ^ c + c),
    ∃ k, ∀ n,
      (toDag (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiled M n).circuit).size ≤
        n ^ k + k

theorem compiledAcceptOutputWireAgreement_of_runtimeWireEvalAgreement
    (hWire : CompiledRuntimeWireEvalAgreement) :
    CompiledAcceptOutputWireAgreement := by
  intro M n x
  exact hWire M n x
    ((Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiled M n).state M.accept)

theorem compiledRuntimeCircuitSizeBoundLoose_of_strict
    (hSize : CompiledRuntimeCircuitSizeBound) :
    CompiledRuntimeCircuitSizeBoundLoose := by
  intro M c hRun
  exact hSize M c hRun

theorem compiledAcceptEvalAgreement_of_outputWireAgreement
    (hOut : CompiledAcceptOutputWireAgreement) :
    CompiledAcceptCircuitEvalAgreement := by
  intro M n x
  let sc := Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiled M n
  have hArch :
      ArchiveStraightLineAdapter.eval
        (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuitCompiled M n) x =
      ArchiveStraightLineAdapter.evalWire sc.circuit x (sc.state M.accept) := by
    change ArchiveStraightLineAdapter.eval
      (ArchiveStraightLineAdapter.withOutput sc.circuit (sc.state M.accept)) x =
      ArchiveStraightLineAdapter.evalWire sc.circuit x (sc.state M.accept)
    rfl
  have hInt :
      Pnp3.Internal.PsubsetPpoly.StraightLine.eval
        (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuitCompiled M n) x =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire sc.circuit x (sc.state M.accept) := by
    simpa [Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuitCompiled,
      Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuitOf, sc] using
      (Pnp3.Internal.PsubsetPpoly.StraightLine.eval_withOutput_eq_evalWire
        (C := sc.circuit) (out := sc.state M.accept) (x := x))
  exact hArch.trans ((hOut M n x).trans hInt.symm)

theorem compiledAcceptOutputWireAgreement_of_compiledAcceptEvalAgreement
    (hEval : CompiledAcceptCircuitEvalAgreement) :
    CompiledAcceptOutputWireAgreement := by
  intro M n x
  let sc := Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiled M n
  have hArch :
      ArchiveStraightLineAdapter.eval
        (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuitCompiled M n) x =
      ArchiveStraightLineAdapter.evalWire sc.circuit x (sc.state M.accept) := by
    change ArchiveStraightLineAdapter.eval
      (ArchiveStraightLineAdapter.withOutput sc.circuit (sc.state M.accept)) x =
      ArchiveStraightLineAdapter.evalWire sc.circuit x (sc.state M.accept)
    rfl
  have hInt :
      Pnp3.Internal.PsubsetPpoly.StraightLine.eval
        (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuitCompiled M n) x =
      Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire sc.circuit x (sc.state M.accept) := by
    simpa [Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuitCompiled,
      Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuitOf, sc] using
      (Pnp3.Internal.PsubsetPpoly.StraightLine.eval_withOutput_eq_evalWire
        (C := sc.circuit) (out := sc.state M.accept) (x := x))
  exact hArch.symm.trans ((hEval M n x).trans hInt)

theorem compiledAcceptSizeBound_of_runtimeCircuitSizeBound
    (hSize : CompiledRuntimeCircuitSizeBound) :
    CompiledAcceptCircuitSizeBound := by
  intro M c hRun
  rcases hSize M c hRun with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  intro n
  have hBase :
      (toDag (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiled M n).circuit).size ≤
        n ^ k + k :=
    hk n
  simpa [size_toDag,
    Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuitCompiled_gates]
    using hBase

/--
Gate-count upper bound for compiled runtime circuits with the canonical
polynomial shape used downstream.
-/
def CompiledRuntimeCircuitGateBound : Prop :=
  ∀ (M : TM) (c : Nat)
    (_hRun : ∀ n, M.runTime n ≤ n ^ c + c),
    ∃ k, ∀ n,
      (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiled M n).circuit.gates ≤
        n ^ k + k

/--
Residual one-step increment obligation for the compiled runtime route:
`stepCompiled` must increase gate count by at most `linearStepBudgetExpanded`.
-/
def CompiledRuntimeStepIncrementBound : Prop :=
  ∀ (M : TM) (n : Nat)
    (sc : Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig M n),
    (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.stepCompiled M sc).circuit.gates ≤
      sc.circuit.gates +
        Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.BuiltWire.linearStepBudgetExpanded M n

/--
Linear-step variant of the one-step increment obligation.

This contract is already closed internally via the append-only builder route.
-/
def CompiledRuntimeStepIncrementBoundLinear : Prop :=
  ∀ (M : TM) (n : Nat)
    (sc : Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig M n),
    (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.stepCompiledLinearCandidate M sc).circuit.gates ≤
      sc.circuit.gates +
        Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.BuiltWire.linearStepBudgetExpanded M n

theorem compiledRuntimeStepIncrementBoundLinear_internal :
    CompiledRuntimeStepIncrementBoundLinear := by
  intro M n sc
  exact
    Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.stepCompiledLinearCandidate_gates_le_budgetExpanded
      (M := M) (sc := sc)

theorem compiledRuntimeStepIncrementBound_of_stepCompiled_eq_linear
    (hEq :
      ∀ (M : TM) (n : Nat)
        (sc : Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig M n),
        Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.stepCompiled M sc =
          Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.stepCompiledLinearCandidate M sc) :
    CompiledRuntimeStepIncrementBound := by
  intro M n sc
  simpa [hEq M n sc] using
    (compiledRuntimeStepIncrementBoundLinear_internal M n sc)

/--
Linear-runtime gate-count contract: same polynomial shape as the canonical
compiled-runtime gate contract, but for `runtimeConfigCompiledLinear`.
-/
def CompiledRuntimeCircuitGateBoundLinear : Prop :=
  ∀ (M : TM) (c : Nat)
    (_hRun : ∀ n, M.runTime n ≤ n ^ c + c),
    ∃ k, ∀ n,
      (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiledLinear M n).circuit.gates ≤
        n ^ k + k

/--
Linear-runtime size contract derived from `CompiledRuntimeCircuitGateBoundLinear`.
-/
def CompiledRuntimeCircuitSizeBoundLinear : Prop :=
  ∀ (M : TM) (c : Nat)
    (_hRun : ∀ n, M.runTime n ≤ n ^ c + c),
    ∃ k, ∀ n,
      (toDag
        (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiledLinear M n).circuit).size ≤
        n ^ k + k

/--
Residual polynomial-domination obligation for accumulated runtime budget:
`2 + runTime * linearStepBudgetExpanded` must be polynomially bounded.
-/
def CompiledRuntimeBudgetPolyBound : Prop :=
  ∀ (M : TM) (c : Nat)
    (_hRun : ∀ n, M.runTime n ≤ n ^ c + c),
    ∃ k, ∀ n,
      2 + M.runTime n *
          Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.BuiltWire.linearStepBudgetExpanded M n ≤
        n ^ k + k

/-- Any natural constant is bounded by `n^const` once `n ≥ 2`. -/
private lemma const_le_pow_of_two_le
    {n : Nat} (hn2 : 2 ≤ n) (m : Nat) :
    m ≤ n ^ m := by
  cases m with
  | zero =>
      simp
  | succ m =>
      have hlt : Nat.succ m < 2 ^ Nat.succ m := Nat.lt_two_pow_self
      have hpow : 2 ^ Nat.succ m ≤ n ^ Nat.succ m := Nat.pow_le_pow_left hn2 _
      exact Nat.le_trans (Nat.le_of_lt hlt) hpow

/--
If `a ≤ n^A` and `b ≤ n^B` (with `n ≥ 2`), then `a + b` is bounded by a
single power of `n` with one extra additive exponent slack.
-/
private lemma add_le_pow_of_le_pow
    {n a b A B : Nat}
    (hn2 : 2 ≤ n)
    (ha : a ≤ n ^ A)
    (hb : b ≤ n ^ B) :
    a + b ≤ n ^ (A + B + 1) := by
  have hn1 : 1 ≤ n := Nat.le_trans (by decide : 1 ≤ 2) hn2
  have ha' : a ≤ n ^ (A + B) := by
    exact Nat.le_trans ha (Nat.pow_le_pow_right hn1 (Nat.le_add_right A B))
  have hb' : b ≤ n ^ (A + B) := by
    have hB : B ≤ A + B := Nat.le_add_left B A
    exact Nat.le_trans hb (Nat.pow_le_pow_right hn1 hB)
  have hsum : a + b ≤ n ^ (A + B) + n ^ (A + B) := Nat.add_le_add ha' hb'
  have hstep : n ^ (A + B) + n ^ (A + B) ≤ n * n ^ (A + B) := by
    calc
      n ^ (A + B) + n ^ (A + B) = 2 * n ^ (A + B) := by omega
      _ ≤ n * n ^ (A + B) := Nat.mul_le_mul_right _ hn2
  calc
    a + b ≤ n ^ (A + B) + n ^ (A + B) := hsum
    _ ≤ n * n ^ (A + B) := hstep
    _ = n ^ (A + B + 1) := by
          simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- Multiplicative closure of `≤ n^k` bounds. -/
private lemma mul_le_pow_of_le_pow
    {n a b A B : Nat}
    (ha : a ≤ n ^ A)
    (hb : b ≤ n ^ B) :
    a * b ≤ n ^ (A + B) := by
  calc
    a * b ≤ n ^ A * n ^ B := Nat.mul_le_mul ha hb
    _ = n ^ (A + B) := by
          simp [Nat.pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/--
For `n ≥ 2`, a polytime bound `runTime n ≤ n^c + c` collapses to
`runTime n ≤ n^(c+1)`.
-/
private lemma runTime_le_pow_succ_of_poly
    (M : TM) (c n : Nat)
    (hn2 : 2 ≤ n)
    (hRun : M.runTime n ≤ n ^ c + c) :
    M.runTime n ≤ n ^ (c + 1) := by
  have hc : c ≤ n ^ c := const_le_pow_of_two_le hn2 c
  have h1 : n ^ c + c ≤ n ^ c + n ^ c := Nat.add_le_add_left hc (n ^ c)
  have h2 : n ^ c + n ^ c = 2 * n ^ c := by omega
  have h3 : 2 * n ^ c ≤ n * n ^ c := Nat.mul_le_mul_right _ hn2
  calc
    M.runTime n ≤ n ^ c + c := hRun
    _ ≤ n ^ c + n ^ c := h1
    _ = 2 * n ^ c := h2
    _ ≤ n * n ^ c := h3
    _ = n ^ (c + 1) := by
          simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/--
For `n ≥ 2`, tape length is bounded by a polynomial power `n^(c+3)` under the
same polytime assumption.
-/
private lemma tapeLength_le_pow_of_poly
    (M : TM) (c n : Nat)
    (hn2 : 2 ≤ n)
    (hRun : M.runTime n ≤ n ^ c + c) :
    M.tapeLength n ≤ n ^ (c + 3) := by
  have hn1 : 1 ≤ n := Nat.le_trans (by decide : 1 ≤ 2) hn2
  have hrt : M.runTime n ≤ n ^ (c + 1) :=
    runTime_le_pow_succ_of_poly (M := M) (c := c) (n := n) hn2 hRun
  have hn : n ≤ n ^ (c + 1) := Nat.le_self_pow (Nat.succ_ne_zero c) n
  have hOne : 1 ≤ n ^ (c + 1) := Nat.le_trans hn1 hn
  have hsum :
      n + M.runTime n + 1 ≤ n ^ (c + 1) + n ^ (c + 1) + n ^ (c + 1) := by
    omega
  have hthree : n ^ (c + 1) + n ^ (c + 1) + n ^ (c + 1) = 3 * n ^ (c + 1) := by omega
  have h3le : 3 ≤ n ^ 2 := by
    have h4 : 4 ≤ n * n := Nat.mul_le_mul hn2 hn2
    exact Nat.le_trans (by decide : 3 ≤ 4) (by simpa [pow_two] using h4)
  have hmul : 3 * n ^ (c + 1) ≤ n ^ 2 * n ^ (c + 1) := Nat.mul_le_mul_right _ h3le
  have hpow : n ^ 2 * n ^ (c + 1) = n ^ (c + 3) := by
    calc
      n ^ 2 * n ^ (c + 1) = n ^ (2 + (c + 1)) := by
        simpa [Nat.pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      _ = n ^ (c + 3) := by
        simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have htape : M.tapeLength n = n + M.runTime n + 1 := by
    rfl
  calc
    M.tapeLength n = n + M.runTime n + 1 := htape
    _ ≤ n ^ (c + 1) + n ^ (c + 1) + n ^ (c + 1) := hsum
    _ = 3 * n ^ (c + 1) := hthree
    _ ≤ n ^ 2 * n ^ (c + 1) := hmul
    _ = n ^ (c + 3) := hpow

theorem compiledRuntimeBudgetPolyBound_internal :
    CompiledRuntimeBudgetPolyBound := by
  intro M c hRun
  let S : Nat := Pnp3.Internal.PsubsetPpoly.Simulation.stateCard M
  let E1 : Nat := ((((1 + (c + 3)) + 2 + 1) + (1 + S)) + 3 + 1)
  let E2 : Nat := (((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S)) + 1 + 1)
  let E3 : Nat := (2 + (c + 3))
  let E4 : Nat := ((((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) + (c + 3))
  let E5 : Nat := ((((1 + (c + 3)) + 2 + 1) + (1 + S)) + S)
  let kBudget : Nat := (((E1 + E2 + 1) + E3 + 1) + E4 + 1) + E5 + 1
  let kCore : Nat := 1 + ((c + 1) + (kBudget + 3)) + 1
  let v0 : Nat :=
    2 + M.runTime 0 *
      Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.BuiltWire.linearStepBudgetExpanded M 0
  let v1 : Nat :=
    2 + M.runTime 1 *
      Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.BuiltWire.linearStepBudgetExpanded M 1
  refine ⟨max kCore (max v0 v1), ?_⟩
  intro n
  by_cases hn0 : n = 0
  · subst hn0
    have hk : v0 ≤ max kCore (max v0 v1) := by
      exact Nat.le_trans (Nat.le_max_left v0 v1) (Nat.le_max_right kCore (max v0 v1))
    exact Nat.le_trans hk (Nat.le_add_left _ _)
  · by_cases hn1 : n = 1
    · subst hn1
      have hk : v1 ≤ max kCore (max v0 v1) := by
        exact Nat.le_trans (Nat.le_max_right v0 v1) (Nat.le_max_right kCore (max v0 v1))
      exact Nat.le_trans hk (Nat.le_add_left _ _)
    · have hn2 : 2 ≤ n := by omega
      have hnPos : 1 ≤ n := Nat.le_trans (by decide : 1 ≤ 2) hn2
      let L : Nat := M.tapeLength n
      have hL : L ≤ n ^ (c + 3) := by
        simpa [L] using tapeLength_le_pow_of_poly (M := M) (c := c) (n := n) hn2 (hRun n)
      have hRunPow : M.runTime n ≤ n ^ (c + 1) :=
        runTime_le_pow_succ_of_poly (M := M) (c := c) (n := n) hn2 (hRun n)
      have hS : S ≤ n ^ S := by
        simpa [S] using const_le_pow_of_two_le (n := n) hn2 S
      have hOne : (1 : Nat) ≤ n ^ 1 := by
        simpa using hnPos
      have hTwo : (2 : Nat) ≤ n ^ 1 := by
        exact Nat.le_trans hn2 (by simpa using Nat.pow_le_pow_left hn2 (1 : Nat))
      have hFour : (4 : Nat) ≤ n ^ 2 := by
        have hmul : 4 ≤ n * n := Nat.mul_le_mul hn2 hn2
        simpa [pow_two] using hmul
      have hFive : (5 : Nat) ≤ n ^ 3 := by
        have h8 : 8 ≤ n ^ 3 := by
          have h2pow : 2 ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hn2 3
          simpa using h2pow
        exact Nat.le_trans (by decide : 5 ≤ 8) h8
      have h2L : 2 * L ≤ n ^ (1 + (c + 3)) := by
        exact mul_le_pow_of_le_pow (n := n) (a := 2) (b := L) (A := 1) (B := c + 3) hTwo hL
      have h2S : 2 * S ≤ n ^ (1 + S) := by
        exact mul_le_pow_of_le_pow (n := n) (a := 2) (b := S) (A := 1) (B := S) hTwo hS
      have h2L4 : 2 * L + 4 ≤ n ^ ((1 + (c + 3)) + 2 + 1) := by
        exact add_le_pow_of_le_pow (n := n) (a := 2 * L) (b := 4)
          (A := 1 + (c + 3)) (B := 2) hn2 h2L hFour
      have h2L5 : 2 * L + 5 ≤ n ^ ((1 + (c + 3)) + 3 + 1) := by
        exact add_le_pow_of_le_pow (n := n) (a := 2 * L) (b := 5)
          (A := 1 + (c + 3)) (B := 3) hn2 h2L hFive
      have hL2S : L * (2 * S) ≤ n ^ ((c + 3) + (1 + S)) := by
        exact mul_le_pow_of_le_pow (n := n) (a := L) (b := 2 * S)
          (A := c + 3) (B := 1 + S) hL h2S
      have hT1 : ((2 * L + 4) * (2 * S) + 5) ≤
          n ^ ((((1 + (c + 3)) + 2 + 1) + (1 + S)) + 3 + 1) := by
        have hProd :
            (2 * L + 4) * (2 * S) ≤ n ^ (((1 + (c + 3)) + 2 + 1) + (1 + S)) := by
          exact mul_le_pow_of_le_pow (n := n) (a := 2 * L + 4) (b := 2 * S)
            (A := ((1 + (c + 3)) + 2 + 1)) (B := 1 + S) h2L4 h2S
        exact add_le_pow_of_le_pow (n := n) (a := (2 * L + 4) * (2 * S)) (b := 5)
          (A := (((1 + (c + 3)) + 2 + 1) + (1 + S))) (B := 3) hn2 hProd hFive
      have hProd2 :
          (2 * L + 5) * (L * (2 * S)) ≤
            n ^ (((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) := by
        exact mul_le_pow_of_le_pow (n := n) (a := 2 * L + 5) (b := L * (2 * S))
          (A := ((1 + (c + 3)) + 3 + 1)) (B := ((c + 3) + (1 + S))) h2L5 hL2S
      have hT2 : ((2 * L + 5) * (L * (2 * S)) + 1) ≤
          n ^ ((((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) + 1 + 1) := by
        exact add_le_pow_of_le_pow (n := n) (a := (2 * L + 5) * (L * (2 * S))) (b := 1)
          (A := (((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S)))) (B := 1)
          hn2 hProd2 hOne
      have hT3 : 4 * L ≤ n ^ (2 + (c + 3)) := by
        exact mul_le_pow_of_le_pow (n := n) (a := 4) (b := L) (A := 2) (B := c + 3) hFour hL
      have hT4 : ((2 * L + 5) * (L * (2 * S))) * L ≤
          n ^ ((((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) + (c + 3)) := by
        exact mul_le_pow_of_le_pow (n := n)
          (a := ((2 * L + 5) * (L * (2 * S)))) (b := L)
          (A := (((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S)))) (B := c + 3) hProd2 hL
      have hProd1 :
          ((2 * L + 4) * (2 * S)) ≤ n ^ (((1 + (c + 3)) + 2 + 1) + (1 + S)) := by
        exact mul_le_pow_of_le_pow (n := n) (a := 2 * L + 4) (b := 2 * S)
          (A := ((1 + (c + 3)) + 2 + 1)) (B := (1 + S)) h2L4 h2S
      have hT5 : ((2 * L + 4) * (2 * S)) * S ≤
          n ^ ((((1 + (c + 3)) + 2 + 1) + (1 + S)) + S) := by
        exact mul_le_pow_of_le_pow (n := n) (a := ((2 * L + 4) * (2 * S))) (b := S)
          (A := (((1 + (c + 3)) + 2 + 1) + (1 + S))) (B := S) hProd1 hS
      have h12 : ((2 * L + 4) * (2 * S) + 5) + ((2 * L + 5) * (L * (2 * S)) + 1) ≤
          n ^ ((((((1 + (c + 3)) + 2 + 1) + (1 + S)) + 3 + 1) +
                ((((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) + 1 + 1)) + 1) := by
        exact add_le_pow_of_le_pow (n := n)
          (a := ((2 * L + 4) * (2 * S) + 5))
          (b := ((2 * L + 5) * (L * (2 * S)) + 1))
          (A := ((((1 + (c + 3)) + 2 + 1) + (1 + S)) + 3 + 1))
          (B := ((((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) + 1 + 1))
          hn2 hT1 hT2
      have h123 :
          (((2 * L + 4) * (2 * S) + 5) + ((2 * L + 5) * (L * (2 * S)) + 1)) + 4 * L ≤
            n ^ (((((((1 + (c + 3)) + 2 + 1) + (1 + S)) + 3 + 1) +
                ((((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) + 1 + 1)) + 1) +
                (2 + (c + 3)) + 1) := by
        exact add_le_pow_of_le_pow (n := n)
          (a := (((2 * L + 4) * (2 * S) + 5) + ((2 * L + 5) * (L * (2 * S)) + 1)))
          (b := 4 * L)
          (A := ((((((1 + (c + 3)) + 2 + 1) + (1 + S)) + 3 + 1) +
                ((((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) + 1 + 1)) + 1))
          (B := (2 + (c + 3)))
          hn2 h12 hT3
      have h1234 :
          ((((2 * L + 4) * (2 * S) + 5) + ((2 * L + 5) * (L * (2 * S)) + 1)) + 4 * L) +
              ((2 * L + 5) * (L * (2 * S))) * L ≤
            n ^ ((((((((1 + (c + 3)) + 2 + 1) + (1 + S)) + 3 + 1) +
                ((((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) + 1 + 1)) + 1) +
                (2 + (c + 3)) + 1) +
                ((((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) + (c + 3)) + 1) := by
        exact add_le_pow_of_le_pow (n := n)
          (a := ((((2 * L + 4) * (2 * S) + 5) + ((2 * L + 5) * (L * (2 * S)) + 1)) + 4 * L))
          (b := ((2 * L + 5) * (L * (2 * S))) * L)
          (A := (((((((1 + (c + 3)) + 2 + 1) + (1 + S)) + 3 + 1) +
                ((((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) + 1 + 1)) + 1) +
                (2 + (c + 3)) + 1))
          (B := ((((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) + (c + 3)))
          hn2 h123 hT4
      have h12345 :
          (((((2 * L + 4) * (2 * S) + 5) + ((2 * L + 5) * (L * (2 * S)) + 1)) + 4 * L) +
              ((2 * L + 5) * (L * (2 * S))) * L) + ((2 * L + 4) * (2 * S)) * S ≤
            n ^ kBudget := by
        have hRaw :
            (((((2 * L + 4) * (2 * S) + 5) + ((2 * L + 5) * (L * (2 * S)) + 1)) + 4 * L) +
                ((2 * L + 5) * (L * (2 * S))) * L) + ((2 * L + 4) * (2 * S)) * S ≤
              n ^ (((((((((1 + (c + 3)) + 2 + 1) + (1 + S)) + 3 + 1) +
                  ((((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) + 1 + 1)) + 1) +
                  (2 + (c + 3)) + 1) +
                  ((((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) + (c + 3)) + 1) +
                  ((((1 + (c + 3)) + 2 + 1) + (1 + S)) + S) + 1) := by
          exact add_le_pow_of_le_pow (n := n)
            (a := (((((2 * L + 4) * (2 * S) + 5) + ((2 * L + 5) * (L * (2 * S)) + 1)) + 4 * L) +
                  ((2 * L + 5) * (L * (2 * S))) * L))
            (b := ((2 * L + 4) * (2 * S)) * S)
            (A := ((((((((1 + (c + 3)) + 2 + 1) + (1 + S)) + 3 + 1) +
                  ((((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) + 1 + 1)) + 1) +
                  (2 + (c + 3)) + 1) +
                  ((((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) + (c + 3)) + 1))
            (B := ((((1 + (c + 3)) + 2 + 1) + (1 + S)) + S))
            hn2 h1234 hT5
        have hk :
            ((((((((1 + (c + 3)) + 2 + 1) + (1 + S)) + 3 + 1) +
                  ((((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) + 1 + 1)) + 1) +
                  (2 + (c + 3)) + 1) +
                  ((((1 + (c + 3)) + 3 + 1) + ((c + 3) + (1 + S))) + (c + 3)) + 1) +
                  ((((1 + (c + 3)) + 2 + 1) + (1 + S)) + S) + 1
              = kBudget := by
          simp [kBudget, E1, E2, E3, E4, E5, Nat.add_assoc]
        rw [← hk]
        exact hRaw
      have hBudgetPow :
          Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.BuiltWire.linearStepBudgetExpanded M n ≤
            n ^ (kBudget + 3) := by
        let oldBudget : Nat :=
          (((((2 * L + 4) * (2 * S) + 5) + ((2 * L + 5) * (L * (2 * S)) + 1)) + 4 * L) +
            ((2 * L + 5) * (L * (2 * S))) * L) + ((2 * L + 4) * (2 * S)) * S
        have hOld : oldBudget ≤ n ^ kBudget := by
          simpa [oldBudget] using h12345
        have hOld' : oldBudget ≤ n ^ (kBudget + 1) := by
          exact Nat.le_trans hOld (Nat.pow_le_pow_right hnPos (Nat.le_add_right kBudget 1))
        have hL' : L ≤ n ^ (kBudget + 1) := by
          exact Nat.le_trans hL (Nat.pow_le_pow_right hnPos (by omega))
        have hS' : S ≤ n ^ (kBudget + 1) := by
          exact Nat.le_trans hS (Nat.pow_le_pow_right hnPos (by omega))
        have hSum :
            oldBudget + L + S ≤ n ^ (kBudget + 1) + n ^ (kBudget + 1) + n ^ (kBudget + 1) := by
          have hTmp1 : oldBudget + L ≤ n ^ (kBudget + 1) + n ^ (kBudget + 1) :=
            Nat.add_le_add hOld' hL'
          have hTmp2 : oldBudget + L + S ≤
              (n ^ (kBudget + 1) + n ^ (kBudget + 1)) + n ^ (kBudget + 1) :=
            Nat.add_le_add hTmp1 hS'
          simpa [Nat.add_assoc] using hTmp2
        have hThree : n ^ (kBudget + 1) + n ^ (kBudget + 1) + n ^ (kBudget + 1) = 3 * n ^ (kBudget + 1) := by
          omega
        have h3le : 3 ≤ n ^ 2 := by
          have h4 : 4 ≤ n * n := Nat.mul_le_mul hn2 hn2
          exact Nat.le_trans (by decide : 3 ≤ 4) (by simpa [pow_two] using h4)
        have hMul : 3 * n ^ (kBudget + 1) ≤ n ^ 2 * n ^ (kBudget + 1) := Nat.mul_le_mul_right _ h3le
        have hPow : n ^ 2 * n ^ (kBudget + 1) = n ^ (kBudget + 3) := by
          calc
            n ^ 2 * n ^ (kBudget + 1) = n ^ (2 + (kBudget + 1)) := by
              simpa [Nat.pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
            _ = n ^ (kBudget + 3) := by
              have hk : 1 + (2 + kBudget) = 3 + kBudget := by omega
              simpa [hk, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        have hBudgetUpper :
            Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.BuiltWire.linearStepBudgetExpanded M n ≤
              oldBudget + L + S := by
          have hHeadSplit :
              (((2 * L + 5) * (L * (2 * S)) + 1) * L) =
                ((2 * L + 5) * (L * (2 * S))) * L + L := by
            rw [Nat.add_mul]
            simp
          have hStateSplit :
              (((2 * L + 4) * (2 * S) + 1) * S) =
                ((2 * L + 4) * (2 * S)) * S + S := by
            rw [Nat.add_mul]
            simp
          dsimp [oldBudget, L, S]
          unfold Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.BuiltWire.linearStepBudgetExpanded
          rw [hHeadSplit, hStateSplit]
          apply le_of_eq
          ac_rfl
        calc
          Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.BuiltWire.linearStepBudgetExpanded M n
              ≤ oldBudget + L + S := hBudgetUpper
          _ ≤ n ^ (kBudget + 1) + n ^ (kBudget + 1) + n ^ (kBudget + 1) := hSum
          _ = 3 * n ^ (kBudget + 1) := hThree
          _ ≤ n ^ 2 * n ^ (kBudget + 1) := hMul
          _ = n ^ (kBudget + 3) := hPow
      have hMul :
          M.runTime n *
              Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.BuiltWire.linearStepBudgetExpanded M n ≤
            n ^ ((c + 1) + (kBudget + 3)) := by
        exact mul_le_pow_of_le_pow (n := n)
          (a := M.runTime n)
          (b := Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.BuiltWire.linearStepBudgetExpanded M n)
          (A := c + 1) (B := kBudget + 3) hRunPow hBudgetPow
      have hMain :
          2 + M.runTime n *
              Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.BuiltWire.linearStepBudgetExpanded M n ≤
            n ^ kCore := by
        have hRaw :
            2 + M.runTime n *
                Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.BuiltWire.linearStepBudgetExpanded M n ≤
              n ^ (1 + ((c + 1) + (kBudget + 3)) + 1) := by
          exact add_le_pow_of_le_pow (n := n) (a := 2)
            (b := M.runTime n *
              Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.BuiltWire.linearStepBudgetExpanded M n)
            (A := 1) (B := (c + 1) + (kBudget + 3)) hn2 hTwo hMul
        have hk : 1 + ((c + 1) + (kBudget + 3)) + 1 = kCore := by
          simp [kCore]
        simpa [hk] using hRaw
      have hkCore : kCore ≤ max kCore (max v0 v1) := Nat.le_max_left _ _
      have hPowLift : n ^ kCore ≤ n ^ (max kCore (max v0 v1)) :=
        Nat.pow_le_pow_right hnPos hkCore
      exact Nat.le_trans hMain (Nat.le_trans hPowLift (Nat.le_add_right _ _))

/--
Linear-route reduction of `CompiledRuntimeCircuitGateBoundLinear`:
the one-step increment side is closed internally (`stepCompiledLinear`), so only
the residual polynomial-domination obligation remains explicit.
-/
theorem compiledRuntimeCircuitGateBoundLinear_of_budgetPoly
    (hBudgetPoly : CompiledRuntimeBudgetPolyBound) :
    CompiledRuntimeCircuitGateBoundLinear := by
  intro M c hRun
  rcases hBudgetPoly M c hRun with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  intro n
  have hIter :
      (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiledLinear M n).circuit.gates ≤
        2 + M.runTime n *
          Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.BuiltWire.linearStepBudgetExpanded M n :=
    Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiledLinear_gates_le_budgetExpanded
      (M := M) (n := n)
  exact Nat.le_trans hIter (hk n)

theorem compiledRuntimeCircuitGateBoundLinear_internal :
    CompiledRuntimeCircuitGateBoundLinear :=
  compiledRuntimeCircuitGateBoundLinear_of_budgetPoly
    compiledRuntimeBudgetPolyBound_internal

/--
Bundle of the two remaining local obligations needed to close compiled-runtime
size bounds.
-/
def CompiledRuntimeGateClosureContracts : Prop :=
  CompiledRuntimeStepIncrementBound ∧ CompiledRuntimeBudgetPolyBound

/--
Reduction of `CompiledRuntimeCircuitGateBound` to two local obligations:
1. one-step gate increment by `linearStepBudgetExpanded`;
2. polynomial domination of accumulated runtime budget.

This isolates the remaining nontrivial closure work in a single theorem shape.
-/
theorem compiledRuntimeCircuitGateBound_of_linearBudget
    (hStepInc : CompiledRuntimeStepIncrementBound)
    (hBudgetPoly : CompiledRuntimeBudgetPolyBound) :
    CompiledRuntimeCircuitGateBound := by
  intro M c hRun
  rcases hBudgetPoly M c hRun with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  intro n
  have hIter :
      (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiled M n).circuit.gates ≤
        2 + M.runTime n *
          Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.BuiltWire.linearStepBudgetExpanded M n :=
    Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiled_gates_le_of_stepCompiled_inc'
      (M := M) (n := n)
      (inc := Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.BuiltWire.linearStepBudgetExpanded M n)
      (hStepInc := hStepInc M n)
  exact Nat.le_trans hIter (hk n)

theorem compiledRuntimeCircuitSizeBound_of_gateBound
    (hGate : CompiledRuntimeCircuitGateBound) :
    CompiledRuntimeCircuitSizeBound := by
  intro M c hRun
  rcases hGate M c hRun with ⟨k, hk⟩
  refine ⟨k + 2, ?_⟩
  intro n
  have hGates :
      (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiled M n).circuit.gates ≤
        n ^ k + k :=
    hk n
  have hSize :
      (toDag (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiled M n).circuit).size ≤
        (n ^ k + k) + 1 := by
    simpa [size_toDag, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Nat.add_le_add_right hGates 1
  have hTarget :
      (n ^ k + k) + 1 ≤ n ^ (k + 2) + (k + 2) := by
    by_cases hn : n = 0
    · subst hn
      cases k with
      | zero =>
          simp
      | succ k' =>
          simp
    · have hpow : n ^ k ≤ n ^ (k + 2) := by
        have h1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
        simpa [Nat.add_assoc] using Nat.pow_le_pow_right h1 (Nat.le_add_right k 2)
      have hk1 : k + 1 ≤ k + 2 := Nat.le_succ (k + 1)
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using Nat.add_le_add hpow hk1
  exact le_trans hSize hTarget

theorem compiledRuntimeCircuitSizeBoundLinear_of_gateBound
    (hGate : CompiledRuntimeCircuitGateBoundLinear) :
    CompiledRuntimeCircuitSizeBoundLinear := by
  intro M c hRun
  rcases hGate M c hRun with ⟨k, hk⟩
  refine ⟨k + 2, ?_⟩
  intro n
  have hGates :
      (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiledLinear M n).circuit.gates ≤
        n ^ k + k :=
    hk n
  have hSize :
      (toDag
        (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiledLinear M n).circuit).size ≤
        (n ^ k + k) + 1 := by
    simpa [size_toDag, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Nat.add_le_add_right hGates 1
  have hTarget :
      (n ^ k + k) + 1 ≤ n ^ (k + 2) + (k + 2) := by
    by_cases hn : n = 0
    · subst hn
      cases k with
      | zero =>
          simp
      | succ k' =>
          simp
    · have hpow : n ^ k ≤ n ^ (k + 2) := by
        have h1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
        simpa [Nat.add_assoc] using Nat.pow_le_pow_right h1 (Nat.le_add_right k 2)
      have hk1 : k + 1 ≤ k + 2 := Nat.le_succ (k + 1)
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using Nat.add_le_add hpow hk1
  exact le_trans hSize hTarget

theorem compiledRuntimeCircuitSizeBoundLinear_internal :
    CompiledRuntimeCircuitSizeBoundLinear :=
  compiledRuntimeCircuitSizeBoundLinear_of_gateBound
    compiledRuntimeCircuitGateBoundLinear_internal

/--
One-shot closure theorem for the compiled-runtime size contract from the two
local residual obligations.
-/
theorem compiledRuntimeCircuitSizeBound_of_gateClosureContracts
    (hContracts : CompiledRuntimeGateClosureContracts) :
    CompiledRuntimeCircuitSizeBound :=
  compiledRuntimeCircuitSizeBound_of_gateBound
    (compiledRuntimeCircuitGateBound_of_linearBudget hContracts.1 hContracts.2)

theorem compiledRuntimeCircuitSizeBound_internal_of_stepCompiled_eq_linear
    (hEq :
      ∀ (M : TM) (n : Nat)
        (sc : Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig M n),
        Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.stepCompiled M sc =
          Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.stepCompiledLinearCandidate M sc) :
    CompiledRuntimeCircuitSizeBound := by
  have hStepInc : CompiledRuntimeStepIncrementBound :=
    compiledRuntimeStepIncrementBound_of_stepCompiled_eq_linear hEq
  have hBudget : CompiledRuntimeBudgetPolyBound :=
    compiledRuntimeBudgetPolyBound_internal
  exact compiledRuntimeCircuitSizeBound_of_gateClosureContracts ⟨hStepInc, hBudget⟩

/--
Internal runtime-only contract bundle closed from a single semantic switch-point
hypothesis (`stepCompiled = stepCompiledLinearCandidate`).
-/
theorem iteratedRuntimeOnlyContracts_internal_of_stepCompiled_eq_linear
    (hOut : CompiledAcceptOutputWireAgreement)
    (hEq :
      ∀ (M : TM) (n : Nat)
        (sc : Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig M n),
        Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.stepCompiled M sc =
          Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.stepCompiledLinearCandidate M sc) :
    CompiledAcceptOutputWireAgreement ∧
      CompiledRuntimeCircuitSizeBound ∧
      CompiledRuntimeAcceptCorrectness := by
  refine ⟨?_, ?_, ?_⟩
  · exact hOut
  · exact compiledRuntimeCircuitSizeBound_internal_of_stepCompiled_eq_linear hEq
  · exact compiledRuntimeAcceptCorrectness_internal

theorem compiledAcceptOutputWireAgreement_of_evalAgreement
    (hEval : InternalCompiler.EvalAgreement) :
    CompiledAcceptOutputWireAgreement := by
  intro M n x
  let sc := Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiled M n
  let Cacc :
      StraightLineCircuit n :=
    Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuitOf M sc
  have hC : ArchiveStraightLineAdapter.eval Cacc x =
      Pnp3.Internal.PsubsetPpoly.StraightLine.eval Cacc x :=
    hEval (C := Cacc) (x := x)
  have hArch :
      ArchiveStraightLineAdapter.eval Cacc x =
        ArchiveStraightLineAdapter.evalWire sc.circuit x (sc.state M.accept) := by
    change ArchiveStraightLineAdapter.eval
      (ArchiveStraightLineAdapter.withOutput sc.circuit (sc.state M.accept)) x =
      ArchiveStraightLineAdapter.evalWire sc.circuit x (sc.state M.accept)
    rfl
  have hInt :
      Pnp3.Internal.PsubsetPpoly.StraightLine.eval Cacc x =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire sc.circuit x (sc.state M.accept) := by
    simpa [Cacc, Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuitOf, sc] using
      (Pnp3.Internal.PsubsetPpoly.StraightLine.eval_withOutput_eq_evalWire
        (C := sc.circuit) (out := sc.state M.accept) (x := x))
  exact hArch.symm.trans (hC.trans hInt)

/--
Global archive/internal evaluator agreement implies wire-level agreement on the
entire compiled-runtime base circuit.
-/
theorem compiledRuntimeWireEvalAgreement_of_evalAgreement
    (hEval : InternalCompiler.EvalAgreement) :
    CompiledRuntimeWireEvalAgreement := by
  intro M n x i
  let Cbase := (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.runtimeConfigCompiled M n).circuit
  have hC :
      ArchiveStraightLineAdapter.eval (ArchiveStraightLineAdapter.withOutput Cbase i) x =
      Pnp3.Internal.PsubsetPpoly.StraightLine.eval
        (ArchiveStraightLineAdapter.withOutput Cbase i) x :=
    hEval (C := ArchiveStraightLineAdapter.withOutput Cbase i) (x := x)
  have hArch :
      ArchiveStraightLineAdapter.eval (ArchiveStraightLineAdapter.withOutput Cbase i) x =
        ArchiveStraightLineAdapter.evalWire Cbase x i := by
    rfl
  have hInt :
      Pnp3.Internal.PsubsetPpoly.StraightLine.eval
          (ArchiveStraightLineAdapter.withOutput Cbase i) x =
        Pnp3.Internal.PsubsetPpoly.StraightLine.evalWire Cbase x i := by
    simpa [Cbase] using
      (Pnp3.Internal.PsubsetPpoly.StraightLine.eval_withOutput_eq_evalWire
        (C := Cbase) (out := i) (x := x))
  exact hArch.symm.trans (hC.trans hInt)

theorem compiledAcceptContracts_of_outputAndRuntimeSize
    (hOut : CompiledAcceptOutputWireAgreement)
    (hSize : CompiledRuntimeCircuitSizeBound) :
    CompiledAcceptCircuitEvalAgreement ∧ CompiledAcceptCircuitSizeBound := by
  exact
    ⟨ compiledAcceptEvalAgreement_of_outputWireAgreement hOut
    , compiledAcceptSizeBound_of_runtimeCircuitSizeBound hSize ⟩

theorem compiledAcceptContracts_of_wireAndRuntimeSize
    (hWire : CompiledRuntimeWireEvalAgreement)
    (hSize : CompiledRuntimeCircuitSizeBound) :
    CompiledAcceptCircuitEvalAgreement ∧ CompiledAcceptCircuitSizeBound :=
  compiledAcceptContracts_of_outputAndRuntimeSize
    (compiledAcceptOutputWireAgreement_of_runtimeWireEvalAgreement hWire)
    hSize

/--
Compiled-runtime DAG route with a minimal explicit residual contract surface:
only size bound and archive/internal evaluator agreement for the
`acceptCircuitCompiled` family.
-/
theorem P_subset_PpolyDAG_of_compiledRuntimeContracts
    (hEval : CompiledAcceptCircuitEvalAgreement)
    (hSize : CompiledAcceptCircuitSizeBound)
    (hCorrectCompiled : CompiledRuntimeAcceptCorrectness) :
    P_subset_PpolyDAG := by
  refine P_subset_PpolyDAG_of_P_subset_PpolyStraightLine ?_
  intro L hPL
  rcases exists_poly_tm_for_P (L := L) hPL with ⟨M, c, hRun, hLangCorrect⟩
  rcases hSize M c hRun with ⟨k, hk⟩
  refine ⟨({
    polyBound := fun n => n ^ k + k
    polyBound_poly := ⟨k, by
      intro n
      exact Nat.le_refl _⟩
    family := fun n => Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuitCompiled M n
    family_size_le := by
      intro n
      exact hk n
    correct := by
      intro n x
      calc
        eval (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuitCompiled M n) x =
            Pnp3.Internal.PsubsetPpoly.StraightLine.eval
              (Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.acceptCircuitCompiled M n) x :=
          hEval M n x
        _ = TM.accepts M n x :=
          hCorrectCompiled M n x
        _ = L n x := hLangCorrect n x
  } : InPpolyStraightLine L), trivial⟩

theorem proved_P_subset_PpolyDAG_of_compiledRuntimeOutputAndSize
    (hOut : CompiledAcceptOutputWireAgreement)
    (hSize : CompiledRuntimeCircuitSizeBound)
    (hCorrectCompiled : CompiledRuntimeAcceptCorrectness) :
    P_subset_PpolyDAG := by
  have hContracts : CompiledAcceptCircuitEvalAgreement ∧ CompiledAcceptCircuitSizeBound :=
    compiledAcceptContracts_of_outputAndRuntimeSize hOut hSize
  exact P_subset_PpolyDAG_of_compiledRuntimeContracts hContracts.1 hContracts.2 hCorrectCompiled

theorem proved_P_subset_PpolyDAG_of_compiledRuntimeWireAndSize
    (hWire : CompiledRuntimeWireEvalAgreement)
    (hSize : CompiledRuntimeCircuitSizeBound)
    (hCorrectCompiled : CompiledRuntimeAcceptCorrectness) :
    P_subset_PpolyDAG := by
  have hContracts : CompiledAcceptCircuitEvalAgreement ∧ CompiledAcceptCircuitSizeBound :=
    compiledAcceptContracts_of_wireAndRuntimeSize hWire hSize
  exact P_subset_PpolyDAG_of_compiledRuntimeContracts hContracts.1 hContracts.2 hCorrectCompiled

/--
Bridge closure route: if global evaluator agreement is available, then together
with compiled-runtime size bounds it immediately yields `P ⊆ PpolyDAG`.
-/
theorem proved_P_subset_PpolyDAG_of_evalAgreementAndRuntimeSize
    (hEval : InternalCompiler.EvalAgreement)
    (hSize : CompiledRuntimeCircuitSizeBound)
    (hCorrectCompiled : CompiledRuntimeAcceptCorrectness) :
    P_subset_PpolyDAG :=
  proved_P_subset_PpolyDAG_of_compiledRuntimeWireAndSize
    (compiledRuntimeWireEvalAgreement_of_evalAgreement hEval)
    hSize hCorrectCompiled

/--
Minimal default contract bundle for the internal `P ⊆ P/poly` route.

The default route is runtime-only and does not require the global evaluator
agreement contract.
-/
def PsubsetPpolyInternalContracts : Prop :=
  InternalCompiler.RuntimeSpecProvider

/--
Legacy bundle for compatibility with the original bridge route
(`RuntimeSpecProvider ∧ EvalAgreement`).
-/
def PsubsetPpolyInternalContractsLegacy : Prop :=
  InternalCompiler.RuntimeSpecProvider ∧ InternalCompiler.EvalAgreement

/--
Iterated-runtime variant of the minimal internal contract bundle.

This is the constructive shape produced by the closed `stepCompiled` path.
-/
def PsubsetPpolyInternalContractsIterated : Prop :=
  InternalCompiler.RuntimeSpecProviderIterated ∧ InternalCompiler.EvalAgreement

/--
Iterated-runtime bundle without the global evaluator-agreement contract.

This is the runtime-only variant of the iterated bridge route.
-/
def PsubsetPpolyInternalContractsIteratedRuntimeOnly : Prop :=
  CompiledAcceptOutputWireAgreement ∧
    CompiledRuntimeCircuitSizeBound ∧
    CompiledRuntimeAcceptCorrectness

/--
Canonical iterated contract bundle for the active internal DAG route.

Kept as a stable name so downstream code can avoid legacy "bridge" naming.
-/
abbrev PsubsetPpolyInternalContractsIteratedCanonical : Prop :=
  PsubsetPpolyInternalContractsIteratedRuntimeOnly

/--
Iterated-contract bundle augmented with the runtime-config equality bridge.
-/
def PsubsetPpolyInternalContractsIteratedBridged : Prop :=
  InternalCompiler.RuntimeSpecProviderIterated ∧
  InternalCompiler.RuntimeConfigEqStepCompiled ∧
  InternalCompiler.EvalAgreement

/--
Compiled-runtime contract bundle with minimized residual obligations.
-/
def PsubsetPpolyCompiledRuntimeContracts : Prop :=
  CompiledAcceptCircuitEvalAgreement ∧
    CompiledAcceptCircuitSizeBound ∧
    CompiledRuntimeAcceptCorrectness

/--
Step-11 contract closure theorem: once the two remaining internal contracts are
available, `P_subset_PpolyDAG` follows immediately.
-/
theorem proved_P_subset_PpolyDAG_of_contracts
    (hContracts : PsubsetPpolyInternalContracts) :
    P_subset_PpolyDAG := by
  exact P_subset_PpolyDAG_of_runtimeSpec_internal hContracts

/--
Legacy closure theorem for routes that still consume global evaluator
agreement as an explicit contract.
-/
theorem proved_P_subset_PpolyDAG_of_legacyContracts
    (hContracts : PsubsetPpolyInternalContractsLegacy) :
    P_subset_PpolyDAG := by
  rcases hContracts with ⟨hRuntime, hEvalAgree⟩
  exact P_subset_PpolyDAG_of_runtimeSpec hRuntime hEvalAgree

/--
Runtime-only closure route for the internal compiler track.

This path is useful when the goal is to avoid the global evaluator-agreement
contract and rely only on the specialized acceptance-circuit bridge.
-/
theorem proved_P_subset_PpolyDAG_of_runtimeOnly
    (hRuntime : InternalCompiler.RuntimeSpecProvider) :
    P_subset_PpolyDAG :=
  P_subset_PpolyDAG_of_runtimeSpec_internal hRuntime

/--
Iterated-contract closure route. The only additional bridge required to recover
the current compiler theorem is equality between `runtimeConfig` and the
iterated `stepCompiled` configuration.
-/
theorem proved_P_subset_PpolyDAG_of_iteratedContracts
    (hContracts : PsubsetPpolyInternalContractsIterated)
    (hCfgEq : InternalCompiler.RuntimeConfigEqStepCompiled) :
    P_subset_PpolyDAG := by
  rcases hContracts with ⟨hRuntimeIter, hEvalAgree⟩
  have hRuntime : InternalCompiler.RuntimeSpecProvider :=
    InternalCompiler.runtimeSpecProvider_of_iterated_eq hRuntimeIter hCfgEq
  exact P_subset_PpolyDAG_of_runtimeSpec hRuntime hEvalAgree

/--
Contract closure theorem for the bridged iterated bundle (no extra arguments).
-/
theorem proved_P_subset_PpolyDAG_of_iteratedContractsBridged
    (hContracts : PsubsetPpolyInternalContractsIteratedBridged) :
    P_subset_PpolyDAG := by
  rcases hContracts with ⟨hRuntimeIter, hCfgEq, hEvalAgree⟩
  exact P_subset_PpolyDAG_of_iteratedRuntime hRuntimeIter hCfgEq hEvalAgree

/--
Runtime-only iterated closure route.

This route keeps the iterated runtime witness while routing closure through the
compiled-runtime residual bundle, and avoids both the global
evaluator-agreement contract and the runtime-config equality bridge.
-/
theorem proved_P_subset_PpolyDAG_of_iteratedRuntimeOnlyContracts
    (hContracts : PsubsetPpolyInternalContractsIteratedRuntimeOnly) :
    P_subset_PpolyDAG := by
  rcases hContracts with ⟨hOut, hSize, hCorrectCompiled⟩
  exact proved_P_subset_PpolyDAG_of_compiledRuntimeOutputAndSize
    hOut hSize hCorrectCompiled

/--
Canonical iterated closure theorem for the active internal DAG route.
-/
theorem proved_P_subset_PpolyDAG_of_iteratedCanonicalContracts
    (hContracts : PsubsetPpolyInternalContractsIteratedCanonical) :
    P_subset_PpolyDAG :=
  proved_P_subset_PpolyDAG_of_iteratedRuntimeOnlyContracts hContracts

/--
Near-final internal closure route from a single switch-point hypothesis.

Once `stepCompiled` is identified with `stepCompiledLinearCandidate`, the
runtime-only canonical bundle is closed internally and yields `P_subset_PpolyDAG`.
-/
theorem proved_P_subset_PpolyDAG_of_stepCompiled_eq_linear
    (hOut : CompiledAcceptOutputWireAgreement)
    (hEq :
      ∀ (M : TM) (n : Nat)
        (sc : Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig M n),
        Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.stepCompiled M sc =
          Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.stepCompiledLinearCandidate M sc) :
    P_subset_PpolyDAG := by
  have hContracts : PsubsetPpolyInternalContractsIteratedCanonical :=
    iteratedRuntimeOnlyContracts_internal_of_stepCompiled_eq_linear hOut hEq
  exact proved_P_subset_PpolyDAG_of_iteratedCanonicalContracts hContracts

/--
Convenience closure route from global eval agreement plus switch-point equality.

This discharges the output-wire agreement contract internally and leaves only
the semantic switch-point hypothesis explicit.
-/
theorem proved_P_subset_PpolyDAG_of_evalAgreement_and_stepCompiled_eq_linear
    (hEval : InternalCompiler.EvalAgreement)
    (hEq :
      ∀ (M : TM) (n : Nat)
        (sc : Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig M n),
        Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.stepCompiled M sc =
          Pnp3.Internal.PsubsetPpoly.Simulation.StraightConfig.stepCompiledLinearCandidate M sc) :
    P_subset_PpolyDAG := by
  have hOut : CompiledAcceptOutputWireAgreement :=
    compiledAcceptOutputWireAgreement_of_evalAgreement hEval
  exact proved_P_subset_PpolyDAG_of_stepCompiled_eq_linear hOut hEq

/--
Compiled-runtime closure route from the minimized residual contract bundle.
-/
theorem proved_P_subset_PpolyDAG_of_compiledRuntimeContracts
    (hContracts : PsubsetPpolyCompiledRuntimeContracts) :
    P_subset_PpolyDAG := by
  rcases hContracts with ⟨hEval, hSize, hCorrectCompiled⟩
  exact P_subset_PpolyDAG_of_compiledRuntimeContracts hEval hSize hCorrectCompiled

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
