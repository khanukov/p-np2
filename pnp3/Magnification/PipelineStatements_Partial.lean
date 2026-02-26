import LowerBounds.LB_Formulas_Core_Partial
import Models.Model_PartialMCSP
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
  pnp3/Magnification/PipelineStatements_Partial.lean

  Partial‑версия формулировок шага C для дальнейшей магнификации.

  Мы переносим те же структуры, что и в `PipelineStatements.lean`,
  но теперь параметры и решатели относятся к Partial MCSP.
  На этом этапе фиксируем только формульный (AC⁰) трек в
  семантической/конструктивной форме:

  * `AC0StatementPartial_semantic`;
  * `AC0BoundedStatementPartial_semantic`;
  * `FormulaLowerBoundHypothesisPartial`.

  Локальные/общие схемы будут добавлены после интеграции partial‑версии
  locality‑lift (см. `PARTIAL_MCSP_PLAN.md`, шаг 5).
-/

namespace Pnp3
namespace Magnification

open Models
open LowerBounds

/-!
  ### Формульные гипотезы для Partial MCSP
-/

/-!
  ## Semantic Step-C API (non-vacuous)

  These predicates are the active Step-C interface:
  they quantify over concrete solvers and require solver-local AC0 witnesses.
-/

/-- Semantic (family-level counting) Step-C statement. -/
def AC0StatementPartial_semantic (p : GapPartialMCSPParams) : Prop :=
  ∀ solver : SmallAC0Solver_Partial p,
    AC0EasyFamilyDataPartial solver.params.ac0 → False

/--
Primary Step-C contract for the partial pipeline.

This keeps the name used by downstream code while giving it the non-vacuous
semantic meaning (`solver`-local easy-family package), with no dependence on
legacy global witnesses.
-/
abbrev AC0StatementPartial (p : GapPartialMCSPParams) : Prop :=
  AC0StatementPartial_semantic p

/--
Constructive (non-vacuous) Step-C statement:
quantifies over solver packages that carry easy-family data internally.
-/
def AC0StatementPartial_constructive (p : GapPartialMCSPParams) : Prop :=
  ∀ _solver : ConstructiveSmallAC0Solver_Partial p, False

/--
Closed-world constructive Step-C statement.

This is the strongest in-repo interface for Step-C in the current architecture:
it quantifies over syntactic solver packages that already carry explicit AC0
syntax and family-level easy-data, so the contradiction has no extra
`hEasy/hComp` arguments.
-/
def AC0StatementPartial_closed (p : GapPartialMCSPParams) : Prop :=
  ∀ _solver : SmallAC0Solver_Partial_Syntactic p, False

/--
Solver-local provider-style closed Step-C statement.

This is the "residual math" interface: each solver comes with its own
`StepCClosureDataPartialProvider` package.
-/
def AC0StatementPartial_providerClosed (p : GapPartialMCSPParams) : Prop :=
  ∀ solver : SmallAC0Solver_Partial p,
    StepCClosureDataPartialProvider solver → False

/--
Constructive solver-package variant of provider-closed Step-C.

Compared to `AC0StatementPartial_providerClosed`, this formulation quantifies
over `ConstructiveSmallAC0Solver_Partial`, so provider data can be built from
the internally carried `easyData` package.
-/
def AC0StatementPartial_constructive_providerClosed (p : GapPartialMCSPParams) : Prop :=
  ∀ _solver : ConstructiveSmallAC0Solver_Partial p, False

/--
Fully closed semantic Step-C statement over plain semantic solvers.

This statement is parameterized by an explicit closure package that
constructs family-level easy-data from each semantic solver.
-/
def AC0StatementPartial_fully_closed (p : GapPartialMCSPParams) : Prop :=
  ∀ _closure : StepCClosureDataPartial p,
    ∀ _solver : SmallAC0Solver_Partial p, False

/-- Bounded semantic Step-C statement. -/
def AC0BoundedStatementPartial_semantic
    (p : GapPartialMCSPParams) (ε : Rat) : Prop :=
  ∀ solver : SmallAC0Solver_Partial p,
    (solver.params.ac0.M : Real) ≤
      Real.rpow (Models.partialInputLen p) (1 + (ε : Real)) →
    AC0EasyFamilyDataPartial solver.params.ac0 → False

/-- Bounded constructive Step-C statement. -/
def AC0BoundedStatementPartial_constructive
    (p : GapPartialMCSPParams) (ε : Rat) : Prop :=
  ∀ solver : ConstructiveSmallAC0Solver_Partial p,
    (solver.params.ac0.M : Real) ≤
      Real.rpow (Models.partialInputLen p) (1 + (ε : Real)) →
    False

/--
  Формульная гипотеза для OPS в partial‑треке.
-/
def FormulaLowerBoundHypothesisPartial
    (p : GapPartialMCSPParams) (δ : Rat) : Prop :=
  (0 : Rat) < δ ∧ AC0BoundedStatementPartial_semantic p δ

/-- Semantic counterpart of `FormulaLowerBoundHypothesisPartial`. -/
abbrev FormulaLowerBoundHypothesisPartial_semantic
    (p : GapPartialMCSPParams) (δ : Rat) : Prop :=
  FormulaLowerBoundHypothesisPartial p δ

/-!
  ### Выводы шага C в partial‑треке
-/

/--
Build the semantic formula lower-bound hypothesis from an explicit semantic
bounded Step-C statement.
-/
lemma formula_hypothesis_from_semantic_stepC_partial
    (p : GapPartialMCSPParams) (δ : Rat) (hδ : (0 : Rat) < δ)
    (hStepC : AC0BoundedStatementPartial_semantic p δ) :
    FormulaLowerBoundHypothesisPartial_semantic p δ := by
  exact ⟨hδ, hStepC⟩

/--
Semantic AC0 statement from the family-level counting core.
-/
lemma ac0_statement_from_pipeline_partial_semantic
    (p : GapPartialMCSPParams) : AC0StatementPartial_semantic p := by
  intro solver easy
  exact LB_Formulas_core_partial_of_easyFamilyData (solver := solver) easy

/-- Main non-vacuous Step-C statement from the pipeline core. -/
lemma ac0_statement_from_pipeline_partial
    (p : GapPartialMCSPParams) : AC0StatementPartial p :=
  ac0_statement_from_pipeline_partial_semantic p

/--
Constructive Step-C statement from the family-level counting core.
-/
lemma ac0_statement_from_pipeline_partial_constructive
    (p : GapPartialMCSPParams) : AC0StatementPartial_constructive p := by
  intro solver
  exact LB_Formulas_core_partial_constructive (solver := solver)

/-- Closed-world constructive Step-C statement from the core contradiction. -/
lemma ac0_statement_from_pipeline_partial_closed
    (p : GapPartialMCSPParams) : AC0StatementPartial_closed p := by
  intro solver
  exact LB_Formulas_core_partial_closed (solver := solver)

/-- Provider-style closed Step-C statement from the core contradiction. -/
lemma ac0_statement_from_pipeline_partial_providerClosed
    (p : GapPartialMCSPParams) : AC0StatementPartial_providerClosed p := by
  intro solver hProv
  letI : StepCClosureDataPartialProvider solver := hProv
  exact LB_Formulas_core_partial_closed_of_provider (solver := solver)

/-- Final internalized closed Step-C statement (no extra hypotheses). -/
lemma ac0_statement_from_pipeline_partial_internalized
    (p : GapPartialMCSPParams) : AC0StatementPartial_semantic p := by
  intro solver _easy
  exact LB_Formulas_core_partial_closed_internalized (solver := solver)

/--
Provider-style closed Step-C statement from semantic-to-syntactic lift data.
-/
lemma ac0_statement_from_pipeline_partial_providerClosed_of_syntacticLift
    (p : GapPartialMCSPParams)
    (liftData : StepCSyntacticLiftDataPartial p) :
    AC0StatementPartial_providerClosed p := by
  intro solver _hProv
  exact LB_Formulas_core_partial_closed_of_syntacticLift_provider
    (solver := solver) (liftData := liftData)

/--
Constructive provider-closed Step-C statement from the core contradiction.

This is the strongest currently fully constructive closed statement in-repo:
it has no external witness hypotheses and no legacy all-functions bridge.
-/
lemma ac0_statement_from_pipeline_partial_constructive_providerClosed
    (p : GapPartialMCSPParams) : AC0StatementPartial_constructive_providerClosed p := by
  intro solver
  exact LB_Formulas_core_partial_constructive_closed_of_provider (solver := solver)

/-- Fully closed semantic Step-C statement from the core contradiction. -/
lemma ac0_statement_from_pipeline_partial_fully_closed
    (p : GapPartialMCSPParams) : AC0StatementPartial_fully_closed p := by
  intro closure solver
  exact LB_Formulas_core_partial_fully_closed
    (closure := closure)
    (solver := solver)

/--
Existential fully closed Step-C statement from an explicit closure package.
-/
lemma ac0_statement_exists_false_from_pipeline_partial_fully_closed
    (p : GapPartialMCSPParams)
    (closure : StepCClosureDataPartial p) :
    ¬ ∃ _solver : SmallAC0Solver_Partial p, True := by
  exact LB_Formulas_core_partial_fully_closed_noExists (closure := closure)

/--
Fully closed semantic Step-C contradiction from semantic-to-syntactic lift
data.
-/
lemma ac0_statement_from_pipeline_partial_fully_closed_of_syntacticLift
    (p : GapPartialMCSPParams)
    (liftData : StepCSyntacticLiftDataPartial p) :
    ∀ _solver : SmallAC0Solver_Partial p, False := by
  intro s
  exact LB_Formulas_core_partial_fully_closed_of_syntacticLift
    (solver := s) (liftData := liftData)

/--
Existential fully closed Step-C statement from semantic-to-syntactic lift
data.
-/
lemma ac0_statement_exists_false_from_pipeline_partial_fully_closed_of_syntacticLift
    (p : GapPartialMCSPParams)
    (liftData : StepCSyntacticLiftDataPartial p) :
    ¬ ∃ _solver : SmallAC0Solver_Partial p, True := by
  exact LB_Formulas_core_partial_fully_closed_noExists_of_syntacticLift
    (liftData := liftData)

/--
Pipeline-level equivalence between pointwise and existential fully-closed
semantic Step-C statements.
-/
lemma ac0_statement_fully_closed_iff_noExists
    (p : GapPartialMCSPParams) :
    AC0StatementPartial_fully_closed p
      ↔ (∀ _closure : StepCClosureDataPartial p,
            ¬ ∃ _solver : SmallAC0Solver_Partial p, True) := by
  constructor
  · intro h closure
    exact (noSmallAC0Solver_partial_closed_iff_noExists closure).1 (h closure)
  · intro h closure
    exact (noSmallAC0Solver_partial_closed_iff_noExists closure).2 (h closure)

/-- Closed-world constructive Step-C implies package-based constructive Step-C. -/
lemma ac0_statement_constructive_of_closed
    (p : GapPartialMCSPParams)
    (_hClosed : AC0StatementPartial_closed p) :
    AC0StatementPartial_constructive p := by
  intro solver
  -- The closed route is stronger, but to keep this implication definitional and
  -- non-axiomatic we reuse the already-internal core contradiction on
  -- constructive packages.
  exact LB_Formulas_core_partial_constructive (solver := solver)

/--
Bounded semantic AC0 statement from the family-level counting core.
-/
lemma ac0_bounded_statement_from_pipeline_partial_semantic
    (p : GapPartialMCSPParams) (ε : Rat) :
    AC0BoundedStatementPartial_semantic p ε := by
  intro solver _hBound easy
  exact ac0_statement_from_pipeline_partial_semantic p solver easy

/-- Bounded constructive Step-C statement from the core contradiction. -/
lemma ac0_bounded_statement_from_pipeline_partial_constructive
    (p : GapPartialMCSPParams) (ε : Rat) :
    AC0BoundedStatementPartial_constructive p ε := by
  intro solver _hBound
  exact ac0_statement_from_pipeline_partial_constructive p solver

/--
Any constructive bounded Step-C statement implies the semantic bounded one
by packaging `(solver, easyData)` into `ConstructiveSmallAC0Solver_Partial`.
-/
lemma ac0_bounded_statement_semantic_of_constructive
    (p : GapPartialMCSPParams) (ε : Rat)
    (hC : AC0BoundedStatementPartial_constructive p ε) :
    AC0BoundedStatementPartial_semantic p ε := by
  intro solver hBound easy
  exact hC
    ({ toSmallAC0Solver_Partial :=
      { params := solver.params
        sem := solver.sem
        witness := solver.witness
        correct := solver.correct
        circuit := solver.circuit
        decide_eq := solver.decide_eq
        easyData := easy } } : ConstructiveSmallAC0Solver_Partial p)
    hBound

/--
Semantic formula-track hypothesis produced directly from the pipeline core.
-/
lemma formula_hypothesis_from_pipeline_partial_semantic
    (p : GapPartialMCSPParams) (δ : Rat) (hδ : (0 : Rat) < δ) :
    FormulaLowerBoundHypothesisPartial_semantic p δ := by
  refine ⟨hδ, ?_⟩
  exact ac0_bounded_statement_semantic_of_constructive
    (p := p) (ε := δ)
    (hC := ac0_bounded_statement_from_pipeline_partial_constructive p δ)

/--
Semantic formula-track hypothesis obtained via the constructive Step-C API.
-/
lemma formula_hypothesis_from_pipeline_partial_constructive
    (p : GapPartialMCSPParams) (δ : Rat) (hδ : (0 : Rat) < δ) :
    FormulaLowerBoundHypothesisPartial_semantic p δ := by
  refine ⟨hδ, ?_⟩
  exact ac0_bounded_statement_semantic_of_constructive
    (p := p) (ε := δ)
    (hC := ac0_bounded_statement_from_pipeline_partial_constructive p δ)

/--
Bounded semantic statement from direct syntactic easy-family hypotheses.
-/
lemma ac0_bounded_statement_from_syntacticEasy_partial
    (p : GapPartialMCSPParams) (ε : Rat)
    (hEasy : ∀ solver : SmallAC0Solver_Partial p,
      ThirdPartyFacts.AC0FamilyWitnessProp solver.params.ac0
        (AC0EasyFamily solver.params.ac0))
    (hComp : AC0CompressionHypothesis p) :
    AC0BoundedStatementPartial_semantic p ε := by
  intro solver _hBound _easy
  exact LB_Formulas_core_partial_of_syntacticEasy
    (solver := solver) (hEasy solver) hComp

/--
Semantic formula lower-bound hypothesis from direct syntactic easy-family
hypotheses.
-/
lemma formula_hypothesis_from_syntacticEasy_partial
    (p : GapPartialMCSPParams) (δ : Rat) (hδ : (0 : Rat) < δ)
    (hEasy : ∀ solver : SmallAC0Solver_Partial p,
      ThirdPartyFacts.AC0FamilyWitnessProp solver.params.ac0
        (AC0EasyFamily solver.params.ac0))
    (hComp : AC0CompressionHypothesis p) :
    FormulaLowerBoundHypothesisPartial_semantic p δ := by
  refine ⟨hδ, ?_⟩
  intro solver hBound _easy
  exact LB_Formulas_core_partial_of_syntacticEasy
    (solver := solver) (hEasy solver) hComp

end Magnification
end Pnp3
