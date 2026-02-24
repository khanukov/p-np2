import LowerBounds.LB_Formulas_Core_Partial
import Models.Model_PartialMCSP
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
  pnp3/Magnification/PipelineStatements_Partial.lean

  Partial‑версия формулировок шага C для дальнейшей магнификации.

  Мы переносим те же структуры, что и в `PipelineStatements.lean`,
  но теперь параметры и решатели относятся к Partial MCSP.
  На этом этапе фиксируем только формульный (AC⁰) трек:

  * `AC0StatementPartial` — отсутствие малых AC⁰‑решателей Partial MCSP;
  * `AC0BoundedStatementPartial` — тот же запрет с явным bound `M ≤ N^{1+ε}`;
  * `FormulaLowerBoundHypothesisPartial` — упаковка гипотезы для OPS.

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

  These predicates are the recommended interface for future migration:
  they quantify over concrete solvers and require solver-local AC0 witnesses.
  Legacy `allFunctionsFamily` predicates are kept below for compatibility.
-/

/-- Semantic (family-level counting) Step-C statement. -/
def AC0StatementPartial_semantic (p : GapPartialMCSPParams) : Prop :=
  ∀ solver : SmallAC0Solver_Partial p,
    AC0EasyFamilyDataPartial solver.params.ac0 → False

/--
Constructive (non-vacuous) Step-C statement:
quantifies over solver packages that carry easy-family data internally.
-/
def AC0StatementPartial_constructive (p : GapPartialMCSPParams) : Prop :=
  ∀ _solver : ConstructiveSmallAC0Solver_Partial p, False

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
  Утверждение «не существует малого AC⁰‑решателя» для Partial MCSP.
  Содержательно это то же, что `AC0Statement`, но для `GapPartialMCSPParams`.
-/
def AC0StatementPartial (p : GapPartialMCSPParams) : Prop :=
  ∀ _solver : SmallAC0Solver_Partial p,
    ThirdPartyFacts.AC0FamilyWitnessProp _solver.params.ac0
      (Counting.allFunctionsFamily _solver.params.ac0.n) → False

/--
  Явный «рукопожатный» bound: `M ≤ N^{1+ε}` с `N = partialInputLen p`.
  Это напрямую совпадает с формой, ожидаемой в OPS‑триггерах.
-/
def ac0SizeBoundPartial (p : GapPartialMCSPParams) (ε : Rat)
    (solver : SmallAC0Solver_Partial p) : Prop :=
  let N : Real := Models.partialInputLen p
  (solver.params.ac0.M : Real) ≤ Real.rpow N (1 + (ε : Real))

/--
  Утверждение «нет малых AC⁰‑решателей с явным bound `M ≤ N^{1+ε}`»
  для Partial MCSP.
-/
def AC0BoundedStatementPartial (p : GapPartialMCSPParams) (ε : Rat) : Prop :=
  ∀ solver : SmallAC0Solver_Partial p,
    ac0SizeBoundPartial p ε solver →
    ThirdPartyFacts.AC0FamilyWitnessProp solver.params.ac0
      (Counting.allFunctionsFamily solver.params.ac0.n) → False

/--
Constructive AC0 statement: for each solver, an explicit multi-switching
witness for the all-functions family yields contradiction.
-/
def AC0StatementPartial_of_multiSwitching (p : GapPartialMCSPParams) : Prop :=
  ∀ solver : SmallAC0Solver_Partial p,
    ThirdPartyFacts.AC0MultiSwitchingWitness solver.params.ac0
      (Counting.allFunctionsFamily solver.params.ac0.n) → False

/--
Bounded constructive AC0 statement (same as above with explicit size bound).
-/
def AC0BoundedStatementPartial_of_multiSwitching
    (p : GapPartialMCSPParams) (ε : Rat) : Prop :=
  ∀ solver : SmallAC0Solver_Partial p,
    ac0SizeBoundPartial p ε solver →
    ThirdPartyFacts.AC0MultiSwitchingWitness solver.params.ac0
      (Counting.allFunctionsFamily solver.params.ac0.n) → False

/--
Constructive AC0 statement with witness obtained from typeclass provider.
-/
def AC0StatementPartial_of_multiSwitching_provider
    (p : GapPartialMCSPParams) : Prop :=
  ∀ solver : SmallAC0Solver_Partial p,
    ThirdPartyFacts.AC0MultiSwitchingWitnessProvider
      solver.params.ac0
      (Counting.allFunctionsFamily solver.params.ac0.n) → False

/--
Constructive AC0 statement with default all-functions multi-switching packages.
-/
def AC0StatementPartial_of_default_multiSwitching
    (p : GapPartialMCSPParams) : Prop :=
  ∀ solver : SmallAC0Solver_Partial p,
    AllFunctionsAC0MultiSwitchingWitness solver.params.ac0 → False

/--
  Формульная гипотеза для OPS в partial‑треке.
-/
def FormulaLowerBoundHypothesisPartial
    (p : GapPartialMCSPParams) (δ : Rat) : Prop :=
  (0 : Rat) < δ ∧ AC0BoundedStatementPartial p δ

/-- Semantic counterpart of `FormulaLowerBoundHypothesisPartial`. -/
def FormulaLowerBoundHypothesisPartial_semantic
    (p : GapPartialMCSPParams) (δ : Rat) : Prop :=
  (0 : Rat) < δ ∧ AC0BoundedStatementPartial_semantic p δ

/-!
  ### Выводы шага C в partial‑треке
-/

/--
  Ключевой вывод шага C (Partial MCSP):
  если дан малый AC⁰‑решатель, получаем противоречие из anti‑checker.
-/
lemma ac0_statement_from_pipeline_partial
    (p : GapPartialMCSPParams) : AC0StatementPartial p := by
  intro solver hF
  exact LB_Formulas_core_partial (solver := solver) hF

/--
  Из `AC0StatementPartial` немедленно получаем `AC0BoundedStatementPartial`.
  Числовой bound здесь лишь усиливает гипотезу.
-/
lemma ac0_bounded_statement_from_pipeline_partial
    (p : GapPartialMCSPParams) (ε : Rat) : AC0BoundedStatementPartial p ε := by
  intro solver _hBound hF
  exact ac0_statement_from_pipeline_partial p solver hF

/--
Constructive AC0 statement from the pipeline core.
-/
lemma ac0_statement_from_pipeline_partial_of_multiSwitching
    (p : GapPartialMCSPParams) : AC0StatementPartial_of_multiSwitching p := by
  intro solver hMS
  exact LB_Formulas_core_partial_of_multiSwitching (solver := solver) hMS

/--
Bounded constructive AC0 statement from the pipeline core.
-/
lemma ac0_bounded_statement_from_pipeline_partial_of_multiSwitching
    (p : GapPartialMCSPParams) (ε : Rat) :
    AC0BoundedStatementPartial_of_multiSwitching p ε := by
  intro solver _hBound hMS
  exact ac0_statement_from_pipeline_partial_of_multiSwitching p solver hMS

/-- Constructive AC0 statement through the provider-style interface. -/
lemma ac0_statement_from_pipeline_partial_of_multiSwitching_provider
    (p : GapPartialMCSPParams) :
    AC0StatementPartial_of_multiSwitching_provider p := by
  intro solver hMS
  exact LB_Formulas_core_partial_of_multiSwitching_provider (solver := solver)

/-- Constructive AC0 statement from default all-functions packages. -/
lemma ac0_statement_from_pipeline_partial_of_default_multiSwitching
    (p : GapPartialMCSPParams) :
    AC0StatementPartial_of_default_multiSwitching p := by
  intro solver hMS
  exact LB_Formulas_core_partial_of_default_multiSwitching (solver := solver)

/--
Build the standard formula lower-bound hypothesis from a default
all-functions multi-switching package.
-/
lemma formula_hypothesis_from_pipeline_partial_of_default_multiSwitching
    (p : GapPartialMCSPParams) (δ : Rat) (hδ : (0 : Rat) < δ)
    (hMS : ∀ solver : SmallAC0Solver_Partial p,
      AllFunctionsAC0MultiSwitchingWitness solver.params.ac0) :
    FormulaLowerBoundHypothesisPartial p δ := by
  refine ⟨hδ, ?_⟩
  intro solver _hBound _hF
  exact ac0_statement_from_pipeline_partial_of_default_multiSwitching p solver (hMS solver)

namespace Compatibility

/--
Legacy helper: derives the formula hypothesis through the
`allFunctionsFamily` Step-C route.
-/
lemma formula_hypothesis_from_pipeline_partial_legacy
    (p : GapPartialMCSPParams) (δ : Rat) (hδ : (0 : Rat) < δ) :
    FormulaLowerBoundHypothesisPartial p δ := by
  refine ⟨hδ, ac0_bounded_statement_from_pipeline_partial p δ⟩

end Compatibility

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

/--
Constructive Step-C statement from the family-level counting core.
-/
lemma ac0_statement_from_pipeline_partial_constructive
    (p : GapPartialMCSPParams) : AC0StatementPartial_constructive p := by
  intro solver
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
    ({ toSmallAC0Solver_Partial := solver, easyData := easy } : ConstructiveSmallAC0Solver_Partial p)
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
