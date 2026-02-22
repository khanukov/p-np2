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

/--
  Формульная гипотеза OPS в partial‑треке (готова к использованию в bridge).
-/
lemma formula_hypothesis_from_pipeline_partial
    (p : GapPartialMCSPParams) (δ : Rat) (hδ : (0 : Rat) < δ) :
    FormulaLowerBoundHypothesisPartial p δ := by
  refine ⟨hδ, ac0_bounded_statement_from_pipeline_partial p δ⟩

end Magnification
end Pnp3
