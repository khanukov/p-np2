import Magnification.Facts_Magnification
import Magnification.PipelineStatements
import LowerBounds.LB_Formulas_Core
import LowerBounds.LB_LocalCircuits
import Models.Model_GapMCSP
import Models.Model_SparseNP
import Complexity.Interfaces

/-!
  pnp3/Magnification/Bridge_to_Magnification.lean

  Мост от нижних оценок (шаг C) к последствиям магнификации (шаг D).
  Сначала мы выводим `NP \nsubseteq P/poly`, а затем — `P ≠ NP`,
  комбинируя соответствующие триггеры OPS/JACM с доказанными ранее
  противоречиями `LB_Formulas_core` и `LB_LocalCircuits_core`.
-/

namespace Pnp3
namespace Magnification

open Classical
open Models
open LowerBounds
open Set
open ComplexityInterfaces

/--
  Общая форма моста: любое доказательство гипотезы
  `GeneralLowerBoundHypothesis` (шаги A–C) автоматически запускает
  магнификацию OPS и даёт разделение `NP \nsubseteq P/poly`.
-/
theorem bridge_from_general_statement
  {p : GapMCSPParams} {ε : Rat} {statement : Prop}
  (hF_all : ∀ loc : SmallLocalCircuitSolver p,
    ThirdPartyFacts.FamilyIsLocalCircuit loc.params.params
      (Counting.allFunctionsFamily loc.params.params.n))
  (h : GeneralLowerBoundHypothesis p ε statement) :
  NP_not_subset_Ppoly :=
by
  classical
  exact OPS_trigger_general (p := p) (ε := ε) (statement := statement) hF_all h

/--
  Мост для CJW-гипотезы: суперлинейная нижняя граница для разреженного
  NP-языка сразу запускает разделение `NP \nsubseteq P/poly`.
-/
theorem bridge_from_sparse_statement
  {p : Models.SparseLanguageParams} {ε : Rat}
  (h : SparseLowerBoundHypothesis p ε (∀ _solver : SmallSparseSolver p, False)) :
  NP_not_subset_Ppoly :=
by
  classical
  exact CJW_sparse_trigger (p := p) (ε := ε) h

/--
  Упаковка CJW-гипотезы для будущих модулей: структура хранит произвольное
  утверждение о разреженном NP-языке и обещание, что для любого положительного
  `ε` выполняется соответствующая гипотеза `SparseLowerBoundHypothesis`.
-/
structure SparseBridgeKit (p : Models.SparseLanguageParams) : Type where
  hypothesis :
    ∀ {ε : Rat}, (0 : Rat) < ε →
      SparseLowerBoundHypothesis p ε (∀ _solver : SmallSparseSolver p, False)

/-- Любой `SparseBridgeKit` немедленно даёт разделение `NP` и `P/poly`. -/
theorem bridge_from_sparse_kit
  {p : Models.SparseLanguageParams} (kit : SparseBridgeKit p)
  {ε : Rat} (hε : (0 : Rat) < ε) :
  NP_not_subset_Ppoly :=
by
  classical
  have hHyp : SparseLowerBoundHypothesis p ε (∀ _solver : SmallSparseSolver p, False) :=
    kit.hypothesis (ε := ε) hε
  exact bridge_from_sparse_statement (p := p) (ε := ε) hHyp

/-- `SparseBridgeKit` также приводит к разделению `P` и `NP`. -/
theorem P_ne_NP_from_sparse_kit
  {p : Models.SparseLanguageParams} (kit : SparseBridgeKit p)
  {ε : Rat} (hε : (0 : Rat) < ε) :
  P_ne_NP :=
by
  have hNP : NP_not_subset_Ppoly :=
    bridge_from_sparse_kit (p := p) (kit := kit) (ε := ε) hε
  exact P_ne_NP_of_nonuniform_separation hNP P_subset_Ppoly_proof

/--
  Мост, использующий готовую упаковку шага C: положительное `ε`
  и лемма `general_hypothesis_from_pipeline` мгновенно запускают
  OPS-триггер.
-/
theorem bridge_from_pipeline_general
  {p : GapMCSPParams} {ε : Rat} (hε : (0 : Rat) < ε)
  (hF_all : ∀ loc : SmallLocalCircuitSolver p,
    ThirdPartyFacts.FamilyIsLocalCircuit loc.params.params
      (Counting.allFunctionsFamily loc.params.params.n)) :
  NP_not_subset_Ppoly :=
by
  classical
  have hHyp : GeneralLowerBoundHypothesis p ε (AC0Statement p) :=
    general_hypothesis_from_pipeline (p := p) (ε := ε) hε
  -- Переписываем гипотезу в формульном виде: размерное условие уже более узкое.
  have hFormula : FormulaLowerBoundHypothesis p ε := by
    refine And.intro hHyp.1 ?_
    intro solver hBound hF_all
    exact hHyp.2 solver hF_all
  exact OPS_trigger_formulas (p := p) (δ := ε) hF_all hFormula

/--
  Мост, использующий Locality-Lift: положительное `ε` и запрет общих схем
  (через `general_hypothesis_from_locality`) дают разделение `NP` и `P/poly`.
-/
theorem bridge_from_general_circuits
  {p : GapMCSPParams} {ε : Rat} (hε : (0 : Rat) < ε)
  (hF_all : ∀ loc : SmallLocalCircuitSolver p,
    ThirdPartyFacts.FamilyIsLocalCircuit loc.params.params
      (Counting.allFunctionsFamily loc.params.params.n)) :
  NP_not_subset_Ppoly :=
by
  classical
  have hHyp : GeneralLowerBoundHypothesis p ε (GeneralCircuitStatement p) :=
    general_hypothesis_from_locality (p := p) (ε := ε) hε
  exact OPS_trigger_general_circuits (p := p) (ε := ε) hF_all hHyp

/--
  Удобная версия моста, использующая заранее собранный `PipelineBridgeKit`.
-/
theorem bridge_from_pipeline_kit_general
  {p : GapMCSPParams} (kit : PipelineBridgeKit p)
  {ε : Rat} (hε : (0 : Rat) < ε)
  (hF_all : ∀ loc : SmallLocalCircuitSolver p,
    ThirdPartyFacts.FamilyIsLocalCircuit loc.params.params
      (Counting.allFunctionsFamily loc.params.params.n)) :
  NP_not_subset_Ppoly :=
by
  classical
  have hHyp := kit.general_hypothesis (ε := ε) hε
  -- Сужаемся до формульной гипотезы и запускаем конструктивный триггер.
  have hFormula : FormulaLowerBoundHypothesis p ε := by
    refine And.intro hHyp.1 ?_
    intro solver hBound hF_all
    exact hHyp.2 solver hF_all
  exact OPS_trigger_formulas (p := p) (δ := ε) hF_all hFormula

/--
  Версия Locality-Lift для заранее собранного комплекта `PipelineBridgeKit`.
-/
theorem bridge_from_pipeline_kit_general_circuits
  {p : GapMCSPParams} (kit : PipelineBridgeKit p)
  {ε : Rat} (hε : (0 : Rat) < ε)
  (hF_all : ∀ loc : SmallLocalCircuitSolver p,
    ThirdPartyFacts.FamilyIsLocalCircuit loc.params.params
      (Counting.allFunctionsFamily loc.params.params.n)) :
  NP_not_subset_Ppoly :=
by
  classical
  have hHyp := kit.general_circuit_hypothesis (ε := ε) hε
  exact OPS_trigger_general_circuits (p := p) (ε := ε) hF_all hHyp

/--
  Шаг D.1: лемма `bridge_from_LB_Formulas` принимает положительное значение `δ`
  и мгновенно применяет OPS-триггер.  Нулевая часть (`∀ solver, False`) уже
  обеспечена теоремой `LB_Formulas_core` из шага C.
-/
theorem bridge_from_LB_Formulas
  {p : GapMCSPParams} {δ : Rat} (hδ : (0 : Rat) < δ)
  (hF_all : ∀ loc : SmallLocalCircuitSolver p,
    ThirdPartyFacts.FamilyIsLocalCircuit loc.params.params
      (Counting.allFunctionsFamily loc.params.params.n)) :
  NP_not_subset_Ppoly := by
  classical
  have hHyp : FormulaLowerBoundHypothesis p δ :=
    formula_hypothesis_from_pipeline (p := p) (δ := δ) hδ
  exact OPS_trigger_formulas (p := p) (δ := δ) hF_all hHyp

/--
  Мост, полагающийся на набор выводов `PipelineBridgeKit`.
-/
theorem bridge_from_pipeline_kit_formulas
  {p : GapMCSPParams} (kit : PipelineBridgeKit p)
  {δ : Rat} (hδ : (0 : Rat) < δ)
  (hF_all : ∀ loc : SmallLocalCircuitSolver p,
    ThirdPartyFacts.FamilyIsLocalCircuit loc.params.params
      (Counting.allFunctionsFamily loc.params.params.n)) :
  NP_not_subset_Ppoly :=
by
  classical
  have hHyp := kit.formula_hypothesis (δ := δ) hδ
  exact OPS_trigger_formulas (p := p) (δ := δ) hF_all hHyp

/--
  Шаг D.1 (локальная версия): при `κ > 0` барьер локальности JACM’22
  срабатывает на тех же гипотезах, что и лемма `LB_LocalCircuits_core`.
-/
theorem bridge_from_LB_Local
  {p : GapMCSPParams} {κ : Nat} (hκ : 0 < κ)
  (hF_all : ∀ loc : SmallLocalCircuitSolver p,
    ThirdPartyFacts.FamilyIsLocalCircuit loc.params.params
      (Counting.allFunctionsFamily loc.params.params.n)) :
  NP_not_subset_Ppoly := by
  classical
  have hHyp : LocalLowerBoundHypothesis p κ :=
    local_hypothesis_from_pipeline (p := p) (κ := κ) hκ
  exact Locality_trigger (p := p) (κ := κ) hF_all hHyp

/--
  Версия моста для `PipelineBridgeKit` и локальных схем.
-/
theorem bridge_from_pipeline_kit_local
  {p : GapMCSPParams} (kit : PipelineBridgeKit p)
  {κ : Nat} (hκ : 0 < κ)
  (hF_all : ∀ loc : SmallLocalCircuitSolver p,
    ThirdPartyFacts.FamilyIsLocalCircuit loc.params.params
      (Counting.allFunctionsFamily loc.params.params.n)) :
  NP_not_subset_Ppoly :=
by
  classical
  have hHyp := kit.local_hypothesis (κ := κ) hκ
  exact Locality_trigger (p := p) (κ := κ) hF_all hHyp

/--
  Шаг D.2: комбинация предыдущего шага с классическим включением `P ⊆ P/poly`
  немедленно даёт `P ≠ NP`.
-/
theorem P_ne_NP_from_formulas_bridge
  {p : GapMCSPParams} {δ : Rat} (hδ : (0 : Rat) < δ)
  (hF_all : ∀ loc : SmallLocalCircuitSolver p,
    ThirdPartyFacts.FamilyIsLocalCircuit loc.params.params
      (Counting.allFunctionsFamily loc.params.params.n)) :
  P_ne_NP := by
  have hNP : NP_not_subset_Ppoly :=
    bridge_from_LB_Formulas (p := p) (δ := δ) hδ hF_all
  exact P_ne_NP_of_nonuniform_separation hNP P_subset_Ppoly_proof

/--
  Финальное разделение `P` и `NP`, полученное из набора `PipelineBridgeKit`.
-/
theorem P_ne_NP_from_pipeline_kit_formulas
  {p : GapMCSPParams} (kit : PipelineBridgeKit p)
  {δ : Rat} (hδ : (0 : Rat) < δ)
  (hF_all : ∀ loc : SmallLocalCircuitSolver p,
    ThirdPartyFacts.FamilyIsLocalCircuit loc.params.params
      (Counting.allFunctionsFamily loc.params.params.n)) :
  P_ne_NP :=
by
  have hNP : NP_not_subset_Ppoly :=
    bridge_from_pipeline_kit_formulas (p := p) (kit := kit) (δ := δ) hδ hF_all
  exact P_ne_NP_of_nonuniform_separation hNP P_subset_Ppoly_proof

/--
  Общий вывод `P ≠ NP` из Locality-Lift.
-/
theorem P_ne_NP_from_general_circuits
  {p : GapMCSPParams} {ε : Rat} (hε : (0 : Rat) < ε)
  (hF_all : ∀ loc : SmallLocalCircuitSolver p,
    ThirdPartyFacts.FamilyIsLocalCircuit loc.params.params
      (Counting.allFunctionsFamily loc.params.params.n)) :
  P_ne_NP :=
by
  have hNP : NP_not_subset_Ppoly :=
    bridge_from_general_circuits (p := p) (ε := ε) hε hF_all
  exact P_ne_NP_of_nonuniform_separation hNP P_subset_Ppoly_proof

/--
  Финальный вывод `P ≠ NP` на основе комплекта `PipelineBridgeKit` и
  общих схем.
-/
theorem P_ne_NP_from_pipeline_kit_general_circuits
  {p : GapMCSPParams} (kit : PipelineBridgeKit p)
  {ε : Rat} (hε : (0 : Rat) < ε)
  (hF_all : ∀ loc : SmallLocalCircuitSolver p,
    ThirdPartyFacts.FamilyIsLocalCircuit loc.params.params
      (Counting.allFunctionsFamily loc.params.params.n)) :
  P_ne_NP :=
by
  have hNP : NP_not_subset_Ppoly :=
    bridge_from_pipeline_kit_general_circuits (p := p) (kit := kit) (ε := ε) hε hF_all
  exact P_ne_NP_of_nonuniform_separation hNP P_subset_Ppoly_proof

/--
  Та же логика для локальных схем: барьер локальности плюс включение `P ⊆ P/poly`
  приводят к отличию `P` от `NP`.
-/
theorem P_ne_NP_from_local_bridge
  {p : GapMCSPParams} {κ : Nat} (hκ : 0 < κ)
  (hF_all : ∀ loc : SmallLocalCircuitSolver p,
    ThirdPartyFacts.FamilyIsLocalCircuit loc.params.params
      (Counting.allFunctionsFamily loc.params.params.n)) :
  P_ne_NP := by
  have hNP : NP_not_subset_Ppoly := bridge_from_LB_Local (p := p) (κ := κ) hκ hF_all
  exact P_ne_NP_of_nonuniform_separation hNP P_subset_Ppoly_proof

/--
  Разделение `P` и `NP` на основе локальной части комплекта `PipelineBridgeKit`.
-/
theorem P_ne_NP_from_pipeline_kit_local
  {p : GapMCSPParams} (kit : PipelineBridgeKit p)
  {κ : Nat} (hκ : 0 < κ)
  (hF_all : ∀ loc : SmallLocalCircuitSolver p,
    ThirdPartyFacts.FamilyIsLocalCircuit loc.params.params
      (Counting.allFunctionsFamily loc.params.params.n)) :
  P_ne_NP :=
by
  have hNP : NP_not_subset_Ppoly :=
    bridge_from_pipeline_kit_local (p := p) (kit := kit) (κ := κ) hκ hF_all
  exact P_ne_NP_of_nonuniform_separation hNP P_subset_Ppoly_proof

/--
  Общая версия: при любой гипотезе вида `GeneralLowerBoundHypothesis`
  разделение `P ≠ NP` следует немедленно.
-/
theorem P_ne_NP_from_general_bridge
  {p : GapMCSPParams} {ε : Rat} {statement : Prop}
  (hF_all : ∀ loc : SmallLocalCircuitSolver p,
    ThirdPartyFacts.FamilyIsLocalCircuit loc.params.params
      (Counting.allFunctionsFamily loc.params.params.n))
  (h : GeneralLowerBoundHypothesis p ε statement) :
  P_ne_NP :=
by
  have hNP : NP_not_subset_Ppoly :=
    bridge_from_general_statement (p := p) (ε := ε) (statement := statement) hF_all h
  exact P_ne_NP_of_nonuniform_separation hNP P_subset_Ppoly_proof

/--
  Версия CJW: суперлинейная нижняя граница для разреженного NP-языка
  также приводит к разделению `P` и `NP`.
-/
theorem P_ne_NP_from_sparse_statement
  {p : Models.SparseLanguageParams} {ε : Rat}
  (h : SparseLowerBoundHypothesis p ε (∀ _solver : SmallSparseSolver p, False)) :
  P_ne_NP :=
by
  have hNP : NP_not_subset_Ppoly :=
    bridge_from_sparse_statement (p := p) (ε := ε) h
  exact P_ne_NP_of_nonuniform_separation hNP P_subset_Ppoly_proof

/--
  Комбинация общей версии с упаковкой шага C: достаточно зафиксировать
  положительное `ε`.
-/
theorem P_ne_NP_from_pipeline_general
  {p : GapMCSPParams} {ε : Rat} (hε : (0 : Rat) < ε)
  (hF_all : ∀ loc : SmallLocalCircuitSolver p,
    ThirdPartyFacts.FamilyIsLocalCircuit loc.params.params
      (Counting.allFunctionsFamily loc.params.params.n)) :
  P_ne_NP :=
by
  have hNP : NP_not_subset_Ppoly :=
    bridge_from_pipeline_general (p := p) (ε := ε) hε
      (hF_all := hF_all)
  exact P_ne_NP_of_nonuniform_separation hNP P_subset_Ppoly_proof

/--
  Комбинация универсальной версии моста с комплектом `PipelineBridgeKit`.
-/
theorem P_ne_NP_from_pipeline_kit_general
  {p : GapMCSPParams} (kit : PipelineBridgeKit p)
  {ε : Rat} (hε : (0 : Rat) < ε)
  (hF_all : ∀ loc : SmallLocalCircuitSolver p,
    ThirdPartyFacts.FamilyIsLocalCircuit loc.params.params
      (Counting.allFunctionsFamily loc.params.params.n)) :
  P_ne_NP :=
by
  have hNP : NP_not_subset_Ppoly :=
    bridge_from_pipeline_kit_general (p := p) (kit := kit) (ε := ε) hε hF_all
  exact P_ne_NP_of_nonuniform_separation hNP P_subset_Ppoly_proof

end Magnification
end Pnp3
