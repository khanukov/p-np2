import Magnification.Facts_Magnification
import LowerBounds.LB_Formulas_Core
import LowerBounds.LB_LocalCircuits
import Models.Model_GapMCSP
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
  (h : GeneralLowerBoundHypothesis p ε statement) :
  NP_not_subset_Ppoly :=
by
  classical
  exact OPS_trigger_general (p := p) (ε := ε) (statement := statement) h

/--
  Шаг D.1: лемма `bridge_from_LB_Formulas` принимает положительное значение `δ`
  и мгновенно применяет OPS-триггер.  Нулевая часть (`∀ solver, False`) уже
  обеспечена теоремой `LB_Formulas_core` из шага C.
-/
theorem bridge_from_LB_Formulas
  {p : GapMCSPParams} {δ : Rat} (hδ : (0 : Rat) < δ) :
  NP_not_subset_Ppoly := by
  classical
  refine OPS_trigger_formulas (p := p) (δ := δ) ?hyp
  exact
    And.intro hδ
      (fun solver => (LB_Formulas_core (p := p) solver).elim)

/--
  Шаг D.1 (локальная версия): при `κ > 0` барьер локальности JACM’22
  срабатывает на тех же гипотезах, что и лемма `LB_LocalCircuits_core`.
-/
theorem bridge_from_LB_Local
  {p : GapMCSPParams} {κ : Nat} (hκ : 0 < κ) :
  NP_not_subset_Ppoly := by
  classical
  refine Locality_trigger (p := p) (κ := κ) ?hyp
  exact
    And.intro hκ
      (fun solver => (LB_LocalCircuits_core (p := p) solver).elim)

/--
  Шаг D.2: комбинация предыдущего шага с классическим включением `P ⊆ P/poly`
  немедленно даёт `P ≠ NP`.
-/
theorem P_ne_NP_from_formulas_bridge
  {p : GapMCSPParams} {δ : Rat} (hδ : (0 : Rat) < δ) :
  P_ne_NP := by
  have hNP : NP_not_subset_Ppoly := bridge_from_LB_Formulas (p := p) (δ := δ) hδ
  exact P_ne_NP_of_nonuniform_separation hNP P_subset_Ppoly_proof

/--
  Та же логика для локальных схем: барьер локальности плюс включение `P ⊆ P/poly`
  приводят к отличию `P` от `NP`.
-/
theorem P_ne_NP_from_local_bridge
  {p : GapMCSPParams} {κ : Nat} (hκ : 0 < κ) :
  P_ne_NP := by
  have hNP : NP_not_subset_Ppoly := bridge_from_LB_Local (p := p) (κ := κ) hκ
  exact P_ne_NP_of_nonuniform_separation hNP P_subset_Ppoly_proof

/--
  Общая версия: при любой гипотезе вида `GeneralLowerBoundHypothesis`
  разделение `P ≠ NP` следует немедленно.
-/
theorem P_ne_NP_from_general_bridge
  {p : GapMCSPParams} {ε : Rat} {statement : Prop}
  (h : GeneralLowerBoundHypothesis p ε statement) :
  P_ne_NP :=
by
  have hNP : NP_not_subset_Ppoly :=
    bridge_from_general_statement (p := p) (ε := ε) (statement := statement) h
  exact P_ne_NP_of_nonuniform_separation hNP P_subset_Ppoly_proof

end Magnification
end Pnp3
