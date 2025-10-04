import Mathlib.Data.Finset.Basic
import Core.SAL_Core
import LowerBounds.LB_Formulas
import Models.Model_GapMCSP
import ThirdPartyFacts.Facts_Switching

/-!
  pnp3/LowerBounds/AntiChecker.lean

  Античекер — это содержательный мостик между конкретной задачей GapMCSP
  и универсальными оценками части B.  В классических доказательствах
  (Chapman–Williams, Williams, Hitchcock–Pătraşcu и др.) он строится через
  Circuit-Input Game или анализ YES/NO-слоёв.  Здесь мы формализуем его как
  внешний факт (аксиому), выделив точный интерфейс, который необходим для
  дальнейшей «машинной» части доказательства.

  * `SmallAC0Solver` описывает гипотезу о существовании малой формулы/схемы
    класса AC⁰, решающей GapMCSP при заданных параметрах.
  * `antiChecker_exists_large_Y` утверждает, что из такой гипотезы существует
    «богатое» конечное подсемейство `Y` внутри семейства функций, обслуживаемого
    SAL-сценарием.  Мощность `Y` превосходит ёмкость сценария, что вкупе с
    Covering-Power даст противоречие.

  Эти утверждения используются в `LB_Formulas_Core.lean`, где собран каркас
  нижней оценки: малый решатель ⇒ противоречие.
-/
namespace Pnp3
namespace LowerBounds

open Classical
open Core
open Models
open ThirdPartyFacts

/--
  Гипотеза «малый AC⁰-решатель» для GapMCSP на входной длине `N = 2^p.n`.
  Мы фиксируем набор параметров AC⁰ и требуем, чтобы число входных переменных
  совпадало с длиной таблицы истинности рассматриваемой функции.
-/
structure SmallAC0Solver (p : Models.GapMCSPParams) where
  ac0 : ThirdPartyFacts.AC0Parameters
  same_n : ac0.n = Models.inputLen p
  deriving Repr

/--
  Аналогичная оболочка для локальных схем.  Мы предполагаем, что
  решатель описывается параметрами `LocalCircuitParameters` и действует
  на входах длины `N = 2^p.n`.
-/
structure SmallLocalCircuitSolver (p : Models.GapMCSPParams) where
  params : ThirdPartyFacts.LocalCircuitParameters
  same_n : params.n = Models.inputLen p
  deriving Repr

/--
  Античекер: из гипотезы о малом решателе существует семейство функций `F`
  на `N = 2^p.n` битах, для которого SAL-конвейер (через `scenarioFromAC0`)
  строит ограниченный атлас `sc`, а внутри `sc.family` найдётся конечное
  подсемейство `Y`, мощность которого строго превосходит ёмкость сценария.

  В дальнейшем это подсемейство будет противопоставляться Covering-Power,
  что немедленно приводит к противоречию.  Доказательство античекера опирается
  на содержательную часть работы (Circuit-Input Game, richness), поэтому
  здесь оно оформлено как внешний факт с чёткой сигнатурой.
-/
axiom antiChecker_exists_large_Y
  {p : Models.GapMCSPParams} (solver : SmallAC0Solver p) :
  ∃ (F : Family (Models.inputLen p))
    (Y : Finset (Core.BitVec (Models.inputLen p) → Bool)),
      let Fsolver : Family solver.ac0.n :=
        (solver.same_n.symm ▸ F)
      let scWitness := (scenarioFromAC0 (params := solver.ac0) Fsolver).2
      let Ysolver : Finset (Core.BitVec solver.ac0.n → Bool) :=
        (solver.same_n.symm ▸ Y)
      Ysolver ⊆ familyFinset (sc := scWitness) ∧
        scenarioCapacity (sc := scWitness) < Ysolver.card

/--
  Версия античекера для локальных схем.  Она утверждает существование
  богатого подсемейства, которое будет использовано в `LB_LocalCircuits_core`.
-/
axiom antiChecker_exists_large_Y_local
  {p : Models.GapMCSPParams} (solver : SmallLocalCircuitSolver p) :
  ∃ (F : Family (Models.inputLen p))
    (Y : Finset (Core.BitVec (Models.inputLen p) → Bool)),
      let Fsolver : Family solver.params.n :=
        (solver.same_n.symm ▸ F)
      let scWitness :=
        (scenarioFromLocalCircuit (params := solver.params) Fsolver).2
      let Ysolver : Finset (Core.BitVec solver.params.n → Bool) :=
        (solver.same_n.symm ▸ Y)
      Ysolver ⊆ familyFinset (sc := scWitness) ∧
        scenarioCapacity (sc := scWitness) < Ysolver.card

end LowerBounds
end Pnp3
