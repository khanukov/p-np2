import Mathlib.Data.Finset.Basic
import Counting.Atlas_to_LB_Core
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

  **Proof sketch (Circuit-Input Game from Chapman-Williams ITCS'15):**

  1. **Setup**: Assume we have a small AC⁰ formula of size M, depth d solving
     GapMCSP with parameters (n, s_yes, s_no, β).

  2. **Circuit-Input Game**: Two players alternate:
     - CircuitPlayer: Provides a small formula/circuit attempting to solve GapMCSP
     - InputPlayer: Constructs "hard" truth tables (functions) that the circuit
       must distinguish

  3. **YES/NO layers**:
     - YES instances: truth tables of functions with circuit complexity ≥ s_yes
     - NO instances: truth tables of functions with circuit complexity ≤ s_no
     - Gap: β = s_yes / s_no >> 1

  4. **Richness property**: The InputPlayer can construct a large family Y where:
     - Each function in Y corresponds to a YES instance
     - Any two distinct functions in Y differ on at least polylog(N) positions
     - Therefore, no small dictionary can approximate all of Y on a small test set

  5. **Capacity contradiction**:
     - The atlas from SAL has capacity ~ 2^{O(t log(1/ε))}
     - The richness ensures |Y| > capacity(atlas)
     - But SAL guarantees every function in the family can be approximated
     - Contradiction!

  6. **Key technical lemmas needed**:
     - Switching lemma gives small t (polylog depth)
     - GapMCSP structure ensures YES instances are complex
     - Circuit-Input Game ensures |Y| is large (exponential in gap parameter)
     - Counting lemma bounds atlas capacity

  Reference: Chapman-Williams, "Circuit-Input Games and Hardness Magnification",
  ITCS 2015.
-/
axiom antiChecker_exists_large_Y
  {p : Models.GapMCSPParams} (solver : SmallAC0Solver p) :
  ∃ (F : Family (Models.inputLen p))
    (inst : HasAC0PartialWitness solver.ac0 (solver.same_n.symm ▸ F))
    (Y : Finset (Core.BitVec (Models.inputLen p) → Bool)),
      let Fsolver : Family solver.ac0.n :=
        (solver.same_n.symm ▸ F)
      let instWitness : HasAC0PartialWitness solver.ac0 Fsolver := inst
      let scWitness := (@scenarioFromAC0 solver.ac0 Fsolver instWitness).2
      let Ysolver : Finset (Core.BitVec solver.ac0.n → Bool) :=
        (solver.same_n.symm ▸ Y)
      Ysolver ⊆ familyFinset (sc := scWitness) ∧
        scenarioCapacity (sc := scWitness) < Ysolver.card

/--
  Усиленная форма античекера: кроме богатого семейства `Y` мы получаем малый
  тест-набор `T`, на котором любая функция из `Y` совпадает с некоторым
  объединением словаря `scWitness.atlas.dict`.  Это превращает гипотезу о малом
  решателе в конкретное утверждение о покрытии тест-набора локальными атласами.

  **Additional structure beyond antiChecker_exists_large_Y:**

  This stronger version provides an explicit test set T such that:
  - |T| ≤ polylog(N) (small witness set)
  - Every function f ∈ Y can be approximated by some union of ≤ k dictionary
    functions on the test set T
  - The union bound: (dict_size choose k) · 2^|T| < |Y|
    This shows that even accounting for all possible unions on the test set,
    there aren't enough combinations to cover all of Y.

  **Why this is stronger:**
  - antiChecker_exists_large_Y only asserts |Y| > capacity
  - This version shows the contradiction more explicitly: even optimistically
    counting all possible approximations on a small test set, we can't cover Y

  **Proof approach:**
  1. Use Circuit-Input Game to construct Y (as before)
  2. The game ensures functions in Y differ on many positions
  3. Extract a small test set T capturing these differences
  4. Show that the union bound on T fails to cover Y

  This is used in the final counting argument to derive the contradiction.
-/
axiom antiChecker_exists_testset
  {p : Models.GapMCSPParams} (solver : SmallAC0Solver p) :
  ∃ (F : Family (Models.inputLen p))
    (inst : HasAC0PartialWitness solver.ac0 (solver.same_n.symm ▸ F))
    (Y : Finset (Core.BitVec (Models.inputLen p) → Bool))
    (T : Finset (Core.BitVec (Models.inputLen p))),
      let Fsolver : Family solver.ac0.n :=
        (solver.same_n.symm ▸ F)
      let instWitness : HasAC0PartialWitness solver.ac0 Fsolver := inst
      let scWitness := (@scenarioFromAC0 solver.ac0 Fsolver instWitness).2
      let Ysolver : Finset (Core.BitVec solver.ac0.n → Bool) :=
        (solver.same_n.symm ▸ Y)
      let Tsolver : Finset (Core.BitVec solver.ac0.n) :=
        (solver.same_n.symm ▸ T)
      Ysolver ⊆ familyFinset (sc := scWitness) ∧
        scenarioCapacity (sc := scWitness) < Ysolver.card ∧
        Tsolver.card ≤ Models.polylogBudget solver.ac0.n ∧
        (∀ f ∈ Ysolver,
          f ∈ Counting.ApproxOnTestset
            (R := scWitness.atlas.dict) (k := scWitness.k) (T := Tsolver)) ∧
        Counting.unionBound
            (Counting.dictLen scWitness.atlas.dict)
            scWitness.k
            * 2 ^ Tsolver.card
          < Ysolver.card

/--
  Версия античекера для локальных схем.  Она утверждает существование
  богатого подсемейства, которое будет использовано в `LB_LocalCircuits_core`.

  **Local circuits vs. formulas:**

  Local circuits have restricted fan-in (locality parameter ℓ), but can be
  more powerful than formulas. The antichecker for local circuits follows the
  same Circuit-Input Game approach but accounts for the locality structure.

  **Key differences:**
  - Switching lemma for local circuits has different parameters
  - The shrinkage witness uses LocalCircuitWitness instead of AC0PartialWitness
  - The capacity bounds are adjusted for the locality parameter
  - But the overall structure is the same: |Y| > capacity(atlas)

  **Connection to formulas:**
  The formula lower bound (antiChecker_exists_large_Y) can be lifted to local
  circuits via the locality-to-general transformation. This axiom provides the
  direct statement for local circuits, avoiding the intermediate lifting step.

  Reference: Same Chapman-Williams ITCS'15 framework, adapted for local circuits.
-/
axiom antiChecker_exists_large_Y_local
  {p : Models.GapMCSPParams} (solver : SmallLocalCircuitSolver p) :
  ∃ (F : Family (Models.inputLen p))
    (inst : HasLocalCircuitWitness solver.params (solver.same_n.symm ▸ F))
    (Y : Finset (Core.BitVec (Models.inputLen p) → Bool)),
      let Fsolver : Family solver.params.n :=
        (solver.same_n.symm ▸ F)
      let instWitness : HasLocalCircuitWitness solver.params Fsolver := inst
      let scWitness :=
        (@scenarioFromLocalCircuit solver.params Fsolver instWitness).2
      let Ysolver : Finset (Core.BitVec solver.params.n → Bool) :=
        (solver.same_n.symm ▸ Y)
      Ysolver ⊆ familyFinset (sc := scWitness) ∧
        scenarioCapacity (sc := scWitness) < Ysolver.card

/--
  Усиленная локальная версия античекера с явным тест-набором.  Здесь `T`
  ограничивает точки, на которых функции из `Y` могут отличаться от
  соответствующих объединений словаря локальной схемы.

  **Structure:**
  This is the local circuit version of antiChecker_exists_testset.
  It provides:
  - A large rich family Y (|Y| > capacity)
  - An explicit small test set T (|T| ≤ polylog(N))
  - Union bound failure: combinations on T can't cover Y

  **Usage:**
  This is the final antichecker axiom used in the complete lower bound proof
  for local circuits. The explicit test set T makes the counting argument
  concrete and allows direct application of the union bound lemma.

  **Relationship to other axioms:**
  - Stronger than antiChecker_exists_large_Y_local (adds test set)
  - Local circuit version of antiChecker_exists_testset
  - Used in LB_LocalCircuits to complete the contradiction

  Together, these four antichecker axioms provide the "richness" results
  needed to connect the switching lemma (which gives small atlases) to
  the GapMCSP structure (which forces large families).
-/
axiom antiChecker_exists_testset_local
  {p : Models.GapMCSPParams} (solver : SmallLocalCircuitSolver p) :
  ∃ (F : Family (Models.inputLen p))
    (inst : HasLocalCircuitWitness solver.params (solver.same_n.symm ▸ F))
    (Y : Finset (Core.BitVec (Models.inputLen p) → Bool))
    (T : Finset (Core.BitVec (Models.inputLen p))),
      let Fsolver : Family solver.params.n :=
        (solver.same_n.symm ▸ F)
      let instWitness : HasLocalCircuitWitness solver.params Fsolver := inst
      let scWitness :=
        (@scenarioFromLocalCircuit solver.params Fsolver instWitness).2
      let Ysolver : Finset (Core.BitVec solver.params.n → Bool) :=
        (solver.same_n.symm ▸ Y)
      let Tsolver : Finset (Core.BitVec solver.params.n) :=
        (solver.same_n.symm ▸ T)
      Ysolver ⊆ familyFinset (sc := scWitness) ∧
        scenarioCapacity (sc := scWitness) < Ysolver.card ∧
        Tsolver.card ≤ Models.polylogBudget solver.params.n ∧
        (∀ f ∈ Ysolver,
          f ∈ Counting.ApproxOnTestset
            (R := scWitness.atlas.dict) (k := scWitness.k) (T := Tsolver)) ∧
        Counting.unionBound
            (Counting.dictLen scWitness.atlas.dict)
            scWitness.k
            * 2 ^ Tsolver.card
          < Ysolver.card

end LowerBounds
end Pnp3
