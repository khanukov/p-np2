import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Complexity.Promise
import Complexity.Interfaces
import Counting.Atlas_to_LB_Core
import Counting.CapacityGap
import Counting.Count_EasyFuncs
import Core.BooleanBasics
import Core.SAL_Core
import LowerBounds.LB_Formulas
import LowerBounds.MCSPGapLocality
import Models.Model_PartialMCSP
import ThirdPartyFacts.Facts_Switching

/-!
  pnp3/LowerBounds/AntiChecker_Partial.lean

  Частичный трек anti-checker для Partial MCSP.

  Этот файл **пока** фиксирует ключевые структуры и интерфейсы, чтобы
  дальнейшие доказательства можно было переносить по шагам, не ломая
  legacy-версию в `AntiChecker.lean`.

  Основные цели:
  * выделить корректного решателя `SmallAC0Solver_Partial`;
  * подготовить место для комбинаторных лемм (подсчёт согласованных таблиц);
  * использовать `Models.GapPartialMCSPPromise` как canonical promise-задачу.
-/

namespace Pnp3
namespace LowerBounds

open Core
open Complexity
open ComplexityInterfaces
open Models
open ThirdPartyFacts

/--
  Параметры «малого» AC⁰-решателя для Partial MCSP.

  В первой итерации мы копируем структуру `SmallAC0Params`, но под `GapPartialMCSPParams`.
  Это даёт чёткую точку расширения для переноса anti-checker-а.
  Явную гипотезу `AC0SmallEnough` убираем: в partial‑треке она заменяется
  на будущий strong‑witness из multi‑switching.
-/
structure SmallAC0ParamsPartial (p : GapPartialMCSPParams) where
  ac0 : ThirdPartyFacts.AC0Parameters
  same_n : ac0.n = partialInputLen p
  union_small :
    let bound := Nat.pow 2 (ThirdPartyFacts.ac0DepthBound_strong ac0)
    Counting.unionBound bound bound ≤
      Nat.pow 2 (Nat.pow 2 ac0.n / (ac0.n + 2))
  deriving Repr

/--
Default constructive package for the AC0 all-functions family:
provides a concrete multi-switching witness.
-/
class AllFunctionsAC0MultiSwitchingWitness
    (params : ThirdPartyFacts.AC0Parameters) : Type where
  witness :
    ThirdPartyFacts.AC0MultiSwitchingWitness params
      (Counting.allFunctionsFamily params.n)

/-- Bridge: default all-functions package provides the generic provider class. -/
instance allFunctions_multiSwitchingProvider
    (params : ThirdPartyFacts.AC0Parameters)
    [h : AllFunctionsAC0MultiSwitchingWitness params] :
    ThirdPartyFacts.AC0MultiSwitchingWitnessProvider
      params
      (Counting.allFunctionsFamily params.n) where
  witness := h.witness

/--
Reverse bridge: a specialized generic provider for `allFunctionsFamily`
can be used as the default all-functions multi-switching package.
-/
def allFunctions_multiSwitchingPackage_of_provider
    (params : ThirdPartyFacts.AC0Parameters)
    [h :
      ThirdPartyFacts.AC0MultiSwitchingWitnessProvider
        params
        (Counting.allFunctionsFamily params.n)] :
    AllFunctionsAC0MultiSwitchingWitness params :=
  ⟨h.witness⟩


/--
  Корректный AC⁰-решатель Partial MCSP.

  Здесь фиксируем только интерфейс: функция `decide` и доказательство
  корректности относительно `GapPartialMCSPPromise`.
-/
structure SmallAC0Solver_Partial (p : GapPartialMCSPParams) where
  params : SmallAC0ParamsPartial p
  sem : ComplexityInterfaces.SemanticDecider (partialInputLen p)
  witness : sem.Carrier
  correct : SolvesPromise (GapPartialMCSPPromise p) (fun x => sem.eval witness x)

/-- Evaluator induced by the semantic witness of an AC0 solver. -/
@[simp] def SmallAC0Solver_Partial.decide
    {p : GapPartialMCSPParams}
    (solver : SmallAC0Solver_Partial p) :
    Core.BitVec (partialInputLen p) → Bool :=
  fun x => solver.sem.eval solver.witness x

/-- Convenience view of `correct` through `solver.decide`. -/
lemma SmallAC0Solver_Partial.correct_decide
    {p : GapPartialMCSPParams}
    (solver : SmallAC0Solver_Partial p) :
    SolvesPromise (GapPartialMCSPPromise p) solver.decide := by
  simpa [SmallAC0Solver_Partial.decide] using solver.correct

/-!
  ### Semantic AC0 witness API (non-vacuous Step-C interface)

  The legacy route below uses `allFunctionsFamily` witnesses.  For a
  semantically faithful Step-C statement we expose a solver-local witness
  interface: the AC0 evidence must be attached to the concrete solver function.
-/

/-- Solver function viewed on the AC0 input length `solver.params.ac0.n`. -/
def solverDecideOnAC0Domain
    {p : GapPartialMCSPParams}
    (solver : SmallAC0Solver_Partial p) :
    Core.BitVec solver.params.ac0.n → Bool :=
  solver.params.same_n ▸ solver.decide

/--
Singleton family containing exactly the concrete solver function.
-/
def solverFunctionFamily
    {p : GapPartialMCSPParams}
    (solver : SmallAC0Solver_Partial p) :
    Core.Family solver.params.ac0.n :=
  [solverDecideOnAC0Domain solver]

/--
Semantic AC0 witness for a concrete solver:
the solver's own function family (singleton) is AC0-realizable.
-/
def SolverAC0WitnessPartial
    {p : GapPartialMCSPParams}
    (solver : SmallAC0Solver_Partial p) : Prop :=
  ThirdPartyFacts.AC0FamilyWitnessProp
    solver.params.ac0
    (solverFunctionFamily solver)

/--
Multi-switching witness counterpart for the concrete solver family.
-/
def SolverAC0MultiSwitchingWitnessPartial
    {p : GapPartialMCSPParams}
    (solver : SmallAC0Solver_Partial p) : Type :=
  ThirdPartyFacts.AC0MultiSwitchingWitness
    solver.params.ac0
    (solverFunctionFamily solver)

/--
Family-level AC0 data for a counting-style Step-C contradiction.

`F` is the candidate "easy" class, `witness` gives AC0 realizability, and
`card_lower` is the large-cardinality premise required by the capacity gap.
-/
structure AC0EasyFamilyDataPartial (params : ThirdPartyFacts.AC0Parameters) where
  F : Core.Family params.n
  witness : ThirdPartyFacts.AC0FamilyWitnessProp params F
  card_lower : Nat.pow 2 (Nat.pow 2 params.n) ≤ F.toFinset.card

/--
Constructive Step-C solver package:
the solver carries the full easy-family counting data internally.
-/
structure ConstructiveSmallAC0Solver_Partial (p : GapPartialMCSPParams)
    extends SmallAC0Solver_Partial p where
  easyData : AC0EasyFamilyDataPartial params.ac0

/-!
  ### Локальные схемы (partial‑трек)

  Локальная версия структуры повторяет интерфейс AC⁰-оболочки,
  но работает с длиной входа `partialInputLen p`.
-/

structure SmallLocalCircuitParamsPartial (p : GapPartialMCSPParams) where
  params : ThirdPartyFacts.LocalCircuitParameters
  same_n : params.n = partialInputLen p
  /-- Quantitative smallness assumption for local circuits. -/
  small : ThirdPartyFacts.LocalCircuitSmallEnough params
  deriving Repr

structure SmallLocalCircuitSolver_Partial (p : GapPartialMCSPParams) where
  params : SmallLocalCircuitParamsPartial p
  sem : ComplexityInterfaces.SemanticDecider (partialInputLen p)
  witness : sem.Carrier
  correct : SolvesPromise (GapPartialMCSPPromise p) (fun x => sem.eval witness x)
  decideLocal : ∃ (alive : Finset (Fin (partialInputLen p))),
    alive.card ≤ Partial.tableLen p.n / 2 ∧
    ∀ x y : Core.BitVec (partialInputLen p),
      (∀ i ∈ alive, x i = y i) →
        sem.eval witness x = sem.eval witness y

/-- Evaluator induced by the semantic witness of a local solver. -/
@[simp] def SmallLocalCircuitSolver_Partial.decide
    {p : GapPartialMCSPParams}
    (solver : SmallLocalCircuitSolver_Partial p) :
    Core.BitVec (partialInputLen p) → Bool :=
  fun x => solver.sem.eval solver.witness x

/-- Convenience view of `correct` through `solver.decide`. -/
lemma SmallLocalCircuitSolver_Partial.correct_decide
    {p : GapPartialMCSPParams}
    (solver : SmallLocalCircuitSolver_Partial p) :
    SolvesPromise (GapPartialMCSPPromise p) solver.decide := by
  simpa [SmallLocalCircuitSolver_Partial.decide] using solver.correct

/-- Convenience view of `decideLocal` through `solver.decide`. -/
lemma SmallLocalCircuitSolver_Partial.decideLocal_decide
    {p : GapPartialMCSPParams}
    (solver : SmallLocalCircuitSolver_Partial p) :
    ∃ (alive : Finset (Fin (partialInputLen p))),
      alive.card ≤ Partial.tableLen p.n / 2 ∧
      ∀ x y : Core.BitVec (partialInputLen p),
        (∀ i ∈ alive, x i = y i) → solver.decide x = solver.decide y := by
  rcases solver.decideLocal with ⟨alive, hcard, hloc⟩
  refine ⟨alive, hcard, ?_⟩
  intro x y hxy
  simpa [SmallLocalCircuitSolver_Partial.decide] using hloc x y hxy

/-!
  ### Counting-утверждения для Partial MCSP

  Здесь мы фиксируем минимальный набор комбинаторных фактов, которые нужны
  для anti-checker'а.  Центральная мысль: число тотальных функций,
  согласованных с частичной таблицей `T`, равно `2^{undefinedCount T}`.

  Эти леммы являются «локальным мостом» между моделью `PartialTruthTable`
  и подсчётными оценками, используемыми в Part C.
-/

/-- Множество тотальных функций, согласованных с таблицей `T`. -/
def consistentTotals {n : Nat} (T : PartialFunction n) :
    Set (TotalFunction n) :=
  fun f => consistentTotal T f

/-- Подтип согласованных функций (для явной кардинальности). -/
abbrev ConsistentTotalSubtype {n : Nat} (T : PartialFunction n) :=
  {f : TotalFunction n // consistentTotal T f}

/-- Кардинал согласованных функций равен `2^{undefinedCount T}`. -/
lemma card_consistentTotals {n : Nat} (T : PartialFunction n) :
    Fintype.card (ConsistentTotalSubtype T) = 2 ^ undefinedCount T := by
  simpa [ConsistentTotalSubtype] using (card_consistentTotal (T := T))

/-- Если `undefinedCount T = k`, то согласованных функций ровно `2^k`. -/
lemma card_consistentTotals_eq {n : Nat} (T : PartialFunction n) (k : Nat)
    (hk : undefinedCount T = k) :
    Fintype.card (ConsistentTotalSubtype T) = 2 ^ k := by
  simpa [hk] using (card_consistentTotals (T := T))

/-- Верхняя оценка: число согласованных функций не больше всех функций `2^{2^n}`. -/
lemma card_consistentTotals_le_all {n : Nat} (T : PartialFunction n) :
    Fintype.card (ConsistentTotalSubtype T) ≤ 2 ^ (2 ^ n) := by
  -- Используем `undefinedCount T ≤ 2^n` и монотонность степени.
  have hcount : undefinedCount T ≤ Partial.tableLen n :=
    undefinedCount_le_tableLen (T := T)
  have hpow : 2 ^ undefinedCount T ≤ 2 ^ Partial.tableLen n :=
    Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hcount
  -- Переписываем `Partial.tableLen n = 2^n`.
  simpa [Partial.tableLen] using
    (le_trans (by simpa using (card_consistentTotals (T := T)).le) hpow)

/-!
  ### Partial-таблицы, согласованные с фиксированной тотальной функцией

  Этот блок симметричен предыдущему: вместо фиксированной partial-таблицы
  мы фиксируем тотальную функцию `f` и считаем, сколько partial-таблиц
  с ней согласуются. Это число равно `2^{2^n}` (маска свободна).
-/

/-- Тотальная функция в табличной форме. -/
abbrev TotalTable (n : Nat) := TotalFunction n

/-- Частичная таблица в табличной форме. -/
abbrev PartialTable (n : Nat) := PartialFunction n

/-- Множество всех тотальных таблиц. -/
def totalTables (n : Nat) : Finset (TotalTable n) := Finset.univ

/-- Множество всех partial‑таблиц. -/
def partialTables (n : Nat) : Finset (PartialTable n) := Finset.univ

/-- Кардинал всех тотальных таблиц равен `2^{2^n}`. -/
lemma card_totalTables (n : Nat) :
    (totalTables n).card = 2 ^ Partial.tableLen n := by
  classical
  simp [totalTables, TotalTable, TotalFunction]

/-- Кардинал всех partial‑таблиц равен `3^{2^n}`. -/
lemma card_partialTables (n : Nat) :
    (partialTables n).card = 3 ^ Partial.tableLen n := by
  classical
  simp [partialTables, PartialTable]

/-- Множество partial‑таблиц, согласованных с фиксированной `f`. -/
def consistentPartials {n : Nat} (f : TotalTable n) : Set (PartialTable n) :=
  fun T => consistentWithTotal T f

/-- Подтип partial‑таблиц, согласованных с фиксированной `f`. -/
abbrev ConsistentPartialSubtype {n : Nat} (f : TotalTable n) :=
  {T : PartialTable n // consistentWithTotal T f}

/-- Кардинал согласованных partial‑таблиц равен `2^{2^n}`. -/
lemma card_consistentPartials {n : Nat} (f : TotalTable n) :
    Fintype.card (ConsistentPartialSubtype f) = 2 ^ Partial.tableLen n := by
  have hcard := card_consistentPartial_withTotal (f := f)
  simpa [ConsistentPartialSubtype, TotalTable, PartialTable] using hcard

/-- Эквивалентная форма: `2^{2^n}` как `2^(2^n)`. -/
lemma card_consistentPartials_eq (n : Nat) (f : TotalTable n) :
    Fintype.card (ConsistentPartialSubtype f) = 2 ^ (2 ^ n) := by
  simpa [Partial.tableLen] using (card_consistentPartials (f := f))

/-- Кардинал согласованных partial‑таблиц не превосходит всех partial‑таблиц. -/
lemma card_consistentPartials_le_all {n : Nat} (f : TotalTable n) :
    Fintype.card (ConsistentPartialSubtype f) ≤ 3 ^ Partial.tableLen n := by
  -- Подтип множества всех partial‑таблиц.
  have hle :
      Fintype.card (ConsistentPartialSubtype f) ≤ Fintype.card (PartialTable n) :=
    Fintype.card_subtype_le (p := fun T : PartialTable n => consistentWithTotal T f)
  simpa [PartialTable, card_partialTables n] using hle

/-!
  ### Финитные семейства согласованных partial‑таблиц

  Для работы с `Finset` (как в Part B) полезно иметь явный список/финит
  всех partial‑таблиц, согласованных с фиксированной тотальной функцией `f`.
-/

/-- Финитное множество partial‑таблиц, согласованных с `f`. -/
noncomputable def consistentPartialsFinset {n : Nat} (f : TotalTable n) :
    Finset (PartialTable n) := by
  classical
  exact (partialTables n).filter (fun T => consistentWithTotal T f)

/-- Характеризация принадлежности `consistentPartialsFinset`. -/
lemma mem_consistentPartialsFinset {n : Nat} (f : TotalTable n) (T : PartialTable n) :
    T ∈ consistentPartialsFinset (f := f) ↔ consistentWithTotal T f := by
  classical
  simp [consistentPartialsFinset, partialTables, PartialTable]

/-- `consistentPartialsFinset` — подмножество `partialTables`. -/
lemma consistentPartialsFinset_subset {n : Nat} (f : TotalTable n) :
    consistentPartialsFinset (f := f) ⊆ partialTables n := by
  classical
  intro T hT
  -- Фильтрация по `consistentWithTotal` не выводит из `partialTables`.
  have hmem :
      T ∈ partialTables n ∧ consistentWithTotal T f := by
    simpa [consistentPartialsFinset, partialTables] using hT
  exact hmem.1

/-- Кардинал `consistentPartialsFinset` не больше `3^{2^n}`. -/
lemma card_consistentPartialsFinset_le_all {n : Nat} (f : TotalTable n) :
    (consistentPartialsFinset (f := f)).card ≤ 3 ^ Partial.tableLen n := by
  classical
  -- Через подмножество `partialTables`.
  have hsubset := consistentPartialsFinset_subset (f := f)
  have hcard := Finset.card_le_card hsubset
  -- Переписываем кардинал всех partial‑таблиц.
  simpa [partialTables, PartialTable, card_partialTables n] using hcard

/-- Финитная версия согласованных partial‑таблиц совпадает с подтипом. -/
lemma card_consistentPartialsFinset_eq_subtype {n : Nat} (f : TotalTable n) :
    (consistentPartialsFinset (f := f)).card =
      Fintype.card (ConsistentPartialSubtype f) := by
  classical
  -- Считаем элементы через `Finset.filter` и `Fintype.card_subtype`.
  -- Кардинал фильтра равен кардиналу подтипа по предикату.
  have hcard :
      Fintype.card (ConsistentPartialSubtype f) =
        (Finset.univ.filter (fun T : PartialTable n => consistentWithTotal T f)).card := by
    simpa [ConsistentPartialSubtype] using
      (Fintype.card_subtype (p := fun T : PartialTable n => consistentWithTotal T f))
  -- Сводим `consistentPartialsFinset` к фильтру по `consistentWithTotal`.
  simpa [consistentPartialsFinset, partialTables, PartialTable] using hcard.symm

/-- Точная оценка: `consistentPartialsFinset` имеет кардинал `2^{2^n}`. -/
lemma card_consistentPartialsFinset_eq_pow {n : Nat} (f : TotalTable n) :
    (consistentPartialsFinset (f := f)).card = 2 ^ (2 ^ n) := by
  have hEq := card_consistentPartialsFinset_eq_subtype (f := f)
  have hCard := card_consistentPartials_eq (n := n) (f := f)
  simp [hEq, hCard]

/-!
  ### Дополнительные арифметические леммы

  Эти оценки используются в блоке `noSmallLocalCircuitSolver_partial` для
  передачи полиномиальной части в экспоненциальную форму.
-/

/-- Для больших `n` имеем `n+2 ≤ 2^(n/2)`; нужна для последующего деления. -/
lemma nplus2_le_twoPow_half (n : Nat) (hn : 16 ≤ n) :
    n + 2 ≤ Nat.pow 2 (n / 2) := by
  classical
  -- Классическая схема: вводим `m = n/2`, сравниваем квадратичную оценку.
  set m := n / 2
  have hm : 8 ≤ m := by
    have hmul : 8 * 2 ≤ n := by
      nlinarith
    exact (Nat.le_div_iff_mul_le (by decide : 0 < (2 : Nat))).2 hmul
  have hpow : m * (m + 2) < Nat.pow 2 m :=
    Counting.twoPow_gt_mul m hm
  have hmod_lt : n % 2 < 2 := Nat.mod_lt n (by decide : 0 < (2 : Nat))
  have hmod_le : n % 2 ≤ 1 := Nat.lt_succ_iff.mp hmod_lt
  have hdecomp : n = 2 * m + n % 2 := by
    have h := Nat.div_add_mod n 2
    calc
      n = n / 2 * 2 + n % 2 := by simpa [Nat.mul_comm] using h.symm
      _ = 2 * m + n % 2 := by
        simp [m, Nat.mul_comm]
  have hbound : n + 2 ≤ 2 * m + 3 := by
    nlinarith [hdecomp, hmod_le]
  have hquad : 2 * m + 3 ≤ m * (m + 2) := by
    have hm2 : 2 ≤ m := by exact le_trans (by decide : 2 ≤ 8) hm
    nlinarith [hm2]
  have hle : n + 2 ≤ m * (m + 2) := le_trans hbound hquad
  have hlt : n + 2 < Nat.pow 2 m := lt_of_le_of_lt hle hpow
  exact le_of_lt hlt

/-- Переводим `n+2 ≤ 2^(n/2)` в нужное неравенство с делением. -/
lemma twoPow_half_le_div (n : Nat) (hn : 16 ≤ n) :
    Nat.pow 2 (n / 2) ≤ Nat.pow 2 n / (n + 2) := by
  classical
  have hbase : n + 2 ≤ Nat.pow 2 (n / 2) :=
    nplus2_le_twoPow_half n hn
  have hpos : 0 < n + 2 := by
    exact Nat.succ_pos (n + 1)
  apply (Nat.le_div_iff_mul_le hpos).2
  have hmul :
      Nat.pow 2 (n / 2) * (n + 2)
        ≤ Nat.pow 2 (n / 2) * Nat.pow 2 (n / 2) := by
    exact Nat.mul_le_mul_left _ hbase
  have hpow_le :
      Nat.pow 2 (n / 2) * Nat.pow 2 (n / 2) ≤ Nat.pow 2 n := by
    have hsum : n / 2 + n / 2 ≤ n := by
      have hmul : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
      nlinarith
    have hpow := Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hsum
    calc
      Nat.pow 2 (n / 2) * Nat.pow 2 (n / 2)
          = Nat.pow 2 (n / 2 + n / 2) := by
            simp [Nat.pow_add]
      _ ≤ Nat.pow 2 n := hpow
  exact le_trans hmul hpow_le

/-!
  ### Union-bound заготовки (Partial MCSP)

  Цель следующего блока — формализовать «комбинаторный union bound»:
  если есть семейство малых схем, то объединение их согласованных наборов
  partial‑таблиц всё ещё меньше общего числа таблиц, а значит существует
  таблица вне покрытия.

  Здесь мы вводим минимальные абстрактные конструкции над семействами
  `Finset`, чтобы потом подставить оценки из counting‑лемм.
-/

/-- Семейство наборов partial‑таблиц: каждому решателю сопоставляется набор `Finset`. -/
noncomputable def familyOfPartialSets {n : Nat} (F : Finset (TotalTable n)) :
    Finset (Finset (PartialTable n)) :=
  F.image (fun f => consistentPartialsFinset (f := f))

/-- Объединение всех наборов из `familyOfPartialSets`. -/
noncomputable def unionPartialSets {n : Nat} (F : Finset (TotalTable n)) :
    Finset (PartialTable n) :=
  (familyOfPartialSets (F := F)).biUnion id

/-!
  Для дальнейших рассуждений удобно иметь явную формулировку «покрытия»
  partial‑таблицы семейством `F`.
-/

/-- Таблица `T` покрыта семейством `F`, если согласована с некоторым `f ∈ F`. -/
def coveredByFamily {n : Nat} (F : Finset (TotalTable n)) (T : PartialTable n) : Prop :=
  ∃ f ∈ F, T ∈ consistentPartialsFinset (f := f)

/-- Характеризация принадлежности объединению через `coveredByFamily`. -/
lemma mem_unionPartialSets_iff {n : Nat} (F : Finset (TotalTable n)) (T : PartialTable n) :
    T ∈ unionPartialSets (F := F) ↔ coveredByFamily F T := by
  classical
  constructor
  · intro hT
    rcases Finset.mem_biUnion.mp hT with ⟨S, hS, hmem⟩
    rcases Finset.mem_image.mp hS with ⟨f, hfF, rfl⟩
    exact ⟨f, hfF, hmem⟩
  · rintro ⟨f, hfF, hmem⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨consistentPartialsFinset (f := f), ?_, hmem⟩
    exact Finset.mem_image.mpr ⟨f, hfF, rfl⟩

/-- Если таблица не в объединении, то она не покрыта семейством `F`. -/
lemma not_covered_of_not_mem_union {n : Nat} (F : Finset (TotalTable n))
    {T : PartialTable n} (h : T ∉ unionPartialSets (F := F)) :
    ¬ coveredByFamily F T := by
  intro hcov
  exact h ((mem_unionPartialSets_iff (F := F) T).2 hcov)

/-- Если таблица покрыта семейством `F`, то она лежит в объединении. -/
lemma mem_union_of_covered {n : Nat} (F : Finset (TotalTable n))
    {T : PartialTable n} (hcov : coveredByFamily F T) :
    T ∈ unionPartialSets (F := F) := by
  exact (mem_unionPartialSets_iff (F := F) T).2 hcov

/-- Если таблица не покрыта, то она вне объединения. -/
lemma not_mem_union_of_not_covered {n : Nat} (F : Finset (TotalTable n))
    {T : PartialTable n} (hcov : ¬ coveredByFamily F T) :
    T ∉ unionPartialSets (F := F) := by
  intro hmem
  exact hcov ((mem_unionPartialSets_iff (F := F) T).1 hmem)

/-- Внутри `partialTables` покрытие эквивалентно принадлежности объединению. -/
lemma covered_iff_mem_union {n : Nat} (F : Finset (TotalTable n))
    (T : PartialTable n) :
    coveredByFamily F T ↔ T ∈ unionPartialSets (F := F) := by
  exact (mem_unionPartialSets_iff (F := F) T).symm

/-- Если таблица покрыта, то она согласована хотя бы с одним `f ∈ F`. -/
lemma coveredByFamily_exists_consistent {n : Nat} (F : Finset (TotalTable n))
    {T : PartialTable n} (hcov : coveredByFamily F T) :
    ∃ f ∈ F, consistentWithTotal T f := by
  rcases hcov with ⟨f, hfF, hmem⟩
  exact ⟨f, hfF, (mem_consistentPartialsFinset (f := f) T).1 hmem⟩

/-!
  Эти леммы позволяют формулировать «hard‑instance» как отрицание покрытия
  семейства малых решателей: `¬ coveredByFamily F T`.
-/

/-- Мощность объединения не превосходит суммы мощностей (тривиальный union bound). -/
lemma card_unionPartialSets_le_sum {n : Nat} (F : Finset (TotalTable n)) :
    (unionPartialSets (F := F)).card ≤
      (familyOfPartialSets (F := F)).sum Finset.card := by
  classical
  -- Используем стандартную лемму `card_biUnion_le`.
  simpa [unionPartialSets, familyOfPartialSets] using
    (Finset.card_biUnion_le (s := familyOfPartialSets (F := F)) (t := id))

/-- Каждое множество в `familyOfPartialSets` имеет кардинал `2^(2^n)`. -/
lemma card_familyOfPartialSets_eq {n : Nat} (F : Finset (TotalTable n)) :
    ∀ S ∈ familyOfPartialSets (F := F),
      S.card = 2 ^ (2 ^ n) := by
  classical
  intro S hS
  -- Раскрываем, что `S` — образ `consistentPartialsFinset`.
  rcases Finset.mem_image.mp hS with ⟨f, hfF, rfl⟩
  -- Теперь применяем точную формулу.
  exact card_consistentPartialsFinset_eq_pow (f := f)

/-- Грубая оценка суммарной мощности семейства через `|F| * 2^(2^n)`. -/
lemma sum_familyOfPartialSets_le {n : Nat} (F : Finset (TotalTable n)) :
    (familyOfPartialSets (F := F)).sum Finset.card ≤
      F.card * 2 ^ (2 ^ n) := by
  classical
  -- Каждое множество в семействе имеет кардинал `2^(2^n)`.
  have hcard_eq : ∀ S ∈ familyOfPartialSets (F := F),
      S.card = 2 ^ (2 ^ n) :=
    card_familyOfPartialSets_eq (F := F)
  -- Сумма равна `card * 2^(2^n)` на уровне семейства `familyOfPartialSets`.
  have hsum :
      (familyOfPartialSets (F := F)).sum Finset.card =
        (familyOfPartialSets (F := F)).card * 2 ^ (2 ^ n) := by
    classical
    have hsum' :
        (familyOfPartialSets (F := F)).sum Finset.card =
          (familyOfPartialSets (F := F)).sum (fun _ => 2 ^ (2 ^ n)) := by
      refine Finset.sum_congr rfl ?_
      intro S hS
      simp [hcard_eq S hS]
    calc
      (familyOfPartialSets (F := F)).sum Finset.card
          = (familyOfPartialSets (F := F)).sum (fun _ => 2 ^ (2 ^ n)) := hsum'
      _ = (familyOfPartialSets (F := F)).card * 2 ^ (2 ^ n) := by
            simp
  -- Кардинал образа не превосходит кардинал исходного множества.
  have hcard_le : (familyOfPartialSets (F := F)).card ≤ F.card := by
    simpa [familyOfPartialSets] using
      (Finset.card_image_le (s := F) (f := fun f => consistentPartialsFinset (f := f)))
  -- Итоговая оценка.
  exact (hsum.le.trans (Nat.mul_le_mul_right _ hcard_le))


/-!
  ### Существование таблицы вне объединения

  Этот блок превращает union‑bound оценку в существование partial‑таблицы,
  не попадающей в объединение всех согласованных наборов.
-/

/-- Если объединение меньше полного множества, есть таблица вне объединения. -/
lemma exists_partial_not_in_union {n : Nat} (F : Finset (TotalTable n))
    (hcard : (unionPartialSets (F := F)).card < (partialTables n).card) :
    ∃ T ∈ partialTables n, T ∉ unionPartialSets (F := F) := by
  classical
  -- Показываем, что объединение — подмножество `partialTables`.
  have hsub : unionPartialSets (F := F) ⊆ partialTables n := by
    intro T hT
    rcases Finset.mem_biUnion.mp hT with ⟨S, hS, hmem⟩
    rcases Finset.mem_image.mp hS with ⟨f, hfF, rfl⟩
    exact consistentPartialsFinset_subset (f := f) hmem
  -- Применяем общую комбинаторную лемму.
  exact _root_.Pnp3.Core.Restriction.exists_not_mem_of_subset_card_lt hsub hcard

/-- Достаточное условие для существования таблицы вне `familyOfPartialSets`. -/
lemma exists_partial_outside_family {n : Nat} (F : Finset (TotalTable n))
    (hbound : (familyOfPartialSets (F := F)).sum Finset.card < (partialTables n).card) :
    ∃ T ∈ partialTables n, T ∉ unionPartialSets (F := F) := by
  -- Оцениваем кардинал объединения суммой.
  have hcard_union :
      (unionPartialSets (F := F)).card < (partialTables n).card := by
    have hle := card_unionPartialSets_le_sum (F := F)
    exact lt_of_le_of_lt hle hbound
  exact exists_partial_not_in_union (F := F) hcard_union

/-!
  ### Комбинаторный критерий существования hard‑таблицы

  Следующие леммы позволяют «закрыть цикл»: если число решателей мало
  (точнее, их семейство `F` имеет кардинал, дающий строгий разрыв),
  то существует partial‑таблица, не согласованная ни с одним решателем.
-/

/-- Полная мощность partial‑таблиц равна `3^(2^n)` в терминах `2^n`. -/
lemma card_partialTables_pow (n : Nat) :
    (partialTables n).card = 3 ^ (2 ^ n) := by
  classical
  -- Переписываем через `Partial.tableLen n = 2^n`.
  simpa [Partial.tableLen] using (card_partialTables n)

/-- Достаточно, чтобы `|F| * 2^(2^n) < 3^(2^n)`, тогда есть таблица вне union. -/
lemma exists_partial_outside_if_card_lt {n : Nat} (F : Finset (TotalTable n))
    (hsmall : F.card * 2 ^ (2 ^ n) < 3 ^ (2 ^ n)) :
    ∃ T ∈ partialTables n, T ∉ unionPartialSets (F := F) := by
  -- Сначала оцениваем сумму семейства через `|F| * 2^(2^n)`.
  have hsum_le : (familyOfPartialSets (F := F)).sum Finset.card ≤
      F.card * 2 ^ (2 ^ n) :=
    sum_familyOfPartialSets_le (F := F)
  -- Затем сравниваем с полной мощностью partial‑таблиц.
  have hbound :
      (familyOfPartialSets (F := F)).sum Finset.card < (partialTables n).card := by
    have hcard : (partialTables n).card = 3 ^ (2 ^ n) :=
      card_partialTables_pow n
    -- Комбинируем оценку суммы с предположением `hsmall`.
    exact lt_of_le_of_lt hsum_le (by simpa [hcard] using hsmall)
  exact exists_partial_outside_family (F := F) hbound

/-- Версия с явным `Partial.tableLen` (удобно в доказательствах без `2^n`). -/
lemma exists_partial_outside_if_card_lt_tableLen {n : Nat} (F : Finset (TotalTable n))
    (hsmall : F.card * 2 ^ Partial.tableLen n < 3 ^ Partial.tableLen n) :
    ∃ T ∈ partialTables n, T ∉ unionPartialSets (F := F) := by
  -- Переписываем в форме `2^n`.
  have hsmall' : F.card * 2 ^ (2 ^ n) < 3 ^ (2 ^ n) := by
    simpa [Partial.tableLen] using hsmall
  exact exists_partial_outside_if_card_lt (F := F) hsmall'

/-!
  TODO (следующий шаг): связать множество `F` с семейством «малых» AC⁰‑решателей
  и получить конкретную числовую оценку для `F.card`, чтобы применить
  `exists_partial_outside_if_card_lt`.
-/

/-!
  ### Hard‑таблицы относительно семейства `F`

  Определяем, что таблица «hard» относительно семейства решателей `F`,
  если она лежит в полном множестве partial‑таблиц и не покрывается `F`.
  Далее формализуем удобные леммы, превращающие union‑bound в такую таблицу.
-/

/-- Таблица hard относительно `F`, если не покрывается семейством. -/
def HardForFamily {n : Nat} (F : Finset (TotalTable n)) (T : PartialTable n) : Prop :=
  T ∈ partialTables n ∧ ¬ coveredByFamily F T

/-- Оболочка‑свидетель hard‑таблицы. -/
structure HardWitness {n : Nat} (F : Finset (TotalTable n)) where
  table : PartialTable n
  table_mem : table ∈ partialTables n
  not_covered : ¬ coveredByFamily F table

/-- Из `HardForFamily` получаем `HardWitness`. -/
def hardForFamily_to_witness {n : Nat} {F : Finset (TotalTable n)}
    {T : PartialTable n} (h : HardForFamily F T) : HardWitness F := by
  refine ⟨T, h.1, h.2⟩

/-- Любой `HardWitness` даёт `HardForFamily`. -/
lemma hardWitness_to_hard {n : Nat} {F : Finset (TotalTable n)}
    (w : HardWitness F) : HardForFamily F w.table := by
  exact ⟨w.table_mem, w.not_covered⟩

/-- Если `T` вне union, то `T` hard относительно `F`. -/
lemma hard_of_not_in_union {n : Nat} (F : Finset (TotalTable n))
    {T : PartialTable n} (hmem : T ∈ partialTables n)
    (h : T ∉ unionPartialSets (F := F)) : HardForFamily F T := by
  exact ⟨hmem, not_covered_of_not_mem_union (F := F) h⟩

/-- Если `T` hard, то `T` не согласована ни с одним `f ∈ F`. -/
lemma hard_not_consistent {n : Nat} (F : Finset (TotalTable n))
    {T : PartialTable n} (h : HardForFamily F T) :
    ∀ f ∈ F, ¬ consistentWithTotal T f := by
  intro f hfF hcons
  have hcov : coveredByFamily F T := by
    exact ⟨f, hfF, (mem_consistentPartialsFinset (f := f) T).2 hcons⟩
  exact h.2 hcov

/-- Из `exists_partial_outside_family` получаем hard‑таблицу (свидетель). -/
noncomputable def exists_hard_of_outside_family {n : Nat} (F : Finset (TotalTable n))
    (h : ∃ T ∈ partialTables n, T ∉ unionPartialSets (F := F)) :
    HardWitness F := by
  classical
  refine ⟨Classical.choose h, ?_, ?_⟩
  · exact (Classical.choose_spec h).1
  · exact not_covered_of_not_mem_union (F := F) (Classical.choose_spec h).2

/-- Конструктивный критерий: если `|F| * 2^(2^n) < 3^(2^n)`, есть hard‑таблица. -/
noncomputable def exists_hard_if_card_lt {n : Nat} (F : Finset (TotalTable n))
    (hsmall : F.card * 2 ^ (2 ^ n) < 3 ^ (2 ^ n)) :
    HardWitness F := by
  have hex :=
    exists_partial_outside_if_card_lt (F := F) hsmall
  exact exists_hard_of_outside_family (F := F) hex

/-- Версия с `Partial.tableLen`. -/
noncomputable def exists_hard_if_card_lt_tableLen {n : Nat} (F : Finset (TotalTable n))
    (hsmall : F.card * 2 ^ Partial.tableLen n < 3 ^ Partial.tableLen n) :
    HardWitness F := by
  have hex :=
    exists_partial_outside_if_card_lt_tableLen (F := F) hsmall
  exact exists_hard_of_outside_family (F := F) hex

/-!
  Эти леммы отделяют комбинаторную часть (подсчёты) от структурной:
  как только получена оценка на `F.card`, можно получить `HardWitness`.
-/

/-!
  ### Дополнительные формы hard‑свидетелей

  Эти леммы делают удобные преобразования между `HardWitness`, отрицанием
  покрытия и оценками по union‑bound. Они упрощают подключение результата
  к anti-checker'у и последующему выводу о NO‑слое.
-/

/-- Сокращённая форма: существует hard‑таблица. -/
def HardInstance {n : Nat} (F : Finset (TotalTable n)) : Prop :=
  ∃ T : PartialTable n, HardForFamily F T

/-- `HardWitness` даёт `HardInstance`. -/
lemma hardWitness_to_instance {n : Nat} {F : Finset (TotalTable n)}
    (w : HardWitness F) : HardInstance F := by
  exact ⟨w.table, hardWitness_to_hard (w := w)⟩

/-- Если таблица hard, она не лежит в union‑покрытии. -/
lemma hard_not_in_union {n : Nat} (F : Finset (TotalTable n))
    {T : PartialTable n} (h : HardForFamily F T) :
    T ∉ unionPartialSets (F := F) := by
  exact not_mem_union_of_not_covered (F := F) (hcov := h.2)

/-- Эквивалентность: hard‑таблица ⇔ вне `unionPartialSets`. -/
lemma hard_iff_not_in_union {n : Nat} (F : Finset (TotalTable n))
    {T : PartialTable n} :
    HardForFamily F T ↔ T ∈ partialTables n ∧ T ∉ unionPartialSets (F := F) := by
  constructor
  · intro h
    exact ⟨h.1, hard_not_in_union (F := F) h⟩
  · intro h
    exact hard_of_not_in_union (F := F) h.1 h.2

/-- Из строгой оценки на union‑bound получаем `HardInstance`. -/
lemma exists_hard_of_sum_lt {n : Nat} (F : Finset (TotalTable n))
    (hbound : (familyOfPartialSets (F := F)).sum Finset.card < (partialTables n).card) :
    HardInstance F := by
  rcases exists_partial_outside_family (F := F) hbound with ⟨T, hmem, hnot⟩
  exact ⟨T, hard_of_not_in_union (F := F) hmem hnot⟩

/-- Из строгой оценки на union‑card получаем `HardInstance`. -/
lemma exists_hard_of_union_lt {n : Nat} (F : Finset (TotalTable n))
    (hcard : (unionPartialSets (F := F)).card < (partialTables n).card) :
    HardInstance F := by
  rcases exists_partial_not_in_union (F := F) hcard with ⟨T, hmem, hnot⟩
  exact ⟨T, hard_of_not_in_union (F := F) hmem hnot⟩

/-- Hard‑таблица даёт явное отрицание согласованности для любого `f ∈ F`. -/
lemma hard_not_consistent_all {n : Nat} (F : Finset (TotalTable n))
    (w : HardWitness F) :
    ∀ f ∈ F, ¬ consistentWithTotal w.table f := by
  exact hard_not_consistent (F := F) (h := hardWitness_to_hard (w := w))

/-!
  Эти формы позволяют подключать hard‑свидетель прямо в NO‑условия,
  минуя ручное распаковывание union‑bound лемм.
-/

/-!
  ### Good‑таблицы (эквивалентное имя)

  В ряде формулировок удобнее говорить о "good" таблице: она лежит в
  полном множестве partial‑таблиц и не покрыта семейством `F`.
  Это синоним `HardForFamily`, но с более «поведенческой» трактовкой.
-/

/-- Таблица считается good относительно `F`, если она валидна и не покрыта. -/
def GoodTable {n : Nat} (F : Finset (TotalTable n)) (T : PartialTable n) : Prop :=
  T ∈ partialTables n ∧ ¬ coveredByFamily F T

/-- `GoodTable` эквивалентен `HardForFamily`. -/
lemma good_iff_hard {n : Nat} (F : Finset (TotalTable n)) (T : PartialTable n) :
    GoodTable F T ↔ HardForFamily F T := by
  rfl

/-- Из hard‑свидетеля получаем good‑таблицу. -/
lemma good_of_hardWitness {n : Nat} (F : Finset (TotalTable n))
    (w : HardWitness F) : GoodTable F w.table := by
  exact hardWitness_to_hard (w := w)

/-- Если таблица good, то она вне union. -/
lemma good_not_in_union {n : Nat} (F : Finset (TotalTable n))
    {T : PartialTable n} (h : GoodTable F T) :
    T ∉ unionPartialSets (F := F) := by
  exact hard_not_in_union (F := F) (h := h)

/-- Если таблица вне union, то она good. -/
lemma good_of_not_in_union {n : Nat} (F : Finset (TotalTable n))
    {T : PartialTable n} (hmem : T ∈ partialTables n)
    (h : T ∉ unionPartialSets (F := F)) : GoodTable F T := by
  exact hard_of_not_in_union (F := F) hmem h

/-- Любая good‑таблица не согласована ни с одним `f ∈ F`. -/
lemma good_not_consistent {n : Nat} (F : Finset (TotalTable n))
    {T : PartialTable n} (h : GoodTable F T) :
    ∀ f ∈ F, ¬ consistentWithTotal T f := by
  exact hard_not_consistent (F := F) (h := h)

/-- Существование good‑таблицы из union‑bound оценки. -/
lemma exists_good_of_sum_lt {n : Nat} (F : Finset (TotalTable n))
    (hbound : (familyOfPartialSets (F := F)).sum Finset.card < (partialTables n).card) :
    ∃ T : PartialTable n, GoodTable F T := by
  rcases exists_partial_outside_family (F := F) hbound with ⟨T, hmem, hnot⟩
  exact ⟨T, good_of_not_in_union (F := F) hmem hnot⟩

/-- Существование good‑таблицы из оценки `|F| * 2^(2^n) < 3^(2^n)`. -/
lemma exists_good_if_card_lt {n : Nat} (F : Finset (TotalTable n))
    (hsmall : F.card * 2 ^ (2 ^ n) < 3 ^ (2 ^ n)) :
    ∃ T : PartialTable n, GoodTable F T := by
  rcases exists_hard_if_card_lt (F := F) hsmall with ⟨T, hmem, hnot⟩
  exact ⟨T, ⟨hmem, hnot⟩⟩

/-- Версия с `Partial.tableLen`. -/
lemma exists_good_if_card_lt_tableLen {n : Nat} (F : Finset (TotalTable n))
    (hsmall : F.card * 2 ^ Partial.tableLen n < 3 ^ Partial.tableLen n) :
    ∃ T : PartialTable n, GoodTable F T := by
  rcases exists_hard_if_card_lt_tableLen (F := F) hsmall with ⟨T, hmem, hnot⟩
  exact ⟨T, ⟨hmem, hnot⟩⟩

/-!
  ### Преобразования good ↔ witness

  Иногда удобнее работать с `HardWitness`, чем с чистой формулой `GoodTable`.
  Ниже фиксируем простые преобразования между ними.
-/

/-- Из good‑таблицы получаем `HardWitness`. -/
def witness_of_good {n : Nat} (F : Finset (TotalTable n))
    {T : PartialTable n} (h : GoodTable F T) : HardWitness F := by
  exact hardForFamily_to_witness h

/-- Любой `HardWitness` даёт good‑таблицу. -/
lemma good_of_witness {n : Nat} (F : Finset (TotalTable n))
    (w : HardWitness F) : GoodTable F w.table := by
  exact good_of_hardWitness (F := F) w

/-!
  Эти леммы позволяют формулировать итог anti‑checker напрямую как
  существование good‑таблицы без покрытия семейства решателей.
-/

/-!
  ### Базовые следствия корректности решателя

  Эти леммы служат «мостом» между promise-формализацией и конкретным
  языком Partial MCSP, аналогично `AntiChecker.lean` в legacy-треке.
-/

/-- Корректный решатель совпадает с языком Partial MCSP на всех входах. -/
lemma solver_decide_eq_language
    {p : GapPartialMCSPParams} (solver : SmallAC0Solver_Partial p) :
    solver.decide = gapPartialMCSP_Language p (partialInputLen p) := by
  apply funext
  intro x
  have hsolves :=
    (solvesPromise_gapPartialMCSP_iff (p := p) (decide := solver.decide)).1
      solver.correct
  exact hsolves x

/-!
  ### Приведение к входной длине AC⁰

  Удобно иметь версию решателя, действующую на входах длины `ac0.n`.
  Это позволяет напрямую использовать семейства функций из части B.
-/

/-- Решатель, перенесённый на входную длину `ac0.n`. -/
def decide_ac0
    {p : GapPartialMCSPParams} (solver : SmallAC0Solver_Partial p) :
    Core.BitVec solver.params.ac0.n → Bool :=
  solver.params.same_n ▸ solver.decide

lemma decide_ac0_eq_language
    {p : GapPartialMCSPParams} (solver : SmallAC0Solver_Partial p) :
    decide_ac0 solver =
      solver.params.same_n ▸ gapPartialMCSP_Language p (partialInputLen p) := by
  have hEq := solver_decide_eq_language solver
  simpa [decide_ac0] using congrArg (fun f => (solver.params.same_n ▸ f)) hEq

/-!
  ### Полный anti-checker в partial-треке (аналог legacy-версии)

  Ниже мы переносим ключевой вывод `noSmallAC0Solver` и стандартные
  конструктивные интерфейсы:
  * явный witness `Y` (без `False.elim`-экстракции),
  * testset-incompatibility в форме «из данных `Y, T` следует `False`».
  В доказательствах используется только факт, что решатель совпадает с
  языком Partial MCSP на всех входах.
-/

/--
  Generic counting-core contradiction:
  from AC0 witness for a family `F` and a large-cardinality lower bound on `F`
  we derive inconsistency with the capacity upper bound.
-/
theorem noSmallAC0Solver_partial_of_family_card
    {p : GapPartialMCSPParams} (solver : SmallAC0Solver_Partial p)
    {F : Family solver.params.ac0.n}
    (hF : ThirdPartyFacts.AC0FamilyWitnessProp solver.params.ac0 F)
    (hCardLower : Nat.pow 2 (Nat.pow 2 solver.params.ac0.n) ≤ F.toFinset.card) :
    False := by
  classical
  let pack :=
    scenarioFromAC0
      (params := solver.params.ac0) (F := F) (hF := hF)
  let sc := pack.2
  let bound := Nat.pow 2 (ThirdPartyFacts.ac0DepthBound_strong solver.params.ac0)
  have hsummary :=
    scenarioFromAC0_stepAB_summary_strong
      (params := solver.params.ac0) (F := F) (hF := hF)
  dsimp [pack, sc, bound] at hsummary
  rcases hsummary with ⟨hfamily, hk, hdict, _hε0, _hε1, hεInv, hcap_le⟩
  set N := Nat.pow 2 solver.params.ac0.n
  set t := N / (solver.params.ac0.n + 2)
  have hU :
      Counting.unionBound (Counting.dictLen sc.atlas.dict) sc.k
        ≤ Nat.pow 2 t := by
    have hmono_left :
        Counting.unionBound (Counting.dictLen sc.atlas.dict) sc.k
          ≤ Counting.unionBound bound sc.k :=
      Counting.unionBound_mono_left (k := sc.k) hdict
    have hmono_right :
        Counting.unionBound bound sc.k ≤ Counting.unionBound bound bound :=
      Counting.unionBound_mono_right (D := bound) hk
    have hchain := le_trans hmono_left hmono_right
    simpa [t] using (le_trans hchain solver.params.union_small)
  have hε0' : (0 : Rat) ≤ (1 : Rat) / (solver.params.ac0.n + 2) := by
    have hden : (0 : Rat) ≤ solver.params.ac0.n + 2 := by
      nlinarith
    exact one_div_nonneg.mpr hden
  have hε1' : (1 : Rat) / (solver.params.ac0.n + 2) ≤ (1 : Rat) / 2 := by
    have hden : (2 : Rat) ≤ solver.params.ac0.n + 2 := by
      nlinarith
    have hpos : (0 : Rat) < (2 : Rat) := by
      nlinarith
    exact one_div_le_one_div_of_le hpos hden
  have hcap_le' :
      Counting.capacityBound (Counting.dictLen sc.atlas.dict) sc.k N
        sc.atlas.epsilon sc.hε0 sc.hε1
        ≤ Counting.capacityBound (Counting.dictLen sc.atlas.dict) sc.k N
          ((1 : Rat) / (solver.params.ac0.n + 2)) hε0' hε1' := by
    exact Counting.capacityBound_mono
      (h0 := sc.hε0) (h1 := sc.hε1)
      (h0' := hε0') (h1' := hε1')
      (hD := le_rfl) (hk := le_rfl) hεInv
  have hcap_lt :
      Counting.capacityBound (Counting.dictLen sc.atlas.dict) sc.k N
        ((1 : Rat) / (solver.params.ac0.n + 2)) hε0' hε1'
        < Nat.pow 2 N := by
    have hn : 8 ≤ solver.params.ac0.n := by
      have hpow :=
        Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) p.n_large
      have hpow' : Nat.pow 2 8 ≤ partialInputLen p := by
        have hmul : Nat.pow 2 8 ≤ Nat.pow 2 p.n * 2 := by
          exact le_trans hpow (Nat.le_mul_of_pos_right _ (by decide))
        simpa [Partial.inputLen, Partial.tableLen, Nat.mul_comm, Nat.mul_left_comm,
          Nat.mul_assoc] using hmul
      have h8 : 8 ≤ Nat.pow 2 8 := by decide
      have h8' : 8 ≤ partialInputLen p := by
        exact le_trans h8 hpow'
      simpa [solver.params.same_n] using h8'
    simpa [N, t] using
      (Counting.capacityBound_twoPow_lt_twoPowPow
        (n := solver.params.ac0.n)
        (D := Counting.dictLen sc.atlas.dict)
        (k := sc.k)
        (hn := hn)
        (hε0 := hε0') (hε1 := hε1')
        (hU := hU))
  have hcard_ge : Nat.pow 2 N ≤ (familyFinset sc).card := by
    have hfinset : familyFinset sc = F.toFinset := by
      calc
        familyFinset sc = sc.family.toFinset := rfl
        _ = F.toFinset := by rw [hfamily]
    have hCardLowerN : Nat.pow 2 N ≤ F.toFinset.card := by
      simpa [N] using hCardLower
    simpa [hfinset] using hCardLowerN
  have hcap_le_final :
      (familyFinset sc).card ≤
        Counting.capacityBound (Counting.dictLen sc.atlas.dict) sc.k N
          ((1 : Rat) / (solver.params.ac0.n + 2)) hε0' hε1' := by
    exact hcap_le.trans hcap_le'
  have hpow_le_cap : Nat.pow 2 N ≤
      Counting.capacityBound (Counting.dictLen sc.atlas.dict) sc.k N
        ((1 : Rat) / (solver.params.ac0.n + 2)) hε0' hε1' := by
    exact le_trans hcard_ge hcap_le_final
  exact (Nat.lt_irrefl (Nat.pow 2 N)) (lt_of_le_of_lt hpow_le_cap hcap_lt)

/-- Syntactic AC0-easy predicate for one Boolean function. -/
def IsAC0SyntacticEasyFunc
    (params : ThirdPartyFacts.AC0Parameters)
    (f : Core.BitVec params.n → Bool) : Prop :=
  ∃ c : ThirdPartyFacts.AC0Circuit params,
    ThirdPartyFacts.AC0Circuit.depth c ≤ params.d ∧
    ThirdPartyFacts.AC0Circuit.size c ≤ params.M ∧
    ThirdPartyFacts.AC0Circuit.Computes c f

/-- Finite set of all syntactically AC0-easy functions (at fixed `params`). -/
noncomputable def ac0SyntacticEasyFunctionsFinset
    (params : ThirdPartyFacts.AC0Parameters) :
    Finset (Core.BitVec params.n → Bool) := by
  classical
  exact (Finset.univ : Finset (Core.BitVec params.n → Bool)).filter
    (fun f => IsAC0SyntacticEasyFunc params f)

/-- Family view of `ac0SyntacticEasyFunctionsFinset`. -/
noncomputable def AC0SyntacticEasyFamily
    (params : ThirdPartyFacts.AC0Parameters) : Family params.n :=
  (ac0SyntacticEasyFunctionsFinset params).toList

@[simp] lemma AC0SyntacticEasyFamily_toFinset
    (params : ThirdPartyFacts.AC0Parameters) :
    (AC0SyntacticEasyFamily params).toFinset =
      ac0SyntacticEasyFunctionsFinset params := by
  classical
  simp [AC0SyntacticEasyFamily]

/--
Any family equipped with an AC0 witness is pointwise contained in the
syntactic AC0-easy family.
-/
lemma family_subset_ac0SyntacticEasy_of_witness
    (params : ThirdPartyFacts.AC0Parameters)
    (F : Family params.n)
    (hF : ThirdPartyFacts.AC0FamilyWitnessProp params F) :
    F.toFinset ⊆ ac0SyntacticEasyFunctionsFinset params := by
  classical
  intro f hfmem
  have hw : ThirdPartyFacts.AC0FamilyWitness params F := Classical.choice hF
  rcases hw.covers f (by simpa using hfmem) with ⟨c, hc, hcomp⟩
  have hEasy : IsAC0SyntacticEasyFunc params f := by
    refine ⟨c, hw.depth_le c hc, hw.size_le c hc, hcomp⟩
  have hmem_univ : f ∈ (Finset.univ : Finset (Core.BitVec params.n → Bool)) := by
    simp
  change f ∈ (Finset.univ.filter (fun g => IsAC0SyntacticEasyFunc params g))
  exact Finset.mem_filter.mpr ⟨hmem_univ, hEasy⟩

/-- Concrete easy family used by the current Step-C route. -/
noncomputable def AC0EasyFamily (params : ThirdPartyFacts.AC0Parameters) :
    Family params.n :=
  AC0SyntacticEasyFamily params

/--
Compression Hypothesis (core hardness-magnification interface):
if a small AC0 solver exists for Partial MCSP at parameter `p`, then the
syntactic AC0 easy family is large enough to contain all Boolean functions.
-/
def AC0CompressionHypothesis (p : GapPartialMCSPParams) : Prop :=
  ∀ solver : SmallAC0Solver_Partial p,
    Nat.pow 2 (Nat.pow 2 solver.params.ac0.n) ≤
      (AC0EasyFamily solver.params.ac0).toFinset.card

/--
Easy-family AC0 witness hypothesis: each small AC0 solver has an AC0 witness
for the syntactic easy family at its parameters.
-/
def EasyFunctionsAC0Witness (p : GapPartialMCSPParams) : Prop :=
  ∀ solver : SmallAC0Solver_Partial p,
    ThirdPartyFacts.AC0FamilyWitnessProp solver.params.ac0
      (AC0EasyFamily solver.params.ac0)

/--
Cardinal lower bound for `AC0EasyFamily` derived from an all-functions AC0
witness.
-/
lemma ac0EasyFamily_card_lower_of_allWitness
    (params : ThirdPartyFacts.AC0Parameters)
    (hAll : ThirdPartyFacts.AC0FamilyWitnessProp params
      (Counting.allFunctionsFamily params.n)) :
    Nat.pow 2 (Nat.pow 2 params.n) ≤ (AC0EasyFamily params).toFinset.card := by
  classical
  have hsubset :
      (Counting.allFunctionsFamily params.n).toFinset ⊆
        ac0SyntacticEasyFunctionsFinset params :=
    family_subset_ac0SyntacticEasy_of_witness
      (params := params)
      (F := Counting.allFunctionsFamily params.n)
      hAll
  have hcard_le :
      (Counting.allFunctionsFamily params.n).toFinset.card ≤
        (ac0SyntacticEasyFunctionsFinset params).card :=
    Finset.card_le_card hsubset
  have hcard_all :
      (Counting.allFunctionsFamily params.n).toFinset.card =
        Nat.pow 2 (Nat.pow 2 params.n) := by
    simp [Counting.allFunctionsFamily_toFinset]
  have hpow_le :
      Nat.pow 2 (Nat.pow 2 params.n) ≤
        (ac0SyntacticEasyFunctionsFinset params).card := by
    simpa [hcard_all] using hcard_le
  simpa [AC0EasyFamily, AC0SyntacticEasyFamily_toFinset] using hpow_le

/--
Build an AC0 witness for `AC0EasyFamily` from an all-functions AC0 witness.
-/
lemma ac0EasyFamily_witness_of_allWitness
    (params : ThirdPartyFacts.AC0Parameters)
    (hAll : ThirdPartyFacts.AC0FamilyWitnessProp params
      (Counting.allFunctionsFamily params.n)) :
    ThirdPartyFacts.AC0FamilyWitnessProp params (AC0EasyFamily params) := by
  classical
  refine ⟨?_⟩
  let wAll : ThirdPartyFacts.AC0FamilyWitness params (Counting.allFunctionsFamily params.n) :=
    Classical.choice hAll
  refine
    { circuits := wAll.circuits
      covers := ?_
      depth_le := wAll.depth_le
      size_le := wAll.size_le
      circuits_length_le := wAll.circuits_length_le }
  intro f _hfEasy
  have hfAll : f ∈ Counting.allFunctionsFamily params.n := by
    simp [Counting.allFunctionsFamily]
  exact wAll.covers f hfAll

/-- Build family-level Step-C data from an all-functions AC0 witness. -/
noncomputable def ac0EasyFamilyData_of_witness
    (params : ThirdPartyFacts.AC0Parameters)
    (hAll : ThirdPartyFacts.AC0FamilyWitnessProp params
      (Counting.allFunctionsFamily params.n)) :
    AC0EasyFamilyDataPartial params where
  F := AC0EasyFamily params
  witness := ac0EasyFamily_witness_of_allWitness params hAll
  card_lower := ac0EasyFamily_card_lower_of_allWitness params hAll

/--
Syntactic easy-family package directly from easy-family hypotheses
(no `allFunctionsFamily` argument).
-/
noncomputable def ac0EasyFamilyData_of_syntacticHypotheses
    (params : ThirdPartyFacts.AC0Parameters)
    (hEasy : ThirdPartyFacts.AC0FamilyWitnessProp params (AC0EasyFamily params))
    (hCard : Nat.pow 2 (Nat.pow 2 params.n) ≤ (AC0EasyFamily params).toFinset.card) :
    AC0EasyFamilyDataPartial params where
  F := AC0EasyFamily params
  witness := hEasy
  card_lower := hCard

/-- Contradiction from packaged easy-family data. -/
theorem noSmallAC0Solver_partial_of_easyFamilyData
    {p : GapPartialMCSPParams} (solver : SmallAC0Solver_Partial p)
    (easy : AC0EasyFamilyDataPartial solver.params.ac0) : False := by
  exact noSmallAC0Solver_partial_of_family_card
    (solver := solver)
    (F := easy.F)
    (hF := easy.witness)
    (hCardLower := easy.card_lower)

/--
Constructive non-vacuous Step-C core:
any solver that already carries its family-level easy-data package yields
an immediate contradiction.
-/
theorem noConstructiveSmallAC0Solver_partial
    {p : GapPartialMCSPParams}
    (solver : ConstructiveSmallAC0Solver_Partial p) : False := by
  exact noSmallAC0Solver_partial_of_easyFamilyData
    (solver := solver.toSmallAC0Solver_Partial)
    (easy := solver.easyData)

/--
Build a constructive solver package from a concrete solver, the compression
hypothesis, and an easy-family AC0 witness for this solver.
-/
noncomputable def constructiveSmallAC0Solver_of_hypotheses
    {p : GapPartialMCSPParams}
    (solver : SmallAC0Solver_Partial p)
    (hComp : AC0CompressionHypothesis p)
    (hEasy :
      ThirdPartyFacts.AC0FamilyWitnessProp solver.params.ac0
        (AC0EasyFamily solver.params.ac0)) :
    ConstructiveSmallAC0Solver_Partial p :=
  { toSmallAC0Solver_Partial := solver
    easyData := ac0EasyFamilyData_of_syntacticHypotheses
      solver.params.ac0 hEasy (hComp solver) }

/--
Builder variant that consumes the global easy-family witness hypothesis.
-/
noncomputable def constructiveSmallAC0Solver_of_globalHypotheses
    {p : GapPartialMCSPParams}
    (solver : SmallAC0Solver_Partial p)
    (hComp : AC0CompressionHypothesis p)
    (hEasyAll : EasyFunctionsAC0Witness p) :
    ConstructiveSmallAC0Solver_Partial p :=
  constructiveSmallAC0Solver_of_hypotheses
    (solver := solver) (hComp := hComp) (hEasy := hEasyAll solver)

/--
Contradiction from direct syntactic easy-family hypotheses.
-/
theorem noSmallAC0Solver_partial_of_syntacticEasy
    {p : GapPartialMCSPParams} (solver : SmallAC0Solver_Partial p)
    (hEasy :
      ThirdPartyFacts.AC0FamilyWitnessProp solver.params.ac0
        (AC0EasyFamily solver.params.ac0))
    (hComp : AC0CompressionHypothesis p) : False := by
  exact noSmallAC0Solver_partial_of_easyFamilyData
    (solver := solver)
    (easy := ac0EasyFamilyData_of_syntacticHypotheses
      solver.params.ac0 hEasy (hComp solver))

/--
  Основное противоречие: если существует малый AC⁰-решатель Partial MCSP,
  то это нарушает ограничение ёмкости SAL-сценария.
-/
theorem noSmallAC0Solver_partial
    {p : GapPartialMCSPParams} (solver : SmallAC0Solver_Partial p)
    (hF : ThirdPartyFacts.AC0FamilyWitnessProp solver.params.ac0
      (Counting.allFunctionsFamily solver.params.ac0.n)) : False := by
  exact noSmallAC0Solver_partial_of_easyFamilyData
    (solver := solver)
    (easy := ac0EasyFamilyData_of_witness solver.params.ac0 hF)

/--
Constructive variant: contradiction from an explicit multi-switching witness
for the all-functions family.
-/
theorem noSmallAC0Solver_partial_of_multiSwitching
    {p : GapPartialMCSPParams} (solver : SmallAC0Solver_Partial p)
    (hMS :
      ThirdPartyFacts.AC0MultiSwitchingWitness solver.params.ac0
        (Counting.allFunctionsFamily solver.params.ac0.n)) : False := by
  exact
    noSmallAC0Solver_partial (solver := solver)
      (hF := ⟨hMS.base⟩)

/--
Typeclass-driven constructive variant: witness is supplied by instance search.
-/
theorem noSmallAC0Solver_partial_of_multiSwitching_provider
    {p : GapPartialMCSPParams} (solver : SmallAC0Solver_Partial p)
    [hMS :
      ThirdPartyFacts.AC0MultiSwitchingWitnessProvider
        solver.params.ac0
        (Counting.allFunctionsFamily solver.params.ac0.n)] : False := by
  exact noSmallAC0Solver_partial_of_multiSwitching
    (solver := solver) hMS.witness

/--
Default constructive variant specialized to all-functions witness packages.
-/
theorem noSmallAC0Solver_partial_of_default_multiSwitching
    {p : GapPartialMCSPParams} (solver : SmallAC0Solver_Partial p)
    [hMS : AllFunctionsAC0MultiSwitchingWitness solver.params.ac0] : False := by
  exact noSmallAC0Solver_partial_of_multiSwitching
    (solver := solver) hMS.witness

/--
Constructive large-`Y` witness on AC0 input length (`ac0.n`).

This theorem builds the witness package directly from the SAL scenario and
capacity-gap estimates, without extracting data from `False.elim`.
-/
theorem antiChecker_exists_large_Y_partial_core
    {p : GapPartialMCSPParams} (solver : SmallAC0Solver_Partial p)
    (hAll : ThirdPartyFacts.AC0FamilyWitnessProp solver.params.ac0
      (Counting.allFunctionsFamily solver.params.ac0.n)) :
    ∃ (F : Family solver.params.ac0.n)
      (Y : Finset (Core.BitVec solver.params.ac0.n → Bool)),
      ∃ hF : ThirdPartyFacts.AC0FamilyWitnessProp solver.params.ac0 F,
        let sc := (scenarioFromAC0 (params := solver.params.ac0) (F := F) (hF := hF)).2
        Y ⊆ familyFinset (sc := sc) ∧ scenarioCapacity (sc := sc) < Y.card := by
  classical
  let F : Family solver.params.ac0.n := Counting.allFunctionsFamily solver.params.ac0.n
  let pack := scenarioFromAC0 (params := solver.params.ac0) (F := F) (hF := hAll)
  let sc := pack.2
  refine ⟨F, familyFinset sc, hAll, ?_⟩
  constructor
  · intro f hf
    exact hf
  ·
    let bound := Nat.pow 2 (ThirdPartyFacts.ac0DepthBound_strong solver.params.ac0)
    have hsummary :=
      scenarioFromAC0_stepAB_summary_strong
        (params := solver.params.ac0) (F := F) (hF := hAll)
    dsimp [pack, sc, bound] at hsummary
    rcases hsummary with ⟨hfamily, hk, hdict, _hε0, _hε1, hεInv, hcap_le⟩
    set N := Nat.pow 2 solver.params.ac0.n
    set t := N / (solver.params.ac0.n + 2)
    have hU :
        Counting.unionBound (Counting.dictLen sc.atlas.dict) sc.k ≤ Nat.pow 2 t := by
      have hmono_left :
          Counting.unionBound (Counting.dictLen sc.atlas.dict) sc.k ≤
            Counting.unionBound bound sc.k :=
        Counting.unionBound_mono_left (k := sc.k) hdict
      have hmono_right :
          Counting.unionBound bound sc.k ≤ Counting.unionBound bound bound :=
        Counting.unionBound_mono_right (D := bound) hk
      have hchain := le_trans hmono_left hmono_right
      simpa [t] using (le_trans hchain solver.params.union_small)
    have hε0' : (0 : Rat) ≤ (1 : Rat) / (solver.params.ac0.n + 2) := by
      have hden : (0 : Rat) ≤ solver.params.ac0.n + 2 := by nlinarith
      exact one_div_nonneg.mpr hden
    have hε1' : (1 : Rat) / (solver.params.ac0.n + 2) ≤ (1 : Rat) / 2 := by
      have hden : (2 : Rat) ≤ solver.params.ac0.n + 2 := by nlinarith
      have hpos : (0 : Rat) < (2 : Rat) := by nlinarith
      exact one_div_le_one_div_of_le hpos hden
    have hcap_le' :
        Counting.capacityBound (Counting.dictLen sc.atlas.dict) sc.k N
          sc.atlas.epsilon sc.hε0 sc.hε1
          ≤ Counting.capacityBound (Counting.dictLen sc.atlas.dict) sc.k N
              ((1 : Rat) / (solver.params.ac0.n + 2)) hε0' hε1' := by
      exact Counting.capacityBound_mono
        (h0 := sc.hε0) (h1 := sc.hε1)
        (h0' := hε0') (h1' := hε1')
        (hD := le_rfl) (hk := le_rfl) hεInv
    have hcap_lt :
        Counting.capacityBound (Counting.dictLen sc.atlas.dict) sc.k N
          ((1 : Rat) / (solver.params.ac0.n + 2)) hε0' hε1' < Nat.pow 2 N := by
      have hn : 8 ≤ solver.params.ac0.n := by
        have hpow := Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) p.n_large
        have hpow' : Nat.pow 2 8 ≤ partialInputLen p := by
          have hmul : Nat.pow 2 8 ≤ Nat.pow 2 p.n * 2 := by
            exact le_trans hpow (Nat.le_mul_of_pos_right _ (by decide))
          simpa [Partial.inputLen, Partial.tableLen, Nat.mul_comm, Nat.mul_left_comm,
            Nat.mul_assoc] using hmul
        have h8 : 8 ≤ Nat.pow 2 8 := by decide
        have h8' : 8 ≤ partialInputLen p := le_trans h8 hpow'
        simpa [solver.params.same_n] using h8'
      simpa [N, t] using
        (Counting.capacityBound_twoPow_lt_twoPowPow
          (n := solver.params.ac0.n)
          (D := Counting.dictLen sc.atlas.dict)
          (k := sc.k)
          (hn := hn)
          (hε0 := hε0') (hε1 := hε1')
          (hU := hU))
    have hcard : (familyFinset sc).card = Nat.pow 2 N := by
      have hfinset : familyFinset sc = Counting.allFunctionsFinset solver.params.ac0.n := by
        calc
          familyFinset sc = sc.family.toFinset := rfl
          _ = F.toFinset := by rw [hfamily]
          _ = Counting.allFunctionsFinset solver.params.ac0.n := by simp [F]
      simp [N, hfinset]
    have hScLe :
        scenarioCapacity (sc := sc) ≤
          Counting.capacityBound (Counting.dictLen sc.atlas.dict) sc.k N
            ((1 : Rat) / (solver.params.ac0.n + 2)) hε0' hε1' := by
      simpa [scenarioCapacity, N] using hcap_le'
    have hltPow : scenarioCapacity (sc := sc) < Nat.pow 2 N :=
      lt_of_le_of_lt hScLe hcap_lt
    rw [hcard]
    exact hltPow

/--
  **Anti-Checker (large Y) для Partial MCSP.**
  Из `noSmallAC0Solver_partial` получаем существование `Y`.
-/
theorem antiChecker_exists_large_Y_partial
  {p : GapPartialMCSPParams} (solver : SmallAC0Solver_Partial p)
  (hAll : ThirdPartyFacts.AC0FamilyWitnessProp solver.params.ac0
    (Counting.allFunctionsFamily solver.params.ac0.n)) :
  ∃ (F : Family solver.params.ac0.n)
    (Y : Finset (Core.BitVec solver.params.ac0.n → Bool)),
    ∃ hF : ThirdPartyFacts.AC0FamilyWitnessProp solver.params.ac0 F,
      let scWitness :=
        (scenarioFromAC0
            (params := solver.params.ac0) (F := F) (hF := hF)).2
      Y ⊆ familyFinset (sc := scWitness) ∧
        scenarioCapacity (sc := scWitness) < Y.card := by
  exact antiChecker_exists_large_Y_partial_core (solver := solver) hAll

/--
  Конструктивная testset-версия anti-checker для Partial MCSP:
  явный testset-свидетель приводит к противоречию через `Covering-Power`.
-/
theorem antiChecker_exists_testset_partial
  {p : GapPartialMCSPParams} (solver : SmallAC0Solver_Partial p)
  (hAll : ThirdPartyFacts.AC0FamilyWitnessProp solver.params.ac0
    (Counting.allFunctionsFamily solver.params.ac0.n))
  (Ysolver : Finset (Core.BitVec solver.params.ac0.n → Bool))
  (Tsolver : Finset (Core.BitVec solver.params.ac0.n)) :
  let Fsolver : Family solver.params.ac0.n :=
    Counting.allFunctionsFamily solver.params.ac0.n
  let scWitness :=
    (scenarioFromAC0
        (params := solver.params.ac0) (F := Fsolver) (hF := hAll)).2
  Ysolver ⊆ familyFinset (sc := scWitness) →
  Tsolver.card ≤ Models.polylogBudget solver.params.ac0.n →
  (∀ f ∈ Ysolver,
    f ∈ Counting.ApproxOnTestset
      (R := scWitness.atlas.dict) (k := scWitness.k) (T := Tsolver)) →
  Counting.unionBound
      (Counting.dictLen scWitness.atlas.dict)
      scWitness.k
      * 2 ^ Tsolver.card
    < Ysolver.card →
  False := by
  classical
  intro Fsolver scWitness hSubset _hTcard hApprox hLarge
  exact
    no_bounded_atlas_on_testset_of_large_family
      (sc := scWitness)
      (T := Tsolver)
      (Y := Ysolver)
      hSubset
      hApprox
      hLarge

/-!
  ### Локальные схемы: partial‑версия античекера
-/

theorem noSmallLocalCircuitSolver_partial
    {p : GapPartialMCSPParams} (solver : SmallLocalCircuitSolver_Partial p)
    (hF : ThirdPartyFacts.LocalCircuitFamilyWitnessProp solver.params.params
      (Counting.allFunctionsFamily solver.params.params.n)) : False := by
  classical
  let F : Family solver.params.params.n :=
    Counting.allFunctionsFamily solver.params.params.n
  let pack := scenarioFromLocalCircuit (params := solver.params.params) (F := F) (hF := hF)
  let sc := pack.2
  let bound := Nat.pow 2
    (solver.params.params.ℓ *
      (Nat.log2 (solver.params.params.M + 2) + solver.params.params.depth + 1))
  have hsummary :=
    scenarioFromLocalCircuit_stepAB_summary
      (params := solver.params.params) (F := F) (hF := hF)
  dsimp [pack, sc, bound] at hsummary
  rcases hsummary with ⟨hfamily, hk, hdict, hε0, hε1, hεInv, hcap_le⟩
  set N := Nat.pow 2 solver.params.params.n
  set t := N / (solver.params.params.n + 2)
  have hbound_le_half : bound ≤ Nat.pow 2 (solver.params.params.n / 2) := by
    exact Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) solver.params.small
  have hU :
      Counting.unionBound (Counting.dictLen sc.atlas.dict) sc.k
        ≤ Nat.pow 2 t := by
    have hmono_left :
        Counting.unionBound (Counting.dictLen sc.atlas.dict) sc.k
          ≤ Counting.unionBound bound sc.k :=
      Counting.unionBound_mono_left (k := sc.k) hdict
    have hmono_right :
        Counting.unionBound bound sc.k ≤ Counting.unionBound bound bound :=
      Counting.unionBound_mono_right (D := bound) hk
    have hchain := le_trans hmono_left hmono_right
    have hpow_union : Counting.unionBound bound bound ≤ Nat.pow 2 bound :=
      Counting.unionBound_le_pow bound bound
    have hchain' := le_trans hchain hpow_union
    have h16 : 16 ≤ solver.params.params.n := by
      have hpow :=
        Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) p.n_large
      have hpow' : Nat.pow 2 8 ≤ solver.params.params.n := by
        have hmul : Nat.pow 2 8 ≤ Nat.pow 2 p.n * 2 := by
          exact le_trans hpow (Nat.le_mul_of_pos_right _ (by decide))
        simpa [Partial.inputLen, Partial.tableLen, solver.params.same_n, Nat.mul_comm,
          Nat.mul_left_comm, Nat.mul_assoc] using hmul
      have h16' : 16 ≤ Nat.pow 2 8 := by decide
      exact le_trans h16' hpow'
    have hhalf_le :
        Nat.pow 2 (solver.params.params.n / 2) ≤
          Nat.pow 2 solver.params.params.n / (solver.params.params.n + 2) :=
      twoPow_half_le_div solver.params.params.n h16
    have hbound_le :
        bound ≤ Nat.pow 2 solver.params.params.n / (solver.params.params.n + 2) :=
      le_trans hbound_le_half hhalf_le
    have hpow_le :
        Nat.pow 2 bound ≤
          Nat.pow 2 (Nat.pow 2 solver.params.params.n / (solver.params.params.n + 2)) :=
      Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hbound_le
    simpa [t] using (le_trans hchain' hpow_le)
  have hε0' : (0 : Rat) ≤ (1 : Rat) / (solver.params.params.n + 2) := by
    nlinarith
  have hε1' : (1 : Rat) / (solver.params.params.n + 2) ≤ (1 : Rat) / 2 := by
    have hden : (2 : Rat) ≤ solver.params.params.n + 2 := by
      nlinarith
    have hpos : (0 : Rat) < (2 : Rat) := by
      nlinarith
    exact one_div_le_one_div_of_le hpos hden
  have hcap_le' :
      Counting.capacityBound (Counting.dictLen sc.atlas.dict) sc.k N
        sc.atlas.epsilon sc.hε0 sc.hε1
        ≤ Counting.capacityBound (Counting.dictLen sc.atlas.dict) sc.k N
          ((1 : Rat) / (solver.params.params.n + 2)) hε0' hε1' := by
    exact Counting.capacityBound_mono
      (h0 := sc.hε0) (h1 := sc.hε1)
      (h0' := hε0') (h1' := hε1')
      (hD := le_rfl) (hk := le_rfl) hεInv
  have hcap_lt :
      Counting.capacityBound (Counting.dictLen sc.atlas.dict) sc.k N
        ((1 : Rat) / (solver.params.params.n + 2)) hε0' hε1'
        < Nat.pow 2 N := by
    have h8 : 8 ≤ solver.params.params.n := by
      have hpow :=
        Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) p.n_large
      have hpow' : Nat.pow 2 8 ≤ solver.params.params.n := by
        have hmul : Nat.pow 2 8 ≤ Nat.pow 2 p.n * 2 := by
          exact le_trans hpow (Nat.le_mul_of_pos_right _ (by decide))
        simpa [Partial.inputLen, Partial.tableLen, solver.params.same_n, Nat.mul_comm,
          Nat.mul_left_comm, Nat.mul_assoc] using hmul
      have h8' : 8 ≤ Nat.pow 2 8 := by decide
      exact le_trans h8' hpow'
    simpa [N, t] using
      (Counting.capacityBound_twoPow_lt_twoPowPow
        (n := solver.params.params.n)
        (D := Counting.dictLen sc.atlas.dict)
        (k := sc.k)
        (hn := h8)
        (hε0 := hε0') (hε1 := hε1')
        (hU := hU))
  have hcard :
      (familyFinset sc).card = Nat.pow 2 N := by
    have hfamily' : sc.family = F := hfamily
    have hfinset :
        familyFinset sc = Counting.allFunctionsFinset solver.params.params.n := by
      simp [familyFinset, hfamily', F, Counting.allFunctionsFamily_toFinset]
    simp [N, hfinset]
  have hcap_le_final :
      (familyFinset sc).card ≤
        Counting.capacityBound (Counting.dictLen sc.atlas.dict) sc.k N
          ((1 : Rat) / (solver.params.params.n + 2)) hε0' hε1' := by
    exact hcap_le.trans hcap_le'
  have hcontr := lt_of_le_of_lt hcap_le_final hcap_lt
  have hcontr' : False := by
    simp [hcard] at hcontr
  exact hcontr'

/--
Constructive variant: direct contradiction from solver locality, with no
family-witness assumption.
-/
theorem noSmallLocalCircuitSolver_partial_constructive
    {p : GapPartialMCSPParams} (solver : SmallLocalCircuitSolver_Partial p) :
    False := by
  obtain ⟨alive, h_small, h_local⟩ := solver.decideLocal
  exact no_local_function_solves_mcsp
    solver.decide alive h_small h_local solver.correct

/--
Constructive large-`Y` witness on local-solver input length (`params.n`).

This local analogue avoids `False.elim` by constructing witnesses directly
from the scenario/capacity chain used in `noSmallLocalCircuitSolver_partial`.
-/
theorem antiChecker_exists_large_Y_local_partial_core
    {p : GapPartialMCSPParams} (solver : SmallLocalCircuitSolver_Partial p)
    (hAll : ThirdPartyFacts.LocalCircuitFamilyWitnessProp solver.params.params
      (Counting.allFunctionsFamily solver.params.params.n)) :
    ∃ (F : Family solver.params.params.n)
      (Y : Finset (Core.BitVec solver.params.params.n → Bool)),
      ∃ hF : ThirdPartyFacts.LocalCircuitFamilyWitnessProp solver.params.params F,
        let sc := (scenarioFromLocalCircuit (params := solver.params.params) (F := F) (hF := hF)).2
        Y ⊆ familyFinset (sc := sc) ∧ scenarioCapacity (sc := sc) < Y.card := by
  classical
  let F : Family solver.params.params.n := Counting.allFunctionsFamily solver.params.params.n
  let pack := scenarioFromLocalCircuit (params := solver.params.params) (F := F) (hF := hAll)
  let sc := pack.2
  refine ⟨F, familyFinset sc, hAll, ?_⟩
  constructor
  · intro f hf
    exact hf
  ·
    let bound := Nat.pow 2
      (solver.params.params.ℓ *
        (Nat.log2 (solver.params.params.M + 2) + solver.params.params.depth + 1))
    have hsummary :=
      scenarioFromLocalCircuit_stepAB_summary
        (params := solver.params.params) (F := F) (hF := hAll)
    dsimp [pack, sc, bound] at hsummary
    rcases hsummary with ⟨hfamily, hk, hdict, _hε0, _hε1, hεInv, hcap_le⟩
    set N := Nat.pow 2 solver.params.params.n
    set t := N / (solver.params.params.n + 2)
    have hbound_le_half : bound ≤ Nat.pow 2 (solver.params.params.n / 2) := by
      exact Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) solver.params.small
    have hU :
        Counting.unionBound (Counting.dictLen sc.atlas.dict) sc.k ≤ Nat.pow 2 t := by
      have hmono_left :
          Counting.unionBound (Counting.dictLen sc.atlas.dict) sc.k ≤
            Counting.unionBound bound sc.k :=
        Counting.unionBound_mono_left (k := sc.k) hdict
      have hmono_right :
          Counting.unionBound bound sc.k ≤ Counting.unionBound bound bound :=
        Counting.unionBound_mono_right (D := bound) hk
      have hchain := le_trans hmono_left hmono_right
      have hpow_union : Counting.unionBound bound bound ≤ Nat.pow 2 bound :=
        Counting.unionBound_le_pow bound bound
      have hchain' := le_trans hchain hpow_union
      have h16 : 16 ≤ solver.params.params.n := by
        have hpow := Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) p.n_large
        have hpow' : Nat.pow 2 8 ≤ solver.params.params.n := by
          have hmul : Nat.pow 2 8 ≤ Nat.pow 2 p.n * 2 := by
            exact le_trans hpow (Nat.le_mul_of_pos_right _ (by decide))
          simpa [Partial.inputLen, Partial.tableLen, solver.params.same_n, Nat.mul_comm,
            Nat.mul_left_comm, Nat.mul_assoc] using hmul
        have h16' : 16 ≤ Nat.pow 2 8 := by decide
        exact le_trans h16' hpow'
      have hhalf_le :
          Nat.pow 2 (solver.params.params.n / 2) ≤
            Nat.pow 2 solver.params.params.n / (solver.params.params.n + 2) :=
        twoPow_half_le_div solver.params.params.n h16
      have hbound_le :
          bound ≤ Nat.pow 2 solver.params.params.n / (solver.params.params.n + 2) :=
        le_trans hbound_le_half hhalf_le
      have hpow_le :
          Nat.pow 2 bound ≤
            Nat.pow 2 (Nat.pow 2 solver.params.params.n / (solver.params.params.n + 2)) :=
        Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hbound_le
      simpa [t] using (le_trans hchain' hpow_le)
    have hε0' : (0 : Rat) ≤ (1 : Rat) / (solver.params.params.n + 2) := by
      nlinarith
    have hε1' : (1 : Rat) / (solver.params.params.n + 2) ≤ (1 : Rat) / 2 := by
      have hden : (2 : Rat) ≤ solver.params.params.n + 2 := by nlinarith
      have hpos : (0 : Rat) < (2 : Rat) := by nlinarith
      exact one_div_le_one_div_of_le hpos hden
    have hcap_le' :
        Counting.capacityBound (Counting.dictLen sc.atlas.dict) sc.k N
          sc.atlas.epsilon sc.hε0 sc.hε1
          ≤ Counting.capacityBound (Counting.dictLen sc.atlas.dict) sc.k N
            ((1 : Rat) / (solver.params.params.n + 2)) hε0' hε1' := by
      exact Counting.capacityBound_mono
        (h0 := sc.hε0) (h1 := sc.hε1)
        (h0' := hε0') (h1' := hε1')
        (hD := le_rfl) (hk := le_rfl) hεInv
    have hcap_lt :
        Counting.capacityBound (Counting.dictLen sc.atlas.dict) sc.k N
          ((1 : Rat) / (solver.params.params.n + 2)) hε0' hε1' < Nat.pow 2 N := by
      have h8 : 8 ≤ solver.params.params.n := by
        have hpow := Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) p.n_large
        have hpow' : Nat.pow 2 8 ≤ solver.params.params.n := by
          have hmul : Nat.pow 2 8 ≤ Nat.pow 2 p.n * 2 := by
            exact le_trans hpow (Nat.le_mul_of_pos_right _ (by decide))
          simpa [Partial.inputLen, Partial.tableLen, solver.params.same_n, Nat.mul_comm,
            Nat.mul_left_comm, Nat.mul_assoc] using hmul
        have h8' : 8 ≤ Nat.pow 2 8 := by decide
        exact le_trans h8' hpow'
      simpa [N, t] using
        (Counting.capacityBound_twoPow_lt_twoPowPow
          (n := solver.params.params.n)
          (D := Counting.dictLen sc.atlas.dict)
          (k := sc.k)
          (hn := h8)
          (hε0 := hε0') (hε1 := hε1')
          (hU := hU))
    have hcard : (familyFinset sc).card = Nat.pow 2 N := by
      have hfinset : familyFinset sc = Counting.allFunctionsFinset solver.params.params.n := by
        calc
          familyFinset sc = sc.family.toFinset := rfl
          _ = F.toFinset := by rw [hfamily]
          _ = Counting.allFunctionsFinset solver.params.params.n := by simp [F]
      simp [N, hfinset]
    have hScLe :
        scenarioCapacity (sc := sc) ≤
          Counting.capacityBound (Counting.dictLen sc.atlas.dict) sc.k N
            ((1 : Rat) / (solver.params.params.n + 2)) hε0' hε1' := by
      simpa [scenarioCapacity, N] using hcap_le'
    have hltPow : scenarioCapacity (sc := sc) < Nat.pow 2 N :=
      lt_of_le_of_lt hScLe hcap_lt
    rw [hcard]
    exact hltPow

theorem antiChecker_exists_large_Y_local_partial
  {p : GapPartialMCSPParams} (solver : SmallLocalCircuitSolver_Partial p)
  (hAll : ThirdPartyFacts.LocalCircuitFamilyWitnessProp solver.params.params
    (Counting.allFunctionsFamily solver.params.params.n)) :
  ∃ (F : Family solver.params.params.n)
    (Y : Finset (Core.BitVec solver.params.params.n → Bool)),
    ∃ hF : ThirdPartyFacts.LocalCircuitFamilyWitnessProp solver.params.params F,
      let scWitness :=
        (scenarioFromLocalCircuit
            (params := solver.params.params) (F := F) (hF := hF)).2
      Y ⊆ familyFinset (sc := scWitness) ∧
        scenarioCapacity (sc := scWitness) < Y.card := by
  exact antiChecker_exists_large_Y_local_partial_core (solver := solver) hAll

/--
Constructive variant with no external witness assumptions: uses solver
locality contradiction directly.
-/
theorem antiChecker_exists_large_Y_local_partial_constructive
  {p : GapPartialMCSPParams} (solver : SmallLocalCircuitSolver_Partial p)
  (hAll : ThirdPartyFacts.LocalCircuitFamilyWitnessProp solver.params.params
    (Counting.allFunctionsFamily solver.params.params.n)) :
  ∃ (F : Family solver.params.params.n)
    (Y : Finset (Core.BitVec solver.params.params.n → Bool)),
    ∃ hF : ThirdPartyFacts.LocalCircuitFamilyWitnessProp solver.params.params F,
      let scWitness :=
        (scenarioFromLocalCircuit
            (params := solver.params.params) (F := F) (hF := hF)).2
      Y ⊆ familyFinset (sc := scWitness) ∧
        scenarioCapacity (sc := scWitness) < Y.card := by
  exact antiChecker_exists_large_Y_local_partial (solver := solver) hAll

theorem antiChecker_exists_testset_local_partial
  {p : GapPartialMCSPParams} (solver : SmallLocalCircuitSolver_Partial p)
  (hAll : ThirdPartyFacts.LocalCircuitFamilyWitnessProp solver.params.params
    (Counting.allFunctionsFamily solver.params.params.n))
  (Ysolver : Finset (Core.BitVec solver.params.params.n → Bool))
  (Tsolver : Finset (Core.BitVec solver.params.params.n)) :
  let Fsolver : Family solver.params.params.n :=
    Counting.allFunctionsFamily solver.params.params.n
  let scWitness :=
    (scenarioFromLocalCircuit
        (params := solver.params.params) (F := Fsolver) (hF := hAll)).2
  Ysolver ⊆ familyFinset (sc := scWitness) →
  Tsolver.card ≤ Models.polylogBudget solver.params.params.n →
  (∀ f ∈ Ysolver,
    f ∈ Counting.ApproxOnTestset
      (R := scWitness.atlas.dict) (k := scWitness.k) (T := Tsolver)) →
  Counting.unionBound
      (Counting.dictLen scWitness.atlas.dict)
      scWitness.k
      * 2 ^ Tsolver.card
    < Ysolver.card →
  False := by
  classical
  intro Fsolver scWitness hSubset _hTcard hApprox hLarge
  exact
    no_bounded_atlas_on_testset_of_large_family
      (sc := scWitness)
      (T := Tsolver)
      (Y := Ysolver)
      hSubset
      hApprox
      hLarge

/--
Constructive variant with no external witness assumptions: uses the
constructive large-`Y` local anti-checker.
-/
theorem antiChecker_exists_testset_local_partial_constructive
  {p : GapPartialMCSPParams} (solver : SmallLocalCircuitSolver_Partial p)
  (hAll : ThirdPartyFacts.LocalCircuitFamilyWitnessProp solver.params.params
    (Counting.allFunctionsFamily solver.params.params.n))
  (Ysolver : Finset (Core.BitVec solver.params.params.n → Bool))
  (Tsolver : Finset (Core.BitVec solver.params.params.n)) :
  let Fsolver : Family solver.params.params.n :=
    Counting.allFunctionsFamily solver.params.params.n
  let scWitness :=
    (scenarioFromLocalCircuit
        (params := solver.params.params) (F := Fsolver) (hF := hAll)).2
  Ysolver ⊆ familyFinset (sc := scWitness) →
  Tsolver.card ≤ Models.polylogBudget solver.params.params.n →
  (∀ f ∈ Ysolver,
    f ∈ Counting.ApproxOnTestset
      (R := scWitness.atlas.dict) (k := scWitness.k) (T := Tsolver)) →
  Counting.unionBound
      (Counting.dictLen scWitness.atlas.dict)
      scWitness.k
      * 2 ^ Tsolver.card
    < Ysolver.card →
  False := by
  intro
  exact antiChecker_exists_testset_local_partial (solver := solver) hAll Ysolver Tsolver

/-!
  ### Комбинаторная версия «случайной» леммы

  В TODO требовалась вероятностная формулировка: случайная partial‑таблица
  редко согласуется с малой схемой.  Мы фиксируем эквивалентную
  counting‑форму: если число функций «малого» класса ограничено, то
  существует partial‑таблица, не согласованная ни с одной из них.
-/

/--
Комбинаторный аналог вероятностной леммы:
если семейство `F` достаточно мало (по явной оценке `|F| * 2^(2^n) < 3^(2^n)`),
то существует partial‑таблица, не согласованная ни с одним `f ∈ F`.

Это именно тот факт, который в probabilistic proof формулируется как
«случайная таблица с высокой вероятностью противоречит каждому малому решателю».
-/
lemma exists_partial_not_consistent_with_family {n : Nat} (F : Finset (TotalTable n))
    (hsmall : F.card * 2 ^ (2 ^ n) < 3 ^ (2 ^ n)) :
    ∃ T : PartialTable n, ∀ f ∈ F, ¬ consistentWithTotal T f := by
  -- Из комбинаторной оценки получаем hard‑таблицу.
  rcases exists_hard_if_card_lt (F := F) hsmall with ⟨T, hmem, hnot⟩
  refine ⟨T, ?_⟩
  -- Hard‑таблица не согласована ни с одним `f ∈ F`.
  exact hard_not_consistent (F := F) (h := ⟨hmem, hnot⟩)

/-- Версия с `Partial.tableLen` вместо `2^n`. -/
lemma exists_partial_not_consistent_with_family_tableLen {n : Nat}
    (F : Finset (TotalTable n))
    (hsmall : F.card * 2 ^ Partial.tableLen n < 3 ^ Partial.tableLen n) :
    ∃ T : PartialTable n, ∀ f ∈ F, ¬ consistentWithTotal T f := by
  have hsmall' : F.card * 2 ^ (2 ^ n) < 3 ^ (2 ^ n) := by
    simpa [Partial.tableLen] using hsmall
  exact exists_partial_not_consistent_with_family (F := F) hsmall'

/-!
  TODO (следующие шаги):

  1. Аналог `antiChecker_exists_large_Y` для Partial MCSP.
  2. Связка с shrinkage/switching и перенос на magnification.
-/

/-!
  ### Solver locality

  The `decideLocal` field of `SmallLocalCircuitSolver_Partial` directly
  witnesses that the decision function depends on at most `tableLen / 2`
  of its input coordinates.  This locality proof is provided during
  construction (via the P/poly → locality axiom and the locality lift).

  `solver_is_local` is a trivial extraction of the `decideLocal` field.
-/

theorem solver_is_local {p : GapPartialMCSPParams}
    (solver : SmallLocalCircuitSolver_Partial p) :
    ∃ (alive : Finset (Fin (partialInputLen p))),
      alive.card ≤ Partial.tableLen p.n / 2 ∧
      ∀ x y : Core.BitVec (partialInputLen p),
        (∀ i ∈ alive, x i = y i) → solver.decide x = solver.decide y :=
  solver.decideLocal

/-!
  ### New anti-checker via solver locality + MCSP gap

  This theorem replaces the counting-against-family approach with a
  direct argument: multi-switching makes the solver local, and no
  local function can solve MCSP. Unlike the old approach, this
  actually uses `solver.correct`.
-/

/--
  Anti-checker: any small local-circuit solver for Partial MCSP
  leads to a contradiction.

  Proof outline:
  1. `solver.decideLocal` gives a set `alive` with `|alive| ≤ tableLen/2`
     such that `solver.decide` depends only on positions in `alive`.
  2. `no_local_function_solves_mcsp` shows that no such local function
     can satisfy the MCSP promise.
-/
theorem noSmallLocalCircuitSolver_partial_v2
    {p : GapPartialMCSPParams} (solver : SmallLocalCircuitSolver_Partial p) :
    False := by
  obtain ⟨alive, h_small, h_local⟩ := solver_is_local solver
  exact no_local_function_solves_mcsp
    solver.decide alive h_small h_local solver.correct

end LowerBounds
end Pnp3
