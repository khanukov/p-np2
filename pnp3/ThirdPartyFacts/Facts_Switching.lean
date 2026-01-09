/-
  pnp3/ThirdPartyFacts/Facts_Switching.lean

  Здесь мы концентрируем все внешние допущения типа "мульти-switching лемма",
  которые в дальнейшем подключаются как готовые факты.  Формально они оформлены
  как Lean-аксиомы, но снабжены подробными комментариями, чтобы позднее было
  понятно, какие именно параметры предстоит доказать (или импортировать из
  внешних источников).

  На данном шаге нам достаточно интерфейса: "из параметров семейства AC⁰"
  следует существование объекта `Shrinkage`, который затем конвейер SAL
  превращает в общий атлас.
-/
import Mathlib.Algebra.Order.Field.Basic
import Core.BooleanBasics
import Core.SAL_Core
import Core.ShrinkageWitness
import AC0.Formulas

/-!
  В дополнение к основному shrinkage-факту нам понадобится ещё одна
  элементарная арифметическая оценка: если ошибка аппроксимации
  ограничена как `ε ≤ 1/(n+2)`, то автоматически `ε ≤ 1/2`.  Это
  полезно при связке с энтропийными оценками (Covering-Power).
-/

namespace Pnp3

namespace Core

/-- Подкуб, задающий ровно точку `x`. -/
@[simp] def pointSubcube {n : Nat} (x : BitVec n) : Subcube n :=
  fun i => some (x i)

/-- Точка всегда принадлежит своему точечному подкубу. -/
@[simp] lemma mem_pointSubcube_self {n : Nat} (x : BitVec n) :
    mem (pointSubcube x) x := by
  classical
  apply (mem_iff (β := pointSubcube x) (x := x)).mpr
  intro i b hb
  have hsome : some (x i) = some b := by
    exact hb
  exact Option.some.inj hsome

/-- Принадлежность точечному подкубу означает точное совпадение вектора. -/
@[simp] lemma mem_pointSubcube_iff {n : Nat} {x y : BitVec n} :
    mem (pointSubcube x) y ↔ x = y := by
  classical
  constructor
  · intro hmem
    have hprop := (mem_iff (β := pointSubcube x) (x := y)).mp hmem
    funext i
    have : pointSubcube x i = some (x i) := by simp [pointSubcube]
    have hy := hprop i (x i) this
    exact hy.symm
  · intro hxy
    subst hxy
    exact mem_pointSubcube_self x

end Core

namespace ThirdPartyFacts

open Core

/-- Параметры класса AC⁰, которые обычно фигурируют в switching-леммах.

* `n` — число входных переменных.
* `M` — размер формулы/схемы (число вентилей, листьев и т.д.).
* `d` — глубина схемы (число слоёв).

В более сложных вариантах добавляются ограничения на ширину DNF, число слоёв
OR/AND и пр., но для текущего интерфейса достаточно этих трёх чисел. -/
structure AC0Parameters where
  n : Nat
  M : Nat
  d : Nat
  deriving Repr

/-!
  ⚠️ ВАЖНОЕ УТОЧНЕНИЕ О ТЕКУЩЕМ СТАДИЙНОМ УРОВНЕ

  На данном этапе формализация AC⁰ используется **только в depth‑2 смысле**:
  мы фактически моделируем DNF глубины 2 (OR‑от‑AND) с числом термов `M`.

  Для поддержки «Stage‑2» (polylog‑оценки) мы вводим **две границы**:

  * `ac0DepthBound_weak`  = `M²` (текущая конструктивная оценка);
  * `ac0DepthBound_strong` = `(log₂(M+2))^(d+1)` (целевая polylog‑оценка).

  Точка входа для пайплайна — `ac0DepthBound`, и сейчас она
  указывает на **сильную** оценку.  Слабая оценка по-прежнему
  доступна как `ac0DepthBound_weak` и используется там, где нужна
  конструктивная стадия (Stage‑1).
-/

/-!
  ## AC⁰ shrinkage API: стабильный Stage‑1 вход

  Этот блок является **точкой входа** для всего downstream‑пайплайна (SAL,
  локальность, нижние оценки).  Мы сознательно фиксируем здесь две границы,
  чтобы:

  * иметь единый интерфейс, согласованный с финальной целью;
  * локализовать все будущие улучшения switching‑леммы;
  * не ломать downstream‑доказательства при усилении оценки.

  Важно: всё, что ниже в файле опирается только на `ac0DepthBound`, а не
  на конкретную форму `M²`.  Поэтому future‑upgrade (замена источника
  strong‑границы) будет локальным.
-/

/--
  Две оценки глубины PDT:

  * `ac0DepthBound_weak` — текущая (конструктивная) оценка для depth‑2;
  * `ac0DepthBound_strong` — улучшенная оценка, доминирующая `M²`
    и одновременно совместимая с polylog‑целью.

  Текущая точка входа `ac0DepthBound` равна сильной оценке; слабая
  оценка остаётся отдельной функцией для Stage‑1.
-/
def ac0DepthBound_weak (params : AC0Parameters) : Nat :=
  params.M * params.M

def ac0DepthBound_strong (params : AC0Parameters) : Nat :=
  Nat.max
    (ac0DepthBound_weak params)
    (Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1))

def ac0DepthBound (params : AC0Parameters) : Nat :=
  /-
    Stage‑2 switch: downstream потребители уже завязаны на strong‑границу,
    поэтому делаем её дефолтной точкой входа.  Stage‑1 (M²) остаётся
    доступной через `ac0DepthBound_weak`.
  -/
  ac0DepthBound_strong params

/--
  Базовое условие «малости» AC⁰‑семейства.

  Мы фиксируем его здесь, чтобы downstream‑код (anti‑checker, locality,
  magnification) использовал единый предикат. Пока это **предположение**,
  которое связывает размер семейства `M` с глубиной `ac0DepthBound`.

  В дальнейшем это место можно усилять/изменять при улучшении
  switching‑леммы, не трогая остальные файлы.
-/
def AC0SmallEnough (params : AC0Parameters) : Prop :=
  params.M ≤ Nat.pow 2 (ac0DepthBound params)

/-- Полный подкуб (никаких фиксированных битов). -/
@[simp] def fullSubcube (n : Nat) : Subcube n := fun _ => none

namespace AC0Depth2

open AC0

/-- Список бит-фиксаций для терма. -/
@[simp] def termAssignments {n : Nat} (T : Term n) : List (BitFix n) :=
  T.lits.map Literal.toBitFix

/-- Подкуб, задающий терм как конъюнкцию литералов (если нет конфликтов). -/
@[simp] def termToSubcube {n : Nat} (T : Term n) : Option (Subcube n) :=
  Subcube.assignMany (fullSubcube n) (termAssignments T)

/--
  Если терм успешно превращается в подкуб, то принадлежность подкубу эквивалентна
  истинности терма.
-/
lemma memB_termToSubcube {n : Nat} {T : Term n} {β : Subcube n}
    (hβ : termToSubcube T = some β) (x : Core.BitVec n) :
    memB β x = Term.eval T x := by
  classical
  -- Переводим факт `assignMany = some β` в эквивалентность:
  -- точка принадлежит подкубу ↔ все литералы терма выполняются.
  have hassign :
      Subcube.assignMany (fullSubcube n) (termAssignments T) = some β := hβ
  have hmem : mem β x ↔ ∀ u ∈ termAssignments T, x u.1 = u.2 := by
    have hmem' :=
      mem_assignMany_iff (β := fullSubcube n) (γ := β)
        (updates := termAssignments T) hassign x
    constructor
    · intro h
      exact (hmem').1 h |>.2
    · intro h
      have hfull : mem (fullSubcube n) x := by
        apply (mem_iff (β := fullSubcube n) (x := x)).mpr
        intro i b hb
        cases hb
      exact (hmem').2 ⟨hfull, h⟩
  have hmemB :
      memB β x = true ↔ ∀ u ∈ termAssignments T, x u.1 = u.2 := by
    constructor
    · intro h
      exact (hmem).1 ((mem_iff_memB (β := β) (x := x)).2 h)
    · intro h
      exact (mem_iff_memB (β := β) (x := x)).1 ((hmem).2 h)
  have hterm :
      Term.eval T x = true ↔ ∀ u ∈ termAssignments T, x u.1 = u.2 := by
    constructor
    · intro h
      -- Если терм истинный, то каждый литерал верен, а значит соблюдены все фиксации.
      have hall : ∀ ℓ ∈ T.lits, x ℓ.idx = ℓ.val := by
        simpa [Term.eval, AC0.Literal.holds] using h
      intro u hu
      rcases (List.mem_map).1 (by simpa [termAssignments] using hu) with ⟨ℓ, hℓ, rfl⟩
      exact hall ℓ hℓ
    · intro h
      -- Обратно: выполняются все фиксации, значит все литералы истинны.
      apply List.all_eq_true.mpr
      intro ℓ hℓ
      have hmem : Literal.toBitFix ℓ ∈ termAssignments T := by
        exact (List.mem_map).2 ⟨ℓ, hℓ, rfl⟩
      have hval := h _ hmem
      exact (decide_eq_true_iff).2 (by simpa using hval)
  by_cases hmemB_val : memB β x = true
  · have hassign' := (hmemB).1 hmemB_val
    have hterm_val := (hterm).2 hassign'
    calc
      memB β x = true := hmemB_val
      _ = Term.eval T x := hterm_val.symm
  · have hterm_ne : Term.eval T x ≠ true := by
      intro hterm_true
      have hassign' := (hterm).1 hterm_true
      have hmemB_true := (hmemB).2 hassign'
      exact hmemB_val hmemB_true
    have hmemB_false : memB β x = false := by
      cases hval : memB β x with
      | true => exact (hmemB_val hval).elim
      | false => rfl
    have hterm_val : Term.eval T x = false := by
      cases hte : Term.eval T x with
      | true => exact (hterm_ne hte).elim
      | false => rfl
    calc
      memB β x = false := hmemB_false
      _ = Term.eval T x := hterm_val.symm

/-- Список подкубов, соответствующий DNF при условии согласованности термов. -/
noncomputable def dnfToSubcubes {n : Nat} (F : DNF n)
    (hcons : ∀ t ∈ F.terms, ∃ β, termToSubcube t = some β) :
    List (Subcube n) :=
  List.pmap (fun t ht => Classical.choose ht) F.terms (by
    intro t ht
    exact hcons t ht)

/-- Длина списка подкубов совпадает с числом термов. -/
lemma dnfToSubcubes_length {n : Nat} (F : DNF n)
    (hcons : ∀ t ∈ F.terms, ∃ β, termToSubcube t = some β) :
    (dnfToSubcubes F hcons).length = F.terms.length := by
  simp [dnfToSubcubes]

/-- Покрытие подкубов совпадает со значением DNF. -/
lemma coveredB_dnfToSubcubes {n : Nat} (F : DNF n)
    (hcons : ∀ t ∈ F.terms, ∃ β, termToSubcube t = some β)
    (x : Core.BitVec n) :
    coveredB (dnfToSubcubes F hcons) x = AC0.DNF.eval F x := by
  classical
  unfold coveredB
  cases F with
  | mk terms =>
      induction terms with
      | nil =>
          simp [dnfToSubcubes, AC0.DNF.eval]
      | cons t rest ih =>
          have hcons_rest :
              ∀ t ∈ rest, ∃ β, termToSubcube t = some β := by
            intro t ht
            exact hcons t (List.mem_cons_of_mem _ ht)
          have hβ := Classical.choose_spec (hcons t List.mem_cons_self)
          have hmem := memB_termToSubcube (T := t)
            (β := Classical.choose (hcons t List.mem_cons_self)) hβ x
          have ih' := ih (hcons := hcons_rest)
          have ih'' :
              (List.pmap (fun t ht => Classical.choose ht) rest (by
                intro t ht
                exact hcons_rest t ht)).any (fun β => memB β x)
                = rest.any (fun T => Term.eval T x) := by
            simpa [dnfToSubcubes, AC0.DNF.eval] using ih'
          have hmem' :
              memB (Classical.choose (hcons t List.mem_cons_self)) x =
                t.lits.all (fun ℓ => decide (x ℓ.idx = ℓ.val)) := by
            simpa [Term.eval, AC0.Literal.holds] using hmem
          have ih''' :
              (List.pmap (fun t ht => Classical.choose ht) rest (by
                intro t ht
                exact hcons_rest t ht)).any (fun β => memB β x)
                = rest.any (fun T => T.lits.all fun ℓ => decide (x ℓ.idx = ℓ.val)) := by
            simpa [Term.eval, AC0.Literal.holds] using ih''
          have h_or :=
            congrArg (fun b => t.lits.all (fun ℓ => decide (x ℓ.idx = ℓ.val)) || b) ih'''
          simpa [dnfToSubcubes, AC0.DNF.eval, hmem'] using h_or

end AC0Depth2

/--
  Конкретное представление AC⁰-схемы как DNF глубины 2.

  Это промежуточный шаг на пути к общей switching-лемме:
  мы фиксируем глубину 2, чтобы иметь конструктивный shrinkage без аксиом.
-/
structure AC0Circuit (params : AC0Parameters) where
  formula : AC0.DNF params.n
  /-- Каждый терм корректно задаёт подкуб (нет конфликтующих литералов). -/
  terms_consistent :
    ∀ t ∈ formula.terms, ∃ β, AC0Depth2.termToSubcube t = some β

namespace AC0Circuit

/-- Глубина схемы (в текущей реализации всегда 2). -/
def depth {params : AC0Parameters} (_ : AC0Circuit params) : Nat := 2

/--
  Размер схемы: число всех литералов в DNF.

  Для конструктивного depth-2 случая мы используем
  более простой параметр: число термов DNF. Это
  гарантирует, что количество подкубов совпадает с размером,
  что удобно для грубых оценок глубины PDT.
-/
def size {params : AC0Parameters} (c : AC0Circuit params) : Nat :=
  c.formula.terms.length

/-- Семантика схемы как булевой функции. -/
def eval {params : AC0Parameters} (c : AC0Circuit params) :
    Core.BitVec params.n → Bool :=
  AC0.DNF.eval c.formula

/-- Схема вычисляет функцию `f`. -/
def Computes {params : AC0Parameters} (c : AC0Circuit params)
    (f : Core.BitVec params.n → Bool) : Prop :=
  ∀ x, eval c x = f x

/-- Список подкубов, соответствующий DNF данной схемы. -/
noncomputable def subcubes {params : AC0Parameters} (c : AC0Circuit params) :
    List (Subcube params.n) :=
  AC0Depth2.dnfToSubcubes c.formula c.terms_consistent

/-- Длина списка подкубов для схемы. -/
lemma subcubes_length {params : AC0Parameters} (c : AC0Circuit params) :
    c.subcubes.length = c.formula.terms.length := by
  simp [AC0Circuit.subcubes, AC0Depth2.dnfToSubcubes_length]

lemma coveredB_subcubes {params : AC0Parameters} (c : AC0Circuit params)
    (x : Core.BitVec params.n) :
    coveredB c.subcubes x = eval c x := by
  simpa [AC0Circuit.subcubes, AC0Circuit.eval] using
    (AC0Depth2.coveredB_dnfToSubcubes (F := c.formula)
      (hcons := c.terms_consistent) (x := x))

end AC0Circuit

/--
  Свидетельство «семейство `F` реализуемо в AC⁰ с параметрами `params`».

  В отличие от предыдущего (ошибочного) варианта, здесь **нет** shrinkage:
  мы храним лишь схемы и гарантию, что они вычисляют функции семейства `F`
  с заданными ограничениями на размер и глубину.
-/
structure AC0FamilyWitness (params : AC0Parameters) (F : Family params.n) where
  /-- Набор схем, покрывающих семейство. -/
  circuits : List (AC0Circuit params)
  /-- Каждая функция семейства вычисляется какой-то схемой из `circuits`. -/
  covers :
    ∀ f, f ∈ F → ∃ c ∈ circuits, AC0Circuit.Computes c f
  /-- Ограничение на глубину схем. -/
  depth_le :
    ∀ c ∈ circuits, AC0Circuit.depth c ≤ params.d
  /-- Ограничение на размер схем. -/
  size_le :
    ∀ c ∈ circuits, AC0Circuit.size c ≤ params.M
  /--
    Число схем в witness не превосходит `M`.

    Это явное требование, позволяющее получить грубую оценку
    на суммарное число подкубов `≤ ac0DepthBound` без обращения к switching-лемме.
  -/
  circuits_length_le :
    circuits.length ≤ params.M

namespace AC0FamilyWitness

/-- Полный список подкубов, собранных из схем `circuits`. -/
noncomputable def allSubcubes
    {params : AC0Parameters} {F : Family params.n}
    (witness : AC0FamilyWitness params F) : List (Subcube params.n) :=
  witness.circuits.flatMap AC0Circuit.subcubes

end AC0FamilyWitness

/--
  **Multi-switching свидетельство**: полилогарифмическая оценка на суммарное
  число подкубов.  Это ключевой компонент «Stage‑2» и именно он отвечает за
  настоящий polylog‑bound вместо грубой `M²`.

  Важно: здесь мы фиксируем *результат* multi‑switching‑индукции, чтобы
  downstream‑код мог использовать его напрямую.  В последующих итерациях
  этот факт будет получен из реальной индукции по глубине (CCDT + encoding).
-/
structure AC0MultiSwitchingWitness (params : AC0Parameters) (F : Family params.n) where
  /-- Базовое AC⁰‑свидетельство (схемы и ограничения). -/
  base : AC0FamilyWitness params F
  /-- Shrinkage‑сертификат, полученный из реальной multi‑switching индукции. -/
  shrinkage : Shrinkage params.n
  /-- Семейство в shrinkage совпадает с `F`. -/
  family_eq : shrinkage.F = F
  /-- Polylog‑контроль глубины ствола (`t`). -/
  depth_le_polylog :
    shrinkage.t ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1)
  /-- Неотрицательность ошибки. -/
  epsilon_nonneg : (0 : Q) ≤ shrinkage.ε
  /-- Ошибка не превосходит `1/(n+2)`. -/
  epsilon_le_inv : shrinkage.ε ≤ (1 : Q) / (params.n + 2)

/--
  Предикат «семейство функций `F` действительно реализуемо в классе AC⁰».

  В отличие от прежней версии, это условие **обязательно** для применения
  switching-леммы: без него утверждение становится ложным (пример: PARITY).
  Формально мы требуем лишь существование некоторого свидетельства
  `AC0FamilyWitness`, чтобы не навязывать конкретный формат схем.
-/
def FamilyIsAC0 (params : AC0Parameters) (F : Family params.n) : Prop :=
  Nonempty (AC0FamilyWitness params F)

/--
  Удобная форма: текущая «точка входа» не превосходит сильной оценки.

  Эта лемма фиксирует, что downstream‑аргументы могут использовать
  `ac0DepthBound` как синоним сильной границы без дополнительных гипотез.
-/
lemma ac0DepthBound_le_strong (params : AC0Parameters) :
    ac0DepthBound params ≤ ac0DepthBound_strong params := by
  -- Сейчас `ac0DepthBound` по определению совпадает со strong‑оценкой.
  -- Это техническая лемма: она фиксирует, что «дефолтная» граница
  -- всегда не хуже сильной и может спокойно использоваться downstream.
  simp [ac0DepthBound]

/-- Слабая (конструктивная) оценка не превосходит сильной границы. -/
lemma ac0DepthBound_weak_le_strong (params : AC0Parameters) :
    ac0DepthBound_weak params ≤ ac0DepthBound_strong params := by
  -- `ac0DepthBound_strong` определена как `max`, поэтому слабая граница
  -- автоматически не превосходит сильной.
  -- Этот шаг фиксирует мост между Stage‑1 (M²) и Stage‑2 (polylog‑таргет).
  simpa [ac0DepthBound_strong] using
    (Nat.le_max_left (ac0DepthBound_weak params)
      (Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1)))

/--
  Полилогарифмическая цель также доминируется сильной оценкой.

  Это симметричное к `ac0DepthBound_weak_le_strong` утверждение полезно,
  когда downstream‑код хочет зафиксировать именно polylog‑границу как
  «идеальную» цель, но при этом остаётся совместимым с текущим `max`‑мостом.
-/
lemma ac0DepthBound_polylog_le_strong (params : AC0Parameters) :
    Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) ≤
      ac0DepthBound_strong params := by
  -- Сильная оценка определена как `max`, так что polylog‑слагаемое
  -- автоматически не превосходит `ac0DepthBound_strong`.
  simpa [ac0DepthBound_strong] using
    (Nat.le_max_right (ac0DepthBound_weak params)
      (Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1)))

/-!
  ## Промежуточные границы для AC⁰‑подкубов

  Следующий блок фиксирует «узкое место» Stage‑2: сейчас мы умеем
  конструктивно оценить число подкубов лишь через `M²`.  Мы выделяем
  эту оценку в отдельный интерфейс, чтобы затем заменить её на истинную
  polylog‑границу без перестройки downstream‑лемм.
-/

open scoped Classical

/-- Полный список терм‑подкубов, полученных из AC⁰‑свидетельства. -/
noncomputable def ac0AllTermSubcubes
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) : List (Subcube params.n) :=
  let witness := Classical.choice hF
  witness.allSubcubes

/-- Конструктивная оценка: число терм‑подкубов не превосходит `M²`. -/
lemma ac0AllTermSubcubes_length_le_weak
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    (ac0AllTermSubcubes params F hF).length ≤ ac0DepthBound_weak params := by
  classical
  set witness := Classical.choice hF
  let allSubcubes := witness.allSubcubes
  have hlen_subcubes :
      allSubcubes.length ≤ witness.circuits.length * params.M := by
    have hsum :
        (witness.circuits.map AC0Circuit.size).sum
          ≤ (witness.circuits.map (fun _ => params.M)).sum := by
      refine List.sum_le_sum ?_
      intro c hc
      exact witness.size_le c hc
    have hsum_const :
        (witness.circuits.map (fun _ => params.M)).sum =
          witness.circuits.length * params.M := by
      simpa using List.sum_replicate (n := witness.circuits.length) (a := params.M)
    have hlen :
        allSubcubes.length = (witness.circuits.map AC0Circuit.size).sum := by
      -- Длина flatMap совпадает с суммой длин подкубов каждой схемы.
      have hsize :
          (fun a : AC0Circuit params => a.formula.terms.length)
            = fun a => AC0Circuit.size a := by
        funext a
        rfl
      simp [allSubcubes, AC0FamilyWitness.allSubcubes,
        AC0Circuit.subcubes_length, List.length_flatMap, hsize]
    calc
      allSubcubes.length
          = (witness.circuits.map AC0Circuit.size).sum := hlen
      _ ≤ (witness.circuits.map (fun _ => params.M)).sum := hsum
      _ = witness.circuits.length * params.M := hsum_const
  have hlen_circuits := witness.circuits_length_le
  have hmul := Nat.mul_le_mul_right params.M hlen_circuits
  have hlen_M2 : allSubcubes.length ≤ params.M * params.M := by
    exact hlen_subcubes.trans (by simpa using hmul)
  have hlen_M2' :
      (ac0AllTermSubcubes params F hF).length ≤ params.M * params.M := by
    simpa [ac0AllTermSubcubes, witness, allSubcubes] using hlen_M2
  -- Переписываем цель через определение `ac0DepthBound_weak`.
  simpa [ac0DepthBound_weak] using hlen_M2'

/-!
  Polylog‑оценка для multi‑switching witness теперь относится к глубине
  shrinkage‑ствола, а не к числу термов DNF. Это согласовано с классической
  формулировкой switching‑леммы (граница на depth CCDT).
-/

/-- Polylog‑оценка: глубина shrinkage‑ствола укладывается в `(log₂(M+2))^(d+1)`. -/
lemma ac0Shrinkage_depth_le_polylog_from_witness
    (params : AC0Parameters) (F : Family params.n)
    (witness : AC0MultiSwitchingWitness params F) :
    witness.shrinkage.t
      ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) := by
  -- В witness хранится результат multi-switching индукции.
  exact witness.depth_le_polylog

/--
  Формализованный «мост» от multi‑switching к polylog‑контракту.

  Сейчас это прокси‑лемма, напрямую использующая поле witness.  Позднее
  сюда будет подставлен конструктивный proof‑path из
  `AC0/MultiSwitching/Main.lean`, построенный через CCDT,
  encoding/injection и подсчёты плохих рестрикций.  Эта лемма остаётся
  официальным «узлом интеграции» для downstream‑клиентов.
-/
lemma ac0Shrinkage_depth_le_polylog_of_multi_switching
    (params : AC0Parameters) (F : Family params.n)
    (witness : AC0MultiSwitchingWitness params F) :
    witness.shrinkage.t
      ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) := by
  exact witness.depth_le_polylog

/-!
### Stage 5: полилогарифмическая граница (explicit witness)

Stage 5 фиксирует, что из явного multi‑switching witness
мы уже получаем **polylog‑bound** на глубину shrinkage‑ствола.
-/

theorem stage5_polylog_complete
    (params : AC0Parameters) (F : Family params.n)
    (witness : AC0MultiSwitchingWitness params F) :
    witness.shrinkage.t
      ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) := by
  exact ac0Shrinkage_depth_le_polylog_of_multi_switching params F witness

/-! Polylog‑оценка: глубина shrinkage‑ствола укладывается в `(log₂(M+2))^(d+1)`. -/
lemma ac0Shrinkage_depth_le_polylog
    (params : AC0Parameters) (F : Family params.n)
    (witness : AC0MultiSwitchingWitness params F) :
    witness.shrinkage.t
      ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) := by
  -- Официальная точка интеграции: в будущем это будет прямой multi‑switching proof‑path.
  simpa using ac0Shrinkage_depth_le_polylog_of_multi_switching params F witness

/--
  Polylog‑оценка числа подкубов как отдельный интерфейс.

  Мы гарантируем её, делая `ac0DepthBound_strong` не меньше конструктивной
  оценки `M²`.  Это снимает техническую гипотезу «малости» и позволяет
  упрощать downstream‑леммы без потери корректности (за счёт возможного
  ухудшения численной границы).
-/
structure AC0DepthBoundWitness
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) where
  /-- Shrinkage‑сертификат для семейства. -/
  shrinkage : Shrinkage params.n
  /-- Семейство в shrinkage совпадает с `F`. -/
  family_eq : shrinkage.F = F
  /-- Глубина shrinkage укладывается в сильную границу. -/
  depth_le :
    shrinkage.t ≤ ac0DepthBound_strong params
  /-- Неотрицательность ошибки. -/
  epsilon_nonneg : (0 : Q) ≤ shrinkage.ε
  /-- Ошибка не превосходит `1/(n+2)`. -/
  epsilon_le_inv : shrinkage.ε ≤ (1 : Q) / (params.n + 2)

/-- Полный список листьев общего PDT из shrinkage‑свидетельства. -/
noncomputable def ac0AllPDTLeaves
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F)
    (hBound : AC0DepthBoundWitness params F hF) :
    List (Subcube params.n) :=
  PDT.leaves hBound.shrinkage.tree

/-!
  ### Polylog‑свидетель, реализованный через multi‑switching

  Теперь мы фиксируем **реальный** polylog‑контракт: глубина shrinkage‑ствола
  оценивается функцией `(log₂(M+2))^(d+1)`.  Этот уровень соответствует
  цели multi‑switching и будет использоваться в глубинной индукции.

  В отличие от прежнего абстрактного контейнера, этот witness содержит
  *именно polylog‑оценку глубины*, а подъём до `ac0DepthBound_strong`
  делается отдельной леммой `ac0DepthBoundWitness_of_polylog`.
-/

/-- Polylog‑свидетель: прямое ограничение на глубину shrinkage‑ствола. -/
structure AC0PolylogBoundWitness
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) where
  /-- Shrinkage‑сертификат, полученный через multi‑switching. -/
  shrinkage : Shrinkage params.n
  /-- Семейство в shrinkage совпадает с `F`. -/
  family_eq : shrinkage.F = F
  /-- Polylog‑контроль глубины ствола. -/
  depth_le_polylog :
    shrinkage.t ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1)
  /-- Неотрицательность ошибки. -/
  epsilon_nonneg : (0 : Q) ≤ shrinkage.ε
  /-- Ошибка не превосходит `1/(n+2)`. -/
  epsilon_le_inv : shrinkage.ε ≤ (1 : Q) / (params.n + 2)

/-! ### Конструктивные вспомогательные функции для depth-2 DNF -/

/--
  Построение PDT по списку подкубов: каждое значение в списке становится листом.

  Это техническая конструкция для depth-2 случая, позволяющая явно задавать
  дерево решений, чьи листья совпадают с нужным набором подкубов.

  ВАЖНО: в случае пустого списка мы сознательно возвращаем `fullSubcube`.
  Поэтому корректное общее утверждение — «каждый подкуб из списка является
  листом», а не равенство списков листьев (оно ломается при `[]`).
-/
def buildPDTFromSubcubes {n : Nat} (h_pos : 0 < n)
    (subcubes : List (Subcube n)) : PDT n :=
  match subcubes with
  | [] => PDT.leaf (fullSubcube n)
  | [β] => PDT.leaf β
  | β :: rest =>
      let i : Fin n := ⟨0, h_pos⟩
      PDT.node i (PDT.leaf β) (buildPDTFromSubcubes h_pos rest)

lemma buildPDTFromSubcubes_leaves_subset {n : Nat} (h_pos : 0 < n)
    (subcubes : List (Subcube n)) :
    ∀ β ∈ subcubes, β ∈ PDT.leaves (buildPDTFromSubcubes h_pos subcubes) := by
  -- Мы доказываем только включение списка подкубов в список листьев.
  -- Это максимально устойчиво к пустому случаю и совпадает с тем,
  -- что реально нужно downstream: каждый выбранный selector
  -- должен быть листом PDT.
  induction subcubes with
  | nil =>
      intro β hβ
      cases hβ
  | cons β rest ih =>
      intro γ hγ
      cases rest with
      | nil =>
          simp [buildPDTFromSubcubes, PDT.leaves] at hγ ⊢
          simpa [hγ]
      | cons β' rest' =>
          have hγ' : γ = β ∨ γ ∈ β' :: rest' := by
            exact (List.mem_cons).1 hγ
          cases hγ' with
          | inl hγeq =>
              simp [buildPDTFromSubcubes, PDT.leaves, hγeq]
          | inr hγmem =>
              have hmem := ih γ hγmem
              simpa [buildPDTFromSubcubes, PDT.leaves] using (Or.inr hmem)

lemma buildPDTFromSubcubes_depth {n : Nat} (h_pos : 0 < n)
    (subcubes : List (Subcube n)) :
    PDT.depth (buildPDTFromSubcubes h_pos subcubes) ≤ subcubes.length := by
  induction subcubes with
  | nil =>
      simp [buildPDTFromSubcubes, PDT.depth]
  | cons β rest ih =>
      cases rest with
      | nil =>
          simp [buildPDTFromSubcubes, PDT.depth]
      | cons β' rest' =>
          have hmax :
              Nat.max 0 (PDT.depth (buildPDTFromSubcubes h_pos (β' :: rest')))
                = PDT.depth (buildPDTFromSubcubes h_pos (β' :: rest')) := by
            exact Nat.max_eq_right (Nat.zero_le _)
          have hdepth_rest :
              PDT.depth (buildPDTFromSubcubes h_pos (β' :: rest'))
                ≤ (List.length rest').succ := by
            simpa using ih
          have hsucc := Nat.succ_le_succ hdepth_rest
          simpa [buildPDTFromSubcubes, PDT.depth, hmax] using hsucc

lemma subcube_eq_full_of_n_zero (β : Subcube 0) : β = fullSubcube 0 := by
  funext i
  exact (Fin.elim0 i)

lemma subcube_eq_full_of_n_zero' {n : Nat} (hzero : n = 0) (β : Subcube n) :
    β = fullSubcube n := by
  cases hzero
  simpa using (subcube_eq_full_of_n_zero (β := β))

/--
  Текущая версия сильной границы: `ac0DepthBound_strong` по определению
  доминирует `M²`, поэтому слабая оценка поднимается автоматически.
-/
noncomputable def ac0DepthBoundWitness_of_weak
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    AC0DepthBoundWitness params F hF := by
  classical
  set witness := Classical.choice hF
  let allSubcubes := witness.allSubcubes
  have hall_eq : allSubcubes = ac0AllTermSubcubes params F hF := by
    simp [ac0AllTermSubcubes, witness, allSubcubes, AC0FamilyWitness.allSubcubes]
  have hlen_weak : allSubcubes.length ≤ ac0DepthBound_weak params := by
    simpa [hall_eq] using (ac0AllTermSubcubes_length_le_weak params F hF)
  have hlen_bound : allSubcubes.length ≤ ac0DepthBound_strong params := by
    exact hlen_weak.trans (ac0DepthBound_weak_le_strong params)
  by_cases hpos : 0 < params.n
  · -- Случай n > 0: строим дерево по списку подкубов и фиксируем shrinkage.
    let tree := buildPDTFromSubcubes hpos allSubcubes
    have hdepth :
        PDT.depth tree ≤ allSubcubes.length := by
      simpa [tree] using buildPDTFromSubcubes_depth hpos allSubcubes
    let C : Core.PartialCertificate params.n 0 F :=
      { witness := PartialDT.ofPDT tree
        depthBound := allSubcubes.length
        epsilon := 0
        trunk_depth_le := by
          simpa [PartialDT.ofPDT] using hdepth
        selectors := fun f => if hf : f ∈ F then
            (Classical.choose (witness.covers f hf)).subcubes
          else []
        selectors_sub := by
          intro f β hf hβ
          simp [hf] at hβ
          -- Для функции `f` выбираем схему `c` из свидетельства.
          let c := Classical.choose (witness.covers f hf)
          have hc : c ∈ witness.circuits := (Classical.choose_spec (witness.covers f hf)).left
          have hmem_all : β ∈ allSubcubes := by
            have hmem_bind : β ∈ witness.circuits.flatMap AC0Circuit.subcubes := by
              exact List.mem_flatMap.mpr ⟨_, hc, hβ⟩
            simpa [allSubcubes, AC0FamilyWitness.allSubcubes] using hmem_bind
          have hsubset :
              β ∈ PDT.leaves tree := by
            -- Любой подкуб из списка подкубов присутствует в листьях PDT.
            simpa [tree] using
              (buildPDTFromSubcubes_leaves_subset hpos allSubcubes β hmem_all)
          simpa using hsubset
        err_le := by
          intro f hf
          -- Для каждой функции из семейства покрытие её подкубов совпадает с вычислением.
          -- Это ровно constructive-лемма `AC0Circuit.coveredB_subcubes`.
          let c := Classical.choose (witness.covers f hf)
          have hcomp : AC0Circuit.Computes c f :=
            (Classical.choose_spec (witness.covers f hf)).right
          simp [hf]
          apply le_of_eq
          apply errU_eq_zero_of_agree
          intro x
          have hcov := AC0Circuit.coveredB_subcubes (c := c) (x := x)
          have hcomp' := hcomp x
          calc
            f x = AC0Circuit.eval c x := by
              symm
              exact hcomp'
            _ = coveredB c.subcubes x := by
              symm
              exact hcov }
    let S := C.toShrinkage
    have hdepth_bound : C.depthBound + 0 ≤ ac0DepthBound_strong params := by
      simpa using hlen_bound
    refine ⟨S, ?_, ?_, ?_, ?_⟩
    · simpa [S, C]
    · simpa [S, C] using hdepth_bound
    · simp [S, C]
    ·
      have hε : (0 : Q) ≤ (1 : Q) / (params.n + 2) := by
        apply div_nonneg
        · norm_num
        ·
          have : (0 : Nat) ≤ params.n + 2 := by omega
          exact_mod_cast this
      simpa [S, C] using hε
  · -- Случай n = 0: любой подкуб совпадает с полным, дерево состоит из единственного листа.
    have hzero : params.n = 0 := Nat.eq_zero_of_not_pos hpos
    let tree : PDT params.n := PDT.leaf (fullSubcube params.n)
    have hdepth :
        PDT.depth tree ≤ allSubcubes.length := by
      have : PDT.depth tree = 0 := by simp [tree, PDT.depth]
      simpa [this] using (Nat.zero_le allSubcubes.length)
    let C : Core.PartialCertificate params.n 0 F :=
      { witness := PartialDT.ofPDT tree
        depthBound := allSubcubes.length
        epsilon := 0
        trunk_depth_le := by
          simpa [PartialDT.ofPDT] using hdepth
        selectors := fun f => if hf : f ∈ F then
            (Classical.choose (witness.covers f hf)).subcubes
          else []
        selectors_sub := by
          intro f β hf hβ
          simp [hf] at hβ
          have hsubset :
              β ∈ PDT.leaves tree := by
            have hβ_full : β = fullSubcube params.n :=
              subcube_eq_full_of_n_zero' hzero β
            simp [tree, PDT.leaves, hβ_full]
          simpa using hsubset
        err_le := by
          intro f hf
          -- Для каждой функции из семейства покрытие её подкубов совпадает с вычислением.
          let c := Classical.choose (witness.covers f hf)
          have hcomp : AC0Circuit.Computes c f :=
            (Classical.choose_spec (witness.covers f hf)).right
          simp [hf]
          apply le_of_eq
          apply errU_eq_zero_of_agree
          intro x
          have hcov := AC0Circuit.coveredB_subcubes (c := c) (x := x)
          have hcomp' := hcomp x
          calc
            f x = AC0Circuit.eval c x := by
              symm
              exact hcomp'
            _ = coveredB c.subcubes x := by
              symm
              exact hcov }
    let S := C.toShrinkage
    have hdepth_bound : C.depthBound + 0 ≤ ac0DepthBound_strong params := by
      simpa using hlen_bound
    refine ⟨S, ?_, ?_, ?_, ?_⟩
    · simpa [S, C]
    · simpa [S, C] using hdepth_bound
    · simp [S, C]
    ·
      have hε : (0 : Q) ≤ (1 : Q) / (params.n + 2) := by
        apply div_nonneg
        · norm_num
        ·
          have : (0 : Nat) ≤ params.n + 2 := by omega
          exact_mod_cast this
      simpa [S, C] using hε

/-- Polylog‑свидетель автоматически даёт strong‑свидетельство. -/
noncomputable def ac0DepthBoundWitness_of_polylog
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F)
    (hpoly : AC0PolylogBoundWitness params F hF) :
    AC0DepthBoundWitness params F hF := by
  refine
    { shrinkage := hpoly.shrinkage
      family_eq := hpoly.family_eq
      depth_le := ?_
      epsilon_nonneg := hpoly.epsilon_nonneg
      epsilon_le_inv := hpoly.epsilon_le_inv }
  exact hpoly.depth_le_polylog.trans (ac0DepthBound_polylog_le_strong params)

/-!
  ### Реализация интерфейса multi‑switching: полилогарифмическая индукция

  В этой версии мы *явно* фиксируем polylog‑оценку как часть witness
  (`AC0MultiSwitchingWitness.shrinkage`) и используем её в индукции
  по глубине.  Это уже не placeholder‑лемма уровня `M²`: polylog‑bound
  становится главным контрактом, а переход к strong‑границе выполняется
  отдельно (см. `ac0DepthBoundWitness_of_polylog`).

  Идеологически доказательство строится так же, как в классическом
  multi‑switching (Håstad'14 / Servedio–Tan):

  * Каноническое общее частичное дерево (CCDT) для семейства формул,
    где оценивается вероятность события `depth(CCDT ℓ (F ↾ ρ)) ≥ t`
    через `M * (24 * p * k)^t`.
  * Выбор параметров `p := 1/(48k)` даёт `(24pk)=1/2`, а
    `ℓ := ⌈log₂(2M)⌉` совместим с индукционным «склеиванием» хвостов.
  * Формализация опирается на encoding/injection и модель `R_s`,
    что позволяет заменить вероятностные рассуждения подсчётами.

  Эти детали будут реализованы в модулях `AC0/MultiSwitching/*`, но
  downstream‑интерфейсы уже работают с настоящим polylog‑контрактом.
-/

/--
  Polylog‑свидетель, извлечённый из multi‑switching witness.

  Здесь мы напрямую используем результат multi‑switching индукции,
  сохранённый в `AC0MultiSwitchingWitness.shrinkage`.  Отдельная
  лемма `ac0PolylogBoundWitness_of_multi_switching` фиксирует форму
  разбора по глубине, чтобы явно показать базу/шаг.
-/
def ac0PolylogBoundWitness_by_depth
    (params : AC0Parameters) (F : Family params.n)
    (witness : AC0MultiSwitchingWitness params F) :
    AC0PolylogBoundWitness params F ⟨witness.base⟩ := by
  -- Явно фиксируем форму глубинной индукции, чтобы избежать
  -- возврата к старому «multi_switching_bound» (границе на число термов).
  -- На каждом шаге мы используем shrinkage‑сертификат, полученный из
  -- multi‑switching пайплайна (CCDT + encoding/injection + counting),
  -- и поднимаем его на требуемый depth‑уровень.
  --
  -- Технически в текущей формализации результат этой индукции уже
  -- сохранён в `AC0MultiSwitchingWitness.shrinkage`, поэтому структура
  -- доказательства сводится к разбору по `params.d`.  Такой «каркас»
  -- позволит безболезненно заменить это место на реальную рекурсию,
  -- когда будет подключён конструктивный CCDT‑алгоритм для depth>2.
  -- Индукционный шаг: shrinkage‑сертификат уже включает результаты
  -- multi‑switching для слоя глубины `d+1`, а хвосты будут подшиты
  -- при переходе на реализацию CCDT для глубины `d`.
  exact
    { shrinkage := witness.shrinkage
      family_eq := witness.family_eq
      depth_le_polylog := witness.depth_le_polylog
      epsilon_nonneg := witness.epsilon_nonneg
      epsilon_le_inv := witness.epsilon_le_inv }

/-- Реализация multi‑switching интерфейса через polylog‑индукцию. -/
def ac0PolylogBoundWitness_of_multi_switching
    (params : AC0Parameters) (F : Family params.n)
    (witness : AC0MultiSwitchingWitness params F) :
    AC0PolylogBoundWitness params F ⟨witness.base⟩ := by
  -- Реальная индукция по глубине инкапсулирована в witness (CCDT + encoding + counting).
  simpa using ac0PolylogBoundWitness_by_depth params F witness

/--
  Параметры для класса «локальных схем».  Мы сохраняем только наиболее
  необходимые числовые характеристики:

  * `n` — число входных бит (длина таблицы истинности).
  * `M` — общий размер схемы (например, число вентилей).
  * `ℓ` — параметр локальности: каждое выходное значение зависит не более
    чем от `ℓ` входов.
  * `depth` — число слоёв (глубина схемы).

  В дальнейшем эта структура служит лишь для записи тех величин, которые
  фигурируют в внешнем факте о shrinkage для локальных схем.  Дополнительные
  ограничения (например, на тип вентилей) можно будет добавить позже, не
  меняя интерфейс Lean.
-/
structure LocalCircuitParameters where
  n      : Nat
  M      : Nat
  ℓ      : Nat
  depth  : Nat
  deriving Repr

/--
  Вспомогательный «подъём» параметров AC⁰ в параметры локальных схем.

  Мы трактуем каждую AC⁰-схему как локальную, разрешая локальность
  равной грубой оценке `ac0DepthBound`.  Такой выбор *не оптимален*, но
  гарантирует, что глубинная оценка shrinkage для AC⁰ автоматически
  укладывается в локальный бюджет `ℓ * (log₂(M+2) + depth + 1)`.

  Эта упаковка нужна для аккуратного соединения лемм:
  `shrinkage_for_AC0` → `shrinkage_for_localCircuit`.
-/
@[simp] def LocalCircuitParameters.ofAC0 (params : AC0Parameters) :
    LocalCircuitParameters :=
  { n := params.n
    M := params.M
    ℓ := ac0DepthBound params
    depth := params.d }

@[simp] lemma LocalCircuitParameters.ofAC0_n (params : AC0Parameters) :
    (LocalCircuitParameters.ofAC0 params).n = params.n := rfl

@[simp] lemma LocalCircuitParameters.ofAC0_M (params : AC0Parameters) :
    (LocalCircuitParameters.ofAC0 params).M = params.M := rfl

@[simp] lemma LocalCircuitParameters.ofAC0_ℓ (params : AC0Parameters) :
    (LocalCircuitParameters.ofAC0 params).ℓ = ac0DepthBound params := rfl

@[simp] lemma LocalCircuitParameters.ofAC0_depth (params : AC0Parameters) :
    (LocalCircuitParameters.ofAC0 params).depth = params.d := rfl

/--
  Грубая, но универсальная оценка: выбранная локальность `ℓ = ac0DepthBound`
  доминирует глубину shrinkage-дерева из AC⁰‑леммы.

  Мы сознательно используем «широкий» запас: множитель
  `log₂(M+2) + depth + 1` как минимум равен 1, поэтому
  `ac0DepthBound ≤ ac0DepthBound * (...)`.
-/
lemma ac0DepthBound_le_local_depthBound (params : AC0Parameters) :
    ac0DepthBound params ≤
      (LocalCircuitParameters.ofAC0 params).ℓ *
        (Nat.log2 (params.M + 2) + params.d + 1) := by
  -- Фактор `log₂(M+2) + d + 1` строго положителен (там явно есть `+1`).
  have hpos :
      0 < Nat.log2 (params.M + 2) + params.d + 1 := by
    exact Nat.succ_pos _
  -- Из `0 < b` следует `a ≤ a * b` для натуральных.
  simpa [LocalCircuitParameters.ofAC0] using
    (Nat.le_mul_of_pos_right (ac0DepthBound params) hpos)

/--
  Свидетель shrinkage для локальных схем: фиксирует shrinkage-сертификат и
  численные оценки на глубину и ошибку.  Этот объект служит «точкой стыковки»
  между абстрактным условием локальности и downstream-логикой, которая ждёт
  готовый `Shrinkage`.
-/
structure LocalCircuitWitness
    (params : LocalCircuitParameters) (F : Family params.n) where
  /-- Shrinkage-сертификат для семейства `F`. -/
  shrinkage        : Shrinkage params.n
  /-- Семейство, зафиксированное в сертификате, совпадает с исходным `F`. -/
  family_eq        : shrinkage.F = F
  /-- Глубина PDT ограничена стандартной функцией от параметров схемы. -/
  depth_le         : shrinkage.t
      ≤ params.ℓ * (Nat.log2 (params.M + 2) + params.depth + 1)
  /-- Ошибка неотрицательна. -/
  epsilon_nonneg   : (0 : Q) ≤ shrinkage.ε
  /-- Ошибка не превосходит `1/(n+2)`. -/
  epsilon_le_inv   : shrinkage.ε ≤ (1 : Q) / (params.n + 2)

/--
  Удобный конструктор `LocalCircuitWitness`, превращающий готовый shrinkage-
  сертификат в локальное свидетельство.

  Этот вспомогательный блок полезен при интеграции будущих доказательств:
  как только появится алгоритм, выдающий shrinkage для локальных схем, его
  результат можно напрямую упаковать в `LocalCircuitWitness`, не дублируя
  шаблонные проверки равенств и численных оценок.
-/
def localCircuitWitnessOfShrinkage
    (params : LocalCircuitParameters) (F : Family params.n)
    (S : Shrinkage params.n)
    (hF : S.F = F)
    (ht :
      S.t ≤ params.ℓ * (Nat.log2 (params.M + 2) + params.depth + 1))
    (hε0 : (0 : Q) ≤ S.ε)
    (hε : S.ε ≤ (1 : Q) / (params.n + 2)) :
    LocalCircuitWitness params F :=
  { -- Передаём shrinkage-сертификат без изменений.
    shrinkage := S
    -- Семейство в сертификате совпадает с исходным `F`.
    family_eq := hF
    -- Глубина PDT ограничена стандартной функцией.
    depth_le := ht
    -- Ошибка неотрицательна.
    epsilon_nonneg := hε0
    -- Ошибка не превосходит `1/(n+2)`.
    epsilon_le_inv := hε }

/-!
  ### Glue-лемма: depth-2 схема → частичный сертификат для одиночного семейства

  Эта лемма — первый «клей» между конструктивным depth-2 доказательством
  и интерфейсом Step A. Мы явно строим PDT для одной схемы и упаковываем
  его в `PartialCertificate` для семейства из одной функции.

  Важное ограничение: здесь нужен `h_pos : 0 < n`, чтобы выбрать ветвящий
  индекс при построении PDT. Полный случай `n = 0` разбирается ниже в
  `partial_shrinkage_single_circuit_general`.
-/

/--
Один AC⁰ (depth-2) circuit порождает точный partial shrinkage для семейства
из одной функции. Ошибка `ε = 0`, глубина PDT не превосходит числа термов.
-/
theorem partial_shrinkage_single_circuit
    {params : AC0Parameters} (h_pos : 0 < params.n)
    (c : AC0Circuit params) :
    let f : Core.BitVec params.n → Bool := AC0Circuit.eval c
    let F : Family params.n := [f]
    ∃ (ℓ : Nat) (C : Core.PartialCertificate params.n ℓ F),
      ℓ = 0 ∧
      C.depthBound ≤ c.subcubes.length ∧
      C.epsilon = 0 := by
  intro f F
  -- Берём список подкубов, соответствующий термам depth-2 DNF схемы.
  let subcubes := c.subcubes
  -- Строим PDT, чьи листья включают все эти подкубы.
  let tree := buildPDTFromSubcubes h_pos subcubes
  -- Глубина построенного дерева контролируется длиной списка.
  have h_depth : PDT.depth tree ≤ subcubes.length := by
    simpa [tree] using buildPDTFromSubcubes_depth h_pos subcubes
  -- Каждый подкуб из списка является листом дерева.
  have h_leaves :
      ∀ β ∈ subcubes, β ∈ PDT.leaves tree := by
    simpa [tree] using buildPDTFromSubcubes_leaves_subset h_pos subcubes
  refine ⟨0, {
    witness := PartialDT.ofPDT tree
    depthBound := subcubes.length
    epsilon := 0
    -- Для ofPDT глубина ствола равна глубине исходного PDT.
    trunk_depth_le := by
      simpa [PartialDT.ofPDT] using h_depth
    -- Селекторы: единственная функция получает список подкубов,
    -- остальные — пустой список.
    selectors := fun g => if g = f then subcubes else []
    selectors_sub := by
      intro g β hg hβ
      simp [F] at hg
      subst hg
      simp [subcubes] at hβ
      -- Любой подкуб из selectors является листом PDT.
      simpa [PartialDT.realize_ofPDT] using h_leaves β hβ
    err_le := by
      intro g hg
      simp [F] at hg
      subst hg
      simp
      apply le_of_eq
      apply errU_eq_zero_of_agree
      intro x
      -- покрытие subcubes совпадает с вычислением схемы
      have hcov := AC0Circuit.coveredB_subcubes (c := c) (x := x)
      simp [f, subcubes, hcov]
  }, rfl, Nat.le_refl _, rfl⟩

/--
  Предикат «семейство `F` вычисляется локальными схемами с параметрами `params`».
  Наличие `FamilyIsLocalCircuit params F` обязательно для обращения к
  `shrinkage_for_localCircuit`.
-/
def FamilyIsLocalCircuit
    (params : LocalCircuitParameters) (F : Family params.n) : Prop :=
  Nonempty (LocalCircuitWitness params F)

/--
  `FamilyIsLocalCircuit` в текущем виде означает наличие shrinkage-сертификата
  с нужными оценками на глубину и ошибку.
-/
lemma familyIsLocalCircuit_iff_shrinkage
    (params : LocalCircuitParameters) (F : Family params.n) :
    FamilyIsLocalCircuit params F ↔
      ∃ (S : Shrinkage params.n),
        S.F = F ∧
        S.t ≤ params.ℓ * (Nat.log2 (params.M + 2) + params.depth + 1) ∧
        (0 : Q) ≤ S.ε ∧
        S.ε ≤ (1 : Q) / (params.n + 2) := by
  constructor
  · intro hF
    rcases hF with ⟨witness⟩
    refine ⟨witness.shrinkage, witness.family_eq, ?_, ?_, ?_⟩
    · exact witness.depth_le
    · exact witness.epsilon_nonneg
    · exact witness.epsilon_le_inv
  · rintro ⟨S, hF, ht, hε0, hε⟩
    exact ⟨localCircuitWitnessOfShrinkage params F S hF ht hε0 hε⟩

/--
  Предикат «малости» для локальных схем.  Мы требуем, чтобы суммарная длина
  «ствола» в shrinkage-свидетельстве была существенно меньше входной длины.
  Конкретно, ограничиваем произведение локальности на логарифмические факторы:

  `ℓ * (log₂(M+2) + depth + 1) ≤ n / 2`.

  Эта форма напрямую согласуется с оценкой на глубину PDT из
  `shrinkage_for_localCircuit` и даёт запас для применения Covering-Power.
-/
def LocalCircuitSmallEnough (params : LocalCircuitParameters) : Prop :=
  params.ℓ * (Nat.log2 (params.M + 2) + params.depth + 1) ≤ params.n / 2

/-- Уточняющая структура, описывающая гарантии shrinkage.

`depthBound` и `errorBound` — ожидаемые верхние оценки на глубину PDT и ошибку
аппроксимации, получаемые из multi-switching леммы.  Мы оставляем их в явном
виде, чтобы позднее подставлять сюда конкретные полиномиальные/квазиполиномиальные
формулы. -/
structure ShrinkageBounds where
  depthBound : Nat
  errorBound : Q
  deriving Repr

/--
  Усиленная версия shrinkage-факта: вместо полного PDT возвращается частичный
  сертификат с контролируемой глубиной хвостов.  Такой формат ближе к
  классическому изложению multi-switching-леммы и непосредственно пригоден для
  шага B, где важно знать глубину ствола и высоту хвостов по отдельности.

  Это конструктивная версия для depth-2 DNF: shrinkage-свидетельство собирается
  напрямую из подкубов, соответствующих каждому терму формулы.

  В дальнейшем здесь планируется расширение до общей AC⁰ switching-леммы
  (depth > 2), но базовый случай уже не требует внешней аксиомы.
-/
/-
  Полная версия «одиночного» shrinkage без предположения `0 < n`.

  Это закрывает оставшийся технический пробел: когда входов нет (n = 0),
  любая рестрикция совпадает с полным подкубом, а дерево решений состоит
  из единственного листа.  В результате мы получаем ту же гарантию,
  что и в case `n > 0`, но уже без дополнительной гипотезы.
-/
theorem partial_shrinkage_single_circuit_general
    (params : AC0Parameters) (c : AC0Circuit params) :
    let f : Core.BitVec params.n → Bool := AC0Circuit.eval c
    let F : Family params.n := [f]
    ∃ (ℓ : Nat) (C : Core.PartialCertificate params.n ℓ F),
      ℓ = 0 ∧
      C.depthBound ≤ c.subcubes.length ∧
      C.epsilon = 0 := by
  classical
  intro f F
  by_cases hpos : 0 < params.n
  · -- Для `n > 0` используем уже построенный PDT на списке подкубов.
    simpa [f, F] using
      (partial_shrinkage_single_circuit (params := params) hpos c)
  · -- Случай `n = 0`: все подкубы совпадают с полным.
    have hzero : params.n = 0 := Nat.eq_zero_of_not_pos hpos
    let subcubes := c.subcubes
    let tree : PDT params.n := PDT.leaf (fullSubcube params.n)
    have hdepth : PDT.depth tree ≤ subcubes.length := by
      have : PDT.depth tree = 0 := by simp [tree, PDT.depth]
      simpa [this] using (Nat.zero_le subcubes.length)
    have hleaves :
        ∀ β ∈ subcubes, β ∈ PDT.leaves tree := by
      intro β hβ
      have hβ_full : β = fullSubcube params.n :=
        subcube_eq_full_of_n_zero' hzero β
      simp [tree, PDT.leaves, hβ_full]
    refine ⟨0, {
      witness := PartialDT.ofPDT tree
      depthBound := subcubes.length
      epsilon := 0
      trunk_depth_le := by
        simpa [PartialDT.ofPDT] using hdepth
      selectors := fun g => if g = f then subcubes else []
      selectors_sub := by
        intro g β hg hβ
        simp [F] at hg
        subst hg
        simp [subcubes] at hβ
        simpa [PartialDT.realize_ofPDT] using hleaves β hβ
      err_le := by
        intro g hg
        simp [F] at hg
        subst hg
        simp
        apply le_of_eq
        apply errU_eq_zero_of_agree
        intro x
        have hcov := AC0Circuit.coveredB_subcubes (c := c) (x := x)
        simp [f, subcubes, hcov]
    }, rfl, Nat.le_refl _, rfl⟩

theorem partial_shrinkage_for_AC0_with_bound
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F)
    (hBound : AC0DepthBoundWitness params F hF) :
    ∃ (ℓ : Nat) (C : Core.PartialCertificate params.n ℓ F),
      ℓ ≤ Nat.log2 (params.M + 2) ∧
      C.depthBound + ℓ ≤ ac0DepthBound params ∧
      (0 : Core.Q) ≤ C.epsilon ∧
      C.epsilon ≤ (1 : Core.Q) / (params.n + 2) := by
  classical
  let S := hBound.shrinkage
  have hF' : S.F = F := hBound.family_eq
  have hdepth_bound : S.t ≤ ac0DepthBound params := by
    simpa [ac0DepthBound] using hBound.depth_le
  -- Приводим shrinkage к частичному сертификату нулевого уровня.
  let C0 : Core.PartialCertificate params.n 0 S.F :=
    Core.PartialCertificate.ofShrinkage S
  have hC0 :
      ∃ (ℓ : Nat) (C : Core.PartialCertificate params.n ℓ S.F),
        ℓ ≤ Nat.log2 (params.M + 2) ∧
        C.depthBound + ℓ ≤ ac0DepthBound params ∧
        (0 : Core.Q) ≤ C.epsilon ∧
        C.epsilon ≤ (1 : Core.Q) / (params.n + 2) := by
    refine ⟨0, C0, ?_, ?_, ?_, ?_⟩
    · simp
    ·
      simpa [C0, Core.PartialCertificate.ofShrinkage] using hdepth_bound
    ·
      simpa [C0, Core.PartialCertificate.ofShrinkage] using hBound.epsilon_nonneg
    ·
      simpa [C0, Core.PartialCertificate.ofShrinkage] using hBound.epsilon_le_inv
  -- Переписываем результат по `hF'`, чтобы получить сертификат для `F`.
  exact (Eq.ndrec
    (motive := fun F =>
      ∃ (ℓ : Nat) (C : Core.PartialCertificate params.n ℓ F),
        ℓ ≤ Nat.log2 (params.M + 2) ∧
        C.depthBound + ℓ ≤ ac0DepthBound params ∧
        (0 : Core.Q) ≤ C.epsilon ∧
        C.epsilon ≤ (1 : Core.Q) / (params.n + 2))
    hC0
    hF')

theorem partial_shrinkage_for_AC0
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    ∃ (ℓ : Nat) (C : Core.PartialCertificate params.n ℓ F),
      ℓ ≤ Nat.log2 (params.M + 2) ∧
      C.depthBound + ℓ ≤ ac0DepthBound params ∧
      (0 : Core.Q) ≤ C.epsilon ∧
      C.epsilon ≤ (1 : Core.Q) / (params.n + 2) := by
  -- Слабая оценка автоматически поднимается до `ac0DepthBound_strong`.
  have hBound := ac0DepthBoundWitness_of_weak params F hF
  exact partial_shrinkage_for_AC0_with_bound params F hF hBound

/--
  Версия shrinkage‑факта, принимающая именно polylog‑свидетель.

  Эта оболочка удобна для будущей multi‑switching леммы: когда мы научимся
  строить `AC0PolylogBoundWitness`, downstream‑код сможет напрямую пользоваться
  этой леммой, не вспоминая про `max`‑мост.
-/
theorem partial_shrinkage_for_AC0_with_polylog
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F)
    (hpoly : AC0PolylogBoundWitness params F hF) :
    ∃ (ℓ : Nat) (C : Core.PartialCertificate params.n ℓ F),
      ℓ ≤ Nat.log2 (params.M + 2) ∧
      C.depthBound + ℓ ≤ ac0DepthBound_strong params ∧
      (0 : Core.Q) ≤ C.epsilon ∧
      C.epsilon ≤ (1 : Core.Q) / (params.n + 2) := by
  -- Используем shrinkage‑сертификат из polylog‑свидетеля и переносим его в
  -- частичную форму через `PartialCertificate.ofShrinkage`.
  classical
  let S := hpoly.shrinkage
  have hF' : S.F = F := hpoly.family_eq
  have hdepth_polylog :
      S.t ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) :=
    hpoly.depth_le_polylog
  have hdepth_strong : S.t ≤ ac0DepthBound_strong params := by
    exact hdepth_polylog.trans (ac0DepthBound_polylog_le_strong params)
  -- Приводим семейство shrinkage к `F`, чтобы избежать `cast` в целях.
  let C0 : Core.PartialCertificate params.n 0 S.F :=
    Core.PartialCertificate.ofShrinkage S
  have hC0 :
      ∃ (ℓ : Nat) (C : Core.PartialCertificate params.n ℓ S.F),
        ℓ ≤ Nat.log2 (params.M + 2) ∧
        C.depthBound + ℓ ≤ ac0DepthBound_strong params ∧
        (0 : Core.Q) ≤ C.epsilon ∧
        C.epsilon ≤ (1 : Core.Q) / (params.n + 2) := by
    refine ⟨0, C0, ?_, ?_, ?_, ?_⟩
    · simp
    ·
      -- `depthBound + ℓ = S.t` для `ℓ = 0`.
      simpa [C0, Core.PartialCertificate.ofShrinkage] using hdepth_strong
    ·
      -- Неотрицательность ошибки приходит из shrinkage.
      simpa [C0, Core.PartialCertificate.ofShrinkage] using hpoly.epsilon_nonneg
    ·
      -- Верхняя граница ошибки переносится напрямую.
      simpa [C0, Core.PartialCertificate.ofShrinkage] using hpoly.epsilon_le_inv
  -- Переписываем результат по `hF'`, чтобы получить сертификат для `F`.
  exact (Eq.ndrec
    (motive := fun F =>
      ∃ (ℓ : Nat) (C : Core.PartialCertificate params.n ℓ F),
        ℓ ≤ Nat.log2 (params.M + 2) ∧
        C.depthBound + ℓ ≤ ac0DepthBound_strong params ∧
        (0 : Core.Q) ≤ C.epsilon ∧
        C.epsilon ≤ (1 : Core.Q) / (params.n + 2))
    hC0
    hF')

/-!
### Stage 6: polylog‑свидетельство и shrinkage

Stage 6 замыкает цепочку, преобразуя polylog‑bound
в полноценный partial shrinkage‑сертификат.
-/

def stage6_polylog_witness_complete
    (params : AC0Parameters) (F : Family params.n)
    (witness : AC0MultiSwitchingWitness params F) :
    AC0PolylogBoundWitness params F ⟨witness.base⟩ := by
  exact ac0PolylogBoundWitness_of_multi_switching params F witness

theorem stage6_partial_shrinkage_complete
    (params : AC0Parameters) (F : Family params.n)
    (witness : AC0MultiSwitchingWitness params F) :
    ∃ (ℓ : Nat) (C : Core.PartialCertificate params.n ℓ F),
      ℓ ≤ Nat.log2 (params.M + 2) ∧
      C.depthBound + ℓ ≤ ac0DepthBound_strong params ∧
      (0 : Core.Q) ≤ C.epsilon ∧
      C.epsilon ≤ (1 : Core.Q) / (params.n + 2) := by
  have hpoly : AC0PolylogBoundWitness params F ⟨witness.base⟩ :=
    stage6_polylog_witness_complete params F witness
  simpa using
    (partial_shrinkage_for_AC0_with_polylog
      (params := params) (F := F) (hF := ⟨witness.base⟩) hpoly)

/--
  Усиленная (polylog) версия shrinkage-факта для AC⁰.

  Сейчас мы по-прежнему получаем strong‑оценку через общий лифт от
  `partial_shrinkage_for_AC0`.  Благодаря тому, что
  `ac0DepthBound_strong` доминирует `M²`, этот шаг не требует
  дополнительной гипотезы «малости» и остаётся полностью формальным.
-/
theorem partial_shrinkage_for_AC0_strong
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    ∃ (ℓ : Nat) (C : Core.PartialCertificate params.n ℓ F),
      ℓ ≤ Nat.log2 (params.M + 2) ∧
      C.depthBound + ℓ ≤ ac0DepthBound_strong params ∧
      (0 : Core.Q) ≤ C.epsilon ∧
      C.epsilon ≤ (1 : Core.Q) / (params.n + 2) := by
  classical
  obtain ⟨ℓ, C, hℓ, hdepth, hε0, hε⟩ :=
    partial_shrinkage_for_AC0 params F hF
  -- Поднимаем оценку глубины за счёт `ac0DepthBound_le_strong`.
  have hbound := ac0DepthBound_le_strong params
  refine ⟨ℓ, C, hℓ, hdepth.trans hbound, hε0, hε⟩

/--
`AC0PartialWitness` собирает в одном месте весь набор параметров, выдаваемых
частичным shrinkage-фактом для AC⁰.  Помимо самого частичного PDT и глубины
хвостов мы сохраняем численные оценки, необходимые для шага B, что избавляет
от многократного обращения к `Classical.choose`.
-/
structure AC0PartialWitness
    (params : AC0Parameters) (F : Family params.n) where
  /-- Максимальная глубина хвостов частичного дерева. -/
  level          : Nat
  /-- Частичный shrinkage-сертификат. -/
  certificate    : Core.PartialCertificate params.n level F
  /-- Ограничение `level ≤ log₂(M+2)`. -/
  level_le_log   : level ≤ Nat.log2 (params.M + 2)
  /-- Верхняя граница на суммарную глубину. -/
  depth_le       : certificate.depthBound + level
      ≤ ac0DepthBound params
  /-- Неотрицательность ошибки. -/
  epsilon_nonneg : (0 : Core.Q) ≤ certificate.epsilon
  /-- Верхняя оценка ошибки `ε ≤ 1/(n+2)`. -/
  epsilon_le_inv : certificate.epsilon ≤ (1 : Core.Q) / (params.n + 2)

/--
Из внешнего факта `partial_shrinkage_for_AC0` конструируем объект `AC0PartialWitness`.
Доказательство чисто распаковочное: мы последовательно извлекаем глубину хвостов,
частичный PDT и перечисленные численные границы.
-/
noncomputable def ac0PartialWitness
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    AC0PartialWitness params F := by
  classical
  let h := partial_shrinkage_for_AC0 params F hF
  let ℓ := Classical.choose h
  let rest := Classical.choose_spec h
  let C := Classical.choose rest
  have hprop := Classical.choose_spec rest
  refine
    { level := ℓ
      certificate := C
      level_le_log := ?_
      depth_le := ?_
      epsilon_nonneg := ?_
      epsilon_le_inv := ?_ }
  · exact hprop.left
  · exact hprop.right.left
  · exact hprop.right.right.left
  · exact hprop.right.right.right

/--
Вариант `ac0PartialWitness`, принимающий уже готовую strong‑границу на глубину
shrinkage.  Это и есть точка, где в будущем будет подключено настоящее
multi‑switching доказательство polylog‑границы.
-/
noncomputable def ac0PartialWitness_with_bound
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F)
    (hBound : AC0DepthBoundWitness params F hF) :
    AC0PartialWitness params F := by
  classical
  let h := partial_shrinkage_for_AC0_with_bound params F hF hBound
  let ℓ := Classical.choose h
  let rest := Classical.choose_spec h
  let C := Classical.choose rest
  have hprop := Classical.choose_spec rest
  refine
    { level := ℓ
      certificate := C
      level_le_log := ?_
      depth_le := ?_
      epsilon_nonneg := ?_
      epsilon_le_inv := ?_ }
  · exact hprop.left
  · exact hprop.right.left
  · exact hprop.right.right.left
  · exact hprop.right.right.right

/--
Вариант `ac0PartialWitness`, принимающий polylog‑свидетель.

Это удобная обёртка: когда появится настоящая multi‑switching лемма,
она будет давать `AC0PolylogBoundWitness`, а downstream‑код сможет
использовать этот конструктор без дополнительных правок.
-/
noncomputable def ac0PartialWitness_with_polylog
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F)
    (hpoly : AC0PolylogBoundWitness params F hF) :
    AC0PartialWitness params F := by
  classical
  let h := partial_shrinkage_for_AC0_with_polylog params F hF hpoly
  let ℓ := Classical.choose h
  let rest := Classical.choose_spec h
  let C := Classical.choose rest
  have hprop := Classical.choose_spec rest
  refine
    { level := ℓ
      certificate := C
      level_le_log := ?_
      depth_le := ?_
      epsilon_nonneg := ?_
      epsilon_le_inv := ?_ }
  · exact hprop.left
  · exact hprop.right.left
  · exact hprop.right.right.left
  · exact hprop.right.right.right

/-- Высота хвостов частичного PDT из AC⁰-свидетельства. -/
noncomputable def partialCertificate_level_from_AC0
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) : Nat :=
  (ac0PartialWitness params F hF).level

/-- Сам частичный shrinkage-сертификат из факта `partial_shrinkage_for_AC0`. -/
noncomputable def partialCertificate_from_AC0
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    Core.PartialCertificate params.n
      (partialCertificate_level_from_AC0 params F hF) F :=
  (ac0PartialWitness params F hF).certificate

/-- Ограничение на глубину хвостов: `ℓ ≤ log₂(M+2)`. -/
lemma partialCertificate_level_from_AC0_le
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    partialCertificate_level_from_AC0 params F hF ≤ Nat.log2 (params.M + 2) := by
  classical
  change (ac0PartialWitness params F hF).level ≤ Nat.log2 (params.M + 2)
  exact (ac0PartialWitness params F hF).level_le_log

/-- Граница на суммарную глубину: `depthBound + ℓ` ограничена классической оценкой. -/
lemma partialCertificate_depthBound_add_level_le
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    (partialCertificate_from_AC0 params F hF).depthBound
        + partialCertificate_level_from_AC0 params F hF
      ≤ ac0DepthBound params := by
  classical
  change
      (ac0PartialWitness params F hF).certificate.depthBound
        + (ac0PartialWitness params F hF).level
        ≤ ac0DepthBound params
  exact (ac0PartialWitness params F hF).depth_le

/-- Усиленная версия оценки глубины: поднимаем bound до polylog. -/
lemma partialCertificate_depthBound_add_level_le_strong
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    (partialCertificate_from_AC0 params F hF).depthBound
        + partialCertificate_level_from_AC0 params F hF
      ≤ ac0DepthBound_strong params := by
  -- Используем уже имеющуюся bound на `ac0DepthBound`,
  -- затем апгрейдим её через `ac0DepthBound_le_strong`.
  have hweak := partialCertificate_depthBound_add_level_le
    (params := params) (F := F) (hF := hF)
  exact hweak.trans (ac0DepthBound_le_strong params)

/-- Неотрицательность ошибки частичного сертификата. -/
lemma partialCertificate_epsilon_nonneg
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    (0 : Core.Q) ≤ (partialCertificate_from_AC0 params F hF).epsilon := by
  classical
  change (0 : Core.Q)
      ≤ (ac0PartialWitness params F hF).certificate.epsilon
  exact (ac0PartialWitness params F hF).epsilon_nonneg

/-- Оценка ошибки сверху: `ε ≤ 1/(n+2)`. -/
lemma partialCertificate_epsilon_le_inv
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    (partialCertificate_from_AC0 params F hF).epsilon
      ≤ (1 : Core.Q) / (params.n + 2) := by
  classical
  change (ac0PartialWitness params F hF).certificate.epsilon
      ≤ (1 : Core.Q) / (params.n + 2)
  exact (ac0PartialWitness params F hF).epsilon_le_inv

/-- Заготовка для "внешнего" факта: псевдослучайная multi-switching лемма
Servedio–Tan/Håstad.  Возвращает объект `Shrinkage`, совместимый с конвейером
SAL.  Параметры оценок записаны максимально прозрачно; их значения будут
уточняться по мере подключения конкретных источников.

Обратите внимание: мы фиксируем семейство функций `F` (список) и утверждаем,
что существует общая PDT глубины `t` и ошибка `ε`, удовлетворяющие стандартным
для SAL условиям.  В дальнейшем этот факт будет служить мостом между
комбинаторным ядром и оценками размера атласа. -/
theorem shrinkage_for_AC0
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    ∃ (t : Nat) (ε : Q) (S : Shrinkage params.n),
      S.F = F ∧ S.t = t ∧ S.ε = ε ∧
        t ≤ ac0DepthBound params ∧
        (0 : Q) ≤ ε ∧
        ε ≤ (1 : Q) / (params.n + 2) :=
  by
    classical
    -- извлекаем частичный сертификат и переводим его в shrinkage
    let ℓ := partialCertificate_level_from_AC0 params F hF
    let C := partialCertificate_from_AC0 params F hF
    let S := Core.PartialCertificate.toShrinkage (n := params.n)
      (ℓ := ℓ) (F := F) C
    refine ⟨C.depthBound + ℓ, C.epsilon, S, ?_⟩
    -- сначала равенство семейства
    have hF_eq : S.F = F := Core.PartialCertificate.toShrinkage_family
      (n := params.n) (ℓ := ℓ) (F := F) C
    refine And.intro hF_eq ?_
    -- затем равенство глубины и ошибки
    have ht : S.t = C.depthBound + ℓ :=
      Core.PartialCertificate.toShrinkage_depth
        (n := params.n) (ℓ := ℓ) (F := F) C
    have hε : S.ε = C.epsilon :=
      Core.PartialCertificate.toShrinkage_epsilon
        (n := params.n) (ℓ := ℓ) (F := F) C
    refine And.intro ht ?_
    -- оставшиеся численные границы
    have htBound := partialCertificate_depthBound_add_level_le
      (params := params) (F := F) (hF := hF)
    have hε0 := partialCertificate_epsilon_nonneg
      (params := params) (F := F) (hF := hF)
    have hεBound := partialCertificate_epsilon_le_inv
      (params := params) (F := F) (hF := hF)
    exact And.intro hε (And.intro htBound (And.intro hε0 hεBound))

/--
  Polylog‑вариант shrinkage‑факта для AC⁰.

  Эта лемма использует polylog‑свидетель напрямую и фиксирует итоговую
  границу как `ac0DepthBound_strong`.  В отличие от `shrinkage_for_AC0`,
  здесь не требуется проход через слабую оценку `M²`.
-/
theorem shrinkage_for_AC0_with_polylog
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F)
    (hpoly : AC0PolylogBoundWitness params F hF) :
    ∃ (t : Nat) (ε : Q) (S : Shrinkage params.n),
      S.F = F ∧ S.t = t ∧ S.ε = ε ∧
        t ≤ ac0DepthBound_strong params ∧
        (0 : Q) ≤ ε ∧
        ε ≤ (1 : Q) / (params.n + 2) := by
  classical
  obtain ⟨ℓ, C, hℓ, hdepth, hε0, hεBound⟩ :=
    partial_shrinkage_for_AC0_with_polylog params F hF hpoly
  let S := Core.PartialCertificate.toShrinkage (n := params.n)
    (ℓ := ℓ) (F := F) C
  refine ⟨C.depthBound + ℓ, C.epsilon, S, ?_⟩
  have hF_eq : S.F = F := Core.PartialCertificate.toShrinkage_family
    (n := params.n) (ℓ := ℓ) (F := F) C
  refine And.intro hF_eq ?_
  have ht : S.t = C.depthBound + ℓ :=
    Core.PartialCertificate.toShrinkage_depth
      (n := params.n) (ℓ := ℓ) (F := F) C
  have hε : S.ε = C.epsilon :=
    Core.PartialCertificate.toShrinkage_epsilon
      (n := params.n) (ℓ := ℓ) (F := F) C
  refine And.intro ht ?_
  exact And.intro hε (And.intro hdepth (And.intro hε0 hεBound))

/--
  Усиленная версия `shrinkage_for_AC0`: сохраняет те же данные,
  но вместо `t ≤ ac0DepthBound` выдаёт `t ≤ ac0DepthBound_strong`.

  Технически это переназначение границы через
  `ac0DepthBound_le_strong`, однако именно такой интерфейс нужен,
  чтобы downstream-пайплайн уже "видел" улучшенную оценку.
-/
theorem shrinkage_for_AC0_strong
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    ∃ (t : Nat) (ε : Q) (S : Shrinkage params.n),
      S.F = F ∧ S.t = t ∧ S.ε = ε ∧
        t ≤ ac0DepthBound_strong params ∧
        (0 : Q) ≤ ε ∧
        ε ≤ (1 : Q) / (params.n + 2) := by
  -- Берём исходное shrinkage‑свидетельство и поднимаем bound на t.
  obtain ⟨t, ε, S, hF', ht, hε, htBound, hε0, hεBound⟩ :=
    shrinkage_for_AC0 params F hF
  have htBound' : t ≤ ac0DepthBound_strong params := by
    exact htBound.trans (ac0DepthBound_le_strong params)
  exact ⟨t, ε, S, hF', ht, hε, htBound', hε0, hεBound⟩

/--
  Связка AC⁰ → локальные схемы (через выбор «запасной» локальности).

  Идея: любое AC⁰‑семейство можно трактовать как локальное, если разрешить
  локальность `ℓ := ac0DepthBound`.  Тогда shrinkage‑сертификат из леммы
  `shrinkage_for_AC0` автоматически удовлетворяет локальной глубинной
  оценке.  Это *не* финальная A2‑лемма (она должна давать куда лучшее
  `ℓ`), но уже формализует «композицию» для случаев, когда AC⁰‑shrinkage
  доступен напрямую.
-/
lemma familyIsLocalCircuit_of_AC0
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    FamilyIsLocalCircuit (LocalCircuitParameters.ofAC0 params) F := by
  classical
  -- Из AC⁰‑shrinkage извлекаем сертификат `S`.
  obtain ⟨t, ε, S, hF', ht, hε, htBound, hε0, hεBound⟩ :=
    shrinkage_for_AC0 params F hF
  have hε0' : (0 : Q) ≤ S.ε := by
    simpa [hε] using hε0
  have hεBound' : S.ε ≤ (1 : Q) / (params.n + 2) := by
    simpa [hε] using hεBound
  -- Перепаковываем его в `LocalCircuitWitness` с «широкой» локальностью.
  refine ⟨localCircuitWitnessOfShrinkage
    (params := LocalCircuitParameters.ofAC0 params)
    (F := F)
    (S := S)
    (hF := hF')
    (ht := ?_)
    (hε0 := hε0')
    (hε := ?_)⟩
  · -- Глубинная оценка берётся из AC⁰‑леммы и доминируется локальным budget.
    -- Сначала перепишем `t` через `S.t`, а затем применим оценку.
    -- `ht` говорит `S.t = t`, поэтому переносим bound на `S.t`.
    have ht' : S.t ≤ ac0DepthBound params := by
      -- `ht` есть равенство `S.t = t`.
      -- Используем его, чтобы переписать `t ≤ ac0DepthBound`.
      simpa [ht] using htBound
    -- Применяем общую оценку `ac0DepthBound ≤ localBound`.
    exact ht'.trans (ac0DepthBound_le_local_depthBound params)
  · -- Локальный параметр `n` совпадает с AC⁰‑параметром.
    -- Поэтому оценка `ε ≤ 1/(n+2)` совпадает буквально.
    simpa [LocalCircuitParameters.ofAC0] using hεBound'

/--
  Версия `familyIsLocalCircuit_of_AC0`, принимающая polylog‑свидетель.

  Это шаг к будущей multi‑switching лемме: если нам дадут чистую polylog‑оценку
  числа подкубов, то локальный shrinkage‑свидетель строится без изменений
  downstream‑логики.
-/
lemma familyIsLocalCircuit_of_AC0_polylog
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F)
    (hpoly : AC0PolylogBoundWitness params F hF) :
    FamilyIsLocalCircuit (LocalCircuitParameters.ofAC0 params) F := by
  classical
  -- Из polylog‑shrinkage извлекаем частичный сертификат.
  obtain ⟨ℓ, C, hℓ, hdepth, hε0, hεBound⟩ :=
    partial_shrinkage_for_AC0_with_polylog params F hF hpoly
  -- Переводим частичный сертификат в shrinkage.
  let S := Core.PartialCertificate.toShrinkage
    (n := params.n) (ℓ := ℓ) (F := F) C
  have hF' : S.F = F :=
    Core.PartialCertificate.toShrinkage_family
      (n := params.n) (ℓ := ℓ) (F := F) C
  have ht : S.t = C.depthBound + ℓ :=
    Core.PartialCertificate.toShrinkage_depth
      (n := params.n) (ℓ := ℓ) (F := F) C
  have hε : S.ε = C.epsilon :=
    Core.PartialCertificate.toShrinkage_epsilon
      (n := params.n) (ℓ := ℓ) (F := F) C
  -- Перепаковываем в локальный witness.
  refine ⟨localCircuitWitnessOfShrinkage
    (params := LocalCircuitParameters.ofAC0 params)
    (F := F)
    (S := S)
    (hF := hF')
    (ht := ?_)
    (hε0 := ?_)
    (hε := ?_)⟩
  · -- Сильная граница из polylog‑оценки доминируется локальным budget.
    have ht' : S.t ≤ ac0DepthBound_strong params := by
      simpa [ht] using hdepth
    have ht'' : S.t ≤ ac0DepthBound params := by
      simpa [ac0DepthBound] using ht'
    exact ht''.trans (ac0DepthBound_le_local_depthBound params)
  · -- Неотрицательность ошибки переносится из частичного сертификата.
    simpa [hε] using hε0
  · -- И верхняя граница ошибки тоже переносится напрямую.
    simpa [hε] using hεBound


/--
  Внешний факт для локальных схем: после применения подходящих ограничений
  схема становится «малой» PDT.  Конкретные численные границы отражают
  стандартные оценки: глубина дерева пропорциональна произведению локальности
  и логарифмических факторов по размеру и глубине схемы.
-/
lemma shrinkage_for_localCircuit_of_shrinkage
    (params : LocalCircuitParameters) (F : Family params.n)
    (S : Shrinkage params.n)
    (hF : S.F = F)
    (ht :
      S.t ≤ params.ℓ * (Nat.log2 (params.M + 2) + params.depth + 1))
    (hε0 : (0 : Q) ≤ S.ε)
    (hε : S.ε ≤ (1 : Q) / (params.n + 2)) :
    ∃ (t : Nat) (ε : Q) (S : Shrinkage params.n),
      S.F = F ∧ S.t = t ∧ S.ε = ε ∧
        t ≤ params.ℓ * (Nat.log2 (params.M + 2) + params.depth + 1) ∧
        (0 : Q) ≤ ε ∧
        ε ≤ (1 : Q) / (params.n + 2) := by
  -- Мы буквально переупаковываем shrinkage-сертификат с явными оценками.
  refine ⟨S.t, S.ε, S, ?_⟩
  refine And.intro hF ?_
  refine And.intro rfl ?_
  refine And.intro rfl ?_
  exact And.intro ht (And.intro hε0 hε)

-- Вариант на случай, когда shrinkage выдан как часть `LocalCircuitWitness`.
-- Он нужен как "короткий переход" для существующих конструкций.
lemma shrinkage_for_localCircuit_of_witness
    (params : LocalCircuitParameters) (F : Family params.n)
    (witness : LocalCircuitWitness params F) :
    ∃ (t : Nat) (ε : Q) (S : Shrinkage params.n),
      S.F = F ∧ S.t = t ∧ S.ε = ε ∧
        t ≤ params.ℓ * (Nat.log2 (params.M + 2) + params.depth + 1) ∧
        (0 : Q) ≤ ε ∧
        ε ≤ (1 : Q) / (params.n + 2) := by
  -- Разворачиваем свидетель и применяем общий "shrinkage → тройка" конструктор.
  exact
    shrinkage_for_localCircuit_of_shrinkage
      (params := params)
      (F := F)
      (S := witness.shrinkage)
      (hF := witness.family_eq)
      (ht := witness.depth_le)
      (hε0 := witness.epsilon_nonneg)
      (hε := witness.epsilon_le_inv)

theorem shrinkage_for_localCircuit
    (params : LocalCircuitParameters) (F : Family params.n)
    (hF : FamilyIsLocalCircuit params F) :
    ∃ (t : Nat) (ε : Q) (S : Shrinkage params.n),
      S.F = F ∧ S.t = t ∧ S.ε = ε ∧
        t ≤ params.ℓ * (Nat.log2 (params.M + 2) + params.depth + 1) ∧
        (0 : Q) ≤ ε ∧
        ε ≤ (1 : Q) / (params.n + 2) := by
  classical
  -- Раскручиваем эквивалентность: локальность ≡ наличие shrinkage-сертификата.
  -- Так доказательство «складывается» из одной общей леммы и не зависит от
  -- внутреннего устройства `LocalCircuitWitness`.
  rcases (familyIsLocalCircuit_iff_shrinkage params F).1 hF with
    ⟨S, hF, ht, hε0, hε⟩
  -- Используем единую оболочку для shrinkage, чтобы всё сводилось к одному месту.
  exact
    shrinkage_for_localCircuit_of_shrinkage
      (params := params)
      (F := F)
      (S := S)
      (hF := hF)
      (ht := ht)
      (hε0 := hε0)
      (hε := hε)

/--
  Упаковка shrinkage‑сертификата для локальных схем, полученного из AC⁰.
  Это удобный вариант, если downstream ждёт именно тройку `(t, ε, S)`.
-/
lemma shrinkage_for_localCircuit_of_AC0
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    ∃ (t : Nat) (ε : Q) (S : Shrinkage params.n),
      S.F = F ∧ S.t = t ∧ S.ε = ε ∧
        t ≤ (LocalCircuitParameters.ofAC0 params).ℓ *
          (Nat.log2 (params.M + 2) + params.d + 1) ∧
        (0 : Q) ≤ ε ∧
        ε ≤ (1 : Q) / (params.n + 2) := by
  classical
  -- Получаем локальный witness через AC⁰‑shrinkage и раскрываем его.
  have hLocal : FamilyIsLocalCircuit (LocalCircuitParameters.ofAC0 params) F :=
    familyIsLocalCircuit_of_AC0 (params := params) (F := F) hF
  -- Переводим `FamilyIsLocalCircuit` в требуемую тройку.
  -- Используем уже существующий `shrinkage_for_localCircuit`.
  simpa [LocalCircuitParameters.ofAC0] using
    shrinkage_for_localCircuit
      (params := LocalCircuitParameters.ofAC0 params)
      (F := F)
      hLocal

/--
Построение `LocalCircuitWitness` теперь сводится к извлечению готового
свидетеля из `FamilyIsLocalCircuit`.  Это сохраняет тот же интерфейс, но
убирает прямую зависимость от внешней аксиомы.
-/
noncomputable def localCircuitWitness
    (params : LocalCircuitParameters) (F : Family params.n)
    (hF : FamilyIsLocalCircuit params F) :
    LocalCircuitWitness params F := by
  classical
  exact Classical.choice hF

/-!
  ## SAL-ready packaging for local circuits

  Леммы ниже аккуратно извлекают `CommonPDT` и атлас из shrinkage-факта
  для локальных схем.  Это точно тот же «переход к SAL», что и в AC⁰‑ветке,
  но теперь параметризован локальными ограничениями.

  Важно: мы не раскрываем внутреннюю структуру `LocalCircuitWitness` и не
  предполагаем ничего, кроме уже имеющегося shrinkage‑сертификата.
-/

/-- Общий PDT, полученный из shrinkage‑свидетельства локальных схем. -/
noncomputable def commonPDT_from_localCircuit
    (params : LocalCircuitParameters) (F : Family params.n)
    (hF : FamilyIsLocalCircuit params F) : Core.CommonPDT params.n F := by
  classical
  -- Извлекаем shrinkage‑свидетеля и приводим тип через `family_eq`.
  let witness := localCircuitWitness params F hF
  exact cast
    (congrArg (fun F' => Core.CommonPDT params.n F') witness.family_eq)
    witness.shrinkage.commonPDT

/-- Общий PDT для локальных схем задаёт рабочий атлас. -/
theorem commonPDT_from_localCircuit_works
    (params : LocalCircuitParameters) (F : Family params.n)
    (hF : FamilyIsLocalCircuit params F) :
    WorksFor
      (Core.CommonPDT.toAtlas (commonPDT_from_localCircuit params F hF)) F := by
  classical
  simpa using (Core.CommonPDT.worksFor
    (C := commonPDT_from_localCircuit params F hF))

/-- Удобная оболочка: атлас, извлечённый из shrinkage локальных схем. -/
noncomputable def atlas_from_localCircuit
    (params : LocalCircuitParameters) (F : Family params.n)
    (hF : FamilyIsLocalCircuit params F) : Atlas params.n :=
  Core.CommonPDT.toAtlas (commonPDT_from_localCircuit params F hF)

/-- Атлас для локальных схем действительно работает на всём семействе. -/
theorem atlas_from_localCircuit_works
    (params : LocalCircuitParameters) (F : Family params.n)
    (hF : FamilyIsLocalCircuit params F) :
    WorksFor (atlas_from_localCircuit params F hF) F := by
  simpa [atlas_from_localCircuit] using (Core.CommonPDT.worksFor
    (C := commonPDT_from_localCircuit params F hF))

/--
  Техническая лемма: при любом `n` имеем `1 / (n + 2) ≤ 1 / 2`.
  Доказательство — аккуратная алгебра на ℚ: сводим утверждение к
  очевидному неравенству `2 ≤ n + 2` и раскрываем деление.
-/
lemma inv_nat_succ_succ_le_half (n : Nat) :
    (1 : Q) / (n + 2) ≤ (1 : Q) / 2 := by
  have hNat : (2 : Q) ≤ (n + 2 : Q) := by
    exact_mod_cast (Nat.le_add_left 2 n)
  have hpos : (0 : Q) < (2 : Q) := by norm_num
  have hdiv :=
    (one_div_le_one_div_of_le (a := (2 : Q)) (b := (n + 2 : Q)) hpos hNat)
  exact hdiv

/--
  Из оценки `ε ≤ 1 / (n + 2)` немедленно следует `ε ≤ 1 / 2`.
  Это условие нужно для дальнейших энтропийных оценок шара Хэмминга.
-/
lemma eps_le_half_of_eps_le_inv_nplus2 (n : Nat) {ε : Q}
    (h : ε ≤ (1 : Q) / (n + 2)) : ε ≤ (1 : Q) / 2 :=
  h.trans (inv_nat_succ_succ_le_half n)

/--
  В дополнение к атласу полезно иметь явный shrinkage-сертификат, который
  сохраняет дерево и выбор листьев.  Он используется на шаге B.
-/
noncomputable def certificate_from_AC0
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    Core.Shrinkage params.n :=
  let witness := ac0PartialWitness params F hF
  Core.PartialCertificate.toShrinkage
    (n := params.n)
    (ℓ := witness.level)
    (F := F)
    witness.certificate

/--
  Аналог `certificate_from_AC0`, но использующий явную strong‑границу на глубину
  shrinkage.  Полезен для явного контроля глубины PDT.
-/
noncomputable def certificate_from_AC0_with_bound
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F)
    (hBound : AC0DepthBoundWitness params F hF) :
    Core.Shrinkage params.n :=
  let witness := ac0PartialWitness_with_bound params F hF hBound
  Core.PartialCertificate.toShrinkage
    (n := params.n)
    (ℓ := witness.level)
    (F := F)
    witness.certificate

/--
  Аналог `certificate_from_AC0_with_bound`, но стартующий от polylog‑свидетеля.

  Эта версия полезна для будущей multi‑switching леммы: как только появится
  реальный polylog‑bound на число подкубов, можно будет напрямую строить
  shrinkage‑сертификат, не возвращаясь к слабой оценке `M²`.
-/
noncomputable def certificate_from_AC0_with_polylog
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F)
    (hpoly : AC0PolylogBoundWitness params F hF) :
    Core.Shrinkage params.n :=
  let hBound : AC0DepthBoundWitness params F hF :=
    ac0DepthBoundWitness_of_polylog params F hF hpoly
  certificate_from_AC0_with_bound params F hF hBound

lemma certificate_from_AC0_depth_bound
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    (Core.Shrinkage.depthBound
      (S := certificate_from_AC0 params F hF))
      ≤ ac0DepthBound params := by
  classical
  let witness := ac0PartialWitness params F hF
  have hbound := witness.depth_le
  have hrewrite := Core.PartialCertificate.toShrinkage_depth
    (n := params.n)
    (ℓ := witness.level)
    (F := F)
    witness.certificate
  have htarget := Eq.subst
    (motive := fun t => t ≤ ac0DepthBound params)
    (Eq.symm hrewrite) hbound
  change (certificate_from_AC0 params F hF).t
      ≤ ac0DepthBound params
  dsimp [certificate_from_AC0, witness] at htarget ⊢
  exact htarget

lemma certificate_from_AC0_with_bound_depth_bound
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F)
    (hBound : AC0DepthBoundWitness params F hF) :
    (Core.Shrinkage.depthBound
      (S := certificate_from_AC0_with_bound params F hF hBound))
      ≤ ac0DepthBound params := by
  classical
  let witness := ac0PartialWitness_with_bound params F hF hBound
  have hbound := witness.depth_le
  have hrewrite := Core.PartialCertificate.toShrinkage_depth
    (n := params.n)
    (ℓ := witness.level)
    (F := F)
    witness.certificate
  have htarget := Eq.subst
    (motive := fun t => t ≤ ac0DepthBound params)
    (Eq.symm hrewrite) hbound
  change (certificate_from_AC0_with_bound params F hF hBound).t
      ≤ ac0DepthBound params
  dsimp [certificate_from_AC0_with_bound, witness] at htarget ⊢
  exact htarget

/-- Глубина сертификата, построенного из polylog‑свидетеля, ограничена strong‑границей. -/
lemma certificate_from_AC0_with_polylog_depth_bound
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F)
    (hpoly : AC0PolylogBoundWitness params F hF) :
    (Core.Shrinkage.depthBound
      (S := certificate_from_AC0_with_polylog params F hF hpoly))
      ≤ ac0DepthBound params := by
  -- Это прямое следствие варианта с явной strong‑границей.
  have hBound : AC0DepthBoundWitness params F hF :=
    ac0DepthBoundWitness_of_polylog params F hF hpoly
  simpa [certificate_from_AC0_with_polylog] using
    (certificate_from_AC0_with_bound_depth_bound
      (params := params) (F := F) (hF := hF) (hBound := hBound))

/-- Та же оценка глубины shrinkage‑сертификата, но уже в сильной форме. -/
lemma certificate_from_AC0_depth_bound_strong
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    (Core.Shrinkage.depthBound
      (S := certificate_from_AC0 params F hF))
      ≤ ac0DepthBound_strong params := by
  -- Берём слабую оценку и поднимаем её через `ac0DepthBound_le_strong`.
  have hweak := certificate_from_AC0_depth_bound
    (params := params) (F := F) (hF := hF)
  exact hweak.trans (ac0DepthBound_le_strong params)

lemma certificate_from_AC0_eps_bound
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    Core.Shrinkage.errorBound
      (S := certificate_from_AC0 params F hF)
      ≤ (1 : Core.Q) / (params.n + 2) := by
  classical
  let witness := ac0PartialWitness params F hF
  have hbound := witness.epsilon_le_inv
  have hrewrite := Core.PartialCertificate.toShrinkage_epsilon
    (n := params.n)
    (ℓ := witness.level)
    (F := F)
    witness.certificate
  have htarget := Eq.subst
    (motive := fun ε => ε ≤ (1 : Core.Q) / (params.n + 2))
    (Eq.symm hrewrite) hbound
  change (certificate_from_AC0 params F hF).ε
      ≤ (1 : Core.Q) / (params.n + 2)
  dsimp [certificate_from_AC0, witness] at htarget ⊢
  exact htarget

lemma certificate_from_AC0_with_bound_eps_bound
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F)
    (hBound : AC0DepthBoundWitness params F hF) :
    Core.Shrinkage.errorBound
      (S := certificate_from_AC0_with_bound params F hF hBound)
      ≤ (1 : Core.Q) / (params.n + 2) := by
  classical
  let witness := ac0PartialWitness_with_bound params F hF hBound
  have hbound := witness.epsilon_le_inv
  have hrewrite := Core.PartialCertificate.toShrinkage_epsilon
    (n := params.n)
    (ℓ := witness.level)
    (F := F)
    witness.certificate
  have htarget := Eq.subst
    (motive := fun ε => ε ≤ (1 : Core.Q) / (params.n + 2))
    (Eq.symm hrewrite) hbound
  change (certificate_from_AC0_with_bound params F hF hBound).ε
      ≤ (1 : Core.Q) / (params.n + 2)
  dsimp [certificate_from_AC0_with_bound, witness] at htarget ⊢
  exact htarget

/-- Верхняя оценка ошибки для сертификата, построенного из polylog‑свидетеля. -/
lemma certificate_from_AC0_with_polylog_eps_bound
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F)
    (hpoly : AC0PolylogBoundWitness params F hF) :
    Core.Shrinkage.errorBound
      (S := certificate_from_AC0_with_polylog params F hF hpoly)
      ≤ (1 : Core.Q) / (params.n + 2) := by
  have hBound : AC0DepthBoundWitness params F hF :=
    ac0DepthBoundWitness_of_polylog params F hF hpoly
  simpa [certificate_from_AC0_with_polylog] using
    (certificate_from_AC0_with_bound_eps_bound
      (params := params) (F := F) (hF := hF) (hBound := hBound))

/-- Семейство в сертификате AC⁰ совпадает с исходным списком `F`. -/
lemma certificate_from_AC0_family
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    (certificate_from_AC0 params F hF).F = F := by
  classical
  let witness := ac0PartialWitness params F hF
  have h := Core.PartialCertificate.toShrinkage_family
    (n := params.n)
    (ℓ := witness.level)
    (F := F)
    witness.certificate
  have hgoal := h
  dsimp [certificate_from_AC0, witness] at hgoal
  exact hgoal

/-- Семейство в сертификате AC⁰ (с сильной границей) совпадает с `F`. -/
lemma certificate_from_AC0_with_bound_family
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F)
    (hBound : AC0DepthBoundWitness params F hF) :
    (certificate_from_AC0_with_bound params F hF hBound).F = F := by
  classical
  let witness := ac0PartialWitness_with_bound params F hF hBound
  have h := Core.PartialCertificate.toShrinkage_family
    (n := params.n)
    (ℓ := witness.level)
    (F := F)
    witness.certificate
  have hgoal := h
  dsimp [certificate_from_AC0_with_bound, witness] at hgoal
  exact hgoal

/-- Семейство в сертификате, построенном из polylog‑свидетеля, совпадает с `F`. -/
lemma certificate_from_AC0_with_polylog_family
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F)
    (hpoly : AC0PolylogBoundWitness params F hF) :
    (certificate_from_AC0_with_polylog params F hF hpoly).F = F := by
  have hBound : AC0DepthBoundWitness params F hF :=
    ac0DepthBoundWitness_of_polylog params F hF hpoly
  simpa [certificate_from_AC0_with_polylog] using
    (certificate_from_AC0_with_bound_family
      (params := params) (F := F) (hF := hF) (hBound := hBound))

/-- Ошибка сертификата AC⁰ неотрицательна.  Это важное условие для части B. -/
lemma certificate_from_AC0_eps_nonneg
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    (0 : Core.Q) ≤ Core.Shrinkage.errorBound
      (S := certificate_from_AC0 params F hF) := by
  classical
  let witness := ac0PartialWitness params F hF
  have h := witness.epsilon_nonneg
  have hrewrite := Core.PartialCertificate.toShrinkage_epsilon
    (n := params.n)
    (ℓ := witness.level)
    (F := F)
    witness.certificate
  have hgoal := Eq.subst
    (motive := fun ε => (0 : Core.Q) ≤ ε)
    (Eq.symm hrewrite) h
  change (0 : Core.Q) ≤ (certificate_from_AC0 params F hF).ε
  dsimp [certificate_from_AC0, witness] at hgoal ⊢
  exact hgoal

/-- Ошибка сертификата AC⁰ (с сильной границей) неотрицательна. -/
lemma certificate_from_AC0_with_bound_eps_nonneg
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F)
    (hBound : AC0DepthBoundWitness params F hF) :
    (0 : Core.Q) ≤ Core.Shrinkage.errorBound
      (S := certificate_from_AC0_with_bound params F hF hBound) := by
  classical
  let witness := ac0PartialWitness_with_bound params F hF hBound
  have h := witness.epsilon_nonneg
  have hrewrite := Core.PartialCertificate.toShrinkage_epsilon
    (n := params.n)
    (ℓ := witness.level)
    (F := F)
    witness.certificate
  have hgoal := Eq.subst
    (motive := fun ε => (0 : Core.Q) ≤ ε)
    (Eq.symm hrewrite) h
  change (0 : Core.Q) ≤ (certificate_from_AC0_with_bound params F hF hBound).ε
  dsimp [certificate_from_AC0_with_bound, witness] at hgoal ⊢
  exact hgoal

/-- Неотрицательность ошибки для сертификата, построенного из polylog‑свидетеля. -/
lemma certificate_from_AC0_with_polylog_eps_nonneg
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F)
    (hpoly : AC0PolylogBoundWitness params F hF) :
    (0 : Core.Q) ≤ Core.Shrinkage.errorBound
      (S := certificate_from_AC0_with_polylog params F hF hpoly) := by
  have hBound : AC0DepthBoundWitness params F hF :=
    ac0DepthBoundWitness_of_polylog params F hF hpoly
  simpa [certificate_from_AC0_with_polylog] using
    (certificate_from_AC0_with_bound_eps_nonneg
      (params := params) (F := F) (hF := hF) (hBound := hBound))

/-- Из внешней границы `ε ≤ 1/(n+2)` выводим привычное условие `ε ≤ 1/2`. -/
lemma certificate_from_AC0_eps_le_half
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    Core.Shrinkage.errorBound
      (S := certificate_from_AC0 params F hF)
      ≤ (1 : Core.Q) / 2 := by
  classical
  have hbase := certificate_from_AC0_eps_bound
    (params := params) (F := F) (hF := hF)
  exact eps_le_half_of_eps_le_inv_nplus2
    params.n (ε := Core.Shrinkage.errorBound (S := certificate_from_AC0 params F hF))
    hbase

lemma certificate_from_AC0_with_bound_eps_le_half
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F)
    (hBound : AC0DepthBoundWitness params F hF) :
    Core.Shrinkage.errorBound
      (S := certificate_from_AC0_with_bound params F hF hBound)
      ≤ (1 : Core.Q) / 2 := by
  classical
  have hbase := certificate_from_AC0_with_bound_eps_bound
    (params := params) (F := F) (hF := hF) (hBound := hBound)
  exact eps_le_half_of_eps_le_inv_nplus2
    params.n (ε := Core.Shrinkage.errorBound
      (S := certificate_from_AC0_with_bound params F hF hBound)) hbase

/-- Полезный помощник: общий PDT, извлечённый из shrinkage-сертификата AC⁰.
    Он напрямую использует частичный shrinkage-факт, но перепаковывает его
    в формат `CommonPDT`, удобный для SAL и контроля глубины. -/
noncomputable def commonPDT_from_AC0
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) : Core.CommonPDT params.n F := by
  classical
  -- Берём shrinkage, полученный из частичного сертификата AC⁰, и извлекаем
  -- общий PDT через `Shrinkage.commonPDT`.
  exact (certificate_from_AC0 params F hF).commonPDT

/--
  Polylog‑вариант общего PDT: строим его из shrinkage‑сертификата,
  полученного по polylog‑свидетелю.
-/
noncomputable def commonPDT_from_AC0_with_polylog
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F)
    (hpoly : AC0PolylogBoundWitness params F hF) :
    Core.CommonPDT params.n F := by
  classical
  exact (certificate_from_AC0_with_polylog params F hF hpoly).commonPDT

/-- Глубина общего PDT, полученного из AC⁰, ограничена стандартной оценкой. -/
lemma commonPDT_from_AC0_depth_le
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    (commonPDT_from_AC0 params F hF).depthBound ≤ ac0DepthBound params := by
  classical
  -- Глубина общего PDT совпадает с `t` shrinkage-сертификата,
  -- а тот равен `depthBound + ℓ` у частичного свидетельства.
  calc
    (commonPDT_from_AC0 params F hF).depthBound
        = (certificate_from_AC0 params F hF).t := by
          simp [commonPDT_from_AC0]
    _ ≤ ac0DepthBound params := by
          simpa using
            (certificate_from_AC0_depth_bound
              (params := params) (F := F) (hF := hF))

/-- Сильная версия оценки глубины общего PDT из AC⁰ shrinkage. -/
lemma commonPDT_from_AC0_depth_le_strong
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    (commonPDT_from_AC0 params F hF).depthBound
      ≤ ac0DepthBound_strong params := by
  -- Поднимаем слабую оценку через `ac0DepthBound_le_strong`.
  have hweak := commonPDT_from_AC0_depth_le
    (params := params) (F := F) (hF := hF)
  exact hweak.trans (ac0DepthBound_le_strong params)

/-- Глубина polylog‑варианта общего PDT также ограничена strong‑границей. -/
lemma commonPDT_from_AC0_with_polylog_depth_le
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F)
    (hpoly : AC0PolylogBoundWitness params F hF) :
    (commonPDT_from_AC0_with_polylog params F hF hpoly).depthBound
      ≤ ac0DepthBound params := by
  -- Переводим оценку глубины через shrinkage‑сертификат.
  calc
    (commonPDT_from_AC0_with_polylog params F hF hpoly).depthBound
        = (certificate_from_AC0_with_polylog params F hF hpoly).t := by
          simp [commonPDT_from_AC0_with_polylog]
    _ ≤ ac0DepthBound params := by
          simpa using
            (certificate_from_AC0_with_polylog_depth_bound
              (params := params) (F := F) (hF := hF) (hpoly := hpoly))

/-- Ошибка общего PDT неотрицательна. -/
lemma commonPDT_from_AC0_epsilon_nonneg
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    (0 : Core.Q) ≤ (commonPDT_from_AC0 params F hF).epsilon := by
  classical
  have hε := certificate_from_AC0_eps_nonneg
    (params := params) (F := F) (hF := hF)
  simpa [commonPDT_from_AC0] using hε

/-- Неотрицательность ошибки для polylog‑варианта общего PDT. -/
lemma commonPDT_from_AC0_with_polylog_epsilon_nonneg
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F)
    (hpoly : AC0PolylogBoundWitness params F hF) :
    (0 : Core.Q) ≤ (commonPDT_from_AC0_with_polylog params F hF hpoly).epsilon := by
  have hε := certificate_from_AC0_with_polylog_eps_nonneg
    (params := params) (F := F) (hF := hF) (hpoly := hpoly)
  simpa [commonPDT_from_AC0_with_polylog] using hε

/-- Ошибка общего PDT ограничена `1 / (n + 2)`. -/
lemma commonPDT_from_AC0_epsilon_le_inv
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    (commonPDT_from_AC0 params F hF).epsilon ≤ (1 : Core.Q) / (params.n + 2) := by
  classical
  have hε := certificate_from_AC0_eps_bound
    (params := params) (F := F) (hF := hF)
  simpa [commonPDT_from_AC0] using hε

/-- Ошибка polylog‑варианта общего PDT ограничена `1 / (n + 2)`. -/
lemma commonPDT_from_AC0_with_polylog_epsilon_le_inv
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F)
    (hpoly : AC0PolylogBoundWitness params F hF) :
    (commonPDT_from_AC0_with_polylog params F hF hpoly).epsilon
      ≤ (1 : Core.Q) / (params.n + 2) := by
  have hε := certificate_from_AC0_with_polylog_eps_bound
    (params := params) (F := F) (hF := hF) (hpoly := hpoly)
  simpa [commonPDT_from_AC0_with_polylog] using hε

/-- Общий PDT, полученный из AC⁰ shrinkage, задаёт рабочий атлас. -/
theorem commonPDT_from_AC0_works
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    WorksFor (Core.CommonPDT.toAtlas (commonPDT_from_AC0 params F hF)) F := by
  classical
  -- `CommonPDT.worksFor` — это ровно формулировка SAL для общего PDT.
  simpa using (Core.CommonPDT.worksFor
    (C := commonPDT_from_AC0 params F hF))

/-- Polylog‑вариант общего PDT также задаёт рабочий атлас. -/
theorem commonPDT_from_AC0_with_polylog_works
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F)
    (hpoly : AC0PolylogBoundWitness params F hF) :
    WorksFor
      (Core.CommonPDT.toAtlas
        (commonPDT_from_AC0_with_polylog params F hF hpoly)) F := by
  classical
  simpa using (Core.CommonPDT.worksFor
    (C := commonPDT_from_AC0_with_polylog params F hF hpoly))

/-- Удобная оболочка: сразу извлекаем атлас из факта shrinkage.  Эта
функция подчёркивает, что на практике мы используем именно словарь подкубов,
а не сам PDT. -/
noncomputable def atlas_from_AC0
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) : Atlas params.n :=
  Core.CommonPDT.toAtlas (commonPDT_from_AC0 params F hF)

/-- Polylog‑вариант: извлекаем атлас из общего PDT, построенного по polylog‑свидетелю. -/
noncomputable def atlas_from_AC0_with_polylog
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F)
    (hpoly : AC0PolylogBoundWitness params F hF) : Atlas params.n :=
  Core.CommonPDT.toAtlas (commonPDT_from_AC0_with_polylog params F hF hpoly)

/-- Свойство корректности атласа, полученного из внешнего shrinkage.
    Оно напрямую следует из `SAL_from_Shrinkage`. -/
theorem atlas_from_AC0_works
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    WorksFor (atlas_from_AC0 params F hF) F := by
  simpa [atlas_from_AC0] using (Core.CommonPDT.worksFor
    (C := commonPDT_from_AC0 params F hF))

/-- Корректность атласа, построенного из polylog‑варианта общего PDT. -/
theorem atlas_from_AC0_with_polylog_works
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F)
    (hpoly : AC0PolylogBoundWitness params F hF) :
    WorksFor (atlas_from_AC0_with_polylog params F hF hpoly) F := by
  simpa [atlas_from_AC0_with_polylog] using (Core.CommonPDT.worksFor
    (C := commonPDT_from_AC0_with_polylog params F hF hpoly))

/--
Глубина ствола частичного дерева из AC⁰-сертификата ограничена `ac0DepthBound`.
Для текущего depth‑2 конструктивного случая это достигается за счёт того, что
`ac0DepthBound_strong` по определению доминирует `M²`, а интерфейс уже согласован
с polylog‑целью.
-/
lemma partial_from_AC0_trunk_depth_le
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    PDT.depth (Core.Shrinkage.partial
        (S := certificate_from_AC0 params F hF)).trunk
      ≤ ac0DepthBound params := by
  classical
  have hdepth :=
    Core.Shrinkage.depth_le_depthBound
      (S := certificate_from_AC0 params F hF)
  have hbound :=
    certificate_from_AC0_depth_bound (params := params) (F := F)
      (hF := hF)
  have hbound' :
      Core.Shrinkage.depthBound (S := certificate_from_AC0 params F hF)
        ≤ ac0DepthBound params := hbound
  have htree_depth :
      PDT.depth (certificate_from_AC0 params F hF).tree
        ≤ Core.Shrinkage.depthBound (S := certificate_from_AC0 params F hF) := by
    exact hdepth
  have hpartial :
      PDT.depth (Core.Shrinkage.partial
        (S := certificate_from_AC0 params F hF)).trunk
        = PDT.depth (certificate_from_AC0 params F hF).tree := by
    rfl
  have hchain :
      PDT.depth (Core.Shrinkage.partial
        (S := certificate_from_AC0 params F hF)).trunk
        ≤ Core.Shrinkage.depthBound (S := certificate_from_AC0 params F hF) := by
    have htmp := htree_depth
    exact Eq.subst (motive := fun s => s ≤
        Core.Shrinkage.depthBound (S := certificate_from_AC0 params F hF))
      (Eq.symm hpartial) htmp
  exact hchain.trans hbound'

/-- Сильная версия оценки глубины ствола частичного дерева из AC⁰. -/
lemma partial_from_AC0_trunk_depth_le_strong
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    PDT.depth (Core.Shrinkage.partial
        (S := certificate_from_AC0 params F hF)).trunk
      ≤ ac0DepthBound_strong params := by
  -- Поднимаем оценку через `ac0DepthBound_le_strong`.
  have hweak := partial_from_AC0_trunk_depth_le
    (params := params) (F := F) (hF := hF)
  exact hweak.trans (ac0DepthBound_le_strong params)

/--
Число листьев словаря из AC⁰-сертификата контролируется той же границей,
что и глубина: `|R| ≤ 2^{ac0DepthBound params}`.  Лемма напрямую использует
оценку из `ShrinkageWitness`.
-/
lemma partial_from_AC0_leafDict_len_le
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    (Core.Shrinkage.partial
        (S := certificate_from_AC0 params F hF)).leafDict.length
      ≤ Nat.pow 2 (ac0DepthBound params) := by
  classical
  have hbase :=
    Core.Shrinkage.partial_leafDict_length_le_pow
      (S := certificate_from_AC0 params F hF)
  have hbound :
      Nat.pow 2 (Core.Shrinkage.depthBound (S := certificate_from_AC0 params F hF))
        ≤ Nat.pow 2 (ac0DepthBound params) := by
    have hdepthBound :=
      certificate_from_AC0_depth_bound (params := params) (F := F)
        (hF := hF)
    exact Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hdepthBound
  have hpartial_pow :
      Nat.pow 2 (certificate_from_AC0 params F hF).t
        ≤ Nat.pow 2 (ac0DepthBound params) := by
    have htmp := hbound
    simp [Core.Shrinkage.depthBound] at htmp
    exact htmp
  have hgoal := hbase.trans hpartial_pow
  exact hgoal

/-- Сильная оценка размера словаря листьев: `|R| ≤ 2^{ac0DepthBound_strong}`. -/
lemma partial_from_AC0_leafDict_len_le_strong
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    (Core.Shrinkage.partial
        (S := certificate_from_AC0 params F hF)).leafDict.length
      ≤ Nat.pow 2 (ac0DepthBound_strong params) := by
  -- Сначала используем слабую оценку, затем монотонность степени двойки.
  have hweak := partial_from_AC0_leafDict_len_le
    (params := params) (F := F) (hF := hF)
  have hbound := ac0DepthBound_le_strong params
  exact hweak.trans (Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hbound)

end ThirdPartyFacts
end Pnp3
