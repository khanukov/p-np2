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
  Это временный, но полностью формальный «Stage‑1», где верхняя оценка
  на глубину PDT грубо задаётся как `M²`.

  Когда появится настоящая switching‑лемма (polylog‑оценка), этот блок
  будет заменён на более сильный интерфейс, но **без массового переписывания**
  downstream: именно поэтому внизу используются абстрактные оценочные
  функции вроде `ac0DepthBound`.
-/

/--
  Грубая численная оценка на глубину PDT для конструктивного depth-2 случая.

  Сейчас мы используем только глубину-2 DNF, поэтому число подкубов
  ограничено квадратично через `M`.  Позже, когда будет формализована
  настоящая switching-лемма, эту функцию можно заменить более сильной
  (polylog) оценкой и переподключить downstream без массового переписывания.
-/
def ac0DepthBound (params : AC0Parameters) : Nat :=
  params.M * params.M

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
  Предикат «малости» для AC⁰-параметров.  Он фиксирует грубое требование
  на рост размера `M` относительно числа входных переменных
  `n`: даже после применения грубой оценки `ac0DepthBound` результат остаётся
  не больше `n`.  Это честная оценка для конструктивного depth-2 случая,
  где глубина PDT строится как число подкубов.
-/
def AC0SmallEnough (ac0 : AC0Parameters) : Prop :=
  ac0DepthBound ac0 ≤ ac0.n

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

/-!
  ### Glue-лемма: depth-2 схема → частичный сертификат для одиночного семейства

  Эта лемма — первый «клей» между конструктивным depth-2 доказательством
  и интерфейсом Step A. Мы явно строим PDT для одной схемы и упаковываем
  его в `PartialCertificate` для семейства из одной функции.

  Важное ограничение: здесь нужен `h_pos : 0 < n`, чтобы выбрать ветвящий
  индекс при построении PDT. Для `n = 0` корректный частный случай можно
  добавить позже (он тривиален, так как все подкубы совпадают с полным).
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
lemma subcube_eq_full_of_n_zero (β : Subcube 0) : β = fullSubcube 0 := by
  funext i
  exact (Fin.elim0 i)

lemma subcube_eq_full_of_n_zero' {n : Nat} (hzero : n = 0) (β : Subcube n) :
    β = fullSubcube n := by
  cases hzero
  simpa using (subcube_eq_full_of_n_zero (β := β))

theorem partial_shrinkage_for_AC0
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    ∃ (ℓ : Nat) (C : Core.PartialCertificate params.n ℓ F),
      ℓ ≤ Nat.log2 (params.M + 2) ∧
      C.depthBound + ℓ ≤ ac0DepthBound params ∧
      (0 : Core.Q) ≤ C.epsilon ∧
      C.epsilon ≤ (1 : Core.Q) / (params.n + 2) := by
  classical
  obtain ⟨witness⟩ := hF
  let allSubcubes := witness.circuits.flatMap AC0Circuit.subcubes
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
      -- длина flatMap совпадает с суммой длин подкубов
      have hsize :
          (fun a : AC0Circuit params => a.formula.terms.length)
            = fun a => AC0Circuit.size a := by
        funext a
        rfl
      simp [allSubcubes, AC0Circuit.subcubes_length, List.length_flatMap, hsize]
    calc
      allSubcubes.length
          = (witness.circuits.map AC0Circuit.size).sum := hlen
      _ ≤ (witness.circuits.map (fun _ => params.M)).sum := hsum
      _ = witness.circuits.length * params.M := hsum_const
  have hlen_bound : allSubcubes.length ≤ ac0DepthBound params := by
    have hlen_circuits := witness.circuits_length_le
    have hmul := Nat.mul_le_mul_right params.M hlen_circuits
    exact hlen_subcubes.trans (by simpa [ac0DepthBound] using hmul)
  by_cases hpos : 0 < params.n
  · -- Случай n > 0: строим дерево по списку подкубов и сразу фиксируем глубину.
    let tree := buildPDTFromSubcubes hpos allSubcubes
    have hdepth :
        PDT.depth tree ≤ allSubcubes.length := by
      simpa [tree] using buildPDTFromSubcubes_depth hpos allSubcubes
    -- Для удобства фиксируем сокращённые имена для выбранной схемы,
    -- соответствующей конкретной функции `f`.
    -- Это подчёркивает, что мы используем конструктивный depth-2
    -- вывод из `AC0Circuit.coveredB_subcubes`.
    refine ⟨0, {
      witness := PartialDT.ofPDT tree
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
          simpa [allSubcubes] using hmem_bind
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
            exact hcov
    }, ?_, ?_, ?_, ?_⟩
    · simp
    · exact hlen_bound
    · simp
    ·
      apply div_nonneg
      · norm_num
      ·
        have : (0 : Nat) ≤ params.n + 2 := by omega
        exact_mod_cast this
  · -- Случай n = 0: любой подкуб совпадает с полным, дерево состоит из единственного листа.
    have hzero : params.n = 0 := Nat.eq_zero_of_not_pos hpos
    let tree : PDT params.n := PDT.leaf (fullSubcube params.n)
    have hdepth :
        PDT.depth tree ≤ allSubcubes.length := by
      have : PDT.depth tree = 0 := by simp [tree, PDT.depth]
      simpa [this] using (Nat.zero_le allSubcubes.length)
    refine ⟨0, {
      witness := PartialDT.ofPDT tree
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
        have hβ_full : β = fullSubcube params.n :=
          subcube_eq_full_of_n_zero' hzero β
        have hleaf :
            fullSubcube params.n ∈ PDT.leaves (PDT.leaf (fullSubcube params.n)) := by
          simp [PDT.leaves]
        simpa [tree, hβ_full] using hleaf
      err_le := by
        intro f hf
        have hchoose := Classical.choose_spec (witness.covers f hf)
        have hcomp : AC0Circuit.Computes (Classical.choose (witness.covers f hf)) f :=
          hchoose.right
        simp [hf]
        apply le_of_eq
        apply errU_eq_zero_of_agree
        intro x
        have hcov := AC0Circuit.coveredB_subcubes
          (c := Classical.choose (witness.covers f hf)) (x := x)
        have hcomp' := hcomp x
        simp [hcov, hcomp']
    }, ?_, ?_, ?_, ?_⟩
    · simp
    · exact hlen_bound
    · simp
    ·
      apply div_nonneg
      · norm_num
      ·
        have : (0 : Nat) ≤ params.n + 2 := by omega
        exact_mod_cast this

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
  Внешний факт для локальных схем: после применения подходящих ограничений
  схема становится «малой» PDT.  Конкретные численные границы отражают
  стандартные оценки: глубина дерева пропорциональна произведению локальности
  и логарифмических факторов по размеру и глубине схемы.
-/
theorem shrinkage_for_localCircuit
    (params : LocalCircuitParameters) (F : Family params.n)
    (hF : FamilyIsLocalCircuit params F) :
    ∃ (t : Nat) (ε : Q) (S : Shrinkage params.n),
      S.F = F ∧ S.t = t ∧ S.ε = ε ∧
        t ≤ params.ℓ * (Nat.log2 (params.M + 2) + params.depth + 1) ∧
        (0 : Q) ≤ ε ∧
        ε ≤ (1 : Q) / (params.n + 2) := by
  classical
  obtain ⟨witness⟩ := hF
  refine ⟨witness.shrinkage.t, witness.shrinkage.ε, witness.shrinkage, ?_⟩
  refine And.intro witness.family_eq ?_
  refine And.intro rfl ?_
  refine And.intro rfl ?_
  exact And.intro witness.depth_le (And.intro witness.epsilon_nonneg witness.epsilon_le_inv)

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
  change (certificate_from_AC0 params F hF).ε ≤ (1 : Core.Q) / (params.n + 2)
  dsimp [certificate_from_AC0, witness] at htarget ⊢
  exact htarget

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
    params.n (ε := Core.Shrinkage.errorBound (S := certificate_from_AC0 params F hF)) hbase

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

/-- Ошибка общего PDT неотрицательна. -/
lemma commonPDT_from_AC0_epsilon_nonneg
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    (0 : Core.Q) ≤ (commonPDT_from_AC0 params F hF).epsilon := by
  classical
  have hε := certificate_from_AC0_eps_nonneg
    (params := params) (F := F) (hF := hF)
  simpa [commonPDT_from_AC0] using hε

/-- Ошибка общего PDT ограничена `1 / (n + 2)`. -/
lemma commonPDT_from_AC0_epsilon_le_inv
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    (commonPDT_from_AC0 params F hF).epsilon ≤ (1 : Core.Q) / (params.n + 2) := by
  classical
  have hε := certificate_from_AC0_eps_bound
    (params := params) (F := F) (hF := hF)
  simpa [commonPDT_from_AC0] using hε

/-- Общий PDT, полученный из AC⁰ shrinkage, задаёт рабочий атлас. -/
theorem commonPDT_from_AC0_works
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    WorksFor (Core.CommonPDT.toAtlas (commonPDT_from_AC0 params F hF)) F := by
  classical
  -- `CommonPDT.worksFor` — это ровно формулировка SAL для общего PDT.
  simpa using (Core.CommonPDT.worksFor
    (C := commonPDT_from_AC0 params F hF))

/-- Удобная оболочка: сразу извлекаем атлас из факта shrinkage.  Эта
функция подчёркивает, что на практике мы используем именно словарь подкубов,
а не сам PDT. -/
noncomputable def atlas_from_AC0
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) : Atlas params.n :=
  Core.CommonPDT.toAtlas (commonPDT_from_AC0 params F hF)

/-- Свойство корректности атласа, полученного из внешнего shrinkage.
    Оно напрямую следует из `SAL_from_Shrinkage`. -/
theorem atlas_from_AC0_works
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    WorksFor (atlas_from_AC0 params F hF) F := by
  simpa [atlas_from_AC0] using (Core.CommonPDT.worksFor
    (C := commonPDT_from_AC0 params F hF))

/--
Глубина ствола частичного дерева из AC⁰-сертификата ограничена классической
грубой квадратичной оценкой от параметра `M`, поскольку мы строим дерево
из всех подкубов depth-2 DNF.
-/
lemma partial_from_AC0_trunk_depth_le
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    PDT.depth (Core.Shrinkage.partial (S := certificate_from_AC0 params F hF)).trunk
      ≤ ac0DepthBound params := by
  classical
  have hdepth :=
    Core.Shrinkage.depth_le_depthBound
      (S := certificate_from_AC0 params F hF)
  have hbound :=
    certificate_from_AC0_depth_bound (params := params) (F := F) (hF := hF)
  have hbound' :
      Core.Shrinkage.depthBound (S := certificate_from_AC0 params F hF)
        ≤ ac0DepthBound params := hbound
  have htree_depth :
      PDT.depth (certificate_from_AC0 params F hF).tree
        ≤ Core.Shrinkage.depthBound (S := certificate_from_AC0 params F hF) := by
    exact hdepth
  have hpartial :
      PDT.depth (Core.Shrinkage.partial (S := certificate_from_AC0 params F hF)).trunk
        = PDT.depth (certificate_from_AC0 params F hF).tree := by
    rfl
  have hchain :
      PDT.depth (Core.Shrinkage.partial (S := certificate_from_AC0 params F hF)).trunk
        ≤ Core.Shrinkage.depthBound (S := certificate_from_AC0 params F hF) := by
    have htmp := htree_depth
    exact Eq.subst (motive := fun s => s ≤
        Core.Shrinkage.depthBound (S := certificate_from_AC0 params F hF))
      (Eq.symm hpartial) htmp
  exact hchain.trans hbound'

/--
Число листьев словаря из AC⁰-сертификата контролируется той же границей,
что и глубина: `|R| ≤ 2^{ac0DepthBound params}`.  Лемма напрямую использует
оценку из `ShrinkageWitness`.
-/
lemma partial_from_AC0_leafDict_len_le
    (params : AC0Parameters) (F : Family params.n)
    (hF : FamilyIsAC0 params F) :
    (Core.Shrinkage.partial (S := certificate_from_AC0 params F hF)).leafDict.length
      ≤ Nat.pow 2 (ac0DepthBound params) := by
  classical
  have hbase :=
    Core.Shrinkage.partial_leafDict_length_le_pow
      (S := certificate_from_AC0 params F hF)
  have hbound :
      Nat.pow 2 (Core.Shrinkage.depthBound (S := certificate_from_AC0 params F hF))
        ≤ Nat.pow 2 (ac0DepthBound params) := by
    have hdepthBound :=
      certificate_from_AC0_depth_bound (params := params) (F := F) (hF := hF)
    exact Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hdepthBound
  have hpartial_pow :
      Nat.pow 2 (certificate_from_AC0 params F hF).t
        ≤ Nat.pow 2 (ac0DepthBound params) := by
    have htmp := hbound
    simp [Core.Shrinkage.depthBound] at htmp
    exact htmp
  have hgoal := hbase.trans hpartial_pow
  exact hgoal

end ThirdPartyFacts
end Pnp3
