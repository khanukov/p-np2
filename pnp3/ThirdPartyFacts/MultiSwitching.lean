import Core.ShrinkageWitness
import ThirdPartyFacts.RandomRestriction
import ThirdPartyFacts.Depth1_Switching

namespace Pnp3
namespace ThirdPartyFacts
namespace MultiSwitching

/--
  Удобные числовые функции для выбора параметров multi-switching.  Выносим их в
  отдельный раздел, чтобы дальнейшие доказательства могли ссылаться на
  стандартные оценки без повторного разворачивания `Nat.min`, `Nat.log2` и
  степеней. -/
section ParameterSelection

/-- Логарифмический бюджет `log₂ (M + 2)`, используемый в классических оценках. -/
@[simp] def logBudget (M : Nat) : Nat := Nat.log2 (M + 2)

/--
  Число осевых переменных, фиксируемых в стволе частичного PDT: `ℓ = min(log₂(M+2), n)`.
  Такое определение гарантирует одновременно `ℓ ≤ n` и `ℓ ≤ log₂(M+2)`.
-/
@[simp] def axisLength (n M : Nat) : Nat := min (logBudget M) n

/--
  Верхняя граница на суммарную глубину ствола и хвостов:
  `(log₂ (M + 2))^(d + 1)`.  Она совпадает с классическим выражением в
  формулировке switching-леммы для AC⁰.
-/
@[simp] def depthBudget (M d : Nat) : Nat := Nat.pow (logBudget M) (d + 1)

lemma axisLength_le_n (n M : Nat) : axisLength n M ≤ n := by
  have := Nat.min_le_right (logBudget M) n
  simpa [axisLength]

lemma axisLength_le_log (n M : Nat) : axisLength n M ≤ logBudget M := by
  have := Nat.min_le_left (logBudget M) n
  simpa [axisLength]

lemma depthBudget_succ (M d : Nat) : depthBudget M (d + 1)
    = depthBudget M d * logBudget M := by
  classical
  simp [depthBudget, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

@[simp] lemma depthBudget_zero (M : Nat) : depthBudget M 0 = logBudget M := by
  simp [depthBudget]

lemma depthBudget_le_depthBudget_succ (M d : Nat) :
    depthBudget M d ≤ depthBudget M (d + 1) := by
  classical
  cases hlog : logBudget M with
  | zero =>
      -- База `logBudget = 0`: все значения равны нулю.
      simp [depthBudget, hlog]
  | succ k =>
      -- Для `logBudget = 1` получаем точное равенство.
      cases k with
      | zero =>
          simp [depthBudget, hlog]
      | succ k =>
          -- При `logBudget ≥ 2` умножение на `logBudget` увеличивает бюджет.
          have hpos : 1 ≤ logBudget M := by
            simpa [hlog] using Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k))
          have hmul : depthBudget M d ≤ depthBudget M d * logBudget M := by
            have : depthBudget M d * 1 ≤ depthBudget M d * logBudget M :=
              Nat.mul_le_mul_left _ hpos
            simpa using this
          simpa [depthBudget_succ, hlog, Nat.mul_comm] using hmul

/-- Возведение в степень монотонно по показателю для натуральных баз `≥ 1`. -/
lemma pow_le_pow_succ {a n : Nat} (ha : 1 ≤ a) :
    Nat.pow a n ≤ Nat.pow a (n + 1) := by
  have hmul := Nat.mul_le_mul_left (Nat.pow a n) ha
  simpa [Nat.pow_succ, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm]
    using hmul

/-- Любое натуральное число не превосходит своей степени `d + 1`. -/
lemma self_le_pow_succ (a d : Nat) : a ≤ Nat.pow a (d + 1) := by
  cases a with
  | zero =>
      simp
  | succ a =>
      cases a with
      | zero =>
          -- База `a = 1` даёт равенство `1 = 1^(_ + 1)`.
          simp
      | succ a =>
          -- Для баз `≥ 2` используем индукцию по показателю степени.
          have ha : 1 ≤ Nat.succ (Nat.succ a) :=
            Nat.succ_le_succ (Nat.zero_le (Nat.succ a))
          have hstep :
              Nat.succ (Nat.succ a)
                ≤ Nat.pow (Nat.succ (Nat.succ a)) (d + 1) := by
            induction d with
            | zero =>
                simp
            | succ d ih =>
                have hpow := pow_le_pow_succ (a := Nat.succ (Nat.succ a))
                  (n := d + 1) ha
                exact ih.trans hpow
          simpa using hstep

/-- Глубинный бюджет всегда не меньше выбранной длины оси. -/
lemma logBudget_le_depthBudget (M d : Nat) :
    logBudget M ≤ depthBudget M d := by
  classical
  simpa [depthBudget]
    using self_le_pow_succ (logBudget M) d

lemma axisLength_le_depthBudget (n M d : Nat) :
    axisLength n M ≤ depthBudget M d :=
  (axisLength_le_log (n := n) (M := M)).trans
    (logBudget_le_depthBudget (M := M) (d := d))

/--
  Комбинированная оценка для последующего индуктивного шага: при условии, что
  логарифмический бюджет не меньше двух, сумма длины оси и текущего глубинного
  бюджета не превосходит бюджета следующего уровня.  Интуитивно это отражает
  стандартный выбор параметров в доказательстве switching-леммы, где каждая
  новая итерация умножает глубину хвостов на `log₂ (M + 2)` и добавляет к ней
  ещё одну ось длины `ℓ`.
-/
lemma axisLength_add_depthBudget_le_depthBudget_succ
    (n M d : Nat) (hlog : 2 ≤ logBudget M) :
    axisLength n M + depthBudget M d ≤ depthBudget M (d + 1) := by
  classical
  -- Переписываем логарифмический бюджет через параметр `k + 1`.
  have hpos : 0 < logBudget M :=
    Nat.lt_of_lt_of_le (show 0 < 2 by decide) hlog
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  -- Из `2 ≤ k.succ` следует `1 ≤ k`.
  have hk_pos : 1 ≤ k := by
    have hk_succ : Nat.succ 1 ≤ Nat.succ k := by
      simpa [hk, Nat.succ_eq_add_one] using hlog
    exact Nat.succ_le_succ_iff.mp hk_succ
  -- Текущий глубинный бюджет не меньше логарифмического.
  have hdepth_ge : k.succ ≤ depthBudget M d := by
    simpa [hk] using logBudget_le_depthBudget (M := M) (d := d)
  -- Умножение на `k` (который ≥ 1) усиливает неравенство.
  have hmul_ge : k.succ * k ≤ depthBudget M d * k :=
    Nat.mul_le_mul_right _ hdepth_ge
  -- Благодаря `k ≥ 1` имеем `k.succ ≤ k.succ * k`.
  have hself_le : k.succ ≤ k.succ * k := by
    have hstep : k.succ * 1 ≤ k.succ * k :=
      Nat.mul_le_mul_left _ hk_pos
    simpa using hstep
  -- Совмещаем две оценки: `k.succ ≤ depthBudget * k`.
  have hsucc_le : k.succ ≤ depthBudget M d * k :=
    hself_le.trans hmul_ge
  -- Добавляем `depthBudget` к обеим сторонам и раскрываем правую часть.
  have hsucc_add : k.succ + depthBudget M d
      ≤ depthBudget M d * k.succ := by
    have := Nat.add_le_add_right hsucc_le (depthBudget M d)
    simpa [Nat.mul_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using this
  -- Переходим от `logBudget` к `k.succ` и добавляем оценку для `axisLength`.
  have haxis_add :
      axisLength n M + depthBudget M d ≤ k.succ + depthBudget M d := by
    exact Nat.add_le_add_right
      (axisLength_le_log (n := n) (M := M)) _
  have htotal :
      axisLength n M + depthBudget M d ≤ depthBudget M d * k.succ :=
    haxis_add.trans hsucc_add
  -- Возвращаемся к исходным обозначениям и применяем формулу для `depthBudget`.
  have hrewrite :
      axisLength n M + depthBudget M d ≤
        depthBudget M d * logBudget M := by
    simpa [hk] using htotal
  simpa [depthBudget_succ] using hrewrite

lemma axisLength_add_le_depthBudget_succ
    (n M d τ : Nat) (hlog : 2 ≤ logBudget M)
    (hτ : τ ≤ depthBudget M d) :
    axisLength n M + τ ≤ depthBudget M (d + 1) := by
  have hstep :=
    axisLength_add_depthBudget_le_depthBudget_succ
      (n := n) (M := M) (d := d) (hlog := hlog)
  have hτ' : axisLength n M + τ ≤ axisLength n M + depthBudget M d := by
    exact Nat.add_le_add_left hτ _
  exact hτ'.trans hstep

lemma depthBudget_le_of_le (M : Nat) {d e : Nat} (h : d ≤ e) :
    depthBudget M d ≤ depthBudget M e := by
  classical
  refine Nat.le_induction ?base (fun e _ ih => ih.trans (depthBudget_le_depthBudget_succ (M := M) (d := e))) h
  · exact le_rfl

end ParameterSelection

/--
  pnp3/ThirdPartyFacts/MultiSwitching.lean

  Начинаем формализовывать многослойную switching-лемму.  На данном этапе
  мы абстрагируем общую схему "выбор оси + локальные хвосты" в виде
  структуры `AxisWitness`.  Эта обёртка агрегирует все данные, необходимые
  для сборки частичного PDT через универсальный конструктор из
  `RandomRestriction`: саму ось, хвосты с ограниченной глубиной, локальные
  списки селекторов и глобальную оценку ошибки.

  В дальнейшем индуктивная часть доказательства будет производить такие
  свидетели для верхнего слоя схемы AC⁰, а приведённый здесь метод
  `toPartialCertificate` позволит мгновенно превращать их в объекты
  `Core.PartialCertificate`.
-/

open Core
open RandomRestriction

variable {n ℓ τ : Nat} {F : Family n}

/--
  Свидетель оси `AxisWitness` хранит полный набор данных, который требуется
  для построения частичного shrinkage-сертификата:

  * выбранную ось `axis` и соответствующие хвосты `tails` вместе с
    ограничением на их глубину `tail_depth_le`;
  * локальные селекторы `tailSelectors`, которые в каждом листе хвоста
    выбирают подкубы и гарантированно лежат в списке листьев хвоста;
  * глобальную ошибку `epsilon` и оценку `err_le`, полученную, например,
    из вероятностного анализа (глубина 1, объединение и т.д.).

  Такая упаковка позволяет отделить вероятностную часть доказательства от
  чисто технической сборки `PartialCertificate`.
-/
structure AxisWitness where
  /-- Ось (множество свободных переменных) для ствола частичного PDT. -/
  axis : Axis n ℓ
  /-- Для каждого листа оси задаём хвостовое PDT. -/
  tails : ∀ β, β ∈ Axis.leafList (n := n) (ℓ := ℓ) axis → PDT n
  /-- Ограничение глубины хвостов: все хвостовые PDT не глубже `τ`. -/
  tail_depth_le : ∀ β hβ, PDT.depth (tails β hβ) ≤ τ
  /-- Локальные селекторы, ассоциированные с каждым хвостом. -/
  tailSelectors : ∀ β, β ∈ Axis.leafList (n := n) (ℓ := ℓ) axis →
      (BitVec n → Bool) → List (Subcube n)
  /-- Любой выбранный подкуб действительно является листом соответствующего хвоста. -/
  tailSelectors_mem : ∀ {β} (hβ : β ∈ Axis.leafList (n := n) (ℓ := ℓ) axis)
      {f : BitVec n → Bool} {γ : Subcube n},
        γ ∈ tailSelectors β hβ f → γ ∈ PDT.leaves (tails β hβ)
  /-- Глобальная оценка ошибки, достижимая на основе локальных хвостов. -/
  epsilon : Q
  /-- Верхняя граница на ошибку аппроксимации, сформулированная через `errU`. -/
  err_le : ∀ {f : BitVec n → Bool}, f ∈ F →
      errU f (Axis.selectorsFromTails (n := n) (ℓ := ℓ) (A := axis)
        (tailSelectors := tailSelectors) f)
        ≤ epsilon

namespace AxisWitness

variable (W : AxisWitness (n := n) (ℓ := ℓ) (τ := τ) (F := F))

/--
  Глобальный список селекторов, полученный объединением локальных списков
  по всем листьям выбранной оси.  Именно он фигурирует в формулировке
  вероятностных оценок (`err_le`).
-/
@[simp] def globalSelectors (f : BitVec n → Bool) : List (Subcube n) :=
  Axis.selectorsFromTails (n := n) (ℓ := ℓ) (A := W.axis)
    (tailSelectors := W.tailSelectors) f

/--
  Преобразование свидетеля оси в частичный shrinkage-сертификат.  Отдельно
  указываем верхнюю границу на глубину ствола `depthBound` и условие
  `ℓ ≤ depthBound`, чтобы сохранить гибкость при выборе параметров на
  последующих этапах индукции.
-/
noncomputable def toPartialCertificate (depthBound : Nat)
    (hdepth : ℓ ≤ depthBound) : PartialCertificate n τ F := by
  classical
  refine Axis.buildPartialCertificateFromTailSelectors
    (n := n) (ℓ := ℓ) (τ := τ) (depthBound := depthBound)
    (A := W.axis) (tails := W.tails) (htails := W.tail_depth_le)
    (epsilon := W.epsilon) (tailSelectors := W.tailSelectors)
    (tailSelectors_mem := ?_) (err_le := ?_) (hdepth := hdepth)
  · intro β hβ f γ hγ
    exact W.tailSelectors_mem hβ hγ
  · intro f hf
    simpa [AxisWitness.globalSelectors] using
      W.err_le (n := n) (ℓ := ℓ) (τ := τ) (F := F) (f := f) hf

/--
  Уточняем выражение для глобальных селекторов в построенном частичном
  сертификате: они совпадают с `globalSelectors`, определёнными напрямую
  через данные `AxisWitness`.
-/
@[simp] lemma toPartialCertificate_selectors (depthBound : Nat)
    (hdepth : ℓ ≤ depthBound) (f : BitVec n → Bool) :
    (W.toPartialCertificate (n := n) (ℓ := ℓ) (τ := τ) (F := F)
        (depthBound := depthBound) (hdepth := hdepth)).selectors f
      = W.globalSelectors (n := n) (ℓ := ℓ) (τ := τ) (F := F) f := by
  classical
  simp [AxisWitness.toPartialCertificate, AxisWitness.globalSelectors]

/--
  Частный случай `toPartialCertificate`, который использует естественную
  оценку на глубину ствола `ℓ`.  В большинстве применений глубина оси
  совпадает с числом свободных переменных, поэтому такой вариант избавляет
  от лишнего аргумента `depthBound` и сразу возвращает готовый частичный
  сертификат.
-/
noncomputable def toPartialCertificateSelfBound :
    PartialCertificate n τ F := by
  classical
  exact W.toPartialCertificate (n := n) (ℓ := ℓ) (τ := τ) (F := F)
    (depthBound := ℓ) (hdepth := Nat.le_refl ℓ)

/-- Специализация леммы о селекторах для естественной границы `depthBound = ℓ`. -/
@[simp] lemma toPartialCertificateSelfBound_selectors (f : BitVec n → Bool) :
    (W.toPartialCertificateSelfBound (n := n) (ℓ := ℓ) (τ := τ) (F := F)).selectors f
      = W.globalSelectors (n := n) (ℓ := ℓ) (τ := τ) (F := F) f := by
  classical
  simpa [AxisWitness.toPartialCertificateSelfBound]
    using W.toPartialCertificate_selectors (n := n) (ℓ := ℓ) (τ := τ) (F := F)
      (depthBound := ℓ) (hdepth := Nat.le_refl ℓ) (f := f)

@[simp] lemma globalSelectors_def (f : BitVec n → Bool) :
    W.globalSelectors (n := n) (ℓ := ℓ) (τ := τ) (F := F) f
      = Axis.selectorsFromTails (n := n) (ℓ := ℓ) (A := W.axis)
          (tailSelectors := W.tailSelectors) f := rfl

lemma globalSelectors_mem_leaves {f : BitVec n → Bool} {β : Subcube n}
    (hβ : β ∈ W.globalSelectors (n := n) (ℓ := ℓ) (τ := τ) (F := F) f) :
    ∃ β₀ (hβ₀ : β₀ ∈ Axis.leafList (n := n) (ℓ := ℓ) W.axis),
      β ∈ PDT.leaves (W.tails β₀ hβ₀) := by
  classical
  have :=
    RandomRestriction.selectorsFromTails_mem_leaves (n := n) (ℓ := ℓ)
      (A := W.axis) (tails := W.tails)
      (tailSelectors := W.tailSelectors)
      (hsel := by
        intro β₀ hβ₀ f' γ hγ
        exact W.tailSelectors_mem (n := n) (ℓ := ℓ) (τ := τ) (F := F)
          (β := β₀) hβ₀ (f := f') hγ)
      (f := f) (β := β)
      (by simpa [AxisWitness.globalSelectors, globalSelectors_def]
        using hβ)
  simpa [AxisWitness.globalSelectors, globalSelectors_def] using this

lemma err_le_of_mem {f : BitVec n → Bool}
    (hf : f ∈ F) :
    errU f (W.globalSelectors (n := n) (ℓ := ℓ) (τ := τ) (F := F) f)
      ≤ W.epsilon := by
  simpa [AxisWitness.globalSelectors]
    using W.err_le (n := n) (ℓ := ℓ) (τ := τ) (F := F) (f := f) hf

/--
  Превращаем осевой свидетель в хвостовой сертификат.  Параметр
  `depthBound` контролирует выбранную верхнюю границу на глубину ствола, а
  `τTotal` — глобальный допуск на глубину хвоста при дальнейшей индукции.
  Неравенство `htotal` гарантирует, что суммарная глубина построенного
  сертификата не превышает `τTotal`.
-/
noncomputable def toTailCertificate (depthBound τTotal : Nat)
    (hdepth : ℓ ≤ depthBound)
    (htotal : depthBound + τ ≤ τTotal) :
    AxisTailSystem.TailCertificate (n := n) (τ := τTotal) (F := F) := by
  classical
  refine
    { level := τ
      certificate :=
        W.toPartialCertificate (n := n) (ℓ := ℓ) (τ := τ) (F := F)
          (depthBound := depthBound) (hdepth := hdepth)
      selectors_mem := ?selectors_mem
      depth_le := htotal }
  intro f γ hγ
  -- Переписываем селекторы через глобальное описание.
  have hglobal : γ ∈
      W.globalSelectors (n := n) (ℓ := ℓ) (τ := τ) (F := F) f := by
    simpa [AxisWitness.toPartialCertificate_selectors]
      using hγ
  obtain ⟨β₀, hβ₀, hleaf⟩ :=
    W.globalSelectors_mem_leaves (n := n) (ℓ := ℓ) (τ := τ) (F := F)
      (f := f) (β := γ) hglobal
  -- Этот лист присутствует в стволе построенного частичного PDT.
  have hβ₀_trunk :
      β₀ ∈ PDT.leaves
        (W.toPartialCertificate (n := n) (ℓ := ℓ) (τ := τ) (F := F)
          (depthBound := depthBound) (hdepth := hdepth)).witness.trunk := by
    simpa [AxisWitness.toPartialCertificate,
      RandomRestriction.partialDT, RandomRestriction.trunk,
      RandomRestriction.trunk_leaves]
      using hβ₀
  -- Хвост для `β₀` совпадает с исходным хвостом из `AxisWitness`.
  have htail_eq :
      (W.toPartialCertificate (n := n) (ℓ := ℓ) (τ := τ) (F := F)
          (depthBound := depthBound) (hdepth := hdepth)).witness
            .tails β₀ hβ₀_trunk
        = W.tails β₀ hβ₀ := by
    simp [AxisWitness.toPartialCertificate,
      RandomRestriction.partialDT]
  -- Переносим принадлежность листу хвоста на реализованное дерево.
  have htail_mem :
      γ ∈ PDT.leaves
        ((W.toPartialCertificate (n := n) (ℓ := ℓ) (τ := τ) (F := F)
            (depthBound := depthBound) (hdepth := hdepth)).witness
              .tails β₀ hβ₀_trunk) := by
    simpa [htail_eq]
      using hleaf
  -- Финальный шаг: лист хвоста остаётся листом после раскрытия.
  exact
    Core.PartialDT.mem_realize_of_mem_tail
      (Q := (W.toPartialCertificate (n := n) (ℓ := ℓ) (τ := τ) (F := F)
        (depthBound := depthBound) (hdepth := hdepth)).witness)
      hβ₀_trunk htail_mem

/--
  В построенном хвостовом сертификате локальная глубина `level` совпадает
  с параметром `τ`, переданным в `toTailCertificate`.  Лемма помогает при
  контроле суммарной глубины на индуктивных шагах.
-/
@[simp] lemma toTailCertificate_level (depthBound τTotal : Nat)
    (hdepth : ℓ ≤ depthBound)
    (htotal : depthBound + τ ≤ τTotal) :
    (W.toTailCertificate (n := n) (ℓ := ℓ) (τ := τ) (F := F)
        (depthBound := depthBound) (τTotal := τTotal)
        (hdepth := hdepth) (htotal := htotal)).level = τ := rfl

/--
  Сертификат, упакованный `toTailCertificate`, совпадает с частичным
  сертификатом, построенным из исходного `AxisWitness`.  Это позволяет
  переносить леммы о селекторах и ошибке без дополнительных переписок.
-/
@[simp] lemma toTailCertificate_certificate (depthBound τTotal : Nat)
    (hdepth : ℓ ≤ depthBound)
    (htotal : depthBound + τ ≤ τTotal) :
    (W.toTailCertificate (n := n) (ℓ := ℓ) (τ := τ) (F := F)
        (depthBound := depthBound) (τTotal := τTotal)
        (hdepth := hdepth) (htotal := htotal)).certificate
      = W.toPartialCertificate (n := n) (ℓ := ℓ) (τ := τ) (F := F)
          (depthBound := depthBound) (hdepth := hdepth) := rfl

/--
  Селекторы хвостового сертификата совпадают с глобальными селекторами,
  определёнными в `AxisWitness`.  Равенство удобно при проверке условий
  `hmismatch` и переносе оценок `errU`.
-/
@[simp] lemma toTailCertificate_selectors (depthBound τTotal : Nat)
    (hdepth : ℓ ≤ depthBound)
    (htotal : depthBound + τ ≤ τTotal) (f : BitVec n → Bool) :
    ((W.toTailCertificate (n := n) (ℓ := ℓ) (τ := τ) (F := F)
        (depthBound := depthBound) (τTotal := τTotal)
        (hdepth := hdepth) (htotal := htotal)).certificate.selectors f)
      = W.globalSelectors (n := n) (ℓ := ℓ) (τ := τ) (F := F) f := by
  classical
  simp [AxisWitness.toTailCertificate, AxisWitness.globalSelectors]

end AxisWitness

/--
  Глобальный набор хвостов, с которым мы будем работать при поиске удачной
  оси.  `AxisTailSystem` принимает на вход потенциальную ось `A` и
  возвращает:

  * решающие деревья для каждого листа `A` (`tails`),
  * доказательство того, что глубина этих деревьев не превосходит `τ`,
  * локальные селекторы, соответствующие построенным хвостам.

  Такие данные естественным образом возникают в вероятностной части
  switching‑леммы: для каждой оси нужно иметь возможность «подклеить» хвосты,
  полученные из индуктивного предположения (или локального анализа), и
  перевести оценку числа «плохих» листьев в bound на ошибку `errU`.
-/
structure AxisTailSystem
    (n ℓ τ : Nat) (F : Family n) where
  /-- Хвостовые деревья для каждого листа потенциальной оси. -/
  tails : ∀ A : Axis n ℓ,
      ∀ β, β ∈ Axis.leafList (n := n) (ℓ := ℓ) A → PDT n
  /-- Ограничение глубины хвостов: все деревья не глубже `τ`. -/
  tail_depth_le : ∀ A β hβ,
      PDT.depth (tails A β hβ) ≤ τ
  /-- Локальные селекторы, ассоциированные с каждым хвостом. -/
  tailSelectors : ∀ A : Axis n ℓ,
      ∀ β, β ∈ Axis.leafList (n := n) (ℓ := ℓ) A →
        (BitVec n → Bool) → List (Subcube n)
  /-- Любой выбранный подкуб действительно является листом соответствующего хвоста. -/
  tailSelectors_mem : ∀ {A : Axis n ℓ} {β} (hβ : β ∈ Axis.leafList (n := n) (ℓ := ℓ) A)
      {f : BitVec n → Bool} {γ : Subcube n},
        γ ∈ tailSelectors A β hβ f → γ ∈ PDT.leaves (tails A β hβ)

namespace AxisTailSystem

variable {F} (S : AxisTailSystem (n := n) (ℓ := ℓ) (τ := τ) (F := F))

/--
  Удобная обёртка над частичными сертификатами, которые предполагается
  использовать в качестве хвостов.  Каждый такой пакет содержит:

  * глубину локального параметра `level`,
  * сам частичный сертификат `certificate` с хвостами глубины `level`,
  * доказательство того, что раскрытое дерево (`certificate.witness.realize`)
    имеет глубину не больше `τ`.  Последнее условие позволит без труда
    встроить хвост в глобальную систему `AxisTailSystem`.
-/
structure TailCertificate
    (n τ : Nat) (F : Family n) where
  /-- Локальная глубина хвостов в частичном сертификате. -/
  level : Nat
  /-- Частичный сертификат, отвечающий за данный хвост. -/
  certificate : PartialCertificate n level F
  /-- Любой выбранный лист действительно принадлежит раскрытому хвосту. -/
  selectors_mem : ∀ {f : BitVec n → Bool} {γ : Subcube n},
      γ ∈ certificate.selectors f → γ ∈ PDT.leaves certificate.witness.realize
  /-- Раскрытое дерево не превышает глобальной глубины `τ`. -/
  depth_le : certificate.depthBound + level ≤ τ

/--
  Если мы располагаем хвостовым сертификатом, удовлетворяющим оценке на суммарную
  глубину `τ`, то ту же самую конструкцию можно рассматривать и в рамках любого
  большего бюджета `τ'`.  Функция `extend` переупаковывает существующие данные,
  не меняя сам частичный сертификат и списки селекторов, но обновляя проверку
  ограничения глубины через композицию `depth_le ≤ τ ≤ τ'`.

  Такая обёртка активно используется в индуктивных шагах multi-switching-леммы:
  хвосты, построенные на предыдущем уровне, автоматически удовлетворяют более
  строгим ограничениям, когда мы увеличиваем глобальный бюджет глубины.
-/
def TailCertificate.extend {τ τ' : Nat}
    (tc : TailCertificate (n := n) (τ := τ) (F := F))
    (hτ : τ ≤ τ') : TailCertificate (n := n) (τ := τ') (F := F) :=
  { level := tc.level
    certificate := tc.certificate
    selectors_mem := by
      intro f γ hγ
      exact tc.selectors_mem hγ
    depth_le := tc.depth_le.trans hτ }

@[simp] lemma TailCertificate.extend_level {τ τ' : Nat}
    (tc : TailCertificate (n := n) (τ := τ) (F := F)) (hτ : τ ≤ τ') :
    (tc.extend (n := n) (τ := τ) (F := F) hτ).level = tc.level := rfl

@[simp] lemma TailCertificate.extend_certificate {τ τ' : Nat}
    (tc : TailCertificate (n := n) (τ := τ) (F := F)) (hτ : τ ≤ τ') :
    (tc.extend (n := n) (τ := τ) (F := F) hτ).certificate = tc.certificate := rfl

@[simp] lemma TailCertificate.extend_selectors {τ τ' : Nat}
    (tc : TailCertificate (n := n) (τ := τ) (F := F)) (hτ : τ ≤ τ')
    (f : BitVec n → Bool) :
    (tc.extend (n := n) (τ := τ) (F := F) hτ).certificate.selectors f
      = tc.certificate.selectors f := rfl

/--
  Преобразуем семейство частичных сертификатов (по одной штуке на каждый лист
  и каждую потенциальную ось) в систему хвостов.  Конструкция устраняет
  необходимость вручную извлекать из сертификата дерево, селекторы и оценку
  на глубину: все данные уже присутствуют в `TailCertificate`.
-/
def ofTailCertificates
    (build : ∀ A : Axis n ℓ,
        ∀ β (hβ : β ∈ Axis.leafList (n := n) (ℓ := ℓ) A),
          TailCertificate (n := n) (τ := τ) (F := F)) :
    AxisTailSystem (n := n) (ℓ := ℓ) (τ := τ) (F := F) := by
  classical
  refine
    { tails := ?tails
      tail_depth_le := ?depth
      tailSelectors := ?selectors
      tailSelectors_mem := ?selectors_mem }
  · intro A β hβ
    -- Хвост — это раскрытое дерево частичного сертификата.
    exact (build A β hβ).certificate.witness.realize
  · intro A β hβ
    -- Комбинируем оценку на глубину хвоста с допуском из `TailCertificate`.
    have hcert := (build A β hβ).certificate
    have hdepth_core :
        PDT.depth (hcert.witness.realize)
          ≤ PDT.depth hcert.witness.trunk + (build A β hβ).level := by
      simpa using
        (Core.PartialDT.depth_realize_le (Q := hcert.witness))
    have hdepth_trunk :
        PDT.depth hcert.witness.trunk + (build A β hβ).level
          ≤ hcert.depthBound + (build A β hβ).level := by
      have := hcert.trunk_depth_le
      exact Nat.add_le_add_right this _
    have hcombine :=
      Nat.le_trans hdepth_core hdepth_trunk
    exact Nat.le_trans hcombine (build A β hβ).depth_le
  · intro A β hβ f
    -- Глобальные селекторы совпадают с селекторами локального сертификата.
    exact (build A β hβ).certificate.selectors f
  · intro A β hβ f γ hγ
    -- Необходимая принадлежность — часть данных `TailCertificate`.
    exact (build A β hβ).selectors_mem hγ

/--
  Для удобства переписываем хвост, извлечённый `ofTailCertificates`, через
  исходный частичный сертификат.
-/
@[simp] lemma ofTailCertificates_tails
    (build : ∀ A : Axis n ℓ,
        ∀ β (hβ : β ∈ Axis.leafList (n := n) (ℓ := ℓ) A),
          TailCertificate (n := n) (τ := τ) (F := F))
    (A : Axis n ℓ) {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n) (ℓ := ℓ) A) :
    (ofTailCertificates (n := n) (ℓ := ℓ) (τ := τ) (F := F) build)
        .tails A β hβ
      = (build A β hβ).certificate.witness.realize := rfl

/--
  Аналогичное уточнение для локальных селекторов.
-/
@[simp] lemma ofTailCertificates_tailSelectors
    (build : ∀ A : Axis n ℓ,
        ∀ β (hβ : β ∈ Axis.leafList (n := n) (ℓ := ℓ) A),
          TailCertificate (n := n) (τ := τ) (F := F))
    (A : Axis n ℓ) {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n) (ℓ := ℓ) A)
    (f : BitVec n → Bool) :
    (ofTailCertificates (n := n) (ℓ := ℓ) (τ := τ) (F := F) build)
        .tailSelectors A β hβ f
      = (build A β hβ).certificate.selectors f := rfl

/--
  По зафиксированной оси `A` строим `AxisWitness`, просто подставляя
  соответствующие хвосты и селекторы из системы `S`.  Неравенство на ошибку
  передаётся отдельным аргументом `herr`, поскольку оно обычно выводится из
  вероятностных оценок (например, леммы глубины 1 или индуктивного шага).
-/
def toAxisWitness (A : Axis n ℓ) (epsilon : Q)
    (herr : ∀ {f : BitVec n → Bool}, f ∈ F →
        errU f (Axis.selectorsFromTails (n := n) (ℓ := ℓ) (A := A)
          (tailSelectors := S.tailSelectors A) f)
          ≤ epsilon) :
    AxisWitness (n := n) (ℓ := ℓ) (τ := τ) (F := F) where
  axis := A
  tails := S.tails A
  tail_depth_le := S.tail_depth_le A
  tailSelectors := S.tailSelectors A
  tailSelectors_mem := by
    intro β hβ f γ hγ
    exact S.tailSelectors_mem (A := A) (β := β) hβ (f := f) (γ := γ) hγ
  epsilon := epsilon
  err_le := by
    intro f hf
    exact herr (f := f) hf

/--
  Полезная конструкция: если для каждой оси `A` уже известен явный
  `AxisWitness`, то из них можно собрать глобальную систему хвостов.
  Эта функция просто "забывает" глобальную ошибку и возвращает
  семейство хвостовых PDT и селекторов, готовое для дальнейшего
  применения вероятностных оценок и выбора подходящей оси.
-/
def ofWitnessFamily
    (build : ∀ A : Axis n ℓ,
        AxisWitness (n := n) (ℓ := ℓ) (τ := τ) (F := F)) :
    AxisTailSystem (n := n) (ℓ := ℓ) (τ := τ) (F := F) where
  tails A := (build A).tails
  tail_depth_le A := (build A).tail_depth_le
  tailSelectors A := (build A).tailSelectors
  tailSelectors_mem := by
    intro A β hβ f γ hγ
    exact (build A).tailSelectors_mem hβ hγ

/--
  Часто вероятностная часть доказательства предоставляет существование оси с
  нужной оценкой ошибки.  Эта вспомогательная конструкция извлекает такую ось
  и немедленно превращает её в `AxisWitness`, полагаясь на аксиому выбора.
  Предположение `hexists` должно содержать все вероятностные оценки в виде
  bound на `errU`.
-/
noncomputable def chooseWitness (epsilon : Q)
    (hexists : ∃ A : Axis n ℓ,
        ∀ {f : BitVec n → Bool}, f ∈ F →
          errU f (Axis.selectorsFromTails (n := n) (ℓ := ℓ) (A := A)
            (tailSelectors := S.tailSelectors A) f)
            ≤ epsilon) :
    AxisWitness (n := n) (ℓ := ℓ) (τ := τ) (F := F) := by
  classical
  obtain ⟨A, hA⟩ := hexists
  exact S.toAxisWitness (n := n) (ℓ := ℓ) (τ := τ) (F := F)
    (A := A) (epsilon := epsilon) (herr := by
      intro f hf
      exact hA (f := f) hf)

/-- В построенном свидетеле поле `epsilon` совпадает с параметром `epsilon`.
    Лемма упрощает дальнейшие переписывания при работе с `chooseWitness`. -/
@[simp] lemma chooseWitness_epsilon (epsilon : Q)
    (hexists : ∃ A : Axis n ℓ,
        ∀ {f : BitVec n → Bool}, f ∈ F →
          errU f (Axis.selectorsFromTails (n := n) (ℓ := ℓ) (A := A)
            (tailSelectors := S.tailSelectors A) f)
            ≤ epsilon) :
    (S.chooseWitness (n := n) (ℓ := ℓ) (τ := τ) (F := F)
        (epsilon := epsilon) (hexists := hexists)).epsilon = epsilon := rfl

/-- Хвостовые деревья в результате `chooseWitness` совпадают с исходной
    системой хвостов `S` для выбранной оси. -/
@[simp] lemma chooseWitness_tails (epsilon : Q)
    (hexists : ∃ A : Axis n ℓ,
        ∀ {f : BitVec n → Bool}, f ∈ F →
          errU f (Axis.selectorsFromTails (n := n) (ℓ := ℓ) (A := A)
            (tailSelectors := S.tailSelectors A) f)
            ≤ epsilon)
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n) (ℓ := ℓ)
        (S.chooseWitness (n := n) (ℓ := ℓ) (τ := τ) (F := F)
          (epsilon := epsilon) (hexists := hexists)).axis) :
    (S.chooseWitness (n := n) (ℓ := ℓ) (τ := τ) (F := F)
        (epsilon := epsilon) (hexists := hexists)).tails β hβ
      = S.tails
          (S.chooseWitness (n := n) (ℓ := ℓ) (τ := τ) (F := F)
            (epsilon := epsilon) (hexists := hexists)).axis β hβ := rfl

/-- Локальные селекторы, возвращаемые `chooseWitness`, берутся из исходной
    системы `S` на выбранной оси. -/
@[simp] lemma chooseWitness_tailSelectors (epsilon : Q)
    (hexists : ∃ A : Axis n ℓ,
        ∀ {f : BitVec n → Bool}, f ∈ F →
          errU f (Axis.selectorsFromTails (n := n) (ℓ := ℓ) (A := A)
            (tailSelectors := S.tailSelectors A) f)
            ≤ epsilon)
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n) (ℓ := ℓ)
        (S.chooseWitness (n := n) (ℓ := ℓ) (τ := τ) (F := F)
          (epsilon := epsilon) (hexists := hexists)).axis)
    (f : BitVec n → Bool) :
    (S.chooseWitness (n := n) (ℓ := ℓ) (τ := τ) (F := F)
        (epsilon := epsilon) (hexists := hexists)).tailSelectors β hβ f
      = S.tailSelectors
          (S.chooseWitness (n := n) (ℓ := ℓ) (τ := τ) (F := F)
            (epsilon := epsilon) (hexists := hexists)).axis β hβ f := rfl

end AxisTailSystem

open Core
open RandomRestriction

/--
  Удобное обозначение для семейства булевых функций, полученного из списка
  КНФ-формул.  Каждой формуле сопоставляем её булеву оценку `Core.CNF.eval`.
-/
@[simp] def cnfFamily {n w : Nat} (Fs : List (Core.CNF n w)) : Family n :=
  Fs.map (fun F => F.eval)

/--
  Уточняющее описание элементов `cnfFamily`: функция принадлежит семейству
  тогда и только тогда, когда она совпадает с оценкой одной из исходных
  формул из списка `Fs`.
-/
lemma mem_cnfFamily_iff {n w : Nat} {Fs : List (Core.CNF n w)}
    {f : BitVec n → Bool} :
    f ∈ cnfFamily (Fs := Fs) ↔ ∃ F ∈ Fs, f = F.eval := by
  classical
  unfold cnfFamily
  constructor
  · intro hf
    obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hf
    exact ⟨F, hF, rfl⟩
  · intro h
    rcases h with ⟨F, hF, rfl⟩
    exact List.mem_map.mpr ⟨F, hF, rfl⟩

/--
  Сведение объединённой оценки глубины 1 (`exists_axis_errU_le_list`) к
  конструктивному свидетелю `AxisWitness`.  Предполагается, что система
  хвостов `S` уже снабжена подходящими локальными селекторами для каждой
  оси, а вероятность «плохих» рестрикций контролируется числом `badBound`.

  На выходе получаем `AxisWitness` для семейства функций `Fs.map eval`
  с ошибкой `badBound / 2^ℓ`.
-/
noncomputable def AxisTailSystem.axisWitnessFromCNFList
    {n ℓ τ w t : Nat}
    (Fs : List (Core.CNF n w))
    (S : AxisTailSystem (n := n) (ℓ := ℓ) (τ := τ)
      (F := cnfFamily (Fs := Fs)))
    (hsubset : ∀ {F : Core.CNF n w}, F ∈ Fs →
        Depth1Switching.badSet (n := n) (ℓ := ℓ) (w := w) F t
          ⊆ Depth1Switching.formulaBadFamily
              (n := n) (ℓ := ℓ) (w := w) F t)
    (hℓn : ℓ ≤ n) (htℓ : t ≤ ℓ) (htw : t ≤ w)
    (p : ℝ≥0∞)
    (hp :
      ((1 : ℝ≥0∞) / (2 ^ n : ℝ≥0∞))
          * (Nat.choose w t : ℝ≥0∞)
          * (((ℓ : ℝ≥0∞) / (n - ℓ + 1 : ℝ≥0∞)) * (2 : ℝ≥0∞)) ^ t
          * (1 + ((ℓ : ℝ≥0∞) / (n - ℓ + 1 : ℝ≥0∞)) * (2 : ℝ≥0∞))
              ^ (w - t)
        ≤ (p * (t : ℝ≥0∞)) ^ t)
    (hmismatch : ∀ A : Axis n ℓ, ∀ {F : Core.CNF n w}, F ∈ Fs → ∀ x,
        F.eval x ≠ coveredB
            (Axis.selectorsFromTails (n := n) (ℓ := ℓ) (A := A)
              (tailSelectors := S.tailSelectors A) F.eval) x →
        Axis.leafForPoint (n := n) (ℓ := ℓ) A x
          ∈ Depth1Switching.badLeafFamily
              (n := n) (w := w) F ℓ t A)
    (badBound : Nat)
    (hbound :
      Depth1Switching.clauseWeightSum
          (n := n) (ℓ := ℓ) (w := w) (t := t)
          ((p * (t : ℝ≥0∞)) ^ t) Fs
        * (2 ^ n : ℝ≥0∞)
        ≤ (badBound : ℝ≥0∞)) :
    AxisWitness (n := n) (ℓ := ℓ) (τ := τ)
      (F := cnfFamily (Fs := Fs)) :=
  by
    classical
    -- Упаковываем итоговую границу на ошибку.
    let epsilon : Q :=
      (badBound : Q) / ((Nat.pow 2 ℓ : Nat) : Q)
    -- Применяем объединённый bound глубины 1 к списку формул.
    have hexists_axis :
        ∃ A : Axis n ℓ,
          ∀ {F : Core.CNF n w}, F ∈ Fs →
            errU F.eval
              (Axis.selectorsFromTails (n := n) (ℓ := ℓ) (A := A)
                (tailSelectors := S.tailSelectors A) F.eval)
              ≤ epsilon :=
      by
        obtain ⟨A, hA⟩ :=
          Depth1Switching.exists_axis_errU_le_list
            (n := n) (ℓ := ℓ) (w := w) (Fs := Fs) (t := t)
            (hsubset := hsubset)
            (hℓn := hℓn) (htℓ := htℓ) (htw := htw)
            (p := p) (hp := hp)
            (tailSelectors := fun A : Axis n ℓ => S.tailSelectors A)
            (hmismatch := by
              intro A F hF
              simpa using hmismatch A hF)
            (badBound := badBound) (hbound := hbound)
        refine ⟨A, ?_⟩
        intro F hF
        simpa using hA hF
    -- Переносим bound с формул на функции семейства `cnfFamily`.
    have hexists_family :
        ∃ A : Axis n ℓ,
          ∀ {f : BitVec n → Bool}, f ∈ cnfFamily (Fs := Fs) →
            errU f
              (Axis.selectorsFromTails (n := n) (ℓ := ℓ) (A := A)
                (tailSelectors := S.tailSelectors A) f)
              ≤ epsilon :=
      by
        rcases hexists_axis with ⟨A, hA⟩
        refine ⟨A, ?_⟩
        intro f hf
        obtain ⟨F, hF, hf_eq⟩ := mem_cnfFamily_iff.mp hf
        subst hf_eq
        exact hA hF
    -- Существование подходящей оси превращаем в явный `AxisWitness`.
    exact
      S.chooseWitness (n := n) (ℓ := ℓ) (τ := τ)
        (epsilon := epsilon) hexists_family

/--
  Компактная обёртка для данных, необходимых в глубинном случае switching-леммы.

  В ходе доказательства часто приходится переносить один и тот же набор
  предпосылок: список КНФ-формул `Fs`, систему хвостов `tailSystem`,
  условие `hmismatch`, ограничение на параметры `p`, `t`, `ℓ`, `w` и т.д.
  Структура `Depth1WitnessConfig` собирает всю эту информацию в одном месте,
  чтобы последующие шаги могли обращаться к ней как к единому объекту.

  Основное применение — метод `axisWitness`, который мгновенно извлекает
  `AxisWitness` из сконфигурированного набора данных, используя лемму
  `axisWitnessFromCNFList`.  Такой подход заметно упрощает код на следующих
  уровнях индукции: достаточно передать экземпляр `Depth1WitnessConfig`,
  и все необходимые параметры автоматически подставятся в глубинную оценку.
-/
structure Depth1WitnessConfig (n ℓ τ w t : Nat) where
  /-- Список КНФ-формул верхнего уровня. -/
  Fs : List (Core.CNF n w)
  /-- Система хвостов для каждой потенциальной оси. -/
  tailSystem : AxisTailSystem (n := n) (ℓ := ℓ) (τ := τ)
      (F := cnfFamily (Fs := Fs))
  /-- Каждое «плохое» множество `badSet` содержится в стандартной семье
      `formulaBadFamily`, где подсчитаны соответствующие листья. -/
  hsubset : ∀ {F : Core.CNF n w}, F ∈ Fs →
      Depth1Switching.badSet (n := n) (ℓ := ℓ) (w := w) F t
        ⊆ Depth1Switching.formulaBadFamily (n := n) (ℓ := ℓ) (w := w) F t
  /-- Осевой параметр не превосходит общего числа переменных. -/
  hℓn : ℓ ≤ n
  /-- Порог глубины для хвостов не превышает длину оси. -/
  htℓ : t ≤ ℓ
  /-- Порог глубины не превосходит ширины каждой КНФ. -/
  htw : t ≤ w
  /-- Вероятностный параметр `p`, используемый в p-biased оценке. -/
  p : ℝ≥0∞
  /-- Основное p-biased неравенство из глубинной леммы. -/
  hp :
      ((1 : ℝ≥0∞) / (2 ^ n : ℝ≥0∞))
          * (Nat.choose w t : ℝ≥0∞)
          * (((ℓ : ℝ≥0∞) / (n - ℓ + 1 : ℝ≥0∞)) * (2 : ℝ≥0∞)) ^ t
          * (1 + ((ℓ : ℝ≥0∞) / (n - ℓ + 1 : ℝ≥0∞)) * (2 : ℝ≥0∞))
              ^ (w - t)
        ≤ (p * (t : ℝ≥0∞)) ^ t
  /-- Связь между несоответствием покрытия и множеством «плохих» листьев. -/
  hmismatch : ∀ A : Axis n ℓ, ∀ {F : Core.CNF n w}, F ∈ Fs → ∀ x,
      F.eval x ≠ coveredB
        (Axis.selectorsFromTails (n := n) (ℓ := ℓ) (A := A)
          (tailSelectors := tailSystem.tailSelectors A) F.eval) x →
      Axis.leafForPoint (n := n) (ℓ := ℓ) A x
        ∈ Depth1Switching.badLeafFamily (n := n) (w := w) F ℓ t A
  /-- Целевой bound на число «плохих» листьев (после union bound). -/
  badBound : Nat
  /-- Арифметическая проверка: суммарная масса «плохих» рестрикций
      контролируется числом `badBound`. -/
  hbound :
      Depth1Switching.clauseWeightSum
          (n := n) (ℓ := ℓ) (w := w) (t := t)
          ((p * (t : ℝ≥0∞)) ^ t) Fs
        * (2 ^ n : ℝ≥0∞)
        ≤ (badBound : ℝ≥0∞)

namespace Depth1WitnessConfig

variable {n ℓ τ w t M : Nat}

/--
  Удобный конструктор `Depth1WitnessConfig`, который принимает на вход
  явные хвостовые сертификаты для каждой потенциальной оси.  На практике
  такие сертификаты поступают из индуктивного предположения: для каждого
  листа оси мы уже построили частичный PDT с ограничением на глубину хвоста
  и списком селекторов.  Функция автоматически превращает семейство этих
  сертификатов в систему хвостов `AxisTailSystem`, используя ранее
  определённый конструктор `AxisTailSystem.ofTailCertificates`.

  Остальные параметры (`hsubset`, `hp`, `hmismatch`, `hbound` и т.д.)
  полностью совпадают с полями структуры `Depth1WitnessConfig`.  Мы лишь
  переписываем условие `hmismatch`, подставляя явные селекторы из
  предоставленных хвостовых сертификатов.
-/
noncomputable def fromTailCertificates
    (Fs : List (Core.CNF n w))
    (build : ∀ A : Axis n ℓ,
        ∀ β (hβ : β ∈ Axis.leafList (n := n) (ℓ := ℓ) A),
          AxisTailSystem.TailCertificate
            (n := n) (τ := τ) (F := cnfFamily (Fs := Fs)))
    (hsubset : ∀ {F : Core.CNF n w}, F ∈ Fs →
        Depth1Switching.badSet (n := n) (ℓ := ℓ) (w := w) F t
          ⊆ Depth1Switching.formulaBadFamily (n := n) (ℓ := ℓ) (w := w) F t)
    (hℓn : ℓ ≤ n) (htℓ : t ≤ ℓ) (htw : t ≤ w)
    (p : ℝ≥0∞)
    (hp :
      ((1 : ℝ≥0∞) / (2 ^ n : ℝ≥0∞))
          * (Nat.choose w t : ℝ≥0∞)
          * (((ℓ : ℝ≥0∞) / (n - ℓ + 1 : ℝ≥0∞)) * (2 : ℝ≥0∞)) ^ t
          * (1 + ((ℓ : ℝ≥0∞) / (n - ℓ + 1 : ℝ≥0∞)) * (2 : ℝ≥0∞))
              ^ (w - t)
        ≤ (p * (t : ℝ≥0∞)) ^ t)
    (hmismatch : ∀ A : Axis n ℓ, ∀ {F : Core.CNF n w}, F ∈ Fs → ∀ x,
        F.eval x ≠ coveredB
          (Axis.selectorsFromTails (n := n) (ℓ := ℓ) (A := A)
            (tailSelectors :=
              fun β hβ =>
                (build A β hβ).certificate.selectors)
            F.eval) x →
        Axis.leafForPoint (n := n) (ℓ := ℓ) A x
          ∈ Depth1Switching.badLeafFamily (n := n) (w := w) F ℓ t A)
    (badBound : Nat)
    (hbound :
      Depth1Switching.clauseWeightSum
          (n := n) (ℓ := ℓ) (w := w) (t := t)
          ((p * (t : ℝ≥0∞)) ^ t) Fs
        * (2 ^ n : ℝ≥0∞)
        ≤ (badBound : ℝ≥0∞)) :
    Depth1WitnessConfig n ℓ τ w t := by
  classical
  refine
    { Fs := Fs
      tailSystem :=
        AxisTailSystem.ofTailCertificates
          (n := n) (ℓ := ℓ) (τ := τ) (F := cnfFamily (Fs := Fs)) build
      hsubset := hsubset
      hℓn := hℓn
      htℓ := htℓ
      htw := htw
      p := p
      hp := hp
      hmismatch := ?hmismatch
      badBound := badBound
      hbound := hbound }
  intro A F hF x hcov
  have hrewrite :
      Axis.selectorsFromTails (n := n) (ℓ := ℓ) (A := A)
          (tailSelectors :=
            (AxisTailSystem.ofTailCertificates
              (n := n) (ℓ := ℓ) (τ := τ) (F := cnfFamily (Fs := Fs))
              build).tailSelectors A)
          F.eval
        = Axis.selectorsFromTails (n := n) (ℓ := ℓ) (A := A)
            (tailSelectors :=
              fun β hβ => (build A β hβ).certificate.selectors)
            F.eval := by
    classical
    -- Переписываем через явные селекторы из хвостового сертификата.
    simp [AxisTailSystem.ofTailCertificates_tailSelectors]
  have hgoal := hmismatch A (F := F) hF x
  -- Переносим условие `covered` с использованием полученного равенства.
  have hcov' :
      F.eval x ≠ coveredB
        (Axis.selectorsFromTails (n := n) (ℓ := ℓ) (A := A)
          (tailSelectors :=
            fun β hβ => (build A β hβ).certificate.selectors)
          F.eval) x := by
    simpa [hrewrite] using hcov
  exact hgoal hcov'

@[simp] lemma fromTailCertificates_tailSelectors
    (Fs : List (Core.CNF n w))
    (build : ∀ A : Axis n ℓ,
        ∀ β (hβ : β ∈ Axis.leafList (n := n) (ℓ := ℓ) A),
          AxisTailSystem.TailCertificate
            (n := n) (τ := τ) (F := cnfFamily (Fs := Fs)))
    (hsubset : ∀ {F : Core.CNF n w}, F ∈ Fs →
        Depth1Switching.badSet (n := n) (ℓ := ℓ) (w := w) F t
          ⊆ Depth1Switching.formulaBadFamily (n := n) (ℓ := ℓ) (w := w) F t)
    (hℓn : ℓ ≤ n) (htℓ : t ≤ ℓ) (htw : t ≤ w)
    (p : ℝ≥0∞)
    (hp :
      ((1 : ℝ≥0∞) / (2 ^ n : ℝ≥0∞))
          * (Nat.choose w t : ℝ≥0∞)
          * (((ℓ : ℝ≥0∞) / (n - ℓ + 1 : ℝ≥0∞)) * (2 : ℝ≥0∞)) ^ t
          * (1 + ((ℓ : ℝ≥0∞) / (n - ℓ + 1 : ℝ≥0∞)) * (2 : ℝ≥0∞))
              ^ (w - t)
        ≤ (p * (t : ℝ≥0∞)) ^ t)
    (hmismatch : ∀ A : Axis n ℓ, ∀ {F : Core.CNF n w}, F ∈ Fs → ∀ x,
        F.eval x ≠ coveredB
          (Axis.selectorsFromTails (n := n) (ℓ := ℓ) (A := A)
            (tailSelectors :=
              fun β hβ =>
                (build A β hβ).certificate.selectors)
            F.eval) x →
        Axis.leafForPoint (n := n) (ℓ := ℓ) A x
          ∈ Depth1Switching.badLeafFamily (n := n) (w := w) F ℓ t A)
    (badBound : Nat)
    (hbound :
      Depth1Switching.clauseWeightSum
          (n := n) (ℓ := ℓ) (w := w) (t := t)
          ((p * (t : ℝ≥0∞)) ^ t) Fs
        * (2 ^ n : ℝ≥0∞)
        ≤ (badBound : ℝ≥0∞))
    (A : Axis n ℓ) {β : Subcube n}
    (hβ : β ∈ Axis.leafList (n := n) (ℓ := ℓ) A)
    (f : BitVec n → Bool) :
    ((fromTailCertificates (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t)
          (Fs := Fs) (build := build) (hsubset := hsubset) (hℓn := hℓn)
          (htℓ := htℓ) (htw := htw) (p := p) (hp := hp)
          (hmismatch := hmismatch) (badBound := badBound)
          (hbound := hbound)).tailSystem.tailSelectors A β hβ f)
      = (build A β hβ).certificate.selectors f := by
  classical
  simp [fromTailCertificates, AxisTailSystem.ofTailCertificates_tailSelectors]

@[simp] lemma fromTailCertificates_tails
    (Fs : List (Core.CNF n w))
    (build : ∀ A : Axis n ℓ,
        ∀ β (hβ : β ∈ Axis.leafList (n := n) (ℓ := ℓ) A),
          AxisTailSystem.TailCertificate
            (n := n) (τ := τ) (F := cnfFamily (Fs := Fs)))
    (hsubset : ∀ {F : Core.CNF n w}, F ∈ Fs →
        Depth1Switching.badSet (n := n) (ℓ := ℓ) (w := w) F t
          ⊆ Depth1Switching.formulaBadFamily (n := n) (ℓ := ℓ) (w := w) F t)
    (hℓn : ℓ ≤ n) (htℓ : t ≤ ℓ) (htw : t ≤ w)
    (p : ℝ≥0∞)
    (hp :
      ((1 : ℝ≥0∞) / (2 ^ n : ℝ≥0∞))
          * (Nat.choose w t : ℝ≥0∞)
          * (((ℓ : ℝ≥0∞) / (n - ℓ + 1 : ℝ≥0∞)) * (2 : ℝ≥0∞)) ^ t
          * (1 + ((ℓ : ℝ≥0∞) / (n - ℓ + 1 : ℝ≥0∞)) * (2 : ℝ≥0∞))
              ^ (w - t)
        ≤ (p * (t : ℝ≥0∞)) ^ t)
    (hmismatch : ∀ A : Axis n ℓ, ∀ {F : Core.CNF n w}, F ∈ Fs → ∀ x,
        F.eval x ≠ coveredB
          (Axis.selectorsFromTails (n := n) (ℓ := ℓ) (A := A)
            (tailSelectors :=
              fun β hβ =>
                (build A β hβ).certificate.selectors)
            F.eval) x →
        Axis.leafForPoint (n := n) (ℓ := ℓ) A x
          ∈ Depth1Switching.badLeafFamily (n := n) (w := w) F ℓ t A)
    (badBound : Nat)
    (hbound :
      Depth1Switching.clauseWeightSum
          (n := n) (ℓ := ℓ) (w := w) (t := t)
          ((p * (t : ℝ≥0∞)) ^ t) Fs
        * (2 ^ n : ℝ≥0∞)
        ≤ (badBound : ℝ≥0∞))
    (A : Axis n ℓ) {β : Subcube n}
    (hβ : β ∈ Axis.leafList (n := n) (ℓ := ℓ) A) :
    ((fromTailCertificates (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t)
          (Fs := Fs) (build := build) (hsubset := hsubset) (hℓn := hℓn)
          (htℓ := htℓ) (htw := htw) (p := p) (hp := hp)
          (hmismatch := hmismatch) (badBound := badBound)
          (hbound := hbound)).tailSystem.tails A β hβ)
      = (build A β hβ).certificate.witness.realize := by
  classical
  simp [fromTailCertificates, AxisTailSystem.ofTailCertificates_tails]

/--
  Упаковка всех данных, необходимых для построения конфигурации глубины 1,
  в структуру `Depth1WitnessInput`.  В отличие от `Depth1WitnessConfig`,
  здесь мы храним явную функцию `build`, которая для каждой оси и листа
  возвращает хвостовой сертификат.  Это удобно в индуктивных шагах, где
  хвосты порождаются из рекурсивной гипотезы и требуют дальнейшей обработки
  перед применением леммы глубины 1.
-/
structure Depth1WitnessInput (n ℓ τ w t : Nat) where
  /-- Список КНФ-формул верхнего уровня. -/
  Fs : List (Core.CNF n w)
  /-- Хвостовые сертификаты для каждой потенциальной оси и листа. -/
  build : ∀ A : Axis n ℓ,
      ∀ β (hβ : β ∈ Axis.leafList (n := n) (ℓ := ℓ) A),
        AxisTailSystem.TailCertificate
          (n := n) (τ := τ) (F := cnfFamily (Fs := Fs))
  /-- Включение множества «плохих» рестрикций в стандартное семейство. -/
  hsubset : ∀ {F : Core.CNF n w}, F ∈ Fs →
      Depth1Switching.badSet (n := n) (ℓ := ℓ) (w := w) F t
        ⊆ Depth1Switching.formulaBadFamily (n := n) (ℓ := ℓ) (w := w) F t
  /-- Ограничения на параметры `ℓ`, `t`, `w`. -/
  hℓn : ℓ ≤ n
  htℓ : t ≤ ℓ
  htw : t ≤ w
  /-- Вероятностный параметр и соответствующее p-biased неравенство. -/
  p : ℝ≥0∞
  hp :
      ((1 : ℝ≥0∞) / (2 ^ n : ℝ≥0∞))
          * (Nat.choose w t : ℝ≥0∞)
          * (((ℓ : ℝ≥0∞) / (n - ℓ + 1 : ℝ≥0∞)) * (2 : ℝ≥0∞)) ^ t
          * (1 + ((ℓ : ℝ≥0∞) / (n - ℓ + 1 : ℝ≥0∞)) * (2 : ℝ≥0∞))
              ^ (w - t)
        ≤ (p * (t : ℝ≥0∞)) ^ t
  /-- Связь между несоответствиями покрытия и «плохими» листьями. -/
  hmismatch : ∀ A : Axis n ℓ, ∀ {F : Core.CNF n w}, F ∈ Fs → ∀ x,
      F.eval x ≠ coveredB
        (Axis.selectorsFromTails (n := n) (ℓ := ℓ) (A := A)
          (tailSelectors :=
            fun β hβ => (build A β hβ).certificate.selectors)
          F.eval) x →
      Axis.leafForPoint (n := n) (ℓ := ℓ) A x
        ∈ Depth1Switching.badLeafFamily (n := n) (w := w) F ℓ t A
  /-- Целевой bound на число «плохих» листьев. -/
  badBound : Nat
  hbound :
      Depth1Switching.clauseWeightSum
          (n := n) (ℓ := ℓ) (w := w) (t := t)
          ((p * (t : ℝ≥0∞)) ^ t) Fs
        * (2 ^ n : ℝ≥0∞)
        ≤ (badBound : ℝ≥0∞)

/--
  Из структуры `Depth1WitnessInput` извлекаем готовую конфигурацию
  глубины 1, автоматически собирая систему хвостов через
  `AxisTailSystem.ofTailCertificates`.
-/
noncomputable def Depth1WitnessInput.toConfig
    (input : Depth1WitnessInput n ℓ τ w t) :
    Depth1WitnessConfig n ℓ τ w t := by
  classical
  refine Depth1WitnessConfig.fromTailCertificates
    (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t)
    (Fs := input.Fs)
    (build := input.build)
    (hsubset := ?_)
    (hℓn := input.hℓn)
    (htℓ := input.htℓ)
    (htw := input.htw)
    (p := input.p)
    (hp := input.hp)
    (hmismatch := ?_)
    (badBound := input.badBound)
    (hbound := input.hbound)
  · intro F hF
    exact input.hsubset hF
  · intro A F hF x hcov
    exact input.hmismatch A hF x hcov

namespace Depth1WitnessInput

variable {n ℓ τ w t M : Nat}

/--
  Раскрытие функции `build` внутри конфигурации, полученной из
  `Depth1WitnessInput`: локальные селекторы совпадают с селекторами
  хвостовых сертификатов, предоставленных на вход.
-/
@[simp] lemma toConfig_tailSelectors
    (input : Depth1WitnessInput n ℓ τ w t)
    (A : Axis n ℓ) {β : Subcube n}
    (hβ : β ∈ Axis.leafList (n := n) (ℓ := ℓ) A)
    (f : BitVec n → Bool) :
    ((input.toConfig (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t)).tailSystem
        .tailSelectors A β hβ f)
      = (input.build A β hβ).certificate.selectors f := by
  classical
  simpa using
    Depth1WitnessConfig.fromTailCertificates_tailSelectors
      (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t)
      (Fs := input.Fs) (build := input.build)
      (hsubset := input.hsubset) (hℓn := input.hℓn)
      (htℓ := input.htℓ) (htw := input.htw)
      (p := input.p) (hp := input.hp)
      (hmismatch := input.hmismatch) (badBound := input.badBound)
      (hbound := input.hbound) (A := A) (β := β) (hβ := hβ) (f := f)

/--
  Аналогичное раскрытие для самих хвостов: реализованное PDT в конфигурации
  совпадает с деревом из исходного хвостового сертификата.
-/
@[simp] lemma toConfig_tails
    (input : Depth1WitnessInput n ℓ τ w t)
    (A : Axis n ℓ) {β : Subcube n}
    (hβ : β ∈ Axis.leafList (n := n) (ℓ := ℓ) A) :
    ((input.toConfig (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t)).tailSystem
        .tails A β hβ)
      = (input.build A β hβ).certificate.witness.realize := by
  classical
  simpa using
    Depth1WitnessConfig.fromTailCertificates_tails
      (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t)
      (Fs := input.Fs) (build := input.build)
      (hsubset := input.hsubset) (hℓn := input.hℓn)
      (htℓ := input.htℓ) (htw := input.htw)
      (p := input.p) (hp := input.hp)
      (hmismatch := input.hmismatch) (badBound := input.badBound)
      (hbound := input.hbound) (A := A) (β := β) (hβ := hβ)

/--
  Переносим построение хвостового сертификата из конфигурации глубины 1 на
  исходную структуру входных данных.  Это удобно при индуктивном шаге:
  имея пакет `Depth1WitnessInput`, можно сразу извлечь хвост для верхнего
  уровня, не раскрывая промежуточные определения.
-/
noncomputable def tailCertificate
    (input : Depth1WitnessInput n ℓ τ w t)
    (τTotal : Nat) (hdepth : ℓ + τ ≤ τTotal) :
    AxisTailSystem.TailCertificate (n := n) (τ := τTotal)
      (F := cnfFamily (Fs := input.Fs)) := by
  classical
  exact
    Depth1WitnessConfig.tailCertificate
      (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t)
      (cfg := input.toConfig)
      (τTotal := τTotal) (hdepth := hdepth)

/-- Локальная глубина хвостов, полученная из `Depth1WitnessInput`, равна `τ`. -/
@[simp] lemma tailCertificate_level
    (input : Depth1WitnessInput n ℓ τ w t)
    (τTotal : Nat) (hdepth : ℓ + τ ≤ τTotal) :
    (tailCertificate (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) input
        (τTotal := τTotal) (hdepth := hdepth)).level = τ := by
  classical
  simp [tailCertificate]

/--
  Частичный сертификат внутри построенного хвостового пакета совпадает с
  результатом `Depth1WitnessConfig.partialCertificate`.
-/
@[simp] lemma tailCertificate_certificate
    (input : Depth1WitnessInput n ℓ τ w t)
    (τTotal : Nat) (hdepth : ℓ + τ ≤ τTotal) :
    (tailCertificate (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) input
        (τTotal := τTotal) (hdepth := hdepth)).certificate
      = Depth1WitnessConfig.partialCertificate
          (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t)
          (cfg := input.toConfig) := by
  classical
  simp [tailCertificate]

/-- Списки селекторов в новом хвостовом сертификате описываются через осевой свидетель. -/
@[simp] lemma tailCertificate_selectors
    (input : Depth1WitnessInput n ℓ τ w t)
    (τTotal : Nat) (hdepth : ℓ + τ ≤ τTotal)
    (f : BitVec n → Bool) :
    ((tailCertificate (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) input
        (τTotal := τTotal) (hdepth := hdepth)).certificate.selectors f)
      = Axis.selectorsFromTails (n := n) (ℓ := ℓ)
          (A := (Depth1WitnessConfig.axisWitness
              (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) input.toConfig).axis)
          (tailSelectors :=
            (Depth1WitnessConfig.axisWitness
              (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) input.toConfig)
              .tailSelectors)
          f := by
  classical
  simp [tailCertificate]

/-- Ошибка хвостового сертификата контролируется величиной `(badBound / 2^ℓ)`. -/
lemma tailCertificate_err_le
    (input : Depth1WitnessInput n ℓ τ w t)
    (τTotal : Nat) (hdepth : ℓ + τ ≤ τTotal)
    {f : BitVec n → Bool}
    (hf : f ∈ cnfFamily (Fs := input.Fs)) :
    errU f
        ((tailCertificate (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) input
            (τTotal := τTotal) (hdepth := hdepth)).certificate.selectors f)
      ≤ (input.badBound : Q) / ((Nat.pow 2 ℓ : Nat) : Q) := by
  classical
  simpa [tailCertificate]
    using Depth1WitnessConfig.tailCertificate_err_le
      (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t)
      (cfg := input.toConfig)
      (τTotal := τTotal) (hdepth := hdepth) hf

/-- Параметр ошибки хвостового сертификата совпадает с нормированным `badBound`. -/
@[simp] lemma tailCertificate_epsilon
    (input : Depth1WitnessInput n ℓ τ w t)
    (τTotal : Nat) (hdepth : ℓ + τ ≤ τTotal) :
    (tailCertificate (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) input
        (τTotal := τTotal) (hdepth := hdepth)).certificate.epsilon
      = (input.badBound : Q) / ((Nat.pow 2 ℓ : Nat) : Q) := by
  classical
  simp [tailCertificate]

/-- Ошибка неотрицательна уже на уровне `Depth1WitnessInput`. -/
lemma tailCertificate_epsilon_nonneg
    (input : Depth1WitnessInput n ℓ τ w t)
    (τTotal : Nat) (hdepth : ℓ + τ ≤ τTotal) :
    (0 : Q)
      ≤ (tailCertificate (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) input
          (τTotal := τTotal) (hdepth := hdepth)).certificate.epsilon := by
  classical
  simpa [tailCertificate]
    using Depth1WitnessConfig.tailCertificate_epsilon_nonneg
      (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t)
      (cfg := input.toConfig)
      (τTotal := τTotal) (hdepth := hdepth)

/--
  Укороченная версия `tailCertificate`, в которой суммарная глубина хвоста
  берётся равной `ℓ + τ`.  Такой выбор пригоден по умолчанию и не требует
  дополнительных числовых проверок.
-/
noncomputable def tailCertificateSelfBound
    (input : Depth1WitnessInput n ℓ τ w t) :
    AxisTailSystem.TailCertificate (n := n) (τ := ℓ + τ)
      (F := cnfFamily (Fs := input.Fs)) :=
  tailCertificate (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) input
    (τTotal := ℓ + τ) (hdepth := Nat.le_refl _)

@[simp] lemma tailCertificateSelfBound_level
    (input : Depth1WitnessInput n ℓ τ w t) :
    (tailCertificateSelfBound (n := n) (ℓ := ℓ) (τ := τ)
        (w := w) (t := t) input).level = τ := by
  classical
  simpa [tailCertificateSelfBound]
    using tailCertificate_level (n := n) (ℓ := ℓ) (τ := τ)
      (w := w) (t := t) (input := input)
        (τTotal := ℓ + τ) (hdepth := Nat.le_refl _)

@[simp] lemma tailCertificateSelfBound_certificate
    (input : Depth1WitnessInput n ℓ τ w t) :
    (tailCertificateSelfBound (n := n) (ℓ := ℓ) (τ := τ)
        (w := w) (t := t) input).certificate
      = Depth1WitnessConfig.partialCertificate
          (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t)
          (cfg := input.toConfig) := by
  classical
  simpa [tailCertificateSelfBound]
    using tailCertificate_certificate (n := n) (ℓ := ℓ) (τ := τ)
      (w := w) (t := t) (input := input)
        (τTotal := ℓ + τ) (hdepth := Nat.le_refl _)

@[simp] lemma tailCertificateSelfBound_selectors
    (input : Depth1WitnessInput n ℓ τ w t) (f : BitVec n → Bool) :
    ((tailCertificateSelfBound (n := n) (ℓ := ℓ) (τ := τ)
          (w := w) (t := t) input).certificate.selectors f)
      = Axis.selectorsFromTails (n := n) (ℓ := ℓ)
          (A := (Depth1WitnessConfig.axisWitness
              (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t)
                input.toConfig).axis)
          (tailSelectors :=
            (Depth1WitnessConfig.axisWitness
              (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t)
                input.toConfig).tailSelectors)
          f := by
  classical
  simpa [tailCertificateSelfBound]
    using tailCertificate_selectors (n := n) (ℓ := ℓ) (τ := τ)
      (w := w) (t := t) (input := input)
        (τTotal := ℓ + τ) (hdepth := Nat.le_refl _)

lemma tailCertificateSelfBound_err_le
    (input : Depth1WitnessInput n ℓ τ w t)
    {f : BitVec n → Bool} (hf : f ∈ cnfFamily (Fs := input.Fs)) :
    errU f
        ((tailCertificateSelfBound (n := n) (ℓ := ℓ) (τ := τ)
            (w := w) (t := t) input).certificate.selectors f)
      ≤ (input.badBound : Q) / ((Nat.pow 2 ℓ : Nat) : Q) := by
  classical
  simpa [tailCertificateSelfBound, tailCertificate_selectors]
    using tailCertificate_err_le (n := n) (ℓ := ℓ) (τ := τ)
      (w := w) (t := t) (input := input)
        (τTotal := ℓ + τ) (hdepth := Nat.le_refl _)

@[simp] lemma tailCertificateSelfBound_epsilon
    (input : Depth1WitnessInput n ℓ τ w t) :
    (tailCertificateSelfBound (n := n) (ℓ := ℓ) (τ := τ)
        (w := w) (t := t) input).certificate.epsilon
      = (input.badBound : Q) / ((Nat.pow 2 ℓ : Nat) : Q) := by
  classical
  simpa [tailCertificateSelfBound]
    using tailCertificate_epsilon (n := n) (ℓ := ℓ) (τ := τ)
      (w := w) (t := t) (input := input)
        (τTotal := ℓ + τ) (hdepth := Nat.le_refl _)

lemma tailCertificateSelfBound_epsilon_nonneg
    (input : Depth1WitnessInput n ℓ τ w t) :
    (0 : Q)
      ≤ (tailCertificateSelfBound (n := n) (ℓ := ℓ) (τ := τ)
          (w := w) (t := t) input).certificate.epsilon := by
  classical
  simpa [tailCertificateSelfBound]
    using tailCertificate_epsilon_nonneg (n := n) (ℓ := ℓ) (τ := τ)
      (w := w) (t := t) (input := input)
        (τTotal := ℓ + τ) (hdepth := Nat.le_refl _)

/--
  Перепаковываем хвостовые сертификаты входных данных глубины 1 под более
  щедрый глубинный бюджет `depthBudget M (d + 1)`.  На уровне предпосылок
  требуется лишь `τ ≤ depthBudget M d`; оставшееся неравенство
  `depthBudget M d ≤ depthBudget M (d + 1)` предоставляется числовой леммой
  `depthBudget_le_depthBudget_succ`.

  Конструкция не изменяет сами хвосты: мы используем вспомогательный метод
  `TailCertificate.extend`, который просто обновляет проверку ограничения
  глубины.  Такой переход понадобится в индуктивной части multi-switching-леммы,
  где хвосты предыдущих уровней «встраиваются» в общий бюджет верхнего слоя.
-/
noncomputable def tailSystemWithinBudget
    (input : Depth1WitnessInput n (axisLength n M) τ w t)
    (d : Nat) (hτ : τ ≤ depthBudget M d) :
    AxisTailSystem (n := n) (ℓ := axisLength n M)
      (τ := depthBudget M (d + 1))
      (F := cnfFamily (Fs := input.Fs)) := by
  classical
  have hτ' : τ ≤ depthBudget M (d + 1) :=
    hτ.trans (depthBudget_le_depthBudget_succ (M := M) (d := d))
  refine AxisTailSystem.ofTailCertificates
    (n := n) (ℓ := axisLength n M)
    (τ := depthBudget M (d + 1))
    (F := cnfFamily (Fs := input.Fs))
    (build := fun A β hβ =>
      (input.build A β hβ).extend (n := n)
        (τ := τ) (F := cnfFamily (Fs := input.Fs)) hτ')

/-- Селекторы построенной системы совпадают с селекторами исходных хвостов. -/
@[simp] lemma tailSystemWithinBudget_tailSelectors
    (input : Depth1WitnessInput n (axisLength n M) τ w t)
    (d : Nat) (hτ : τ ≤ depthBudget M d)
    (A : Axis n (axisLength n M))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A) (f : BitVec n → Bool) :
    (tailSystemWithinBudget (n := n) (M := M) (τ := τ)
        (w := w) (t := t) input d hτ)
        .tailSelectors A β hβ f
      = (input.build A β hβ).certificate.selectors f := by
  classical
  simp [tailSystemWithinBudget,
    AxisTailSystem.ofTailCertificates_tailSelectors,
    AxisTailSystem.TailCertificate.extend_selectors]

/-- Хвосты в новой системе совпадают с деревьями исходных сертификатов. -/
@[simp] lemma tailSystemWithinBudget_tails
    (input : Depth1WitnessInput n (axisLength n M) τ w t)
    (d : Nat) (hτ : τ ≤ depthBudget M d)
    (A : Axis n (axisLength n M))
    {β : Subcube n} (hβ : β ∈ Axis.leafList (n := n)
      (ℓ := axisLength n M) A) :
    (tailSystemWithinBudget (n := n) (M := M) (τ := τ)
        (w := w) (t := t) input d hτ)
        .tails A β hβ
      = (input.build A β hβ).certificate.witness.realize := by
  classical
  simp [tailSystemWithinBudget,
    AxisTailSystem.ofTailCertificates_tails,
    AxisTailSystem.TailCertificate.extend_certificate]

/--
  Если глубина хвоста `τ` ограничена бюджетом `depthBudget M d`, то суммарная
  глубина хвостового сертификата (ствол `ℓ` плюс хвост `τ`) не превосходит
  бюджета следующего уровня.  Эта оценка будет использоваться в индуктивном
  шаге multi-switching-леммы при переходе к схемам глубины `d + 1`.
-/
lemma tailCertificateSelfBound_totalDepth_le_depthBudget
    (input : Depth1WitnessInput n (axisLength n M) τ w t)
    (d : Nat) (hτ : τ ≤ depthBudget M d)
    (hlog : 2 ≤ logBudget M) :
    (tailCertificateSelfBound (n := n) (ℓ := axisLength n M)
        (τ := τ) (w := w) (t := t) input).certificate.depthBound
          + (tailCertificateSelfBound (n := n) (ℓ := axisLength n M)
              (τ := τ) (w := w) (t := t) input).level
      ≤ depthBudget M (d + 1) := by
  classical
  have hsum :
      (tailCertificateSelfBound (n := n) (ℓ := axisLength n M)
          (τ := τ) (w := w) (t := t) input).certificate.depthBound
            + (tailCertificateSelfBound (n := n) (ℓ := axisLength n M)
                (τ := τ) (w := w) (t := t) input).level
        = axisLength n M + τ := by
    simp [tailCertificateSelfBound, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc]
  have hbound :=
    axisLength_add_le_depthBudget_succ
      (n := n) (M := M) (d := d) (τ := τ)
      (hlog := hlog) (hτ := hτ)
  simpa [hsum]
    using hbound

/--
  Осевой свидетель, ассоциированный с входными данными глубины 1.  Определение
  просто перенаправляет построение на `Depth1WitnessConfig.axisWitness`,
  чтобы последующие индуктивные шаги могли напрямую обращаться к оси и
  локальным хвостам, не раскрывая промежуточную конфигурацию.
-/
noncomputable def axisWitness
    (input : Depth1WitnessInput n ℓ τ w t) :
    AxisWitness (n := n) (ℓ := ℓ) (τ := τ)
      (F := cnfFamily (Fs := input.Fs)) := by
  classical
  exact Depth1WitnessConfig.axisWitness
    (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) input.toConfig

/--
  Ошибка, зафиксированная в осевом свидетеле, совпадает с нормированным
  `badBound`.  В дальнейшем эта формула позволит мгновенно подставлять
  численные границы при переходе к хвостовым сертификатам.
-/
@[simp] lemma axisWitness_epsilon
    (input : Depth1WitnessInput n ℓ τ w t) :
    (axisWitness (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) input).epsilon
      = (input.badBound : Q) / ((Nat.pow 2 ℓ : Nat) : Q) := by
  classical
  simpa [axisWitness]
    using Depth1WitnessConfig.axisWitness_epsilon
      (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) input.toConfig

/--
  Частичный сертификат, извлечённый напрямую из входных данных глубины 1.
  Конструкция повторяет `Depth1WitnessConfig.partialCertificate`, но избавляет
  от необходимости обращаться к промежуточной конфигурации.
-/
noncomputable def partialCertificate
    (input : Depth1WitnessInput n ℓ τ w t) :
    PartialCertificate n τ (cnfFamily (Fs := input.Fs)) := by
  classical
  exact Depth1WitnessConfig.partialCertificate
    (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) input.toConfig

/--
  Селекторы построенного частичного сертификата совпадают с глобальными
  селекторами осевого свидетеля, что облегчает дальнейшее управление
  `errU` и проверку свойств хвостов.
-/
@[simp] lemma partialCertificate_selectors
    (input : Depth1WitnessInput n ℓ τ w t) (f : BitVec n → Bool) :
    (partialCertificate (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) input)
        .selectors f
      = Axis.selectorsFromTails (n := n) (ℓ := ℓ)
          (A := (axisWitness (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) input).axis)
          (tailSelectors :=
            (axisWitness (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) input)
              .tailSelectors)
          f := by
  classical
  simpa [partialCertificate, axisWitness]
    using Depth1WitnessConfig.partialCertificate_selectors
      (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) input.toConfig (f := f)

/--
  Оценка ошибки для частичного сертификата, построенного из входных данных
  глубины 1.  Формула напрямую использует bound `badBound / 2^ℓ`.
-/
lemma partialCertificate_err_le
    (input : Depth1WitnessInput n ℓ τ w t)
    {f : BitVec n → Bool}
    (hf : f ∈ cnfFamily (Fs := input.Fs)) :
    errU f
        ((partialCertificate (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) input)
          .selectors f)
      ≤ (input.badBound : Q) / ((Nat.pow 2 ℓ : Nat) : Q) := by
  classical
  simpa [partialCertificate]
    using Depth1WitnessConfig.partialCertificate_err_le
      (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t)
      (cfg := input.toConfig) hf

/-- Ошибка частичного сертификата неотрицательна. -/
lemma partialCertificate_epsilon_nonneg
    (input : Depth1WitnessInput n ℓ τ w t) :
    (0 : Q)
      ≤ (partialCertificate (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) input)
          .epsilon := by
  classical
  simpa [partialCertificate]
    using Depth1WitnessConfig.partialCertificate_epsilon_nonneg
      (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) input.toConfig

/-- Параметр ошибки совпадает с нормированным `badBound`. -/
@[simp] lemma partialCertificate_epsilon
    (input : Depth1WitnessInput n ℓ τ w t) :
    (partialCertificate (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) input).epsilon
      = (input.badBound : Q) / ((Nat.pow 2 ℓ : Nat) : Q) := by
  classical
  simpa [partialCertificate]
    using Depth1WitnessConfig.partialCertificate_epsilon
      (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) input.toConfig

/-- Глубина ствола построенного частичного сертификата равна `ℓ`. -/
@[simp] lemma partialCertificate_depthBound
    (input : Depth1WitnessInput n ℓ τ w t) :
    (partialCertificate (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) input).depthBound
      = ℓ := by
  classical
  simpa [partialCertificate]
    using Depth1WitnessConfig.partialCertificate_depthBound
      (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) input.toConfig

end Depth1WitnessInput

/--
  Из сконфигурированного набора данных моментально извлекаем `AxisWitness`.
  Конкретный выбор оси осуществляется с помощью `Classical.choose`,
  использованного внутри `axisWitnessFromCNFList`.
-/
noncomputable def axisWitness (cfg : Depth1WitnessConfig n ℓ τ w t) :
    AxisWitness (n := n) (ℓ := ℓ) (τ := τ)
      (F := cnfFamily (Fs := cfg.Fs)) :=
  AxisTailSystem.axisWitnessFromCNFList
    (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t)
    (Fs := cfg.Fs)
    (S := cfg.tailSystem)
    (hsubset := cfg.hsubset)
    (hℓn := cfg.hℓn)
    (htℓ := cfg.htℓ)
    (htw := cfg.htw)
    (p := cfg.p)
    (hp := cfg.hp)
    (hmismatch := by
      intro A F hF
      simpa using cfg.hmismatch A hF)
    (badBound := cfg.badBound)
    (hbound := cfg.hbound)

/--
  При извлечении свидетеля ошибка `ε` равна `badBound / 2^ℓ` — это ключевой
  параметр, который затем используется при анализе хвостов и индуктивном
  переходе по глубине.
-/
@[simp] lemma axisWitness_epsilon (cfg : Depth1WitnessConfig n ℓ τ w t) :
    (axisWitness (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) cfg).epsilon
      = (cfg.badBound : Q) / ((Nat.pow 2 ℓ : Nat) : Q) := by
  classical
  unfold axisWitness
  simp [AxisTailSystem.axisWitnessFromCNFList]

/--
  Частичный сертификат, полученный из конфигурации глубины 1.
  Мы используем осевой свидетель, сконструированный `axisWitness`,
  и выбираем естественную границу на глубину ствола `depthBound = ℓ`.
-/
noncomputable def partialCertificate
    (cfg : Depth1WitnessConfig n ℓ τ w t) :
    PartialCertificate n τ (cnfFamily (Fs := cfg.Fs)) := by
  classical
  exact (axisWitness (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) cfg)
    |>.toPartialCertificateSelfBound

/--
  Уточняем поле `selectors` построенного частичного сертификата: глобальные
  селекторы совпадают с объединением хвостовых списков, используемых в
  осевом свидетеле.
-/
@[simp] lemma partialCertificate_selectors
    (cfg : Depth1WitnessConfig n ℓ τ w t) (f : BitVec n → Bool) :
    (partialCertificate (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) cfg)
        .selectors f
      = Axis.selectorsFromTails (n := n) (ℓ := ℓ)
          (A := (axisWitness (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) cfg).axis)
          (tailSelectors :=
            (axisWitness (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) cfg).tailSelectors)
          f := by
  classical
  simp [partialCertificate,
    AxisWitness.toPartialCertificateSelfBound,
    AxisWitness.toPartialCertificate,
    AxisWitness.globalSelectors]

/--
  Ошибка частичного сертификата ограничивается тем же параметром, что и у
  исходного осевого свидетеля.  Утверждение удобно в практических расчётах,
  когда требуется ссылаться на выбор `badBound` из конфигурации.
-/
lemma partialCertificate_err_le
    (cfg : Depth1WitnessConfig n ℓ τ w t)
    {f : BitVec n → Bool}
    (hf : f ∈ cnfFamily (Fs := cfg.Fs)) :
    errU f
        ((partialCertificate (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) cfg)
          .selectors f)
      ≤ (cfg.badBound : Q) / ((Nat.pow 2 ℓ : Nat) : Q) := by
  classical
  have haxis :=
    AxisWitness.err_le_of_mem
      (W := axisWitness (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) cfg)
      (n := n) (ℓ := ℓ) (τ := τ)
      (F := cnfFamily (Fs := cfg.Fs)) (f := f) hf
  simpa [partialCertificate_selectors,
    axisWitness_epsilon (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) cfg]
    using haxis

/--
  Поскольку `badBound` — натуральное число, его нормированная версия в поле
  `epsilon` всегда неотрицательна.  Лемма избавляет от повторных расчётов при
  обращении к общим числовым ограничениям.
-/
lemma partialCertificate_epsilon_nonneg
    (cfg : Depth1WitnessConfig n ℓ τ w t) :
    (0 : Q)
      ≤ (partialCertificate (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) cfg)
          .epsilon := by
  classical
  have hnum : (0 : Q) ≤ (cfg.badBound : Q) := by exact_mod_cast Nat.zero_le _
  have hden : 0 < ((Nat.pow 2 ℓ : Nat) : Q) := by
    have htwo : 0 < (2 : Q) := by norm_num
    simpa [Nat.cast_pow] using pow_pos htwo ℓ
  have hdiv := div_nonneg hnum hden.le
  simpa [partialCertificate_epsilon,
    axisWitness_epsilon (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) cfg]
    using hdiv

/--
  Ошибка частичного сертификата, построенного из конфигурации глубины 1,
  совпадает с параметром `(badBound / 2^ℓ)` из вероятностного анализа.
-/
@[simp] lemma partialCertificate_epsilon
    (cfg : Depth1WitnessConfig n ℓ τ w t) :
    (partialCertificate (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) cfg).epsilon
      = (cfg.badBound : Q) / ((Nat.pow 2 ℓ : Nat) : Q) := by
  classical
  simpa [partialCertificate, AxisWitness.toPartialCertificateSelfBound]
    using axisWitness_epsilon
      (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) cfg

/-- Глубина ствола построенного частичного сертификата совпадает с `ℓ`. -/
@[simp] lemma partialCertificate_depthBound
    (cfg : Depth1WitnessConfig n ℓ τ w t) :
    (partialCertificate (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) cfg).depthBound
      = ℓ := by
  classical
  simp [partialCertificate, AxisWitness.toPartialCertificateSelfBound,
    AxisWitness.toPartialCertificate]

/--
  Превращаем конфигурацию глубины 1 в хвостовой сертификат, пригодный для
  дальнейшей индукции.  Параметр `τTotal` задаёт суммарную глубину хвоста после
  приклейки, а неравенство `hdepth` гарантирует, что текущий сертификат
  удовлетворяет этому ограничению.
-/
noncomputable def tailCertificate
    (cfg : Depth1WitnessConfig n ℓ τ w t)
    (τTotal : Nat)
    (hdepth : ℓ + τ ≤ τTotal) :
    AxisTailSystem.TailCertificate (n := n) (τ := τTotal)
      (F := cnfFamily (Fs := cfg.Fs)) := by
  classical
  have htotal : (partialCertificate (n := n) (ℓ := ℓ) (τ := τ)
        (w := w) (t := t) cfg).depthBound + τ ≤ τTotal := by
    simpa [partialCertificate_depthBound, Nat.add_comm] using hdepth
  exact (axisWitness (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) cfg)
    |>.toTailCertificate (n := n) (ℓ := ℓ) (τ := τ)
      (F := cnfFamily (Fs := cfg.Fs))
      (depthBound := ℓ) (τTotal := τTotal)
      (hdepth := Nat.le_refl ℓ) (htotal := htotal)

/-- Локальная глубина хвостов, полученная из конфигурации глубины 1, равна `τ`. -/
@[simp] lemma tailCertificate_level
    (cfg : Depth1WitnessConfig n ℓ τ w t)
    (τTotal : Nat) (hdepth : ℓ + τ ≤ τTotal) :
    (tailCertificate (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) cfg
        (τTotal := τTotal) (hdepth := hdepth)).level = τ := by
  classical
  simp [tailCertificate, AxisWitness.toTailCertificate_level]

/--
  Хвостовой сертификат разворачивает тот же частичный сертификат, что и
  `partialCertificate`.  В дальнейшем это позволит ссылаться на все
  проверенные выше свойства напрямую.
-/
@[simp] lemma tailCertificate_certificate
    (cfg : Depth1WitnessConfig n ℓ τ w t)
    (τTotal : Nat) (hdepth : ℓ + τ ≤ τTotal) :
    (tailCertificate (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) cfg
        (τTotal := τTotal) (hdepth := hdepth)).certificate
      = partialCertificate (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) cfg := by
  classical
  simp [tailCertificate, AxisWitness.toTailCertificate_certificate]

/-- Список селекторов в хвостовом сертификате совпадает с глобальными селекторами. -/
@[simp] lemma tailCertificate_selectors
    (cfg : Depth1WitnessConfig n ℓ τ w t)
    (τTotal : Nat) (hdepth : ℓ + τ ≤ τTotal)
    (f : BitVec n → Bool) :
    ((tailCertificate (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) cfg
        (τTotal := τTotal) (hdepth := hdepth)).certificate.selectors f)
      = Axis.selectorsFromTails (n := n) (ℓ := ℓ)
          (A := (axisWitness (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) cfg).axis)
          (tailSelectors :=
            (axisWitness (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) cfg).tailSelectors)
          f := by
  classical
  simp [tailCertificate, AxisWitness.toTailCertificate_selectors,
    partialCertificate_selectors]

/--
  Ошибка в хвостовом сертификате контролируется тем же параметром,
  что и в исходной конфигурации глубины 1.
-/
lemma tailCertificate_err_le
    (cfg : Depth1WitnessConfig n ℓ τ w t)
    (τTotal : Nat) (hdepth : ℓ + τ ≤ τTotal)
    {f : BitVec n → Bool}
    (hf : f ∈ cnfFamily (Fs := cfg.Fs)) :
    errU f
        ((tailCertificate (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) cfg
            (τTotal := τTotal) (hdepth := hdepth)).certificate.selectors f)
      ≤ (cfg.badBound : Q) / ((Nat.pow 2 ℓ : Nat) : Q) := by
  classical
  simpa [tailCertificate_selectors]
    using partialCertificate_err_le (n := n) (ℓ := ℓ) (τ := τ)
      (w := w) (t := t) (cfg := cfg) hf

/-- Параметр ошибки в хвостовом сертификате совпадает с `badBound / 2^ℓ`. -/
@[simp] lemma tailCertificate_epsilon
    (cfg : Depth1WitnessConfig n ℓ τ w t)
    (τTotal : Nat) (hdepth : ℓ + τ ≤ τTotal) :
    (tailCertificate (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) cfg
        (τTotal := τTotal) (hdepth := hdepth)).certificate.epsilon
      = (cfg.badBound : Q) / ((Nat.pow 2 ℓ : Nat) : Q) := by
  classical
  simp [tailCertificate]

/-- Ошибка хвостового сертификата неотрицательна. -/
lemma tailCertificate_epsilon_nonneg
    (cfg : Depth1WitnessConfig n ℓ τ w t)
    (τTotal : Nat) (hdepth : ℓ + τ ≤ τTotal) :
    (0 : Q)
      ≤ (tailCertificate (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) cfg
          (τTotal := τTotal) (hdepth := hdepth)).certificate.epsilon := by
  classical
  simpa [tailCertificate]
    using partialCertificate_epsilon_nonneg (n := n) (ℓ := ℓ) (τ := τ)
      (w := w) (t := t) (cfg := cfg)

/--
  Укороченная версия `tailCertificate`, где суммарная глубина хвоста берётся
  равной `ℓ + τ`.  Такой выбор соответствует естественной границе после
  приклейки хвостов и используется по умолчанию в индуктивных шагах
  multi-switching-леммы.
-/
noncomputable def tailCertificateSelfBound
    (cfg : Depth1WitnessConfig n ℓ τ w t) :
    AxisTailSystem.TailCertificate (n := n) (τ := ℓ + τ)
      (F := cnfFamily (Fs := cfg.Fs)) :=
  tailCertificate (n := n) (ℓ := ℓ) (τ := τ) (w := w) (t := t) cfg
    (τTotal := ℓ + τ) (hdepth := Nat.le_refl _)

@[simp] lemma tailCertificateSelfBound_level
    (cfg : Depth1WitnessConfig n ℓ τ w t) :
    (tailCertificateSelfBound (n := n) (ℓ := ℓ) (τ := τ)
        (w := w) (t := t) cfg).level = τ := by
  classical
  simpa [tailCertificateSelfBound]
    using tailCertificate_level (n := n) (ℓ := ℓ) (τ := τ)
      (w := w) (t := t) (cfg := cfg)
        (τTotal := ℓ + τ) (hdepth := Nat.le_refl _)

@[simp] lemma tailCertificateSelfBound_certificate
    (cfg : Depth1WitnessConfig n ℓ τ w t) :
    (tailCertificateSelfBound (n := n) (ℓ := ℓ) (τ := τ)
        (w := w) (t := t) cfg).certificate
      = partialCertificate (n := n) (ℓ := ℓ) (τ := τ)
          (w := w) (t := t) cfg := by
  classical
  simpa [tailCertificateSelfBound]
    using tailCertificate_certificate (n := n) (ℓ := ℓ) (τ := τ)
      (w := w) (t := t) (cfg := cfg)
        (τTotal := ℓ + τ) (hdepth := Nat.le_refl _)

@[simp] lemma tailCertificateSelfBound_selectors
    (cfg : Depth1WitnessConfig n ℓ τ w t) (f : BitVec n → Bool) :
    ((tailCertificateSelfBound (n := n) (ℓ := ℓ) (τ := τ)
          (w := w) (t := t) cfg).certificate.selectors f)
      = Axis.selectorsFromTails (n := n) (ℓ := ℓ)
          (A := (axisWitness (n := n) (ℓ := ℓ) (τ := τ)
              (w := w) (t := t) cfg).axis)
          (tailSelectors :=
            (axisWitness (n := n) (ℓ := ℓ) (τ := τ)
              (w := w) (t := t) cfg).tailSelectors)
          f := by
  classical
  simpa [tailCertificateSelfBound]
    using tailCertificate_selectors (n := n) (ℓ := ℓ) (τ := τ)
      (w := w) (t := t) (cfg := cfg)
        (τTotal := ℓ + τ) (hdepth := Nat.le_refl _)

lemma tailCertificateSelfBound_err_le
    (cfg : Depth1WitnessConfig n ℓ τ w t)
    {f : BitVec n → Bool} (hf : f ∈ cnfFamily (Fs := cfg.Fs)) :
    errU f
        ((tailCertificateSelfBound (n := n) (ℓ := ℓ) (τ := τ)
            (w := w) (t := t) cfg).certificate.selectors f)
      ≤ (cfg.badBound : Q) / ((Nat.pow 2 ℓ : Nat) : Q) := by
  classical
  simpa [tailCertificateSelfBound, tailCertificate_selectors]
    using tailCertificate_err_le (n := n) (ℓ := ℓ) (τ := τ)
      (w := w) (t := t) (cfg := cfg)
        (τTotal := ℓ + τ) (hdepth := Nat.le_refl _)

@[simp] lemma tailCertificateSelfBound_epsilon
    (cfg : Depth1WitnessConfig n ℓ τ w t) :
    (tailCertificateSelfBound (n := n) (ℓ := ℓ) (τ := τ)
        (w := w) (t := t) cfg).certificate.epsilon
      = (cfg.badBound : Q) / ((Nat.pow 2 ℓ : Nat) : Q) := by
  classical
  simpa [tailCertificateSelfBound]
    using tailCertificate_epsilon (n := n) (ℓ := ℓ) (τ := τ)
      (w := w) (t := t) (cfg := cfg)
        (τTotal := ℓ + τ) (hdepth := Nat.le_refl _)

lemma tailCertificateSelfBound_epsilon_nonneg
    (cfg : Depth1WitnessConfig n ℓ τ w t) :
    (0 : Q)
      ≤ (tailCertificateSelfBound (n := n) (ℓ := ℓ) (τ := τ)
          (w := w) (t := t) cfg).certificate.epsilon := by
  classical
  simpa [tailCertificateSelfBound]
    using tailCertificate_epsilon_nonneg (n := n) (ℓ := ℓ) (τ := τ)
      (w := w) (t := t) (cfg := cfg)
        (τTotal := ℓ + τ) (hdepth := Nat.le_refl _)

/--
  Числовое следствие: если глубина хвоста `τ` ограничена бюджетом
  `depthBudget M d`, то суммарная глубина хвостового сертификата, построенного
  из данных глубины 1, не превосходит бюджета следующего уровня.  Это ключевой
  шаг при переходе к индуктивному случаю multi-switching-леммы.
-/
lemma tailCertificateSelfBound_totalDepth_le_depthBudget
    (cfg : Depth1WitnessConfig n (axisLength n M) τ w t)
    (d : Nat) (hτ : τ ≤ depthBudget M d)
    (hlog : 2 ≤ logBudget M) :
    (tailCertificateSelfBound (n := n) (ℓ := axisLength n M)
        (τ := τ) (w := w) (t := t) cfg).certificate.depthBound
          + (tailCertificateSelfBound (n := n) (ℓ := axisLength n M)
              (τ := τ) (w := w) (t := t) cfg).level
      ≤ depthBudget M (d + 1) := by
  classical
  have hsum :
      (tailCertificateSelfBound (n := n) (ℓ := axisLength n M)
          (τ := τ) (w := w) (t := t) cfg).certificate.depthBound
            + (tailCertificateSelfBound (n := n) (ℓ := axisLength n M)
                (τ := τ) (w := w) (t := t) cfg).level
        = axisLength n M + τ := by
    simp [tailCertificateSelfBound, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc]
  have hbound :=
    axisLength_add_le_depthBudget_succ
      (n := n) (M := M) (d := d) (τ := τ)
      (hlog := hlog) (hτ := hτ)
  simpa [hsum]
    using hbound

end Depth1WitnessConfig

end MultiSwitching
end ThirdPartyFacts
end Pnp3

namespace Pnp3
namespace ThirdPartyFacts
namespace Depth1Switching

open RandomRestriction

variable {n ℓ w : Nat}

/--
  Сумма весов `restrictionUniform` по произвольному конечному множеству
  точных рестрикций зависит только от числа элементов: каждый элемент имеет
  одинаковый вклад `(1 / |Axis × BitVec|)`.
-/
lemma restrictionUniform_sum_eq_mass_mul_card
    (S : Finset (ExactRestriction n ℓ)) :
    (∑ ρ in S, restrictionUniform n ℓ ρ)
      = ((1 : ℝ≥0∞) / Fintype.card (Axis n ℓ × BitVec n))
          * (S.card : ℝ≥0∞) := by
  classical
  set mass : ℝ≥0∞ :=
      (1 : ℝ≥0∞) / Fintype.card (Axis n ℓ × BitVec n) with hmass_def
  have hconst :
      ∀ ρ : ExactRestriction n ℓ, restrictionUniform n ℓ ρ = mass := by
    intro ρ
    simpa [mass, hmass_def] using restrictionUniform_apply (n := n) (ℓ := ℓ) ρ
  have hrewrite :
      (∑ ρ in S, restrictionUniform n ℓ ρ)
        = ∑ ρ in S, mass := by
    refine Finset.sum_congr rfl ?_
    intro ρ hρ
    simpa [hconst ρ]
  have hsum_const :
      (∑ _ρ in S, mass) = mass * (S.card : ℝ≥0∞) := by
    simpa [nsmul_eq_mul]
      using (Finset.sum_const (s := S) (a := mass)).symm
  simpa [hrewrite, mass, hmass_def]
    using hsum_const.symm

/--
  Объединение «плохих» рестрикций для списка формул.  Это множество содержит
  все точные ограничения, для которых хотя бы одна формула из `Fs`
  порождает хвост глубины `> t` на оси длины `ℓ`.
-/
@[simp] def badSetList :
    List (Core.CNF n w) → Finset (ExactRestriction n ℓ)
  | [] => ∅
  | F :: Fs =>
      badSet (n := n) (ℓ := ℓ) (w := w) F t
        ∪ badSetList (n := n) (ℓ := ℓ) (w := w) Fs t

@[simp] lemma badSetList_nil :
    badSetList (n := n) (ℓ := ℓ) (w := w) ([] : List (Core.CNF n w)) t = ∅ := rfl

@[simp] lemma badSetList_cons (F : Core.CNF n w) (Fs : List (Core.CNF n w)) :
    badSetList (n := n) (ℓ := ℓ) (w := w) (F :: Fs) t
      = badSet (n := n) (ℓ := ℓ) (w := w) F t
          ∪ badSetList (n := n) (ℓ := ℓ) (w := w) Fs t := rfl

/--
  Рекурсивная верхняя граница на мощность объединения «плохих» множеств.
  Это натуральное число равно сумме кардиналов индивидуальных `badSet`.
-/
@[simp] def badSetListCardBound :
    List (Core.CNF n w) → Nat
  | [] => 0
  | F :: Fs =>
      (badSet (n := n) (ℓ := ℓ) (w := w) F t).card
        + badSetListCardBound (n := n) (ℓ := ℓ) (w := w) Fs t

/--
  Мощность объединения `badSetList` не превосходит суммы мощностей
  индивидуальных «плохих» множеств.  Это дискретная версия union bound,
  полученная прямой индукцией по списку формул.
-/
lemma badSetList_card_le_cardBound
    (Fs : List (Core.CNF n w)) :
    (badSetList (n := n) (ℓ := ℓ) (w := w) Fs t).card
      ≤ badSetListCardBound (n := n) (ℓ := ℓ) (w := w) Fs t := by
  classical
  induction Fs with
  | nil => simpa
  | cons F Fs ih =>
      have hcard_union :
          (badSet (n := n) (ℓ := ℓ) (w := w) F t ∪
              badSetList (n := n) (ℓ := ℓ) (w := w) Fs t).card
            ≤ (badSet (n := n) (ℓ := ℓ) (w := w) F t).card
                + (badSetList (n := n) (ℓ := ℓ) (w := w) Fs t).card :=
        Finset.card_union_le _ _
      have hrest := ih
      have hrest' :
          (badSetList (n := n) (ℓ := ℓ) (w := w) Fs t).card
            ≤ badSetListCardBound (n := n) (ℓ := ℓ) (w := w) Fs t := hrest
      have htotal :=
        Nat.add_le_add_left hrest'
          ((badSet (n := n) (ℓ := ℓ) (w := w) F t).card)
      refine hcard_union.trans ?_
      simpa using htotal

/--
  Перевод дискретного bound'а на мощность в bound на суммарную массу:
  поскольку все рестрикции имеют одинаковый вес, общий вес объединения
  не превышает суммы весов для каждой формулы по отдельности.
-/
lemma badSetList_mass_le
    (Fs : List (Core.CNF n w)) :
    ((1 : ℝ≥0∞) / Fintype.card (Axis n ℓ × BitVec n))
        * ((badSetList (n := n) (ℓ := ℓ) (w := w) Fs t).card : ℝ≥0∞)
      ≤
        (badSetListCardBound (n := n) (ℓ := ℓ) (w := w) Fs t : ℝ≥0∞)
            * ((1 : ℝ≥0∞) / Fintype.card (Axis n ℓ × BitVec n)) := by
  classical
  have hcard :=
    badSetList_card_le_cardBound (n := n) (ℓ := ℓ) (w := w) (t := t) Fs
  have hmass_nonneg :
      0 ≤ ((1 : ℝ≥0∞) / Fintype.card (Axis n ℓ × BitVec n)) := by
    exact zero_le _
  have hcast :
      ((badSetList (n := n) (ℓ := ℓ) (w := w) Fs t).card : ℝ≥0∞)
        ≤ (badSetListCardBound (n := n) (ℓ := ℓ) (w := w) Fs t : ℝ≥0∞) := by
    exact_mod_cast hcard
  have hmul :=
    mul_le_mul_of_nonneg_right hcast hmass_nonneg
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

/-- Простая версия union bound для сумм `ℝ≥0∞`: сумма по объединению не превосходит
    сумму по каждому множеству. -/
lemma sum_union_le {α : Type*} [DecidableEq α]
    (f : α → ℝ≥0∞) (s t : Finset α) :
    (∑ x in s ∪ t, f x)
      ≤ (∑ x in s, f x) + ∑ x in t, f x := by
  classical
  have hdecompose : (s ∪ t) = s ∪ (t \ s) := by
    ext x; by_cases hx : x ∈ s <;> by_cases hy : x ∈ t <;> simp [hx, hy]
  have hdisjoint : Disjoint s (t \ s) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hx hx'
    rcases Finset.mem_sdiff.mp hx' with ⟨hmem, hnot⟩
    exact hnot hx
  have hsplit :=
    Finset.sum_union (s := s) (t := t \ s) (f := f) hdisjoint
  have hsubset : t \ s ⊆ t := by
    intro x hx; exact (Finset.mem_sdiff.mp hx).1
  have htail_le : (∑ x in t \ s, f x) ≤ ∑ x in t, f x :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ => le_of_eq (by simp))
  have hrewrite := by
    simpa [hsplit, hdecompose, add_comm, add_left_comm, add_assoc]
  have hrewrite' :
      (∑ x in s, f x) + ∑ x in t \ s, f x
        ≤ (∑ x in s, f x) + ∑ x in t, f x := by
    have := add_le_add_left htail_le (∑ x in s, f x)
    simpa [add_comm, add_left_comm, add_assoc] using this
  exact (le_trans (by simpa [hsplit, hdecompose] using le_of_eq hrewrite)
    hrewrite')

/-- `badMass` совпадает с суммой весов по множеству `badSet`. -/
lemma badMass_eq_sum (F : Core.CNF n w) :
    badMass (n := n) (ℓ := ℓ) (w := w) F t
      = ∑ ρ in badSet (n := n) (ℓ := ℓ) (w := w) F t,
          restrictionUniform n ℓ ρ := by
  classical
  unfold badMass badSet
  have := (Finset.sum_filter
    (s := Finset.univ)
    (f := fun ρ : ExactRestriction n ℓ => restrictionUniform n ℓ ρ)
    (p := fun ρ => BadRestriction (n := n) (ℓ := ℓ) (w := w) F t ρ)).symm
  simpa using this

/-- Сумма весов по объединению `badSetList` оценивается через сумму `badMass`. -/
lemma badSetList_mass_le_sum
    (Fs : List (Core.CNF n w)) :
    (∑ ρ in badSetList (n := n) (ℓ := ℓ) (w := w) Fs t,
        restrictionUniform n ℓ ρ)
      ≤
        (Fs.foldr
          (fun F acc => badMass (n := n) (ℓ := ℓ) (w := w) F t + acc)
          0) := by
  classical
  induction Fs with
  | nil =>
      simp
  | cons F Fs ih =>
      have hunion :
          badSetList (n := n) (ℓ := ℓ) (w := w) (F :: Fs) t
            = badSet (n := n) (ℓ := ℓ) (w := w) F t
                ∪ badSetList (n := n) (ℓ := ℓ) (w := w) Fs t := by simp
      have hsum :=
        sum_union_le (f := fun ρ => restrictionUniform n ℓ ρ)
          (s := badSet (n := n) (ℓ := ℓ) (w := w) F t)
          (t := badSetList (n := n) (ℓ := ℓ) (w := w) Fs t)
      have hhead :
          badMass (n := n) (ℓ := ℓ) (w := w) F t
            = ∑ ρ in badSet (n := n) (ℓ := ℓ) (w := w) F t,
                restrictionUniform n ℓ ρ :=
        badMass_eq_sum (n := n) (ℓ := ℓ) (w := w) (F := F) (t := t)
      have :=
        le_trans (by simpa [hunion] using hsum) (add_le_add_left ih _)
      simpa [hhead, List.foldr, add_comm, add_left_comm, add_assoc]
        using this

/--
  Сумма масс «плохих» рестрикций — удобная вспомогательная функция, которая
  совпадает с правой частью леммы `badSetList_mass_le_sum`.  Мы явно выносим
  её в отдельное обозначение, чтобы далее свободно подменять каждое слагаемое
  на более грубую оценку.
-/
@[simp] def badMassSum : List (Core.CNF n w) → ℝ≥0∞
  | [] => 0
  | F :: Fs =>
      badMass (n := n) (ℓ := ℓ) (w := w) F t
        + badMassSum (n := n) (ℓ := ℓ) (w := w) Fs t

/--
  Удобное обозначение для суммирования по числу клауз с фиксированным
  p-biased множителем.  В дальнейшем это выражение появится в оценках, когда
  мы заменяем каждую `badMass` на верхнюю границу вида
  `(F.clauses.length : ℝ≥0∞) * θ`.
-/
@[simp] def clauseWeightSum (θ : ℝ≥0∞) : List (Core.CNF n w) → ℝ≥0∞
  | [] => 0
  | F :: Fs =>
      (F.clauses.length : ℝ≥0∞) * θ
        + clauseWeightSum (n := n) (ℓ := ℓ) (w := w) (t := t) θ Fs

@[simp] lemma badMassSum_nil :
    badMassSum (n := n) (ℓ := ℓ) (w := w) (t := t) ([] : List (Core.CNF n w)) = 0 :=
  rfl

@[simp] lemma badMassSum_cons (F : Core.CNF n w) (Fs : List (Core.CNF n w)) :
    badMassSum (n := n) (ℓ := ℓ) (w := w) (t := t) (F :: Fs)
      = badMass (n := n) (ℓ := ℓ) (w := w) F t
          + badMassSum (n := n) (ℓ := ℓ) (w := w) (t := t) Fs :=
  rfl

@[simp] lemma clauseWeightSum_nil (θ : ℝ≥0∞) :
    clauseWeightSum (n := n) (ℓ := ℓ) (w := w) (t := t) θ ([] : List (Core.CNF n w)) = 0 :=
  rfl

@[simp] lemma clauseWeightSum_cons (θ : ℝ≥0∞)
    (F : Core.CNF n w) (Fs : List (Core.CNF n w)) :
    clauseWeightSum (n := n) (ℓ := ℓ) (w := w) (t := t) θ (F :: Fs)
      = (F.clauses.length : ℝ≥0∞) * θ
          + clauseWeightSum (n := n) (ℓ := ℓ) (w := w) (t := t) θ Fs :=
  rfl

/--
  Прямая индукция по списку формул: если каждое слагаемое `badMass` заменяется
  на более грубую оценку `(F.clauses.length : ℝ≥0∞) * θ`, то сумма также
  увеличивается.  Эта лемма позволяет связать `badMassSum` с суммой по числу
  клауз.
-/
lemma badMassSum_le_clauseWeightSum (θ : ℝ≥0∞)
    (Fs : List (Core.CNF n w))
    (hbound : ∀ {F : Core.CNF n w}, F ∈ Fs →
        badMass (n := n) (ℓ := ℓ) (w := w) F t
          ≤ (F.clauses.length : ℝ≥0∞) * θ) :
    badMassSum (n := n) (ℓ := ℓ) (w := w) (t := t) Fs
      ≤ clauseWeightSum (n := n) (ℓ := ℓ) (w := w) (t := t) θ Fs := by
  classical
  induction Fs with
  | nil =>
      simp
  | cons F Fs ih =>
      have hF : F ∈ F :: Fs := by simp
      have hrest : ∀ {F' : Core.CNF n w}, F' ∈ Fs →
          badMass (n := n) (ℓ := ℓ) (w := w) F' t
            ≤ (F'.clauses.length : ℝ≥0∞) * θ := by
        intro F' hF'
        exact hbound (by simp [hF'] )
      have hhead := hbound (by simp)
      have htail := ih hrest
      have hsum := add_le_add hhead htail
      simpa [badMassSum_cons, clauseWeightSum_cons, add_comm, add_left_comm,
        add_assoc]
        using hsum

/--
  Масса объединения «плохих» рестрикций оценивается через сумму по числу
  клауз, если для каждой формулы выполняется bound вида `(p · t)^t`.
-/
lemma badSetList_mass_le_clauseWeightSum (Fs : List (Core.CNF n w))
    (θ : ℝ≥0∞)
    (hbound : ∀ {F : Core.CNF n w}, F ∈ Fs →
        badMass (n := n) (ℓ := ℓ) (w := w) F t
          ≤ (F.clauses.length : ℝ≥0∞) * θ) :
    (∑ ρ in badSetList (n := n) (ℓ := ℓ) (w := w) Fs t,
        restrictionUniform n ℓ ρ)
      ≤ clauseWeightSum (n := n) (ℓ := ℓ) (w := w) (t := t) θ Fs := by
  classical
  have hmass := badSetList_mass_le_sum
    (n := n) (ℓ := ℓ) (w := w) (t := t) (Fs := Fs)
  have hrewrite :
      (Fs.foldr
          (fun F acc => badMass (n := n) (ℓ := ℓ) (w := w) F t + acc)
          0)
        = badMassSum (n := n) (ℓ := ℓ) (w := w) (t := t) Fs := by
    induction Fs with
    | nil => simp [badMassSum]
    | cons F Fs ih =>
        simp [badMassSum_cons, ih, add_comm, add_left_comm, add_assoc]
  have hsumBound :=
    badMassSum_le_clauseWeightSum
      (n := n) (ℓ := ℓ) (w := w) (t := t)
      (θ := θ) (Fs := Fs) hbound
  simpa [hrewrite] using hmass.trans hsumBound

/--
  Каждое индивидуальное «плохое» множество входит в объединение `badSetList`.
  Это простая индукция по списку формул, необходимая для переноса оценок с
  объединения обратно на каждую формулу.
-/
lemma badSet_subset_badSetList
    (Fs : List (Core.CNF n w)) (F : Core.CNF n w)
    (hF : F ∈ Fs) :
    badSet (n := n) (ℓ := ℓ) (w := w) F t
      ⊆ badSetList (n := n) (ℓ := ℓ) (w := w) Fs t := by
  classical
  induction Fs with
  | nil =>
      cases hF
  | cons F₀ Fs ih =>
      by_cases hcase : F = F₀
      · subst hcase
        intro ρ hρ
        have : ρ ∈ badSet (n := n) (ℓ := ℓ) (w := w) F₀ t := hρ
        have hmem :
            ρ ∈ badSet (n := n) (ℓ := ℓ) (w := w) F₀ t ∪
                badSetList (n := n) (ℓ := ℓ) (w := w) Fs t := by
          exact Finset.mem_union.mpr (Or.inl this)
        simpa using hmem
      · have hmem : F ∈ Fs := by
          simpa [hcase] using (List.mem_cons.1 hF).resolve_left hcase
        intro ρ hρ
        have hrec := ih hmem hρ
        have : ρ ∈ badSetList (n := n) (ℓ := ℓ) (w := w) Fs t := hrec
        have hmem :
            ρ ∈ badSet (n := n) (ℓ := ℓ) (w := w) F₀ t ∪
                badSetList (n := n) (ℓ := ℓ) (w := w) Fs t := by
          exact Finset.mem_union.mpr (Or.inr this)
        simpa using hmem

/--
  Фильтр по заданной оси сохраняет вложение между `badSet` и `badSetList`.
-/
lemma badSet_filter_subset_badSetList_filter
    (Fs : List (Core.CNF n w)) (F : Core.CNF n w)
    (hF : F ∈ Fs) (A : Axis n ℓ) :
    (badSet (n := n) (ℓ := ℓ) (w := w) F t).filter
        (fun ρ : ExactRestriction n ℓ => ρ.axis = A)
      ⊆
        (badSetList (n := n) (ℓ := ℓ) (w := w) Fs t).filter
          (fun ρ : ExactRestriction n ℓ => ρ.axis = A) := by
  intro ρ hρ
  have hsubset := badSet_subset_badSetList
    (n := n) (ℓ := ℓ) (w := w) (t := t)
    (Fs := Fs) (F := F) hF
  have hmem := Finset.mem_filter.mp hρ
  have hmem' : ρ ∈ badSetList (n := n) (ℓ := ℓ) (w := w) Fs t :=
    hsubset hmem.1
  exact Finset.mem_filter.mpr ⟨hmem', hmem.2⟩

/--
  Сумма масс по всем осям равна общей массе множества `S`.  Этот факт
  отражает разбиение точных рестрикций по их оси и играет ключевую роль в
  аргументе усреднения.
-/
lemma restrictionUniform_sum_split (S : Finset (ExactRestriction n ℓ)) :
    (∑ A : Axis n ℓ,
        ∑ ρ in S.filter (fun ρ => ρ.axis = A), restrictionUniform n ℓ ρ)
      = ∑ ρ in S, restrictionUniform n ℓ ρ := by
  classical
  -- Вес каждого элемента в равномерном распределении постоянен.
  set mass : ℝ≥0∞ :=
      (1 : ℝ≥0∞) / Fintype.card (Axis n ℓ × BitVec n) with hmass_def
  have hconst :
      ∀ ρ : ExactRestriction n ℓ, restrictionUniform n ℓ ρ = mass := by
    intro ρ; simpa [mass, hmass_def] using restrictionUniform_apply (n := n) (ℓ := ℓ) ρ
  -- Каждая сумма по фильтру — это константа `mass`, умноженная на количество
  -- элементов в фильтре.
  have hfiber (A : Axis n ℓ) :
      (∑ ρ in S.filter (fun ρ => ρ.axis = A), restrictionUniform n ℓ ρ)
        = mass * ((S.filter fun ρ => ρ.axis = A).card : ℝ≥0∞) := by
    have := Finset.sum_const (s := S.filter fun ρ : ExactRestriction n ℓ => ρ.axis = A)
      (a := mass)
    simpa [hconst, nsmul_eq_mul] using this.symm
  -- Складываем по всем осям и применяем известную формулу для суммирования
  -- кардинальностей фильтров.
  have hsplit :
      (∑ A : Axis n ℓ,
          ∑ ρ in S.filter (fun ρ => ρ.axis = A), restrictionUniform n ℓ ρ)
        = mass * (∑ A : Axis n ℓ,
            ((S.filter fun ρ => ρ.axis = A).card : ℝ≥0∞)) := by
    classical
    simp [hfiber, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
  -- Сумма кардинальностей фильтров равна общей мощности `S`.
  have hcard :
      (∑ A : Axis n ℓ,
          ((S.filter fun ρ => ρ.axis = A).card : ℝ≥0∞))
        = (S.card : ℝ≥0∞) := by
    simpa using congrArg (fun k : ℕ => (k : ℝ≥0∞))
      (sum_card_filter_eq_card (s := S)
        (f := fun ρ : ExactRestriction n ℓ => ρ.axis))
  -- Подставляем равенство массы из леммы `restrictionUniform_sum_eq_mass_mul_card`.
  have htotal := restrictionUniform_sum_eq_mass_mul_card
    (n := n) (ℓ := ℓ) (S := S)
  -- Финальный расчёт.
  calc
    (∑ A : Axis n ℓ,
        ∑ ρ in S.filter (fun ρ => ρ.axis = A), restrictionUniform n ℓ ρ)
        = mass * (S.card : ℝ≥0∞) := by
            simpa [hsplit, hcard]
    _ = ∑ ρ in S, restrictionUniform n ℓ ρ := by
            simpa [mass, hmass_def] using htotal

/--
  Если суммарная масса множества точных рестрикций ограничена сверху, то можно
  выбрать ось, на которой условная масса не превосходит среднего значения.
  Это прямой аргумент через минимальное слагаемое в сумме из леммы
  `restrictionUniform_sum_split`.
-/
lemma exists_axis_filter_mass_le
    (S : Finset (ExactRestriction n ℓ))
    (hℓn : ℓ ≤ n)
    (bound : ℝ≥0∞)
    (hmass : ∑ ρ in S, restrictionUniform n ℓ ρ ≤ bound) :
    ∃ A : Axis n ℓ,
      (∑ ρ in S.filter (fun ρ => ρ.axis = A), restrictionUniform n ℓ ρ)
        ≤ bound / (Nat.choose n ℓ : ℝ≥0∞) := by
  classical
  -- Сумма по осям равна общей массе: берём ось с минимальным вкладом.
  have hsplit := restrictionUniform_sum_split
    (n := n) (ℓ := ℓ) (S := S)
  have hnonempty : (Finset.univ : Finset (Axis n ℓ)).Nonempty := by
    obtain ⟨A⟩ := RandomRestriction.Axis.nonempty (n := n) (ℓ := ℓ) hℓn
    exact ⟨A, by simp⟩
  let axes := (Finset.univ : Finset (Axis n ℓ))
  obtain ⟨A₀, hA₀_mem, hmin⟩ :=
    (Finset.exists_min_image (s := axes)
      (fun A =>
        ∑ ρ in S.filter (fun ρ : ExactRestriction n ℓ => ρ.axis = A),
          restrictionUniform n ℓ ρ) hnonempty)
  set massFiber :=
    fun A : Axis n ℓ =>
      ∑ ρ in S.filter (fun ρ : ExactRestriction n ℓ => ρ.axis = A),
        restrictionUniform n ℓ ρ
    with hmassFiber_def
  have hmin_le : ∀ A ∈ axes, massFiber A₀ ≤ massFiber A := by
    intro A hA; simpa [hmassFiber_def] using hmin A hA
  have hsum_ge :
      (axes.card : ℝ≥0∞) * massFiber A₀
        ≤ ∑ A in axes, massFiber A := by
    have hsum := Finset.sum_le_sum
      (s := axes) (t := axes)
      (f := fun _ : Axis n ℓ => massFiber A₀)
      (g := massFiber)
      (fun A hA => hmin_le A hA)
    simpa [massFiber, Finset.sum_const, nsmul_eq_mul, mul_comm, mul_left_comm,
      mul_assoc]
      using hsum
  have hsplit_total : ∑ A in axes, massFiber A = ∑ ρ in S, restrictionUniform n ℓ ρ := by
    simpa [massFiber] using hsplit
  have hsum_ge_total :
      (axes.card : ℝ≥0∞) * massFiber A₀
        ≤ ∑ ρ in S, restrictionUniform n ℓ ρ := by
    simpa [hsplit_total]
      using hsum_ge
  have htotal_ge :
      (axes.card : ℝ≥0∞) * massFiber A₀ ≤ bound :=
    hsum_ge_total.trans hmass
  have hcard_eq : (axes.card : ℝ≥0∞) = (Nat.choose n ℓ : ℝ≥0∞) := by
    simpa using congrArg (fun k : ℕ => (k : ℝ≥0∞))
      (RandomRestriction.axis_card_choose (n := n) (ℓ := ℓ))
  have hchoose_pos : (0 : ℝ≥0∞) < (Nat.choose n ℓ : ℝ≥0∞) := by
    by_cases hℓ0 : ℓ = 0
    · subst hℓ0; simp
    · have hpos : 0 < ℓ := Nat.pos_of_ne_zero hℓ0
      exact_mod_cast Nat.choose_pos hpos hℓn
  have hdiv :=
    mul_le_mul_of_nonneg_right htotal_ge
      (show 0 ≤ ((Nat.choose n ℓ : ℝ≥0∞) : ℝ≥0∞)⁻¹
        from inv_nonneg.mpr (le_of_lt hchoose_pos))
  have hmassFiber_bound :
      massFiber A₀ ≤ bound / (Nat.choose n ℓ : ℝ≥0∞) := by
    simpa [div_eq_mul_inv, hcard_eq, mul_comm, mul_left_comm, mul_assoc]
      using hdiv
  refine ⟨A₀, ?_⟩
  simpa [hmassFiber_def]
    using hmassFiber_bound

/--
  Объединённая версия леммы `exists_axis_errU_le`: для списка CNF-массивов
  существует ось, на которой число плохих листьев (а значит, и ошибка `errU`)
  контролируется суммарным bound'ом `badBound`.
-/
lemma exists_axis_errU_le_list
    (Fs : List (Core.CNF n w)) (ℓ t : Nat)
    (hsubset : ∀ {F : Core.CNF n w}, F ∈ Fs →
        badSet (n := n) (ℓ := ℓ) (w := w) F t
          ⊆ formulaBadFamily (n := n) (ℓ := ℓ) (w := w) F t)
    (hℓn : ℓ ≤ n) (htℓ : t ≤ ℓ) (htw : t ≤ w)
    (p : ℝ≥0∞)
    (hp :
      ((1 : ℝ≥0∞) / (2 ^ n : ℝ≥0∞))
          * (Nat.choose w t : ℝ≥0∞)
          * (((ℓ : ℝ≥0∞) / (n - ℓ + 1 : ℝ≥0∞)) * (2 : ℝ≥0∞)) ^ t
          * (1 + ((ℓ : ℝ≥0∞) / (n - ℓ + 1 : ℝ≥0∞)) * (2 : ℝ≥0∞))
              ^ (w - t)
        ≤ (p * (t : ℝ≥0∞)) ^ t)
    (tailSelectors : ∀ A : Axis n ℓ,
        ∀ β, β ∈ Axis.leafList (n := n) (ℓ := ℓ) A →
          (BitVec n → Bool) → List (Subcube n))
    (hmismatch : ∀ A : Axis n ℓ, ∀ {F : Core.CNF n w}, F ∈ Fs →
        ∀ x,
          F.eval x ≠ coveredB
            (selectorsFromTails (n := n) (ℓ := ℓ) (A := A)
              (tailSelectors := tailSelectors A) F.eval) x →
          Axis.leafForPoint (n := n) (ℓ := ℓ) A x
            ∈ badLeafFamily (n := n) (w := w) F ℓ t A)
    (badBound : Nat)
    (hbound :
      clauseWeightSum (n := n) (ℓ := ℓ) (w := w) (t := t)
          ((p * (t : ℝ≥0∞)) ^ t) Fs
        * (2 ^ n : ℝ≥0∞)
        ≤ (badBound : ℝ≥0∞)) :
    ∃ A : Axis n ℓ,
      ∀ {F : Core.CNF n w}, F ∈ Fs →
        errU F.eval
          (selectorsFromTails (n := n) (ℓ := ℓ) (A := A)
            (tailSelectors := tailSelectors A) F.eval)
          ≤ (badBound : Q) / ((Nat.pow 2 ℓ : Nat) : Q) := by
  classical
  -- Сначала получаем bound на массу объединения `badSetList`.
  have hmass_list := badSetList_mass_le_clauseWeightSum
    (n := n) (ℓ := ℓ) (w := w) (t := t) (Fs := Fs)
    (θ := (p * (t : ℝ≥0∞)) ^ t)
    (by
      intro F hF
      have := badMass_le_clauseCount_pt
        (n := n) (ℓ := ℓ) (w := w) (F := F) (t := t)
        (hsubset := hsubset hF) hℓn htℓ htw (p := p) hp
      simpa using this)
  -- Существование оси с контролируемой массой.
  obtain ⟨A, hA_mass⟩ := exists_axis_filter_mass_le
    (n := n) (ℓ := ℓ)
    (S := badSetList (n := n) (ℓ := ℓ) (w := w) Fs t)
    (hℓn := hℓn)
    (bound := clauseWeightSum (n := n) (ℓ := ℓ) (w := w) (t := t)
      ((p * (t : ℝ≥0∞)) ^ t) Fs)
    (hmass := hmass_list)
  -- Выражаем массу через количество элементов.
  set mass : ℝ≥0∞ :=
      (1 : ℝ≥0∞) / Fintype.card (Axis n ℓ × BitVec n) with hmass_def
  have hconst :
      ∀ ρ : ExactRestriction n ℓ, restrictionUniform n ℓ ρ = mass := by
    intro ρ; simpa [mass, hmass_def]
      using restrictionUniform_apply (n := n) (ℓ := ℓ) ρ
  have hfiber_eq :
      ∑ ρ in
          (badSetList (n := n) (ℓ := ℓ) (w := w) Fs t).filter
            (fun ρ => ρ.axis = A), restrictionUniform n ℓ ρ
        = mass
            * (((badSetList (n := n) (ℓ := ℓ) (w := w) Fs t).filter
                  (fun ρ => ρ.axis = A)).card : ℝ≥0∞) := by
    have := Finset.sum_const
      (s := (badSetList (n := n) (ℓ := ℓ) (w := w) Fs t).filter
        fun ρ : ExactRestriction n ℓ => ρ.axis = A)
      (a := mass)
    simpa [hconst, nsmul_eq_mul]
      using this.symm
  have hmass_card := by
    simpa [hfiber_eq]
      using hA_mass
  -- Удаляем константный множитель и переходим к bound'у на количество.
  have hchoose := RandomRestriction.axis_card_choose (n := n) (ℓ := ℓ)
  have hbitvec := Core.card_bitVec (n := n)
  have hmass_choose :
      mass * (Nat.choose n ℓ : ℝ≥0∞)
        = (1 : ℝ≥0∞) / (2 ^ n : ℝ≥0∞) := by
    simp [mass, hmass_def, Fintype.card_prod, hchoose, hbitvec,
      mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]
  have hpow_pos :
      (0 : ℝ≥0∞) < (2 ^ n : ℝ≥0∞) := by
    exact_mod_cast pow_pos (by decide : 0 < 2) n
  have hchoose_pos :
      (0 : ℝ≥0∞) < (Nat.choose n ℓ : ℝ≥0∞) := by
    exact_mod_cast Nat.choose_pos hℓn
  have hcard_union :
      (((badSetList (n := n) (ℓ := ℓ) (w := w) Fs t).filter
            (fun ρ : ExactRestriction n ℓ => ρ.axis = A)).card : ℝ≥0∞)
        ≤ clauseWeightSum (n := n) (ℓ := ℓ) (w := w) (t := t)
            ((p * (t : ℝ≥0∞)) ^ t) Fs
          * (2 ^ n : ℝ≥0∞) := by
    have hmul := mul_le_mul_of_nonneg_right hmass_card hchoose_pos.le
    have hmass_cancel :
        mass * ((Nat.choose n ℓ : ℝ≥0∞)
            * (((badSetList (n := n) (ℓ := ℓ) (w := w) Fs t).filter
                  (fun ρ => ρ.axis = A)).card : ℝ≥0∞)))
          ≤ clauseWeightSum (n := n) (ℓ := ℓ) (w := w) (t := t)
              ((p * (t : ℝ≥0∞)) ^ t) Fs := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    have hpow := mul_le_mul_of_nonneg_right hmass_cancel hpow_pos.le
    have hcancel :
        (mass * (Nat.choose n ℓ : ℝ≥0∞)) * (2 ^ n : ℝ≥0∞)
            * (((badSetList (n := n) (ℓ := ℓ) (w := w) Fs t).filter
                  (fun ρ => ρ.axis = A)).card : ℝ≥0∞)
          = (((badSetList (n := n) (ℓ := ℓ) (w := w) Fs t).filter
                (fun ρ => ρ.axis = A)).card : ℝ≥0∞) := by
      simp [hmass_choose, mul_comm, mul_left_comm, mul_assoc]
    simpa [hcancel, mul_comm, mul_left_comm, mul_assoc]
      using hpow
  -- Отсюда немедленно следует bound на каждое индивидуальное `badSet`.
  have hcard_each :
      ∀ {F : Core.CNF n w}, F ∈ Fs →
        ((badSet (n := n) (ℓ := ℓ) (w := w) F t).filter
            (fun ρ : ExactRestriction n ℓ => ρ.axis = A)).card
          ≤ ((badSetList (n := n) (ℓ := ℓ) (w := w) Fs t).filter
              (fun ρ : ExactRestriction n ℓ => ρ.axis = A)).card := by
    intro F hF
    refine Finset.card_le_of_subset ?_
    exact badSet_filter_subset_badSetList_filter
      (n := n) (ℓ := ℓ) (w := w) (t := t)
      (Fs := Fs) (F := F) hF (A := A)
  -- Переводим bound для рестрикций в bound для плохих листьев и далее в errU.
  refine ⟨A, ?_⟩
  intro F hF
  have hcard_badSet := hcard_each hF
  have hcard_leaf :
      ((badLeafFamily (n := n) (w := w) F ℓ t A).card : ℝ≥0∞)
        ≤ clauseWeightSum (n := n) (ℓ := ℓ) (w := w) (t := t)
            ((p * (t : ℝ≥0∞)) ^ t) Fs
          * (2 ^ n : ℝ≥0∞) := by
    have hleaf_le := badLeafFamily_card_le_badSet_axis_card
      (n := n) (w := w) (F := F) (ℓ := ℓ) (t := t) (A := A)
    have hcast :=
      (by exact_mod_cast hleaf_le) :
        ((badLeafFamily (n := n) (w := w) F ℓ t A).card : ℝ≥0∞)
          ≤ ((badSet (n := n) (ℓ := ℓ) (w := w) F t).filter
                (fun ρ : ExactRestriction n ℓ => ρ.axis = A)).card
    have hchain := hcast.trans (by exact_mod_cast hcard_badSet)
    have := hchain.trans hcard_union
    simpa using this
  have hcard_nat :
      (badLeafFamily (n := n) (w := w) F ℓ t A).card ≤ badBound := by
    exact_mod_cast hcard_leaf.trans hbound
  have herr := RandomRestriction.errU_selectorsFromTails_le_of_badLeaves
    (n := n) (ℓ := ℓ) (A := A)
    (tailSelectors := tailSelectors A)
    (f := F.eval)
    (badLeaves := badLeafFamily (n := n) (w := w) F ℓ t A)
    (hsubset := badLeafFamily_subset_leafList
      (n := n) (w := w) (F := F) (ℓ := ℓ) (t := t) (A := A))
    (hmismatch := hmismatch A hF)
  have hleaves_q :
      ((badLeafFamily (n := n) (w := w) F ℓ t A).card : Q)
        ≤ (badBound : Q) := by exact_mod_cast hcard_nat
  have hdenom_pos :
      0 < ((Nat.pow 2 ℓ : Nat) : Q) := by
    have htwo : 0 < (2 : Q) := by norm_num
    simpa [Nat.cast_pow] using pow_pos htwo ℓ
  have hdiv_le :
      ((badLeafFamily (n := n) (w := w) F ℓ t A).card : Q)
          / ((Nat.pow 2 ℓ : Nat) : Q)
        ≤ (badBound : Q) / ((Nat.pow 2 ℓ : Nat) : Q) := by
    have := mul_le_mul_of_nonneg_right hleaves_q
      (inv_nonneg.mpr hdenom_pos.le)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using this
  exact herr.trans hdiv_le


end Depth1Switching
end ThirdPartyFacts
end Pnp3

