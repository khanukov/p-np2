/-
  pnp3/Core/ShrinkageWitness.lean

  Минимальный интерфейс между структурой `Shrinkage` и только что
  введёнными частичными PDT (`PartialDT`).  Эти вспомогательные функции
  служат «тонким адаптером»: они позволяют воспринимать любой shrinkage-
  сертификат как частичное дерево с нулевыми хвостами, а также явно
  извлекать оценку глубины и допустимую ошибку.

  Такой слой абстракции помогает отделить доказательства shrinkage (шаг A)
  от последующего анализа Covering/Leaf Budget (шаг B).  Внешние модули,
  которым важно знать лишь глубину и ошибку дерева, теперь могут работать
  с лаконичными обёртками `Shrinkage.depthBound` и `Shrinkage.errorBound`.
-/
import Core.PDT
import Core.PDTPartial
import Core.SAL_Core

namespace Pnp3
namespace Core

variable {n : Nat} [DecidableEq (Subcube n)]

/--
Любой shrinkage-сертификат можно рассматривать как частичное PDT без хвостов.
Мы просто берём исходное дерево `S.tree` в качестве "ствола" и приписываем
к каждому листу тривиальный хвост нулевой глубины.  Это удобная точка
стыковки с будущими доказательствами multi-switching: они будут строить
более сложные хвосты, но старая инфраструктура при этом продолжит работать.
-/
@[simp] def Shrinkage.partial (S : Shrinkage n) : PartialDT n 0 :=
  PartialDT.ofPDT S.tree

@[simp] lemma Shrinkage.partial_trunk (S : Shrinkage n) :
    (S.partial).trunk = S.tree := rfl

/--
Словарь, ассоциированный с `Shrinkage.partial`, совпадает со списком
листьев исходного PDT.  Лемма подчёркивает, что переход к частичному
дереву не меняет набор подкубов, используемых в атласе.
-/
@[simp] lemma Shrinkage.partial_leafDict (S : Shrinkage n) :
    (S.partial).leafDict = PDT.leaves S.tree := rfl

/-- Реализация частичного дерева из shrinkage совпадает с исходным PDT. -/
@[simp] lemma Shrinkage.partial_realize (S : Shrinkage n) :
    (S.partial).realize = S.tree := by
  simp [Shrinkage.partial]

/--
Число листьев в частичном дереве, полученном из shrinkage-свидетельства,
ограничено той же экспоненциальной функцией от глубины, что и исходное PDT.
Это наблюдение понадобится при оценке размеров словарей и бюджета листьев
в шаге B.
-/
lemma Shrinkage.partial_leafDict_length_le_pow (S : Shrinkage n) :
    (S.partial).leafDict.length ≤ Nat.pow 2 S.t := by
  classical
  have hbase :
      (S.partial).leafDict.length ≤ Nat.pow 2 (PDT.depth S.tree) := by
    have h := PartialDT.leafDict_length_le_pow_depth (Q := S.partial)
    have htmp := h
    simp at htmp
    exact htmp
  have hdepth := S.depth_le
  have hpow :
      Nat.pow 2 (PDT.depth S.tree) ≤ Nat.pow 2 S.t :=
    Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hdepth
  exact hbase.trans hpow

@[simp] lemma Shrinkage.partial_tail_depth_le (S : Shrinkage n)
    (β : Subcube n) (hβ : β ∈ PDT.leaves S.tree) :
    PDT.depth ((S.partial).tails β hβ) ≤ 0 := by
  change PDT.depth ((PartialDT.ofPDT S.tree).tails β hβ) ≤ 0
  have hzero : PDT.depth ((PartialDT.ofPDT S.tree).tails β hβ) = 0 := by
    simp [PartialDT.ofPDT, PDT.depth]
  have hle : 0 ≤ (0 : Nat) := Nat.le_refl 0
  exact Eq.subst (motive := fun d => d ≤ 0) (Eq.symm hzero) hle

/-- Явная оценка на глубину дерева из shrinkage. -/
@[simp] def Shrinkage.depthBound (S : Shrinkage n) : Nat :=
  S.t

lemma Shrinkage.depth_le_depthBound (S : Shrinkage n) :
    PDT.depth S.tree ≤ S.depthBound := by
  change PDT.depth S.tree ≤ S.t
  exact S.depth_le

/-- Допустимая ошибка из shrinkage-сертификата. -/
@[simp] def Shrinkage.errorBound (S : Shrinkage n) : Q :=
  S.ε

lemma Shrinkage.error_le_errorBound (S : Shrinkage n)
    (f : BitVec n → Bool) (hf : f ∈ S.F) :
    errU f (S.Rsel f) ≤ S.errorBound := by
  change errU f (S.Rsel f) ≤ S.ε
  exact S.err_le f hf

-- `PartialCertificate` аккумулирует данные, которые появляются после
-- доказательства shrinkage через частичное PDT.  Мы храним сам ствол с
-- хвостами, верхнюю границу на глубину ствола, допустимую ошибку и списки
-- листьев для каждой функции.
structure PartialCertificate (n ℓ : Nat) (F : Family n) : Type where
  /-- Частичное дерево решений, построенное на шаге shrinkage. -/
  witness        : PartialDT n ℓ
  /-- Верхняя граница на глубину ствола. -/
  depthBound     : Nat
  /-- Допустимая ошибка аппроксимации. -/
  epsilon        : Q
  /-- Доказательство того, что глубина ствола не превосходит `depthBound`. -/
  trunk_depth_le : PDT.depth witness.trunk ≤ depthBound
  /-- Списки листьев, которые выбираются для каждой функции семейства. -/
  selectors      : (BitVec n → Bool) → List (Subcube n)
  /-- Любой выбранный лист принадлежит `partial.realize`. -/
  selectors_sub  : ∀ {f : BitVec n → Bool} {β : Subcube n},
      f ∈ F → β ∈ selectors f → β ∈ PDT.leaves witness.realize
  /-- Ошибка аппроксимации по выбранным листьям. -/
  err_le         : ∀ {f : BitVec n → Bool}, f ∈ F →
      errU f (selectors f) ≤ epsilon
namespace PartialCertificate

variable {n ℓ : Nat} {F : Family n}

/--
  Уточняем селекторы частичного сертификата, разбивая каждый лист `β`
  на семейство более мелких подкубов `refine β f`.  Технически это ровно
  операция `List.bind` над исходным списком листьев, но мы позволяем
  уточнению зависеть от рассматриваемой функции `f`.  Конструкция
  пригодится при рекурсивном применении switching-лемм: после
  «дораскрытия» хвостов необходимо заменить каждый лист на все листья
  вновь появившегося поддерева, причём конкретный выбор может зависеть
  от ограничения функции на данный лист.
-/
def refineSelectors (C : PartialCertificate n ℓ F)
    (refine : Subcube n → (BitVec n → Bool) → List (Subcube n)) :
    (BitVec n → Bool) → List (Subcube n) :=
  fun f =>
    (C.selectors f).foldr (fun β acc => refine β f ++ acc) []

private lemma mem_refineSelectors_list
    (refine : Subcube n → (BitVec n → Bool) → List (Subcube n))
    (f : BitVec n → Bool) :
    ∀ {L : List (Subcube n)} {β : Subcube n},
      β ∈ List.foldr (fun γ acc => refine γ f ++ acc) [] L ↔
        ∃ γ ∈ L, β ∈ refine γ f
  | [], β => by simp
  | γ :: rest, β => by
      constructor
      · intro hβ
        have hcases : β ∈ refine γ f ∨
            β ∈ List.foldr (fun γ acc => refine γ f ++ acc) [] rest := by
          simpa [List.foldr, List.mem_append] using hβ
        cases hcases with
        | inl hγ =>
            exact ⟨γ, by simp, hγ⟩
        | inr hrest =>
            rcases (mem_refineSelectors_list refine f).1 hrest with
              ⟨δ, hδmem, hβδ⟩
            exact ⟨δ, by simp [List.mem_cons, hδmem], hβδ⟩
      · rintro ⟨δ, hδmem, hβδ⟩
        have hcases : δ = γ ∨ δ ∈ rest := by
          simpa [List.mem_cons] using hδmem
        have htarget :
            β ∈ refine γ f ++ List.foldr (fun γ acc => refine γ f ++ acc) [] rest := by
          cases hcases with
          | inl hδγ =>
              subst hδγ
              exact List.mem_append.mpr (Or.inl hβδ)
          | inr hδrest =>
              have hrest :
                  β ∈ List.foldr (fun γ acc => refine γ f ++ acc) [] rest :=
                (mem_refineSelectors_list refine f).2 ⟨δ, hδrest, hβδ⟩
              exact List.mem_append.mpr (Or.inr hrest)
        change β ∈ refine γ f ++ List.foldr (fun γ acc => refine γ f ++ acc) [] rest
        exact htarget

@[simp] lemma mem_refineSelectors_iff
    (C : PartialCertificate n ℓ F)
    (refine : Subcube n → (BitVec n → Bool) → List (Subcube n))
    {f : BitVec n → Bool} {β : Subcube n} :
    β ∈ C.refineSelectors refine f ↔
      ∃ γ ∈ C.selectors f, β ∈ refine γ f := by
  classical
  unfold refineSelectors
  exact (mem_refineSelectors_list (refine := refine)
    (f := f) (L := C.selectors f) (β := β))

lemma mem_refineSelectors
    (C : PartialCertificate n ℓ F)
    (refine : Subcube n → (BitVec n → Bool) → List (Subcube n))
    {f : BitVec n → Bool} {β γ : Subcube n}
    (hβ : β ∈ C.selectors f) (hγ : γ ∈ refine β f) :
    γ ∈ C.refineSelectors refine f := by
  classical
  exact (C.mem_refineSelectors_iff (refine := refine)).2 ⟨β, hβ, hγ⟩

lemma refineSelectors_subset
    (C : PartialCertificate n ℓ F)
    (refine : Subcube n → (BitVec n → Bool) → List (Subcube n))
    {P : (BitVec n → Bool) → Subcube n → Prop}
    (hbase : ∀ {f : BitVec n → Bool} {β γ : Subcube n},
      f ∈ F → β ∈ C.selectors f → γ ∈ refine β f → P f γ)
    {f : BitVec n → Bool} {γ : Subcube n}
    (hf : f ∈ F) (hγ : γ ∈ C.refineSelectors refine f) :
    P f γ := by
  rcases (C.mem_refineSelectors_iff refine).1 hγ with ⟨β, hβ, hγβ⟩
  exact hbase hf hβ hγβ

/--
  Пропозициональная версия утверждения: покрытие точки `x` уточнённым
  списком селекторов эквивалентно покрытию исходным списком.  Условие
  `hcover` формулирует точное соответствие между листом `β` и его
  «раскрытием» `refine β f`: объединение новых подкубов совпадает с самим
  `β`.  Именно такая ситуация возникает при разворачивании хвостов PDT,
  когда каждый лист заменяется на листья дочернего дерева.
-/
lemma covered_refineSelectors
    (C : PartialCertificate n ℓ F)
    (refine : Subcube n → (BitVec n → Bool) → List (Subcube n))
    (hcover : ∀ β f x, coveredB (refine β f) x = memB β x)
    {f : BitVec n → Bool} {x : BitVec n} :
    covered (C.refineSelectors refine f) x ↔
      covered (C.selectors f) x := by
  classical
  constructor
  · intro hcov
    rcases hcov with ⟨γ, hγ, hmemγ⟩
    rcases (C.mem_refineSelectors_iff (refine := refine)).1 hγ with
      ⟨β, hβ, hγβ⟩
    have hcovered : coveredB (refine β f) x = true := by
      have hx : covered (refine β f) x := ⟨γ, hγβ, hmemγ⟩
      exact (covered_iff (Rset := refine β f) (x := x)).mp hx
    have hmemB : memB β x = true := by
      simpa [hcover β f x] using hcovered
    have hmem : mem β x := (mem_iff_memB (β := β) (x := x)).mpr hmemB
    exact ⟨β, hβ, hmem⟩
  · rintro ⟨β, hβ, hmemβ⟩
    have hmemB : memB β x = true :=
      (mem_iff_memB (β := β) (x := x)).mp hmemβ
    have hcovered : coveredB (refine β f) x = true := by
      simpa [hcover β f x] using hmemB
    rcases (covered_iff (Rset := refine β f) (x := x)).mpr hcovered with
      ⟨γ, hγ, hmemγ⟩
    have hsel := C.mem_refineSelectors
      (refine := refine) (hβ := hβ) (hγ := hγ)
    exact ⟨γ, hsel, hmemγ⟩

/--
  Булева версия `covered_refineSelectors`.  Она удобна для переписывания
  функций покрытия внутри доказательств про ошибку `errU`, где важно
  именно булево значение `coveredB`.
-/
lemma coveredB_refineSelectors
    (C : PartialCertificate n ℓ F)
    (refine : Subcube n → (BitVec n → Bool) → List (Subcube n))
    (hcover : ∀ β f x, coveredB (refine β f) x = memB β x)
    (f : BitVec n → Bool) (x : BitVec n) :
    coveredB (C.refineSelectors refine f) x =
      coveredB (C.selectors f) x := by
  classical
  have htrue :
      coveredB (C.refineSelectors refine f) x = true ↔
        coveredB (C.selectors f) x = true := by
    calc
      coveredB (C.refineSelectors refine f) x = true ↔
          covered (C.refineSelectors refine f) x :=
            (covered_iff (Rset := C.refineSelectors refine f) (x := x)).symm
      _ ↔ covered (C.selectors f) x :=
            covered_refineSelectors (C := C) (refine := refine)
              (hcover := hcover)
      _ ↔ coveredB (C.selectors f) x = true :=
            (covered_iff (Rset := C.selectors f) (x := x))
  -- Перебираем два возможных булевых значения и исключаем несовместимые
  -- комбинации с помощью эквивалентности `htrue`.
  by_cases hselTrue : coveredB (C.selectors f) x = true
  · have hrefTrue : coveredB (C.refineSelectors refine f) x = true :=
      (htrue.mpr hselTrue)
    simp [hrefTrue, hselTrue]
  · have hselFalse : coveredB (C.selectors f) x = false := by
      cases hcase : coveredB (C.selectors f) x with
      | false => rfl
      | true =>
          have hcaseTrue : coveredB (C.selectors f) x = true := by
            simp [hcase]
          exact (hselTrue hcaseTrue).elim
    have hrefFalse : coveredB (C.refineSelectors refine f) x = false := by
      cases href : coveredB (C.refineSelectors refine f) x with
      | false => rfl
      | true =>
          have hrefTrue : coveredB (C.refineSelectors refine f) x = true := by
            simp [href]
          have hcaseTrue : coveredB (C.selectors f) x = true :=
            (htrue.mp hrefTrue)
          exact (hselTrue hcaseTrue).elim
    simp [hrefFalse, hselFalse]

/--
  Ошибка аппроксимации не меняется, если каждый лист `β` заменён на
  эквивалентный набор подкубов `refine β f`.  Формально это следует из
  совпадения булевых функций покрытия, установленного выше.
-/
lemma errU_refineSelectors_eq
    (C : PartialCertificate n ℓ F)
    (refine : Subcube n → (BitVec n → Bool) → List (Subcube n))
    (hcover : ∀ β f x, coveredB (refine β f) x = memB β x)
    (f : BitVec n → Bool) :
    errU f (C.refineSelectors refine f) = errU f (C.selectors f) := by
  classical
  have hfun :
      (fun x : BitVec n => f x ≠ coveredB (C.refineSelectors refine f) x)
        = (fun x : BitVec n => f x ≠ coveredB (C.selectors f) x) := by
    funext x
    have hcoverEq :=
      coveredB_refineSelectors (C := C) (refine := refine)
        (hcover := hcover) (f := f) (x := x)
    simp [hcoverEq]
  unfold errU
  simp [hfun]

/--
Из частичного свидетельства сразу получаем `CommonPDT`.  Глубина полного дерева
ограничена суммой глубины ствола и максимально допустимой глубины хвостов.
-/
def toCommonPDT (C : PartialCertificate n ℓ F) : CommonPDT n F :=
  { tree := C.witness.realize
    depthBound := C.depthBound + ℓ
    epsilon := C.epsilon
    depth_le := by
      have hreal := PartialDT.depth_realize_le (Q := C.witness)
      have hbound := Nat.add_le_add_right C.trunk_depth_le ℓ
      exact Nat.le_trans hreal hbound
    selectors := C.selectors
    selectors_sub := by
      intro f β hf hβ
      exact C.selectors_sub hf hβ
    err_le := by
      intro f hf
      exact C.err_le hf }

/--
Комбинируем частичное свидетельство в полноценный объект `Shrinkage`.
-/
def toShrinkage (C : PartialCertificate n ℓ F) : Shrinkage n :=
  { F := F
    t := C.depthBound + ℓ
    ε := C.epsilon
    tree := C.witness.realize
    depth_le := by
      have hreal := PartialDT.depth_realize_le (Q := C.witness)
      have hbound := Nat.add_le_add_right C.trunk_depth_le ℓ
      exact Nat.le_trans hreal hbound
    Rsel := C.selectors
    Rsel_sub := by
      intro f hf
      refine listSubset_of_mem ?_
      intro β hβ
      exact C.selectors_sub (f := f) (β := β) hf hβ
    err_le := by
      intro f hf
      exact C.err_le hf }

/-- Семейство функций в построенном shrinkage совпадает с исходным. -/
@[simp] lemma toShrinkage_family (C : PartialCertificate n ℓ F) :
    (C.toShrinkage).F = F := rfl

/-- Глубина PDT shrinkage равна `depthBound + ℓ`. -/
@[simp] lemma toShrinkage_depth (C : PartialCertificate n ℓ F) :
    (C.toShrinkage).t = C.depthBound + ℓ := rfl

/-- Ошибка shrinkage равна `epsilon`. -/
@[simp] lemma toShrinkage_epsilon (C : PartialCertificate n ℓ F) :
    (C.toShrinkage).ε = C.epsilon := rfl

/-- Списки листьев сохраняются при переходе к shrinkage. -/
@[simp] lemma toShrinkage_selectors (C : PartialCertificate n ℓ F)
    (f : BitVec n → Bool) :
    (C.toShrinkage).Rsel f = C.selectors f := rfl

/--
Любой shrinkage-сертификат порождает частичное свидетельство с нулевыми хвостами.
Это гарантирует обратную совместимость с прежним интерфейсом.
-/
def ofShrinkage (S : Shrinkage n) :
    PartialCertificate n 0 S.F :=
  { witness := S.partial
    depthBound := S.t
    epsilon := S.ε
    trunk_depth_le := by
      change PDT.depth S.tree ≤ S.t
      exact S.depth_le
    selectors := S.Rsel
    selectors_sub := by
      intro f β hf hβ
      have hsubset := S.Rsel_sub f hf
      have hmem := listSubset.mem (h := hsubset) (ha := hβ)
      have hrewrite :
          PDT.leaves (Shrinkage.partial S).realize = PDT.leaves S.tree := by
        have heq := congrArg PDT.leaves (Shrinkage.partial_realize (S := S))
        exact heq
      have hrewrite_symm := Eq.symm hrewrite
      exact Eq.subst (motive := fun s => β ∈ s) hrewrite_symm hmem
    err_le := by
      intro f hf
      exact S.err_le f hf }

/-- Переход `Shrinkage → PartialCertificate → Shrinkage` не меняет данных. -/
@[simp] lemma toShrinkage_ofShrinkage (S : Shrinkage n) :
    (ofShrinkage (S := S)).toShrinkage = S := by
  cases S
  simp [ofShrinkage, toShrinkage]

end PartialCertificate

end Core
end Pnp3
