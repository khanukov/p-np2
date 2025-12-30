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

/-!
  Дополнительные оценки глубины.

  В дальнейшем (при индукции по глубине AC⁰ и «склейке» хвостов) удобно
  знать, что реализованное дерево не может стать *меньше* ствола. Это
  гарантирует, что общие префиксные вопросы не «схлопываются» после
  уточнения хвостами.
-/

/-- Глубина реализованного дерева не меньше глубины ствола. -/
lemma trunk_depth_le_realize (C : PartialCertificate n ℓ F) :
    PDT.depth C.witness.trunk ≤ PDT.depth C.witness.realize := by
  simpa using (PartialDT.depth_trunk_le_realize (Q := C.witness))

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

/-!
  Важно также, что тот же факт автоматически переносится на `CommonPDT`,
  получаемый из частичного сертификата.  Это удобно, когда в доказательстве
  мы работаем уже с «полным» деревом, но хотим восстановить информацию о
  минимальной глубине, задаваемой стволом.
-/

/-- Глубина ствола не больше глубины дерева в `CommonPDT`. -/
lemma trunk_depth_le_commonPDT (C : PartialCertificate n ℓ F) :
    PDT.depth C.witness.trunk ≤ PDT.depth C.toCommonPDT.tree := by
  simpa [PartialCertificate.toCommonPDT] using
    (trunk_depth_le_realize (C := C))

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
