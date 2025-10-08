/-
  pnp3/Core/SAL_Core.lean

  Ядро Switching-Atlas Lemma (SAL).
  Абстрагируем Shrinkage как наличие общего PDT малой глубины и выбора листьев для каждого f с малой ошибкой.
  Тогда SAL строит общий атлас из листьев PDT и утверждает, что он "работает" для семейства.
-/
import Mathlib.Data.List.Basic
import Core.BooleanBasics
import Core.PDT
import Core.Atlas

namespace Pnp3
namespace Core

/-- Семейство функций как список (для удобства перебора). -/
abbrev Family (n : Nat) := List (BitVec n → Bool)

/--
`CommonPDT F` описывает единое частичное решающее дерево, которое
аппроксимирует каждую функцию семейства `F` с одной и той же глубиной и
погрешностью.  Структура хранит:

* само дерево `tree` и допустимую верхнюю границу `depthBound` на его глубину;
* общую ошибку аппроксимации `epsilon`;
* функцию `selectors`, которая каждой функции сопоставляет подсписок листьев;
* доказательства, что выбранные листья действительно содержатся в `tree` и
  что ошибка не превосходит `epsilon`.

Такая запись удобна тем, что отделяет «конструктивную» часть shrinkage
сертификата (конкретное дерево) от последующей работы с атласами.  В дальнейшем
мы будем явно превращать `CommonPDT` в атлас и показывать, что он работает для
всего семейства.
-/
structure CommonPDT (n : Nat) [DecidableEq (Subcube n)]
    (F : Family n) where
  tree        : PDT n
  depthBound  : Nat
  epsilon     : Q
  depth_le    : PDT.depth tree ≤ depthBound
  selectors   : (BitVec n → Bool) → List (Subcube n)
  selectors_sub :
    ∀ {f : BitVec n → Bool} {β : Subcube n},
      f ∈ F → β ∈ selectors f → β ∈ PDT.leaves tree
  err_le :
    ∀ {f : BitVec n → Bool}, f ∈ F →
      errU f (selectors f) ≤ epsilon

namespace CommonPDT

variable {n : Nat} [DecidableEq (Subcube n)] {F : Family n}

/-- Атлас, полученный из общего PDT.  Словарь совпадает со списком листьев,
а допустимая погрешность равна `epsilon`. -/
def toAtlas (C : CommonPDT n F) : Atlas n :=
  Atlas.ofPDT C.tree C.epsilon

/-- Сценарий SAL: общий PDT автоматически задаёт атлас, работающий для всего
семейства функций.  Доказательство напрямую распаковывает поля структуры. -/
theorem worksFor (C : CommonPDT n F) : WorksFor C.toAtlas F := by
  intro f hf
  refine ⟨C.selectors f, ?_, ?_⟩
  · have hsubset : listSubset (C.selectors f) (C.toAtlas.dict) := by
      intro β hβ
      have hmem := C.selectors_sub (F := F) (f := f) (β := β) hf hβ
      change β ∈ (Atlas.ofPDT C.tree C.epsilon).dict
      dsimp [Atlas.ofPDT]
      exact hmem
    exact hsubset
  · have herr := C.err_le (F := F) hf
    change errU f (C.selectors f) ≤ (Atlas.ofPDT C.tree C.epsilon).epsilon
    dsimp [Atlas.ofPDT]
    exact herr

end CommonPDT

/-- Абстрактная "усадка" (Shrinkage):
    существует ОБЩЕЕ PDT глубины ≤ t и для каждого f ∈ F задан поднабор листьев (Rf),
    дающий ошибку ≤ ε. -/
structure Shrinkage (n : Nat) [DecidableEq (Subcube n)] where
  F        : Family n
  t        : Nat
  ε        : Q
  tree     : PDT n
  depth_le : PDT.depth tree ≤ t
  Rsel     : (BitVec n → Bool) → List (Subcube n)  -- выбор подмножеств листьев для каждого f
  Rsel_sub : ∀ f, f ∈ F → listSubset (Rsel f) (PDT.leaves tree)
  err_le   : ∀ f, f ∈ F → errU f (Rsel f) ≤ ε

/-- Любой shrinkage-сертификат содержит в себе явный `CommonPDT`. -/
def Shrinkage.commonPDT {n : Nat} [DecidableEq (Subcube n)]
    (S : Shrinkage n) : CommonPDT n S.F where
  tree := S.tree
  depthBound := S.t
  epsilon := S.ε
  depth_le := S.depth_le
  selectors := S.Rsel
  selectors_sub := by
    intro f β hf hβ
    have hsubset := S.Rsel_sub f hf
    exact listSubset.mem hsubset hβ
  err_le := by
    intro f hf
    exact S.err_le f hf

@[simp] lemma Shrinkage.commonPDT_tree {n : Nat} [DecidableEq (Subcube n)]
    (S : Shrinkage n) : S.commonPDT.tree = S.tree := rfl

@[simp] lemma Shrinkage.commonPDT_depthBound {n : Nat}
    [DecidableEq (Subcube n)] (S : Shrinkage n) :
    S.commonPDT.depthBound = S.t := rfl

@[simp] lemma Shrinkage.commonPDT_epsilon {n : Nat}
    [DecidableEq (Subcube n)] (S : Shrinkage n) :
    S.commonPDT.epsilon = S.ε := rfl

@[simp] lemma Shrinkage.commonPDT_selectors {n : Nat}
    [DecidableEq (Subcube n)] (S : Shrinkage n) (f : BitVec n → Bool) :
    S.commonPDT.selectors f = S.Rsel f := rfl

/-- Формулировка из плана проекта: из shrinkage следует существование общего PDT. -/
def shrinkage_to_commonPDT {n : Nat} [DecidableEq (Subcube n)]
    (S : Shrinkage n) : CommonPDT n S.F := S.commonPDT

/-- Вспомогательная лемма из плана: общий PDT сразу даёт атлас. -/
theorem commonPDT_to_atlas {n : Nat} [DecidableEq (Subcube n)]
    {F : Family n} (C : CommonPDT n F) : WorksFor C.toAtlas F :=
  C.worksFor

/-- SAL: из Shrinkage строим атлас с dict = листья PDT, ε = заданное, который "работает" для F. -/
theorem SAL_from_Shrinkage {n : Nat} [DecidableEq (Subcube n)]
  (S : Shrinkage n) :
  WorksFor (Atlas.ofPDT S.tree S.ε) S.F := by
  have h := (commonPDT_to_atlas (C := S.commonPDT))
  simp [CommonPDT.toAtlas, Atlas.ofPDT] at h
  exact h

/-- Удобная оболочка: сам атлас из Shrinkage. -/
def Atlas.fromShrinkage {n : Nat} [DecidableEq (Subcube n)]
  (S : Shrinkage n) : Atlas n :=
  Atlas.ofPDT S.tree S.ε

/-- Параметрический факт о размере словаря:
    число листьев PDT не превосходит `2^{depth}`. -/
theorem leaves_count_bound {n : Nat} (t : PDT n) :
  (PDT.leaves t).length ≤ Nat.pow 2 (PDT.depth t) :=
  PDT.leaves_length_le_pow_depth t

end Core
end Pnp3
