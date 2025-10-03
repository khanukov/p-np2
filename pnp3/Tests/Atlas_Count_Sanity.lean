import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
import Core.BooleanBasics
import Counting.Atlas_to_LB_Core

namespace Pnp3
namespace Tests

open Core Counting

open Classical

/-!
# Sanity-проверки подсчётов атласа

В этом файле мы приводим несколько вычислимых проверок для определения
`UnionClass` и вспомогательных конструкций из
`Counting/Atlas_to_LB_Core.lean`.  Цель — убедиться, что "реальная"
комбинаторика (при переборе маленьких словарей подкубов) согласуется с
теоретическими оценками.

Мы не претендуем на строгие доказательства общих фактов — для этого
предназначены теоремы в основном коде.  Вместо этого мы берём крошечные
примеры (`m = 2`, словарь из нескольких подкубов) и убеждаемся, что

* число уникальных объединений подкубов не превышает биномиальных
  комбинаций `∑_{i ≤ k} C(D, i)`;
* значения расстояния `distU` совпадают с "ручными" ожиданиями;
* построения действительно различают функции, которые должны различаться.
-/

/-- Удобный подкуб, фиксирующий один бит, остальные оставляющий свободными. -/
def fixBit {m : Nat} (i : Fin m) (b : Bool) : Subcube m :=
  fun j => if j = i then some b else none

/--
  Вспомогательное наблюдение: подкуб `fixBit i b` выдаёт `some c` на координате
  `j` тогда и только тогда, когда `j = i` и `c = b`.  В остальных случаях он
  возвращает `none`.  Формулируем в виде точной эквивалентности, чтобы
  переиспользовать в дальнейших вычислениях.
-/
lemma fixBit_eq_some_iff {m : Nat} (i j : Fin m) (b c : Bool) :
    fixBit (m := m) i b j = some c ↔ j = i ∧ c = b := by
  classical
  by_cases hji : j = i
  · subst hji
    constructor
    · intro h
      have hb' : some b = some c := by simpa [fixBit] using h
      have hb : b = c := Option.some.inj hb'
      exact ⟨rfl, hb.symm⟩
    · rintro ⟨-, hcb⟩
      simpa [fixBit, hcb.symm]
  · constructor
    · intro h
      have : False := by simpa [fixBit, hji] using h
      exact this.elim
    · intro h
      rcases h with ⟨hji', _⟩
      exact (hji hji').elim

/--
  Для подкуба `fixBit` проверка `memB` сводится к единственному ограничению на
  соответствующий бит: результат равен `true` ⇔ `x i = b`.
-/
lemma memB_fixBit_true_iff {m : Nat} (i : Fin m) (b : Bool)
    (x : Domain m) :
    Core.memB (fixBit (m := m) i b) x = true ↔ x i = b := by
  classical
  constructor
  · intro hmem
    have :=
      (Core.memB_eq_true_iff (β := fixBit (m := m) i b) (x := x)).mp hmem
    have hfix : fixBit (m := m) i b i = some b := by
      simp [fixBit]
    simpa using this i b hfix
  · intro hx
    have hcond : ∀ j : Fin m, ∀ c : Bool,
        fixBit (m := m) i b j = some c → x j = c := by
      intro j c hjc
      rcases (fixBit_eq_some_iff (m := m) (i := i) (j := j) (b := b)
          (c := c)).1 hjc with ⟨hji, hcb⟩
      subst hji
      subst hcb
      simpa using hx
    exact
      (Core.memB_eq_true_iff (β := fixBit (m := m) i b) (x := x)).mpr hcond

/-- Явная формула для покрытия одним подкубом `fixBit`. -/
lemma coveredB_fixBit (m : Nat) (i : Fin m) (b : Bool) (x : Domain m) :
    Core.coveredB [fixBit (m := m) i b] x =
      (if x i = b then true else false) := by
  classical
  have hmem := memB_fixBit_true_iff (m := m) (i := i) (b := b) (x := x)
  by_cases hx : x i = b
  · have : Core.memB (fixBit (m := m) i b) x = true := (hmem).2 hx
    simp [Core.coveredB, this, hx]
  · have hnot : Core.memB (fixBit (m := m) i b) x ≠ true := by
      intro htrue
      exact hx ((hmem).1 htrue)
    have : Core.memB (fixBit (m := m) i b) x = false := by
      cases hval : Core.memB (fixBit (m := m) i b) x
      · rfl
      · have : False := hnot (by simpa [hval])
        exact False.elim this
    simp [Core.coveredB, this, hx]

/-- Перечисление всех объединений ≤ `k` подкубов из словаря `R` в виде списков
значений на полном пространстве `BitVec m`.  Мы кодируем каждую функцию
её таблицей истинности (списком `Bool`), что позволяет сравнивать их на
равенство через `eraseDups`. -/
def unionEvalVectors {m : Nat} (R : List (Subcube m)) (k : Nat) :
    List (List Bool) :=
  let domain := allBitVec m
  let sublists := (List.sublists R).filter fun S => S.length ≤ k
  sublists.map (fun S => domain.map (fun x => coveredB S x))

/-- Число попарно различных объединений ≤ `k` подкубов из словаря `R`. -/
def unionCount {m : Nat} (R : List (Subcube m)) (k : Nat) : Nat :=
  ((unionEvalVectors (m := m) R k).eraseDups).length

/-- Конкретный словарь подкубов на `m = 2`.  Первый элемент фиксирует `x₀ = 1`,
второй — `x₀ = 0`.  Этого достаточно, чтобы проверить поведение объединений. -/
def sampleDict : List (Subcube 2) :=
  [fixBit (m := 2) 0 true, fixBit (m := 2) 0 false]

lemma sampleDict_length : sampleDict.length = 2 := by decide

/-- При ограничении `k = 1` возможны три различные функции:
* пустое объединение (всегда `false`),
* индикатор `x₀ = 1`,
* индикатор `x₀ = 0`.
-/
lemma unionCount_sampleDict_k1 : unionCount sampleDict 1 = 3 := by
  decide

/-- При `k = 2` появляется четвёртая функция — константа `true`, покрывающая
всё пространство. -/
lemma unionCount_sampleDict_k2 : unionCount sampleDict 2 = 4 := by
  decide

/-- Проверяем, что явные значения не превосходят биномиальные суммы. -/
lemma unionCount_sampleDict_k1_le_choose :
    unionCount sampleDict 1 ≤
      Nat.choose sampleDict.length 0 + Nat.choose sampleDict.length 1 := by
  decide

lemma unionCount_sampleDict_k2_le_choose :
    unionCount sampleDict 2 ≤
      Nat.choose sampleDict.length 0 +
        Nat.choose sampleDict.length 1 +
          Nat.choose sampleDict.length 2 := by
  decide

/-- Таблица истинности функции `x ↦ x₀` — удобный эталон для проверки `distU`. -/
def proj₀ : Domain 2 → Bool := fun x => x 0

/-- Постоянно ложная функция. -/
def zeroFunc : Domain 2 → Bool := fun _ => false

/-- Постоянно истинная функция. -/
def oneFunc : Domain 2 → Bool := fun _ => true

/-- Проверяем, что расстояние между `proj₀` и постоянно ложной функцией равно 2
(половина точек из четырёх).
-/
lemma dist_proj₀_zero : distU (m := 2) proj₀ zeroFunc = 2 := by
  decide

/-- Аналогично, расстояние между `proj₀` и константой `true` также равно 2. -/
lemma dist_proj₀_one : distU (m := 2) proj₀ oneFunc = 2 := by
  decide

/-- Для полного совпадения расстояние равно нулю. -/
lemma dist_proj₀_self : distU (m := 2) proj₀ proj₀ = 0 := by
  decide

/-- `proj₀` идеально аппроксимируется подкубом `x₀ = 1`. -/
lemma err_proj₀_fixTrue :
    errU (n := 2) proj₀ [fixBit (m := 2) 0 true] = 0 := by
  classical
  have hcover : ∀ x, proj₀ x = Core.coveredB [fixBit (m := 2) 0 true] x := by
    intro x
    cases hx : x 0 <;> simp [proj₀, coveredB_fixBit, hx]
  exact Core.errU_eq_zero_of_agree (f := proj₀)
    (Rset := [fixBit (m := 2) 0 true]) hcover

/-- Если не брать ни одного подкуба, ошибка для `proj₀` составляет ровно 1/2. -/
lemma err_proj₀_nil : errU (n := 2) proj₀ [] = (1 : ℚ) / 2 := by
  classical
  have hcov : (fun x => Core.coveredB ([] : List (Subcube 2)) x) = zeroFunc := by
    funext x; simp [zeroFunc]
  have hdist := dist_proj₀_zero
  have herr := errU_eq_distU_div_pow (m := 2) (f := proj₀) (S := [])
  have hpow : ((Nat.pow 2 2 : Nat) : ℚ) = 4 := by decide
  have hrewrite :
      errU (n := 2) proj₀ [] = (distU (m := 2) proj₀ zeroFunc : ℚ) / 4 := by
    simpa [zeroFunc, hcov, hpow] using herr
  have hdistQ : (distU (m := 2) proj₀ zeroFunc : ℚ) = 2 := by
    exact_mod_cast hdist
  have herrRat : errU (n := 2) proj₀ [] = (2 : ℚ) / 4 := by
    simpa [hdistQ] using hrewrite
  have hdiv : (2 : ℚ) / 4 = (1 : ℚ) / 2 := by norm_num
  simpa [herrRat, hdiv]

/-- Список `[(x₀ = 1)]` действительно входит в словарь `sampleDict`. -/
lemma fixTrue_subset_sampleDict :
    Core.listSubset [fixBit (m := 2) 0 true] sampleDict := by
  classical
  intro β hβ
  have hβ' : β = fixBit (m := 2) 0 true := by
    simpa [sampleDict] using hβ
  subst hβ'
  simp [sampleDict]

/-- Аппроксимация `proj₀` одним подкубом лежит в классе `ApproxClass`. -/
lemma proj₀_in_approx_sample :
    proj₀ ∈ ApproxClass (R := sampleDict) (k := 1) (ε := 0) := by
  classical
  refine approx_mem_of_errU_le (R := sampleDict) (k := 1) (ε := 0)
    (f := proj₀) ?_
  refine ⟨[fixBit (m := 2) 0 true], ?_, ?_, ?_⟩
  · simp
  · exact fixTrue_subset_sampleDict
  · have herr := err_proj₀_fixTrue
    have : errU (n := 2) proj₀ [fixBit (m := 2) 0 true] ≤ 0 := by
      simpa [herr]
    simpa using this

/-- Из принадлежности `ApproxClass` можно извлечь явный набор подкубов. -/
lemma proj₀_err_witness :
    ∃ S : List (Subcube 2),
      S.length ≤ 1 ∧ listSubset S sampleDict ∧
        errU (n := 2) proj₀ S ≤ (0 : ℚ) := by
  classical
  exact errU_exists_of_mem_approx
    (R := sampleDict) (k := 1) (ε := (0 : ℚ))
    (f := proj₀) proj₀_in_approx_sample

/-- Всякая функция из `UnionClass` автоматически входит в `ApproxClass` при ε = 0. -/
lemma union_subset_approx_zero_sample :
    UnionClass sampleDict 1 ⊆ ApproxClass (R := sampleDict) (k := 1) (ε := 0) := by
  classical
  simpa using union_subset_approx_zero (R := sampleDict) (k := 1)

/-- При `ε = 0` классы аппроксимаций и объединений совпадают на игрушечном примере. -/
lemma approx_zero_eq_union_sample :
    ApproxClass (R := sampleDict) (k := 1) (ε := 0) = UnionClass sampleDict 1 := by
  classical
  simpa using approx_zero_eq_union (R := sampleDict) (k := 1)

end Tests
end Pnp3
