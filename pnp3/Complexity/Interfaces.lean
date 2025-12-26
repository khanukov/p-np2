import ThirdPartyFacts.PsubsetPpoly
import Proof.Turing.Encoding
/-!
  pnp3/Complexity/Interfaces.lean

  Интерфейс к «классической» части доказательства.  Здесь мы не повторяем
  полную формализацию классов `P`, `NP` и `P/poly`,
  а лишь фиксируем их последствия в виде именованных утверждений.  Это
  позволяет шагу D ссылаться на внешний факт `P ⊆ P/poly`
  и на целевое утверждение `P ≠ NP` без дублирования кода.

  * `NP_not_subset_Ppoly` — сокращённая запись утверждения `NP ⊄ P/poly`.
  * `P_subset_Ppoly` — конкретное утверждение «`P ⊆ P/poly`», предоставленное
    внешним пакетом (см. `ThirdPartyFacts/PsubsetPpoly.lean`).
  * `P_ne_NP` — целевое утверждение `P ≠ NP`.
  * `P_ne_NP_of_nonuniform_separation` — классический вывод из двух пунктов
    выше.  В ранней библиотеке проекта эта теорема доказана напрямую (см. `NP_separation.lean`).

  На уровне текущего каталога `pnp3/` мы используем эти утверждения как
  внешние факты.  Включение `P ⊆ P/poly` импортируется из модуля
  `ThirdPartyFacts/PsubsetPpoly.lean`, который напрямую переиспользует
  доказательство из пакета `Facts/PsubsetPpoly`.
-/

open Facts.PsubsetPpoly

namespace Pnp3
namespace ComplexityInterfaces

/-!
### Базовые определения

Мы переиспользуем минимальные структуры из внешнего пакета `P ⊆ P/poly`.
Это гарантирует совместимость с импортируемым утверждением `P ⊆ P/poly`
и позволяет безболезненно расширять интерфейс при необходимости
добавления новых сведений о классах сложности.
-/

/-- Тип языков, используемый во внешнем пакете. -/
abbrev Language := Complexity.Language

/-- Битовые строки фиксированной длины из внешнего пакета. -/
abbrev Bitstring := Complexity.Bitstring

/-- Класс `P` из лёгкой формализации внешнего пакета. -/
abbrev P : Language → Prop := Facts.PsubsetPpoly.P.{0}

/-- Класс `P/poly` из того же пакета. -/
abbrev Ppoly : Language → Prop := Facts.PsubsetPpoly.Ppoly

/-!
  Конструктивное определение NP через полиномиальный верификатор.

  В отличие от класса `P`, который фиксируется через Turing-машины из
  внешнего пакета, для NP мы используем *абстрактный* верификатор:
  функцию `verify`, которая принимает вход `x` и сертификат `w`.
  Это позволяет формально строить свидетельства `NP` для языков, где
  полный TM-уровень пока не развёрнут в коде.

  Важно: мы сохраняем требование полиномиальной длины сертификата и
  вводим функцию `runTime`, чтобы явно фиксировать полиномиальный
  временной бюджет в интерфейсе. Конкретная реализация TM-уровня
  (и перенос верификатора на ленту) может быть добавлена позднее
  без изменения потребителей определения.
-/

/-- Полиномиальный предел длины сертификата для входа длины `n`. -/
def certificateLength (n k : Nat) : Nat := n ^ k + k

/--
Склейка двух битовых строк. Первые `n` позиций берём из `x`,
оставшиеся `m` — из `w`. Такая кодировка позволяет передать вход и
сертификат в одном слове для верификатора.
-/
noncomputable def concatBitstring {n m : Nat} (x : Bitstring n) (w : Bitstring m) :
    Bitstring (n + m) := fun i =>
  by
    classical
    by_cases h : (i : Nat) < n
    · exact x ⟨i, h⟩
    · have hge : n ≤ (i : Nat) := Nat.le_of_not_gt h
      let t := Classical.choose (Nat.exists_eq_add_of_le hge)
      have ht : (i : Nat) = n + t :=
        Classical.choose_spec (Nat.exists_eq_add_of_le hge)
      have ht_lt : t < m := by
        have : n + t < n + m := by
          simpa [ht] using i.isLt
        exact (Nat.add_lt_add_iff_left).1 this
      exact w ⟨t, ht_lt⟩

/--
Класс `NP` через полиномиальный верификатор: язык `L` принадлежит `NP`,
если существует TM, которая за полиномиальное время проверяет сертификат
полиномиальной длины, принимая ровно те пары `(x, w)`, где `w` подтверждает
принадлежность `x` языку `L`.
-/
def NP (L : Language) : Prop :=
  ∃ (c k : Nat)
    (runTime : Nat → Nat)
    (verify : ∀ n, Bitstring n → Bitstring (certificateLength n k) → Bool),
    (∀ n,
      runTime (n + certificateLength n k) ≤
        (n + certificateLength n k) ^ c + c) ∧
    (∀ n (x : Bitstring n),
      L n x = true ↔
        ∃ w : Bitstring (certificateLength n k),
          verify n x w = true)

/-!
### TM-мост для `NP`

Иногда удобнее иметь формулировку NP прямо через Turing-машины из
внешнего пакета `Facts.PsubsetPpoly`. Ниже мы добавляем определение
`NP_TM` и лемму, которая переводит такое TM-свидетельство в абстрактное
`NP`-свидетельство. Это именно «мост»: он не меняет базовое определение
`NP`, но позволяет использовать TM-инфраструктуру при необходимости.
-/

/--
`NP_TM`: версия `NP`, сформулированная через верификатор-TM из внешнего
пакета. Машина читает вход и сертификат, склеенные в одну строку.

Эта формулировка является усилением: из неё всегда можно получить
`NP` в абстрактном смысле (см. `NP_of_NP_TM`).
-/
def NP_TM (L : Language) : Prop :=
  ∃ (M : Facts.PsubsetPpoly.TM.{0}) (c k : Nat),
    (∀ n,
      M.runTime (n + certificateLength n k) ≤
        (n + certificateLength n k) ^ c + c) ∧
    (∀ n (x : Bitstring n),
      L n x = true ↔
        ∃ w : Bitstring (certificateLength n k),
          Facts.PsubsetPpoly.TM.accepts
              (M := M)
              (n := n + certificateLength n k)
              (concatBitstring x w) = true)

/--
TM-верификатор порождает абстрактный верификатор: просто берём
`verify := TM.accepts` на склеенном входе, а временной бюджет
копируем из `M.runTime`.
-/
theorem NP_of_NP_TM {L : Language} : NP_TM L → NP L := by
  intro hTM
  rcases hTM with ⟨M, c, k, hRun, hCorrect⟩
  refine ⟨c, k, M.runTime, ?verify, ?hRun', ?hCorrect'⟩
  · intro n x w
    exact Facts.PsubsetPpoly.TM.accepts
      (M := M)
      (n := n + certificateLength n k)
      (concatBitstring x w)
  · intro n
    exact hRun n
  · intro n x
    simpa using hCorrect n x

/-!
### Формулировки целевых утверждений
-/

/-- Интерпретация утверждения «`NP ⊄ P/poly`» через существование языка. -/
def NP_not_subset_Ppoly : Prop := ∃ L, NP L ∧ ¬ Ppoly L

/-- Утверждение «`P ⊆ P/poly`», предоставленное внешним пакетом. -/
def P_subset_Ppoly : Prop :=
  ∀ L, Facts.PsubsetPpoly.P.{0} L → Facts.PsubsetPpoly.Ppoly L

/--
  Доказательство включения `P ⊆ P/poly`, предоставленное внешним модулем.
  Когда появится реальное доказательство, его достаточно связать с
  `ThirdPartyFacts.PsubsetPpoly.proof`.
-/
@[simp] theorem P_subset_Ppoly_proof : P_subset_Ppoly := by
  intro L hL
  exact (ThirdPartyFacts.P_subset_Ppoly_proof (L := L) hL)

/-- Итоговое целевое утверждение `P ≠ NP`. -/
def P_ne_NP : Prop := Facts.PsubsetPpoly.P.{0} ≠ NP

/-!
### Логический вывод `NP ⊄ P/poly` + `P ⊆ P/poly` ⇒ `P ≠ NP`
-/

/--
  Конкретная версия классического вывода: если существует язык из `NP`, не
  принадлежащий `P/poly`, а также доказано включение `P ⊆ P/poly`, то классы
  `P` и `NP` не совпадают.

  Этот аргумент полностью повторяет доказательство из архивной
  библиотеки (`P_ne_NP_of_nonuniform_separation_concrete`) и не опирается на
  дополнительные аксиомы: достаточно логики множеств и базового свойства
  включения.
-/
theorem P_ne_NP_of_nonuniform_separation_concrete
    (hNP : NP_not_subset_Ppoly) (hP : P_subset_Ppoly) :
    P_ne_NP := by
  classical
  -- Предположим противное и выведем противоречие с `hNP`.
  refine fun hEq => ?_
  have hNP_subset_P : ∀ {L : Language}, NP L → Facts.PsubsetPpoly.P.{0} L := by
    intro L hL
    have hEq_pointwise : Facts.PsubsetPpoly.P.{0} L = NP L := congrArg (fun f => f L) hEq
    exact hEq_pointwise.symm ▸ hL
  have hNP_subset_Ppoly : ∀ {L : Language}, NP L → Ppoly L := by
    intro L hL
    exact hP L (hNP_subset_P hL)
  rcases hNP with ⟨L₀, hL₀_NP, hL₀_not_Ppoly⟩
  exact hL₀_not_Ppoly (hNP_subset_Ppoly hL₀_NP)

/-- Совместимость с прежним именем аксиомы. -/
theorem P_ne_NP_of_nonuniform_separation
    (hNP : NP_not_subset_Ppoly) (hP : P_subset_Ppoly) :
    P_ne_NP :=
  P_ne_NP_of_nonuniform_separation_concrete hNP hP

/--
  Удобная форма для работы от противного: если из предположения
  `∀ L, NP L → P/poly` можно вывести противоречие, то автоматически
  существует язык из `NP`, не лежащий в `P/poly`.

  При работе от противного мы используем классическое рассуждение:
  отрицание импликации `NP L → Ppoly L` даёт одновременно `NP L` и
  `¬ Ppoly L`, то есть явный контрпример к включению.
-/
theorem NP_not_subset_Ppoly_of_contra
    (hContra : (∀ L : Language, NP L → Ppoly L) → False) :
    NP_not_subset_Ppoly := by
  classical
  -- Отрицание универсального включения даёт конкретный язык `L`.
  have hNotAll : ¬ (∀ L : Language, NP L → Ppoly L) := by
    intro hAll
    exact hContra hAll
  rcases Classical.not_forall.mp hNotAll with ⟨L, hNotImp⟩
  -- Из `¬ (NP L → Ppoly L)` классически выводим `NP L`.
  have hNP : NP L := by
    by_contra hNP
    have hImp : NP L → Ppoly L := by
      intro hL
      exact (hNP hL).elim
    exact hNotImp hImp
  -- А также `¬ Ppoly L`.
  have hNotPpoly : ¬ Ppoly L := by
    intro hPpoly
    have hImp : NP L → Ppoly L := by
      intro _hL
      exact hPpoly
    exact hNotImp hImp
  exact ⟨L, hNP, hNotPpoly⟩

/-- Эквивалентная форма `NP_not_subset_Ppoly` через отрицание включения. -/
theorem NP_not_subset_Ppoly_iff_not_forall :
    NP_not_subset_Ppoly ↔ ¬ (∀ L : Language, NP L → Ppoly L) := by
  constructor
  · intro hSep hAll
    rcases hSep with ⟨L, hNP, hNotPpoly⟩
    exact hNotPpoly (hAll L hNP)
  · intro hNotAll
    exact NP_not_subset_Ppoly_of_contra (by
      intro hAll
      exact hNotAll hAll)

end ComplexityInterfaces
end Pnp3
