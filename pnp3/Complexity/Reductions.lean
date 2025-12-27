import Complexity.Interfaces

/-!
  pnp3/Complexity/Reductions.lean

  Минимальный интерфейс сведений (reductions) и NP-трудности.

  В проекте мы не разворачиваем полную теорию полиномиальных сведений.
  Вместо этого фиксируем базовую «логическую» форму many-one сведений:
  существование функции, переводящей экземпляры одной задачи в другую,
  сохраняющей принадлежность.

  Такой интерфейс полезен, когда мы хотим *честно* зафиксировать внешнюю
  гипотезу NP-трудности (например, для GapMCSP) без формализации всех
  деталей построения редукции.
-/

namespace Pnp3
namespace Complexity

open ComplexityInterfaces

/--
  Many-one сведение (Karp reduction) между предикатами на произвольных
  типах. Требуется функция `f`, сохраняющая истинность предиката.

  Мы намеренно не фиксируем полиномиальную ограниченность: в рамках
  формального моста это чистая логическая редукция, пригодная для
  аксиоматизации внешних результатов.
-/
def ManyOneReducible {α β : Type} (L_A : α → Prop) (L_B : β → Prop) : Prop :=
  ∃ f : α → β, ∀ x, L_A x ↔ L_B (f x)

/-- Пара (n, x) для языка длины `n`. -/
abbrev LanguageInstance := Σ n : Nat, Bitstring n

/-- Предикат принадлежности экземпляра языку `L`. -/
def LanguageHolds (L : Language) (x : LanguageInstance) : Prop :=
  L x.1 x.2 = true

/-- Many-one сведение между языками в терминах `LanguageInstance`. -/
def ManyOneReducibleLanguage (L_A L_B : Language) : Prop :=
  ManyOneReducible (LanguageHolds L_A) (LanguageHolds L_B)

/--
  NP-трудность языка `L`: каждый язык из `NP` сводится к `L`.

  Это определение также намеренно «чисто логическое»: мы не моделируем
  вычислимость редукции. В рамках проекта это корректная точка для
  аксиоматизации внешних результатов (например, из литературы по
  hardness magnification).
-/
def Is_NP_Hard (L : Language) : Prop :=
  ∀ L' : Language, NP L' → ManyOneReducibleLanguage L' L

end Complexity
end Pnp3
