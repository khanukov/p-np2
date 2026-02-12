import Complexity.Interfaces

/-!
  pnp3/Complexity/Reductions.lean

  Интерфейсы сведений (reductions) и NP-трудности.

  Файл содержит **два слоя**:

  1. Legacy purely-logical layer (`ManyOneReducibleLanguage`, `Is_NP_Hard`) —
     используется для обратной совместимости и старых теорем.
  2. Complexity-aware layer (`PolyTime...`, `RandPolyTime...`) —
     новый слой с явным требованием полиномиального времени.
-/

namespace Pnp3
namespace Complexity

open ComplexityInterfaces

/-- Many-one сведение между предикатами на произвольных типах. -/
def ManyOneReducible {α β : Type} (L_A : α → Prop) (L_B : β → Prop) : Prop :=
  ∃ f : α → β, ∀ x, L_A x ↔ L_B (f x)

/-- Пара `(n, x)` для языка длины `n`. -/
abbrev LanguageInstance := Σ n : Nat, Bitstring n

/-- Предикат принадлежности экземпляра языку `L`. -/
def LanguageHolds (L : Language) (x : LanguageInstance) : Prop :=
  L x.1 x.2 = true

/-- Legacy many-one сведение между языками (без требований по времени). -/
def ManyOneReducibleLanguage (L_A L_B : Language) : Prop :=
  ManyOneReducible (LanguageHolds L_A) (LanguageHolds L_B)

/-- Legacy NP-hardness: все языки из `NP` логически сводятся к `L`. -/
def Is_NP_Hard (L : Language) : Prop :=
  ∀ L' : Language, NP L' → ManyOneReducibleLanguage L' L

/-!
## Complexity-aware interface (polytime / randomized polytime)

Мы не разворачиваем здесь полную TM-механику вычисления output-строки,
но уже отделяем корректный тип утверждений от purely-logical слоя.
-/

/-- Полиномиальная ограниченность функции времени. -/
def IsPolyTimeBound (timeBound : Nat → Nat) : Prop :=
  ∃ c d : Nat, ∀ n, timeBound n ≤ n ^ c + d

/--
  Детерминированная polytime many-one редукция между языками.
-/
structure PolyTimeManyOneReduction (L_A L_B : Language) : Type where
  map : LanguageInstance → LanguageInstance
  timeBound : Nat → Nat
  time_poly : IsPolyTimeBound timeBound
  preserves : ∀ x, LanguageHolds L_A x ↔ LanguageHolds L_B (map x)

/-- Сокращение: существует детерминированная polytime many-one редукция. -/
def PolyTimeManyOneReducibleLanguage (L_A L_B : Language) : Prop :=
  Nonempty (PolyTimeManyOneReduction L_A L_B)

/-- NP-hardness под детерминированными polytime many-one сведениями. -/
def Is_NP_Hard_poly (L : Language) : Prop :=
  ∀ L' : Language, NP L' → PolyTimeManyOneReducibleLanguage L' L

/--
  Randomized polytime many-one редукция.

  В текущей версии это абстрактный интерфейс (с тем же контрактом `preserves`),
  который нужен для корректной типизации внешних результатов Hirahara 2022.
-/
structure RandPolyTimeManyOneReduction (L_A L_B : Language) : Type where
  map : LanguageInstance → LanguageInstance
  timeBound : Nat → Nat
  time_poly : IsPolyTimeBound timeBound
  preserves : ∀ x, LanguageHolds L_A x ↔ LanguageHolds L_B (map x)

/-- Сокращение: существует randomized polytime many-one редукция. -/
def RandPolyTimeManyOneReducibleLanguage (L_A L_B : Language) : Prop :=
  Nonempty (RandPolyTimeManyOneReduction L_A L_B)

/-- NP-hardness под randomized polytime many-one сведениями. -/
def Is_NP_Hard_rpoly (L : Language) : Prop :=
  ∀ L' : Language, NP L' → RandPolyTimeManyOneReducibleLanguage L' L

end Complexity
end Pnp3
