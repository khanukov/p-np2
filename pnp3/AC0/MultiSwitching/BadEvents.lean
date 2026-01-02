import AC0.MultiSwitching.Definitions
import AC0.MultiSwitching.Trace

/-!
  pnp3/AC0/MultiSwitching/BadEvents.lean

  Удобные имена для «bad»/«good» событий и их базовые свойства.

  Этот файл специально отделён от `Definitions.lean`, чтобы избежать
  циклических импортов: `Trace.lean` использует определения семейств,
  а здесь мы переэкспортируем их как "официальные" имена для downstream-кода.
-/

namespace Pnp3
namespace AC0
namespace MultiSwitching

open Core

variable {n k : Nat}

/-!
### Каноническое bad‑событие для depth‑2 (CNF)

Чтобы downstream‑код мог использовать единые имена, мы здесь переэкспортируем
определения из `Trace.lean`. Это даёт «официальную» точку входа:

* `BadCNF` — наличие канонической трассы длины `t`;
* `BadFamilyCNF` — «существует формула в списке, которая bad»,
  с детерминированным выбором первой формулы через `Nat.find`;
* `badFamilyCNF_trace` — извлечение индекса и трассы длины `t`.

Эти определения полностью детерминированы и пригодны для будущего
encoding/injection без неоднозначности.
-/

abbrev BadFamilyCNF (F : FormulaFamily n k) (t : Nat) (ρ : Restriction n) : Prop :=
  MultiSwitching.BadFamily (F := F) t ρ

abbrev GoodFamilyCNF (F : FormulaFamily n k) (t : Nat) (ρ : Restriction n) : Prop :=
  MultiSwitching.GoodFamily (F := F) t ρ

lemma badFamilyCNF_trace
    {F : FormulaFamily n k} {t : Nat} {ρ : Restriction n}
    (hbad : BadFamilyCNF (F := F) t ρ) :
    ∃ j, ∃ hj : j < F.length,
      Nonempty (Trace (F := F.get ⟨j, hj⟩) t) := by
  exact MultiSwitching.badFamily_trace (F := F) (t := t) (ρ := ρ) hbad

lemma goodFamilyCNF_iff_not_bad
    {F : FormulaFamily n k} {t : Nat} {ρ : Restriction n} :
    GoodFamilyCNF (F := F) t ρ ↔ ¬ BadFamilyCNF (F := F) t ρ := by
  exact MultiSwitching.goodFamily_iff_not_badFamily (F := F) (t := t) (ρ := ρ)

end MultiSwitching
end AC0
end Pnp3
