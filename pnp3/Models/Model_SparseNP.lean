import Models.Model_GapMCSP

/-!
  pnp3/Models/Model_SparseNP.lean

  Минималистичная модель «разреженного» NP-языка.  Нам нужны лишь две
  числовые характеристики: длина входа `n` и верхняя граница на количество
  YES-инстансов.  Ограничение `yesBound` фиксируется как полилогарифмическая
  функция от `n`, что согласуется с предпосылками CJW'22.
-/

namespace Pnp3
namespace Models

/--
  Параметры разреженного NP-языка: `n` — длина входа, `yesCount` — верхняя
  оценка на число YES-инстансов длины `n`.  Мы требуем, чтобы `yesCount`
  не превосходил полилогарифмического бюджета от `n`.
-/
structure SparseLanguageParams where
  n : Nat
  yesCount : Nat
  yesBound : yesCount ≤ polylogBudget n
  deriving Repr

/-- Верхняя граница на количество YES-инстансов. -/
def yesBudget (p : SparseLanguageParams) : Nat := p.yesCount

/-- Полилогарифмический контроль плотности YES-инстансов. -/
lemma yesBudget_le_polylog (p : SparseLanguageParams) :
    yesBudget p ≤ polylogBudget p.n :=
  p.yesBound

end Models
end Pnp3
