# Plan for the canonical equality theorem

This document sketches a proof of the statement
`canonical c₁ = canonical c₂ ↔ ∀ x, eval c₁ x = eval c₂ x` for Boolean circuits.
The outline follows two main steps.

1. **Soundness.**  If two circuits have the same canonical form then they
   are extensionally equal.  This direction is already formalised in the
   lemma `canonical_inj` from `canonical_circuit.lean` and relies on the
   correctness theorem `eval_canonical`.
2. **Completeness.**  Conversely, if the evaluations coincide on every
   input then the canonical forms must agree.  The intended proof proceeds
   by induction on the structure of the canonical circuits, analysing all
   constructor cases and showing that unequal canonical forms always yield
   a distinguishing input.  The long Russian note from the discussion
   expands this argument in detail, covering variables, constants, unary
   and binary gates and the corresponding inductive step.

Combining these directions establishes the desired equivalence, denoted
here as `canonical_eq_iff_eqv`.  The proof is not yet fully formalised in
Lean but the outline provides a concrete roadmap for completing the
implementation without disrupting existing tests.

## Detailed inductive strategy (in Russian)

Доказательство разбивается на два направления.

1. **Звукость (`→`).**  Уже реализована в `canonical_inj`.  Если канонические формы
   совпадают, то схемы вычисляют одну и ту же функцию.  Это следует из
   корректности процедуры `canonical`.
2. **Полнота (`←`).**  Требуется показать обратное: если схемы эквивалентны как
   функции, то их канонические формы совпадают.  Удобнее доказать
   контрапозицию.  Пусть канонические формы различны.  Индукцией по структуре
   показано, что тогда можно подобрать вход, на котором результаты
   исходных схем различаются.  Ниже приводится подробный разбор всех
   случаев.

### База индукции

* `var i` против `var j`.  Если `i ≠ j`, выбираем вектор, где `x i = true`,
  а `x j = false`.  Тогда результаты отличаются.  Если `i = j`, схемы
  совпадают.
* `var i` против `const b`.  Подбираем `x` c противоположным значением на
  координате `i` и получаем различие.
* `var i` против `not d`.  Либо найдётся вход, где `d` выдаёт `x i`, либо
  во всех точках `d` равно `¬x i`.  В первом случае нужный вектор найден,
  во втором схемы эквивалентны, что противоречит различию канонических форм.
* `var` против бинарных узлов.  Меняя только одну координату можно добиться,
  чтобы `var` возвращала `true`, а `and` или `or` — `false` (или наоборот).

### Шаг индукции

* `not` против `not`.  При различии подузлов по предположению индукции
  существует вход, где значения расходятся.  После отрицания различие
  сохраняется.
* `and` против `and`.  Если отличаются левые части, подбираем вход, где
  они дают разные значения и правые части одновременно истинны.  Аналогично
  при различии правых частей.
* `or` против `or`.  Здесь наоборот добиваемся, чтобы отличающаяся ветвь
  давала разные значения при ложном результате другой ветви.

Во всех случаях получаем вход, различающий исходные схемы.  Следовательно,
из эквивалентности схем следует совпадение их канонических форм.
