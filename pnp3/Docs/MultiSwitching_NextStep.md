# Next step: закрыть multi-switching depth-2 и убрать аксиому polylog-bound

Этот документ фиксирует **следующий оптимальный шаг** и минимальный, но
проверяемый старт выполнения. Цель: сделать переход `M² → polylog`
математически честным, заменив аксиому
`ac0PolylogBoundWitness_of_multi_switching` реальным proof-by-encoding для
`depth-2` (CNF/DNF), и затем использовать его как базу индукции по глубине.

## Почему это лучший следующий шаг

* Это **центральный узел**, блокирующий переход на polylog в финальном пайплайне.
* Это **локальная задача**, решаемая в `pnp3/AC0/MultiSwitching/*`.
* Это **самая проверяемая часть**: честное multi-switching сразу улучшает
  внешний вид всей цепочки, не требуя правки downstream.

## Что делаем прямо сейчас (старт выполнения)

1. **Фиксируем аудитный файл** (Done в этом PR):
   * `pnp3/Audit/Axioms.lean` — единая точка, где видно список текущих аксиом.

2. **Далее (следующий кодовый шаг):**
   * В `pnp3/AC0/MultiSwitching/Encoding.lean` подключить реальный encoding для
     канонического DT и показать `Function.Injective` без axiom/sorry.
   * В `pnp3/AC0/MultiSwitching/Counting.lean` получить
     `|Bad ∩ R_s| ≤ |R_{s-t}| * B^t` и затем `|Bad| < |R_s|` для выбранных
     параметров.
   * В `pnp3/AC0/MultiSwitching/ShrinkageFromGood.lean` получить
     `PartialCertificate` из `Good ρ`.

## Definition of Done (для текущего старта)

* `pnp3/Audit/Axioms.lean` собирается и выводит именно ожидаемые аксиомы,
  которые мы хотим устранить.

## Definition of Done (для блока multi-switching depth-2)

* **Encode/Decode:** есть `encode` и доказательство `Function.Injective`.
* **Counting:** доказано `|Bad ∩ R_s| ≤ |R_{s-t}| * B^t` и `|Bad| < |R_s|`.
* **Shrinkage:** `Good ρ` порождает `PartialCertificate` без аксиом.
* **Axiom removal:** `#print axioms ThirdPartyFacts.partial_shrinkage_for_AC0`
  больше не содержит `ac0PolylogBoundWitness_of_multi_switching`.
