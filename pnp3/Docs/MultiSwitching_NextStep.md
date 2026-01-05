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

## Зафиксированное текущее состояние (на сегодня)

Ниже фиксируем фактическое состояние, чтобы не было разночтений:

1. **Stage‑1/Stage‑2 (encoding/injection + counting → ∃ good restriction)**
   теперь **закрыты как для детерминированного `BadFamily`, так и для
   `BadEvent` канонического CCDT**. Это соответствует классической
   формулировке: плохое событие задаётся каноническим (детерминированным)
   процессом построения трассы/DT.

2. **CCDT/BadEvent‑слой снова подключён.**
   Есть явная обёртка `canonicalCCDTAlgorithmCNF` и encoding/injection
   для `BadEvent`, поэтому downstream‑шаги могут использовать стандартный
   интерфейс `BadEvent (A := canonicalCCDTAlgorithm …)` без костылей.

Итог: **можно двигаться к Part 3 без дополнительных мостов**.

## Минимальный план восстановления CCDT‑моста (архив, уже выполнено)

Ниже оставляем прежний план как историческую справку:

1. Ввести канонический CCDT‑алгоритм как функцию.
2. Доказать мост: `BadEvent` ↔ `BadFamily_deterministic`.
3. Поднять encoding/injection на уровень `BadEvent`.
4. Поднять counting на уровень `BadEvent`.

Все 4 пункта реализованы, поэтому дальнейшие задачи должны ориентироваться
на Part 3 (индукция по глубине).

## Что делаем прямо сейчас (старт выполнения)

1. **Фиксируем аудитный файл** (Done в этом PR):
   * `pnp3/Audit/Axioms.lean` — единая точка, где видно список текущих аксиом.

2. **Step‑2 (Done в этом PR):**
   * В `pnp3/AC0/MultiSwitching/Encoding.lean` подключён реальный encoding для
     канонического DT и доказана `Function.Injective` без axiom/sorry
     (см. `encodeBadEvent_canonicalCCDT` и `encodingWitness_canonicalCCDT_CNF`).
   * В `pnp3/AC0/MultiSwitching/Counting.lean` получена оценка
     `|Bad ∩ R_s| ≤ |R_{s-t}| * B^t` для канонического CCDT
     (см. `badRestrictions_card_le_canonicalCCDT_aux`) и добавлен прямой
     existence‑шаг `∃ ρ ∈ R_s, ¬ BadEvent` из Aux‑границы
     (см. `exists_good_restriction_canonicalCCDT_of_bound_aux`).
   * В `pnp3/AC0/MultiSwitching/ShrinkageFromGood.lean` уже есть конструкция
     `PartialCertificate` из `Good ρ`
     (см. `partialCertificate_from_good_restriction` и обёртку
     `shrinkage_from_good_restriction`).

## Definition of Done (для текущего старта)

* `pnp3/Audit/Axioms.lean` собирается и выводит именно ожидаемые аксиомы,
  которые мы хотим устранить.

## Definition of Done (для блока multi-switching depth-2)

* **Encode/Decode:** есть `encode` и доказательство `Function.Injective`.
* **Counting:** доказано `|Bad ∩ R_s| ≤ |R_{s-t}| * B^t` и `|Bad| < |R_s|`.
* **Shrinkage:** `Good ρ` порождает `PartialCertificate` без аксиом.
* **Axiom removal:** `#print axioms ThirdPartyFacts.partial_shrinkage_for_AC0`
  больше не содержит `ac0PolylogBoundWitness_of_multi_switching`.
