# Proof Roadmap for `pnp3`

This document records the complete roadmap for the `pnp3` project, structured
around the four major proof stages A → B → C → D.  Each subsection lists the
current status, dependencies, difficulty estimates, and definition-of-done
criteria.  The goal is to replace every standing axiom by a fully formalized
Lean proof while keeping the existing high-level architecture intact.

## 0. Global picture

### 0.1 Idea

1. **SAL (Switching-Atlas Lemma).**  From a shrinkage certificate (a shallow
   PDT approximating an entire function family) we synthesize a bounded atlas
   whose dictionary of subcubes approximates every member with error ≤ ε and a
   uniform leaf budget `k`.
2. **Covering-Power.**  Using combinatorial counting (binomial bounds and
   Hamming-ball estimates) we upper-bound the number of functions that any such
   atlas can approximate.  This provides a capacity barrier.
3. **Anti-checker.**  Assuming a small GapMCSP solver, we construct a rich
   subfamily `Y` with cardinality strictly exceeding the capacity barrier,
   contradicting Covering-Power and ruling out the solver.
4. **Magnification.**  The established lower bound for GapMCSP triggers hardness
   magnification theorems (OPS/JACM), giving `NP ⊄ P/poly`.  Together with the
   trivial `P ⊆ P/poly` we conclude `P ≠ NP`.

### 0.2 Dependency DAG

```
Shrinkage facts ──► SAL_from_Shrinkage ──► BoundedAtlasScenario
                 │
Leaf budget ◄────┘                                        │
                                                         ▼
Counting bounds (binomial + Hamming) ──► Covering-Power  │
                                                         ▼
Anti-checker existence ──► LB cores (AC⁰ / local) ──► False
                                                         │
Magnification triggers (OPS/JACM) ────────────────────────┘
                                                         ▼
P ⊆ P/poly + NP ⊄ P/poly ──► Final theorem `P ≠ NP`
```

### 0.3 Ultimate target

Replace every axiom in this pipeline with constructive Lean proofs so that the
final theorem `P_ne_NP_final` holds unconditionally.

## 1. Stage A — SAL and shrinkage

### 1.1 Core SAL machinery (status: **done**, difficulty 2/10)

* **Files:** `Core/SAL_Core.lean`, `Core/Atlas.lean`, `ThirdPartyFacts/Facts_Switching.lean`.
* **Scope:** definitions of shrinkage certificates, atlases, and the conversion
  `SAL_from_Shrinkage`.  Current smoke tests (`Tests/LB_Smoke_Scenario.lean`)
  verify the pipeline.
* **Recent progress:** `Core/BooleanBasics.subcube_card_pow` теперь доказана
  конструктивно: мощности подкубов вычисляются через количество свободных
  координат, а не постулируются аксиоматически.
* **DoD:** `SAL_from_Shrinkage` produces a valid atlas for any shrinkage input;
  regression tests remain green.

### 1.2 Leaf budget uniformization (status: **done (dedup/leaf bound)**, difficulty 3/10)

* **File:** `ThirdPartyFacts/LeafBudget.lean` (`leaf_budget_from_shrinkage`).
* **Goal:** derive a global leaf bound `k` for all functions in the family from
  the shrinkage data (ultimately aiming for the textbook `O(t · log(1/ε))`).
  The current Lean proof removes duplicate leaves from every selector, proves
  that the cleaned lists inject into the PDT leaf set, and instantiates `k` with
  the explicit dictionary size `|leaves(tree)|` (hence ≤ `2^t`).
* **DoD:** constructive `k` together with regression tests confirming the SAL →
  counting pipeline operates on the deduplicated lists.  Remaining work focuses
  on sharpening the quantitative bound via multi-switching analytics.

### 1.3 Shrinkage for AC⁰/local circuits (status: **axiom**, difficulty 8/10)

* **File:** `ThirdPartyFacts/Facts_Switching.lean` (`partial_shrinkage_for_AC0`,
  `shrinkage_for_AC0`, and the local analogue).
* **Goal:** formalize the multi-switching lemma to obtain shallow PDTs with
  controlled error.  Early milestones can target depth-2 formulas before moving
  to the full `d`-layer setting.
* **Current status:** the Lean interface packages the axiom
  `partial_shrinkage_for_AC0` into the structured witness
  `MultiSwitchingWitness`, so downstream code no longer refers to a standalone
  `hastad_multiSwitching` assumption.  A constructive fallback exists for the
  canonical point enumeration, but the general combinatorial proof is still
  outstanding.
* **DoD:** fully proved shrinkage lemmas matching the current interface
  (parameter bounds on depth `t` and error `ε`).

## 2. Stage B — Covering-Power and counting

### 2.1 Union/approximation classes (status: **done**, difficulty 2/10)

* **File:** `Counting/Atlas_to_LB_Core.lean`.
* **Scope:** definitions of union classes, approximation classes, distance
  metrics, and the incompatibility lemma bridging SAL scenarios with capacity
  bounds.  The incompatibility result is now fully constructive (`incompatibility`),
  so any finite `Y` of ε-approximable functions automatically satisfies the
  capacity bound.
* **DoD:** definitions remain stable; tests around scenario incompatibility
  continue to pass.

### 2.2 Capacity bounds (status: **done**, difficulty 3/10)

* **File:** `Counting/BinomialBounds.lean`.
* **Scope:** все биномиальные и хамминговые оценки доказаны конструктивно, к ним
  добавлены леммы монотонности (`unionBound_mono_left/right`,
  `hammingBallBound_mono`).  Эти результаты напрямую кормят теорему
  `covering_power_bound`, так что во всём шаге B больше не осталось аксиом или
  незакрытых заготовок.
* **DoD:** `capacityBound` выражена через явные функции от `D`, `k`, `N` и ε,
  все вспомогательные оценки доказаны, sanity-тесты (например,
  `Tests/Atlas_Count_Sanity.lean`) подтверждают корректность на малых
  примерах.  Дополнительных задач на шаге B не запланировано; дальнейшие
  улучшения (при желании) могут рассматриваться как отдельные исследования,
  не входящие в основной план.

## 3. Stage C — GapMCSP lower bounds

### 3.1 Model primitives (status: **done**, difficulty 2/10)

* **File:** `Models/Model_GapMCSP.lean` defines `GapMCSPParams` and basic
  derived data.
* **DoD:** type-level parameters remain consistent across the pipeline.

### 3.2 Anti-checker construction (status: **axiom**, difficulty 9/10)

* **File:** `LowerBounds/AntiChecker.lean`.
* **Goal:** construct the `F` and `Y` witnesses from any small solver, formalize
  solver correctness predicates, and apply counting bounds to yield a
  contradiction.
* **DoD:** Lean proofs of `antiChecker_exists_large_Y` and its local-circuit
  variant; `LB_Formulas_core` and `LB_LocalCircuits_core` compile without
  axioms.

### 3.3 LB cores (status: **done modulo axioms**, difficulty 2/10)

* **Files:** `LowerBounds/LB_Formulas_Core.lean`,
  `LowerBounds/LB_LocalCircuits.lean`.
* **DoD:** once the anti-checker and counting lemmas are proved, these cores
  should close without further modification.

## 4. Stage D — Magnification bridge and final separation

### 4.1 Magnification triggers (status: **axiom**, difficulty 6/10)

* **File:** `Magnification/Facts_Magnification.lean`.
* **Goal:** formalize the OPS'20 and JACM'22 hardness magnification theorems so
  that GapMCSP lower bounds imply `NP ⊄ P/poly`.  At minimum, document precise
  parameter requirements; ideally, provide full proofs.
* **DoD:** the triggers accept the outputs of Stage C and yield
  `NP_not_subset_Ppoly` without axioms.

### 4.2 Bridge and final theorem (status: **done**, difficulty 2/10)

* **Files:** `Magnification/Bridge_to_Magnification.lean`,
  `Magnification/FinalResult.lean`, `Complexity/Interfaces.lean`.
* **DoD:** remains consistent once earlier stages are de-axiomatized; tests in
  `Tests/Magnification_Core_Contradiction.lean` stay green.

## 5. Source map

* `Core/` — shrinkage, SAL, atlases.
* `ThirdPartyFacts/` — external shrinkage and leaf-budget facts.
* `Counting/` — combinatorial capacity bounds.
* `Models/` — GapMCSP parameters.
* `LowerBounds/` — anti-checker interfaces and core contradictions.
* `Magnification/` — hardness magnification triggers and the final bridge.
* `Complexity/` — interfaces for non-uniform complexity classes.
* `Tests/` — smoke tests and contradiction checks (always run `lake test`).

## 6. Risk tracking

* **Parity and FCE barriers:** SAL relies on shrinkage; parity lacks shrinkage,
  so the framework avoids trivial counterexamples.
* **Relativization/natural proofs/locality:** handled explicitly via shrinkage
  assumptions and dedicated locality triggers.
* **Hidden assumptions:** all external inputs are isolated as named axioms with
  references; `#print axioms` audits keep the dependency surface explicit.

## 7. Definition-of-done checklist

| Stage | Task | Difficulty | DoD snapshot |
|-------|------|------------|--------------|
| A | Prove shrinkage lemmas | 8/10 | `shrinkage_for_AC0`/`..._local` proven, tests green |
| A | Leaf budget bound | 3/10 | `leaf_budget_from_shrinkage` deduplicates selectors and bounds them by `|leaves(tree)|` |
| B | Binomial & Hamming bounds | 3/10 | `covering_power_bound` + monotonicity lemmas proved |
| C | Anti-checker | 9/10 | `antiChecker_exists_large_Y[_local]` proven |
| D | Magnification triggers | 6/10 | OPS/JACM triggers formalized |

Each completed DoD removes one major axiom, steadily converting the current
conditional proof into an unconditional Lean development.

## 8. Immediate action items

1. Прописать интерфейс корректности для `SmallAC0Solver` и начать формализацию
   античекера (включая явные описания слоёв YES/NO).
2. Усилить оценку leaf-budget через мульти-switching аналитику, чтобы добиться
   классического `O(t · log(1/ε))` вместо грубого `|leaves(tree)|`.
3. Постепенно деаксиоматизировать `shrinkage_for_AC0`/`..._local`, начиная с
   малых глубин и аккуратно отслеживая параметры.
4. Задокументировать требования к триггерам OPS/JACM и спланировать их
   формализацию (включая перевод параметров из шага C).

Regularly run `lake test` after each milestone and re-examine the assumptions
for potential counterexamples or parameter misalignments.

## 9. Остаточные задачи и связь с `pnp2`

### 9.1 Что ещё предстоит сделать в `pnp3`

* **Шаг A — shrinkage.**  Требуется заменить аксиомы `shrinkage_for_AC0` и
  `shrinkage_for_localCircuit` на доказательства многоступенчатой switching lemma.
  Ближайший подэтап — доказать версию для глубины 2 и зафиксировать все
  численные константы (глубина PDT, порог ошибки).
* **Шаг B — ёмкостные оценки.**  Комбинаторные границы полностью доказаны:
  `unionBound`, `hammingBallBound` и связанные с ними леммы монотонности
  обеспечивают окончательный вариант теоремы `covering_power_bound`.  Ранее
  использовавшаяся заглушка `count_small_circuits_bound` заменена на
  конструктивную границу `2^{2^n}`, поэтому никаких открытых пунктов на шаге B
  не осталось — его инфраструктура зафиксирована и готова к использованию в
  последующих этапах.
* **Шаг C — античекер.**  Основная работа впереди: формализовать корректность
  абстрактного решателя GapMCSP и построить свидетелей `F` и `Y`, превосходящих
  ёмкость SAL-сценария.  После закрытия этого шага ядро `LB_Formulas_core` и
  `LB_LocalCircuits_core` автоматически перестанут зависеть от аксиом.
* **Шаг D — триггеры магнификации.**  В `Magnification/Facts_Magnification.lean`
  пока остаются аксиомы, формализующие результаты OPS’20 и JACM’22.  Нужно
  уточнить их предпосылки, задокументировать перевод параметров и, по
  возможности, заменить интерфейсы на прямые доказательства.

Выполнение этих четырёх пунктов последовательно снимает последние оставшиеся
аксиомы и превращает `P_ne_NP_final` в безусловный результат.

### 9.2 Что переносить из `pnp2`

* **Уже используется.**  В `pnp3/Complexity/Interfaces.lean` мы напрямую опираемся
  на доказанный в `pnp2` факт `P ⊆ P/poly` (`PsubsetPpoly.lean`) и на классический
  вывод `P ≠ NP` из несравнимости `NP` и `P/poly` (`NP_separation.lean`).  Эти
  модули трогать не нужно: они служат готовым «чёрным ящиком» для шага D.
* **Что можно переиспользовать.**  Если для шага B понадобится более сильная
  энтропийная техника, стоит заглянуть в `Pnp2/family_entropy_cover.lean` и
  соседние файлы: там уже есть формализованные оценки мощности подсемейств и
  биномиальных сумм.  Переносить их целиком необязательно, но можно импортировать
  соответствующие леммы или переписать их в облегченном виде под SAL.
* **Что переносить не требуется.**  Старый FCE-конвейер (`Pnp2/Cover/`,
  `Pnp2/fce_lemma_proof.md`) не участвует в текущем проекте: SAL полностью
  заменяет FCE, и дублировать эти доказательства нет необходимости.  Аналогично,
  многочисленные конструкты для симуляции Тьюринговых машин уже интегрированы в
  `pnp2` и подцеплены через интерфейс, поэтому их миграция в `pnp3` не даёт
  дополнительной выгоды.

Итого, `pnp3` сейчас нуждается не в переносе старых фрагментов, а в
  последовательной деаксиоматизации собственных блоков.  `pnp2` остаётся
  «библиотекой справочных фактов», из которой мы берём только те результаты,
  которые уже полностью формализованы и не требуют адаптации.
