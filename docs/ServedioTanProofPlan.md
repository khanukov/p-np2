# Servedio–Tan Multi-Switching Lemma: Formalisation Plan

> **Status (2025‑02)**  The repo still relies on the axiom
> `partial_shrinkage_for_AC0`.  Over the last iterations we implemented helper
> lemmas for literal/term restriction, a constructive constant-family witness,
> and smoke tests that cover the degenerate cases.  No genuine
> multi-switching argument is formalised yet.  This document explains what is
> still missing and, crucially, which precise mathematical inputs are required
> from the research team so that the constructive proof can be carried out.

The endgame is to constructively produce a `Core.PartialCertificate` for every
family of AC⁰-formulas whose parameters live in `AC0Parameters`.  The
certificate must satisfy the numerical guarantees built into the SAL pipeline:
`ℓ ≤ log₂(M + 2)`, `depthBound + ℓ ≤ (log₂(M + 2))^(d + 1)`, and
`ε ≤ 1/(n + 2)`.  The steps below are therefore organised around the missing
formal artefacts and the contextual information we still lack.

## 0. Snapshot of existing Lean components

* `Core/BooleanBasics.lean`, `Core/PDTPartial.lean` — provide subcubes, partial
  decision trees, shrinkage witnesses.
* `AC0/Formulas.lean` — syntax for literals/terms/clauses/formulas, evaluation
  and restriction primitives.  Recent commits supplied `restrict` helpers but
  no switching estimates.
* `ThirdPartyFacts/Facts_Switching.lean` — declares
  `partial_shrinkage_for_AC0`, `partial_shrinkage_for_AC0_of_constant`, and the
  planned interfaces to SAL.  Only the trivial/constant witnesses are proven.
* `Tests/SAL_Smoke_AC0.lean`, `Tests/Switching_Basics.lean` — check the trivial
  shrinkage instances.

Knowing exactly which of these files may be extended versus replaced would
already remove several degrees of freedom from the implementation choices.

## 1. Combinatorial infrastructure

* Extend the restriction API from `Core.BooleanBasics` so that AC⁰ literals,
  terms, and clauses interact smoothly with partial assignments.
* Formalise the “star guessing” process: given a DNF/CNF term, isolate the
  longest non-collapsed path and register the queried variables inside a
  partial decision tree.
* Prove a suite of helper lemmas that quantify how many variables the
  procedure consumes in expectation.  The statements should follow the shape of
  Håstad’s classical switching lemma because the multi-switching bound is
  eventually derived from repeated applications of the single-formula version.

## 2. Iterative certificate construction

* Encode the multi-switching process as a deterministic recursion that
  iteratively refines a `Core.PartialCertificate`.  Each iteration picks the
  “hardest” formula, applies the single-formula shrinkage lemma, and merges the
  resulting trunk with the running certificate.
* Track the quantitative parameters explicitly: after each iteration, update
  the current bound on the tail depth and accumulate the failure probability
  using the combinatorial estimates prepared in Step 1.
* Show that the recursion terminates within `log₂(M + 2)` iterations and that
  the error budget remains within `1 / (n + 2)`.

## 3. Packaging into the SAL interface

* Rephrase the final recursion lemma in terms of `Core.PartialCertificate`,
  extracting the fields required by `Core.PartialCertificate.toShrinkage`.
* Instantiate `AC0PartialWitness` with the constructed certificate and thread
  the inequalities through to `OraclePartialWitness.ofAC0`.
* Extend the existing smoke test `pnp3/Tests/SAL_Smoke_AC0.lean` so that it
  covers the new constructive witness and verifies the depth/error bounds on
  concrete toy formulas.

## 4. Follow-up tasks

* Mirror the same strategy for `shrinkage_for_localCircuit`.
* Replace the entropy stub `Hbin` with the genuine binary entropy function once
  the shrinkage proofs no longer rely on axioms.

## 5. Concrete information that would unblock the work

While the plan above sketches the overall roadmap, turning it into Lean code
requires several very specific design decisions that are still opaque from the
repository alone.  To avoid another round of guesswork, it would be extremely
useful to know the following details:

1. **Reference implementation of the single-formula switching lemma.**
   * Please point to any existing Lean source (private or public) that already
     proves a width‑k switching lemma.  If none exists, we need a confirmation
     that recreating the full proof in Lean 4 is the desired path.
   * Desired statement: an explicit function
     `switchingWitness : Formula n → (restrictionParameters → PartialDT …)`
     together with the precise constants used later in SAL.  Supplying the
     intended signature (types, namespaces, level of universes) would avoid
     painful refactors.
   * Clarify whether the single-formula lemma should be phrased for CNFs, DNFs,
     read-once formulas, or arbitrary `AC0.Formula`.  The proof strategy differs
     drastically depending on the chosen normal form.

2. **Specification of the random restriction model.**
   * We need the exact distribution in Lean terms: are restrictions sampled
     i.i.d. with `Pr[*] = p`, `Pr[0] = Pr[1] = (1-p)/2`, or does the proof rely
     on a biased split?  Should the randomness live in `Measure`/`Probability`
     from mathlib, or is a combinatorial counting measure preferred?
   * Should the constructive proof ultimately synthesise a deterministic trunk
     using the method of conditional expectations, or is it acceptable to apply
     Hilbert choice once the success probability is shown to be > 0?  The answer
     dictates whether we must develop a full derandomisation API.

3. **Exact structure of `AC0.Formulas`.**
   * The current type includes `⊥`, `⊤`, literals, `Not`, `And`, `Or`.  To keep
     the recursion manageable we need to know the normal form expected by the
     proof (e.g. alternating layers of `And`/`Or`, fan-in bounds, de Morgan
     normalisation).  If a preprocessing routine is assumed, please specify its
     contract so we can encode it as a lemma.
   * Are the width/size parameters (`params.M`, `params.d`) already measured in
     the same way as in the analytical proof, or do we need conversion lemmas
     between the Lean definitions and the literature conventions?

4. **Target failure probability expression.**
   * The axiom currently enforces `ε ≤ 1/(n + 2)` without mentioning the family
     size `|F|`.  The classical multi-switching lemma yields bounds of the form
     `|F|^{⌈t/ℓ⌉}·(Cp k)^t`.  We need the exact inequality the SAL stage expects
     so that our constants line up.  Please confirm the intended values of `p`,
     `ℓ`, and `t` as functions of `(n, M, d)`.
   * If there are precomputed numerical inequalities (e.g. bounding powers of
     `log₂ (M + 2)`), sharing them would prevent duplicating routine algebra in
     Lean.

5. **Testing harness expectations.**
   * Which canonical families should be included in the regression suite once
     the constructive proof exists?  Examples could be depth‑2 majority, small
     parity circuits, or randomly generated CNFs.  Providing 2–3 concrete test
     vectors would help us exercise the witness in the way the analysis team
     expects.
   * If there are numeric thresholds (e.g. acceptable depth bounds for
     `M = 32`, `d = 3`), please list them so that the tests can assert the exact
     inequalities.

6. **Interaction with downstream shrinkage.**
   * `OraclePartialWitness.ofAC0` currently assumes the existence of a witness
     with specific fields.  If the interface is expected to change (for example,
     to accommodate additional metadata about the restriction sequence), please
     describe the final shape.  We would rather adapt the certificate once than
     refactor multiple times.
   * Any expectations about computational complexity (should the certified tree
     be extracted algorithmically, or is a proof-of-existence enough?) need to
     be spelled out because they influence whether we build executable Lean
     programs or proof-only artefacts.

Providing even partial answers to the questions above will dramatically shorten
the time needed to eliminate the axiom: we can align notation, reuse existing
combinatorial estimates, and ensure that the final parameters match the rest of
the pipeline without multiple rewrites.  Until that information arrives, the
multi-switching lemma remains blocked on underspecified design choices rather
than on individual missing lemmas.

## 6. Clarifications from the research team (2025-02-XX)

The latest guidance removes the ambiguities called out above.  The following
items are now fixed targets for the formalisation:

1. **Single-formula switching lemma.**  No pre-existing Lean proof is available,
   so we must implement Håstad’s width-`k` lemma from scratch.  The witness
   should be phrased for *CNF formulas* (lists of clauses).  A future symmetric
   version for DNFs can be derived if needed, but the pipeline will consume the
   CNF variant.  Consequently, the development will focus on
   `AC0.CNF`/`AC0.Clause` and ignore the general `AC0.Formula` tree except for
   preprocessing.

2. **Random restriction model and constructivity.**  We adopt the classical
   i.i.d. distribution: each variable is left free with probability `p`, and is
   fixed to `0` or `1` with probability `(1 - p) / 2` each.  Proofs may reason
   combinatorially (counting the fraction of bad restrictions among the
   `3^n` possibilities); genuine measure theory is not required.  The overall
   argument only needs *existence* of a good restriction, so applying
   `Classical.choose` after establishing positive success probability is
   acceptable.  A derandomised/algorithmic trunk can be added later as a corollary.

3. **Formula structure.**  Input families will be supplied as CNFs whose clause
   width is bounded by the size parameter `params.M`.  When a general
   `AC0.Formula` appears, it is assumed to be preprocessed into an equivalent CNF
   without increasing depth beyond `params.d`; encoding this preprocessing as a
   lemma is part of the work.  Fan-in bounds and depth accounting therefore align
   with the existing definitions inside `AC0Parameters`.

4. **Quantitative bounds.**  The constructive lemma must instantiate the axiom
   with

   * trunk length `ℓ := ⌊log₂ (params.M + 2)⌋`,
   * tail depth bounded inductively so that `depthBound + ℓ ≤ (log₂ (params.M + 2))^(params.d + 1)`,
   * failure probability bounded by `|F|^{⌈t/ℓ⌉} · (C · p · k)^t ≤ 1 / (params.n + 2)`.

   The proof should pick `p := 1 / (4 · k)` (any constant multiple of `1/k`
   satisfying `C · p · k ≤ 1/2` works), run for `ℓ` iterations, and set `t := ℓ`
   so that the bound simplifies to `(C · p · k)^ℓ`.  Because `ℓ ≈ log₂ (M + 2)`
   and `|F|` is at most polynomial in `M`, this choice drives the error below
   `1/(n+2)` even in the worst case.  Auxiliary inequalities relating powers of
   `log₂` to `n`/`M` may be imported as lemmas when required.

5. **Regression targets.**  Once the witness is implemented, extend
   `Tests/SAL_Smoke_AC0.lean` (and, if useful, `Tests/Switching_Basics.lean`) to
   cover:

   * depth‑2 majority formulas (`Maj₃`, `Maj₅`),
   * a small parity circuit expressed as a depth‑3 AC⁰ formula,
   * random 3‑CNFs on 6–8 variables with `M ≈ 10` clauses,
   * a hand-crafted depth‑3 example with `M = 32`, `d = 3` verifying explicitly
     that `ℓ ≤ 5`, `depthBound + ℓ ≤ 6^4`, and `ε ≤ 1 / (n + 2)`.

   Tests should check the numerical inequalities exported by the certificate,
   not merely that the witness exists.

6. **SAL integration.**  The `OraclePartialWitness.ofAC0` interface remains
   unchanged.  We must provide a `Core.PartialCertificate` together with proofs
   of the inequalities above.  The witness may be non-computable (extracted via
   choice); no runtime guarantees or explicit derandomisation are required for
   the current milestone.

With these answers recorded, the remaining work is purely proof engineering:
formalise the single switching lemma on CNFs, lift it to the multi-switching
setting using the agreed parameters, and thread the resulting certificate
through `AC0PartialWitness` to discharge the axiom.

## 7. Blueprint for the width‑`k` switching lemma (added 2025‑02)

To keep the coding effort well-scoped, the constructive proof for a *single* CNF
of width `k` will be split into the following concrete lemmas/modules:

1. **Clause filtering utilities (`AC0/Formulas/Switching/ClauseTools`).**
   * Rephrase `Clause.restrict` as a composition of `List.filterMap`/`List.map`
     so that we can lean on the existing algebra of lists instead of analysing
     the hand-written recursion each time.
   * Introduce a predicate `Clause.isAliveUnder β` that records whether a clause
     still contains unresolved literals after the restriction `β`, and prove
     that the predicate depends only on the filtered literal list.

2. **Counting bad restrictions (`AC0/Formulas/Switching/Counting`).**
   * For a fixed clause of width `k`, count the number of restrictions that
     leave ≥ `t` literals unresolved; the classical bound `(C · p · k)^t` should
     arise as the ratio of “bad” restrictions among all `3^n` possibilities.
   * Lift the clause bound to entire CNFs by a union bound over all clauses in
     the list.  The output is an explicit inequality matching the constants
     fixed in §5.

3. **Decision-tree construction (`AC0/Formulas/Switching/Collapse`).**
   * Define a function `collapseCNF : CNF n → Nat → Core.PDT n` that queries
     variables along a fixed order until every surviving clause has ≤ `t`
     literals.  Prove structurally that whenever the counting lemma certifies
     “no clause longer than `t`”, the resulting tree has depth ≤ `t`.
   * Package the result as a lemma returning a `Core.PartialCertificate` for a
     singleton family, together with the `(C · p · k)^t` failure bound.

4. **Interface glue (`ThirdPartyFacts/HastadMSL`).**
   * Wrap the single-formula certificate so that it fits the
     `partial_shrinkage_for_AC0` API.  This mirrors the existing
     `partial_shrinkage_for_AC0_of_constant` construction, replacing the trivial
     trunk with the decision tree assembled in step 3.

Each bullet can be reviewed and merged independently.  Completing all four steps
delivers a constructive replacement for the axiom in the singleton case and
provides the building blocks needed for the multi-formula recursion of §2.

## 8. Дорожная карта кода после уточнений (2025‑04‑11)

Ниже собраны финальные требования к реализации, которые получены от
математиков и программистов проекта.  Выполнение каждого пункта необходимо,
чтобы довести шаг A (и соответствующие зависимости из шага B) до состояния
«без аксиом»:

1. **Целевая теорема.** Нужно оформить `cnfSwitching_badBound` (см. набросок
   сигнатуры ниже) и на её основе построить `multiSwitching_certificate`,
   заменяющий `partial_shrinkage_for_AC0`.

   ```lean
   theorem cnfSwitching_badBound
       (φ : AC0.CNF n) (hwidth : φ.width ≤ k)
       (p : ℚ) (t : ℕ) (C : ℚ := 5) :
       badRestrictions φ p t ≤ (C * p * k)^t

   def multiSwitching_certificate
       (params : AC0Parameters) (F : Family params.n) :
       Core.PartialCertificate params.n (Nat.log2 (params.M + 2)) F
   ```

   В `multiSwitching_certificate` собираются все расчёты по глубине и
   вероятности: на ствол длиной `ℓ := log₂ (M+2)` наклеиваются хвосты глубины
   `≤ ℓ`, а суммарная ошибка выводится из многократного применения
   `cnfSwitching_badBound`.

2. **Комбинаторика плохих ограничений.** Определить функции
   `starsCount : Restriction n → Nat` и `badForClause : AC0.Clause n → Set (Restriction n)`
   с доказательством формулы

   ```lean
   card (badForClause σ) ≤ Nat.choose σ.literals.length t * (2^(σ.literals.length - t))
   ```

   и последующим переписыванием через параметр `p`. Этот блок лучше держать в
   отдельном файле (например, `AC0/Formulas/Switching/Counting.lean`).

3. **Конструкция PDT.** Написать функцию `collapseCNF` с явным доказательством
   ограничения глубины: если после применения ограничения ни одна клауза не
   «жива» длиннее `t`, то дерево решений, построенное по фиксированному порядку
   переменных, имеет глубину ≤ `t`.  Важно подобрать порядок переменных, чтобы
   его можно было восстановить при свёртке нескольких шагов multi-switching.

4. **Индукция по семейству.** Превратить последовательное применение
   `cnfSwitching_badBound` к каждому `f ∈ F` в функцию, строящую общий
   частичный сертификат.  Здесь же нужно аккуратно вести оценку
   `|F|^{⌈t/ℓ⌉}` и доказать, что выбранные параметры дают итоговую ошибку
   `≤ 1/(n+2)`.

5. **Регрессии.** Подготовить `Tests/SAL_Smoke_AC0.lean` с проверками для:
   majority-of-5, случайной 3-CNF, глубины-3 формулы с `M = 32`, а также для
   комбинированного семейства `[f₀, f₁, majority]`. Тесты должны проверять
   не только существование сертификата, но и каждое из численных ограничений.

6. **Документация.** После завершения доказательства обновить текущий план,
   убрав разделы с открытыми вопросами и зафиксировав в changelog’е, что
   аксиома `partial_shrinkage_for_AC0` больше не используется.

Пункты перечислены в рекомендуемом порядке.  Каждый из них можно мерджить
по отдельности; главное — не забывать, что расчёт численных оценок должен
ссылаться ровно на те параметры (`p`, `ℓ`, `t`), которые описаны выше.
