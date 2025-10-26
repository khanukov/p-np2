# Facts/LocalityLift

This directory hosts the stand-alone package that will eventually replace the
axiomatic treatment of the locality-lift lemma (axiom D.5) inside the `pnp3`
project.  The goal is to provide a reusable, well-documented Lean component that
exports the minimal interface required by the magnification pipeline:

* the data structures describing *general* and *local* GapMCSP solvers;
* the polylogarithmic budget helper used throughout Step C;
* the locality-lift theorem, stated with the exact parameter dependencies used
  downstream in `LB_GeneralFromLocal`, `PipelineStatements`, and
  `Bridge_to_Magnification`;
* a wrapper lemma that immediately turns any hypothetical local solver into a
  contradiction when combined with Step C lower bounds.

На текущем этапе пакет предоставляет полный интерфейс и **консервативную
конструктивную реализацию** теоремы: мы строим явный свидетель локальности
с одноточечным тест-набором, удовлетворяющим полилогарифмической границе, что
позволяет устранить явную аксиому из кода.  Это решение служит «заглушкой» до
момента, когда будет формализован шринкаж-факт A.2 (`shrinkage_for_localCircuit`).
Вся инфраструктура для полноценного доказательства уже подготовлена — сразу
после появления результата шага A можно будет заменить базовый свидетель на
доказанный через локализацию и мультиплексоры вариант, не изменяя интерфейсов.

> **Статус на момент публикации.** Работа над доказательством locality lift
> приостановлена до завершения формализации A.2.  Все необходимые точки
> интеграции отмечены в коде и документации: возобновить проект можно будет
> с немедленного подключения шринкаж-свидетеля без дополнительной подготовки.

## Roadmap

1. **Mirror the existing interface.**  The definitions currently living in
   `pnp3/Magnification/LocalityLift.lean` are re-created here (with additional
   commentary) so that other projects can depend on them without pulling the
   entire `pnp3` repository.  The `Exports` module exposes these declarations
   through a compact namespace.
2. **Document all numerical constraints.**  The `ProofSketch` folder records the
   intended proof structure, cross-references to Williams (2014) and
   Murray–Williams (2018), and lists the quantitative inequalities that must be
   discharged when the axiom is replaced by a proof.
3. **Gradually replace the axiom.**  Follow-up work will import the multi-
   switching and shrinkage facts (once they are available as packages of their
   own) and implement the constructive extraction of the local solver, in the
   style of Theorem 5.1 from Williams’ JACM 2014 paper.

## Repository layout

```
Facts/LocalityLift/
├── Interface/
│   ├── Parameters.lean    -- shared numeric parameters for GapMCSP solvers
│   └── Statement.lean     -- the locality-lift interface (использует свидетель)
├── ProofSketch/
│   └── Outline.lean       -- heavily commented blueprint for the proof
├── Proof/
│   ├── Arithmetic.lean    -- базовые числовые леммы про polylogBudget
│   ├── TestSet.lean       -- канонический малый тест-набор и его свойства
│   ├── TestSetExtraction.lean -- преобразование множества «живых» координат в тест-набор
│   ├── Summary.lean       -- сводка shrinkage-параметров и переход к чертежу
│   ├── Localization.lean  -- семантическое условие «зависимости только от alive»,
│   │                         явные операции restrict/extend и локальный эмулятор
│   ├── Restriction.lean   -- формализация рестрикций (частичных назначений)
│   ├── Builder.lean       -- линейный бюджет мультиплексоров и `LocalCircuitSkeleton`
│   │                         (мост от локализационных сертификатов к свидетелям)
│   ├── Blueprint.lean     -- преобразование числовых чертежей в свидетелей
│   └── Witness.lean       -- упаковка shrinkage-сертификатов в итоговый свидетель
├── Exports.lean           -- convenient re-exports for downstream projects
├── FactLocalityLift.lean  -- package entry point (imports `Exports`)
├── lakefile.lean
├── manifest.json
└── README.md              -- this file
```

Each Lean file is saturated with comments so that future contributors can see
exactly where new lemmas must be inserted, which classical results are
referenced, and how the parameters are expected to transform.

## Next steps towards verification

* **(Blocked until Step A completes.)** Formalise the shrinkage and
  multi-switching lemmas relied upon by Williams and Murray–Williams, ideally in
  separate `Facts/Switching` and `Facts/Shrinkage` packages.  This delivers the
  external fact A.2 (`shrinkage_for_localCircuit`) required by the builder.
* Implement the deterministic extraction of the test-set `T` and the local
  solver `loc`, keeping the explicit bounds `hT`, `hM`, `hℓ`, and `hdepth`.  The
  helper modules are already scaffolded; once A.2 is available, the remaining
  proofs can be inserted where indicated by the comments.
* Integrate automated sanity checks (small toy instances, arithmetic lemmas on
  `polylogBudget`, …) to validate the interface before wiring the fact back into
  the main proof pipeline.

## Assumptions and prerequisites (to be discharged later)

*This package is intended to be fully verified. Until the proof is in place,
we record the exact external statements the proof will rely on:*

1. **Shrinkage for local circuits (multi-switching for locality).**  
   A Håstad/Williams-style shrinkage lemma specialised to local circuits, as
   currently exposed in `ThirdPartyFacts/Facts_Switching.lean` under the name
   `shrinkage_for_localCircuit`. Intuitively, it asserts that after suitable
   restrictions the dependency set compresses to a polylogarithmic subset of
   coordinates, with controlled PDT depth and small error.

2. **(No SAL/AC⁰ shrinkage dependency for this lemma.)**  
   The locality-lift proof can be carried out *only* with the local shrinkage
   fact; the AC⁰ multi-switching is not required here. Likewise, Step C
   (anti-checker) is orthogonal to this lemma.

These assumptions will be either (i) imported from a verified package once
available, or (ii) phrased as explicit hypotheses in intermediate draft proofs.

## Parameter policy (fixed constants)

We fix the polylog budget used downstream:
```lean
def polylogBudget (N : Nat) : Nat :=
  (Nat.log2 (N + 1) + 1) ^ 4
```
and keep the exact locality-lift bounds as used by `LB_GeneralFromLocal`:
```
|T| ≤ polylogBudget(N),
M_loc ≤ M_gen * (|T| + 1),
ℓ_loc ≤ polylogBudget(N),
depth_loc ≤ depth_gen.
```
This matches Williams (2014)/Murray–Williams (2018) up to constant factors and
is stable with the existing Step C/Step D code. If a different exponent is ever
required, a monotonicity lemma can be added without changing the public API.

## Test-set invariants (minimal)

For the locality-lift, the test-set `T` only needs:
* type `Finset (BitVec n)` and the cardinality bound above;
* the *semantic* role: the constructed local solver depends only on the
  coordinates indexed by `T` (this is exactly what “locality ℓ = |T|” means).

No closure properties of `T` are required here; anti-checker-specific
requirements (e.g. distinguishing families) belong to Step C and are unrelated
to this lemma.

## API stability contract

The following names and signatures are considered stable:
* `GeneralCircuitParameters`, `SmallGeneralCircuitSolver`,
  `LocalCircuitParameters`, `SmallLocalCircuitSolver`,
  `LocalityWitness`;
* `polylogBudget` as defined above;
* `locality_lift` with the four inequalities on `T`, `M`, `ℓ`, `depth`;
* the wrapper lemma turning “no local solver” into “no general solver”.

Future extensions (e.g. a parametric `polylogBudget_k`) must not break this API.

## Outstanding work checklist

The table below captures the remaining engineering tasks that block the removal
of axiom D.5.  Each entry points to the exact Lean modules that will host the
corresponding proof artefacts so that contributors can jump straight to the
relevant file.

| Status | Task | Target module(s) |
| --- | --- | --- |
| ☑ | Formalise the shrinkage witness interface (`ShrinkageWitness`) specialised to GapMCSP solvers and connect it to the blueprint layer.<br/>The module now also provides `ShrinkageCertificate`, a canonical certificate, and the bridge to semantic localisation certificates. | `Proof/Summary.lean`, `Proof/Blueprint.lean`, `Proof/ShrinkageWitness.lean`, `Proof/Witness.lean` |
| ☑ | Extract the deterministic test-set `T` from a shrinkage certificate and capture the localisation predicate `localizedOn alive general`.<br/>The helper modules now provide canonical test-set constructions for any restriction, glue them to shrinkage summaries, and expose a `localityWitnessOfCertificate` bridge that carries semantic data without unfolding definitions. | `Proof/TestSetExtraction.lean`, `Proof/Restriction.lean`, `Proof/Localization.lean`, `Proof/ShrinkageWitness.lean`, `Proof/Witness.lean` |
| ◕ | Build the local solver by threading iterative ITE/multiplexer layers through the general solver DAG, keeping the size and depth bounds explicit (linear size budget prepared in `Proof/Builder.lean`).<br/>`LocalCircuitSkeleton` now packages shrinkage summaries together with the local evaluator, supplying immediate bridges to `LocalityCertificate` and `LocalityWitness`.  **Финальный шаг заблокирован до тех пор, пока не будет формализована A.2 (`shrinkage_for_localCircuit`)**: после появления доказанного shrinkage-свидетельства его нужно подставить вместо канонической заглушки и реализовать мультиплексорную трансформацию. | `ProofSketch/Outline.lean`, `Proof/Builder.lean` |
| ☑ | Replace the axiom `localityWitness` with an explicit construction (baseline witness with a canonical one-point test-set), factoring the conversion through the blueprint helper. | `Proof/TestSet.lean`, `Proof/Blueprint.lean`, `Proof/Witness.lean`, `Interface/Statement.lean` |

Once all four items are checked, Step D in the main repository will depend only
on the verified shrinkage machinery from Step A.

## Research questions for subject-matter experts

To proceed with the proof, we need authoritative answers to the following
domain-specific questions.  Each question cites the precise Lean identifiers and
mathematical statements it will influence so that researchers can respond
without consulting the repository.

1. **Turning shrinkage witnesses into deterministic test-sets.**
   *Context.* The external fact `ThirdPartyFacts.Facts_Switching.shrinkage_for_localCircuit`
   promises a `ShrinkageWitness` whose `alive` coordinates collapse dependence to
   a set of at most `ℓ := ⌊log₂ (general.params.size + 2)⌋` variables and whose
   partial decision tree has depth `t = O((log general.params.size)^depth)` with
   failure probability ≤ `1 / (inputLen p + 2)`.
   *Question.* What is the canonical construction of the finite test-set
   `T : Finset (BitVec (inputLen p))` that certifies localisation?  Specifically:
   * How do we select a single witness `alive` set deterministically from the
     probabilistic shrinkage statement?
   * Which leaves/paths of the partial decision tree must be retained to ensure
     `T.card ≤ polylogBudget (inputLen p)` (degree 4 in the current definition)?
   * Which literature reference should be cited for this extraction step
     (e.g. Williams 2014, Theorem 5.1; Beame’s switching lemma primer)?

2. **Size accounting for the local solver.**
   *Context.* The interface requires `loc.params.M ≤ general.params.size * (T.card.succ)`
   once the general solver is specialised along the test-set `T`.  The intended
   construction shares subcircuits via iterated if-then-else (multiplexer) gates
   rather than expanding all `2^{|T|}` branches.
   *Question.* Which precise combinatorial bound from the literature justifies
   the linear overhead `(|T| + 1)`?  Please outline how the size of the DAG is
   preserved when each control bit from `T` is threaded through the solver.  A
   citation to a standard source (e.g. Wegener’s *The Complexity of Boolean
   Functions*) would let us mirror the argument in Lean.

3. **Depth preservation versus additive overhead.**
   *Context.* The current signature states `loc.params.depth ≤ general.params.depth`.
   Some expositions of locality lifting allow an additive `O(1)` blow-up while
   others quote a multiplicative `ℓ` factor.
   *Question.* Which inequality should we formalise to stay faithful to the
   Williams (2014) / Murray–Williams (2018) pipeline?  Is there a concise
   argument (or reference) showing that the multiplexer layers can be absorbed
   without increasing depth, or should the interface be relaxed to
   `loc.params.depth ≤ general.params.depth + c` for a small constant `c`?

4. **Input-length invariant sanity check.**
   *Context.* Both `SmallGeneralCircuitSolver` and `SmallLocalCircuitSolver`
   store an equality `params.n = inputLen p`, where `inputLen p = 2 ^ p.n` is the
   length of the truth-table input rather than the number of MCSP variables.
   *Question.* Can we confirm that every downstream consumer—particularly
   `pnp3/LowerBounds/AntiChecker.lean` and the SAL bridge—expects solvers to be
   indexed by truth-table length?  If some components prefer the raw variable
   count `p.n`, we should adjust the interface now before investing in the
   locality proof.

Clear answers to these four questions will unblock the remaining work items
listed above and allow the axiom to be replaced with a fully verified proof.
