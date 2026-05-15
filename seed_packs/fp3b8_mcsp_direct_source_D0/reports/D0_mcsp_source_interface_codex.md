# fp3b8-D0 — Direct MCSP source-interface feasibility audit

Handle: `codex`

## 1. Executive verdict

**INCONCLUSIVE**

I do **not** recommend opening a full fp3b8 Round 1 yet.  The repository already
has a clean pnp4 interface for a direct search-MCSP weak lower bound, and that
interface is much closer to the mainline source obligation than any FP3b
provenance-filter route.  However, the missing step is exactly the hard
magnification contract: turning the selected weak search lower bound into a
`VerifiedNPDAGLowerBoundSource` without hiding `PpolyDAG` hardness.  I cannot
honestly classify this as GREEN-light until that bridge has a concrete,
non-circular plan.  I also do not classify it as RED-light because the candidate
below is a real existing interface target and is not just another provenance
filter.

## 2. Repository interface map

### `SearchMCSPWeakLowerBound`

- **File path:** `pnp4/Pnp4/Frontier/CompressionMagnification.lean`.
- **Current type/signature:**

  ```lean
  structure SearchMCSPWeakLowerBound where
    weakLowerBound : Prop
    weakLowerBoundProof : weakLowerBound
    magnifiesToVerifiedDAGSource :
      weakLowerBound → VerifiedNPDAGLowerBoundSource
  ```

- **What it needs as input:** a proved weak lower-bound proposition and a
  magnification map from that proposition to `VerifiedNPDAGLowerBoundSource`.
- **Status:** active pnp4 mainline interface, but it is a package surface rather
  than an already proved lower bound.  The repository README explicitly says a
  `SearchMCSPWeakLowerBound` must supply a verified `NP` language lower bound
  against `PpolyDAG`, not merely a restricted-model result.

### Concrete search-MCSP target layer

- **File path:** `pnp4/Pnp4/Frontier/SearchMCSPMagnification.lean`.
- **Current type/signature:**

  ```lean
  structure SearchMCSPCompressionProblem where
    instanceBits : Nat → Nat
    witnessBits : Nat → Nat
    promise : ∀ n, BitVec (instanceBits n) → Prop
    relation : ∀ n, BitVec (instanceBits n) → BitVec (witnessBits n) → Prop
    totalOnPromise : ∀ n x, promise n x → ∃ w, relation n x w
  ```

  ```lean
  structure SearchMCSPWeakCircuitLowerBoundTarget where
    problem : SearchMCSPCompressionProblem
    circuitClass : CircuitFamilyClass
    sizeBound : Nat → Nat
  ```

  ```lean
  def SearchMCSPWeakCircuitLowerBoundTarget.noBoundedSolver
      (target : SearchMCSPWeakCircuitLowerBoundTarget) : Prop :=
    SearchProblemNoBoundedSolver target.problem target.circuitClass target.sizeBound
  ```

  ```lean
  structure SearchMCSPWeakCircuitLowerBound (target) where
    noBoundedSolver : target.noBoundedSolver
  ```

  ```lean
  structure SearchMCSPMagnificationContract (target) where
    magnifiesToVerifiedDAGSource :
      target.noBoundedSolver → VerifiedNPDAGLowerBoundSource
  ```

- **What it needs as input:** a concrete search/compression problem, an explicit
  circuit-family class for search solvers, a size schedule, a proof that no such
  bounded solver exists, and a separate magnification contract.
- **Status:** active pnp4 mainline target interface.  It deliberately separates
  the weak lower-bound proof from the magnification contract.

### Concrete tree-MCSP search source layer

- **File path:** `pnp4/Pnp4/Frontier/SearchMCSPConcreteTargets.lean`.
- **Current type/signature:**

  ```lean
  def treeMCSPSearchProblem
      (threshold : Nat → Nat)
      (encoding : TreeMCSPSearchWitnessEncoding threshold) :
      SearchMCSPCompressionProblem
  ```

  ```lean
  def treeMCSPSearchWeakLowerBoundTarget
      (threshold : Nat → Nat)
      (encoding : TreeMCSPSearchWitnessEncoding threshold)
      (C : CircuitFamilyClass)
      (sizeBound : Nat → Nat) :
      SearchMCSPWeakCircuitLowerBoundTarget
  ```

  ```lean
  structure TreeMCSPSearchMagnificationSource where
    threshold : Nat → Nat
    encoding : TreeMCSPSearchWitnessEncoding threshold
    circuitClass : CircuitFamilyClass
    sizeBound : Nat → Nat
    weakLowerBound :
      SearchMCSPWeakCircuitLowerBound
        (treeMCSPSearchWeakLowerBoundTarget threshold encoding circuitClass sizeBound)
    magnification :
      SearchMCSPMagnificationContract
        (treeMCSPSearchWeakLowerBoundTarget threshold encoding circuitClass sizeBound)
  ```

- **What it needs as input:** a threshold schedule, a witness encoding for small
  tree circuits, a circuit class and size schedule for the search solver, a weak
  search lower bound, and the magnification contract.
- **Status:** active pnp4 concrete mainline candidate surface.  It is not a final
  theorem because the weak lower bound and magnification are still inputs.

### `VerifiedNPDAGLowerBoundSource`

- **File path:** `pnp4/Pnp4/AlgorithmsToLowerBounds/BridgeToPpolyDAG.lean`.
- **Current type/signature:**

  ```lean
  structure VerifiedNPDAGLowerBoundSource where
    L : DagLanguage
    inNP : Pnp3.ComplexityInterfaces.NP L
    notInPpolyDAG : ¬ Pnp3.ComplexityInterfaces.PpolyDAG L
  ```

- **What it needs as input:** an explicit language, a proof it is in `NP`, and a
  proof it is not in `PpolyDAG`.
- **Status:** active pnp4 mainline bridge object.  It is the honest endpoint
  source package upstream of `NP_not_subset_PpolyDAG`.

### `NP_not_subset_PpolyDAG`

- **File path:** `pnp3/Complexity/Interfaces.lean`.
- **Current type/signature:**

  ```lean
  def NP_not_subset_PpolyDAG : Prop := ∃ L, NP L ∧ ¬ PpolyDAG L
  ```

- **What it needs as input:** an `NP` language and a lower bound excluding all
  polynomial-size DAG families for that language.
- **Status:** active trust-root target, not a placeholder and not refuted.
  The pnp4 bridge theorem
  `NP_not_subset_PpolyDAG_of_verified_source` converts a
  `VerifiedNPDAGLowerBoundSource` into this target.

### `ResearchGapWitness`

- **File path:** `pnp3/Magnification/UnconditionalResearchGap.lean`.
- **Current type/signature:**

  ```lean
  def ResearchGapTarget : Prop := ComplexityInterfaces.NP_not_subset_PpolyDAG

  structure ResearchGapWitness : Type where
    dagSeparation : ResearchGapTarget
  ```

- **What it needs as input:** an honest proof of `NP_not_subset_PpolyDAG`.
- **Status:** active method-neutral final port.  It is intentionally uninhabited
  by any closed proof in the current repository.  Docs emphasize that green CI
  and route wrappers do not count as progress unless they prove a non-vacuous
  source theorem for this boundary.

### Bridges between the objects

- **`VerifiedNPDAGLowerBoundSource → NP_not_subset_PpolyDAG`:**
  `NP_not_subset_PpolyDAG_of_verified_source` in
  `pnp4/Pnp4/AlgorithmsToLowerBounds/BridgeToPpolyDAG.lean`.
- **`SearchMCSPWeakLowerBound → VerifiedNPDAGLowerBoundSource`:**
  `SearchMCSPWeakLowerBound.verifiedSource` in
  `pnp4/Pnp4/Frontier/CompressionMagnification.lean`, using the package's
  `magnifiesToVerifiedDAGSource` field.
- **Concrete weak target to generic source package:**
  `SearchMCSPWeakLowerBound.of_weakCircuitLowerBound` in
  `pnp4/Pnp4/Frontier/SearchMCSPMagnification.lean`.
- **Concrete tree-MCSP source to verified DAG source:**
  `TreeMCSPSearchMagnificationSource.verifiedSource` in
  `pnp4/Pnp4/Frontier/SearchMCSPConcreteTargets.lean`.
- **`NP_not_subset_PpolyDAG → ResearchGapWitness.dagSeparation`:** there is no
  separate constructor bridge in pnp4; a future pnp3 proof would package the
  separation as the `dagSeparation` field of `ResearchGapWitness`.

## 3. Candidate direct MCSP source statement

I propose exactly one candidate statement:

> **CandidateStatement:** For a fixed, explicit tree-circuit witness encoding
> and a nontrivial threshold schedule `threshold`, there is no non-uniform
> polynomial-size bounded search solver that, on every promised truth table with
> a tree circuit of size at most `threshold n`, outputs a valid encoded small
> tree circuit witness.  Formally, this should instantiate
> `SearchMCSPWeakCircuitLowerBound` for
> `treeMCSPSearchWeakLowerBoundTarget threshold encoding C sizeBound`, with `C`
> chosen as an explicit non-uniform Boolean/DAG-style search-output circuit class
> and `sizeBound` polynomial.

This statement is closer to `SearchMCSPWeakLowerBound` and
`VerifiedNPDAGLowerBoundSource` than FP3b because it targets the existing pnp4
search-MCSP lower-bound interface directly.  It is not a witness-quality filter,
not a syntactic acceptance predicate on formula witnesses, and not a route that
tries to certify acceptable provenance before asking for a source theorem.

The candidate intentionally avoids assuming a hidden `PpolyDAG` separation.
Its explicit content is a weak search lower bound for producing MCSP witnesses
on promised easy tables.  The still-missing part is not smuggled into the
statement; it remains a separate `SearchMCSPMagnificationContract` obligation.

## 4. Non-circularity audit

The candidate is **not immediately circular** at the statement level:

- It does not state `NP_not_subset_PpolyDAG`.
- It does not state `P != NP`.
- It does not say that an `NP` language has no polynomial-size DAG family.
- It does not say that a target language is not computable by `PpolyDAG`.
- It does not directly quantify over all small DAG witnesses for an arbitrary
  `NP` language.

However, the candidate becomes circular if the required magnification contract
is proved by simply choosing a language already assumed not to be in
`PpolyDAG`, or by embedding the nonexistence of polynomial DAGs into the
promise, witness relation, circuit class, or threshold schedule.  The current
repository interface avoids that by making the magnification contract a visible
separate field, but D0 does not yet supply a non-circular proof of that field.

Result: **non-circular as a weak target; unresolved at the full chain.**  This is
why the verdict is INCONCLUSIVE rather than GREEN-light.

## 5. Natural Proofs audit

### Constructivity

The search problem itself is constructive in the weak sense: an output witness
can be checked against a truth table by decoding a circuit and verifying
agreement, as captured by `TreeMCSPSearchWitnessEncoding` and
`TreeCircuitWitnessCodec`.  Constructivity is not automatically fatal because
the candidate is a search lower bound, not a direct property used to accept many
hard truth tables.

### Largeness

The dangerous largeness question is whether the weak lower bound can be
rephrased as an efficiently decidable property that accepts a large fraction of
truth tables while excluding all easy functions.  On the present formulation,
the promise is over easy tables with small witnesses, so the statement is not
obviously a large property of all Boolean functions.  But if the eventual proof
uses a broad MCSP threshold property over random truth tables, the Razborov--
Rudich largeness risk returns.

### Usefulness

Usefulness is exactly the desired endpoint of the magnification contract: a
successful chain must produce a lower bound against `PpolyDAG`.  Thus the weak
statement avoids direct usefulness, while the bridge must eventually create it.
That is acceptable only if the bridge uses a genuinely non-natural ingredient.

### Does it become a large constructive useful property?

Not at the weak-target surface.  It may become natural-proof-shaped in the
magnification proof unless that proof identifies a structural escape, such as a
search-to-decision or compression-theoretic obstruction that is not a large
extensional property of truth tables.  No such escape is formalized or clearly
specified yet.

Result: **partially addressed; the weak statement is not itself an obvious
natural proof, but the missing bridge is natural-proofs-sensitive.**

## 6. NOGO-000006/7/8/9 audit

### `NOGO-000006` — arbitrary all-essential log-width `ttFormula` payload

Status: **not applicable** to the candidate as stated.

Reason: the candidate is not a support-cardinality predicate over formula
witnesses and does not accept/reject witnesses based on a logarithmic support
window.  The arbitrary all-essential log-width payload obstruction was a
hardwiring attack against FP3 support-diversity/provenance filtering, not
against the pnp4 search-MCSP weak-lower-bound interface.

Caveat: if a later Round 1 tries to prove the weak lower bound by selecting
accepted sublinear-support witness families, NOGO-000006 becomes applicable
again.

### `NOGO-000007` — support-cardinality-only meta-barrier

Status: **addressed at the statement level**.

Reason: the candidate statement is about absence of bounded search solvers for a
promise-search relation.  It does not classify witnesses by support cardinality
and does not accept a hardwiring twin because it has the same support profile.

Caveat: a proof strategy based on support-only acceptance of search outputs
would fail this audit.

### `NOGO-000008` — tautological rewrite attack

Status: **addressed at the statement level**.

Reason: the candidate is extensional with respect to the validity of a decoded
MCSP witness for a truth table.  It is not a displayed-gate-shape filter where
conjoining a redundant tautology can turn a bad witness into an accepted one.

Caveat: the concrete circuit encoding still matters.  A later proof must ensure
that padding/rewrite variants of a witness do not create a false search lower
bound or a vacuous relation.

### `NOGO-000009` — normalize-then-filter self-defeat

Status: **not applicable** to the candidate as stated.

Reason: the candidate does not patch a displayed-syntax filter by composing it
with a structural normalizer.  There is no filter non-vacuity witness to destroy
by normalizing away a tautological seed.

Caveat: if Round 1 reintroduces a normalizer as a way to define accepted search
witnesses, this NoGo must be rerun.

## 7. Relativization / algebrization audit

The candidate does **not** yet identify a non-relativizing or non-algebrizing
component.

The repository's barrier files define only abstract bypass interfaces:
`RelativizationBypassWitness` and `AlgebrizationBypassWitness` require explicit
oracle/algebraic-oracle pairs where the statement holds in one world and fails
in another.  The candidate above provides no such witness.  A pure
search-MCSP-to-`PpolyDAG` magnification proof could easily be vulnerable to
standard relativization/algebrization objections unless it uses a component that
is visibly non-relativizing or non-algebrizing.

Result: **not addressed**.  This is another reason not to GREEN-light a full
Round 1 yet.

## 8. Path to `VerifiedNPDAGLowerBoundSource`

The possible interface chain is syntactically clear but mathematically
incomplete:

```text
CandidateStatement
  = SearchMCSPWeakCircuitLowerBound
      (treeMCSPSearchWeakLowerBoundTarget threshold encoding C sizeBound)

CandidateStatement
  + SearchMCSPMagnificationContract
      (treeMCSPSearchWeakLowerBoundTarget threshold encoding C sizeBound)
  → SearchMCSPWeakLowerBound
      via SearchMCSPWeakLowerBound.of_weakCircuitLowerBound

SearchMCSPWeakLowerBound
  → VerifiedNPDAGLowerBoundSource
      via SearchMCSPWeakLowerBound.verifiedSource

VerifiedNPDAGLowerBoundSource
  → NP_not_subset_PpolyDAG
      via NP_not_subset_PpolyDAG_of_verified_source

NP_not_subset_PpolyDAG
  → ResearchGapWitness.dagSeparation
      by packaging the separation as the field of ResearchGapWitness
```

The fatal missing evidence is the concrete `SearchMCSPMagnificationContract`.
Without it, the candidate only proves a weak search lower bound.  The current
repository already warns that restricted MCSP/AC0/formula/local-PRG milestones
are side tracks unless paired with an explicit bridge to `PpolyDAG` or
`VerifiedNPDAGLowerBoundSource`.

So the honest D0 conclusion is:

```text
CandidateStatement
  → SearchMCSPWeakCircuitLowerBound
  ↛ VerifiedNPDAGLowerBoundSource   (missing non-circular magnification contract)
```

## 9. First self-attacks

A responsible next review would have to run at least these attacks before any
full Round 1 seed pack is opened:

1. **Hidden `PpolyDAG` hardness assumption:** check every promise, threshold,
   circuit class, advice object, and witness relation for an embedded lower
   bound against polynomial DAGs.
2. **Natural-proof largeness:** determine whether the proof turns into a large,
   constructive, useful property of Boolean functions.
3. **Search-to-decision collapse:** test whether a bounded search solver can be
   obtained from a decision MCSP oracle or from self-reducibility in the selected
   promise regime, which would make the claimed weak lower bound false or too
   strong.
4. **Relativization:** produce or rule out oracle worlds where the weak search
   statement holds but no `PpolyDAG` separation follows.
5. **Algebrization:** same as above for algebraic-oracle changes.
6. **Vacuity / promise emptiness:** prove the easy-table promise is nonempty and
   not artificially sparse in a way that makes the search lower bound cheap or
   irrelevant.
7. **Encoding dependence:** verify that changing the tree-circuit witness codec
   does not create an artificial lower bound about decoding rather than MCSP.
8. **Known refuted predicates:** ensure the proof does not import refuted
   support-bounds, singleton-provider, multiswitching-data, or FP3 provenance
   surfaces.
9. **Insufficient bridge attack:** ask whether the weak search lower bound is
   merely an interesting meta-complexity statement with no route to
   `VerifiedNPDAGLowerBoundSource`.
10. **Truth-table hardwiring attack:** even though NOGO-000006 is not directly
    applicable, test whether small hardwired tables or lookup-style solvers can
    satisfy the promise relation under the selected size schedule.

## 10. Recommended next action

**run_second_D0_review**

Minimum missing evidence before full Round 1:

1. A concrete non-circular candidate for
   `SearchMCSPMagnificationContract
     (treeMCSPSearchWeakLowerBoundTarget threshold encoding C sizeBound)`.
2. A barrier note identifying which part of that contract is non-relativizing or
   non-algebrizing, or an honest explanation why the route can survive without
   such a component.
3. A natural-proofs escape argument that does not rely on representation
   sensitivity or provenance filtering.
4. A codec/threshold sanity check showing the weak lower bound is about MCSP
   witness search and not about an artificially hard encoding.

If the second D0 review cannot supply those, the operator should choose
`RED_light_fp3b8` or `return_to_broader_research_gap_search` rather than opening
another FP3b-style cycle.
