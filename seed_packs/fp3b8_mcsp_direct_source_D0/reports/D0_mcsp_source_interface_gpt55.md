# fp3b8-D0 — direct MCSP source-interface feasibility audit

Handle: `gpt55`

## 1. Executive verdict

**RED-light.**

The best direct candidate I can state from the existing repository interface is
not a new mathematical source theorem.  It is essentially the already-existing
`TreeMCSPSearchMagnificationSource` package: a concrete tree-MCSP search weak
lower bound plus a `SearchMCSPMagnificationContract` that converts that weak
lower bound into `VerifiedNPDAGLowerBoundSource`.

That package is the correct interface target, but as a D0 research route it is
not enough: the decisive mathematical content is entirely in the magnification
contract.  If the contract is left abstract, the candidate is only a wrapper
around the missing `VerifiedNPDAGLowerBoundSource`; if it is expanded honestly,
D0 currently has no concrete non-natural, non-relativizing, non-algebrizing
argument that would produce an `NP` language lower bound against `PpolyDAG`.
Therefore a full fp3b8 Round 1 should **not** be opened from this candidate.

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

- **Inputs needed:** a concrete weak lower-bound proposition, a proof of that
  proposition, and a theorem-level magnification map from the proposition to
  `VerifiedNPDAGLowerBoundSource`.
- **Status:** active pnp4 mainline interface, but it is a package boundary rather
  than a proved theorem.  The package is intentionally strong enough to feed the
  final bridge only because it contains the magnification map.
- **Bridge role:** `SearchMCSPWeakLowerBound.verifiedSource` extracts
  `VerifiedNPDAGLowerBoundSource`; `NP_not_subset_Ppoly_of_searchMCSPWeakLowerBound`
  then derives the repository-local `NP_not_subset_Ppoly` abbreviation.

### Concrete search-MCSP target interfaces

- **File path:** `pnp4/Pnp4/Frontier/SearchMCSPMagnification.lean`.
- **Current type/signatures:**

  ```lean
  structure SearchMCSPCompressionProblem where
    instanceBits : Nat → Nat
    witnessBits : Nat → Nat
    promise : ∀ n, BitVec (instanceBits n) → Prop
    relation : ∀ n, BitVec (instanceBits n) → BitVec (witnessBits n) → Prop
    totalOnPromise : ∀ n x, promise n x → ∃ w, relation n x w

  structure BoundedSearchSolver (problem C sizeBound) where
    outputCircuit : ∀ n, Fin (problem.witnessBits n) → C.Family (problem.instanceBits n)
    size_le : ∀ n i, C.size (outputCircuit n i) ≤ sizeBound n
    solves : ∀ n x, problem.promise n x →
      problem.relation n x (searchSolverOutput (outputCircuit n) x)

  def SearchProblemNoBoundedSolver (problem C sizeBound) : Prop :=
    ¬ Nonempty (BoundedSearchSolver problem C sizeBound)

  structure SearchMCSPWeakCircuitLowerBoundTarget where
    problem : SearchMCSPCompressionProblem
    circuitClass : CircuitFamilyClass
    sizeBound : Nat → Nat

  structure SearchMCSPWeakCircuitLowerBound (target) where
    noBoundedSolver : target.noBoundedSolver

  structure SearchMCSPMagnificationContract (target) where
    magnifiesToVerifiedDAGSource :
      target.noBoundedSolver → VerifiedNPDAGLowerBoundSource
  ```

- **Inputs needed:** a concrete search/compression problem, a circuit family
  class, a size schedule, a proof that no bounded solver exists, and a separate
  magnification contract.
- **Status:** active pnp4 mainline interface.  It is not audit-only and not
  refuted, but it deliberately separates weak lower bound from magnification.
- **Bridge role:** `SearchMCSPWeakLowerBound.of_weakCircuitLowerBound` packages a
  concrete weak lower bound plus its magnification contract into the older
  `SearchMCSPWeakLowerBound` surface.

### Existing tree-MCSP concrete target

- **File path:** `pnp4/Pnp4/Frontier/SearchMCSPConcreteTargets.lean`.
- **Current type/signatures:**

  ```lean
  structure TreeMCSPSearchWitnessEncoding (threshold : Nat → Nat) where
    witnessBits : Nat → Nat
    verifies : ∀ n, TruthTable n → BitVec (witnessBits n) → Prop
    sound : ∀ n tt w, verifies n tt w → treeMCSPPredicate n (threshold n) tt
    complete : ∀ n tt, treeMCSPPredicate n (threshold n) tt → ∃ w, verifies n tt w

  def treeMCSPSearchProblem (threshold encoding) :
    SearchMCSPCompressionProblem

  def treeMCSPSearchWeakLowerBoundTarget
      (threshold encoding C sizeBound) :
    SearchMCSPWeakCircuitLowerBoundTarget

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

- **Inputs needed:** a threshold schedule, an explicit tree-circuit witness
  encoding, a circuit class and size schedule for solvers, a proof of no bounded
  promised tree-MCSP search solver, and a magnification contract to a verified
  DAG lower-bound source.
- **Status:** active pnp4 mainline target skeleton.  It is not refuted, but its
  decisive fields are uninhabited by current mathematics.
- **Bridge role:** `TreeMCSPSearchMagnificationSource.verifiedSource` returns
  `VerifiedNPDAGLowerBoundSource`; the file also provides final consequences to
  `NP_not_subset_Ppoly` and `P_ne_NP` conditional on such a source package.

### `VerifiedNPDAGLowerBoundSource`

- **File path:** `pnp4/Pnp4/AlgorithmsToLowerBounds/BridgeToPpolyDAG.lean`.
- **Current type/signature:**

  ```lean
  structure VerifiedNPDAGLowerBoundSource where
    L : DagLanguage
    inNP : Pnp3.ComplexityInterfaces.NP L
    notInPpolyDAG : ¬ Pnp3.ComplexityInterfaces.PpolyDAG L
  ```

- **Inputs needed:** an explicit language `L`, an `NP` verifier for `L`, and a
  proof that `L` is not in `PpolyDAG`.
- **Status:** active final-bridge source interface.  It is the honest pnp4 source
  boundary for mainline progress.
- **Bridge role:** `NP_not_subset_PpolyDAG_of_verified_source` converts this
  package into `Pnp3.ComplexityInterfaces.NP_not_subset_PpolyDAG`, and
  `P_ne_NP_of_verified_source` feeds the existing final `P != NP` wrapper.

### `PpolyDAG` and `NP_not_subset_PpolyDAG`

- **File path:** `pnp3/Complexity/Interfaces.lean`.
- **Current type/signatures:**

  ```lean
  structure InPpolyDAG (L : Language) where
    polyBound : Nat → Nat
    polyBound_poly : ∃ c, ∀ n, polyBound n ≤ n ^ c + c
    family : ∀ n, DagCircuit n
    family_size_le : ∀ n, DagCircuit.size (family n) ≤ polyBound n
    correct : ∀ n x, DagCircuit.eval (family n) x = L n x

  def PpolyDAG (L : Language) : Prop := ∃ _ : InPpolyDAG L, True

  def NP_not_subset_PpolyDAG : Prop := ∃ L, NP L ∧ ¬ PpolyDAG L
  ```

- **Inputs needed:** for `PpolyDAG`, a non-uniform polynomial-size DAG family
  deciding the language; for `NP_not_subset_PpolyDAG`, an `NP` language and a
  proof that no such DAG family exists.
- **Status:** active frozen trust-root target boundary, not a candidate and not
  refuted.
- **Bridge role:** this is the final DAG-separation proposition underlying both
  the pnp4 verified-source bridge and the pnp3 `ResearchGapWitness` target.

### `ResearchGapWitness`

- **File path:** `pnp3/Magnification/UnconditionalResearchGap.lean`.
- **Current type/signature:**

  ```lean
  def ResearchGapTarget : Prop :=
    ComplexityInterfaces.NP_not_subset_PpolyDAG

  structure ResearchGapWitness : Type where
    dagSeparation : ResearchGapTarget
  ```

- **Inputs needed:** an honest proof of `NP_not_subset_PpolyDAG` inhabiting the
  `dagSeparation` field.
- **Status:** active final research-gap target product.  It is a placeholder in
  the sense that the repository has not honestly inhabited it; it is not
  audit-only and not refuted.
- **Bridge role:** `P_ne_NP_of_researchGap`, `NP_not_subset_PpolyDAG_final`, and
  `P_ne_NP_final` are conditional on `ResearchGapWitness`.

### Relevant side-track MCSP / gap-MCSP objects

- **File paths:**
  - `pnp4/Pnp4/AlgorithmsToLowerBounds/TruthTableMCSP.lean`;
  - `pnp3/Models/Model_PartialMCSP.lean`;
  - `pnp3/LowerBounds/AC0_GapMCSP.lean`;
  - `pnp3/Magnification/Bridge_to_Magnification_Partial.lean`.
- **Current type/signatures:**
  - `treeMCSPPredicate n s tt := MCSPPredicate treeCircuitClass n s tt`.
  - `gapPartialMCSP_Language p` is a fixed-slice partial-MCSP language.
  - `GapPartialMCSP_not_in_AC0 p := ¬ GapPartialMCSP_in_AC0 p`.
  - The partial-MCSP bridge currently yields formula/real separations such as
    `NP_not_subset_PpolyFormula_from_partial_formulas`, not a DAG separation.
- **Inputs needed:** restricted-model solver exclusions, locality providers, and
  formula lower-bound hypotheses.
- **Status:** useful restricted lower-bound / formula-track side context.  It is
  not enough for pnp4 mainline without an explicit `PpolyDAG` bridge.
- **Bridge role:** no direct `VerifiedNPDAGLowerBoundSource` bridge was found for
  the existing partial-MCSP restricted lower-bound surface.

## 3. Candidate direct MCSP source statement

I considered exactly one direct candidate statement:

```text
CandidateTreeMCSPSearchSource :=
  Nonempty Pnp4.Frontier.TreeMCSPSearchMagnificationSource
```

Expanded informally, this says that there exist:

- a threshold schedule for tree-MCSP;
- a sound and complete encoding of tree-circuit witnesses;
- a circuit family class and solver size schedule;
- a proof that no bounded solver for the promised tree-MCSP search relation
  exists at that schedule; and
- a magnification contract converting that no-bounded-solver theorem into a
  `VerifiedNPDAGLowerBoundSource`.

This candidate is closer to the existing `SearchMCSPWeakLowerBound` /
`VerifiedNPDAGLowerBoundSource` interfaces than any FP3b route because it is
literally expressed through the pnp4 search-MCSP mainline target.  It does not
try to classify witnesses by FP3b-style filters or promote a guard.  However,
that closeness is also the fatal problem: the candidate is currently a package
shape, not a concrete mathematical source statement.

## 4. Non-circularity audit

### Result

**Partially non-circular as syntax; not acceptable as a source theorem.**

The weak-lower-bound half of `CandidateTreeMCSPSearchSource` is not literally
`NP_not_subset_PpolyDAG` or `P != NP`.  It talks about the nonexistence of a
bounded family of output-bit circuits solving a promised tree-MCSP witness
search problem.  That is at least formally upstream of the verified-source
endpoint.

The fatal issue is the second half: the `SearchMCSPMagnificationContract` field
has type

```lean
target.noBoundedSolver → VerifiedNPDAGLowerBoundSource
```

If the candidate is accepted merely because it contains this field, then the
missing hard part has been moved into an abstract contract.  Unless the contract
is expanded into a concise, independently auditable theorem, the candidate is
not a real source theorem; it is a wrapper around the desired verified DAG
source.

It does **not** directly restate `P != NP`, and it does **not** explicitly assume
`NP_not_subset_PpolyDAG`.  But it risks hiding the whole DAG separation in the
magnification field.  Under the requested pessimistic standard, this is a fatal
D0 issue.

## 5. Natural Proofs audit

### Constructivity

The weak tree-MCSP search statement is formulated over truth-table inputs and a
bounded solver relation.  If a future proof derives the lower bound by building
an efficiently checkable property of truth tables that accepts all hard
functions and rejects all functions with small circuits, then constructivity is
present.

At the current D0 level, no non-constructive or proof-complexity obstruction has
been identified.  Therefore there is no structural constructivity escape yet.

### Largeness

The promised tree-MCSP search problem is only total on low-complexity truth
tables, so the search relation itself is not automatically a large property of
all Boolean functions.  But the usual proof route for a lower bound on solvers
could easily become a large truth-table property: a broad, efficiently
recognizable class of tables on which bounded solvers fail or distinguish hard
from easy instances.

No D0 evidence shows a density-small or representation-sensitive escape from
largeness.

### Usefulness

The desired downstream contract must be useful against `PpolyDAG`, because it
must output an `NP` language with `¬ PpolyDAG`.  This is exactly the usefulness
leg of the Razborov--Rudich danger if the proof proceeds through a large
constructive Boolean-function property.

### Natural-proofs result

**Not passed.**  The candidate does not currently exhibit a
`NaturalProofBypassWitness`-style break of constructivity, largeness, or
usefulness.  It may avoid the classical shape only if the magnification proof is
not a large constructive property of truth tables, but D0 found no concrete
structural reason to believe that.

## 6. NOGO-000006/7/8/9 audit

### `NOGO-000006` — arbitrary all-essential log-width `ttFormula` payload

**Status: not applicable to the candidate statement; partially addressed for
future proof routes.**

The candidate is not a support-window criterion and does not accept witnesses
because they have logarithmic support.  Therefore the exact arbitrary
all-essential log-width `ttFormula` payload attack does not directly instantiate
against the statement.

However, any future proof that tries to recover the weak lower bound by arguing
from a small observed variable window or payload budget would re-enter this NoGo
immediately.  Round 1 would need an explicit check that no hardwired truth-table
payload can satisfy the search-source assumptions for trivial reasons.

### `NOGO-000007` — support-cardinality-only meta-barrier

**Status: not applicable to the candidate statement; partially addressed for
future proof routes.**

The candidate is a search-MCSP source package, not a support-profile classifier.
It does not compare witnesses solely by support-cardinality profiles.

The warning remains relevant: if a future proof of the weak lower bound reduces
the obstruction to a support-size invariant of truth tables or witness circuits,
then canonical hardwiring twins can likely simulate the accepted profile.  The
D0 candidate has not supplied the formal anti-hardwiring lemma that would be
needed to make this safe.

### `NOGO-000008` — tautological rewrite attack

**Status: not applicable to the candidate statement; partially addressed for
future proof routes.**

The candidate does not accept or reject formulas based on displayed gate shapes.
A tautological rewrite such as adjoining `x OR NOT x` to a formula is therefore
not directly an attack on the source statement.

The risk returns if the future weak-lower-bound proof relies on displayed syntax
of tree witnesses rather than extensional computation of the truth table and a
sound codec.  The existing `TreeCircuitWitnessCodec.verifies` relation is more
semantic than a displayed-syntax filter because it requires a decoded circuit to
compute the truth table, but this does not by itself prove robustness of the
magnification argument.

### `NOGO-000009` — normalize-then-filter self-defeat

**Status: not applicable to the candidate statement; partially addressed for
future proof routes.**

The candidate does not propose a normalizer followed by a syntactic filter, so
the exact self-defeat theorem does not apply.

The broader lesson still applies: any future attempt to patch a syntactic proof
of the weak lower bound by normalizing witnesses must show that the normalizer
preserves the non-vacuity source and does not erase the very structure used by
the argument.  No such evidence exists at D0.

## 7. Relativization / algebrization audit

The candidate does **not** identify a non-relativizing component.

The candidate does **not** identify a non-algebrizing component.

The repository barrier interfaces are abstract: `RelativizationBypassWitness`
requires two oracle worlds separating a statement scheme, and
`AlgebrizationBypassWitness` requires two algebraic oracle worlds separating a
statement scheme.  D0 found no proposed witness of either kind for the direct
tree-MCSP search candidate.

This is a serious weakness.  A search-MCSP lower-bound-to-`PpolyDAG` bridge that
relativizes or algebrizes is unlikely to be a credible route to the final
non-uniform separation.  Without an identified non-relativizing or
non-algebrizing ingredient, the candidate cannot be green-lit.

## 8. Path to `VerifiedNPDAGLowerBoundSource`

### Formal package chain if the candidate is assumed

If `CandidateTreeMCSPSearchSource` is assumed as a fully inhabited package, then
the repository chain is concrete:

```text
CandidateTreeMCSPSearchSource
  := Nonempty TreeMCSPSearchMagnificationSource

TreeMCSPSearchMagnificationSource
  → TreeMCSPSearchMagnificationSource.verifiedSource
  : VerifiedNPDAGLowerBoundSource

VerifiedNPDAGLowerBoundSource
  → NP_not_subset_PpolyDAG_of_verified_source
  : NP_not_subset_PpolyDAG

NP_not_subset_PpolyDAG
  → ResearchGapWitness.dagSeparation
  by constructing ResearchGapWitness with dagSeparation := that proof
```

The analogous generic chain is:

```text
SearchMCSPWeakCircuitLowerBound target
+ SearchMCSPMagnificationContract target
  → SearchMCSPWeakLowerBound.of_weakCircuitLowerBound
  → SearchMCSPWeakLowerBound.verifiedSource
  → VerifiedNPDAGLowerBoundSource
  → NP_not_subset_PpolyDAG
  → ResearchGapWitness.dagSeparation
```

### Why this is not enough

The chain exists only because the candidate includes the exact missing
magnification contract:

```text
target.noBoundedSolver → VerifiedNPDAGLowerBoundSource
```

That contract is the whole hard bridge.  The weak tree-MCSP search lower bound
alone gives no `VerifiedNPDAGLowerBoundSource`; the current repository has no
proved theorem converting the weak lower bound by itself into an `NP` language
lower bound against `PpolyDAG`.

Therefore the path is formally clear but mathematically under-specified.  This
is better organized than FP3b provenance-filter paths, but it is not yet a
concrete source route.

## 9. First self-attacks

A future reconsideration would need to pass at least these attacks before any
Round 1 is responsible:

1. **Hidden `PpolyDAG` hardness assumption:** expand the magnification contract
   and check that no assumption is equivalent to `¬ PpolyDAG L`, no small DAG
   witness, or `NP_not_subset_PpolyDAG`.
2. **Natural-proof largeness:** determine whether the proof constructs a large,
   efficiently checkable, useful property of truth tables.
3. **Constructivity escape audit:** if the proof claims not to be constructive,
   identify the exact non-constructive or proof-theoretic ingredient and explain
   why it is acceptable in Lean without adding a hidden axiom.
4. **Relativization attack:** formulate the statement as an oracle-parametric
   scheme and look for oracle worlds where the weak lower bound and the claimed
   magnification disconnect.
5. **Algebrization attack:** repeat the previous attack for algebraic-oracle
   extensions and multilinear-extension style access.
6. **Vacuity / ex falso attack:** ensure the promise search problem is total for
   nontrivial reasons and the weak-lower-bound proof is not obtained from an
   inconsistent or impossible encoding.
7. **Codec padding attack:** check that changing witness encodings, padding
   encodings, or using degenerate decoders cannot make the lower-bound statement
   true for irrelevant encoding reasons.
8. **Search-to-decision collapse attack:** show that the search lower bound does
   not merely repackage a decision-MCSP lower bound that is already as hard as
   the desired DAG separation.
9. **Restricted-side-track leakage:** verify that the route does not quietly fall
   back to `AC0[p]`, formula, local-PRG, or partial-MCSP restricted conclusions
   without a `PpolyDAG` bridge.
10. **Known refuted predicate scan:** check that the proof does not transitively
    use refuted support-bounds, multiswitching-only, or audit-route endpoints.

## 10. Recommended next action

**RED_light_fp3b8.**

Fatal issue: the only candidate that cleanly reaches existing source interfaces
is `TreeMCSPSearchMagnificationSource`, but that object already contains the
missing magnification contract to `VerifiedNPDAGLowerBoundSource`.  Treating this
as the source statement would move the hard theorem into a field rather than
finding it.

I do **not** recommend opening full fp3b8 Round 1.  The useful next move is to
return to the broader `ResearchGap` source search, or to run a separate second
D0 only if a worker brings a genuinely new non-relativizing / non-algebrizing
mechanism for the `SearchMCSPMagnificationContract` field.
