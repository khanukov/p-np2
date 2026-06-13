# Input 1, Session 2: Self-Contained Attack Notes (no external sources)

Updated: 2026-06-13

Ground rule for this session: no literature lookups, no web search.  Every
argument below was re-derived from scratch against the in-repo definitions
(`NP_TM`, `PpolyDAG`, `DagCircuit`), and everything provable that survived
the attack was formalized in
`pnp4/Pnp4/AlgorithmsToLowerBounds/SparseWitnessPruning.lean`.

The target is the residual gap left by `DagShannonCounting.lean`:

```text
produce L with   NP L   and   ¬ PpolyDAG L.
```

## Attack line 1: diagonalize inside NP directly

Idea: build an `NP_TM` verifier whose language *forces* disagreement with
every small DAG family.

Where it dies.  Fix a verifier `M` with parameters `(c, k)`.  The slice
`L n : Bitstring n → Bool` is completely determined by the finite control
of `M` (a constant-size object) plus the single number
`runTime (n + n^k + k) ≤ poly(n)`.  So an `NP_TM` language carries
`O(log n)` bits of per-length description, while a `PpolyDAG` family is
allowed `poly(n) · log n` bits of per-length description (the circuit).
The adversary the diagonal must defeat has *strictly more* description
budget per length than the diagonal itself.  Any argument that works by
"counting descriptions" therefore proves the wrong inequality — it shows
the *verifier* class is thin, not the circuit class.  Conclusion: pointwise
or description-counting diagonalization cannot see the separation; hardness
of an `NP` slice must *emerge* from the verifier's combinatorics, not be
enforced index-by-index.

## Attack line 2: hardness certification by certificates

Idea: let the certificate carry a proof that some hard function exists,
e.g. `L = { x : the lexicographically-first hard table at length |x| has
property P(x) }`.

Where it dies.  Certificates have length `n^k + k`; the objects whose
hardness matters are truth tables of length `2^n`, and "table T is hard"
is a universal statement over all `poly(n)`-size DAG descriptions —
checkable in time `2^{poly(n)}`, not `poly(n)`.  The natural quantifier
prefix is `∃ table ∀ circuit`, two alternations over exponential-size
objects; nothing in the `NP_TM` budget can verify even one alternation.
This is the precise sense in which the Shannon argument refuses to become
explicit at the `NP` level: the repo's own
`exists_hard_function_for_dag_gates` produces witnesses of size `2^n`
with `Π₁`-hardness conditions, and no `poly(n)`-certificate squeeze is
available.  (One level up, with an exponential budget, exactly this
argument works and is classical; the `NP` budget is the obstruction.)

## Attack line 3: collapse self-improvement

Idea: assume `NP ⊆ PpolyDAG` and derive a contradiction from the
repo-internal consequences (the audit's hardwiring argument shows e.g.
`NP/log ⊆ P/poly` follows).

Where it dies.  All consequences derivable with in-repo tools are
upper-bound-shaped ("even more things have small circuits"); a
contradiction needs one *lower* bound somewhere in the consequence chain,
and every unconditional lower bound currently in the repository
(`DagShannonCounting`) concerns languages with no verifier.  The classical
way out (collapse of a quantifier hierarchy onto a level that provably
contains a fixed-polynomial-hard language) needs a formalized polynomial
hierarchy and a fixed-polynomial circuit lower bound for it — neither
exists in-repo, and even with both, the known mathematics yields only
fixed-exponent bounds for higher levels, not superpolynomial bounds
for `NP`.  Recorded as out of reach by an honest margin, not by a
formalization accident.

## Attack line 4: thin witnesses (this session's salvage)

Idea: perhaps the witness can be taken *structurally simple* — a unary /
tally language, a language with few accepted strings per length, or the
complement of one.  Several "natural candidate" proposals have this shape
because thin languages are easy to place in `NP`.

This line dies *provably*, and the refutation is now a theorem pair:

```text
PpolyDAG_of_polySparse   : PolySparse L   → PpolyDAG L
PpolyDAG_of_polyCosparse : PolyCosparse L → PpolyDAG L
```

(`PolySparse L` = at most `n ^ c + c` accepted strings at every length;
`PolyCosparse` dually for rejected strings.)  The construction is the
explicit DNF of the thin slice, built from new reusable `DagCompose`-level
combinators (`notC`, `andC`, `orC`, `andList`, `orList`, `literalCircuit`,
`eqCircuit`, `dnfCircuit`) with exact `eval` laws and the size law
`size (dnfCircuit A) ≤ 2 + |A| (5n + 4)`, absorbed into the single
schedule `n ^ (9c+13) + (9c+13)` (`master_poly_bound`).

Consequences wired to the frontier interfaces:

```text
VerifiedNPDAGLowerBoundSource.not_polySparse
VerifiedNPDAGLowerBoundSource.not_polyCosparse
dagHardLanguage_not_polySparse
dagHardLanguage_not_polyCosparse
```

So: **any valid witness for input 1 must have superpolynomially many
accepted strings and superpolynomially many rejected strings** (at
infinitely many lengths).  Unary languages, polynomially-padded point
sets, and their complements are formally out, regardless of how clever
their `NP` verifiers are.  As a sanity check, the unconditional diagonal
witness of `DagShannonCounting` is provably dense on both sides.

## Net assessment after this session

The residual target is now boxed in from three formal directions:

1. (`DagShannonCounting`) hard languages exist unconditionally at the
   endpoint class — hardness alone is not the obstruction;
2. (`SparseWitnessPruning`) the witness cannot be thin on either side —
   structural simplicity of the accepted set is not available;
3. (faithfulness audit, session 1) the statement itself offers no
   definitional slack.

What remains is exactly the classical difficulty: an `NP` verifier whose
language is *dense, co-dense, and provably complex*.  No proof of that
was found in this session, and the lines above record precisely where
each self-generated approach stops.  Per the Research Constitution this
file claims no more than what compiles: two new unconditional upper-bound
theorems, four pruning corollaries, and a sharper map of the gap.
