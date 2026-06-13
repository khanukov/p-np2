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

## Attack line 5: structured witnesses — symmetry (second salvage)

Idea: perhaps a *combinatorially structured* dense language can witness the
gap — weight-based predicates (MAJORITY, thresholds, parity, exact-weight
and mod-counting tests) are dense, co-dense, and trivially in `NP`/`P`,
and "look hard" to weak models.

This line also dies provably.  The classical shared dynamic program for
prefix weights was formalized on the repository's `DagBundle` layer
(`weightBundle`: cell `(i, j)` decides "the first `i` bits have weight
exactly `j`"; `O(n²)` gates, additive growth via `snocBundleSubst`, plus a
new zero-cost `remapOutputs` primitive).  Its semantic law

```text
weightBundle_eval : (weightBundle n).evalOutput w x
                  = decide (hammingWeight x = w)
```

yields:

```text
PpolyDAG_of_weightDetermined :
  (∀ n x y, hammingWeight x = hammingWeight y → L n x = L n y) → PpolyDAG L
VerifiedNPDAGLowerBoundSource.not_weightDetermined
dagHardLanguage_not_weightDetermined
```

So **no symmetric language can witness input 1**: density alone is not
enough; the witness must break weight-symmetry in an essential way.
Together with the complement-closure law (`PpolyDAG_compl_iff`, proved en
route), the witness space is closed under complement and excludes the
sparse, co-sparse, and weight-determined corners.

## Attack line 6: strike at the statement shape itself (third salvage)

Direct order for this session: stop perimeter work and hit the goal's own
statement.  The full statement (`∃ L, NP L ∧ ¬ PpolyDAG L`) requires a
superpolynomial bound; the *shape* was achieved unconditionally at linear
strength, and both halves were new for the repository:

```text
evenParityLanguage_NP : NP evenParityLanguage
exists_NP_language_with_linear_dag_lower_bound :
  ∃ L, NP L ∧ ∀ n C, (∀ x, eval C x = L n x) → n ≤ 2 * C.gates + 1
```

1. The `NP` half is the **first concrete `NP_TM` membership ever proved
   in this repository** (the pnp4 TM-verifier programme had none).  The
   unlock: the strict model's `runTime : ℕ → ℕ` may depend on input
   length, so `parityTM` (a two-state XOR sweep with
   `runTime m = m - 1`) halts exactly at the instance/certificate
   boundary; no end-marker machinery is needed.  This makes every
   one-pass finite-state language cheaply `NP_TM`-certifiable — reusable
   for the verifier programme.
2. The lower-bound half is a support-counting argument at the endpoint
   model: a `DagCircuit` with `g` gates reads at most `2g + 1`
   coordinates (`card_support_le`), while parity provably reads all `n`
   (via the in-repo `eval_eq_of_eq_on_support`).
3. The honest ceiling of this line is also formal: the same language has
   `O(n²)` circuits (`evenParityLanguage_in_PpolyDAG`, from attack
   line 5's machinery), so this witness can never close input 1; and the
   support argument can never give more than `n` (a function only has
   `n` coordinates to read).  Crossing from linear to superpolynomial is
   precisely where natural proofs, relativization, and locality stand.

## Net assessment after this session

The boxed-in map after three working sessions:

1. (`DagShannonCounting`) hardness exists unconditionally at the endpoint;
2. (`SparseWitnessPruning`) the witness is dense and co-dense;
3. (`SymmetricWitnessPruning`) the witness is not weight-determined, and
   hardness is complement-symmetric;
4. (`ParityNPLowerBound`) the statement shape `NP ∧ lower bound` is
   achieved unconditionally at linear strength, with the first concrete
   `NP_TM` witness;
5. (faithfulness audit) the statement offers no definitional slack.

The residual target is an `NP` verifier whose language is dense, co-dense,
weight-asymmetric, and provably complex.  Every self-generated route to
*provable complexity* for an `NP` language still terminates at the
classical obstruction recorded in attack lines 1–3; what this session
added is that two more natural witness families are now theorem-level
dead ends rather than informal expectations.  No claim beyond what
compiles is made.
