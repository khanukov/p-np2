# ResearchGap source theorem reset after FP3b / fp3b6 / fp3b7 / fp3b8 red-lights

Handle: `gpt55`

## 1. Executive verdict

**search_mcsp_contract_expansion**

The smallest honest source theorem surface still worth attacking is not another
local provenance filter and not another package that merely names a source.  It
is the expansion of the currently abstract `SearchMCSPMagnificationContract` into
a concrete theorem with all assumptions visible:

```text
noBoundedSolver(target) → VerifiedNPDAGLowerBoundSource
```

This is the narrowest remaining mainline surface because the repository already
identifies `VerifiedNPDAGLowerBoundSource` as the honest bridge package: an
explicit language, an NP proof, and a DAG lower bound.  The existing search-MCSP
frontier is also the only current route family whose interface is deliberately
wired to produce that package rather than a restricted lower bound.  The recent
fp3b8 red-light shows that **assuming** the contract is a wrapper; the reset is to
study the contract itself, not to keep wrapping it.

## 2. What the actual target is

The actual target remains:

```text
ResearchGapWitness.dagSeparation
= NP_not_subset_PpolyDAG
= ∃ L, NP L ∧ ¬ PpolyDAG L
```

In the pnp3 research-gap module, `ResearchGapTarget` is definitionally
`ComplexityInterfaces.NP_not_subset_PpolyDAG`, and the only mathematical field of
`ResearchGapWitness` is `dagSeparation : ResearchGapTarget`.  The public DAG
endpoint simply returns `gap.dagSeparation`, so any honest source theorem must
produce the same separation rather than a renamed surrogate.

The pnp3 interface defines `PpolyDAG L` through an explicit polynomial-size
family of `DagCircuit`s with correctness at every length and input.  It defines
canonical `NP L` as the TM-verifier track, then defines
`NP_not_subset_PpolyDAG` exactly as an existential language separation.
Therefore a source theorem must eventually produce all three pieces:

1. an explicit language `L`;
2. a proof that `L ∈ NP` in the canonical verifier sense;
3. a proof that `L ∉ PpolyDAG`, i.e. no polynomial-size DAG-circuit family
   decides `L` on all lengths.

The pnp4 bridge confirms the same boundary: `VerifiedNPDAGLowerBoundSource` is
nothing more and nothing less than `L`, `inNP`, and `notInPpolyDAG`, and the
bridge to `NP_not_subset_PpolyDAG` is the tuple constructor.

## 3. What is forbidden as fake source theorem

The following are rejected source-theorem surfaces for this reset:

- **`Nonempty ResearchGapWitness`.**  This is just existential packaging around
  the final target.  It does not expose the language, the NP proof, or the DAG
  lower-bound argument in a smaller attackable theorem.
- **`Nonempty VerifiedNPDAGLowerBoundSource`.**  This is equivalent to producing
  the final bridge package, not a source theorem explaining where the package
  comes from.
- **`TreeMCSPSearchMagnificationSource` without expanding the magnification
  contract.**  The tree-MCSP package contains a weak lower bound plus a
  `SearchMCSPMagnificationContract`; its `verifiedSource` is obtained by applying
  the weak lower bound to that contract.  If the contract stays abstract, the
  package only moves the missing theorem into a field.
- **Any source theorem containing a field
  `weakLowerBound → VerifiedNPDAGLowerBoundSource`, unless that implication is
  itself the new theorem being studied.**  Such a field is exactly the missing
  magnification step.  It may be the object of study, but it cannot be assumed as
  a premise and then counted as progress.
- **Any predicate equivalent to `¬ PpolyDAG` hidden in a promise or certificate.**
  If the promise says, directly or indirectly, that no polynomial-size DAG family
  decides the language, then the source theorem is circular.
- **Any use of refuted support-bounds routes.**  The research-gap module states
  that lower-level approaches are acceptable only if they prove the DAG
  separation without using the refuted support-bounds surfaces.  The NoGoLog
  entries NOGO-000001 through NOGO-000009 record repeated hardwiring and
  syntactic/provenance-filter failures in those local families.
- **Any NaturalProof-shaped large constructive useful property.**  The barrier
  interface formalizes the natural-proof triad as constructivity, largeness, and
  usefulness against `P/poly`; a candidate that fits that triad must be treated as
  barrier-hit unless it carries an explicit bypass witness.

## 4. Candidate source surfaces

### Candidate A — Expand `SearchMCSPMagnificationContract` itself

- **Exact informal statement.**  For a concrete search-MCSP/compression target
  `target`, prove a theorem of the form:

  ```text
  SearchMCSPContractExpansion(target, hypotheses) :
    target.noBoundedSolver → VerifiedNPDAGLowerBoundSource
  ```

  The hypotheses must be strictly weaker than `VerifiedNPDAGLowerBoundSource` and
  must expose the problem, promise, relation, circuit class, size schedule,
  encoding assumptions, reductions, and any hardness-vs-randomness or
  compression-magnification lemma being used.

- **Where it would sit in the repo.**  Design work should start as a markdown D0
  under `seed_packs/source_search_contract_expansion_D0/`.  If later formalized,
  the theorem surface would belong near
  `pnp4/Pnp4/Frontier/SearchMCSPMagnification.lean` or a sibling frontier module,
  but this reset does not authorize Lean code.

- **How it produces `L ∈ NP`.**  The expansion must explicitly construct the
  language `L` from the search/compression target and give a TM verifier for it.
  For example, `L` might encode instances, witnesses, and length-indexed
  consistency checks so that membership can be verified by the stated relation
  and codec.  D0 must require a line-by-line NP-verifier budget, not merely say
  that MCSP is in NP.

- **How it proves `¬ PpolyDAG L`.**  The proof must show that any polynomial-size
  DAG family deciding the constructed `L` would yield a bounded solver for the
  target, contradicting `target.noBoundedSolver`.  This contrapositive extraction
  is the mathematical core: from a decider for `L`, build the forbidden solver
  with the exact circuit class/size loss visible.

- **Why it is not just a wrapper around `VerifiedNPDAGLowerBoundSource`.**  It is
  not allowed to contain a field whose type is the desired implication.  The
  implication itself is the theorem to be attacked, with a concrete construction
  of `L`, a concrete NP verifier, and a concrete decider-to-solver reduction.

- **First NoGo/barrier attack.**  Attempt to instantiate a trivial or hardwired
  `PpolyDAG` decider for the proposed `L` and see whether the extraction really
  yields a bounded solver.  Then check whether the theorem's distinguishing
  property is large, constructive, and useful in the natural-proofs sense.  Also
  oracle-parameterize the construction to test whether it is merely
  relativizing/algebrizing.

- **Whether it deserves a D0 seed pack.**  **Yes.**  This is the recommended next
  seed pack, because it attacks the exact missing implication exposed by fp3b8
  rather than renaming a failed route.

### Candidate B — Proof-complexity source surface

- **Exact informal statement.**  A feasible-interpolation or bounded-arithmetic
  theorem: if a specified proof system has explicit lower bounds for a family of
  tautologies/unsatisfiable formulas, then the interpolant language `L` is in NP
  and is not in `PpolyDAG`.

- **Where it would sit in the repo.**  Initial D0 design would belong under
  `seed_packs/source_search_proof_complexity_D0/`.  Later formal work, if any,
  should be separate from the current search-MCSP frontier until it exposes a
  direct `VerifiedNPDAGLowerBoundSource` bridge.

- **How it produces `L ∈ NP`.**  `L` would be the accepting side of an
  interpolation relation or bounded-arithmetic definable search predicate whose
  certificates are proof fragments, assignments, or witnesses checked in
  polynomial time.

- **How it proves `¬ PpolyDAG L`.**  The proof would show that a polynomial-size
  DAG family for `L` can be converted into short proofs or efficient
  interpolants, contradicting the assumed proof-complexity lower bound.

- **Why it is not just a wrapper around `VerifiedNPDAGLowerBoundSource`.**  It
  would derive the DAG lower bound through a proof-system-to-circuit simulation
  and interpolation theorem, not by assuming a source package.  However, the D0
  must ensure the assumed proof-complexity lower bound is not already as strong
  as `NP ⊄ PpolyDAG`.

- **First NoGo/barrier attack.**  Check whether the assumed proof lower bound is
  an unproved theorem at least as hard as the endpoint, whether interpolation
  only yields restricted circuit lower bounds, and whether the argument
  relativizes.  Also test whether the language hides `¬ PpolyDAG` inside a
  proof-system soundness promise.

- **Whether it deserves a D0 seed pack.**  **Not first.**  It may deserve a later
  D0, but it is currently less tightly connected to the existing pnp4 mainline
  than contract expansion.

### Candidate C — Formal barrier route

- **Exact informal statement.**  Formalize a meta-barrier showing that broad
  classes of provenance/filter/source-package surfaces cannot produce
  `VerifiedNPDAGLowerBoundSource` unless they already contain an assumption
  equivalent to `¬ PpolyDAG` or fall into natural-proof/relativization/
  algebrization barriers.

- **Where it would sit in the repo.**  Design work would be a D0 under
  `seed_packs/source_search_barrier_formalisation_D0/`.  Later Lean work, if any,
  would sit under `pnp3/Barrier/` or an audit-only pnp4 barrier module, not in the
  mainline bridge.

- **How it produces `L ∈ NP`.**  It does not produce `L ∈ NP`; it is a negative
  route.  Its output is route hygiene, not the source theorem.

- **How it proves `¬ PpolyDAG L`.**  It does not prove the endpoint; it proves
  that a family of candidate theorem surfaces cannot honestly prove it.

- **Why it is not just a wrapper around `VerifiedNPDAGLowerBoundSource`.**  It is
  not a source theorem at all.  It is honest only if reported as infrastructure
  or audit progress, never as P-vs-NP mainline progress.

- **First NoGo/barrier attack.**  Verify that the barrier class is not so broad
  that it rules out the repository's own accepted source interfaces by
  definition, and not so narrow that it only restates fp3b failures.  The first
  target class should be source packages containing abstract
  `weakLowerBound → VerifiedNPDAGLowerBoundSource` fields.

- **Whether it deserves a D0 seed pack.**  **Only after** the contract-expansion
  D0 fails to find a non-wrapper theorem shape.  It is valuable, but opening it
  first would prematurely convert the reset into audit-only work.

## 5. Best next seed pack

**Recommend exactly one:**

```text
seed_packs/source_search_contract_expansion_D0/
```

Do not create it in this task.

## 6. First D0 question

```text
Can SearchMCSPMagnificationContract be expanded into a concrete theorem whose assumptions are strictly weaker than VerifiedNPDAGLowerBoundSource and which avoids natural proofs / relativization / algebrization?
```

The first pass must force the candidate to spell out: the target, the language
`L`, the NP verifier, the contrapositive conversion from a `PpolyDAG` decider for
`L` into a bounded search solver, and the barrier-bypass evidence.

## 7. NoGoLog recommendation

**create design-constraints registry instead**

Do not edit `outputs/nogolog.jsonl` for this reset.  The existing NoGoLog entries
NOGO-000001 through NOGO-000009 are formal or review-level closures for specific
hardwiring/provenance/syntactic-normalization failures.  The recent fp3b6,
fp3b7, and fp3b8 documents are broader route-management decisions: stalled
budget mismatch, usefulness weakness, and abstract-contract wrapping.  They are
important constraints, but they should not become NOGO-000010+ unless a later
Lean formal meta-barrier pins a precise reusable failure class.

A lightweight design-constraints registry would be more honest now.  It should
record constraints such as:

- payload-window hiding must account for fingerprint footprint versus width
  budget;
- almost-natural provenance must avoid usefulness weakness rather than merely
  block hardwiring syntax;
- direct MCSP source interfaces must expand the magnification contract instead
  of containing it as a field.

## 8. Final recommendation

Stop FP3b/fp3b8 local routes as source-theorem searches.  FP3b provenance work
can remain audit/no-go infrastructure, and fp3b8's current direct MCSP package
should not be kept alive by renaming `TreeMCSPSearchMagnificationSource` or by
adding another field that already contains
`weakLowerBound → VerifiedNPDAGLowerBoundSource`.

Open exactly one new source-search D0:

```text
seed_packs/source_search_contract_expansion_D0/
```

The first D0 question should be:

```text
Can SearchMCSPMagnificationContract be expanded into a concrete theorem whose assumptions are strictly weaker than VerifiedNPDAGLowerBoundSource and which avoids natural proofs / relativization / algebrization?
```

If that D0 cannot produce a concrete non-wrapper theorem shape, the next honest
move is not another local provenance route; it is a formal barrier D0 explaining
why the current source surfaces cannot work.
