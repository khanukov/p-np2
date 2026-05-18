# L0 hInDag triviality probe — gpt55

## Scope classification

Infrastructure / Lean-probe audit.  This task does **not** reduce
`VerifiedNPDAGLowerBoundSource` or `SearchMCSPWeakLowerBound`, and it does not
claim P-vs-NP mainline progress.  It only probes whether the canonical route
hypothesis

```lean
∀ n β, InPpolyDAG
  (gapPartialMCSP_Language
    ((eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym).paramsOf n β))
```

is trivially dischargeable by fixed-slice truth-table DAG hardwiring.

## Required reading checked

- `RESEARCH_CONSTITUTION.md`: Rule 1 / Rule 6 / Rule 16 constraints were treated
  as route-policy constraints; no endpoint or P ≠ NP claim is made here.
- `STATUS.md`: current canonical asymptotic infrastructure and the warning that
  old support-bounds/provider routes are vacuous were taken as the active status.
- `seed_packs/hInDag_triviality_probe_L0/README.md`: expected L0 outcome and
  allowed verdicts were used.
- `seed_packs/hInDag_triviality_probe_D0/reports/D0_hindag_triviality_gpt55.md`:
  the D0 conclusion that markdown-only evidence is insufficient was respected.
- `pnp3/Magnification/CanonicalAsymptoticTrackData.lean`: the canonical
  instantiation target is `canonicalAsymptoticHAsym` via
  `eventualGapSliceFamily_of_asymptotic`.
- `pnp3/Models/Model_PartialMCSP.lean`: `gapPartialMCSP_Language p` is false
  off `partialInputLen p` and may be nontrivial on that single slice.
- `pnp3/Complexity/Interfaces.lean`: `DagCircuit` is a dependent acyclic DAG
  syntax; `InPpolyDAG` requires an explicit `family : ∀ n, DagCircuit n` with
  kernel-checked semantic correctness.
- `pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean`: the local
  `constFalseDag` shape is straightforward, but it only solves off-slice cases.
- `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`: the recursive
  `ttFormula` template is useful, but importing it is prohibited and its syntax
  is formula-tree, not DAG.
- `pnp3/Magnification/FinalResultMainline.lean`: the `hInDag` consumer remains
  a separate conclusion-side question; this L0 probe only targets the premise.

## Attempted Lean design

The intended proof decomposes into:

1. local `constFalseDag` for all off-slice lengths;
2. a private truth-table DAG constructor `ttDag` for arbitrary
   `f : Bitstring n → Bool`;
3. `ttDag_eval`;
4. the fixed-slice `InPpolyDAG` witness using `ttDag` exactly at
   `partialInputLen p` and `constFalseDag` elsewhere;
5. the canonical one-line instantiation.

Step 1 is small.  The blocker is Step 2/3: with the current `DagCircuit` API,
there is no public append/rename/map combinator for dependent DAGs.  A recursive
Shannon construction needs at least:

- `DagCircuit.rename` for `Fin n → Fin (n+1)` input injections;
- a circuit-copy/offset operation for embedding two sub-DAGs into a larger DAG;
- an output-wire lift through that offset;
- semantic lemmas for the copied gates and renamed inputs;
- final `not`/`and`/`or` composition lemmas.

The direct DNF construction avoids recursive copying but replaces it with an
arithmetically indexed gate layout over all assignments and all coordinates;
its correctness proof still requires a substantial fold/evaluation invariant.
Neither route is plausibly ≤ 200 LOC as an isolated staging file without adding
reusable DAG infrastructure.

## Why no staging Lean file was landed

The prompt permits the verdict `INCONCLUSIVE_NEEDS_FULL_SESSION` when
`hInDag_for_canonicalAsymptoticHAsym` does not fit in 200 LOC or substantive
DAG infrastructure is required.  Landing a partial Lean file would create either
an uncompiled artifact or a misleading theorem surface.  I therefore did not
create `pnp3/Tests/HInDagTrivialityProbe.lean`.

## Command results

No staging Lean file was produced, so there was no new theorem surface to check
with `#check`.  I still ran the repository policy/build script after writing
this report.

## Blocking infrastructure

- `DagCircuit.rename` with `eval_rename`.
- A dependent DAG append/offset/copy operation with output-wire lifting.
- Small constructors for adding a unary or binary gate to an existing DAG.
- A reusable truth-table-to-DAG builder, preferably outside `pnp3/Tests`, with
  polynomial-size bookkeeping separated from semantic correctness.

Estimated implementation size for a clean L1 solution: 300–600 LOC, depending
on whether the existing straight-line adapter is used or native `DagCircuit`
append lemmas are developed.

## Verdict

**`INCONCLUSIVE_NEEDS_FULL_SESSION`**

Next action: `open_hindag_triviality_L1_multi_session`.
