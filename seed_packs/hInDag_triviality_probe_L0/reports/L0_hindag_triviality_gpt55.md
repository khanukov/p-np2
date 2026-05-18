# L0 hInDag triviality probe — gpt55

## Classification

Infrastructure / route-audit probe.  This work does **not** reduce
`SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource`, and it should not
be reported as P-vs-NP mainline lower-bound progress.  It proves a benign
non-uniform upper-bound/triviality witness for the `hInDag` premise used by the
canonical asymptotic route surface.

## Landed Lean artifact

Landed staging file:

```text
pnp3/Tests/HInDagTrivialityProbe.lean
```

The file is 121 lines, below the 200-LOC cap.  It contains:

- a local `constFalseDag` plus size/evaluation lemmas;
- a local `ttDag`, implemented by reusing the existing finite Boolean-cube
  truth-table tree circuit and the existing straight-line-to-DAG adapter;
- `ttDag_eval`, proved by composing the imported truth-table correctness,
  compile-tree wire semantics, and straight-line adapter wire semantics;
- `fixedSlice_gapPartialMCSP_in_PpolyDAG`, an `InPpolyDAG` witness for every
  fixed `gapPartialMCSP_Language p`;
- `hInDag_for_canonicalAsymptoticHAsym`, the canonical route-premise surface.

Lean note: `InPpolyDAG L` is a structure/type in this repository, not a `Prop`,
so the two public witness surfaces are implemented as `noncomputable def`s
rather than `theorem`s.  The noncomputability is explicitly documented in the
file and is inherited from bounded finite truth-table enumeration of a fixed
slice; no oracle, axiom, `sorry`, `admit`, or `native_decide` is introduced.

## Construction summary

The fixed-slice witness uses the standard hardwiring split:

1. At the unique encoded length `partialInputLen p`, use `ttDag` for the Boolean
   function `gapPartialMCSP_Language p (partialInputLen p)`.
2. At every other length, use the one-gate `constFalseDag`.
3. Correctness off-slice is immediate because `gapPartialMCSP_Language` unfolds
   to `false` when the input length differs from `partialInputLen p`.
4. Polynomial boundedness is trivial because there is only one hardwired
   exceptional length; the proof uses the constant size of the selected DAG as
   a polynomial exponent slack.

## Audits performed

- Staging LOC: `wc -l pnp3/Tests/HInDagTrivialityProbe.lean` returned `121`.
- Kernel check: `lake env lean pnp3/Tests/HInDagTrivialityProbe.lean` passed.
- Refuted-carrier string audit:
  `rg "FormulaCertificateProviderPartial|FormulaSupportRestrictionBoundsPartial|MagnificationAssumptions" pnp3/Tests/HInDagTrivialityProbe.lean`
  returned no matches.
- Full repository check: `./scripts/check.sh` passed after the Lean file was
  landed.

## Declaration names audited

- `constFalseDag`
- `constFalseDag_size`
- `constFalseDag_eval`
- `ttDag`
- `ttDag_eval`
- `fixedSlice_gapPartialMCSP_in_PpolyDAG`
- `hInDag_for_canonicalAsymptoticHAsym`

## Imports audited

```lean
import Complexity.Interfaces
import Models.Model_PartialMCSP
import Magnification.CanonicalAsymptoticTrackData
import Complexity.PsubsetPpolyInternal.Simulation
```

No import from `Magnification.LocalityProvider_Partial`, no import of
`pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`, and no import under
`pnp3/RefutedPredicates/` was added.

## Conclusion-side status

The `hInDag` premise at the canonical instantiation is now trivially inhabited
by hardwired non-uniform DAGs.  This does **not** by itself settle the downstream
`IsoStrongFamilyEventually` / promise-YES conclusion under the hardwired premise.
No small Lean argument or structural contradiction proving/refuting that
conclusion was found in L0 scope, and this file intentionally does not claim
any endpoint, source theorem, or `P ≠ NP` consequence.

Next action: open `isoStrong_conclusion_audit_D0` to classify the conclusion
side with the now-landed hardwired `hInDag` witness.

## Scope compliance

- Edited only the authorized staging Lean file and this report.
- No pnp4 files were changed.
- No `axiom`, `sorry`, `admit`, or `native_decide` was added.
- No JSONL / NoGoLog / spec / `known_guards` / trust-root file was edited.
- No `ResearchGapWitness`, `VerifiedNPDAGLowerBoundSource`, endpoint, or
  unconditional `P ≠ NP` claim was added.

RED_HINDAG_TRIVIAL_BUT_CONCLUSION_OPEN
