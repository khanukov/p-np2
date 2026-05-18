# L0 hInDag triviality probe report

Handle: gpt55
Branch observed: `work` (user task base: `main`)
Commit before: `dea89ac9dbed4fdca8635f5aafdb6388049b9bad`

## Classification

Infrastructure / audit probe.  This does not reduce `SearchMCSPWeakLowerBound`
or `VerifiedNPDAGLowerBoundSource`; it kernel-checks whether the canonical
`hInDag` premise is hardwire-trivial at each fixed slice.

## Lean artifact landed

Staging file:

- `pnp3/Tests/HInDagTrivialityProbe.lean`

Line count:

- 166 lines (`wc -l pnp3/Tests/HInDagTrivialityProbe.lean`)

## Construction summary

The file defines a local `constFalseDag` and proves its evaluation theorem.  It
then builds a truth-table tree circuit by recursion on input length, compiles it
through the existing internal tree-to-straight-line compiler, and translates the
straight-line circuit to the canonical `DagCircuit` syntax through the existing
straight-line/DAG adapter.  The key local correctness lemma is:

```lean
private theorem ttDag_eval {n : Nat} (f : Bitstring n → Bool) (x : Bitstring n) :
    DagCircuit.eval (ttDag f) x = f x
```

Using this, the file defines the fixed-slice hardwiring witness:

```lean
def fixedSlice_gapPartialMCSP_in_PpolyDAG
    (p : GapPartialMCSPParams) :
    InPpolyDAG (gapPartialMCSP_Language p)
```

The family uses the truth-table DAG at `partialInputLen p` and local
`constFalseDag` away from that slice; the off-slice language proof unfolds
`gapPartialMCSP_Language` and uses the `dif_neg` branch.

Finally, the canonical route premise is discharged pointwise:

```lean
def hInDag_for_canonicalAsymptoticHAsym :
    ∀ n β,
      InPpolyDAG
        (gapPartialMCSP_Language
          ((eventualGapSliceFamily_of_asymptotic
              canonicalAsymptoticHAsym).paramsOf n β))
```

This shows that the `hInDag` premise at the canonical asymptotic instantiation
is not a substantive obstruction: every fixed slice has a non-uniform DAG
truth-table hardwiring.

## Conclusion-side classification

The L0 Lean file proves the hInDag premise is trivially available by fixed-slice
truth-table hardwiring.  I did not find or add a Lean proof that the downstream
iso-strong / promise-YES conclusion is itself trivial, nor a Lean refutation of
that conclusion.  That conclusion-side question remains outside what this L0
file settles.

Executive verdict:

`RED_HINDAG_TRIVIAL_BUT_CONCLUSION_OPEN`

Next action:

`open_isoStrong_conclusion_audit_D0`

## Hygiene audit

Declaration names audited:

- `constFalseDag`
- `constFalseDag_eval`
- `treeRename`
- `treeRename_eval`
- `ttTree`
- `ttTree_eval`
- `ttDag`
- `ttDag_eval`
- `dag_size_pos`
- `fixedSlice_gapPartialMCSP_in_PpolyDAG`
- `hInDag_for_canonicalAsymptoticHAsym`

Imports audited:

- `Complexity.Interfaces`
- `Models.Model_PartialMCSP`
- `Magnification.CanonicalAsymptoticTrackData`
- `Complexity.PsubsetPpolyInternal.TreeToStraight`
- `Complexity.PsubsetPpolyInternal.StraightLineSemantics`
- `Mathlib.Tactic`

Forbidden/refuted-predicate scan:

```sh
rg -n "FormulaCertificateProviderPartial|FormulaSupportRestrictionBoundsPartial|MagnificationAssumptions" pnp3/Tests/HInDagTrivialityProbe.lean
```

Result: no matches.

Hole/native/axiom scan:

```sh
rg -n "\b(axiom|opaque|sorry|admit|native_decide)\b|noncomputable def" pnp3/Tests/HInDagTrivialityProbe.lean
```

Result: no matches.

## Commands run

```sh
lake env lean pnp3/Tests/HInDagTrivialityProbe.lean
```

Result: PASS.

```sh
./scripts/check.sh
```

Result: FAIL at governance step 12.e due to coordinator HTTP concurrency reset,
after the full Lean build completed successfully.  A structured note was written
at:

- `seed_packs/hInDag_triviality_probe_L0/failures/check_sh_connection_reset_gpt55.md`

## Scope

Changed files:

- `pnp3/Tests/HInDagTrivialityProbe.lean`
- `seed_packs/hInDag_triviality_probe_L0/reports/L0_hindag_triviality_gpt55.md`
- `seed_packs/hInDag_triviality_probe_L0/failures/check_sh_connection_reset_gpt55.md`

No spec, JSONL, NoGoLog, trust-root, `known_guards`, endpoint, or TM-verifier
session file was edited.

RED_HINDAG_TRIVIAL_BUT_CONCLUSION_OPEN
