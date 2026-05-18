# L0 hInDag triviality probe — gpt55

## Progress classification

Infrastructure / audit probe.  This file proves an upper-bound/triviality
premise for a downstream route.  It does **not** reduce
`VerifiedNPDAGLowerBoundSource` or `SearchMCSPWeakLowerBound`, and it is not
reported as P-vs-NP mainline progress.

## Landed artifact

Landed Lean staging file:

- `pnp3/Tests/HInDagTrivialityProbe.lean` (159 LOC)

The staging file imports the requested interfaces plus
`Complexity.PsubsetPpolyInternal.TreeToStraight`.  The extra import is used only
as a proof-producing authoring adapter from tree Boolean circuits to the
canonical `DagCircuit` interface; it avoids importing refuted-predicate tests.

## Lean result

The probe constructs:

- local `constFalseDag` for non-active lengths;
- local truth-table tree circuits `ttTree` with correctness lemma
  `ttTree_eval`;
- local DAG hardwiring `ttDag`, obtained through the existing transparent
  straight-line-to-DAG adapter, with correctness lemma `ttDag_eval`;
- `fixedSlice_gapPartialMCSP_in_PpolyDAG`, a per-slice `InPpolyDAG` witness for
  every `gapPartialMCSP_Language p`;
- `hInDag_for_canonicalAsymptoticHAsym`, the canonical route hypothesis surface.

Lean surface note: `InPpolyDAG L` is a structure in `Type`, not a proposition,
so Lean requires these two exported inhabitants to be `def` declarations rather
than `theorem` declarations.  The semantic content is the requested closed
inhabitant of the structure.

Noncomputability note: `ttDag` goes through the repository's existing
`compileTree`, which is marked `noncomputable`, and the fixed-slice witness
mentions the existing noncomputable `gapPartialMCSP_Language`.  No `axiom`,
`sorry`, `admit`, `opaque`, or `native_decide` is introduced.

## Audits performed

Commands run:

```sh
lake env lean pnp3/Tests/HInDagTrivialityProbe.lean
rg "FormulaCertificateProviderPartial|FormulaSupportRestrictionBoundsPartial|MagnificationAssumptions" pnp3/Tests/HInDagTrivialityProbe.lean
rg -n "\b(axiom|sorry|admit|native_decide|opaque)\b" pnp3/Tests/HInDagTrivialityProbe.lean
./scripts/check.sh
```

The forbidden refuted-predicate surface audit returned no matches.  The local
forbidden-keyword scan returned no `axiom`, `sorry`, `admit`, `native_decide`,
or `opaque` declarations.

`./scripts/check.sh` was run twice.  Both runs passed the full Lean build and
governance checks through Step 12.d, then failed at Step 12.e with a coordinator
HTTP parallel-result `ConnectionResetError: [Errno 104] Connection reset by
peer`; the observation is recorded in
`seed_packs/hInDag_triviality_probe_L0/failures/check_coordinator_reset.md`.

## Conclusion-side status

The landed hInDag premise is now trivial by fixed-slice hardwiring.  L0 did not
settle the separate conclusion-side question for
`IsoStrongFamilyEventually`/promise-YES certificates under that hardwired
premise.  That conclusion-side question remains research-open within this L0
scope.

Recommended next action: `open_isoStrong_conclusion_audit_D0`.

RED_HINDAG_TRIVIAL_BUT_CONCLUSION_OPEN
