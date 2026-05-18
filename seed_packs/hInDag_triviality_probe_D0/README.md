# hInDag triviality probe — D0

## 1. Status

**OPEN — D0 audit only.**

- No Lean code in the seed-pack skeleton.
- A future D0 worker may add a markdown probe report under `reports/`, or
  if the probe requires a small in-repo Lean check, a single Level-0 Lean
  file under a candidates-style staging path documented in the worker
  prompt.  **No** mainline Lean edits, **no** `SourceTheorem`,
  `ResearchGapWitness`, `gap_from`, endpoint, or `P ≠ NP` claim.

The probe is markdown-first.  Lean is allowed only if the worker can show
the entire probe outcome cannot be settled by inspection of existing
declarations.

## 2. Why this exists

The chain so far:

1. PR 13 proved `FormulaCertificateProviderPartial → False` (`Probe 13`).
2. The post-PR13 retarget D0 (`seed_packs/post_pr13_provider_retarget_D0`,
   opus47 handle) recommended `RETARGET_EXISTING_ROUTE`: replumb the
   canonical asymptotic infrastructure onto two non-refuted DAG-side
   consumers,
   - `AsymptoticIsoStrongRoute canonicalAsymptoticHAsym`
   - `AsymptoticPromiseYesCertificateRoute canonicalAsymptoticHAsym`
3. The asymptotic iso-strong / promise-YES route audit D0
   (`seed_packs/asymptotic_isostrong_route_audit_D0`, gpt55 handle)
   returned `YELLOW_ROUTE_OPEN_BUT_NEEDS_TARGETED_SELF_ATTACKS` and named
   the **single decisive next probe**:

```text
open_hInDag_triviality_probe
```

This seed pack opens that probe.

The reason it is decisive: the route hypothesis surface

```lean
hInDag : ∀ n β, InPpolyDAG (gapPartialMCSP_Language
  ((eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym).paramsOf n β))
```

is the gating premise of every retarget candidate.  If `hInDag` can be
**internally discharged** from already-landed in-repo facts (canonical
decider, `proved_P_subset_PpolyDAG_internal`, etc.), the route Prop
collapses to its conclusion alone — and the entire retarget verdict
must be re-examined.  If `hInDag` cannot be internally discharged, the
promise-YES route opens as the next Level-0 target.

## 3. Central question

Can

```lean
∀ n β, InPpolyDAG (gapPartialMCSP_Language
  ((eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym).paramsOf n β))
```

be proved in-repo on `main` (commit `72ea5e4` or later) **without**:

- introducing new mainline Lean source files,
- importing any refuted predicate
  (`FormulaCertificateProviderPartial`,
   `FormulaSupportRestrictionBoundsPartial`,
   `FormulaSupportBoundsPartial_fromPipeline`,
   `MagnificationAssumptions[_fromPipeline]`,
   `FormulaSupportBoundsFromMultiSwitchingContract`),
- assuming a hypothesis,
- changing `canonicalAsymptoticSpec`, `canonicalAsymptoticParams`,
  `canonicalAsymptoticHAsym`, or any other trust-root surface?

## 4. Attack routes the probe must address

The probe report must explicitly check or rule out each of the following
three attack routes.  All three should be attempted before issuing a
verdict.

### Route 1 — via P-membership + `proved_P_subset_PpolyDAG_internal`

Path:

```text
canonical language slice is in P
    ↪ via P_subset_PpolyStraightLine
    ↪ via P_subset_PpolyDAG_of_P_subset_PpolyStraightLine
    ↪ InPpolyDAG (gapPartialMCSP_Language (paramsOf n β))
```

Required: a theorem of the form `ComplexityInterfaces.P
(gapPartialMCSP_Language p)` for every canonical slice `p`.  The probe
must search for or rule out such a theorem in `pnp3/Complexity/`,
`pnp3/Models/`, and `pnp3/Magnification/`.

### Route 2 — via canonical decider + Cook–Levin / compilation

Path: use `Magnification.decideAsymptotic` (and `decideAsymptotic_iff`)
together with whatever P-to-PpolyDAG compiler the repo exposes, to
compile the decider on each canonical slice into a polynomial-size DAG
family.

Required: the decider must run in polynomial time on canonical input
lengths, AND the in-repo compiler must accept the decider as input.

The probe must locate the compiler entry point (likely under
`pnp3/Complexity/Simulation/Circuit_Compiler.lean` or
`pnp3/Complexity/PsubsetPpolyDAG_Internal.lean`) and check the exact
input shape required (e.g. straight-line program, Turing-machine
witness, etc.) and whether `decideAsymptotic`'s implementation already
satisfies that shape.

### Route 3 — direct algorithmic argument from `sYES=1, sNO=2`

Heuristic observation (recorded for the worker to validate or refute):

- The canonical asymptotic spec sets `sYES n = 1`, `sNO n = 2`.
- `Magnification.decideYesAt1 m T` is already defined at
  `pnp3/Magnification/CanonicalAsymptoticDecider.lean:107` and checks
  consistency of a partial truth table `T` against each of the `m + 2`
  size-1 circuit candidates (`Circuit.const false`, `Circuit.const true`,
  and `Circuit.input i` for `i : Fin m`).
- Each consistency check is `O(2^m)` bit operations on the table.
- Canonical input length at slice `m` is `N = Partial.inputLen m = 2 ·
  2^m`, so the decider's total work is `O(N · log N)`, i.e.
  **polynomial in `N`**.
- If this work can be formalised as a Lean polynomial-time bound and
  fed into the `P → PpolyDAG` compiler, the canonical asymptotic
  language is in `P` and `hInDag` is discharged.

The probe report must either (a) confirm that Routes 2 or 3 close, or
(b) identify the precise missing intermediate theorem that blocks
closure.

## 5. Possible verdicts

End the report with exactly one of:

- **`RED_HINDAG_TRIVIALLY_PROVABLE`** — at least one of the three attack
  routes yields `hInDag` from already-landed in-repo facts (with at most
  a small Level-0 Lean addition).  Consequence: the retarget verdict
  `RETARGET_EXISTING_ROUTE` from the post-PR13 D0 is invalid for the
  canonical spec; the route is vacuous at `canonicalAsymptoticHAsym`.
- **`GREEN_HINDAG_NOT_TRIVIALLY_PROVABLE`** — the report can demonstrate
  that none of the three routes closes, AND the failure mode is
  structural (not "I did not find a theorem").  Consequence: the
  promise-YES route opens as the next L0 target.
- **`YELLOW_INCONCLUSIVE`** — one or more attack routes are plausible
  but the probe cannot settle them without a Lean construction beyond
  D0 scope.  Consequence: escalate to a Level-0 Lean probe.
- **`INCONCLUSIVE_NEEDS_LEAN`** — the markdown probe cannot answer the
  central question; a small (≤ 200 LOC) Level-0 Lean file is required.
  The report must include the exact theorem statement that the L0 file
  would prove and the file path it would land at (under
  `pnp3/Tests/HInDagTrivialityProbe.lean` or a similar staging path
  outside the mainline closure).

A `YELLOW_INCONCLUSIVE` or `INCONCLUSIVE_NEEDS_LEAN` verdict is **not**
a failure mode for D0 — it is a valid outcome that triggers a follow-up
work item.  A `RED` verdict triggers a structural re-audit of the
post-PR13 retarget.  A `GREEN` verdict triggers the promise-YES L0 probe.

## 6. Audit targets

Read-only context that the probe must inspect:

- `pnp3/Magnification/CanonicalAsymptoticTrackData.lean`
  (canonical spec, params, hAsym)
- `pnp3/Magnification/CanonicalAsymptoticDecider.lean`
  (decider, `decideYesAt1`, `findCanonicalSlice`, components bridge)
- `pnp3/Complexity/PsubsetPpolyDAG_Internal.lean`
  (`P_subset_PpolyDAG_of_P_subset_PpolyStraightLine`)
- `pnp3/Complexity/Simulation/Circuit_Compiler.lean`
  (`proved_P_subset_PpolyDAG_internal`, ~line 602)
- `pnp3/Models/Model_PartialMCSP.lean`
  (definition of `gapPartialMCSP_Language`,
   `eventualGapSliceFamily_of_asymptotic`)
- `pnp3/Magnification/FinalResultMainline.lean`
  (definitions of `AsymptoticIsoStrongRoute`,
   `AsymptoticPromiseYesCertificateRoute`, ~lines 218–282)

## 7. Forbidden scope

- No mainline Lean source edits.  No edits to files under
  `pnp3/Magnification/`, `pnp3/LowerBounds/`, `pnp3/Complexity/`,
  `pnp3/Models/`, `pnp3/ThirdPartyFacts/`, `pnp3/Spec/`, `pnp3/Tests/`
  (except the staging path for an `INCONCLUSIVE_NEEDS_LEAN` follow-up),
  or `pnp4/`.
- No JSONL / NoGoLog / spec / known_guards / trust-root edits.
- No `ResearchGapWitness`, `SourceTheorem`, `gap_from`, endpoint, or
  `P ≠ NP` claim.
- No TM-verifier session work.
- No promotion of refuted predicates.

## 8. Allowed scope

Only:

- `seed_packs/hInDag_triviality_probe_D0/README.md`
- `seed_packs/hInDag_triviality_probe_D0/WORKER_PROMPT_D0.md`
- `seed_packs/hInDag_triviality_probe_D0/reports/D0_hindag_triviality_<HANDLE>.md`
- `seed_packs/hInDag_triviality_probe_D0/failures/<note>.md`
- (only on an `INCONCLUSIVE_NEEDS_LEAN` verdict) one Lean file at a
  staging path explicitly named in the report.
