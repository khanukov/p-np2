# Global hInDag contract L0

## 1. Status

**OPEN — L0 Lean probe.**

This is **not** a markdown-only seed pack.  L0 authorises ONE Lean file at
the staging path `pnp3/Tests/GlobalHInDagContractProbe.lean`, ≤ 250 LOC,
under the hygiene constraints in WORKER section 6.

No mainline Lean edits.  No `SourceTheorem`, `ResearchGapWitness`,
`gap_from`, endpoint, or `P ≠ NP` claim.  No trust-root edits.

## 2. Why this exists

The chain so far:

1. PR 13 / Probe 13: `FormulaCertificateProviderPartial → False`.
2. `seed_packs/post_pr13_provider_retarget_D0` (opus47):
   `RETARGET_EXISTING_ROUTE`.
3. `seed_packs/asymptotic_isostrong_route_audit_D0` (gpt55, PR #1378):
   `YELLOW`.
4. `seed_packs/hInDag_triviality_probe_D0` (gpt55, PR #1383):
   `YELLOW_INCONCLUSIVE`.
5. `seed_packs/hInDag_triviality_probe_L0` (gpt55, PR #1388):
   **`RED_HINDAG_TRIVIAL_BUT_CONCLUSION_OPEN`**.  Landed
   `pnp3/Tests/HInDagTrivialityProbe.lean` (121 LOC) showing the
   `∀ hInDag, ...` quantification in canonical asymptotic routes is
   satisfied by truth-table DAG hardwiring at fixed slice.  The
   `polyBound : Nat → Nat` clause of `InPpolyDAG` allows slice-local
   constants `K_p`, so per-slice hardwiring is admissible.
6. `seed_packs/global_hInDag_contract_repair_D0` (codex53, PR #1396):
   **`REPAIR_POSSIBLE_WITH_GLOBAL_WITNESS`**.  Proposed
   `GlobalAsymptoticDAGWitness` structure carrying a single family
   `family : Nat → DagCircuit` with a shared polynomial bound
   `(coeff, exponent)` across all input lengths.  This closes the
   hardwiring loophole because the slice-local constants `K_p` from
   the L0-A witness do not exhibit a single uniform `(coeff, exponent)`.

This seed pack opens the L0 follow-up to PR #1396:
**`global_hInDag_contract_L0`**.  The task is to land the proposed
contract as a kernel-checked Lean construction at the staging path.

## 3. The four required pieces

The L0 staging file must define (in order):

### Piece A — `GlobalAsymptoticDAGWitness` structure (~50 LOC)

```lean
structure GlobalAsymptoticDAGWitness
    (hAsym : AsymptoticFormulaTrackHypothesis) where
  family : ∀ N : Nat, DagCircuit N
  coeff : Nat
  exponent : Nat
  size_bound : ∀ N : Nat,
    DagCircuit.size (family N) ≤ coeff * N ^ exponent + coeff
  decides_global :
    ∀ N : Nat, ∀ x : Bitstring N,
      DagCircuit.eval (family N) x =
        Models.gapPartialMCSP_AsymptoticLanguage hAsym.spec N x
```

The single global polynomial `q(N) = coeff · N^exponent + coeff` bounds
`size (family N)` for every input length `N`.  The `decides_global`
clause says the family computes the global asymptotic language at
every input length.

### Piece B — `globalPolyDAGSizeBound` size-bound predicate (~20 LOC)

```lean
def globalPolyDAGSizeBound
    {hAsym : AsymptoticFormulaTrackHypothesis}
    (W : GlobalAsymptoticDAGWitness hAsym) :
    Nat → Rat → Rat → Nat → Prop :=
  fun n β _ε s =>
    s ≤ W.coeff * ((eventualGapSliceFamily_of_asymptotic hAsym).encodedLen n β) ^ W.exponent + W.coeff
```

This is the **global** size-bound predicate (polynomial in the slice's
encoded input length) that replaces the per-slice
`ppolyDAGSizeBoundOnSlicesEventually F hInDag` (which is the per-slice
`hInDag`'s `polyBound` evaluated at `encodedLen`).

### Piece C — `AsymptoticPromiseYesWeakRouteEventually_global` Prop (~30 LOC)

```lean
def AsymptoticPromiseYesWeakRouteEventually_global
    (hAsym : AsymptoticFormulaTrackHypothesis) : Prop :=
  ∀ W : GlobalAsymptoticDAGWitness hAsym,
    ∃ ε β0 : Rat, 0 < ε ∧ 0 < β0 ∧
      ∀ β : Rat, 0 < β → β < β0 →
        ∃ n0 : Nat,
          (eventualGapSliceFamily_of_asymptotic hAsym).N0 ≤ n0 ∧
            ∀ n ≥ n0,
              LowerBounds.SmallDAGImpliesPromiseYesSubcubeAtEventually
                (eventualGapSliceFamily_of_asymptotic hAsym)
                (globalPolyDAGSizeBound W)
                n β ε
```

This mirrors the existing
`Magnification.AsymptoticPromiseYesWeakRouteEventually`
(at `pnp3/Magnification/FinalResultMainline.lean:265–282`) but the
size-bound predicate fed to `SmallDAGImpliesPromiseYesSubcubeAtEventually`
is the **global** polynomial bound (Piece B), not the per-slice
`ppolyDAGSizeBoundOnSlicesEventually F hInDag`.

### Piece D — forward projection (~80–100 LOC)

```lean
def globalWitness_to_hInDag
    {hAsym : AsymptoticFormulaTrackHypothesis}
    (W : GlobalAsymptoticDAGWitness hAsym) :
    ∀ n β,
      InPpolyDAG
        (Models.gapPartialMCSP_Language
          ((eventualGapSliceFamily_of_asymptotic hAsym).paramsOf n β))
```

For each slice `(n, β)`, this constructs an `InPpolyDAG` witness by:

- Selecting the global family's circuit at the slice's encoded length:
  `family m := if m = encodedLen then W.family encodedLen else constFalseDag m`.
- The polynomial bound is constant at the active length and `2`
  elsewhere — `polyBound_poly` trivially holds with `c` chosen large
  enough.
- Correctness uses `hAsym.sliceEq` to convert the global asymptotic
  language at the active length into the per-slice language, then
  applies `W.decides_global`.

This projection demonstrates the **forward** relationship to the
original `hInDag` framework.  Note: this projection **collapses**
the global polynomial bound (it discards the global `q(N)` and uses
a slice-local constant for `polyBound`).  This is expected and
explains why the route refactor (Piece C) is necessary — the
projected `hInDag` would re-enter the hardwiring regime if used
directly.

## 4. Anti-hardwiring observation (record, not required to prove in L0)

Under the existing hardwired witness
`hInDag_for_canonicalAsymptoticHAsym` (in
`pnp3/Tests/HInDagTrivialityProbe.lean`), the per-slice `polyBound`
returns the truth-table-DAG size at canonical length
`N = 2 · 2^m`, which is roughly `2^N · N` (the DNF size).  This is
**doubly-exponential** in the slice index `m`, hence not polynomial
in `N` with any fixed exponent.

Therefore: no `GlobalAsymptoticDAGWitness` whose `family` matches
the hardwired `ttDag` at canonical lengths satisfies `size_bound`.

The L0 report MAY include a sketch of this observation but is not
required to prove it formally in Lean.  Formalising
`2^N > coeff · N^exponent + coeff` for all sufficiently large `N`
is bounded arithmetic (Nat / Polynomial.degree lemmas) and is
expected to add 80–120 LOC if attempted.

## 5. Verdicts

End the L0 report with **exactly one** of:

- **`RED_GLOBAL_CONTRACT_FULLY_LANDED`** — Pieces A, B, C, D all land
  kernel-checked, plus the anti-hardwiring sketch is formalised as a
  Lean lemma.  This is the maximum L0 deliverable.
- **`RED_GLOBAL_CONTRACT_CORE_LANDED`** — Pieces A, B, C, D land but
  anti-hardwiring is left as a documented sketch (not formalised).
  This is the **expected** outcome for ≤ 250 LOC budget.
- **`YELLOW_PARTIAL_LANDING`** — Pieces A, B, C land but Piece D
  (forward projection) does not fit in 250 LOC (the dependent
  `if h : m = encodedLen` cast may require more infrastructure than
  expected).  Next: L1 multi-session.
- **`INCONCLUSIVE_NEEDS_FULL_SESSION`** — even Pieces A–C don't fit
  in 250 LOC.  No Lean file landed.  Next: L1 multi-session probe.

## 6. Audit targets

Read-only context the worker must inspect:

- `pnp3/Tests/HInDagTrivialityProbe.lean` — the existing L0 file the
  current L0 builds on top of (DO NOT IMPORT — see hygiene below).
- `pnp3/Magnification/CanonicalAsymptoticTrackData.lean` —
  `canonicalAsymptoticSpec`, `canonicalAsymptoticParams`,
  `canonicalAsymptoticHAsym`.
- `pnp3/Magnification/FinalResultMainline.lean:42–53`
  (`AsymptoticFormulaTrackHypothesis` definition).
- `pnp3/Magnification/FinalResultMainline.lean:173–195`
  (`eventualGapSliceFamily_of_asymptotic` definition).
- `pnp3/Magnification/FinalResultMainline.lean:265–282`
  (`AsymptoticPromiseYesWeakRouteEventually` — the route to mirror).
- `pnp3/LowerBounds/AsymptoticDAGBarrierInterfaces.lean:70–104`
  (`GapSliceFamilyEventually`, `encodedLen`, `tableLen`).
- `pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean:966–984`
  (`ppolyDAGSizeBoundOnSlicesEventually`,
  `SmallDAGImpliesPromiseYesSubcubeAtEventually`).
- `pnp3/Models/Model_PartialMCSP.lean` —
  `gapPartialMCSP_Language`, `gapPartialMCSP_AsymptoticLanguage`,
  `Partial.inputLen`.
- `pnp3/Complexity/Interfaces.lean:187–250, 435–446` — `DagCircuit`,
  `DagCircuit.size`, `DagCircuit.eval`, `InPpolyDAG`.

The seed-pack README of PR #1396 — `seed_packs/global_hInDag_contract_repair_D0/reports/D0_global_hInDag_contract_repair_codex53.md` — is also part of required reading.

## 7. Forbidden scope

- No edits outside `pnp3/Tests/GlobalHInDagContractProbe.lean`,
  `seed_packs/global_hInDag_contract_L0/reports/`, and `failures/`.
- No mainline Lean edits.
- No edits to `pnp3/RefutedPredicates/`, `pnp3/Magnification/`,
  `pnp3/LowerBounds/`, `pnp3/Complexity/`, `pnp3/Models/`,
  `pnp3/ThirdPartyFacts/`, `pnp3/Spec/`, or `pnp4/`.
- **No imports of** `Magnification.LocalityProvider_Partial`,
  `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`,
  `pnp3/Tests/HInDagTrivialityProbe.lean` (the existing L0 — this one
  is a fresh staging file), or any file under
  `pnp3/RefutedPredicates/`.
- No `axiom`, `opaque` (unless using `Classical.choice` on a strictly
  bounded existential, justified in docstring), `Fact`, `Provider`,
  `Payload`, `Default`, `Source`, `Witness`, `Gap` in declaration names
  (per RESEARCH_CONSTITUTION Rule 16).
- No `sorry`, `admit`, `native_decide`.
- No JSONL / NoGoLog / spec / `known_guards` / trust-root edits.
- No `ResearchGapWitness`, `VerifiedNPDAGLowerBoundSource`,
  `SourceTheorem`, `gap_from`, endpoint, `P ≠ NP` claim.
- No TM-verifier session work.
- No promotion of refuted predicates.

## 8. Allowed scope

- ONE Lean file at `pnp3/Tests/GlobalHInDagContractProbe.lean`,
  ≤ 250 LOC.
- ONE markdown report at
  `seed_packs/global_hInDag_contract_L0/reports/L0_global_contract_<HANDLE>.md`.
- Optional failure notes under
  `seed_packs/global_hInDag_contract_L0/failures/`.
