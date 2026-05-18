# Worker prompt — hInDag triviality probe L0

Branch: `main` (base).  Develop on a worker branch.

Task type: **L0 Lean probe** + markdown report.  ONE Lean file
authorised at the staging path `pnp3/Tests/HInDagTrivialityProbe.lean`,
≤ 200 LOC, plus ONE markdown report at
`seed_packs/hInDag_triviality_probe_L0/reports/L0_hindag_triviality_<HANDLE>.md`.

## Context

This task is the L0 follow-up to the D0 chain:

- PR 13 / Probe 13: `FormulaCertificateProviderPartial → False`.
- `seed_packs/post_pr13_provider_retarget_D0` (opus47): `RETARGET_EXISTING_ROUTE`.
- `seed_packs/asymptotic_isostrong_route_audit_D0` (gpt55): `YELLOW`,
  next = `open_hInDag_triviality_probe`.
- `seed_packs/hInDag_triviality_probe_D0` (gpt55): `YELLOW_INCONCLUSIVE`,
  next = **`open_hInDag_triviality_probe_L0`** (this task).

The D0 audit established that no markdown-only argument can settle the
question.  The blocking construction is either `canonicalAsymptotic_in_P`
(via the multi-session TM-verifier plan, out of L0 scope) **or** a direct
DAG truth-table hardwiring at fixed slice (the L0-A route, ≤ 200 LOC).

This L0 task attempts the L0-A route.

## Goal

Land ONE Lean file:

```
pnp3/Tests/HInDagTrivialityProbe.lean
```

with the structure:

```lean
import Complexity.Interfaces
import Models.Model_PartialMCSP
import Magnification.CanonicalAsymptoticTrackData
-- (optional) import Magnification.CanonicalAsymptoticDecider

namespace Pnp3
namespace Tests
namespace HInDagTrivialityProbe

open ComplexityInterfaces
open Models
open Magnification

-- A small local constFalseDag (cannot import the private one from
-- AsymptoticDAGBarrierTheorems).
private def constFalseDag (n : Nat) : DagCircuit n := { ... }

-- A truth-table DAG construction for a fixed input length.  This is
-- the DAG analogue of ttFormula from
-- pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean:130 — DO NOT
-- import that file (it carries refuted-predicate imports).
private def ttDag : ∀ {n : Nat}, (Bitstring n → Bool) → DagCircuit n := ...
private theorem ttDag_eval : ∀ {n : Nat} (f : Bitstring n → Bool) (x : Bitstring n),
    DagCircuit.eval (ttDag f) x = f x := ...

-- Per-slice InPpolyDAG witness for gapPartialMCSP_Language p.
theorem fixedSlice_gapPartialMCSP_in_PpolyDAG
    (p : GapPartialMCSPParams) :
    InPpolyDAG (gapPartialMCSP_Language p) := ...

-- The route hypothesis surface at canonical instantiation.
theorem hInDag_for_canonicalAsymptoticHAsym :
    ∀ n β,
      InPpolyDAG
        (gapPartialMCSP_Language
          ((eventualGapSliceFamily_of_asymptotic
              canonicalAsymptoticHAsym).paramsOf n β)) := by
  intro n β
  exact fixedSlice_gapPartialMCSP_in_PpolyDAG _

end HInDagTrivialityProbe
end Tests
end Pnp3
```

The file must compile with `./scripts/check.sh` and must NOT modify any
other file.

## Required reading

- `RESEARCH_CONSTITUTION.md` (Rule 1, Rule 16, Rule 6 in particular).
- `STATUS.md`.
- `seed_packs/hInDag_triviality_probe_L0/README.md` (this seed pack's README).
- `seed_packs/hInDag_triviality_probe_D0/reports/D0_hindag_triviality_gpt55.md`
  (the D0 audit that authorised this L0 task).
- `pnp3/Magnification/CanonicalAsymptoticTrackData.lean`
  (`canonicalAsymptoticSpec`, `canonicalAsymptoticParams`,
  `canonicalAsymptoticHAsym`).
- `pnp3/Models/Model_PartialMCSP.lean`
  (`gapPartialMCSP_Language`, `Partial.inputLen`, `Partial.tableLen`,
  `eventualGapSliceFamily_of_asymptotic`).
- `pnp3/Complexity/Interfaces.lean:187–448`
  (`DagCircuit`, `DagGate`, `DagWire`, `DagCircuit.eval`,
  `DagCircuit.size`, `InPpolyDAG` structure).
- `pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean:1399–1411`
  (`constFalseDag` reference implementation — re-implement locally,
  do not import).
- `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean:107–220`
  (`ttFormula` recursive construction — read as TEMPLATE ONLY; do NOT
  import this file).
- `pnp3/Magnification/FinalResultMainline.lean:218–282` (the three
  route definitions that consume `hInDag`).

## Construction guidance

### `constFalseDag`

```lean
private def constFalseDag (n : Nat) : DagCircuit n where
  gates := 1
  gate := fun _ => .const false
  output := .gate ⟨0, Nat.lt.base 0⟩
```

`size (constFalseDag n) = 2`, `eval (constFalseDag n) x = false` for
all `x`.

### `ttDag`

The recommended construction is DNF over the truth table.  For
`f : Bitstring n → Bool`, build:

```
ttDag f := OR_{x : Bitstring n, f x = true}
             (AND_{i : Fin n}
                (if x i then DagCircuit.input i else NOT (input i)))
```

Size: `O(2^n · n)`.  For fixed `n`, this is a fixed constant.

Alternative construction (more elegant, similar to `ttFormula`):
recursive split on the first input bit.  At `n = 0`: `f : Bitstring 0
→ Bool` is essentially a single Bool; if `f .empty = true`, return
`DagCircuit.const true`, else `constFalseDag 0`.  At `n + 1`: split
`f` into `f_false` and `f_true` (on `x 0 = false` and `x 0 = true`),
recursively build `D_false := ttDag f_false` and `D_true := ttDag f_true`,
then combine via `OR(AND(NOT (input 0), D_false_renamed),
AND(input 0, D_true_renamed))`.  This requires a `DagCircuit.rename`
helper that injects `Fin n → Fin (n+1)`.

Pick whichever fits in 200 LOC and admits a clean eval-correctness proof.

### `fixedSlice_gapPartialMCSP_in_PpolyDAG`

The witness:

```lean
{ polyBound := fun m => if m = partialInputLen p
                          then DagCircuit.size (ttDag (gapPartialMCSP_Language p (partialInputLen p)))
                          else 2
, polyBound_poly := ⟨K_p, by intro m; by_cases h : m = partialInputLen p; · simp [h]; · ...⟩
, family := fun m => if h : m = partialInputLen p
                       then h ▸ ttDag (gapPartialMCSP_Language p (partialInputLen p))
                       else constFalseDag m
, family_size_le := ...
, correct := ...
}
```

The `correct` proof has two cases:

1. `m = partialInputLen p`: use `ttDag_eval` after the type-cast through
   `h ▸ ...`.
2. `m ≠ partialInputLen p`: `eval (constFalseDag m) x = false` and
   `gapPartialMCSP_Language p m x = false` (off-slice).

The off-slice false-fact is already in
`pnp3/Models/Model_PartialMCSP.lean`; locate it via `rg "dif_neg.*partialInputLen"`
or `rg "gapPartialMCSP_Language.*false"`.

### `hInDag_for_canonicalAsymptoticHAsym`

One-liner:

```lean
theorem hInDag_for_canonicalAsymptoticHAsym :
    ∀ n β,
      InPpolyDAG (gapPartialMCSP_Language
        ((eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym).paramsOf n β)) :=
  fun n β => fixedSlice_gapPartialMCSP_in_PpolyDAG _
```

## Hygiene constraints

- ≤ 200 source lines (including imports, declarations, blank lines, comments).
- Lean kernel-checks (no `sorry`, `admit`, `native_decide`).
- Allowed forbidden-keyword-free declaration names — see Forbidden scope.
- No imports of:
  - `Magnification.LocalityProvider_Partial`
  - `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`
  - any file under `pnp3/RefutedPredicates/`
  - any other refuted-predicate carrier.
- Audit: `rg "FormulaCertificateProviderPartial|FormulaSupportRestrictionBoundsPartial|MagnificationAssumptions" pnp3/Tests/HInDagTrivialityProbe.lean` must return no matches.

## Forbidden scope

- No edits to any file outside `pnp3/Tests/HInDagTrivialityProbe.lean`
  and the seed-pack report/failure paths.
- No `axiom`, `opaque`, `Fact`, `Provider`, `Payload`, `Default`,
  `Source`, `Witness`, `Gap` in any declaration name.
- No `noncomputable def` unless using `Classical.choice` on a
  strictly bounded existential, with explicit justification in the
  docstring.
- No `sorry`, `admit`, `native_decide`.
- No JSONL / NoGoLog / spec / `known_guards` / trust-root edits.
- No `ResearchGapWitness`, `VerifiedNPDAGLowerBoundSource`,
  `SourceTheorem`, `gap_from`, endpoint, `P ≠ NP` claim.
- No TM-verifier session work.
- No edits to `RESEARCH_CONSTITUTION.md` or `STATUS.md`.

## Verdict mapping

End the report with exactly one of:

- **`RED_HINDAG_TRIVIAL_AND_CONCLUSION_TRIVIAL`** — `hInDag_for_canonicalAsymptoticHAsym`
  lands, AND the worker shows the iso-strong / promise-YES conclusion
  under the hardwired `hInDag` is itself dischargeable (small Lean
  argument or structural triviality).  The route is fully vacuous.
- **`RED_HINDAG_TRIVIAL_AND_CONCLUSION_REFUTED`** — Lands AND the
  worker shows the conclusion under hardwired `hInDag` is provably
  false (e.g., via a counterexample DAG with no YES-isolating
  certificate).  The route is inconsistent at canonical instantiation
  and must be closed.
- **`RED_HINDAG_TRIVIAL_BUT_CONCLUSION_OPEN`** — Lands.  The hInDag
  premise is trivially provable, but the conclusion under hardwired
  hInDag is research-open.  This is the **expected** outcome based on
  the D0 caveat audit (see seed-pack README section 4).
- **`GREEN_HINDAG_TRIVIAL_CONCLUSION_NEEDS_NEW_PROBE`** — Lands, but
  the worker cannot classify the conclusion-side question in L0 scope.
  Next: open a new audit for `IsoStrongFamilyEventually` under
  hardwired hInDag.
- **`INCONCLUSIVE_NEEDS_FULL_SESSION`** — `hInDag_for_canonicalAsymptoticHAsym`
  does not fit in 200 LOC, or substantive infrastructure (DAG rename,
  recursive eval proofs) is required.  No Lean file is landed.  Next:
  L1 multi-session probe.

## Commands

```sh
./scripts/check.sh
```

If `check.sh` fails for an environment reason (e.g. `lake` not
installed), record the exact command, exit code, and observation in
the seed pack's `failures/` directory.

## Required output format

End the response with:

```
Task: hInDag triviality probe L0
Handle: <handle>
Branch: <branch>
Commit before: <hash>
Commit after: <hash>
Changed files:
  pnp3/Tests/HInDagTrivialityProbe.lean (if landed)
  seed_packs/hInDag_triviality_probe_L0/reports/L0_hindag_triviality_<HANDLE>.md
  seed_packs/hInDag_triviality_probe_L0/failures/<note>.md (if any)

Outcome:
  L0_LANDED | INCONCLUSIVE_NEEDS_FULL_SESSION | STRUCTURED_FAILURE

If L0 landed:
  staging file: pnp3/Tests/HInDagTrivialityProbe.lean (<LOC> lines)
  executive verdict: RED_HINDAG_TRIVIAL_AND_CONCLUSION_TRIVIAL |
                     RED_HINDAG_TRIVIAL_AND_CONCLUSION_REFUTED |
                     RED_HINDAG_TRIVIAL_BUT_CONCLUSION_OPEN |
                     GREEN_HINDAG_TRIVIAL_CONCLUSION_NEEDS_NEW_PROBE
  ./scripts/check.sh: PASS | <observation>
  declaration names audited: <list>
  imports audited: <list>
  next action:
    if RED_CONCLUSION_TRIVIAL: close_canonical_route
    if RED_CONCLUSION_REFUTED: update post_pr13_retarget verdict to DESIGN_NEW_PROVIDER
    if RED_CONCLUSION_OPEN: open_isoStrong_conclusion_audit_D0
    if GREEN: open_isoStrong_conclusion_audit_D0

If INCONCLUSIVE_NEEDS_FULL_SESSION:
  blocking infrastructure: <list>
  estimated LOC: <number>
  next action: open_hindag_triviality_L1_multi_session

Scope violations:
  none | list
```
