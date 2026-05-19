# Worker prompt — global hInDag contract L0

Branch: `main` (base).  Develop on a worker branch.

Task type: **L0 Lean probe** + markdown report.  ONE Lean file authorised
at the staging path `pnp3/Tests/GlobalHInDagContractProbe.lean`, ≤ 250
LOC, plus ONE markdown report at
`seed_packs/global_hInDag_contract_L0/reports/L0_global_contract_<HANDLE>.md`.

## Context

The audit chain:

1. PR 13 refutation: `FormulaCertificateProviderPartial → False`.
2. Post-PR13 retarget D0 (opus47): `RETARGET_EXISTING_ROUTE`.
3. Asymptotic iso-strong audit D0 (gpt55, PR #1378): `YELLOW`.
4. hInDag triviality D0 (gpt55, PR #1383): `YELLOW_INCONCLUSIVE`.
5. hInDag triviality L0 (gpt55, PR #1388): **`RED_HINDAG_TRIVIAL_BUT_CONCLUSION_OPEN`**.
   Landed `pnp3/Tests/HInDagTrivialityProbe.lean` showing per-slice
   truth-table DAG hardwiring satisfies the `∀ hInDag, ...` quantifier.
6. Global hInDag contract repair D0 (codex53, PR #1396):
   **`REPAIR_POSSIBLE_WITH_GLOBAL_WITNESS`**.  Proposed the
   `GlobalAsymptoticDAGWitness` structure with a single shared
   polynomial bound `(coeff, exponent)` across all input lengths.

This L0 task lands the proposed contract as a kernel-checked Lean
construction.

## Goal

Land ONE Lean file at the staging path:

```text
pnp3/Tests/GlobalHInDagContractProbe.lean
```

The file must define four pieces (in order):

- **Piece A**: `GlobalAsymptoticDAGWitness` structure.
- **Piece B**: `globalPolyDAGSizeBound` size-bound predicate.
- **Piece C**: `AsymptoticPromiseYesWeakRouteEventually_global` Prop.
- **Piece D**: `globalWitness_to_hInDag` forward projection.

The file must compile via `./scripts/check.sh` and must NOT modify any
other file.

## Required reading

Read these files before writing the Lean code.  Do not edit them.

- `RESEARCH_CONSTITUTION.md` (Rules 0, 1, 6, 16).
- `STATUS.md`.
- `seed_packs/global_hInDag_contract_L0/README.md` (this seed pack's
  README; required reading, especially sections 3–5).
- `seed_packs/global_hInDag_contract_repair_D0/reports/D0_global_hInDag_contract_repair_codex53.md`
  (the D0 proposal this L0 implements).
- `pnp3/Magnification/CanonicalAsymptoticTrackData.lean`
  (`canonicalAsymptoticSpec`, `canonicalAsymptoticParams`,
  `canonicalAsymptoticHAsym`).
- `pnp3/Magnification/FinalResultMainline.lean:42–53`
  (`AsymptoticFormulaTrackHypothesis`).
- `pnp3/Magnification/FinalResultMainline.lean:173–195`
  (`eventualGapSliceFamily_of_asymptotic`).
- `pnp3/Magnification/FinalResultMainline.lean:265–282`
  (`AsymptoticPromiseYesWeakRouteEventually` — the route to mirror).
- `pnp3/LowerBounds/AsymptoticDAGBarrierInterfaces.lean:70–104`
  (`GapSliceFamilyEventually` structure, `encodedLen`, `tableLen`).
- `pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean:966–984`
  (`ppolyDAGSizeBoundOnSlicesEventually` (Phase III size-bound
  predicate signature), `SmallDAGImpliesPromiseYesSubcubeAtEventually`).
- `pnp3/Models/Model_PartialMCSP.lean`
  (`gapPartialMCSP_Language`, `gapPartialMCSP_AsymptoticLanguage`,
  `Partial.inputLen`).
- `pnp3/Complexity/Interfaces.lean:187–250` (`DagCircuit`, `DagGate`,
  `DagWire`, `DagCircuit.size`, `DagCircuit.eval`).
- `pnp3/Complexity/Interfaces.lean:435–446` (`InPpolyDAG` structure).

## File structure

```lean
import Complexity.Interfaces
import Models.Model_PartialMCSP
import Magnification.CanonicalAsymptoticTrackData
import Magnification.FinalResultMainline
import LowerBounds.AsymptoticDAGBarrierTheorems

namespace Pnp3
namespace Tests
namespace GlobalHInDagContractProbe

open ComplexityInterfaces
open Models
open Magnification
open LowerBounds

noncomputable section

-- Local constFalseDag (do NOT import HInDagTrivialityProbe; this is
-- a fresh staging file).
private def constFalseDag (n : Nat) : DagCircuit n where
  gates := 1
  gate := fun _ => .const false
  output := .gate ⟨0, Nat.lt.base 0⟩

private theorem constFalseDag_size {n : Nat} :
    DagCircuit.size (constFalseDag n) = 2 := by
  simp [constFalseDag, DagCircuit.size]

private theorem constFalseDag_eval {n : Nat} (x : Bitstring n) :
    DagCircuit.eval (constFalseDag n) x = false := by
  simp [constFalseDag, DagCircuit.eval, DagCircuit.eval.evalGateAt]

-- =============== Piece A ===============

/-- The global polynomial-size DAG family contract for the asymptotic
language.  See `seed_packs/global_hInDag_contract_L0/README.md`
section 3.A for design rationale. -/
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

-- =============== Piece B ===============

/-- Global polynomial size-bound predicate derived from a
`GlobalAsymptoticDAGWitness`.  Replaces the per-slice
`ppolyDAGSizeBoundOnSlicesEventually F hInDag`. -/
def globalPolyDAGSizeBound
    {hAsym : AsymptoticFormulaTrackHypothesis}
    (W : GlobalAsymptoticDAGWitness hAsym) :
    Nat → Rat → Rat → Nat → Prop :=
  fun n β _ε s =>
    s ≤ W.coeff *
      ((eventualGapSliceFamily_of_asymptotic hAsym).encodedLen n β) ^ W.exponent
      + W.coeff

-- =============== Piece C ===============

/-- Global version of `AsymptoticPromiseYesWeakRouteEventually`. -/
def AsymptoticPromiseYesWeakRouteEventually_global
    (hAsym : AsymptoticFormulaTrackHypothesis) : Prop :=
  ∀ W : GlobalAsymptoticDAGWitness hAsym,
    ∃ ε β0 : Rat, 0 < ε ∧ 0 < β0 ∧
      ∀ β : Rat, 0 < β → β < β0 →
        ∃ n0 : Nat,
          (eventualGapSliceFamily_of_asymptotic hAsym).N0 ≤ n0 ∧
            ∀ n ≥ n0,
              SmallDAGImpliesPromiseYesSubcubeAtEventually
                (eventualGapSliceFamily_of_asymptotic hAsym)
                (globalPolyDAGSizeBound W)
                n β ε

-- =============== Piece D ===============

/-- Forward projection from the global witness to per-slice `hInDag`. -/
def globalWitness_to_hInDag
    {hAsym : AsymptoticFormulaTrackHypothesis}
    (W : GlobalAsymptoticDAGWitness hAsym)
    (n : Nat) (β : Rat) :
    InPpolyDAG
      (Models.gapPartialMCSP_Language
        ((eventualGapSliceFamily_of_asymptotic hAsym).paramsOf n β)) := by
  ...

end

end GlobalHInDagContractProbe
end Tests
end Pnp3
```

## Construction guidance

### Piece A

Straightforward structure declaration.  Use the field order shown
above so callers can pattern-match cleanly.

### Piece B

A definition, no proof required.  The `_ε` argument is intentionally
ignored — it matches the signature of `ppolyDAGSizeBoundOnSlicesEventually`
(Phase III size-bound predicates have shape `Nat → Rat → Rat → Nat → Prop`).

### Piece C

Mirror the existing `AsymptoticPromiseYesWeakRouteEventually` Prop at
`FinalResultMainline.lean:265–282`.  Only one substitution: replace the
`∀ hInDag, ...` outer quantifier with `∀ W : GlobalAsymptoticDAGWitness hAsym,
...`, and replace `ppolyDAGSizeBoundOnSlicesEventually F hInDag` with
`globalPolyDAGSizeBound W`.  The rest of the Prop body is identical.

### Piece D — the forward projection

This is the largest piece (estimated 80–120 LOC).

For a slice `(n, β)`, construct an `InPpolyDAG L` witness where
`L = gapPartialMCSP_Language ((eventualGapSliceFamily_of_asymptotic hAsym).paramsOf n β)`.

Strategy:

- Let `p := (eventualGapSliceFamily_of_asymptotic hAsym).paramsOf n β`.
- Let `activeLen := Models.partialInputLen p`.  (Note:
  `encodedLen F n β = partialInputLen ((paramsOf F n β))`, so `activeLen =
  (eventualGapSliceFamily_of_asymptotic hAsym).encodedLen n β`.)
- `gapPartialMCSP_Language p` is false for input length `m ≠ activeLen`
  and equals the per-slice predicate at `m = activeLen`.
- Use the global family's circuit at `activeLen` for the active length;
  use `constFalseDag` elsewhere.

Concrete shape:

```lean
refine
  { polyBound := fun m =>
      if m = activeLen then DagCircuit.size (W.family activeLen) else 2
    polyBound_poly := ?_
    family := fun m =>
      if h : m = activeLen then h ▸ W.family activeLen else constFalseDag m
    family_size_le := ?_
    correct := ?_ }
```

For `polyBound_poly`: provide `c := DagCircuit.size (W.family activeLen) + 2`.
At `m = activeLen`, `polyBound m = size (...) ≤ c ≤ m^c + c`.  At
`m ≠ activeLen`, `polyBound m = 2 ≤ c ≤ m^c + c`.

For `family_size_le`: case-split on `m = activeLen`.  Active case: by
`rfl`-style computation.  Inactive case: `constFalseDag_size` gives
size 2 ≤ 2.

For `correct`: case-split on `m = activeLen`.

- Active case (`m = activeLen`): after `subst`, the goal is
  `DagCircuit.eval (W.family activeLen) x = gapPartialMCSP_Language p activeLen x`.
  Use `W.decides_global activeLen x` to rewrite the LHS to
  `gapPartialMCSP_AsymptoticLanguage hAsym.spec activeLen x`.  Then
  use `hAsym.sliceEq (pAt_n p)` ... or more directly: at canonical
  asymptotic lengths the asymptotic language equals the per-slice
  language.  See `hAsym.sliceEq` field of `AsymptoticFormulaTrackHypothesis`.
  Hint: there is a theorem `Magnification.eventual_coherence_at` and
  related slice-equality lemmas in `Magnification/FinalResultMainline.lean`
  and `Models/Model_PartialMCSP.lean` that align the two languages at
  canonical length.
- Inactive case (`m ≠ activeLen`): `eval (constFalseDag m) x = false`.
  Off-slice, `gapPartialMCSP_Language p m x = false`.  The latter is via
  `dif_neg` on the `partialInputLen` test inside
  `gapPartialMCSP_Language`'s definition.

If the correctness proof in the active case is too involved (e.g.,
requires careful `hAsym.sliceEq` orchestration that doesn't fit), the
worker MAY simplify Piece D to a specialised case that only covers
the canonical instantiation (i.e., `hAsym = canonicalAsymptoticHAsym`):

```lean
def globalWitness_to_hInDag_canonical
    (W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym)
    (n : Nat) (β : Rat) :
    InPpolyDAG
      (Models.gapPartialMCSP_Language
        ((eventualGapSliceFamily_of_asymptotic
            canonicalAsymptoticHAsym).paramsOf n β)) := ...
```

Specialisation to canonical is acceptable for L0 — the general
`globalWitness_to_hInDag` form can land in a follow-up if the
canonical case alone fits the budget.

## Hygiene constraints

- ≤ 250 source lines (including imports, declarations, blank lines, comments).
- Lean kernel-checks (no `sorry`, `admit`, `native_decide`).
- No `axiom`, `opaque`.  `noncomputable def` is allowed (the
  `InPpolyDAG` structure is Type-valued; `globalWitness_to_hInDag` will
  necessarily be a `def`, likely `noncomputable` because it inspects
  `DagCircuit.size` of a generic global family).  Document the
  noncomputability in the docstring.
- No declaration names containing `Provider`, `Payload`, `Default`,
  `Source`, `Witness`, `Gap` outside the structure name
  `GlobalAsymptoticDAGWitness` (which is the contract-repair proposal
  from PR #1396 and is unavoidable for this task).  The
  `GlobalAsymptoticDAGWitness` name is allowed as a one-time exception
  documented here; do NOT introduce additional `*Witness*` declarations.
- No imports of:
  - `Magnification.LocalityProvider_Partial`
  - `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`
  - `pnp3/Tests/HInDagTrivialityProbe.lean` (the existing L0; this is
    a fresh staging file)
  - any file under `pnp3/RefutedPredicates/`.
- Audit (worker must run): `rg "FormulaCertificateProviderPartial|FormulaSupportRestrictionBoundsPartial|MagnificationAssumptions|FormulaCertificateProviderPartial_fromPipeline" pnp3/Tests/GlobalHInDagContractProbe.lean` must return no matches.

## Forbidden scope

- No edits outside `pnp3/Tests/GlobalHInDagContractProbe.lean` and the
  seed pack's `reports/` + `failures/` directories.
- No mainline Lean edits.
- No JSONL / NoGoLog / spec / `known_guards` / trust-root edits.
- No `ResearchGapWitness`, `VerifiedNPDAGLowerBoundSource`,
  `SourceTheorem`, `gap_from`, endpoint, `P ≠ NP` claim.
- No TM-verifier session work.
- No promotion of refuted predicates.

## Verdicts

End the report with exactly one of:

- **`RED_GLOBAL_CONTRACT_FULLY_LANDED`** — All four pieces land
  kernel-checked plus the anti-hardwiring lemma (sketch from the L0
  README section 4) is formalised in Lean as
  `no_global_witness_matches_hardwired_ttDag` or equivalent.  Likely
  > 250 LOC; if achieved, expect L0 budget extension to ~350 LOC.
- **`RED_GLOBAL_CONTRACT_CORE_LANDED`** — Pieces A, B, C, D land,
  with Piece D specialised to canonical instantiation if necessary.
  Anti-hardwiring lemma deferred.  Expected primary outcome.
- **`YELLOW_PARTIAL_LANDING`** — Pieces A, B, C land but Piece D does
  not fit in 250 LOC.  Next: L1 multi-session to complete projection.
- **`INCONCLUSIVE_NEEDS_FULL_SESSION`** — Pieces A–C don't fit.  No
  Lean file landed.  Next: L1 multi-session probe.

## Commands

```sh
./scripts/check.sh
```

If `check.sh` fails for an environment reason (e.g., `lake` not
installed in the sandbox), record the exact command, exit status, and
observation in `failures/`.  Confirm the same failure reproduces on
`main` HEAD to establish non-regression.

## Required output format

End the response with:

```
Task: global hInDag contract L0
Handle: <handle>
Branch: <branch>
Commit before: <hash>
Commit after: <hash>
Changed files:
  pnp3/Tests/GlobalHInDagContractProbe.lean (if landed; <LOC> lines)
  seed_packs/global_hInDag_contract_L0/reports/L0_global_contract_<HANDLE>.md
  seed_packs/global_hInDag_contract_L0/failures/<note>.md (if any)

Outcome:
  L0_LANDED | INCONCLUSIVE_NEEDS_FULL_SESSION | STRUCTURED_FAILURE

If L0 landed:
  staging file: pnp3/Tests/GlobalHInDagContractProbe.lean (<LOC> lines)
  executive verdict: RED_GLOBAL_CONTRACT_FULLY_LANDED |
                     RED_GLOBAL_CONTRACT_CORE_LANDED |
                     YELLOW_PARTIAL_LANDING
  pieces landed: A | A,B | A,B,C | A,B,C,D | A,B,C,D + anti-hardwiring
  Piece D form: general | canonical-specialised
  ./scripts/check.sh: PASS | <observation>
  declaration names audited: <list>
  imports audited: <list>
  next action:
    if FULLY_LANDED: open_isoStrong_route_global_refactor_L0
    if CORE_LANDED: open_anti_hardwiring_lemma_L1 OR
                    open_isoStrong_route_global_refactor_L0
    if PARTIAL: open_global_contract_L1_complete_projection

If INCONCLUSIVE_NEEDS_FULL_SESSION:
  blocking infrastructure: <list>
  estimated LOC: <number>
  next action: open_global_contract_L1_multi_session

Scope violations:
  none | list
```
