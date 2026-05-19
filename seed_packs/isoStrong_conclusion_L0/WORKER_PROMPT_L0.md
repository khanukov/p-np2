# Worker prompt — iso-strong conclusion L0 probe

Branch: `main` (base).  Develop on a worker branch.

Task type: **L0 Lean probe** + markdown report.  ONE Lean file
authorised at the staging path `pnp3/Tests/IsoStrongConclusionProbe.lean`,
≤ 300 LOC, plus ONE markdown report at
`seed_packs/isoStrong_conclusion_L0/reports/L0_isoStrong_conclusion_<HANDLE>.md`.

## Context

Audit chain (most recent first):

1. PR #1407 (`isoStrong_conclusion_audit_D0`, codex53):
   `INCONCLUSIVE_NEEDS_LEAN_PROBE`.  All 4 D0 worker variants
   converged on this verdict.  Markdown audit cannot decide whether
   `IsoStrongFamilyEventually F (globalWitness_to_hInDag W)` at
   canonical `sYES = 1, sNO = 2` is provable, refutable, or open.
2. PR #1404 (`global_hInDag_contract_L0`, gpt55): landed
   `pnp3/Tests/GlobalHInDagContractProbe.lean` (116 LOC) with
   `GlobalAsymptoticDAGWitness` + projection.
3. Earlier post-PR13 chain.

This L0 attempts to settle the conclusion-side question via a Lean
probe.

## Goal

Land ONE Lean file at the staging path:

```text
pnp3/Tests/IsoStrongConclusionProbe.lean
```

The file should attempt **one** of the two probe directions
(see README sections 3, 4):

- **Direction P (positive)**: `∀ W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym, IsoStrongFamilyEventually F (globalWitness_to_hInDag W)`.
- **Direction N (structural negation)**: `∀ W, ¬ IsoStrongFamilyEventually F (globalWitness_to_hInDag W)`.

**Strategic recommendation (from README section 4):** Direction N
looks more tractable structurally due to a pigeonhole argument:

- The slack inequality forces `|D| ≤ 2^m - log_2(m+2) - O(1)`,
  leaving ≥ `log_2(m+2) + 1` free value coordinates in the
  agreement subcube.
- The agreement subcube then has ≥ `m + 2 + 1 = m + 3` distinct
  partial truth tables.
- But there are only `m + 2` size-1 functions, so at most `m + 2`
  partial truth tables in the subcube are in YES.
- By pigeonhole, at least one subcube member is NOT in YES, so the
  forcing condition fails for any choice of yYes and D within the
  slack budget.

This pigeonhole argument, **if formalisable in ≤ 300 LOC**, gives
Direction N and verdict `RED_CONCLUSION_REFUTED`.

The worker MAY try Direction P first if structural intuition
suggests a positive proof, but Direction N is the recommended first
attempt.

The file must compile via `./scripts/check.sh` and must NOT modify
any other file.

## Required reading

Before writing the Lean code, read:

- `RESEARCH_CONSTITUTION.md` (Rules 0, 1, 6, 16).
- `STATUS.md`.
- `seed_packs/isoStrong_conclusion_L0/README.md` (this seed pack's
  README — section 3 has the probe target signatures; section 4 has
  the strategic guidance with pigeonhole sketch).
- `seed_packs/isoStrong_conclusion_audit_D0/reports/D0_isoStrong_conclusion_audit_codex53.md`
  (the D0 report that motivated this L0).
- `pnp3/Tests/GlobalHInDagContractProbe.lean` (the L0 #1404 contract
  surface this L0 builds on).
- `pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean:1078–1104`
  (`IsoStrongFamilyEventually`).
- `pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean:966–984`
  (`ppolyDAGSizeBoundOnSlicesEventually`).
- `pnp3/LowerBounds/AsymptoticDAGBarrierInterfaces.lean:25–104`
  (`GapSlice`, `CorrectOnPromiseSlice`, `gapSliceOfParams`,
  `GapSliceFamilyEventually`, `encodedLen`, `tableLen`).
- `pnp3/LowerBounds/MCSPGapLocality.lean:148–165`
  (`ValueCoordinateSet`, `AgreeOnValues`, `ValidEncoding`,
  `encodePartial`, `decodePartial`).
- `pnp3/Magnification/CanonicalAsymptoticTrackData.lean`
  (canonical spec, params, hAsym; `canonicalShannonBound`).
- `pnp3/Models/Model_PartialMCSP.lean`
  (especially `circuitCountBound`, `PartialTruthTable`,
  `gapPartialMCSP_Language`).

## File structure

```lean
import Complexity.Interfaces
import Models.Model_PartialMCSP
import Magnification.CanonicalAsymptoticTrackData
import Magnification.FinalResultMainline
import LowerBounds.AsymptoticDAGBarrierTheorems
import LowerBounds.AsymptoticDAGBarrierInterfaces
import LowerBounds.MCSPGapLocality
import «pnp3».Tests.GlobalHInDagContractProbe -- the L0 #1404 contract surface

namespace Pnp3
namespace Tests
namespace IsoStrongConclusionProbe

open ComplexityInterfaces
open Models
open Magnification
open LowerBounds
open GlobalHInDagContractProbe

-- Optional helper lemmas (canonical sYES = 1 + sNO = 2 facts)
-- ...

-- Direction N target (recommended first attempt):
theorem isoStrong_conclusion_negative_for_canonical :
    ∀ W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym,
      ¬ IsoStrongFamilyEventually
          (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym)
          (globalWitness_to_hInDag W) := by
  ...

-- OR Direction P target (alternative):
-- theorem isoStrong_conclusion_positive_for_canonical :
--     ∀ W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym,
--       IsoStrongFamilyEventually
--           (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym)
--           (globalWitness_to_hInDag W) := by
--   ...

end IsoStrongConclusionProbe
end Tests
end Pnp3
```

## Construction guidance for Direction N

### Pigeonhole sketch

The Direction N proof reduces to:

```text
Assume IsoStrongFamilyEventually F (globalWitness_to_hInDag W) holds.
Then ∃ β0 > 0, ∃ κ : Nat → Rat → Nat, ∃ nIso : Rat → Nat such that
  (forcing) ∀ n ≥ max F.N0 (nIso β), ∀ C correct, ∃ yYes ∈ Yes,
            ∃ D : Finset (Fin (tableLen F n β)), |D| ≤ κ n β,
            (every valid agreement extension in YES)
  AND (slack) ∀ n ≥ max F.N0 (nIso β), m+2 < 2^(2^m - κ n β).

Take any sufficiently large m ≥ max canonicalAsymptoticHAsym.N0 (nIso β),
some β in (0, β0), and any correct C (e.g., the constant DAG that
checks promise — but we don't need to construct C explicitly; we just
need the existential ∃ C, _).

  Actually for Direction N, we need to UNIVERSALLY refute the
  conclusion, which means: for every choice of β0, κ, nIso, the
  forcing-and-slack conjunction fails.

Strategy: pick specific m, β, C, then show that for ANY yYes and
ANY D with |D| ≤ κ n β (where the slack inequality holds), the
agreement subcube has size 2^(2^m - |D|) > m + 2, but YES has at most
m + 2 distinct consistency classes, so by pigeonhole at least one
agreement subcube member is not in YES.

  Need a C that exists and is correct on promise.  Use the
  hypothesis `IsoStrongFamilyEventually F hInDag`'s OWN existential
  to bring W.family into the picture: take C := W.family encodedLen,
  which has size ≤ globalPolyDAGSizeBound W (so the size bound
  holds), and decides the asymptotic language correctly (so promise-
  correctness holds via W.decides_global + hAsym.sliceEq).
```

Concretely, the proof structure is:

```lean
intro W hIso
-- Destructure: ∃ β0, κ, nIso, _
obtain ⟨β0, hβ0pos, κ, nIso, hForcing, hSlack⟩ := hIso
-- Pick concrete β, m
let β : Rat := β0 / 2  -- some value in (0, β0)
have hβpos : 0 < β := by ...
have hβlt : β < β0 := by ...
let m : Nat := max canonicalAsymptoticHAsym.N0 (nIso β)
have hm : m ≥ max F.N0 (nIso β) := le_refl _
-- Use the global family as the witness DAG C
let C : DagCircuit (encodedLen F m β) := W.family (encodedLen F m β)
have hCsize : size C ≤ (globalWitness_to_hInDag W m β).polyBound (encodedLen F m β) := ...
have hCcorrect : CorrectOnPromiseSlice C (gapSliceOfParams (F.paramsOf m β)) := ...
-- Apply forcing
obtain ⟨yYes, hyYes, hValid, D, hDcard, hForcingDetail⟩ := hForcing m β hβpos hβlt hm C hCsize hCcorrect
-- Apply slack
have hSlackDetail := hSlack m β hβpos hβlt hm
-- Pigeonhole: |agreement subcube ∩ valid encodings| > |YES ∩ agreement subcube|
-- Construct a specific z that agrees with yYes on D but is not in YES.
-- Contradicts hForcingDetail.
exact absurd hForcingDetail (...)
```

This is the structural proof shape.  Concrete details (especially
constructing the counterexample `z`) require careful work with the
`Partial.tableLen` / `partialInputLen` encoding and the
`circuitCountBound` value for canonical params.

### Pigeonhole helper lemma (likely needed)

A helper lemma that may need to be proven locally (or extracted from
mathlib) is roughly:

```lean
lemma pigeonhole_subcube_exceeds_yes :
    ∀ n ≥ canonicalAsymptoticHAsym.N0,
      ∀ |D| ≤ 2^n - log_2 (n + 2) - 1,
        (size of agreement subcube > m + 2) ∧
        (|YES ∩ subcube| ≤ m + 2)
```

Or directly: "for sufficiently large `n`, every yYes and every D
with size satisfying the slack, the agreement subcube contains at
least one valid encoding not in YES."

The cardinality `m + 2` of size-1 functions is exact for canonical
`sYES = 1`.  The slack inequality gives the precise relationship to
`|D|`.

### Falling back to YELLOW or INCONCLUSIVE

If Direction N's pigeonhole structural argument doesn't fit in
300 LOC (likely possibilities: the encoding/decoding overhead for
`Partial.tableLen ↔ partialInputLen` doubles the LOC; constructing
the counterexample `z` requires more machinery than expected), the
worker should:

1. Land **partial progress** as Lean lemmas (e.g., the
   counterexample-existence lemma without the full conclusion-
   refutation).
2. Document precisely which sub-lemmas are needed for L1.
3. Issue verdict `YELLOW_PARTIAL_LANDING` (if some Lean landed) or
   `INCONCLUSIVE_NEEDS_L1` (if nothing landed).

## Construction guidance for Direction P

If Direction N doesn't seem tractable in 300 LOC, fall back to
Direction P.  Strategy:

- Choose specific β0 (e.g., 1).
- Choose κ as a function of n that maximises the agreement subcube
  while satisfying the slack.
- Construct yYes from a specific size-1 function (e.g., const-false).
- Construct D to force the agreement subcube into YES.

**The key difficulty:** at sYES=1, the YES set has only `m + 2`
distinct consistency classes.  Forcing the entire agreement subcube
into YES requires the subcube to span at most `m + 2` partial truth
tables.  This needs |D| close to `2^m`, but then slack fails.

**Best case for Direction P:** worker finds a CONSTRUCTIVE choice
that threads the slack/forcing balance.  If structural intuition
suggests this is impossible (per the pigeonhole sketch), Direction N
is the correct target.

## Hygiene constraints

- ≤ 300 source lines (including imports, declarations, blank lines,
  comments).
- Lean kernel-checks (no `sorry`, `admit`, `native_decide`).
- No `axiom`, `opaque`.  `noncomputable def` is allowed if needed.
- No declaration names containing `Provider`, `Payload`, `Default`,
  `Source`, `Witness`, `Gap` outside the unavoidable
  `GlobalAsymptoticDAGWitness` parameter type (per the L0 #1404
  exception clause).
- No `sorry`, `admit`, `native_decide`.
- No imports of `Magnification.LocalityProvider_Partial`,
  `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`, or any
  file under `pnp3/RefutedPredicates/`.
- Audit (worker must run): `rg "FormulaCertificateProviderPartial|FormulaSupportRestrictionBoundsPartial|MagnificationAssumptions|FormulaCertificateProviderPartial_fromPipeline" pnp3/Tests/IsoStrongConclusionProbe.lean` must return no matches.

## Forbidden scope

- No edits outside the staging file and seed pack reports/failures.
- No mainline Lean edits.
- No JSONL / NoGoLog / spec / `known_guards` / trust-root edits.
- No `ResearchGapWitness`, `VerifiedNPDAGLowerBoundSource`,
  `SourceTheorem`, `gap_from`, endpoint, `P ≠ NP` claim.
- No TM-verifier session work.
- No promotion of refuted predicates.

## Verdicts

End the report with **exactly one** of:

- **`GREEN_CONCLUSION_PROVEN`** — Direction P theorem lands kernel-
  checked.  Route is formally vacuous at canonical.  Canonical track
  closes as fourth refutation pattern.
- **`RED_CONCLUSION_REFUTED`** — Direction N theorem lands kernel-
  checked.  Route is formally inconsistent at canonical.  Canonical
  track closes inconsistent.
- **`YELLOW_PARTIAL_LANDING`** — A partial Lean result lands (e.g.,
  the pigeonhole counterexample-existence lemma, or proof for fixed
  small `n` slices, or proof under an extra hypothesis), but the
  full probe theorem does not fit in 300 LOC.  Report identifies
  precise L1 sub-targets.
- **`INCONCLUSIVE_NEEDS_L1`** — No Lean theorem lands.  Report
  identifies precise blocking lemmas and infrastructure for L1
  multi-session probe.

## Commands

```sh
./scripts/check.sh
```

If `check.sh` fails for an environment reason (e.g., `lake` not
installed in the sandbox), record the exact command, exit status,
and observation in `failures/`.  Confirm the same failure
reproduces on `main` HEAD to establish non-regression.

## Required output format

End the response with:

```
Task: iso-strong conclusion L0 probe
Handle: <handle>
Branch: <branch>
Commit before: <hash>
Commit after: <hash>
Changed files:
  pnp3/Tests/IsoStrongConclusionProbe.lean (if landed; <LOC> lines)
  seed_packs/isoStrong_conclusion_L0/reports/L0_isoStrong_conclusion_<HANDLE>.md
  seed_packs/isoStrong_conclusion_L0/failures/<note>.md (if any)

Outcome:
  L0_LANDED | YELLOW_PARTIAL | INCONCLUSIVE_NEEDS_L1 | STRUCTURED_FAILURE

If L0 landed (GREEN or RED):
  staging file: pnp3/Tests/IsoStrongConclusionProbe.lean (<LOC> lines)
  executive verdict: GREEN_CONCLUSION_PROVEN | RED_CONCLUSION_REFUTED
  direction attempted: P | N | both
  ./scripts/check.sh: PASS | <observation>
  declaration names audited: <list>
  imports audited: <list>
  next action:
    if GREEN: close_canonical_track_record_fourth_refutation
    if RED: close_canonical_track_record_conclusion_inconsistent

If YELLOW_PARTIAL:
  partial Lean result: <theorem name>
  L1 sub-target: <precise theorem statement + missing infrastructure>
  ./scripts/check.sh: PASS | <observation>
  next action: open_isoStrong_conclusion_L1_multi_session

If INCONCLUSIVE_NEEDS_L1:
  blocking infrastructure: <list>
  estimated L1 LOC: <number>
  next action: open_isoStrong_conclusion_L1_multi_session

Scope violations:
  none | list
```
