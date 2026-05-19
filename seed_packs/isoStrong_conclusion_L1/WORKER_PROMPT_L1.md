# Worker prompt — iso-strong conclusion L1 multi-session probe

Branch: `main` (base).  Develop on a worker branch.

Task type: **L1 multi-session Lean probe**.  Extend the existing
staging file `pnp3/Tests/IsoStrongConclusionProbe.lean` (currently 80
LOC from L0 #1413) with the **pigeonhole bridge** for Direction N.

Total combined file budget: ≤ 500 LOC.  Multi-session work is
allowed: worker may submit partial progress (1 or 2 of 3 sub-lemmas)
with precise handoff for follow-up sessions.

## Context

The audit chain has 7 stages closed (PR 13 + 6 D0/L0 in post-PR13
chain).  This L1 is the 8th stage and the final formal step for the
canonical asymptotic track.

L0 #1413 (squashed as `806a5e0`) landed:

- `F_Mof : F.Mof n (F.Tof n 0) = n + 2` — concrete numeric fact.
- `canonical_isoStrong_implies_eventual_strict_slack` — slack
  inequality extraction.

All 4 L0 worker variants converged on `YELLOW_PARTIAL_LANDING` and
identified the same blocker: the **constructive pigeonhole
z-construction**.  This L1 formalises that bridge.

## Goal

**Extend** the existing file `pnp3/Tests/IsoStrongConclusionProbe.lean`
with the L1 sub-lemmas and main theorem.  Do not create a new file.
Do not delete or modify the existing L0 content.

Target combined file structure:

```lean
-- Existing L0 content (do not modify):
import ...
namespace Pnp3.Tests.IsoStrongConclusionProbe
open ...
private def F : GapSliceFamilyEventually := ...
@[simp] lemma F_Mof ...
theorem canonical_isoStrong_implies_eventual_strict_slack ...

-- ---- L1 EXTENSION STARTS HERE ----

-- Sub-lemma 1: agreement subcube cardinality lower bound.
theorem agreement_subcube_cardinality_lower_bound
    (p : GapPartialMCSPParams)
    (yYes : Bitstring (partialInputLen p))
    (hValidYes : ValidEncoding p yYes)
    (D : Finset (Fin (Partial.tableLen p.n))) :
    -- TODO: exact statement form
    ... := by
  ...

-- Sub-lemma 2: canonical YES class count upper bound at sYES=1.
theorem canonical_yes_class_count_upper_bound_sYES1
    (p : GapPartialMCSPParams) (hp : p.sYES = 1) :
    -- TODO: exact statement form
    ... := by
  ...

-- Sub-lemma 3: pigeonhole conclusion.
theorem exists_valid_agreeing_not_yes_under_slack
    (p : GapPartialMCSPParams) (hp : p.sYES = 1)
    (yYes : Bitstring (partialInputLen p))
    (hValidYes : ValidEncoding p yYes)
    (D : Finset (Fin (Partial.tableLen p.n)))
    (hSlack : p.n + 2 < 2 ^ (Partial.tableLen p.n - D.card)) :
    ∃ z : Bitstring (partialInputLen p),
      ValidEncoding p z ∧
      AgreeOnValues D yYes z ∧
      ¬ (z ∈ (gapSliceOfParams p).Yes) := by
  ...

-- Main theorem: structural negation of iso-strong at canonical.
theorem isoStrong_conclusion_negative_for_canonical :
    ∀ W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym,
      ¬ IsoStrongFamilyEventually
          (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym)
          (globalWitness_to_hInDag W) := by
  ...
```

The file must compile via `./scripts/check.sh` and must NOT modify
any other file.

## Required reading

Before writing Lean, read:

- `RESEARCH_CONSTITUTION.md` (Rules 0, 1, 6, 16).
- `STATUS.md`.
- `seed_packs/isoStrong_conclusion_L1/README.md` (this seed pack's
  README — sections 3, 4, 5 are essential).
- `seed_packs/isoStrong_conclusion_L0/reports/L0_isoStrong_conclusion_codex.md`
  (L0 report identifying the 3 L1 sub-targets).
- `pnp3/Tests/IsoStrongConclusionProbe.lean` (the L0 file to extend).
- `pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean:1078–1104`
  (`IsoStrongFamilyEventually` definition).
- `pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean:966–984`
  (`ppolyDAGSizeBoundOnSlicesEventually`).
- `pnp3/LowerBounds/AsymptoticDAGBarrierInterfaces.lean:25–104`
  (slice structures).
- `pnp3/LowerBounds/MCSPGapLocality.lean:140–200`
  (`ValueCoordinateSet`, `AgreeOnValues`, `ValidEncoding`,
  `encodePartial`, `decodePartial`, `Partial.valPart`,
  `Partial.maskPart`).
- `pnp3/Models/Model_PartialMCSP.lean`
  (`gapPartialMCSP_Language`, `PartialTruthTable`, `circuitCountBound`).
- `pnp3/Magnification/CanonicalAsymptoticDecider.lean` (especially
  `size1Candidates m` and the enumeration of size-1 functions).
- `pnp3/Tests/GlobalHInDagContractProbe.lean` (the global contract
  with `globalWitness_to_hInDag`).

## Construction guidance

### Sub-lemma 1 strategy

Construct an injection from `Bool ^ (Fin.complement D)` into the set
of valid encodings agreeing with `yYes` on `D`:

- For each function `f : Fin.complement D → Bool`, build `z` by:
  - Setting `Partial.valPart z i = yYes.valPart i` for `i ∈ D`.
  - Setting `Partial.valPart z i = f i` for `i ∈ Fin.complement D`.
  - Setting `Partial.maskPart z` to make the encoding canonical
    (apply `encodePartial ∘ decodePartial` to canonicalise).

The image is exactly the agreement subcube intersected with valid
encodings.  Cardinality of domain: `2^(tableLen - D.card)`.

**Caveat about masks:** the encoding has mask + value halves.
`AgreeOnValues` only constrains value coordinates at positions in
`D`.  Mask coordinates at all positions are free in agreement.  But
`ValidEncoding` constrains the relationship between mask and value:
in canonical form, position `i` has `(mask = 0 → value = 0)` and
`(mask = 1 → value = either)`.  This means:

- At position `i ∈ D` with `yYes.maskPart i = 1`: `z.valPart i =
  yYes.valPart i` (forced by agreement).  `z.maskPart i = 1` (forced
  by ValidEncoding if `z.valPart i ≠ 0`).
- At position `i ∉ D`: `z.valPart i, z.maskPart i` can vary subject
  to ValidEncoding constraints.

The L1 worker should choose a clean injection that respects these
constraints.  Easiest: fix `z.maskPart = yYes.maskPart` everywhere
(so mask is same as yYes), and vary `z.valPart` only at positions
where `yYes.maskPart i = 1` and `i ∉ D`.

Actually simpler: vary mask AND value together at positions `i ∉ D`.
For each `i ∉ D`, either `(mask, value) = (0, 0)` (unset) or `(1, 0)`
or `(1, 1)` — 3 choices per position.  This gives `3^(tableLen -
D.card) ≥ 2^(tableLen - D.card)` distinct valid encodings.

Either choice works for the cardinality lower bound.  The worker
should pick whichever is easiest to prove injective.

### Sub-lemma 2 strategy

The set of size-1 circuits on `p.n` inputs is exactly:

```lean
Magnification.size1Candidates p.n =
  Circuit.const false :: Circuit.const true ::
    (List.finRange p.n).map Circuit.input
```

This is a list of length `p.n + 2`.  Each size-1 circuit determines
a Boolean function `f : Bitstring p.n → Bool`.

A partial truth table T is YES iff `∃ C ∈ size1Candidates p.n,
is_consistent C T` (or equivalent).  So the YES set can be
partitioned into at most `p.n + 2` consistency classes (one per
size-1 candidate).

The L1 worker should formalize "YES is contained in the union of
`p.n + 2` consistency classes", and conclude that the count of
distinct partial truth tables in YES is ≤ `(number of partial tables
consistent with at least one size-1 function)`.

A more useful form for sub-lemma 3: "for any sequence of partial
truth tables in YES of length > `p.n + 2`, two of them share the
same consistent size-1 function".

Or yet another: "the set of partial-truth-table-encodings z that
agree with some yYes on D AND lie in YES has cardinality bounded by
`p.n + 2` × (partial tables per consistency class)".

The exact statement depends on the proof path for sub-lemma 3.

### Sub-lemma 3 strategy

Standard pigeonhole:

- Domain: the agreement subcube (≥ `2^(tableLen - D.card)` valid
  encodings by sub-lemma 1).
- Codomain: the YES set (≤ `p.n + 2` distinct partial tables by
  sub-lemma 2 — modulo what "distinct" means for valid encodings).
- Slack: `p.n + 2 < 2^(tableLen - D.card)` (from L0).
- Pigeonhole: at least one domain element maps to "not in YES"
  (else the YES class count would exceed the slack bound).

The worker can use `Finset.card_lt_card` or `Finset.exists_of_card_lt`
type lemmas from mathlib.

### Main theorem assembly

Given the 3 sub-lemmas, the main theorem follows by:

```lean
theorem isoStrong_conclusion_negative_for_canonical :
    ∀ W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym,
      ¬ IsoStrongFamilyEventually F (globalWitness_to_hInDag W) := by
  intro W hIso
  -- Step 1: Extract slack from hIso via L0 helper.
  rcases canonical_isoStrong_implies_eventual_strict_slack W hIso with
    ⟨β0, hβ0, κ, nIso, hSlack⟩
  -- Step 2: Pick concrete (m, β).
  let β : Rat := β0 / 2
  have hβPos : 0 < β := ...
  have hβLt : β < β0 := ...
  let m : Nat := max canonicalAsymptoticHAsym.N0 (nIso β)
  have hm : m ≥ max F.N0 (nIso β) := le_refl _
  -- Step 3: Get slack inequality at (m, β).
  have hSlackm := hSlack m β hβPos hβLt hm
  -- Step 4: Apply forcing (need to also extract the forcing branch
  -- from hIso; use a fresh destructure or a separate L0 helper).
  rcases hIso with ⟨_β0', _hβ0', _κ', _nIso', hForce, _hSlack'⟩
  -- Step 5: Pick C = W.family encodedLen as the witness DAG.
  ...
  -- Step 6: Apply hForce at (m, β, C) to get yYes, D.
  obtain ⟨yYes, hyYes, hValid, D, hDCard, hAllYes⟩ := hForce ...
  -- Step 7: Apply exists_valid_agreeing_not_yes_under_slack to get
  -- a counterexample z.
  obtain ⟨z, hzValid, hzAgree, hzNotYes⟩ :=
    exists_valid_agreeing_not_yes_under_slack ... hSlackm
  -- Step 8: Contradiction: hAllYes z hzValid hzAgree gives z ∈ Yes,
  -- but hzNotYes says z ∉ Yes.
  exact hzNotYes (hAllYes z hzValid hzAgree)
```

## Hygiene constraints

- ≤ 500 source lines (total combined file, including the 80 LOC L0).
- Lean kernel-checks (no `sorry`, `admit`, `native_decide`).
- No `axiom`, `opaque` (unless using `Classical.choice` on a
  strictly bounded existential, justified in docstring).
- No declaration names containing `Provider`, `Payload`, `Default`,
  `Source`, `Witness`, `Gap` outside the `GlobalAsymptoticDAGWitness`
  parameter type.
- No imports beyond what L0 already has, plus:
  - mathlib `Finset.card` / pigeonhole lemmas (e.g.,
    `Mathlib.Data.Finset.Card`)
  - `Mathlib.Combinatorics.Pigeonhole` if needed.
- Audit (worker must run): `rg "FormulaCertificateProviderPartial|FormulaSupportRestrictionBoundsPartial|MagnificationAssumptions|FormulaCertificateProviderPartial_fromPipeline" pnp3/Tests/IsoStrongConclusionProbe.lean` must return no matches.

## Multi-session option

If the worker estimates that completing all 3 sub-lemmas + main
theorem requires > 500 LOC, they MAY:

1. **Land partial progress**: 1 or 2 sub-lemmas only.
2. **Document handoff**: precise theorem statements for the
   remaining sub-lemmas + estimated LOC + which mathlib helpers are
   needed.
3. **Issue verdict** `YELLOW_TWO_OF_THREE_LANDED` or
   `YELLOW_ONE_OF_THREE_LANDED`.

Subsequent L1 sessions (separate dispatches) can pick up where the
previous one left off, extending the same staging file.

## Forbidden scope

- No edits outside the staging file and seed pack reports/failures.
- No mainline Lean edits.
- No JSONL / NoGoLog / spec / `known_guards` / trust-root edits.
- No `ResearchGapWitness`, `VerifiedNPDAGLowerBoundSource`,
  `SourceTheorem`, `gap_from`, endpoint, `P ≠ NP` claim.
- No TM-verifier session work.
- No promotion of refuted predicates.

## Verdicts

End the L1 report with **exactly one** of:

- **`RED_CONCLUSION_REFUTED`** — full Direction N theorem
  (`isoStrong_conclusion_negative_for_canonical`) lands.  Route is
  formally inconsistent at canonical.  Canonical track closes
  inconsistent (fourth major refutation in the chain).
- **`YELLOW_TWO_OF_THREE_LANDED`** — two of the three sub-lemmas
  land; precise blocker identified for the third sub-lemma and
  main theorem.
- **`YELLOW_ONE_OF_THREE_LANDED`** — exactly one sub-lemma lands;
  precise sub-targets for the remaining two.
- **`INCONCLUSIVE_NEEDS_L2`** — pigeonhole structure does not compose
  in expected way; structural obstruction identified.

## Commands

```sh
./scripts/check.sh
```

If `check.sh` fails for an environment reason, record in `failures/`.

## Required output format

End the response with:

```
Task: iso-strong conclusion L1 probe
Handle: <handle>
Branch: <branch>
Session: <1 of multi | 2 of multi | full L1>
Commit before: <hash>
Commit after: <hash>
Changed files:
  pnp3/Tests/IsoStrongConclusionProbe.lean (extended; <new LOC>/<total LOC> lines)
  seed_packs/isoStrong_conclusion_L1/reports/L1_isoStrong_conclusion_<HANDLE>.md
  seed_packs/isoStrong_conclusion_L1/failures/<note>.md (if any)

Outcome:
  L1_LANDED | YELLOW_PARTIAL | INCONCLUSIVE_NEEDS_L2 | STRUCTURED_FAILURE

If L1 landed (RED):
  staging file: pnp3/Tests/IsoStrongConclusionProbe.lean (<total LOC> lines)
  executive verdict: RED_CONCLUSION_REFUTED
  sub-lemmas landed: 1, 2, 3, main
  ./scripts/check.sh: PASS | <observation>
  declaration names audited: <list>
  imports audited: <list>
  next action: close_canonical_track_record_conclusion_inconsistent

If YELLOW_TWO_OF_THREE_LANDED:
  sub-lemmas landed: <which 2>
  remaining: <which 1>
  L2 sub-target: <precise theorem statement + LOC estimate>
  next action: open_isoStrong_conclusion_L1_session_2

If YELLOW_ONE_OF_THREE_LANDED:
  sub-lemma landed: <which 1>
  remaining: <which 2>
  L2 sub-targets: <precise statements + LOC estimates>
  next action: open_isoStrong_conclusion_L1_session_2

If INCONCLUSIVE_NEEDS_L2:
  structural obstruction: <description>
  recommended L2 approach: <e.g., port mathlib lemmas; refactor encoding>
  next action: open_isoStrong_conclusion_L2_design

Scope violations:
  none | list
```
