# Iso-strong conclusion L1 multi-session probe

## 1. Status

**OPEN — L1 multi-session Lean probe.**

This is NOT a single-session L0.  L1 authorises **extending** the
existing staging file `pnp3/Tests/IsoStrongConclusionProbe.lean`
(currently 80 LOC from L0 #1413) with the **pigeonhole bridge**
that completes Direction N's structural refutation.

Total budget: ≤ 500 LOC for the combined L0 + L1 staging file
(approximately 420 LOC of new content on top of the 80 LOC L0
landing).  Worker may also submit **partial multi-session work** —
landing 1 or 2 of the 3 sub-lemmas in this session and deferring the
rest, with precise handoff notes for follow-up sessions.

No mainline Lean edits.  No trust-root edits.  No `SourceTheorem`,
`ResearchGapWitness`, `gap_from`, endpoint, or `P ≠ NP` claim.

## 2. Why this exists

The audit chain (most recent first):

1. PR #1413 (`isoStrong_conclusion_L0`, codex):
   `YELLOW_PARTIAL_LANDING`.  All 4 L0 worker variants converged on
   this verdict.  Landed `pnp3/Tests/IsoStrongConclusionProbe.lean`
   (80 LOC) with:
   - `F_Mof : F.Mof n (F.Tof n 0) = n + 2` (concrete numeric fact)
   - `canonical_isoStrong_implies_eventual_strict_slack` (slack
     inequality extraction)
   - 3 named L1 sub-target placeholders:
     - `agreement_subcube_cardinality_lower_bound`
     - `canonical_yes_class_count_upper_bound_sYES1`
     - `exists_valid_agreeing_not_yes_under_slack`
2. PR #1407 (`isoStrong_conclusion_audit_D0`): `INCONCLUSIVE_NEEDS_LEAN_PROBE`.
3. Earlier post-PR13 chain (7 D0/L0 stages).

All 4 L0 worker variants identified the same blocker: the
**constructive pigeonhole z-construction** from `ValidEncoding`,
`D`, and strict slack to a valid encoding agreeing with yYes on D
but lying outside YES.  This L1 task formalises that bridge.

## 3. The L1 target

**Primary target theorem** (extending the L0 staging file):

```lean
theorem isoStrong_conclusion_negative_for_canonical :
    ∀ W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym,
      ¬ IsoStrongFamilyEventually
          (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym)
          (globalWitness_to_hInDag W)
```

**Strategy** (per L0 #1413 report and #1412 complementary work):
prove via the 3-step pigeonhole bridge specified below.

### Sub-lemma 1 — agreement subcube cardinality lower bound

```lean
theorem agreement_subcube_cardinality_lower_bound
    (p : GapPartialMCSPParams)
    (yYes : Bitstring (partialInputLen p))
    (hValidYes : ValidEncoding p yYes)
    (D : Finset (Fin (Partial.tableLen p.n))) :
    -- The set {z : ValidEncoding p z ∧ AgreeOnValues D yYes z}
    -- has cardinality at least 2^(Partial.tableLen p.n - D.card).
    ...
```

Intuition: valid encodings agreeing with `yYes` on positions in `D`
are determined by the value choices at the `tableLen - |D|` positions
outside `D`.  Each free position gives 2 choices, so the agreement
subcube has at least `2^(tableLen - |D|)` distinct valid encodings.

Caveat: the actual statement may need to also account for mask
positions (the encoding has mask + value halves).  The worker
should examine `encodePartial`, `decodePartial`, `Partial.valPart`,
`Partial.maskPart` carefully.

Estimated LOC: 100–150.

### Sub-lemma 2 — canonical YES class count upper bound at sYES=1

```lean
theorem canonical_yes_class_count_upper_bound_sYES1
    (p : GapPartialMCSPParams) (hp : p.sYES = 1) :
    -- The number of distinct partial truth tables in (gapSliceOfParams p).Yes
    -- is at most p.n + 2.
    Finset.card ... ≤ p.n + 2
```

Intuition: at `sYES = 1`, YES instances are partial truth tables
consistent with some size-1 circuit.  Size-1 Boolean functions on
`p.n` inputs are exactly: `const false`, `const true`, and
`Circuit.input i` for `i : Fin p.n`.  Total: `p.n + 2`.

Caveat: the actual statement should bound the number of YES
CONSISTENCY CLASSES (each class can have many partial encodings;
the relevant cardinality is the count of size-1 functions that
extend to valid YES inputs).

Estimated LOC: 100–150.

### Sub-lemma 3 — pigeonhole conclusion

```lean
theorem exists_valid_agreeing_not_yes_under_slack
    (p : GapPartialMCSPParams) (hp : p.sYES = 1)
    (yYes : Bitstring (partialInputLen p))
    (hValidYes : ValidEncoding p yYes)
    (D : Finset (Fin (Partial.tableLen p.n)))
    (hSlack : p.n + 2 < 2 ^ (Partial.tableLen p.n - D.card)) :
    ∃ z : Bitstring (partialInputLen p),
      ValidEncoding p z ∧
      AgreeOnValues D yYes z ∧
      ¬ (z ∈ (gapSliceOfParams p).Yes)
```

Intuition: combine sub-lemmas 1 and 2 via pigeonhole.  Agreement
subcube has ≥ `2^(tableLen - |D|)` valid encodings.  YES ∩ subcube
has ≤ `p.n + 2` consistency classes.  Slack gives `p.n + 2 <
2^(tableLen - |D|)`, so by pigeonhole at least one valid encoding
in the subcube is not in YES.

Estimated LOC: 80–120.

### Main theorem assembly

Given the 3 sub-lemmas, the main theorem
`isoStrong_conclusion_negative_for_canonical` follows by:

1. Take any `W` and assume `hIso : IsoStrongFamilyEventually F (globalWitness_to_hInDag W)`.
2. Extract `β0, κ, nIso, hForce, hSlack` from `hIso` via
   `canonical_isoStrong_implies_eventual_strict_slack` (L0).
3. Pick concrete `m` ≥ `max F.N0 (nIso β)` and `β` ∈ (0, β0).
4. Use `W.family encodedLen` as the witness `C` (sized polynomially
   via `W.size_bound`, correct on promise via `W.decides_global` +
   `hAsym.sliceEq`).
5. Apply `hForce` at `(m, β, C)` to get `yYes, hyYes, hValid, D,
   hDCard`.
6. Apply `exists_valid_agreeing_not_yes_under_slack` to construct
   `z` violating the forcing condition.
7. Contradiction.

Estimated LOC: 50–80.

**Total L1 budget:** ~330–500 LOC of new content on top of the 80
LOC L0 file.

## 4. Multi-session option

L1 worker MAY split work across sessions:

- **Session 1 (this session):** Land sub-lemmas 1 and 2 (cardinality
  + YES class count).  These are independent of each other and of
  the main theorem.  Total budget: ~200–300 LOC of new content.
- **Session 2 (follow-up):** Land sub-lemma 3 + main theorem
  assembly.  Total budget: ~150–200 LOC of new content.

Alternatively, the worker MAY attempt the full L1 in one session if
it fits in the 500 LOC budget.

## 5. Optional infrastructure to port from L0 variants

The L0 worker variant #1412 (closed in favour of #1413) landed two
complementary lemmas worth porting if they help the L1 proof:

- `slack_fails_for_full_coordinates`: at `D = Finset.univ`, the
  slack inequality is impossible.
- `any_isoStrong_witness_has_nonfull_D`: contrapositive — any
  iso-strong witness has `|D| < tableLen`.

These rule out the degenerate `D = full` regime, which may simplify
the pigeonhole proof in sub-lemma 3 (the worker can assume
`D.card < tableLen` and hence `tableLen - D.card ≥ 1`).

The L1 worker MAY port these lemmas (re-proving them locally with
the same proof structure) if useful.  Not required.

## 6. Possible verdicts

End the L1 report with **exactly one** of:

- **`RED_CONCLUSION_REFUTED`** — full Direction N theorem
  (`isoStrong_conclusion_negative_for_canonical`) lands kernel-checked.
  Route is formally inconsistent at canonical.  Canonical track
  closes inconsistent.  This is the strongest possible L1 outcome.
- **`YELLOW_TWO_OF_THREE_LANDED`** — two of the three sub-lemmas
  (any combination) land kernel-checked, plus precise blocker
  identification for the third sub-lemma and the main theorem.
- **`YELLOW_ONE_OF_THREE_LANDED`** — exactly one sub-lemma lands;
  precise sub-targets identified for the remaining two.
- **`INCONCLUSIVE_NEEDS_L2`** — the pigeonhole structure does not
  compose as expected in Lean (e.g., encoding details add
  prohibitive overhead, or a sub-lemma is not provable in the
  current formalization).  Report identifies the structural
  obstruction and recommends L2 (next-level escalation, possibly
  requiring mainline Lean infrastructure changes).

## 7. Anti-hardwiring caveat (carried forward from L0)

The L1 probe must NOT rely on:

- Truth-table hardwiring of `W.family` (per L0 #1388 result).
- Constructing concrete `W` via Classical.choice on a non-effective
  existential.
- Importing or referencing refuted predicates.

The L1 SHOULD use:

- Generic `W` as opaque parameter (using `W.size_bound`,
  `W.decides_global` as needed).
- Canonical `sYES = 1, sNO = 2` numeric facts (`F.Mof = n + 2`
  from L0).
- Standard mathlib Nat / pigeonhole / Finset.card lemmas.

## 8. Audit targets (read-only)

- `pnp3/Tests/IsoStrongConclusionProbe.lean` — the L0 staging file
  this L1 extends.
- `pnp3/LowerBounds/AsymptoticDAGBarrierTheorems.lean:1078–1104`
  (`IsoStrongFamilyEventually`).
- `pnp3/LowerBounds/AsymptoticDAGBarrierInterfaces.lean:25–104`
  (slice structures).
- `pnp3/LowerBounds/MCSPGapLocality.lean:140–200`
  (`ValueCoordinateSet`, `AgreeOnValues`, `ValidEncoding`,
  `encodePartial`, `decodePartial`, `Partial.valPart`,
  `Partial.maskPart`).
- `pnp3/Models/Model_PartialMCSP.lean`
  (`gapPartialMCSP_Language`, `PartialTruthTable`, `circuitCountBound`,
  size-1 circuit enumeration via `Magnification.size1Candidates`).
- `pnp3/Magnification/CanonicalAsymptoticDecider.lean`
  (`size1Candidates m` exact enumeration: `m + 2` candidates).
- `pnp3/Magnification/CanonicalAsymptoticTrackData.lean`
  (canonical spec, params).
- `pnp3/Tests/GlobalHInDagContractProbe.lean` (the global contract).
- `seed_packs/isoStrong_conclusion_L0/reports/L0_isoStrong_conclusion_codex.md`
  (L0 report including L1 sub-target framing).

## 9. Forbidden scope

- No edits outside `pnp3/Tests/IsoStrongConclusionProbe.lean` and
  the seed pack's `reports/` + `failures/` directories.
- No mainline Lean edits.
- No imports of `Magnification.LocalityProvider_Partial`,
  `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`, or any
  file under `pnp3/RefutedPredicates/`.
- No `axiom`, `opaque` (unless using `Classical.choice` on a strictly
  bounded existential, justified in docstring), `Fact`, `Provider`,
  `Payload`, `Default`, `Source`, `Witness`, `Gap` in declaration
  names other than the unavoidable `GlobalAsymptoticDAGWitness`
  parameter type.
- No `sorry`, `admit`, `native_decide`.
- No JSONL / NoGoLog / spec / `known_guards` / trust-root edits.
- No `ResearchGapWitness`, `VerifiedNPDAGLowerBoundSource`,
  `SourceTheorem`, `gap_from`, endpoint, `P ≠ NP` claim.
- No TM-verifier session work.
- No promotion of refuted predicates.

## 10. Allowed scope

- Extending the L0 staging file `pnp3/Tests/IsoStrongConclusionProbe.lean`
  with L1 lemmas + main theorem, ≤ 500 LOC total.
- ONE markdown report at
  `seed_packs/isoStrong_conclusion_L1/reports/L1_isoStrong_conclusion_<HANDLE>.md`.
- Optional failure notes under `failures/`.
