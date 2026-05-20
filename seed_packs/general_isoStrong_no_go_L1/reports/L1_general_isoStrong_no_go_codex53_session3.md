# L1 general iso-strong no-go — session 3 (codex53)

## 1. Executive verdict
INCONCLUSIVE_NEEDS_L2

## 2. What landed
- No new kernel-checked theorem landed in this session.

## 3. General not-YES bridge status
- Attempted to generalize the canonical not-YES bridge pattern from
  `IsoStrongConclusionProbe` into
  `GeneralIsoStrongNoGoProbe` using bounded-size circuits and
  `traceCircuitOnRows`.
- The main blocker was a type-shape mismatch around the row domain used by
  `traceCircuitOnRows` over `((Finset.univ \ D).attach)`, which produced a
  doubly-attached subtype in local goals and prevented direct reuse of
  `assignmentIndex_vecOfNat_eq` and the expected diagonal simplification.
- A second blocker is the missing/undiscovered direct bridge lemmas used in
  canonical staging (`gapSlice_yes_iff`,
  `gapPartialMCSP_Language_eq_true_iff_yes`) under current imports/names for
  this file.

## 4. Remaining blockers
1. Precise row-domain coercion lemma needed for:

```lean
traceCircuitOnRows
  ((Finset.univ \ D).attach)
  (fun a => a.1)
  C
```

to align with

```lean
assignmentIndex_vecOfNat_eq :
  assignmentIndex (Core.vecOfNat p.n i.val) = i
```

without introducing nested subtype coercions.

2. A stable YES-membership elimination bridge in this file's context:

```lean
z ∈ (gapSliceOfParams p).Yes
  -> ∃ C, C.size ≤ p.sYES ∧ is_consistent C (decodePartial z)
```

plus the encode/decode rewrite to `generalDiagonalPartialTable`.

3. Membership bridge for bounded-size circuit enumeration:

```lean
C.size ≤ p.sYES -> C ∈ circuitsOfSizeAtMost p.n p.sYES
```

with namespace/import resolution pinned in this module.

## 5. Next action
open_general_isoStrong_no_go_L1_session_4
