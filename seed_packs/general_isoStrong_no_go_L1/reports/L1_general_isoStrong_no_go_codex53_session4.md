# L1 general iso-strong no-go — session 4

Task: general iso-strong no-go L1 session 4
Handle: codex53 (with opus47 enrichment on merge)
Branch: main

## 1. Executive verdict

**RED_GENERAL_ISOSTRONG_REFUTED**

The final L1 route-level assembly landed.  Two new theorems were added
to `pnp3/Tests/GeneralIsoStrongNoGoProbe.lean`, both kernel-checked
with clean axiom dependencies (no `axiom` / `opaque` / `sorry` /
`admit` / `native_decide` / `sorryAx`).

After this session **the entire canonical iso-strong L1 chain has a
parameter-agnostic generic counterpart**, and the route-level
conclusion-side refutation of `IsoStrongFamilyEventually` is closed
for arbitrary `GapSliceFamilyEventually`.

## 2. What landed in session 4

In `pnp3/Tests/GeneralIsoStrongNoGoProbe.lean`:

1. `correctOnPromiseSlice_of_InPpolyDAG_family_general` — lifts an
   `InPpolyDAG` witness at slice `(n, β)` to the corresponding
   `CorrectOnPromiseSlice` witness for the family circuit at encoded
   length.  Direct general counterpart of the canonical helper
   `correctOnPromiseSlice_of_InPpolyDAG_family` in
   `pnp3/Tests/IsoStrongConclusionProbe.lean`.
   Axiom deps: `[propext, Classical.choice, Quot.sound]`.

2. `isoStrong_conclusion_negative_general` — the route-level
   no-go assembly:
   ```
   ∀ F : GapSliceFamilyEventually,
   ∀ hInDag : ∀ n β, InPpolyDAG (gapPartialMCSP_Language (F.paramsOf n β)),
     ¬ IsoStrongFamilyEventually F hInDag
   ```
   Closed by composing all prior L1 bricks via the canonical
   assembly template:
   - Destructure `IsoStrongFamilyEventually` to obtain
     `(β0, hβ0, κ, nIso, hForce, hSlack)`.
   - Choose `β := β0 / 2` and `n := max F.N0 (nIso β)`.
   - Lift the per-slice `InPpolyDAG` witness `C` via
     `correctOnPromiseSlice_of_InPpolyDAG_family_general`.
   - Invoke `hForce` at the chosen `(n, β, C)` to obtain a
     YES witness `yYes`, a coordinate set `D`, and the
     "all valid agreeing on `D` are YES" clause `hAllYes`.
   - Invoke `hSlack` and convert raw slack to `D.card` form via
     `slack_for_D_of_isoStrong_slack_general` and a
     `Finset.card_sdiff` normalisation.
   - Apply `exists_valid_agreeing_not_yes_under_general_slack` to
     produce a `z` that is `ValidEncoding`, agrees with `yYes` on `D`,
     and is not in the YES promise slice.
   - Contradict `hAllYes z hzValid hzAgree` against `hzNotYes`.
   Axiom deps: `[propext, Classical.choice, Quot.sound]`.

## 3. Ten-of-ten generic L1 ingredient table

| # | Canonical L1 ingredient | Generic equivalent | Session |
|---|---|---|---|
| 1 | `exists_trace_not_size1_of_card_lt` | `exists_label_not_in_trace_image_of_card_lt` | 1 |
| 2 | `slack_for_D_of_isoStrong_slack` | `slack_for_D_of_isoStrong_slack_general` | 1 |
| 3 | `diagonalPartialTable` | `generalDiagonalPartialTable` | 2 |
| 4 | `diagonal_z_valid` | `general_diagonal_z_valid` | 2 |
| 5 | `diagonal_z_agrees_on_D` | `general_diagonal_z_agrees_on_D` | 2 |
| 6 | `is_consistent_diagonal_table_implies_label_trace` | `is_consistent_general_diagonal_table_implies_trace_in_image` | 3 |
| 7 | `diagonal_z_not_yes_of_label_not_trace` | `general_diagonal_z_not_yes_of_label_not_in_trace_image` | 3 |
| 8 | `exists_valid_agreeing_not_yes_under_slack` | `exists_valid_agreeing_not_yes_under_general_slack` | 3 |
| 9 | `correctOnPromiseSlice_of_InPpolyDAG_family` | `correctOnPromiseSlice_of_InPpolyDAG_family_general` | **4** |
| 10 | `isoStrong_conclusion_negative_for_canonical` | `isoStrong_conclusion_negative_general` | **4** |

## 4. Build verification (local, lean4 v4.22.0-rc2)

- `lake build Tests.GeneralIsoStrongNoGoProbe` → success.
- `lake build PnP3 Pnp4` → success.
- `#print axioms` for both new theorems → standard kernel axioms only.

## 5. Strategic significance

The canonical iso-strong refutation was previously formalised only at
the canonical `sYES = 1, sNO = 2` instantiation
(`isoStrong_conclusion_negative_for_canonical`).  After session 4 the
**entire iso-strong route class** is provably empty for arbitrary
`GapSliceFamilyEventually` — not just the canonical point.

This means:

- The iso-strong route class is **mathematically dead** as a route
  family in this formalisation, not merely at one parametrisation.
- Future attacks on the canonical lower-bound chain via the
  iso-strong shape are precluded — the obstruction is generic and
  structural, not specific to the chosen `(sYES, sNO)` parameters.
- Future work must pivot to a different route family (promise-YES
  weak / certificate, pnp4 frontier `SearchMCSPWeakLowerBound`,
  AC0 milestone, or genuinely new research-level mathematics).

## 6. Scope violations

none.  Markdown report + one Lean test-local file; no endpoint, spec,
JSONL, NoGoLog, known_guards, or trust-root edits; no
`ResearchGapWitness`, `SourceTheorem`, `gap_from`, endpoint, or
`P ≠ NP` claim.

## 7. Next action

**close_isoStrong_route_pattern_refuted**

(Optional follow-ups: update STATUS.md to record the general iso-strong
route closure; consider lifting the promise-YES routes via the
existing pointwise contrapositive implications now that all generic
iso-strong machinery is in place.)
