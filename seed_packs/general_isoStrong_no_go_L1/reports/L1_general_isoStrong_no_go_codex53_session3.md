# L1 general iso-strong no-go — session 3

Task: general iso-strong no-go L1 session 3
Handle: codex53 (with opus47 enrichment on merge)
Branch: main

## 1. Executive verdict

**YELLOW_SESSION3_GENERAL_BRIDGE_LANDED**

Three L1 session-3 theorems landed, kernel-checked, with clean axiom
dependencies (no `axiom` / `opaque` / `sorry` / `admit` /
`native_decide` / `sorryAx`).  After this session **all six canonical
L1 ingredients have generic replacements** at the per-slice
`GapPartialMCSPParams` level.  The only work remaining is the final
route-level assembly `isoStrong_conclusion_negative_general` at
`GapSliceFamilyEventually`, staged for L1 session 4.

## 2. What landed

In `pnp3/Tests/GeneralIsoStrongNoGoProbe.lean`:

1. `is_consistent_general_diagonal_table_implies_trace_in_image` —
   any bounded-size circuit `C` consistent with the general diagonal
   table satisfies `traceCircuitOnRows ... C = label` on the free
   rows.  Generic replacement for canonical
   `is_consistent_diagonal_table_implies_label_trace`, lifted from
   size-1 candidate consistency to arbitrary bounded-size circuit
   consistency.
   Axiom deps: `[propext, Classical.choice, Quot.sound]`.

2. `general_diagonal_z_not_yes_of_label_not_in_trace_image` — if
   `label` lies outside the bounded-size trace image, the encoded
   general diagonal cannot be in the YES promise slice.  Generic
   replacement for canonical `diagonal_z_not_yes_of_label_not_trace`.
   Axiom deps: `[propext, Classical.choice, Quot.sound]`.

3. `exists_valid_agreeing_not_yes_under_general_slack` — the
   session-3 final composition: under the strict trace-cardinality
   slack `circuitCountBound p.n (p.sNO - 1) < 2 ^ |Finset.univ \ D|`,
   there exists `z` that is a `ValidEncoding`, agrees with `yYes`
   on `D`, and is not in the YES promise slice.  Generic replacement
   for canonical `exists_valid_agreeing_not_yes_under_slack`.
   Axiom deps: `[propext, Classical.choice, Quot.sound]`.

## 3. Six-of-six canonical L1 ingredient table

| Canonical L1 ingredient | Generic equivalent | Status |
|---|---|---|
| `exists_trace_not_size1_of_card_lt` (session 1) | `exists_label_not_in_trace_image_of_card_lt` | ✅ landed (session 1) |
| `slack_for_D_of_isoStrong_slack` (session 4) | `slack_for_D_of_isoStrong_slack_general` | ✅ landed (session 1) |
| `diagonalPartialTable` (session 2) | `generalDiagonalPartialTable` | ✅ landed (session 2) |
| `diagonal_z_valid` (session 2) | `general_diagonal_z_valid` | ✅ landed (session 2) |
| `diagonal_z_agrees_on_D` (session 2) | `general_diagonal_z_agrees_on_D` | ✅ landed (session 2) |
| `is_consistent_diagonal_table_implies_label_trace` + `diagonal_z_not_yes_of_label_not_trace` + `exists_valid_agreeing_not_yes_under_slack` (sessions 3–4) | `is_consistent_general_diagonal_table_implies_trace_in_image` + `general_diagonal_z_not_yes_of_label_not_in_trace_image` + `exists_valid_agreeing_not_yes_under_general_slack` | ✅ landed (session 3) |

## 4. General not-YES bridge proof structure

The session-3 not-YES bridge converts
`encodePartial (generalDiagonalPartialTable p yYes D label) ∈ (gapSliceOfParams p).Yes`
into a contradiction via:

1. `gapPartialMCSP_language_true_iff_yes` to unpack YES-membership
   directly into `∃ C, C.size ≤ p.sYES ∧ is_consistent C (decodePartial z)`,
   bypassing the heavier `gapSlice_yes_iff` API (which under this
   file's import surface triggers a `whnf` heartbeat blow-up; see
   §6 notes).
2. `decodePartial_encodePartial` to rewrite consistency on the
   decoded encoded table into consistency on `generalDiagonalPartialTable`
   directly.
3. `is_consistent_general_diagonal_table_implies_trace_in_image` to
   deduce `traceCircuitOnRows ... C = label`.
4. `Counting.mem_circuitsOfSizeAtMost C p.sYES hSize` plus
   `Finset.mem_image.mpr` to package `label ∈ image(traceCircuitOnRows ...)`.
5. Contradict the `label ∉ image(...)` hypothesis.

This is the structural argument used in the canonical proof at the
size-1 level, lifted unchanged to bounded-size circuits via the L0
bricks.

## 5. Build verification (local, lean4 v4.22.0-rc2)

- `lake build Tests.GeneralIsoStrongNoGoProbe` → success.
- `lake build PnP3 Pnp4` → success.
- `#print axioms` for all eight landed theorems (sessions 1–3) →
  standard kernel axioms only.

## 6. Notes on proof engineering

Two API-selection choices were decisive for getting this session to
build:

(a) Use `gapPartialMCSP_language_true_iff_yes` directly to unpack
   YES-membership, instead of the `gapSlice_yes_iff` route which
   demands a length-equality side condition `partialInputLen p = …`
   discharged by `simp` followed by a cascade of rewrites
   (`gapPartialMCSP_Language_eq_true_iff_yes` + `PartialMCSP_YES` +
   `decodePartial_encodePartial`).  Under this file's extended
   import set, the cascade fires `whnf` enough times to exceed
   the default 200000-heartbeat budget at the existential intro
   step.  (See `seed_packs/general_isoStrong_no_go_L1/failures/`
   notes from the parallel structured-failure variants for the
   precise failure pattern.)

(b) Reuse `Counting.mem_circuitsOfSizeAtMost` directly instead of the
   alternative `mem_circuitsOfSizeAtMost_of_size_le` API which is not
   exposed under the `Counting` namespace path used by the rest of
   the chain.

## 7. Remaining blocker for L1 session 4

Final route-level assembly:

```lean
theorem isoStrong_conclusion_negative_general
    (F : GapSliceFamilyEventually)
    (hInDag : ∀ n β, InPpolyDAG (gapPartialMCSP_Language (F.paramsOf n β))) :
    ¬ IsoStrongFamilyEventually F hInDag
```

Expected proof shape:

1. Unpack `IsoStrongFamilyEventually` to obtain eventual slack on the
   `(tableLen, κ)` axis.
2. Pick a sufficiently large `n` and witness `D` of cardinality `κv`.
3. Apply `slack_for_D_of_isoStrong_slack_general` to convert the
   slack to the `D.card` form at the per-slice
   `(F.paramsOf n β)`-parameters.
4. Apply `exists_valid_agreeing_not_yes_under_general_slack` to
   obtain a `z` that is `ValidEncoding`, agrees with `yYes` on `D`,
   and is not in the YES promise slice.
5. Contradict the iso-strong forcing clause `hForce` which would
   require all valid `z` agreeing on `D` to be in YES.

Estimated size: ~50 LOC, analogous in shape to canonical L1 session 4.

## 8. Scope violations

none.  Markdown report + one Lean test-local file; no endpoint, spec,
JSONL, NoGoLog, known_guards, or trust-root edits; no
`ResearchGapWitness`, `SourceTheorem`, `gap_from`, endpoint, or
`P ≠ NP` claim.

## 9. Next action

**open_general_isoStrong_no_go_L1_session_4**
