# L1 general iso-strong no-go — session 2

Task: general iso-strong no-go L1 session 2
Handle: codex53 (with opus47 enrichment on merge)
Branch: main

## 1. Executive verdict

**YELLOW_PARTIAL_GENERAL_L1**

Three L1 session-2 bricks landed, kernel-checked, with clean axiom
dependencies (no `axiom` / `opaque` / `sorry` / `admit` /
`native_decide` / `sorryAx`).  The full generalised contradiction
`isoStrong_conclusion_negative_general` is not yet assembled and is
explicitly staged for L1 session 3 (the not-YES bridge plus final
composition).

## 2. What landed in session 2

In `pnp3/Tests/GeneralIsoStrongNoGoProbe.lean`:

1. `generalDiagonalPartialTable` — the general diagonal partial table
   over an arbitrary `GapPartialMCSPParams`, copying `decodePartial yYes`
   on fixed rows `D` and using `label` on free rows
   `(Finset.univ \ D).attach → Bool`.  Generic replacement for the
   canonical `diagonalPartialTable`.

2. `general_diagonal_z_valid` — the encoded general diagonal is a
   `ValidEncoding p` via `validEncoding_encodePartial`.
   Axiom deps: `[propext, Classical.choice, Quot.sound]`.

3. `general_diagonal_z_agrees_on_D` — the encoded general diagonal
   agrees with `yYes` on the fixed coordinates `D` (`AgreeOnValues D yYes
   (encodePartial (generalDiagonalPartialTable ...))`) under
   `ValidEncoding p yYes`.  Closed by the same value-bit calc chain
   used in the canonical proof (`Partial.valPart` round-trip through
   `encodePartial`/`decodePartial`).  Axiom deps:
   `[propext, Classical.choice, Quot.sound]`.

The two earlier session-1 bricks
(`exists_label_not_in_trace_image_of_card_lt`,
`slack_for_D_of_isoStrong_slack_general`) are unchanged.

## 3. Does this generalise canonical RED?

**Partially** — diagonal-encoding infrastructure landed.

The session-2 bricks landed are the generic replacements for three of
the six canonical L1 ingredients:

- canonical session 2 `diagonalPartialTable` → `generalDiagonalPartialTable`;
- canonical session 2 `diagonal_z_valid` → `general_diagonal_z_valid`;
- canonical session 2 `diagonal_z_agrees_on_D` → `general_diagonal_z_agrees_on_D`.

Combined with session 1's `exists_label_not_in_trace_image_of_card_lt`
(generic pigeonhole) and `slack_for_D_of_isoStrong_slack_general`
(generic slack conversion), five of six canonical L1 ingredients are
now generic.  The only canonical-specific ingredient remaining is the
not-YES bridge `is_consistent_diagonal_table_implies_label_trace` and
the final composition `exists_valid_agreeing_not_yes_under_slack`,
both of which need to be lifted from `Size1Candidate` consistency to
bounded-size circuit consistency using the L0 trace-image bound
`boundedSizeTrace_image_card_le`.

## 4. Remaining blockers for L1 session 3

- General not-YES bridge `is_consistent_general_diagonal_table_implies_trace_in_image`
  (replacement for canonical `is_consistent_diagonal_table_implies_label_trace`).
- General not-YES inverse `general_diagonal_z_not_yes_of_label_not_in_trace_image`
  (replacement for canonical `diagonal_z_not_yes_of_label_not_trace`).
- General composition `exists_valid_agreeing_not_yes_under_general_slack`.
- Final assembly into `isoStrong_conclusion_negative_general` over an
  arbitrary `GapSliceFamilyEventually`.

## 5. Build verification (local, lean4 v4.22.0-rc2)

- `lake build Tests.GeneralIsoStrongNoGoProbe` → success.
- `lake build PnP3 Pnp4` → success.
- Axiom-dependency check via `#print axioms` confirms all four landed
  theorems use only standard kernel axioms.

## 6. Notes on proof engineering

The canonical proof of `diagonal_z_agrees_on_D` uses `simpa [hy]` to
substitute `yYes = encodePartial (decodePartial yYes)`.  Direct port
to the general file triggered a `simp` infinite-recursion blowup
under this file's extra `simp`-set surface (additional imports from
`LowerBounds.AsymptoticDAGBarrierTheorems` / `Interfaces`).  Replaced
with the equivalent `congrArg (fun s => Partial.valPart s i) hy`
which is `simp`-set-independent and matches the same kernel term.

The `(Finset.univ \ D).attach → Bool` label-domain type — flagged by
the structured-failure reports #1460 and #1461 as a potential
double-subtype blocker — is in fact the type used by the canonical
proof; it is not a real blocker.  The earlier failures were caused
by `simp`-set divergence on the value-bit calc chain (resolved
above) and by namespace/import issues at the not-YES bridge step
(deferred to session 3).

## 7. Scope violations

none.  Markdown report + one Lean test-local file; no endpoint, spec,
JSONL, NoGoLog, known_guards, or trust-root edits; no
`ResearchGapWitness`, `SourceTheorem`, `gap_from`, endpoint, or
`P ≠ NP` claim.

## 8. Next action

**open_general_isoStrong_no_go_L1_session_3**
