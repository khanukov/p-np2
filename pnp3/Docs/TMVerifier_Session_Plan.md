# Plan: closing the TM verifier for canonical asymptotic GapPartialMCSP

> **ARCHIVED SCAFFOLD (2026-05-29).** The Lean files this plan targets
> (`GapMCSPVerifier.lean` and `TuringToolkit/*`) have been moved out of the
> active build to `archive/pnp3/Complexity/PsubsetPpolyInternal/` (orphaned,
> incomplete, and unrelated to the `P ⊆ P/poly` inclusion). Paths below refer
> to the pre-archive locations; restore from `archive/` and re-add the
> `lakefile.lean` globs to resume.

**Repository:** `/home/user/p-np2/pnp3`
**Baseline branch:** `claude/audit-hnpbridge-interface-FnO1v` (already
carries the decoder + components bridge)

## 1. Context

The reduction layer in
`pnp3/Magnification/CanonicalAsymptoticDecider.lean` already collapses
the canonical asymptotic NP track to a single typed target: build
`CanonicalAsymptoticVerifierComponents`.  Downstream,
`canonicalAsymptoticData_of_components → AsymptoticFormulaTrackData`
is fully proved with no `sorry` / axioms.

Closing the TM verifier is **multi-thousand-LOC engineering**.  One
Lean session ≈ one leaf blocker, so we decompose into **7
sequential sessions**, each with a standalone theorem and a "0 sorry
/ standard classical axioms only" obligation.

The toolkit already carries the heavyweight theorems:
- `BinaryCounter.incrementProgram_correct` —
  `BinaryCounter.lean:1315`
- `CombineAtOffset.combineAtOffsetCS_run_full` —
  `CombineAtOffset.lean:1037`
- `GateWrappers.circuitEvaluatorCS_run_correct_wf` —
  `GateWrappers.lean:5034`
- `GateWrappers.seqList_timeBound_le_uniform` —
  `GateWrappers.lean:577`

## 2. Architectural decision: Variant B (NP-style)

Replace `CanonicalAsymptoticVerifierComponents.accepts_eq` with the
standard NP formulation:

```lean
accepts_eq : ∀ n (x : Bitstring n),
  decideAsymptotic n x = true ↔
    ∃ w : Bitstring (certificateLength n k),
      Internal.PsubsetPpoly.TM.accepts (M := M) (n := n + certificateLength n k)
        (concatBitstring x w) = true
```

**Rationale:**
- Removes the internal "Phase A scan + Phase B identify" (~600 LOC)
  for enumerate-all-candidates.
- The TM just **verifies** a guessed candidate encoded in `w` — the
  standard OPS19 / CJW20 pattern.
- Non-canonical lengths are handled trivially: the verifier rejects
  every `(x ++ w)` whenever `n ≠ 2·2^m`, without a special search.
- Saves ~30% of LOC across sessions 3–6.

After the structure change, the current `witness` (lines 296–312)
will directly use the existential rewrite instead of `trivialCert`.

## 3. Per-session plan

### Session 1 — `seqList_run_full`
**File:** `pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/ConstStatePhasedProgram.lean`
**LOC:** ~350
**Building blocks:** `runConfig_seq_succ_*` (lines 414–544),
`seqList` (line 573)
**Deliverable:** a generic `seqList_run_full` with motive parameter
`Configuration → S → Prop`, modelled on `runConfig_seq_succ_P2_*`
(lines 488–544).
**Acceptance:** theorem typechecks; axiom audit ∈
`{propext, Classical.choice, Quot.sound}`.

### Session 2 — `writeVecOfNatProgram`
**File:** new
`pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/RowInputWriter.lean`
**LOC:** ~300
**Building blocks:** `incrementProgram_correct`,
`CopyAtOffset.copyAtOffsetProgram_run_full`
**Deliverable:** `writeVecOfNatProgram` + the `_run_full` theorem:
after `timeBound N` steps, the tape region `[Δrow .. Δrow+m)` equals
`vecOfNat n i`.
**Acceptance:** theorem closed; module registered in
`lakefile.lean`.

### Session 3 — `mcspCheckAllRows_correct`
**File:**
`pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/RowConsistencyCheck.lean`
(extension)
**LOC:** ~450
**Building blocks:** Session 1 (`seqList_run_full`),
`circuitEvaluatorCS_run_correct_wf`, Session 2
(`writeVecOfNat`), `rowConsistencyCheckCSAt_row` (line 69)
**Deliverable:** `tape[Δflag]` after the run =
`List.any (List.ofFn …) inconsistent_at_row_i`.
**Acceptance:** theorem + axiom audit.

### Session 4 — Witness decoder
**File:** new
`pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/WitnessDecoder.lean`
**LOC:** ~250
**Building blocks:** `Encoding.lean` table layout,
`CopyAtOffset.copyAtOffsetProgram_run_full`
**Deliverable:**
`decodeCandidateSpec : Bitstring (certLen) → Option (CandidateSpec n)` +
`decodeCandidateSpec_writeToTape_run_full` (writes the gate table
into the tape region) +
`decodeCandidateSpec_surjective_on_valid_candidates`.
**Acceptance:** both theorems closed.

### Session 5 — Length probe
**File:** new
`pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/LengthProbe.lean`
**LOC:** ~250
**Building blocks:** `incrementProgram_correct` (doubling),
`UnaryAtOffset` for compare
**Deliverable:** `canonicalLengthCheckProgram` reads `m` from the
standard `w` slot and checks `n = 2·2^m` via walk + compare; returns
`(m, true)` or `false`.
**Acceptance:** `canonicalLengthCheckProgram_run_full` closed.

### Session 6 — Top-level composition
**File:** new
`pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/CanonicalVerifierTM.lean`
**LOC:** ~500
**Building blocks:** sessions 1–5,
`decideAsymptotic_at_inputLen`, `decideAsymptotic_of_not_canonical`
**Deliverable:** `verifierProgram` + `verifierProgram_accepts_iff`:
```
TM.accepts (concatBitstring x w) = true ↔ candidateValid w ∧ decideAsymptotic n x = true
```
The non-canonical branch rejects via
`decideAsymptotic_of_not_canonical`.
**Acceptance:** theorem + full build.

### Session 7 — Runtime bound + Components term
**Files:**
- new `pnp3/Magnification/CanonicalAsymptoticVerifierInstance.lean`;
- edit `pnp3/Magnification/CanonicalAsymptoticDecider.lean` (struct +
  witness body, Variant B switch);
- edit
  `pnp3/Complexity/PsubsetPpolyInternal/GapMCSPVerifier.lean`
  (documentation);
- edit `pnp3/Tests/CanonicalIntegrationTests.lean` (adapt examples to
  the new structure).

**LOC:** ~450
**Building blocks:** `seqList_timeBound_le_uniform`,
`mcspCheckAllRows_timeBound_le` (line 213), session 6
**Deliverable:**
1. `verifierProgram_runTime_poly` with explicit `c`, `k`.
2. `canonicalAsymptoticVerifierComponents : CanonicalAsymptoticVerifierComponents`
   (Variant B).
3. `witness` body rewritten through the existential rewrite.

**Acceptance:** `def canonicalAsymptoticVerifierComponents`
typechecks; `#print axioms` ⊆
`{propext, Classical.choice, Quot.sound}`; all `canonical_*` theorems
in `CanonicalIntegrationTests.lean` are now unconditional (after
applying `witness` to the new term).

## 4. Critical files (reusable pieces)

- `pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/BinaryCounter.lean:1315`
  — `incrementProgram_correct`
- `pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/CombineAtOffset.lean:1037`
  — `combineAtOffsetCS_run_full`
- `pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/GateWrappers.lean:5034`
  — `circuitEvaluatorCS_run_correct_wf`
- `pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/GateWrappers.lean:577`
  — `seqList_timeBound_le_uniform`
- `pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/ConstStatePhasedProgram.lean:414-544`
  — `runConfig_seq_succ_*` (for session 1)
- `pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/RowConsistencyCheck.lean:69,175,213`
  — row primitives
- `pnp3/Magnification/CanonicalAsymptoticDecider.lean:192,206,223,244,271,296`
  — decider + bridge
- `pnp3/Models/Model_PartialMCSP.lean:883`
  — `GapPartialMCSP_Asymptotic_TMWitness`

## 5. Per-session verification checklist

At the end of each session:

1. **Build PnP3:**
   ```
   export PATH="$HOME/.elan/bin:$PATH" && cd /home/user/p-np2 && lake build PnP3
   ```
   Must pass with no errors and no `sorry` warnings.

2. **Axiom audit** for new top-level theorems: add `#print axioms T`
   to `scripts/audit_canonical_axioms.lean` and confirm the output is
   ⊆ `{propext, Classical.choice, Quot.sound}`.

3. **scripts/check.sh:**
   ```
   bash /home/user/p-np2/scripts/check.sh
   ```
   Exit 0.

4. **Integration regression:**
   `pnp3/Tests/CanonicalIntegrationTests.lean` must compile.  Session
   7 requires adapting the examples.

5. **Zero sorry / zero axiom policy:**
   `grep -c "sorry\|admit" pnp3/**/*.lean` stays 0; no new `axiom`
   declarations.

6. **Commit + push:** one session = one commit with an explicit
   message `Session N: <leaf theorem name>`, push to
   `claude/audit-hnpbridge-interface-FnO1v`.

## 6. Cross-session risk register

- **Session 1:** `seqList_run_full` needs a flexible motive parameter
  `Configuration → S → Prop`; otherwise we have to re-prove at every
  call site.  Mitigation: model on `runConfig_seq_succ_P2_*` (lines
  488–544) with an explicit state predicate.
- **Session 3:** `OR_{i<2^m}` may cause a
  `Decidable.decide`-vs-`Bool` mismatch with
  `circuitEvaluatorCS_run_correct_wf`.  Mitigation: formulate `OR`
  via `List.any` from the start.
- **Session 7:** changing `accepts_eq` is a breaking API change.  A
  grep shows only `Tests/CanonicalIntegrationTests.lean` (lines
  124–152) and `GapMCSPVerifier.lean` (lines 91–101) — both must be
  updated atomically in the same session.

## 7. Final state after session 7

- `Pnp3.Magnification.canonicalAsymptoticVerifierComponents` — a
  concrete term.
- `Pnp3.Magnification.CanonicalAsymptoticVerifierComponents.witness canonicalAsymptoticVerifierComponents`
  — a concrete `GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec`.
- All `canonical_*_of_TM` theorems in `CanonicalIntegrationTests.lean`
  are instantiated on this witness and become unconditional.
- The canonical asymptotic track is closed unconditionally.  The only
  remainder is the research-level `ResearchGapWitness.dagSeparation`
  (a separate problem, not part of the TM verifier).

**Total estimated work:** 7 sessions × ~350 LOC ≈ 2500 LOC of new
engineering plus ~50 LOC of edits to the bridge structure.
