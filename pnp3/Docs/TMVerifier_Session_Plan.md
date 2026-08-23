# Plan: closing the TM verifier for canonical asymptotic GapPartialMCSP

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
**File:** `pnp3/Complexity/TMVerifier/TuringToolkit/ConstStatePhasedProgram.lean`
**LOC:** ~350
**Building blocks:** `runConfig_seq_succ_*` (lines 414–544),
`seqList` (line 573)
**Deliverable:** a generic `seqList_run_full` with motive parameter
`Configuration → S → Prop`, modelled on `runConfig_seq_succ_P2_*`
(lines 488–544).
**Acceptance:** theorem typechecks; axiom audit ∈
`{propext, Classical.choice, Quot.sound}`.

**W-A infrastructure delivered (2026-08-22):**
`TuringToolkit/ConstStatePhasedProgramSeqRun.lean` now completes the named
two-program configuration-flow theorem `seq_run_full`, ordinary `RunSpec.seq`
closure, and the specialized terminal closure `RunSpec.seqList_singleton`, not
the full list induction promised by this session.  `RunSpec` records the
non-automatic prefix conditions (not reaching the accept phase early and
right-move head safety), arrival at the accept phase at `timeBound`, and a
caller-chosen semantic postcondition.  Phase arrival alone is not TM
acceptance, because it does not assert equality with the accepting local state.
`seq_run_full` starts from
`embedSeqConfig P1 P2 c1`, derives the handoff head bound from the single
`P1.tapeLength ≤ P2.tapeLength` premise, starts P2 at
`liftP1ToP2 P1 P2 (P1.run ...)`, and returns the final configuration as
`embedSeqP2Config P1 P2 (P2.run ...)` together with both postconditions.
`RunSpec.seq` packages that flow as a `RunSpec (seq P1 P2)` whose postcondition
identifies the exact embedded final configuration and preserves both component
postconditions.  Its full P2 `RunSpec` premise is intentionally stronger than
configuration flow alone requires: P2's early-phase avoidance and final phase
arrival are required to prove closure and support later right-nested
induction.  It cannot serve as the singleton base by taking `P2 := idleCS`:
for nonzero `P.timeBound`, `P.tapeLength ≤ idleCS.tapeLength` is false.
`RunSpec.seqList_singleton` instead performs the final handoff directly in the
`seq P idleCS` composite, reaches the composite accept phase, and preserves the
embedded P final tape and head without projecting either into a shorter idle
tape.  The two-piece concrete theorem's second write postcondition is relative
to the P1-to-P2 boundary lift `c2Init`, not directly to the original P1
configuration.  `gateConstCS_seqList_singleton_runSpec` supplies a concrete
compiling singleton `seqList [gateConstCS b d]` surface.
`gateConstCS_seq_run_full` instantiates the theorem on two ordered constant
gate pieces and derives the second gate's destination bound from the first
gate's bound and `d1 ≤ d2`.  These two concrete constant-gate examples live in
`TuringToolkit/ConstStatePhasedProgramSeqRunExamples.lean`; the generic
`RunSpec` interface and composition theorems remain in
`TuringToolkit/ConstStatePhasedProgramSeqRun.lean`.

This W-A increment was **Infrastructure**, not a restricted lower bound and
not P-vs-NP mainline progress.  At that stage, ordinary `RunSpec.seq` plus the
terminal singleton closure formed the induction kernel, while the recursive
theorem assembling it over `seqList` remained open.  It did not close any
verifier-language correctness or runtime obligation.

**W-B non-dependent list layer delivered (2026-08-22):**
`TuringToolkit/ConstStatePhasedProgramSeqListRun.lean` now supplies the light
`seqList` recursion layer, importing only the preceding `SeqRun` module.  The
bridge `liftP1ToSeq_eq_embedSeqConfig_lift` proves that lifting directly into a
composite tail agrees with lifting into its head and embedding, under the
explicit adjacent comparison `Pᵢ.tapeLength n ≤ Pᵢ₊₁.tapeLength n`.
This adjacent hypothesis is essential: embedding through a shorter successor
can erase cells.  The current public API covers adjacent-monotone lists; a
shorter handoff would require a separate no-information-loss premise rather
than an unrestricted-list claim.

`RunSpec.seqList_singleton_exact` identifies the actual terminal boundary-step
configuration.  `RunSpec.seqList_cons` is the semantic recursion interface: it
preserves the exact final composite configuration together with the head
program's standalone postcondition and the already-assembled tail
postcondition.  The separate non-dependent control-flow theorem
`RunSpec.seqList_of_forall` handles every nonempty list using ordinary
`List.Forall` and `List.Chain' (ReadyStep ready)` and deliberately concludes
with postcondition `True`.  It guarantees whole-list `prefixSafe` and arrival
at the declared accept phase.  It does **not** collect heterogeneously typed
intermediate configurations, and it does not assert TM acceptance: phase
arrival remains distinct from equality with the accepting local state.

`TuringToolkit/ConstStatePhasedProgramSeqListRunExamples.lean` proves an actual
two-constant-gate `seqList` `RunSpec` with exact final configuration and both
gate-write facts; this exercises the bridge and exact singleton.  A three-gate
probe applies the cons theorem twice under only `d₁ ≤ d₂` and `d₂ ≤ d₃`,
pinning the recursive scope without claiming arbitrary unordered gates.
The arbitrary control-flow driver is now concretely inhabited for every
nonempty homogeneous list `P :: List.replicate copies P`, where
`P = gateConstCS b d`: its explicit readiness predicate and every
`List.Forall`/`List.Chain' ReadyStep` obligation are proved from the constant
gate run facts.  This remains a phase-only result.  An arbitrary-length
semantic accumulator (including the proposed `zeroExtTape`-style tape
description) remains open.
The modules, public signatures, and headline axiom dependencies are registered
in `lakefile.lean`, `Tests/TMSeqRunSurfaceTests.lean`, and
`Tests/AxiomsAudit.lean`.

This remains **Infrastructure**, not a restricted lower bound and not P-vs-NP
mainline progress.  It closes the non-dependent, adjacent-monotone list
control-flow layer, but it does not prove verifier-language correctness,
acceptance, or a polynomial runtime bound for the eventual verifier.

**W-C actual-input conditional-accept capstone delivered (2026-08-23):**
`TuringToolkit/ConstStatePhasedProgramInitialConfig.lean` proves the
unconditional full-configuration identity
`initialConfig_seq_eq_embedSeqConfig_initialConfig`.  The equality covers the
dependent phase/local state, head, and every cell of the composite tape; it
has no hypotheses and no input cast.

`TuringToolkit/ConstStatePhasedProgramConditionalAcceptExamples.lean` defines
`gateConstThenAcceptIfCS b d := seq (gateConstCS b d) (acceptIfCellCS d)`.
The operands both have standalone clock `2*d+3`, so ordinary `RunSpec.seq`
applies with equal tape lengths and no padding.  From the composite machine's
actual `initialConfig`, the dependency-closed `RunSpec` proves that the exact
final local state is `(b,b)`, the head returns to its initial position, and
the complete final tape is the initial tape with cell `d` set to `b`.  Hence
`TM.accepts ... = b` for every input length, input, bit, and offset, covering
both the accepting and rejecting executions.

This W-C increment is **Infrastructure**, not a restricted lower bound and
not P-vs-NP mainline progress.  It constructs no content verifier and proves
no runtime bound for one.  Generic padding and the discipline needed to rule
out advice through arbitrary functional clocks remain explicitly open; this
increment adds neither a padding constructor nor a free clock argument.

**T1a fixed-control true uniform seek delivered (2026-08-23):**
`TuringToolkit/TrueUniformSeekEncoding.lean` defines the canonical four-bit
frame ABI and proves the encoder/decoder round trip.
`TuringToolkit/TrueUniformSeek.lean` defines one closed finite-control
`ConstStatePhasedProgram` with the public exact clock
`128 * (N + 1)^2 + 128`.  `TuringToolkit/TrueUniformSeekValidation.lean`
proves genuine `TM.runConfig` traces for the four-bit forward macrostep,
canonical grammar validation, and the exact rewind to the left anchor.  The
exact finite-time theorem `t1CS_validate_rewind_encoded_exact` reaches the
`startMutation` handoff while preserving the initial tape.  T1b-A subsequently
makes that handoff active, so the former T1a full-clock idle-handoff theorem is
intentionally superseded rather than retained with a false conclusion.

This increment is **Infrastructure**, not a restricted lower bound and not
P-vs-NP mainline progress.

**T1b-A fixed destructive-seek opening delivered (2026-08-23):**
`TuringToolkit/TrueUniformSeek.lean` extends the same zero-parameter finite
control with a single Boolean latch and machine-created `spent`/`cursor`
markers.  The ABI, public quadratic clock, and absence of runtime `Nat`, width,
offset, or index fields are unchanged.  Small transition-table lemmas feed the
generic `ConstStatePhasedStepBridge`; mutation proofs do not unfold the full
control table inside `TM.stepConfig`.

`TuringToolkit/TrueUniformSeekMutation.lean` proves genuine atomic execution
for leaving `startMutation`, probing data/OOB, installing and restoring cursor
frames, marking one unary index frame as `spent`, and finding the next index or
success anchor.  The capstones prove exact first-cursor installation from both
the mutation boundary and the real initial configuration, and prove that an
empty data region reaches the idle OOB boundary under the full public clock.
Concrete index-zero, nonzero-index, and empty-data runs instantiate the public
theorems.

This T1b-A increment remains **Infrastructure**.  It does not prove the
iterated `j → j+1` mutation invariant, successful runtime-index lookup,
restoration of all temporary markers, output writing, malformed-input closure,
or acceptance.  Those are explicit T1b-B/T1c obligations.  The modules and
their public headline results are covered by concrete examples, a compile-time
surface test, and the axiom audit.

**T1a review hardening (2026-08-23):** the generic forward-frame scanner
`t1CS_scan_frames` and non-anchor reverse scanner `t1CS_rewind_tail` are public
T1b reuse surfaces, with exact import-side type probes and axiom audits.  Their
shared public signature exposes only the concrete-machine abbreviation `T1M`
in addition to the existing frame/tape/path vocabulary.  The public
`t1CS_frame_macrostep` now takes the positive `T1ForwardMode` premise.  The
clock theorem remains available by name but is not a simp rule: the generic
clock projections stop at `t1CS.timeBound N`, and the named theorem supplies
the explicit program-specific expansion to `t1Clock N` when needed.

The pure parser is now canonical: `decodeT1Tape? bits = some r` implies
`bits = encodeT1 r`.  Separately, `t1CanonicalEncoderAutomatonTrace` connects
the encoder's frames plus the explicit blank frame to the forward control
trace ending at rewind.  This is not a theorem equating the parser and the TM,
nor a malformed/trailing-input rejection theorem.  `T1Physical` is retained
only as vocabulary for that future scope and is not claimed to be discharged
by the current canonical execution results.  This review increment remains
**Infrastructure**, not P-vs-NP mainline progress.

**Generic step bridge delivered (2026-08-23):**
`TuringToolkit/ConstStatePhasedStepBridge.lean` proves, once and generically,
that an opaque `ConstStatePhasedProgram.transition` tuple equality determines
the complete compiled `TM.stepConfig`: dependent control state, moved head and
pointwise tape update.  Its five corollaries (`left`, `left_clamped`, `right`,
`right_clamped`, `stay` — the two `left` and the two `right` premises are
pairwise complementary, so every move at every head position is covered) let
large fixed control tables supply one small transition lemma without unfolding
every branch inside each machine proof.  Separate one-phase probes exercise all
five corollaries on concrete programs.  This is **Infrastructure**, not
verifier correctness, runtime closure, or P-vs-NP mainline progress; it
unblocks the T1b destructive seek proof layer after direct unfolding exceeded
the heartbeat budget.

**T1b-A1 fixed-control activation delivered (2026-08-23, after the generic
step bridge it consumes):**
`TuringToolkit/TrueUniformSeek.lean` extends the same zero-parameter finite
control with one Boolean latch and the machine-only modes needed to create
`spent` and `cursor` markers.  The ABI and quadratic clock are unchanged, and
no runtime `Nat`, width, offset, or index enters the state or program term.
Small transition-table lemmas feed the generic `ConstStatePhasedStepBridge`;
the latch-aware validation module supplies reusable aligned right/left/stay
step adapters and proves the success/OOB handoff states are stable.

The control table is a **T1a/T1b-A fragment, not a complete T1 control**: the
T1c transitions — index-field restoration, the output write, and acceptance —
are absent from the table, not merely unproved.  No transition enters
`accept`, and no transition leaves `successStart` or `oobStart`.

The existing exact validation/rewind execution theorem still reaches the now
active `startMutation` boundary at its finite prefix time with the complete tape
unchanged.  This A1 slice is **Infrastructure** and does not yet execute cursor
installation, a unary decrement, the `j → j+1` loop, restoration, output, or
acceptance; those genuine execution theorems are isolated in T1b-A2/T1c.

**T1b-A1 review-surface hardening:** headline semantic probes in
`Tests/TMTrueUniformSeekSurfaceTests.lean` are `theorem check_*` restatements:
the forward macrostep and scan quantify the latch, and the cursor-position
probe pins the exact marker equation.  The remaining T1b-A1 `#check` entries
pin declaration existence only; their theorem bodies are covered by the
corresponding `Tests/AxiomsAudit.lean` roots.  `t1CS_frame_macrostep` and
`t1CS_scan_frames` take the latch as an explicit argument rather than an
`optParam`, so callers cannot silently select only the `latch = false` instance.
`t1MutationFrames_getElem?_cursor` puts `t1CursorFrameIndex`'s arithmetic under
the kernel.  `t1CursorBase` remains a pure bounded-layout definition; any
machine execution that reads or writes at that physical address is deferred to
the T1b-A2 slice.
The control-table bodies, the frame ABI, the clock and every pre-existing proof
are untouched: the only new content is that cursor-position theorem, and the
only signature change is the two now-explicit latch arguments.

### Session 2 — `writeVecOfNatProgram`
**File:** new
`pnp3/Complexity/TMVerifier/TuringToolkit/RowInputWriter.lean`
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
`pnp3/Complexity/TMVerifier/TuringToolkit/RowConsistencyCheck.lean`
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
`pnp3/Complexity/TMVerifier/TuringToolkit/WitnessDecoder.lean`
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
`pnp3/Complexity/TMVerifier/TuringToolkit/LengthProbe.lean`
**LOC:** ~250
**Building blocks:** `incrementProgram_correct` (doubling),
`UnaryAtOffset` for compare
**Deliverable:** `canonicalLengthCheckProgram` reads `m` from the
standard `w` slot and checks `n = 2·2^m` via walk + compare; returns
`(m, true)` or `false`.
**Acceptance:** `canonicalLengthCheckProgram_run_full` closed.

### Session 6 — Top-level composition
**File:** new
`pnp3/Complexity/TMVerifier/TuringToolkit/CanonicalVerifierTM.lean`
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
  `pnp3/Complexity/TMVerifier/GapMCSPVerifier.lean`
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

- `pnp3/Complexity/TMVerifier/TuringToolkit/BinaryCounter.lean:1315`
  — `incrementProgram_correct`
- `pnp3/Complexity/TMVerifier/TuringToolkit/CombineAtOffset.lean:1037`
  — `combineAtOffsetCS_run_full`
- `pnp3/Complexity/TMVerifier/TuringToolkit/GateWrappers.lean:5034`
  — `circuitEvaluatorCS_run_correct_wf`
- `pnp3/Complexity/TMVerifier/TuringToolkit/GateWrappers.lean:577`
  — `seqList_timeBound_le_uniform`
- `pnp3/Complexity/TMVerifier/TuringToolkit/ConstStatePhasedProgram.lean:414-544`
  — `runConfig_seq_succ_*` (for session 1)
- `pnp3/Complexity/TMVerifier/TuringToolkit/RowConsistencyCheck.lean:69,175,213`
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
