# Phase I detailed design: asymptotic NP verifier (WIP)

**Status**: Phase I of the "max-possible final" plan is approximately
30% delivered by commits `83c8892 .. b29700a` (sessions 9e-d
steps 13 – 19).  This file documents the remaining design decisions
and pinpoint technical obstacles so a future session can proceed
directly.

## What is delivered

### Infrastructure (100% ready)

- `PhasedProgram` / `toTM` / `runConfig_add` — Foundation.
- `BinaryCounter.incrementProgram k` with `incrementProgram_correct`
  (line 1903).
- `Encoding` module: `CircuitTree`, `SLProgram`, `TapeLayout`,
  `TapeMatches`, all roundtrip lemmas.
- 4 atomic primitives + 4 unary compounds + `copyAtOffsetProgram` +
  `combineAtOffsetProgram` + AND/OR/NotSrcDst specializations.
- **`ConstStatePhasedProgram S`** uniform-state restriction with:
  - `toPhased` embedding
  - `seq` combinator with 12 transition + 12 stepConfig + 10
    runConfig_succ unfolding lemmas
  - `idleCS` + `seqList` list composition
  - `seqList_timeBound_le_uniform` polynomial bound
- **`GateEvalCS`** — 5 per-SLGate wrappers (input/const/not/and/or)
  as `ConstStatePhasedProgram (Bool × Bool)` via `combineAtOffsetCS`
  specializations.
- **`evalOneGateCS`** dispatcher + **`circuitEvaluatorCS`** gates-list
  composer.

## What remains — milestone-by-milestone details

### Milestone F: `circuitEvaluatorCS_run_correct` (~800 LOC)

**Statement:**
```
theorem circuitEvaluatorCS_run_correct {n : Nat} (gates : List (SLGate n))
    (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch)
    {N : Nat}
    (c : Configuration (M := (circuitEvaluatorCS gates Δrowbase Δscratch hle).toPhased.toTM) N)
    (h_init : c is at start phase with default state)
    (h_bound : Δscratch + gates.length ≤ ...) :
    ∃ (vals : List Bool), SLProgram.evalAll gates (fun i => c.tape ⟨(c.head : ℕ) + Δrowbase + i.val, ...⟩) = some vals ∧
    ∀ (i : Fin gates.length),
      (TM.runConfig c (circuitEvaluatorCS ...).timeBound).tape
        ⟨(c.head : ℕ) + Δscratch + i.val, ...⟩ = vals[i]
```

**Difficulty**: High.  Requires induction over `gates` with careful
preservation invariants:
- Each previously-evaluated gate's tape slot MUST NOT be overwritten
  by subsequent gates.  This follows because:
  - Each gate writes at `scratch + slot`, where slot increases.
  - Previous gates at slot < current only read from their fixed
    positions; they don't write anywhere outside their slot.
  - Must formalize this "write-region-disjointness" property explicitly.

**Proof strategy**:
1. Unfold `seqList` by induction on `gates`.
2. Base case (empty list): `idleCS` is 1-phase, does nothing, tape
   unchanged, `evalAll [] x = some []`.
3. Inductive case: assume for `rest`, prove for `g :: rest`.
   - By `seqList_cons` and `seq`, first `evalOneGateCS g 0 Δrowbase
     Δscratch` runs for `evalOneGateCS.timeBound` steps.
   - Apply that gate's correctness (a direct corollary of
     `combineAtOffsetProgram_run_full`, NOT yet re-expressed for CS).
   - Then one boundary step transitions to seq's P2 region (where
     `seqList rest` lives).
   - Apply IH on the remaining gates (shifted slot +1 in each).
   - Combine via `runConfig_add` / `runConfig_succ`.

**Blocker**: each gateXCS wrapper's correctness currently exists only
via the PhasedProgram version (`combineAtOffsetProgram_run_full`).
Need to state+prove the equivalent on `(toPhased combineAtOffsetCS
...).toTM`, which is structurally identical but formally a different
TM.  Options:
- **(a)** Prove `combineAtOffsetCS.toPhased = combineAtOffsetProgram`
  via `funext` + `Fin.ext rfl` for the transition — **~150 LOC**,
  then correctness transports by `rfl` rewrite.
- **(b)** Re-prove correctness separately for CS version
  (~800 LOC mirroring combineAtOffsetProgram_run_full).

**Recommended**: Option (a).  Start milestone F with the `.toPhased =`
equality proof.

### Milestone G: `rowConsistencyCheckCS` (~500 LOC)

**Design**: compose four CS programs via `seqList`:
1. `circuitEvaluatorCS gates Δrowbase Δscratch hle` — evaluate circuit.
2. `combineAtOffsetCS (Δscratch + gates.length - 1) Δvalue Δtmp
    (fun a b => a ≠ b)` — compute XOR (mismatch).
3. `combineAtOffsetCS Δmask Δtmp Δtmp (fun a b => a && b)` — AND with
   mask (inconsistency flag for this row).
4. `combineAtOffsetCS Δtmp Δflag Δflag (fun a b => a || b)` — OR into
   global invalid flag.

**Critical ordering constraint**:
```
Δrowbase + n  ≤ Δscratch
Δscratch + gates.length  ≤ Δmask
Δmask   ≤ Δvalue
Δvalue  ≤ Δtmp
Δtmp    ≤ Δflag
```
Use `seqList [step1, step2, step3, step4]`.

**Correctness**: depends on Milestone F + 3 applications of
`combineAtOffsetProgram_run_full`.

**Issue**: `Δmask` and `Δvalue` in the real verifier depend on CURRENT
ROW INDEX, which is stored in the counter region.  They are NOT
fixed offsets.

**Resolution**: this is fundamentally a VARIABLE-OFFSET read, which
`combineAtOffsetCS` cannot do.  Two paths:

1. **Unroll the outer loop**: for each row `i = 0, …, 2^n-1`, generate
   a dedicated `rowConsistencyCheckCS_at_i` with fixed offsets
   `Δmask + i`, `Δvalue + i`.  Then `mcspVerifierProgram` becomes
   `seqList [check_0, check_1, …, check_{2^n - 1}]`.  `numPhases`
   grows linearly with `2^n = N/2` — polynomial in `N`.  **Feasible,
   but the verifier is a function of `N` at the Lean level; `toTM`'s
   phase count must be constant.**  This option requires
   `numPhases := fun N => ...`, which **the current `PhasedProgram`
   structure does not support** (`numPhases` is `Nat`, not `Nat → Nat`).

2. **Add a seek-by-counter compound**: a new ConstStatePhasedProgram
   that reads the binary counter region, computes the equivalent head
   move, and seeks the head there.  ~1000 LOC.  Removes the need for
   loop unrolling.  Makes `numPhases` constant.

**Recommended path**: Option 2 is cleaner but substantial.  Option 1
requires extending `PhasedProgram` with a size-dependent `numPhases`,
which is a foundation-level change.

### Milestone H: `rowLoopProgram n` (~600 LOC)

**Design**: wrap `rowConsistencyCheckCS` in a `while counter < 2^n`
loop, using `incrementProgram` for the step.

PhasedProgram supports this via backward transitions:
```
transition := fun i q b =>
  if i.val = LOOP_END then
    if counter_overflow then (ACCEPT_PHASE, ...)
    else (LOOP_START_PHASE, ...)   -- jump back
  else normal_transition ...
```

**Blocker**: to "check counter overflow", the program must READ the
overflow bit.  `incrementProgram` stores overflow implicitly in
phase state (phase `k+1` = accept, meaning done).  Composing
`rowConsistencyCheckCS + incrementProgram` requires observing the
resulting phase, which is NOT naturally available inside the
transition of a composed program.

**Resolution**: add an overflow detector that writes overflow to a
dedicated tape bit AFTER `incrementProgram` runs.  Then the outer loop
checks that bit.  ~200 extra LOC.

### Milestone I: `mcspVerifierProgram spec` (~800 LOC)

Top-level: combines input-shape validation + `SLProgram.decode` from
certificate + size check + `rowLoopProgram` + accept iff flag = 0.

**Critical**: needs `mcspVerifier_runTime_poly : ∀ N,
M.runTime (N + N^k + k) ≤ (N + N^k + k)^c + c`.  Concrete constants
`(c, k)`:
- Per-row cost: O(gates.length × Δtape) = O(polylog(N) × N^c) = poly(N).
- Number of rows: 2^n = N/2.
- Total: N · poly(N) = poly(N).

Can be computed explicitly once all sub-components have timeBound
bounds (we have `seqList_timeBound_le_uniform` for the backbone).

### Milestones J, K: `MCSPVerifier.lean` + public theorem (~400 LOC)

Mostly mechanical once F–I are done.

## Key technical recommendations

1. **Start with Option (a) from Milestone F**: prove
   `combineAtOffsetCS.toPhased = combineAtOffsetProgram` via `congr` /
   `Fin.ext`.  This unlocks transport of all existing compound
   correctness to the CS framework.

2. **Resolve variable-offset issue (Milestone G) early**: either extend
   `PhasedProgram` with variable `numPhases : Nat → Nat` OR add a
   `seekByCounter` compound.  This decision sets the architecture for
   the rest.

3. **Expect 4-6 more focused sessions** for Phase I completion.  Each
   milestone is independently committable once F is closed.

## Open mathematical / formalization obstacles

- **None new**: all remaining work is formalization of concepts
  already sketched in the hardness-magnification literature.  No new
  research results needed to close Phase I.
- **Milestone I's polynomial constants**: specific values for `(c, k)`
  depend on circuit-encoding scheme in `SLProgram.encode`; may need
  size-explicit analysis.

## Session 20 findings (commit `8f22b85`)

Attempted `combineAtOffsetCS_run_full` via transport from
`combineAtOffsetProgram_run_full`.  Delivered:

- `combineAtOffsetCS_toPhased_transition_eq` — funext + split_ifs
  proves the two transition functions equal.
- `combineAtOffsetCS_toPhased_toTM_step` — lifts equality through
  `toTM`'s step wrapper.

**Reverted attempt** at full `runConfig`/`run_full` transport — hits
Lean type mismatch: `Configuration (M := combineAtOffsetCS.toPhased.toTM)`
and `Configuration (M := combineAtOffsetProgram.toTM)` are NOT
definitionally equal despite having same `state`, `tapeLength`, and
`step` (via the step-eq lemma).  They are distinct structure-types
parameterized by distinct TMs.

**Implication for Milestone F path**: the step-level transport is
available but cannot be trivially lifted to `runConfig` transport via
`rfl` / `rw`.  The correctness of `combineAtOffsetCS.toPhased.toTM`
must be proven either:
- (α) From scratch, mirroring the existing 50+ lemmas in
  `CombineAtOffset.lean`'s run-invariant chain (~700 LOC), OR
- (β) Via a cast-based bridge `castConfig : Configuration (M := T1) n →
  Configuration (M := T2) n` when `T1.state = T2.state` and
  `T1.tapeLength = T2.tapeLength`, plus a theorem that `runConfig`
  commutes with this cast.  ~200 LOC of cast manipulation.

**Recommended** for next session: attempt (β), as it's a reusable
piece that helps Milestones E/F/G uniformly.

## Verification at each milestone

1. `lake build Complexity.PsubsetPpolyInternal.TuringToolkit` — green.
2. `./scripts/check.sh` — all six gates pass.
3. Axiom audit: `{propext, Classical.choice, Quot.sound}` only.
4. `#print axioms` for each new theorem — confirm no axiom leaks.

## Session history (commits on `claude/check-unconditional-requirements-cXryZ`)

| Commit | Session step | Content |
|--------|-------------|---------|
| `83c8892` | — | Refactor TuringToolkit → 9 submodules |
| `d5124a3` | 13 | 12 stepConfig_seq lemmas |
| `eb8ab63` | 14 | 10 runConfig_succ_seq derivatives |
| `3364fe4` | 15 | combineAtOffsetCS |
| `8af0f90` | 16 | 5 GateEvalCS wrappers + uniform timeBound |
| `b37c646` | 17 | idleCS + seqList |
| `e1ca9e3` | 18 | evalOneGateCS + circuitEvaluatorCS |
| `b29700a` | 19 | seqList_timeBound_le_uniform (polynomial bound) |
| `8f22b85` | 20 | combineAtOffsetCS transport lemmas (transition / step step-level eq) |
| `078fb7d` | 21 | castConfig generic + castCombineConfig specialized |
| `4a3c96e` | 22 | **Milestone β COMPLETE**: combineAtOffsetCS_run_full via runConfig commutation |
| `e7baaed` | 23 | **5 gate `*CS_run_full` correctness theorems** via combineAtOffsetCS_run_full |
| `c811260` | 24 | evalOneGateCS_writes_at_dst uniform invariant (case analysis on SLGate) |
| `7925278` | 25 | circuitEvaluatorCS base case (empty gate list) |

## Milestone F remaining work (detailed)

### Key structural blocker — seqList simulation

The core difficulty for `circuitEvaluatorCS_run_correct` is the
**seq-simulation** between the composed TM and the individual gate
TMs.  Specifically:

- `evalOneGateCS g slot` lives in its OWN TM with its own numPhases.
- `circuitEvaluatorCS gates` lives in a LARGER TM (via seqList/seq)
  with summed numPhases.
- To transport `gate*CS_run_full` (which is about the per-gate TM)
  into claims about `circuitEvaluatorCS`'s run, we need a cast
  bridge **between `evalOneGateCS.toPhased.toTM` and the seqList
  composite TM** — same shape of bridge as session 22 (castCombineConfig)
  but more general.

### Concrete remaining sub-milestones

1. **F.3a — Generic seqList cast bridge** (~300 LOC):
   `castSeqListConfig` between a gate's solo TM and its "slice"
   within `seqList`.  Uses `castConfig` from step 21 with appropriate
   state/tapeLength agreements.  Similar pattern to `castCombineConfig`.

2. **F.3b — seqList runConfig decomposition** (~200 LOC):
   `seqList_runConfig_cons` — running `seqList (p :: rest)` for
   `p.timeBound + 1 + (seqList rest).timeBound` steps equals running
   `p` alone (via cast), then boundary handoff, then `seqList rest`
   alone (via another cast).  Uses step-level seq lemmas from
   sessions 13-14 + new casts.

3. **F.3c — Preservation of prior scratch** (~150 LOC):
   Inductive invariant that gate `i`'s run writes only at
   `head + Δscratch + i`, leaving prior scratch slots untouched.
   Uses evalOneGateCS_writes_at_dst (step 24) + runConfig decomposition.

4. **F.4 — Main theorem** (~250 LOC):
   `circuitEvaluatorCS_run_correct`: for every gate index `k < gates.length`,
   `tape[head + Δscratch + k]` after run equals
   `SLGate.compute gates[k] (row-accessor) (scratch[0..k]-accessor)`.
   Induction over gates.length using F.3c's preservation.

### Session-by-session remaining

- Session A (~500 LOC): F.3a + F.3b — seqList simulation bridge.
- Session B (~400 LOC): F.3c + F.4 — main correctness via induction.

After F: Milestones G (row consistency) → H (row loop) → I
(mcspVerifierProgram + runtime) → J, K. **Estimated 5-6 more focused
sessions for full Phase I closure.**

Total Milestone F remaining: ~900 LOC across 2 sessions.
