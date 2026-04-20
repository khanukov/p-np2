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
| `8f22b85` | 20 | combineAtOffsetCS transport lemmas |
| `078fb7d` | 21 | castConfig generic + castCombineConfig specialized |
| `4a3c96e` | 22 | **Milestone β COMPLETE**: combineAtOffsetCS_run_full |
| `e7baaed` | 23 | 5 gate `*CS_run_full` correctness |
| `c811260` | 24 | evalOneGateCS_writes_at_dst uniform invariant |
| `7925278` | 25 | circuitEvaluatorCS base case |
| `90362c6` | 26 | embedSeqConfig generic seq embed |
| `90a0ca2` | 27 | embedSeqConfig_tape_at_head simp |
| `6b1776a` | 28 | stepConfig state commutation (phase + snd) |
| `b72afc5` | 29 | moveHead_stay + moveHead_left |
| `cbe518a` | 30 | moveHead_right_safe |
| `4fa4b03` | 31 | moveHead_val_commutes unified |
| `0ea5e8e` | 32 | written_bit + move commutation |
| `ec924c5` | 33 | stepConfig_components summary |
| `990f9bd` | 34 | stepConfig_state_eq (Σ-level) |
| `a896f7c` | 35 | stepConfig_head_val commutation |
| `ccddb7c` | 36 | head_val via embed |
| `3dce1ec` | 37 | stepConfig_head_in_P1 range invariant |
| `426f18e` | 38 | stepConfig_tape_out_of_range |
| `41625c9` | 39 | tape in-range (both head cases) |
| `8bc6cb0` | 40 | **stepConfig_tape_eq full funext** |
| `6e3be75` | 41 | **stepConfig_eq FULL Configuration equality** |
| `639243e` | 42 | **runConfig_eq multi-step induction** |

## Milestone F status (updated after step 42)

### CLOSED (steps 22-42)

- **β: Cast bridge** — combineAtOffsetCS_run_full transported.
- **F.1: Per-gate correctness** — all 5 gate CS wrappers.
- **F.2: Uniform writes_at_dst** — evalOneGateCS case analysis.
- **F.3: Seq simulation bridge** (the former blocker):
  - `embedSeqConfig` definition + all @[simp] infrastructure.
  - All component step-commutations (state / head / bit / move).
  - Full `stepConfig_eq` Configuration equality.
  - **Multi-step `runConfig_eq` induction** — the keystone.

### F.4 PROGRESS — sessions 43-46 (Chunks 1, 2, 2b, 3)

**New infrastructure (+~1030 LOC, 4 commits):**

- **Session 43 (Chunk 1)** — invariants for prefix runs:
  - `combineAtOffsetProgram_phase_head_at_step`: at step `s ≤ 2*Δdst+3`,
    phase = s and head ∈ [c.head, c.head + Δdst].  Case analysis on the
    5 phase blocks (seek-to-src1 / src2 / dst / write / seek-back).
  - `combineAtOffsetCS_run_invariants_in_prefix`: the three run-invariants
    (phase in range, phase ≠ accept, Move.right head-safe) at every prefix
    step.  Transported from program-level via `castCombineConfig_runConfig`.
  - `evalOneGateCS_run_invariants_in_prefix`: the uniform 5-variant
    wrapper over SLGate (input / const / notGate / andGate / orGate).

- **Session 44 (Chunk 2)** — past-boundary commutation:
  - `combineAtOffsetCS_in_seq_run_past_boundary`: after `P1.timeBound + 1`
    seq-steps (P1's prefix + 1 boundary handoff), the composed config has
    phase = `P1.numPhases + P2.startPhase.val`, state.snd = `P2.startState`,
    head and tape matching `embedSeqConfig P1 P2 cP1final`.

- **Session 45 (Chunk 2b)** — lift to evalOneGateCS:
  - `evalOneGateCS_in_seq_run_past_boundary`: uniform 5-gate wrapper.

- **Session 46 (Chunk 3)** — full P2-region embedding (~437 LOC):
  - `seq_tapeLength_ge_P2`: P2's tape embedded in seq's.
  - `embedSeqP2Config`: embed P2-config into seq-config at phase
    `P1.numPhases + P2.phase`; head preserved; tape padded with false
    in the extra `P1.timeBound + 1` slack cells.
  - Basic simp lemmas (state / head / tape variants).
  - MoveHead commutation (stay / left / right_safe / val_commutes).
  - Per-component step commutation (phase, state.snd, written_bit,
    move, head_val).  Notable difference from P1 side: *no* "not
    accept" condition — seq.transition in P2 region is exactly
    P2.transition with phase shift (no boundary special-case).
  - Per-position tape commutation + full tape equality via funext.
  - Sigma state equality + Fin head equality → full `stepConfig_eq`.
  - Multi-step `embedSeqP2Config_runConfig_eq` via induction.

**All architectural blockers for F.4 are now cleared.**  The main
theorem `circuitEvaluatorCS_run_correct` can be assembled from:
- Chunk 1 (invariants) — prove `embedSeqConfig_runConfig_eq`
  hypotheses for the gate-0 prefix run.
- Chunk 2 + 2b (past-boundary) — get from start-of-composed-run to
  just-past-the-boundary of gate 0.
- Chunk 3 (P2-embedding) — transfer the tail's standalone
  `seqList rest.mapIdx ...` run into the seq's P2 region.

### REMAINING (F.4 — main theorem)

**`circuitEvaluatorCS_run_correct`** (~200-300 LOC).  Pure mechanical
induction on `gates` combining the above chunks.

Structure:
```lean
theorem circuitEvaluatorCS_run_correct {n : Nat} (gates : List (SLGate n))
    (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) {N : Nat}
    (c : Configuration (M := (circuitEvaluatorCS gates ...).toPhased.toTM) N)
    (h_init : c is at program's start state)
    (h_bound : enough tape + phase bounds) :
    ∃ (vals : List Bool),
      SLProgram.evalAll gates (row-accessor c) = some vals ∧
      ∀ (i : Fin gates.length),
        (runConfig ... (timeBound ...)).tape
          ⟨c.head.val + Δscratch + i.val, _⟩ = vals[i]
```

Proof method (mechanical now):
1. Induction on `gates` list.
2. Base case (empty): `seqList []` is `idleCS`; tape unchanged; evalAll [] = some [].
3. Inductive case (g :: rest):
   a. First `evalOneGateCS g 0` runs within its own P1 range of the composed TM.
      Apply `embedSeqConfig_runConfig_eq` (step 42) to translate to g's solo run.
   b. Apply g-specific correctness (step 23) to get scratch[0] = gate output.
   c. Boundary step: phase jumps to `(seqList rest-shifted)`'s start.
      Apply `stepConfig_seq_P1_boundary_*` (step 13).
   d. By IH on `rest`, remaining gates produce correct scratch[1..].
   e. Tape-region-disjointness shows gate 0's scratch[0] isn't overwritten.

**Tools available for F.4 (all in Lean):**
- ✅ `embedSeqConfig_runConfig_eq` (step 42): P1-prefix commutes with embed.
- ✅ `stepConfig_seq_P1_boundary_*` (step 13): handoff semantics.
- ✅ `runConfig_tape_eq_outside_range` (Foundation): tape preservation.
- ✅ All 5 `gate*CS_run_full` (step 23): per-gate output correctness.
- ✅ `evalOneGateCS_writes_at_dst` (step 24): uniform write invariant.

**No remaining architectural blockers.**  F.4 is pure mechanical induction + combination of existing lemmas.

### Session 47 — F.4 scaffold + toolkit hygiene

Delivered in this session:

1. **F.4 target statement fixed** — a named `Prop` definition
   `CircuitEvaluatorCS_RunCorrect gates Δrowbase Δscratch hle` in
   `TuringToolkit/GateWrappers.lean` (below `circuitEvaluatorCS_nil_*`)
   packaging the exact conclusion of F.4.  Base-case theorem
   `circuitEvaluatorCS_nil_run_correct` is proved: the empty-gate-list
   evaluator satisfies the property vacuously.  The tape-index bound
   proofs inside the Prop's row-accessor and scratch-accessor closures
   use `by omega` fed by `hle`, `hbound`, `i.isLt`, and `c.head.isLt`,
   so no `sorry`/`admit` placeholders are needed.
2. **Detailed proof-strategy doc-block** (~30 lines) immediately before
   the Prop definition spells out the induction structure, the four
   already-built bridge lemmas (with exact file paths and line
   numbers), the auxiliary list-level invariant lemma, and the
   `List.mapIdx` unfolding caveat with two resolution options.
3. **Toolkit hygiene** — 64 linter warnings in
   `TuringToolkit/*.lean` eliminated (deprecated `List.get?` →
   `[·]?`, `Option.map_some'` → `Option.map_some`, dead
   `have`/`simp`-arguments, unused hypotheses renamed to `_`, and the
   `[Inhabited S]` variable scoped into a dedicated
   `section IdleSeqList` block).  `./scripts/check.sh` remains green,
   axiom inventory unchanged (`propext = 349`, `Classical.choice = 345`,
   `Quot.sound = 349`).

### Session 47b — F.4 induction scaffold

Added in the continuation of session 47 to prepare the ground for the
main F.4 proof:

1. **`circuitEvaluatorCS_cons`** — unfolds
   `circuitEvaluatorCS (g :: rest) Δrowbase Δscratch hle` into
   `seq (evalOneGateCS g 0 …) (seqList (rest.mapIdx (fun slot g' =>
   evalOneGateCS g' (slot + 1) …)))` via the Lean stdlib's
   `List.mapIdx_cons`.  Closes the `mapIdx`-offset unfolding caveat
   flagged in the F.4 strategy doc-block.
2. **`circuitEvaluatorCSAt gates offset`** — explicit-recursion variant
   of the evaluator in which the slot offset is a visible parameter.
   Comes with `_nil / _cons` simp lemmas, `_cons_timeBound` and
   `_cons_numPhases` simp lemmas (arithmetic for the induction step),
   and `circuitEvaluatorCSAt_zero_eq` which certifies
   `circuitEvaluatorCSAt gates 0 = circuitEvaluatorCS gates`.
3. **`circuitEvaluatorCSAt_eq_seqList_mapIdx`** — offset-generalised
   equivalence to the `seqList (mapIdx …)` form, proven by induction
   on `gates` using `List.mapIdx_cons` and
   `ConstStatePhasedProgram.seqList_cons`.

With this helper in place, the remaining F.4 proof can:

- Induct on `gates` at the level of `circuitEvaluatorCSAt gates offset`
  with `offset` generalised in the IH (so the shift on the tail aligns
  automatically).
- Transfer the final result to `circuitEvaluatorCS` via
  `circuitEvaluatorCSAt_zero_eq`.

This removes the architectural friction of `List.mapIdx` offset
threading from the future F.4 proof, leaving only the mechanical
application of the existing bridge lemmas (`embedSeqConfig_runConfig_eq`,
`evalOneGateCS_in_seq_run_past_boundary`,
`embedSeqP2Config_runConfig_eq`, `evalOneGateCS_writes_at_dst`) and the
list-level invariants helper.  Both `./scripts/check.sh` and axiom
inventory remain unchanged.

### Session 47 — audit: old `Simulation.lean` vs. TuringToolkit

Findings:

- The legacy `pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean`
  (~9 000 LOC) and its satellites (`StraightLine.lean`,
  `StraightLineBuilder.lean`, `StraightLineSemantics.lean`,
  `TreeToStraight.lean`) build a **TM → straight-line DAG circuit**
  compilation and a non-uniform simulation theorem
  `runtime_spec_of_stepCompiledProvider`.
- The new `TuringToolkit/*` build **phased-program abstractions** for
  synthesising polynomial-size MCSP-verifier components
  (top-down from spec).
- No cross-imports between the two hierarchies.  `Simulation.lean`
  references neither `TuringToolkit.*`, nor vice-versa.
- Only overlap: both define a tree-of-gates type.  Legacy:
  `Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit` (constructors `var /
  const / not / and / or`).  Toolkit:
  `Pnp3.Internal.PsubsetPpoly.TM.Encoding.CircuitTree` (constructors
  `input / const / not / and / or`).  Structurally identical, only
  constructor names differ (`var` vs. `input`).
- Recommendation: **NO replacement in this session.**  The two systems
  are **complementary**, not redundant: legacy extracts worst-case
  circuit families bottom-up from a TM; toolkit composes verifier
  phases top-down from spec.  The duplicate `Circuit` / `CircuitTree`
  is the only candidate for unification, but it would require
  constructor renaming across ~60+ call sites in legacy Simulation
  proofs with no functional gain — deferred as pure code-hygiene
  optimisation (not blocking Phase I).

## Overall Phase I remaining

- **Milestone F**: ~300 LOC (F.4 only).
- **Milestone G** (row consistency + variable offsets): ~1000 LOC + arch decision.
- **Milestone H** (row loop): ~600 LOC.
- **Milestone I** (mcspVerifier + runtime): ~800 LOC.
- **Milestone J+K** (MCSPVerifier.lean + wire-in): ~400 LOC.

**Total Phase I remaining: ~3 100 LOC.**

After F closure, main technical question shifts to Milestone G's variable-offset problem (the other foundation-level architectural question).
