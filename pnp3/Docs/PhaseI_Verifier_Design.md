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

### Session 47c — offset-generalised correctness Prop

Extended the F.4 scaffold with the **offset-generalised** form that
the future induction will target directly:

- `CircuitEvaluatorCSAt_RunCorrect gates offset Δrowbase Δscratch hle` —
  offset-parameterised correctness property.  Adds an explicit `prior
  : List Bool` accumulator (matching `SLProgram.evalAux`'s threading)
  and puts the scratch-region index at `Δscratch + offset + i.val` so
  the `+ 1` shift on the tail aligns with the helper's recursion.
- `circuitEvaluatorCSAt_nil_run_correct` — base case for the
  offset-generalised Prop: empty list, trivial evalAux (`prior ++ []`),
  vacuous `∀ i : Fin 0`.

Kept the interaction with `CircuitEvaluatorCS_RunCorrect` as an
inline note rather than a packaged bridge lemma: the offset-zero
specialisation is straightforward to apply at the call site via
`rw [← circuitEvaluatorCSAt_zero_eq]`, but a generic bridge lemma
stumbles on `Configuration`-typed hypothesis transport through a
propositional equality between two `ConstStatePhasedProgram`s.  This
is fine — future-session invocations know their local goal shape and
can drive the rewrite directly.

### Session 47l–47z — Full induction factored, tape facts as premises

Session 47l–47z produced a sequence of incremental wins culminating in the
**factored all-const theorem**:

```lean
theorem circuitEvaluatorCSAt_constList_RunCorrect_from_tape_facts (bs offset ...)
    (h_tape_slot : ∀ c ..., composite.tape at slot i = bs[i]?.getD false)
    (h_preservation : ∀ c ..., tape at j outside scratch = c.tape at j) :
  CircuitEvaluatorCSAt_RunCorrect (bs.map SLGate.const) offset ...
```

This theorem **unconditionally proves the full 4-conjunct Prop for any
`bs`**, conditional ONLY on the 2 tape facts.  Length + evalAux conjuncts
are proved internally via `constList_length` + `evalAux_constList`.

Demonstrations via factored theorem:
- `circuitEvaluatorCSAt_constList_RunCorrect_empty_via_factored`: empty
  list (47y).
- `circuitEvaluatorCSAt_constList_RunCorrect_single_via_factored`:
  single-gate (47z), extracting `vals = [b]` from the existing const
  theorem via `evalAux` uniqueness.

Additional primitives committed:
- 47l: Configuration-level post-boundary = embedSeqP2Config(lift).
- 47m: Safety invariant via head-bound (trivially proved: Fin.isLt +
  runConfig_head_val_le).
- 47n: Full composite run = embedSeqP2Config(P2.run lift tR).
- 47o: Strengthened Prop with preservation conjunct.
- 47u: lift head value equals c head value.
- 47v: evalAux_constList — pure semantic fact.
- 47w: constList_length + witness slot lookup.

The remaining work: discharge the 2 tape facts (`h_tape_slot` and
`h_preservation`) for arbitrary bs by induction on bs.  Given that this
factoring DEPENDS on no ∃-complication, the cons-step proof is now a
∀-form induction (simpler than the original 4-conjunct ∃ form), though
still requires careful config-lifting for the cons case.

### Session 48 — FULL UNCONDITIONAL CONST-LIST CORRECTNESS PROVED

Sessions 48a–48h closed F.4 for all-const lists via a sequence of
focused compiler-driven increments.  The culminating theorem is

```lean
theorem circuitEvaluatorCSAt_constList_RunCorrect_unconditional
    (bs : List Bool) (offset Δrowbase Δscratch : Nat)
    (hle : Δrowbase + n ≤ Δscratch) :
    CircuitEvaluatorCSAt_RunCorrect (bs.map SLGate.const) offset ...
```

**No `bs.length ≤ 1` or any other length restriction**.  No axioms.
All 6 `check.sh` steps pass with axiom surface unchanged:
propext=349, Classical.choice=345, Quot.sound=349.

Proof outline:

Sessions 48a–48d built arithmetic helpers:
- **48a**: `cons_const_P1_tapeLength_le_P2_tapeLength_nonempty` and
  `cons_const_lift_head_plus_tR_lt_tapeLength` — the two lift-safety
  arithmetic facts for the cons-nonempty step.
- **48b**: `cons_const_nonempty_composite_run_tape_at` — the packaged
  decomposition:
  `composite.runConfig c T = embedSeqP2Config P1 P2 (P2.runConfig lift P2.timeBound)`,
  existentially quantified over the witnesses `hphase_lt`, `hhead_lt`,
  `h_tG_head`.
- **48c**: `cons_const_nonempty_lift_tape_clean` — lift's tape is
  clean outside N, via gate write_other + projectSeqP1 identity.
- **48d**: `cons_const_nonempty_lift_preconditions` — bundled
  IH-preconditions for the lift config.

Sessions 48e–48f proved the two tape facts:
- **48e**: `cons_const_nonempty_preservation_fact`.  Four sub-cases
  by position: j in P2's range × j in P1's range.  Uses IH
  preservation + gate P1's write_other + projectSeqP1 identity.
- **48f**: `cons_const_nonempty_tape_slot_fact`.  Two cases by
  i.val: slot 0 (via gate write_self + IH preservation); slot ≥ 1
  (via IH slots + evalAux_constList uniqueness).

Session 48g combined both facts via the factored theorem
(`circuitEvaluatorCSAt_constList_RunCorrect_from_tape_facts`) to
give `_cons_nonempty` for `(b :: b' :: bs'').map SLGate.const`.

Session 48h wired up the full induction on `bs`:
- **nil**: `circuitEvaluatorCSAt_nil_run_correct`.
- **[b]** (single-gate): `circuitEvaluatorCSAt_const_RunCorrect`.
- **b :: b' :: bs''** (non-empty tail): inlines the factored
  theorem body (`refine ⟨b :: b' :: bs'', ...⟩`) with the two tape
  facts from 48e, 48f.

Session 48i notes: the public CS-form wrapper
`circuitEvaluatorCS_run_correct_constList` requires Eq.rec transport
across `circuitEvaluatorCSAt_zero_eq` (dependent-type motive).  This
mechanical transport is deferred.  Downstream callers apply
`circuitEvaluatorCSAt_constList_RunCorrect_unconditional` at the
desired offset (typically 0).

Cumulative LOC added across 48a–48i: ~800 lines of focused proofs
in `GateWrappers.lean`.  No sorry/admit/axiom additions.

### Session 49 — Generic infrastructure + conditional correctness for ANY gate type

Session 49 extended the const-only framework to arbitrary gates
(const/input/notGate/andGate/orGate) via uniform helper theorems.
All 5 gate types are now handled via a single dispatch point in
`evalOneGateCS_writes_compute_result` (49a).

**Proved (for ANY gate type, no sorry/admit)**:

- `circuitEvaluatorCSAt_run_correct_cond_nil` (49g): empty gate list.
- `circuitEvaluatorCSAt_run_correct_cond_single` (49i): SINGLE gate
  of any type.  ~200 LOC combining projectSeqP1, past-boundary,
  `evalOneGateCS_writes_compute_result`, write_self, write_other.
- `circuitEvaluatorCSAt_run_correct_cond_short` (49k): unified for
  `gates.length ≤ 1` with any gate type.  Uses
  `SLProgram_evalAux_cons_split` to extract v from h_eval.
- `evalAux_inputList` (49m): pure semantic fact (analog of
  evalAux_constList).

**Infrastructure helpers (all gate-polymorphic)**:

- `evalOneGateCS_writes_compute_result` (49a): uniform write
  semantics.  For any gate g, the TM writes exactly `g.compute row prior`
  provided prior matches the scratch tape and compute returns some.
- `evalOneGateCS_run_preserves_head` (49b): uniform head preservation.
- `cons_any_P1_tapeLength_le_P2_tapeLength_nonempty` (49c).
- `cons_any_lift_head_plus_tR_lt_tapeLength` (49c).
- `cons_any_nonempty_composite_run_tape_at` (49d): generic
  decomposition theorem.
- `cons_any_nonempty_lift_tape_clean` (49e).
- `cons_any_nonempty_lift_preconditions` (49e): bundled IH preconds.
- `SLProgram_evalAux_prior_prefix` (49j): evalAux output structure.
- `SLProgram_evalAux_cons_split` (49j): extract v + vals_rest from h_eval.
- `rowFromConfig` + `rowFromConfig_bounds` (49g): row function abstraction.

**Cumulative session 49**: ~1400 LOC.  No sorry/admit/axiom additions.
All 6 `check.sh` steps pass.  Axiom inventory unchanged:
propext=349, Classical.choice=345, Quot.sound=349.

### Session 49q–49u — F.4 CLOSED for arbitrary gates (Sessions 49q–49u breakthrough)

Using the web-searched `termination_by gates.length` pattern (Mario
Carneiro's Lean community recipe), session 49q–49u delivered:

**Session 49q**: Mathematical formulation — defined
`CircuitEvaluatorCSAt_CondCorrect` as a single predicate on gate lists,
plus `_nil` and `_single` case theorems.

**Session 49r**: `CircuitEvaluatorCSAt_CondCorrect_cons_multi` — the
multi-gate cons step, ~180 LOC combining decomposition + IH + slot-0
via the 49n-49p helpers.

**Session 49s**: 🎉 `CircuitEvaluatorCSAt_CondCorrect_all` — FULL
unconditional conditional correctness for ARBITRARY gate lists of ANY
length, composed of ANY gate types (const/input/notGate/andGate/orGate):

```lean
theorem CircuitEvaluatorCSAt_CondCorrect_all (gates : List (SLGate n)) :
    CircuitEvaluatorCSAt_CondCorrect gates := by
  match gates with
  | [] => CondCorrect_nil
  | [g] => CondCorrect_single g
  | g :: g' :: rest' =>
    CondCorrect_cons_multi g g' rest' (CondCorrect_all (g' :: rest'))
termination_by gates.length
```

This is the DEFINITIVE mathematical F.4 correctness theorem.

**Session 49t–49u**: Derivation helpers:
- `canonicalPrior` (49t): extracts prior matching c's tape.
- `circuitEvaluatorCSAt_inputList_RunCorrect_unconditional` (49u): ∃-form
  for all-input gate lists, derived from `CondCorrect_all` + `canonicalPrior`
  + `evalAux_inputList`.  Parallel to session 48's all-const version.

**F.4 closure status**:
- ∀ gates (any type, any length): `CondCorrect_all` proves correctness
  conditionally on prior consistency.
- All-const lists (session 48): ∃-form `CircuitEvaluatorCSAt_constList_RunCorrect_unconditional`.
- All-input lists (session 49u): ∃-form `circuitEvaluatorCSAt_inputList_RunCorrect_unconditional`.

**Remaining as future work** (not blocking):
- Public CS-form wrapper `circuitEvaluatorCS_run_correct` via
  `circuitEvaluatorCSAt_zero_eq` transport (Eq.rec motive issue on
  auto-generated Fin proofs; downstream callers use the CSAt-0 form).
- ∃-form derivations for not/and/or gate families require
  well-formedness hypotheses (these gate types aren't prior-independent).

### Session 47f — F.4 architecture breakthrough (const case PROVED in Prop form)

Delivered the first fully Prop-form proof of `CircuitEvaluatorCSAt_RunCorrect`
for a non-empty gate list.  Closes the architectural uncertainty around
transporting P1-config-based concrete theorems to arbitrary
composite-configs.

**Infrastructure added in `ConstStatePhasedProgram.lean`**:

- `projectSeqP1 P1 P2 c hphase hhead : Configuration P1 N` — the
  inverse of `embedSeqConfig`.  Extracts the P1-config from a
  composite-config with phase and head in P1 range.
- `embedSeqConfig_projectSeqP1 c ... htape_outer` — identity:
  `embedSeqConfig P1 P2 (projectSeqP1 c ...) = c` under the assumption
  that `c`'s tape outside `P1.tapeLength` is all `false`.  Proved via
  structural `Configuration.mk` case analysis + `Sigma.ext` on state +
  `funext` + `dif` on tape.

**Prop refinements in `GateWrappers.lean`**:

- `hbound` strengthened to `c.head + Δscratch + offset + gates.length ≤ N`
  (was: `≤ tapeLength`).  Universal form that makes the tail-run IH
  applicable and simplifies arithmetic in the composite-to-P1 lift.
- New `htape_clean` premise: `∀ i, N ≤ i.val → c.tape i = false`.
  Encodes the canonical "scratch zero-initialised" form typical of
  MCSP verifier use.  Discharge strategy at the call site: the MCSP
  verifier constructs initial configs with tape = input bits in
  `[0, n)` and `false` elsewhere, so positions ≥ N are trivially
  `false`.

**Theorem** (in GateWrappers.lean):
```lean
theorem circuitEvaluatorCSAt_const_RunCorrect (b : Bool)
    (offset Δrowbase Δscratch hle) :
    CircuitEvaluatorCSAt_RunCorrect [SLGate.const b] offset
      Δrowbase Δscratch hle
```

**Proof recipe** (composite-to-P1 lift):
1. Derive `hphase_lt : c.state.fst.val < P1.numPhases` from `h_phase = 0`.
2. Derive `hhead_lt : c.head.val < P1.tapeLength N` from `hbound` using
   the composite/P1 tapeLength relationship.
3. Derive `htape_outer` (tape = `false` past `P1.tapeLength`) from
   `htape_clean` (tape = `false` past `N`) since `P1.tapeLength ≥ N+1`.
4. Project `c` to `c_P1` via `projectSeqP1`.
5. Apply `embedSeqConfig_projectSeqP1` to get `embedSeqConfig P1 P2 c_P1 = c`.
6. Apply `circuitEvaluatorCSAt_const_run_correct` (P1-config form) on `c_P1`.
7. Transport tape result back to `c` via `hembed ▸` (propositional
   substitution).
8. Handle `i : Fin 1` via pattern match + `Fin.ext`-based index matching.

**Public theorem aliases added**:
- `circuitEvaluatorCS_run_correct_nil` — empty gates.
- `circuitEvaluatorCSAt_run_correct_const` — single-gate const case in
  the offset-generalised form.

**Scope & path forward**:
The const case is a direct stepping stone to the multi-gate induction.
The same composite-to-P1 recipe handles the head gate in a cons case;
the tail-segment handling (via `embedSeqP2Config_runConfig_eq`) and
IH assembly close the remaining gap.  Extending to `[input i]` follows
the same pattern but with an existential `h_src` to transport alongside
the tape value.

### Session 47e — single-gate case proved (concrete F.4 demonstrator)

Proved the **single-gate case** of F.4 for two gate types as concrete,
self-contained theorems in `TuringToolkit/GateWrappers.lean`:

- `circuitEvaluatorCSAt_const_run_correct` — for `gates = [SLGate.const b]`.
- `circuitEvaluatorCSAt_input_run_correct` — for `gates = [SLGate.input i]`.

Both take a **P1-config** (of `evalOneGateCS g offset Δrowbase Δscratch
hle`) rather than a composite-config, side-stepping the
composite-arbitrary-tape issue noted in the 47d blueprint.  The proof
pattern is identical across both:

1. Apply `evalOneGateCS_in_seq_run_past_boundary` with `P2 := tail`
   (= `circuitEvaluatorCSAt [] (offset+1) …` = `idleCS`) to evaluate
   the composite over `tG + 1 = 2*(Δscratch+offset) + 4` steps.
2. `composite.timeBound N = 2*(Δscratch+offset) + 4` since tail's
   `timeBound = 0` (from `idleCS`).
3. `embedSeqConfig_tape_in_range` reduces the embed's tape at the
   scratch position to P1's post-run tape at that position.
4. Apply the per-gate correctness
   (`gateConstCS_run_full` / `gateInputCS_run_full`) → P1's tape at
   the scratch position is `c_P1.write _ value _`; use
   `Configuration.write_self` to read back `value`.

**Why this is a genuine F.4 milestone**: validates that the entire
prefix-and-boundary sub-proof — the `embedSeqConfig_runConfig_eq`
(implicit inside past-boundary) + per-gate correctness +
`embedSeqConfig_tape_in_range` + `write_self` chain — composes
correctly.  The multi-gate induction reuses this exact pattern for
the head gate, with the additional tail-segment handling (via
`embedSeqP2Config_runConfig_eq`) overlaid on top.

**Why the other three gate types aren't proved here**: `notGate`,
`andGate`, `orGate` at `slot = 0` reference non-existent prior slots
(0 values have been computed yet), so `SLProgram.evalAux` returns
`none` — the Prop shape `∃ vals, evalAux = some vals ∧ …` is false
for them in isolation.  These cases become valid in the multi-gate
induction's tail where the gate's slot is ≥ 1 and prior slots are
populated.

**Scope of this milestone**: ~110 LOC added to `GateWrappers.lean`.
All proofs axiom-clean (`{propext, Classical.choice, Quot.sound}`).
`./scripts/check.sh` green.

### Session 47d — downstream audit + F.4 induction blueprint

Audited the downstream consumers of `circuitEvaluatorCS_run_correct`
in Phase I / MCSP verifier route to confirm the target Prop shape is
aligned with how the theorem will actually be consumed.

**Audit findings**:

- Milestones G (row-consistency check) / H (row loop) / I (top-level
  verifier program) all need the tape-slot correctness form:
  "after running `circuitEvaluatorCS gates ...` for its full
  `timeBound`, `scratch[i]` equals the i-th computed gate value for
  all `i < gates.length`."
- `AsymptoticFormulaTrackData.asymptoticNP_TM` (FinalResultMainline.lean:58–70)
  requires a TM correctness witness that wraps an inner verifier.  The
  MCSP verifier's correctness reduction to F.4 is documented but not
  yet implemented (Milestones J, K).
- The Prop shape in `CircuitEvaluatorCS_RunCorrect`
  (GateWrappers.lean:964) matches exactly what downstream wants:
  `∃ vals, evalAux gates row = some vals ∧ ∀ i, scratch[i] = vals[i]`.
  *No reformulation needed.*

**F.4 induction blueprint** (target for the next dedicated session,
~400-600 LOC):

1. **Strengthen `hbound`** in both `CircuitEvaluatorCS_RunCorrect` and
   `CircuitEvaluatorCSAt_RunCorrect` from
   `c.head.val + Δscratch + offset + gates.length ≤ composite.tapeLength N`
   to `c.head.val + Δscratch + offset + gates.length ≤ N`.  This is
   universally applicable (any program's `tapeLength N ≥ N + 1`) and,
   crucially, makes the tail-run bound `c.head.val + Δscratch +
   (offset+1) + rest.length ≤ (circuitEvaluatorCSAt rest
   (offset+1)).tapeLength N` derivable from the cons-level hypothesis
   — without it, the induction step can't apply IH.
2. **Well-formedness premise**.  Add `hwf : ∃ vals, SLProgram.evalAux
   row gates prior = some vals` (equivalently, gates reference only
   prior slots).  Required because malformed gates make the Prop
   trivially false (∃ vals, evalAux = some vals is impossible).  The
   downstream MCSP verifier generates well-formed gates by construction
   (via `SLGate.decode` + `SLGate.wellFormedUnder`), so this premise
   is discharged at the call site.
3. **Induction structure** (on `gates`, generalising `offset`):
   * Base `gates = []`: already proved
     (`circuitEvaluatorCSAt_nil_run_correct`).
   * Step `gates = g :: rest`:
     * Unfold via `circuitEvaluatorCSAt_cons` → `seq (evalOneGateCS g
       offset) (circuitEvaluatorCSAt rest (offset+1))`.
     * Split run via `runConfig_add`:
       `timeBound = tG + tR + 1` where `tG = 2*(Δscratch+offset)+3`,
       `tR = (circuitEvaluatorCSAt rest (offset+1)).timeBound N`.
     * Prefix segment (`tG` steps): apply `embedSeqConfig_runConfig_eq`
       with safety from `evalOneGateCS_run_invariants_in_prefix` to
       reduce to a standalone `evalOneGateCS g offset` run.  Apply
       `combineAtOffsetCS_run_full` (or `gate*CS_run_full` per-gate):
       obtain `scratch[offset+0] = (evalGate g row)`,
       `cfinal.head = c.head` (head returns to start), phase at
       `evalOneGateCS.acceptPhase`.
     * Boundary segment (1 step): apply
       `evalOneGateCS_in_seq_run_past_boundary`.  Composite config now
       has phase = `P1.numPhases + 0`, state.snd = `P2.startState`,
       head = `c.head`, tape = `embedSeqConfig`-padded `P1`-run.
     * Tail segment (`tR` steps): apply `embedSeqP2Config_runConfig_eq`.
       **Tape alignment subtlety** — the post-boundary composite tape
       is in `embedSeqConfig` form (P1-padded), but
       `embedSeqP2Config_runConfig_eq` expects `embedSeqP2Config`
       (P2-padded).  Resolution: construct a "lifted" P2-config
       `c'` whose tape equals `c`'s tape restricted to
       `P2.tapeLength N`; then prove the composite's post-boundary
       tape agrees with `embedSeqP2Config P1 P2 c'` on all indices
       relevant to the tail's head movement (which stays within
       `P2.tapeLength N` by Milestone F safety invariants).  This
       alignment argument is ~100 LOC and the crux of F.4's novelty.
     * Combine: outer's `i = 0` uses gate 0's write (preserved through
       boundary + tail since tail's head stays in
       `[c.head+Δscratch+offset+1, c.head+Δscratch+offset+gates.length+1)`
       — proved via `runConfig_tape_eq_outside_range`
       (Foundation.lean:436)).  Outer's `i ≥ 1` uses IH on `rest` at
       `offset+1`.
4. **Specialisation** via `circuitEvaluatorCSAt_zero_eq` — rewrite
   `circuitEvaluatorCS gates` to `circuitEvaluatorCSAt gates 0` at the
   call site; apply the offset-generalised theorem.
5. **Public alias** — after the induction is proved, expose
   `theorem circuitEvaluatorCS_run_correct : ∀ gates …, hwf →
   CircuitEvaluatorCS_RunCorrect gates …` in `GateEvalCS` namespace
   (or a re-export in `Complexity.PsubsetPpolyInternal.TuringToolkit`).

**Why this is multi-session work**: the tape-alignment argument (point
3, tail segment) requires constructing the lifted P2-config, proving
its equivalence to the post-boundary composite config on all
relevant indices, and managing the dependent-type casts through
`ConstStatePhasedProgram` propositional equalities.  Careful
step-by-step work with iterative compilation check needed; attempting
blind without intermediate compile passes risks unbounded regression.

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
