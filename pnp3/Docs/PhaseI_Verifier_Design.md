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

1. `lake build Complexity.TMVerifier.TuringToolkit` — green.
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
- ∃-form derivations for not/and/or gate families require
  well-formedness hypotheses (these gate types aren't prior-independent).

### Session 50 — Public CS-form wrappers via definitional alias refactor

Session 50 closed the last F.4 deliverable: the public CS-form
correctness theorems `circuitEvaluatorCS_run_correct_constList` and
`circuitEvaluatorCS_run_correct_inputList`.

**The Eq.rec obstruction**.  `circuitEvaluatorCS gates = circuitEvaluatorCSAt
gates 0` is a **propositional** (not definitional) equality — the two
definitions have different structural unfoldings (`seqList ∘ mapIdx` vs
`match`).  A direct `rw [← circuitEvaluatorCSAt_zero_eq]` on a goal of
shape `CircuitEvaluatorCS_RunCorrect gates ...` fails the motive check
because the Prop body contains auto-generated proof terms (e.g.,
`CircuitEvaluatorCS_RunCorrect._proof_5`) from `by omega` blocks
establishing Fin bounds; those proof types are tied to the specific
program and cannot be abstracted uniformly over the rewrite variable.

**Resolution (Option A, chosen after Option B `rw` attempt failed)**:
refactor `CircuitEvaluatorCS_RunCorrect` as a **definitional alias**
of `CircuitEvaluatorCSAt_RunCorrect gates 0`.  In
`pnp3/Complexity/TMVerifier/TuringToolkit/GateWrappers.lean`:

```lean
def CircuitEvaluatorCS_RunCorrect {n : Nat} (gates : List (SLGate n))
    (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) : Prop :=
  CircuitEvaluatorCSAt_RunCorrect gates 0 Δrowbase Δscratch hle
```

Semantic equivalence holds: the CSAt form with `offset = 0` and
`prior = []` degenerates to the natural 3-conjunct CS statement via
def-eq (`Δscratch + 0 = Δscratch` and `[] ++ vals = vals`).  The extra
`prior` universal and preservation conjunct are conservative
generalisations that do not restrict the statement.

**Public wrappers** (both one-liners through the alias):
```lean
theorem circuitEvaluatorCS_run_correct_constList (bs : List Bool)
    (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) :
    CircuitEvaluatorCS_RunCorrect (bs.map SLGate.const) Δrowbase Δscratch hle :=
  circuitEvaluatorCSAt_constList_RunCorrect_unconditional bs 0 Δrowbase Δscratch hle

theorem circuitEvaluatorCS_run_correct_inputList (is : List (Fin n))
    (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) :
    CircuitEvaluatorCS_RunCorrect (is.map SLGate.input) Δrowbase Δscratch hle :=
  circuitEvaluatorCSAt_inputList_RunCorrect_unconditional is 0 Δrowbase Δscratch hle
```

**Downstream usage pattern**: consumers that construct a `Configuration`
for `circuitEvaluatorCS` rewrite through `circuitEvaluatorCSAt_zero_eq`
once at the term level (before any Fin-bound proofs are generated) to
reach the CSAt-at-0 form, then apply these correctness theorems.

**Verification** (session 50): `lake build` green; `check.sh` all
6 steps pass; axiom inventory unchanged (propext=349, Classical.choice=345,
Quot.sound=349).

**F.4 status after session 50**: CS-form wrappers for const/input closed;
arbitrary-gates ∃-form still outstanding.
- Conditional correctness for arbitrary gates: ✓ (session 49s).
- ∃-form for all-const lists: ✓ (session 48).
- ∃-form for all-input lists: ✓ (session 49u).
- Public CS-form wrappers (const/input): ✓ (session 50).
- ∃-form for arbitrary gates (incl. notGate/andGate/orGate, mixed): **remaining**.

### Session 51 — F.4 FULLY CLOSED for arbitrary well-formed gate lists

Session 51 closed the last F.4 gap: ∃-form unconditional correctness
for **arbitrary well-formed gate lists** (including `.notGate`,
`.andGate`, `.orGate`, and any mixture of gate types).

**Why was this the last gap?**  The all-const and all-input ∃-form
theorems exploit *prior-independence*: for those gate types,
`SLGate.compute` ignores the accumulator, so `SLProgram.evalAux`
succeeds unconditionally for any prior.  For `.notGate`/`.andGate`/
`.orGate`, `compute` reads from the accumulator, so `evalAux` may fail
on malformed lists.  The F.4 ∃-form for arbitrary gates therefore
requires a **positional well-formedness** hypothesis.

**New definitions** (in `pnp3/Complexity/TMVerifier/TuringToolkit/GateWrappers.lean`):

```lean
def SLGate_wfAtLen {n : Nat} (L : Nat) : SLGate n → Prop
  | .input _ => True
  | .const _ => True
  | .notGate k => k < L
  | .andGate k l => k < L ∧ l < L
  | .orGate k l => k < L ∧ l < L

def SLProgram_wfFromOffset {n : Nat} : List (SLGate n) → Nat → Prop
  | [], _ => True
  | g :: rest, offset =>
    SLGate_wfAtLen offset g ∧ SLProgram_wfFromOffset rest (offset + 1)
```

A gate list is well-formed starting from accumulator length `offset`
iff each gate at position `i` has all its references in `[0, offset + i)`.

**Key existence lemma** (pure SL-program statement, no TM content):

```lean
theorem evalAux_of_wf (row : Fin n → Bool) :
    ∀ (gates : List (SLGate n)) (offset : Nat) (prior : List Bool),
      prior.length = offset →
      SLProgram_wfFromOffset gates offset →
      ∃ vals : List Bool,
        vals.length = gates.length ∧
        SLProgram.evalAux row gates prior = some (prior ++ vals)
```

Proved by structural recursion on `gates` with case analysis over the
5 gate constructors; `.notGate`/`.andGate`/`.orGate` cases use the
well-formedness hypothesis to guarantee `prior[k]? = some prior[k]`
(and similarly for `l`).

**Main theorem — CSAt-form ∃-form for arbitrary gates** (via canonical prior):

```lean
theorem circuitEvaluatorCSAt_RunCorrect_wf_unconditional
    (gates : List (SLGate n)) (offset Δrowbase Δscratch : Nat)
    (hle : Δrowbase + n ≤ Δscratch)
    (hwf : SLProgram_wfFromOffset gates offset)
    {N : Nat} (c : Configuration ...) ... :
    ∃ vals : List Bool,
      vals.length = gates.length ∧
      SLProgram.evalAux row gates (canonicalPrior gates offset ...) =
        some (canonicalPrior gates offset ... ++ vals) ∧
      (∀ i, (TM.runConfig c ...).tape ⟨..., _⟩ = vals[i]?.getD false) ∧
      (∀ j, j outside write region → (TM.runConfig ...).tape j = c.tape j)
```

**Proof** (15 LOC): set canonical prior from tape, apply `evalAux_of_wf`
to obtain `vals` + `h_eval`, invoke `CircuitEvaluatorCSAt_CondCorrect_all`
with the canonical prior (using `canonicalPrior_length` and
`canonicalPrior_h_prior_match` for its hypotheses) to obtain tape and
preservation facts.

**Why `canonicalPrior` rather than universally-quantified prior?**  The
existing `CircuitEvaluatorCSAt_RunCorrect` Prop universally quantifies
over user-supplied prior without requiring it to match the tape.  For
prior-dependent gates (`.notGate`/`.andGate`/`.orGate`), a mismatched
user prior would make `evalAux` compute vals *inconsistent with the
tape* — so the Prop as written cannot hold for arbitrary gates with
arbitrary prior.  The canonical prior (derived from the tape) sidesteps
this tension entirely.

**Public CS-form at offset = 0** — the original Milestone F target:

```lean
theorem circuitEvaluatorCS_run_correct_wf
    (gates : List (SLGate n)) (Δrowbase Δscratch : Nat)
    (hle : Δrowbase + n ≤ Δscratch)
    (hwf : SLProgram_wfFromOffset gates 0)
    {N : Nat} (c : Configuration ...) ... :
    ∃ vals : List Bool,
      vals.length = gates.length ∧
      SLProgram.evalAux row gates [] = some vals ∧
      ∀ i, (TM.runConfig c ...).tape ⟨..., _⟩ = vals[i]?.getD false
```

At `offset = 0`, the canonical prior collapses to `[]` (via
`canonicalPrior_length = 0` and `List.length_eq_zero_iff`), the
`prior ++ vals = vals` simplification applies, and the 4-conjunct CSAt
conclusion reduces to the 3-conjunct CS form that matches the original
Milestone F statement (design doc lines 38–48).

**Verification** (session 51):
- `lake build` green; `check.sh` all 6 steps pass.
- Axiom inventory unchanged: propext=349, Classical.choice=345, Quot.sound=349.
- New theorem axiom dependencies (via `#print axioms`):
  - `evalAux_of_wf`: `[propext, Quot.sound]` (no `Classical.choice`).
  - `circuitEvaluatorCSAt_RunCorrect_wf_unconditional`: `[propext, Classical.choice, Quot.sound]`.
  - `circuitEvaluatorCS_run_correct_wf`: `[propext, Classical.choice, Quot.sound]`.

**F.4 status after session 51**: **CLOSED UNCONDITIONALLY for well-formed
arbitrary gate lists**.

Complete deliverables:
- Conditional correctness for arbitrary gates (session 49s, `CondCorrect_all`).
- ∃-form for all-const lists (session 48).
- ∃-form for all-input lists (session 49u).
- Public CS-form wrappers for const/input (session 50).
- **∃-form for arbitrary well-formed gates via canonical prior (session 51).**
- **Public CS-form at offset=0 matching original Milestone F target (session 51).**

**Two honest caveats** (noted in the session 51 review):

1. *Positional well-formedness is a real hypothesis, not cosmetic.*
   `circuitEvaluatorCS_run_correct_wf` requires
   `hwf : SLProgram_wfFromOffset gates 0`.  This is **mathematically
   necessary**: `SLGate.notGate k` reads `prior[k]?`, returning `none`
   when `k ≥ prior.length`, so a malformed list (e.g., `[notGate 5]`
   at `prior = []`) makes `evalAux` return `none` and the ∃-form
   theorem is false.  Well-formedness = "every gate at position `i`
   references only slots `< offset + i`" = topological order.  This is
   the minimal requirement; eliminating it would require replacing
   `Nat`-indexed references with `Fin (accumulator_length)` (a ~2000
   LOC refactor of the encoding/decoding infrastructure).

2. *The session 51 theorems are stated on `circuitEvaluatorCSAt gates 0`,
   not on literal `circuitEvaluatorCS gates`.*  The two are
   propositionally equal (via `circuitEvaluatorCSAt_zero_eq`), but at
   session 51 they were NOT definitionally equal (different structural
   unfoldings: `match` vs `seqList ∘ mapIdx`).  This means downstream
   code that constructs a `Configuration` for literal `circuitEvaluatorCS
   gates` would need a `castConfig`-based bridge or `rw` transport to
   apply the session 51 theorem — another Eq.rec-motive hazard.

Session 52 closes caveat #2 completely.  Caveat #1 is inherent to the
`SLGate` design and remains.

### Session 52 — Integration-edge closure (`circuitEvaluatorCS := circuitEvaluatorCSAt gates 0`)

Session 52 eliminates the propositional-vs-definitional gap between
`circuitEvaluatorCS gates` and `circuitEvaluatorCSAt gates 0` by
**redefining** the former as the `offset = 0` specialisation of the
latter.  The previous definition via `seqList ∘ mapIdx` is retained as
the propositional-equality lemma
`circuitEvaluatorCSAt_eq_seqList_mapIdx`.

**Edit in `pnp3/Complexity/TMVerifier/TuringToolkit/GateWrappers.lean`**:

```lean
-- OLD (session 47 era):
def circuitEvaluatorCS {n : Nat} (gates : List (SLGate n))
    (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) :
    ConstStatePhasedProgram (Bool × Bool) :=
  ConstStatePhasedProgram.seqList
    ((gates.mapIdx (fun slot g => evalOneGateCS g slot Δrowbase Δscratch hle)))

-- NEW (session 52):
def circuitEvaluatorCS {n : Nat} (gates : List (SLGate n))
    (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch) :
    ConstStatePhasedProgram (Bool × Bool) :=
  circuitEvaluatorCSAt gates 0 Δrowbase Δscratch hle
```

Structural file reordering: `circuitEvaluatorCSAt` (definition + two
`@[simp]` unfolding lemmas + `_eq_seqList_mapIdx`) moved above
`circuitEvaluatorCS` so the latter can reference the former.

**Immediate consequences**:

- `circuitEvaluatorCSAt_zero_eq gates Δrowbase Δscratch hle` becomes
  provable by `rfl` (previously a ~15-line induction).
- `Configuration (M := (circuitEvaluatorCS gates ...).toPhased.toTM) N` and
  `Configuration (M := (circuitEvaluatorCSAt gates 0 ...).toPhased.toTM) N`
  are **definitionally the same type**.  No `castConfig`, no `rw`
  transport needed.
- Every session 50–51 theorem that was stated on the CSAt-at-0 form
  now applies directly to literal `circuitEvaluatorCS`.

**Integration test** (compiled during session 52, then deleted):

```lean
example {n : Nat} (gates : List (SLGate n))
    (Δrowbase Δscratch : Nat) (hle : Δrowbase + n ≤ Δscratch)
    (hwf : SLProgram_wfFromOffset gates 0)
    {N : Nat}
    (c : Configuration (M := (circuitEvaluatorCS gates Δrowbase Δscratch hle).toPhased.toTM) N)
    (h_phase : c.state.fst.val = 0) (h_state_snd : c.state.snd = (false, false))
    (hbound : (c.head : ℕ) + Δscratch + gates.length ≤ N) (htape_clean : …) :
    ∃ vals, … :=
  circuitEvaluatorCS_run_correct_wf gates Δrowbase Δscratch hle hwf c …
```

The `c` here has type `Configuration` over the literal
`circuitEvaluatorCS` TM; it feeds directly into the session 51 theorem.

**Minor migration** within GateWrappers.lean:

- `circuitEvaluatorCS_cons` (line ~835): proof rewritten.  The old
  `rw [List.mapIdx_cons]; rfl` depended on `circuitEvaluatorCS`'s
  `seqList ∘ mapIdx` body; the new proof uses
  `circuitEvaluatorCSAt_eq_seqList_mapIdx` at `offset = 1` to re-express
  the tail.
- `circuitEvaluatorCS_nil_timeBound` and
  `circuitEvaluatorCS_nil_runConfig_zero` remain `rfl`-provable (nil
  case of CSAt is also `idleCS` by match-unfolding).
- No external files affected.

**Verification** (session 52):
- `lake build` green; `check.sh` all 6 steps pass.
- Axiom inventory unchanged: propext=349, Classical.choice=345, Quot.sound=349.
- Integration-edge test confirmed: session 51 theorems apply to literal
  `circuitEvaluatorCS` configs without any cast.

**F.4 status after session 52**: CLOSED UNCONDITIONALLY for well-formed
arbitrary gate lists, on literal `circuitEvaluatorCS gates`.  Caveat #1
(positional well-formedness is required, not a cosmetic hypothesis)
remains by design.  Caveat #2 (CSAt-at-0 integration edge) **is
eliminated**.

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
   (or a re-export in `Complexity.TMVerifier.TuringToolkit`).

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

---

## Session 53 — Milestone G architectural decision (research-only)

After closing F.4 on literal `circuitEvaluatorCS` in sessions 50–52, the
next blocker is Milestone G's variable-offset issue (design doc
lines 87–135).  This session is a research-only investigation of
design options, producing a concrete recommendation before committing
to implementation in session 54+.

### The problem, restated precisely

MCSP-verifier row consistency check reads **four** bits per row:
- `mask[i]` at tape position `head + Δmask + i`
- `value[i]` at tape position `head + Δvalue + i`
- scratch (circuit output) at `head + Δscratch + gates.length - 1`
- global invalid flag at `head + Δflag`

The row index `i` ranges `0..2^n - 1` where `n = spec.n`.  Three of the
four positions (`Δmask + i`, `Δvalue + i`, and implicitly the scratch
slot used by later rows) **depend on `i`**.

`combineAtOffsetCS Δ1 Δ2 Δdst op` takes offsets as `Nat` parameters
fixed at program-construction time.  Its `numPhases := 2 * Δdst + 4`
IS parameter-dependent (see `CombineAtOffset.lean:40`), but the
parameters must be concrete at the moment of construction — NOT
computed from tape contents at runtime.

### Options considered

**Option A — Co-located circuit evaluation**:  merge circuit evaluation
with per-row consistency check in a single pass.  Rejected: requires
either redoing circuit evaluation for each row (2^n × gates.length
work, multiplicative blowup over current 2^n + gates.length) or
interleaving input/output layouts that break the existing
`evalOneGateCS` / `circuitEvaluatorCS` scratch-region invariants.  Net
cost ≥ 1500 LOC with substantial refactor of F.4 infrastructure.

**Option B — Pre-compute circuit outputs in certificate**:  include
2^n circuit values in the certificate; verifier just checks
consistency.  Rejected: certificate size blows up by 2^n factor,
violating `circuit_bound_ok : circuitCountBound n (sNO - 1) < 2 ^
(Partial.tableLen n / 2)` in `Model_PartialMCSP.lean:27-35`.  The gap
argument breaks.

**Option C — Position-based encoding (head walks row by row)**:  use
fixed-block tape layout `[row_0 | row_1 | … | row_{2^n-1}]` where each
block is `blockSize` cells.  Head advances by `blockSize` between rows.
Eliminates variable offsets, but loses flexibility if any per-row
quantity becomes variable-size later.  ~600-800 LOC new layout lemmas.
Moderate coupling risk.

**Option D — Head = row index encoding**:  eliminate counter region
entirely; head position IS the row index modulo blockSize.  ~400 LOC
but brittle; locks tape layout.  Not recommended.

**Option E — Non-uniform family (TM per n)**:  ruled out by the
uniform-TM requirement in `NP_TM` at `Interfaces.lean:560-571`.

**Option F — Multi-tape simulation**:  adds simulation overhead
without solving the core variable-offset issue.  Rejected.

### Main contenders: Path 1 vs Path 2

**Path 1 — Loop unrolling via `List.ofFn`**:

```lean
def rowConsistencyCheckCSAt_row (spec : GapPartialMCSPParams)
    (Δmask Δvalue Δscratch Δtmp Δflag : Nat) (i : Fin (2 ^ spec.n)) :
    ConstStatePhasedProgram S :=
  ConstStatePhasedProgram.seqList [
    circuitEvaluatorCS spec.gates ... Δscratch,
    combineAtOffsetCS (Δscratch + spec.gates.length - 1) (Δvalue + i.val)
                      Δtmp ...  (· ≠ ·),
    combineAtOffsetCS (Δmask + i.val) Δtmp Δtmp (· && ·),
    combineAtOffsetCS Δtmp Δflag Δflag (· || ·)
  ]

def mcspCheckAllRows (spec : GapPartialMCSPParams) ... :
    ConstStatePhasedProgram S :=
  ConstStatePhasedProgram.seqList
    (List.ofFn (fun i : Fin (2 ^ spec.n) =>
      rowConsistencyCheckCSAt_row spec ... i))
```

For each `i : Fin (2 ^ spec.n)`, the per-row program has **fixed**
offsets `Δvalue + i.val`, `Δmask + i.val` (concrete `Nat` values once
`i` is fixed at construction).  The top-level
`mcspCheckAllRows` is a `seqList` of `2 ^ spec.n` such programs — a
`List.ofFn` over `Fin (2 ^ spec.n)`.  Total `numPhases = 2^n ·
poly(n) = poly(N)` where `N = tableLen spec.n`.

**Critical insight**: the design doc (lines 118–127) calls this a
"foundation change" requiring `numPhases : Nat → Nat`.  **This is
overstated.**  `PhasedProgram.numPhases` is already a `Nat` expression
involving parameters of the construction (see `combineAtOffsetProgram`
in `CombineAtOffset.lean:40`: `numPhases := 2 * Δdst + 4` with `Δdst`
a constructor parameter).  For a specific `spec`, `n` is concrete, so
`2 ^ spec.n` is a concrete `Nat` — the verifier IS a valid
`PhasedProgram` in the current foundation, no structural change
needed.

The concern about "the verifier is a function of `N` at the Lean
level" reflects a mis-framing: every parametric construction is a
function from parameters to PhasedProgram.  What `PhasedProgram`
genuinely cannot express is `numPhases` that depends on the *runtime
input length* (i.e., on the length of the tape at runtime).  But
MCSP's `numPhases` depends only on `spec.n`, a *construction-time
parameter* — no foundation change required.

The one genuine concern is **kernel proof-checking cost**: if we
unfold `List.ofFn` via explicit enumeration, we get a list of `2^n`
terms, which for `n = 20` is ~10^6 terms — infeasible.  The mitigation
is to reason about `List.ofFn` and `seqList` **abstractly via the
relevant induction / `getElem?` lemmas** rather than unfolding.  This
is standard Lean 4 practice and supported by the existing
`seqList_timeBound_le_uniform` proof.

LOC estimate:
- `rowConsistencyCheckCSAt_row` definition + per-row correctness (via F.4
  + 3 × `combineAtOffsetProgram_run_full`): ~250 LOC.
- `mcspCheckAllRows` composition via `seqList` over `List.ofFn` + its
  correctness by induction on `i : Fin (2 ^ spec.n)`: ~200 LOC.
- Arithmetic bounds (`2^n · poly(n) = poly(N)`): ~50 LOC.
- **Total Milestone G: ~500 LOC.**

**Path 2 — `seekByCounter` compound**:

New primitive `seekByCounterProgram counterStart counterLen Δbase` that:
1. Reads bits of a binary counter at `[counterStart, counterStart + counterLen)`.
2. Computes effective offset `offset := Δbase + counter_value`.
3. Seeks head to `head + offset`.

Used in Milestone G as:

```lean
seqList [
  seekByCounterProgram counterStart n (Δmask - counterStart),
    -- now head is at (original_head + Δmask + counter_value)
  combineAtOffsetCS 0 Δvalue' Δtmp' ...,
    -- offsets relative to new head position
  seekByCounterProgram_reverse ...,
    -- restore head to original position
  ...
]
```

LOC estimate (per design doc and Explore analysis):
- `seekByCounterProgram` definition: ~200 LOC.
- `seekByCounterProgram_correct`: ~500 LOC (similar to
  `incrementProgram_correct` + 50-lemma run-invariant chain).
- Integration with Milestone G's 4-step seqList + re-alignment
  compounds: ~300 LOC.
- **Total Milestone G: ~1000 LOC.**

### Comparison

| Criterion | Path 1 (unroll via `List.ofFn`) | Path 2 (`seekByCounter`) |
|-----------|-------------------------------|---------------------------|
| Foundation change? | No | No (new primitive in toolkit) |
| LOC | ~500 | ~1000 |
| New semantics | None (reuses existing seqList + combineAtOffset) | One new primitive family |
| Proof reuse | Maximal (leverages existing `combineAtOffsetProgram_run_full` verbatim for each row) | Partial (needs fresh run-invariant chain for seekByCounter) |
| Downstream impact on H/I | Clean: `rowLoopProgram` becomes trivial (loop body is just index `i`) | Moderate: H must thread seekByCounter invariants through the loop |
| Risk | Low (mechanical composition) | Medium (new semantics to verify) |
| Time bound proof | Direct: `seqList_timeBound_le_uniform` applied to 2^n copies of same per-row bound | Indirect: need to compose seekByCounter timeBound with combineAtOffsetCS timeBound |

### Recommendation: **Path 1**

Path 1 is **strictly dominant**: half the LOC, no new semantics, maximal
reuse of existing F.4 and `combineAtOffsetProgram_run_full`
infrastructure.  The design doc's "foundation change" concern was
overstated — no structural modification of `PhasedProgram` is needed
because `numPhases` already accepts parameter-dependent `Nat`
expressions (as `combineAtOffsetProgram.numPhases := 2 * Δdst + 4`
demonstrates).

The one real technical concern (proof-kernel cost of enumerating 2^n
terms) is mitigated by reasoning about `List.ofFn` abstractly via
existing helpers like `seqList_timeBound_le_uniform`.

### Execution plan for session 54+ (Milestone G, Path 1)

**Session 54** (~250 LOC): `rowConsistencyCheckCSAt_row` + per-row
correctness.  Definition + proof that running the 4-step seqList for a
specific `i` correctly sets the invalid flag to `(mask[i] ∧ (value[i] ≠
circuit_output[i])) ∨ prior_invalid_flag`.  Proof pattern: chain 4
existing lemmas (F.4 + 3 × `combineAtOffsetProgram_run_full`) via
`seqList` composition.

**Session 55** (~200 LOC): `mcspCheckAllRows` + correctness by
induction on `i : Fin (2 ^ spec.n)`.  Show that after processing the
first `k` rows, `invalid_flag = ⋁_{j < k} (mask[j] ∧ mismatch[j])`.

**Session 56** (~50 LOC): arithmetic bound `2^n · poly(n) = poly(N)`
for the full verifier time budget.  Uses
`seqList_timeBound_le_uniform` applied to the List.ofFn of row
checks.

### Showstoppers to monitor

1. **Kernel timeout on large `n`**: if Lean's definitional unfolding
   hits List.ofFn enumeration, specific lemmas may need `@[irreducible]`
   annotation to force abstract reasoning.  Mitigation: profile during
   session 54 and add annotations as needed.
2. **`Fin (2 ^ spec.n)` arithmetic**: working with `Fin` over
   exponential bounds may need explicit `Nat.pow` lemmas.  Mitigation:
   have a fallback to `List.range (2 ^ spec.n)` + bound hypothesis if
   `Fin` proves awkward.
3. **Scratch-region overflow between rows**: each row's scratch slots
   must not collide with the next row's mask/value positions.
   Mitigation: explicit offset hierarchy `Δscratch + gates.length ≤
   Δmask`, `Δmask + 2^n ≤ Δvalue`, etc. — similar to existing
   `hle12 : Δ1 ≤ Δ2` constraints in `combineAtOffsetProgram`.

**Fallback**: if any showstopper blocks Path 1, pivot to Path 2 within
the same sprint.  Path 2's `seekByCounter` design is documented in
lines 128–131 of the original design doc and remains implementable as
~1000 LOC fallback.

### Deliverable

This session 53 entry itself is the deliverable: no code written.
Session 54 will begin Path 1 implementation with
`rowConsistencyCheckCSAt_row`.

---

## Session 54 — Milestone G: `RowConsistencyCheck.lean` scaffold

Created new file
`pnp3/Complexity/TMVerifier/TuringToolkit/RowConsistencyCheck.lean`
implementing Path 1 of Milestone G (see session 53 design note).

**What's in the file** (~215 LOC):

1. **`rowConsistencyCheckCSAt_row`** (4-step `seqList` composition): for a
   concrete row index `i`, composes
   - `circuitEvaluatorCS gates Δrowbase Δscratch`
   - XOR with `value[i]` at `Δtmp`
   - AND with `mask[i]` at `Δtmp` (in place)
   - OR into global flag at `Δflag` (in place)

   **In-place writes are verified safe** by close reading of the
   `combineAtOffsetCS` phase layout at `CombineAtOffset.lean:19-27`:
   phase `Δ2 + 1` reads `src2` into state before phase `Δdst + 2`
   writes `dst`, so `Δ2 = Δdst` is safe (original value captured in
   state).  The agent-reported "forbids Δ2 = Δdst" concern turned out
   to be over-cautious; the `≤` constraint in the type really is `≤`,
   not `<`.

2. **`rowConsistencyCheckCSAt_row_timeBound`** — closed form:
   `(circuit timeBound) + (2·Δtmp + 3) + (2·Δtmp + 3) + (2·Δflag + 3) + 3`.
   Proved by unfolding `seqList` 4 times and applying
   `combineAtOffsetCS_timeBound`.

3. **`rowConsistencyCheckCSAt_row_timeBound_le`** — simplified bound:
   `≤ (circuit timeBound) + 6·Δflag + 15`, using `Δtmp ≤ Δflag`.

4. **`mcspCheckAllRows`** — the Path 1 loop-unroll:
   ```lean
   ConstStatePhasedProgram.seqList
     (List.ofFn (fun i : Fin (2 ^ n) =>
       rowConsistencyCheckCSAt_row gates ... i.val ...))
   ```
   For each row `i : Fin (2 ^ n)`, offsets `Δvalue + i.val`, `Δmask + i.val`
   are concrete `Nat`s; `seqList` threads all `2 ^ n` per-row checks.

5. **`mcspCheckAllRows_timeBound_le`** — aggregate bound:
   `≤ 2^n · ((circuit timeBound) + 6·Δflag + 16) + 1`, using the
   `seqList_timeBound_le_uniform` helper with uniform per-row bound.

**What's NOT in this session**:

- Per-row *semantic* correctness (the 4-step composition actually
  computes `flag' = flag ∨ (mask[i] ∧ (circuit_output ≠ value[i]))`).
  This requires threading `circuitEvaluatorCS_run_correct_wf` +
  3×`combineAtOffsetCS_run_full` through the `seqList`'s transport
  lemmas (`embedSeqConfig_runConfig_eq` etc.) — deferred to session 55.
- Row-input writing (the `n` bits representing row index `i`).
  Deferred to Milestone H's row-loop compound; `rowConsistencyCheckCSAt_row`
  assumes the row input is already on the tape.
- Tape-preservation-outside-region theorem (needed for Milestone H's
  loop invariant) — deferred to session 55.

**Verification** (session 54):
- `lake build` green; `check.sh` all 6 steps pass.
- Axiom inventory unchanged: propext=349, Classical.choice=345, Quot.sound=349.
- Per-theorem `#print axioms` — all `[propext, Classical.choice, Quot.sound]`.

**Files changed**:
- `lakefile.lean` (+1 line) — added `RowConsistencyCheck` glob.
- `pnp3/Complexity/TMVerifier/TuringToolkit/RowConsistencyCheck.lean`
  (new, ~215 LOC).

**Next (session 55)**: per-row semantic correctness for
`rowConsistencyCheckCSAt_row`.  Will compose the four correctness
theorems (F.4 WF + 3× combineAtOffsetCS_run_full) through seqList.
Also: tape-outside-region preservation.

---

## Session 55 — `FormulaSupportRestrictionBoundsPartial` falsifiability audit: quarantine + regression probe

Milestone-G implementation is paused one session while we address a
pre-existing but previously unformalized issue in the Magnification
surface: the predicate
`Magnification.FormulaSupportRestrictionBoundsPartial` in
`pnp3/Magnification/LocalityProvider_Partial.lean:200` is **formally
inconsistent** with other already-proven parts of the project.  Any
"final line" theorem consuming it is ex-falso rather than a genuine
step toward unconditional `NP ⊄ P/poly`.

### Finding (audit source)

- Audit commit: `d8a7753`, branch `claude/check-unconditional-requirements-Dg8ZQ`.
- Informal reports: `outputs/formula-support-bounds-falsifiability-audit.md`
  + `outputs/formula-support-bounds-falsifiability-audit.provenance.md`.
- External Lean probe (not committed): `/tmp/pnp3_formula_support_falsifiability_probe.lean`.

The predicate universally quantifies over *every* strict formula witness
`PpolyFormula (gapPartialMCSP_Language p)`, but the fixed-slice
language at input length `partialInputLen p` admits a truth-table
hardwired formula whose syntactic support is the entire input region —
trivially violating the polylog / quarter-support / LocalCircuitSmallEnough
bounds the predicate claims.

Formally:
- **Probe 1** (in the audit): `hBounds → ¬ PpolyDAG (gapPartialMCSP_Language p)`.
- **Probe 2** (in the audit): truth-table hardwiring proves `PpolyFormula (gapPartialMCSP_Language p)` unconditionally.
- **Probe 3** (in the audit): combining Probes 1 and 2 gives `hBounds → False`.

### Session 55 deliverables (~90 LOC)

1. **In-project regression lemma** at
   `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`:
   ```lean
   theorem fixedSlice_not_PpolyDAG_of_FormulaSupportRestrictionBoundsPartial
       {p : GapPartialMCSPParams}
       (hBounds : Magnification.FormulaSupportRestrictionBoundsPartial) :
       ¬ ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p)

   theorem false_of_FormulaSupportBounds_and_fixedSlice_PpolyDAG
       {p : GapPartialMCSPParams}
       (hBounds : Magnification.FormulaSupportRestrictionBoundsPartial)
       (hDag : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p)) :
       False
   ```
   These formalize Probe 1 of the audit using only existing
   infrastructure (`ppolyFormula_of_ppolyDAG_gapPartialMCSP_fixedSlice`
   + `abstractGapTargetedSingletonDensityPayload_of_dag` +
   `false_of_abstractGapTargetedPayload_of_supportBounds`).  Any
   future edit that silently breaks this inconsistency proof now
   triggers a `lake build` failure.

   **Probe 2 + Probe 3 port** (session 56, ~150 LOC extension of
   the same file): closed.  Added:
   - `FormulaCircuit.rename σ c` + `eval_rename` — index relabeling.
   - `ttFormula : (Bitstring n → Bool) → FormulaCircuit n` —
     recursive DNF-style construction, case-splitting on input bit 0.
   - `ttFormula_eval` — correctness via `Fin.cases_zero` / `Fin.cases_succ`.
   - `formula_size_pos` — inlined size positivity helper.
   - `fixedSlice_gapPartialMCSP_in_PpolyFormula` — Probe 2 (truth-table
     hardwiring gives a `PpolyFormula` witness at
     `partialInputLen p`).
   - `false_of_FormulaSupportRestrictionBoundsPartial p hBounds : False` —
     Probe 3, UNCONDITIONAL inconsistency witness for the predicate.

   Axiom audit of new theorems (session 56):
   - `ttFormula`: `[propext]`.
   - `ttFormula_eval`: `[propext, Quot.sound]`.
   - `fixedSlice_gapPartialMCSP_in_PpolyFormula`: `[propext, Classical.choice, Quot.sound]`.
   - `false_of_FormulaSupportRestrictionBoundsPartial`: `[propext, Classical.choice, Quot.sound]`.

   With Probe 3 now in-project as a theorem, the predicate's ex-falso
   nature is locked as a build gate: anyone who later reintroduces the
   predicate anywhere in the "final line" cannot pretend it's a
   meaningful hypothesis — `False` is one `false_of_FormulaSupportRestrictionBoundsPartial`
   call away.

   **Probes 4/5/6 (session 57, same file)** — walking the derivation
   chain up to the top-level:

   - `false_of_FormulaSupportBoundsFromMultiSwitchingContract p hMS : False`
     (Probe 4).  The A9 multi-switching contract is ALSO inconsistent:
     it universally quantifies over `∀ hFormula, ∃ ac0 F ... ∧ support
     bounds ...`, and the truth-table hardwired hFormula violates the
     embedded support bounds.  Direct consequence of Probe 3 via the
     existing `formula_support_bounds_from_multiswitching`.

   - `false_of_MagnificationAssumptions p hMag : False` (Probe 5).
     `MagnificationAssumptions` contains `hMag.switching.multiswitching :
     FormulaSupportBoundsFromMultiSwitchingContract` — ex-falso by
     Probe 4.

   - `NP_not_subset_PpolyFormula_final_via_ex_falso p hMag n hn :
     ComplexityInterfaces.NP_not_subset_PpolyFormula` (Probe 6).
     Directly derives the **same type** as the top-level final
     theorem `NP_not_subset_PpolyFormula_final` via `False.elim`.  This
     is the clearest demonstration that the top-level theorem's
     conclusion is vacuous under the current formalization — no
     mathematical content, just an ex-falso step.

   **Implication**: the migration (steps 1–4 in session 55 entry) must
   replace `FormulaSupportBoundsFromMultiSwitchingContract` as well,
   not just the downstream `FormulaSupportRestrictionBoundsPartial`.
   Both are inconsistent in the current form and both need
   AC0-provenance-taking-input variants.

2. **Prominent warning docstring** on
   `FormulaSupportRestrictionBoundsPartial` in
   `pnp3/Magnification/LocalityProvider_Partial.lean:200` (~30 lines),
   documenting:
   - The inconsistency with existing infrastructure.
   - The regression probe location.
   - The required repair (pipeline-restricted contract).
   - Affected downstream files.

### What's NOT done in this session

- **Migration of the active final line**: the ~50 call sites across
  `Magnification/FinalResult{Mainline,LegacyTM}.lean`,
  `LowerBounds/SingletonDensityContradiction.lean`, and
  `LowerBounds/DAGStableRestrictionProducer.lean` still consume
  `FormulaSupportRestrictionBoundsPartial` unchanged.  This is a
  multi-session refactor; see migration plan below.

- **Removal of the predicate**: cannot delete yet — would break ~50
  theorems.  The predicate is retained with a warning docstring while
  migration proceeds.

### Migration plan (future sessions)

**Step 1** — introduce pipeline-restricted replacement.  Define a new
predicate at the same location in `LocalityProvider_Partial.lean`:

```lean
/-- Pipeline-restricted support-bounds contract.  For formulas that
come from a specific AC0/multi-switching extraction pipeline, the
support satisfies the polylog / quarter / LocalCircuitSmallEnough
bounds.  Unlike `FormulaSupportRestrictionBoundsPartial`, this version
does NOT vacuously quantify over fixed-slice truth-table hardwiring. -/
def FormulaSupportRestrictionBoundsPartial_fromPipeline
    (pipeline : AC0LocalityBridge.FormulaSupportBoundsFromMultiSwitchingContract) :
    Prop := ...
```

**Step 2** — migrate the two consumers that directly use the predicate:
- `formulaRestrictionCertificateData_of_supportBounds`
  (LocalityProvider_Partial.lean:2202)
- `false_of_abstractGapTargetedPayload_of_supportBounds`
  (SingletonDensityContradiction.lean:623)

Give them pipeline-restricted variants.

**Step 3** — propagate through the ~50 call sites in the three
downstream files (DAGStableRestrictionProducer, SingletonDensityContradiction,
FinalResult*).

**Step 4** — delete `FormulaSupportRestrictionBoundsPartial` after all
consumers migrate.

**Step 5** — formalize Probe 2 (truth-table hardwiring → PpolyFormula)
as the final regression lemma; then delete the old predicate's
warning docstring since the predicate is gone.

Estimated effort: ~3 sessions, ~800 LOC (mostly mechanical signature
updates).

### Impact on Milestone G execution

Milestone G (started session 54) is **orthogonal** to this audit:
`rowConsistencyCheckCSAt_row` and `mcspCheckAllRows` are purely TM-level
constructions with no dependency on Magnification's support-bounds
chain.  Milestone G work can continue unchanged; the support-bounds
migration is an independent refactor on the Magnification side.

### Verification (session 55)

- `lake build` green; `check.sh` all 6 steps pass.
- Axiom inventory unchanged.
- New regression lemmas axiom-clean: `[propext, Classical.choice, Quot.sound]`.
- `Tests/FormulaSupportBoundsFalsifiabilityProbe.lean` is compiled as
  part of the default `PnP3` library, not optional — so regression is
  a build gate.
