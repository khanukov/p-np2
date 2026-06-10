# TM-verifier construction strategy (NP-verifier track, Phase 5)

> **Status: design note, not code.** This document maps the construction of the verifier
> Turing machine required by `PrefixExtensionNPWitness` onto the existing
> `pnp3/Complexity/TMVerifier/TuringToolkit/` toolkit. **No Turing machine is built here, and
> no NP-membership / lower-bound / `P ≠ NP` claim is made.** It exists so the subsequent
> TM-construction bricks can be built in the right order against a fixed plan.

## 1. What must be produced

`PrefixExtensionNPWitness (parser)` (`PrefixExtensionNPWitness.lean`) requires:

* `M : Pnp3.Internal.PsubsetPpoly.TM.{0}`,
* exponents `c k : Nat`,
* `runTime_poly : ∀ n, M.runTime (n + certificateLength n k) ≤ (n + certificateLength n k)^c + c`,
* `correct : ∀ n (x : Bitstring n), PrefixExtensionLanguage parser n x = true ↔
    ∃ w : Bitstring (certificateLength n k), TM.accepts (M:=M) (concatBitstring x w) = true`.

PR 1 (`TreeMCSPPrefixSemanticVerifier.lean`) already proved the *semantic* equivalence at `k = 1`

```
PrefixExtensionLanguage (treeMCSPConcretePrefixParser threshold codec) N query = true
  ↔ ∃ cert, treePrefixSemanticAccepts codec N query cert = true
```

So the **only** remaining mathematical content of `correct` is a single bridge lemma

```
accepts (M:=M) (concatBitstring x w) = treePrefixSemanticAccepts codec n x w        (★)
```

after which `correct n x` is `(treePrefixSemanticAccepts_correct codec n x).trans` composed with
`exists_congr (fun w => by rw [★])`, and `k := 1`. **The TM track's job is exactly: build `M`,
prove (★), and bound `M.runTime`.**

## 2. TM model facts that constrain the design

From `pnp3/Complexity/PsubsetPpolyInternal/TuringEncoding.lean`:

* single tape, binary alphabet (`false` = blank), `state : Type` finite with `DecidableEq`;
* `runTime : ℕ → ℕ` is a **declared field** (an asserted bound), not computed from `step`;
* `run x = runConfig (initialConfig x) (M.runTime n)` runs for **exactly `runTime n` steps**;
* `tapeLength n = n + M.runTime n + 1` — the scratch space available *is* the runtime budget;
* `initialConfig x` loads the input into cells `[0, n)`, head at `0`, rest blank;
* `accepts n x = decide ((run x).state = M.accept)`.

**Consequences for the build:**

1. There is no "halt"; the machine always runs `runTime n` steps. A program must reach its
   `accept` *phase/state* and then **idle there** (every atomic program already does this).
2. `runTime` must be chosen `≥` the actual work and idle out the remainder; the polynomial bound is
   proved against this chosen closed form.
3. All scratch is within `[input length, tapeLength)`; offsets must stay `< tapeLength`, which holds
   because `tapeLength = inputLen + runTime + 1` and `runTime` is generous.

## 3. Reusable toolkit inventory

`pnp3/Complexity/TMVerifier/TuringToolkit/` (≈14.6k lines):

| Piece | What it gives | Reuse |
|-------|---------------|-------|
| `Foundation.lean` | `PhasedProgram`, `toTM` (transparent `step`/`accept`/`runTime`), `runConfig_zero/succ/add`, tape-preservation lemmas (`runConfig_tape_eq_outside_range`), head bounds (`runConfig_head_val_le`, `…_ge_of_never_left`), `TMNeverMovesLeft` | direct |
| `ConstStatePhasedProgram.lean` | uniform-state programs, `seq` / `seqList`, **additive** `timeBound` (`seq_timeBound : … = t1 + t2 + 1`), `seqList_run_decomp` | direct |
| `AtomicPrograms.lean` | `seekRightProgram`/`seekLeftProgram`/`readBitProgram`/`writeBitProgram` + full `runConfig` lemmas | direct |
| `UnaryAtOffset.lean` | `readAtOffsetProgram`/`writeAtOffsetProgram` (seek-read/write-return, time `2Δ+1`) | direct |
| `CopyAtOffset.lean`, `CombineAtOffset.lean`, `GateWrappers.lean` | copy a bit between offsets; 2-input gate-at-offset (`and`/`or`/`not`/`input`/`const`) with full correctness | direct, for per-gate circuit evaluation |
| `BinaryCounter.lean` | `incrementProgram k`, `counterValue` (little-endian) semantics + bounds | direct, for the row index |
| `Encoding.lean` | `CircuitTree` encode/decode (`decodeCircuitTreeAtDepth`), `decodeFin`, round-trips | reference for the *on-tape* decoder |
| `RowConsistencyCheck.lean` | verifier-specific row consistency checking (to be leveraged for the per-row compare) | partial |

## 4. Tape layout

Input is `concatBitstring query cert`, length `L = N + certificateLength N 1 = N + (N+1)`, where a
well-formed `query` has length `N = treeMCSPPrefixM codec n = tagLen + gammaLen n + tableLen n +
idxWidth … + witnessBits n` and `tableLen n = 2^n`.

```
[0 .............................. N) [N ........................ 2N+1)   [2N+1 ........ tapeLength)
  query (tag|gamma(n)|x[2^n]|idx|p)    cert (witness[witnessBits]|pad)     scratch (row idx, gate regs)
```

The scratch region (row counter of `n` bits, gate-evaluation registers, decoded-circuit area) lives
above the input, inside the `runTime` budget.

## 5. Phase decomposition (the program)

Assembled as a `seqList` of sub-programs (each idles in its accept phase; a rejecting check routes to
a non-accept sink phase that idles):

1. **Tag check** — read the `tagLen`-bit tag field, compare to `treePrefixTag`. `readAtOffset` + a
   small compare state. Reject ⇒ sink.
2. **Gamma-decode `n` + locate fields** — scan the Elias-gamma block to recover `n` and the field
   offsets. *Data-dependent length* ⇒ needs a bounded scan loop (see §6).
3. **Length-convention check** — verify the input length equals `treeMCSPPrefixM codec n`. Arithmetic
   on decoded `n`.
4. **Witness slice** — the first `witnessBits n` bits of `cert` are the witness; copy into a scratch
   register (or address them in place).
5. **Prefix agreement** — for each `t < i`, compare `cert[t]` to the query's prefix field bit `p[t]`.
   Bounded loop over `i ≤ witnessBits n` bits (see §6).
6. **Codec verification** — decode the tree circuit from the witness on tape
   (`decodeCircuitTreeAtDepth` realized as a tape program), check `size ≤ threshold n`, and **evaluate
   the circuit over all `2^n` truth-table rows**, comparing each output bit to `x`. Reject ⇒ sink.

Step 6's per-row work reuses `GateWrappers` (one gate program per circuit gate, chained by `seqList`);
the row loop and the gamma scan are the parts the current toolkit does **not** yet support.

## 6. Bounded-loop primitive `repeatProgram` — **BUILT** (`BoundedLoopProgram.lean`), but see the correction

`seq`/`seqList` are straight-line (no back-edges) and `numPhases` is a literal `Nat`.  Built as:

* `ConstStatePhasedProgram.repeatProgram body k := seqList (List.replicate k body)`;
* `repeatProgram_timeBound : (repeatProgram body k).timeBound n = k * body.timeBound n + k`;
* `repeatProgram_succ` (one peel, `rfl`), `repeatProgram_run_succ` (per-iteration run decomposition),
  `repeatProgram_timeBound_le` (uniform bound).

> **Critical correction (re-derived this session — supersedes the earlier "no back-edge needed"
> claim).** `repeatProgram body k` has `numPhases = k · |body|` *phases*, so `k` must be a literal
> fixed at **program-definition time**.  The verifier `M : Pnp3.…TM.{0}` is **one fixed TM** (fixed
> finite state set), quantified *outside* `correct : ∀ n, …`; its row loop must iterate `2^m` times
> where `m` is **decoded from the input at runtime**.  You therefore *cannot* write
> `repeatProgram body (2^m)` inside `M` — `2^m` is not known at definition time, and a fixed `M`
> cannot have an input-dependent phase count.  **Input-dependent iteration in a single fixed TM
> requires a genuine back-edge** (a fixed loop-body block re-entered via a transition that reads a
> tape counter / row index, terminating when it reaches `2^m`), i.e. a transition mapping a phase
> *backward*.  The same applies to *variable-length scans*: the gamma block length `gammaLen m`
> grows (slowly) without bound in the input, so the gamma scan in `M` must be a **self-loop** (one
> scan phase re-entering while it reads `0`), not a fixed-`maxIters` straight-line program.
>
> **What this does and does not invalidate.**  `repeatProgram` and the `maxIters`-parameterized
> `gammaZeroScanProgram` are *correct programs* with *correct* lemmas, and they directly serve any
> processing whose width is a **true compile-time constant** — e.g. the tag check (`tagLen = 8`).
> They are also valid *reasoning devices* for a fixed unrolling.  But they do **not** compose into the
> single fixed `M` for the **data-dependent** fields/loops (gamma length, `2^m` truth-table rows).
> The genuinely missing fundamental primitive is a **back-edge / self-loop loop construct** (fixed
> phase count, runtime-counted iteration) — neither the toolkit's straight-line combinators
> (`seq`/`seqList`/`seekRight`/`repeatProgram`) nor anything built so far provides it.  Bricks 2
> (gamma), 5 (rows), and the parse orchestration depend on building it first.

### 6a. Composition reasoning layer — **BUILT** (`BoundedLoopProgram.lean`)

The toolkit proved each composed program (`combineAtOffsetProgram`, …) *monolithically*; the generic
seam was missing.  Now built (NP-verifier track), feeding the loop/assembly invariants:

* `repeatProgram_timeBound_le` — uniform per-iteration bound `≤ k·(B+1)` (the `k=2^n`, `B=poly n`
  ⇒ `poly L` shape `runTime_poly` is discharged against);
* `seq_neverMovesLeft` / `seqList_neverMovesLeft` (+ `idleCS`) — `TMNeverMovesLeft` is preserved by
  composition, so a `seqList` of right-only/stay phases is right-only/stay;
* `seqList_runConfig_head_bounds` — head stays in `[c.head, c.head+j]` during a composed run
  (offset-validity within the `tapeLength` budget);
* **complete single-step `seq` simulation** `seq_stepConfig_{P1_normal,P1_accept,P2}_{phase,state,tape,head}`
  — one `stepConfig` of `seq P1 P2` described entirely by the component transitions, across all three
  regions (P1-normal, the P1→P2 handoff, P2).  This is the per-step backbone a concrete composed
  program uses to prove its intrinsic run invariant.

**Cross-type caveat (why there is no *generic* run-simulation).**  `(seq P1 P2).toTM` and `P1.toTM`
have different `runTime`, hence different `tapeLength`, hence different `Configuration` types — so
"seq's run = P1's run" is not even type-correct to state.  Each concrete phase therefore proves its
*own* intrinsic invariant on the composed TM, consuming the single-step lemmas region-by-region (the
tag-check's `runConfig_scan`/`accepts_eq_tagMatch` is the worked template).

**Composition-survival worked for a self-loop — DONE** (`TreeMCSPCounterComposition.lean`).  The
per-instance lift is now demonstrated end-to-end for the **increment as the first component** of a
composition `seq selfLoopIncrement P2` (generic `P2`): the composition single-step carry/stop/handoff
lemmas, the carry-ripple run invariant (`selfLoopIncrement_seq_runConfig_carry`), the `counterValue + 1`
correctness at the completion step (`selfLoopIncrement_seq_runConfig_counterValue`), and the run-level
P1→P2 handoff (`selfLoopIncrement_seq_runConfig_handoff`: after `j+2` steps control sits at `P2`'s
shifted start with the counter incremented and the tape stable).  This is concrete evidence that a
proven self-loop primitive *retains its semantics when embedded as a `seqList` phase*, plus the
reusable template (mirror the standalone proof, swap in the `seq_stepConfig_*` single-steps, adjust the
now-`P2`-dependent `tapeLength` arithmetic) for lifting the scan and decrement the same way.

The template is now applied to the **whole self-loop family** (`TreeMCSPCounterComposition.lean`,
`TreeMCSPScanComposition.lean`): the increment (carry-ripple + `counterValue+1` + handoff), the
**scan** (`gammaSelfLoopScan_seq_runConfig_{scanning,terminator,handoff}` — a *different* shape:
no-write scan + locate), and the **decrement** (borrow-ripple + `counterValue = after+1` via the dual
`counterValue_first_one_diff`).  So every self-loop `M` needs is proven to survive composition as a
`seq`'s first phase, with control handed to `P2` carrying the right tape.

**State-type-uniformity finding (key open assembly point).**  `seq`/`seqList` are parameterized by a
*single fixed* state type `S` (both components must share it), and the toolkit ships **no** state-lift /
state-relabel combinator.  But `M`'s phases do **not** currently share `S`: the tag check is
`ConstStatePhasedProgram Bool` (it tracks "prefix matches tag so far"), while the self-loops are
`ConstStatePhasedProgram Unit`.  So before the phases can actually be `seqList`-composed into `M`, one
of: (a) pick a common `S` for all phases (e.g. carry the tag-check's `Bool`, or a richer record) and
define each phase over it; (b) add a `mapState`/`relabel` combinator
(`(S → S') → ConstStatePhasedProgram S → ConstStatePhasedProgram S'`) with a proved `toTM`
simulation, then lift each phase; or (c) re-express the tag check over `Unit` (phase-encoding the
match state).  The self-loops ignore their state component (`transition := fun i _ b => …`), so (a)/(b)
are natural — but this is a genuine design decision, recorded here for the next assembly step (not
rushed).

**State-uniformity — RESOLVED via option (c)** (`TreeMCSPTagCheckUnit.lean`).  The common state is fixed
to **`Unit`**, and the tag check is re-expressed over `Unit` by *phase-encoding* the match state:
`tagCheckProgramU` advances on a match, jumps to a dedicated **reject sink** phase `tagLen + 1` on a
mismatch, and idles at the accept phase `tagLen` / the sink.  Fully proven: `timeBound`, never-left,
single-steps, a unified run invariant (phase `= k` iff `tagMatchPrefix x k`, else sink), and the
end-to-end `tagCheckProgramU_accepts_iff` (accepts ⟺ leading `tagLen` cells match `treePrefixTag`,
reusing the `Bool` version's `tagMatchPrefix_eq_true_iff`).  Consequently **all phases are native
`Unit`** and compose directly: `mSkeletonU` (`TreeMCSPSkeletonComposition.lean`) is the genuine
M-leading-phases skeleton (tag check ; gamma scan ; counter) over `Unit`, never-left and
polynomially-time-bounded with **no lifting/bisimulation**.  This supersedes the lifted route
(`liftUnitProgram`/`mSkeletonDemo`, retained as a demonstration); the run-bisimulation is no longer on
the critical path.

### 6b. Gamma-scan TM — design analysis (next-session entry point)

The gamma field at `[tagLen, tagLen + gammaLen n)` is `0^z 1 b₁…b_z` with `z = bitLength(n+1) − 1`
and `gammaLen n = 2z + 1`; the suffix `1 b₁…b_z` is the `(z+1)`-bit big-endian of `n+1`.  The *pure*
decode is fully proven (`decodeGamma_gammaBit`, fuel-sufficient `decodeGammaAux_gammaBit_from_at`,
`gammaBit_zero_prefix`/`_terminator`/`_payload_eq_natBitBE`); the open work is realizing it on the TM.

**Preconditions now in place** (this session): `gammaLen_le_treeMCSPPrefixM`
(`tagLen + gammaLen n ≤ N`, so the scan stays in the query), `queryXOffset_le`/`queryIdxOffset_le`,
and `instanceSize_lt_treeMCSPPrefixM` (`n < N`, with `2^n ≤ N` ⇒ **`n` logarithmic in `N`**, so a
candidate `n` and a `bitLength N`-bit counter fit in the input).  Loop primitive (`repeatProgram`),
proven counter (`incrementProgram_correct`), and composition single-step layer (§6a) all ready.

**Status (this session): the gamma terminator is now *located within the full chain*.**
`tagCheckThenGammaScanTerminator_runConfig` (`TreeMCSPLeadingPhasesChain.lean`) runs
`seq tagCheckProgramU gammaSelfLoopScan` from the initial config through tag-verify ▸ handoff ▸
zero-scan ▸ terminator, leaving the head resting *exactly on the gamma terminator* (`tagLen + z`),
phase `tagLen + 3`, tape unchanged.  That is the launch point for the payload read — so the
right-only composition infrastructure is complete *up to* the terminator.

**Core difficulty (the right-only ceiling).**  The model is *single-tape, binary alphabet* (no marker
symbols).  Reading the `z`-bit payload (`readNatBE y (offset+z+1) z` in `decodeGammaAux?`) means
stopping after *exactly* `z` bits, where `z` is data-dependent and unbounded — impossible with finite
state and a right-only head: the machine would have to either re-read the consumed zero-prefix
(**leftward** travel) or hold `z` in its state (unbounded).  The *same* ceiling blocks the
**prefix-agreement compare** (it must interleave reads of the instance's prefix `p` and the
certificate's witness `w`, which sit in *separate* tape regions → back-and-forth).  So the next major
investment is **bidirectional head primitives** (relax `neverMovesLeft`; add a left-scan / rewind with
a `0`-floored head and a lower-bound head-position invariant; re-derive the composition layer for
two-way motion) — a sizeable new toolkit, on par with the right-only layer this PR built.  Until then
the gamma payload read, the prefix compare, and (separately, upstream) the row loop remain open.  This
is the documented `0ⁿ1ⁿ`-on-one-tape awkwardness, made precise.

**First bidirectional brick DONE:** `selfLoopScanLeft` (`TreeMCSPScanLeftProgram.lean`) — the
fundamental *leftward motion* primitive, the exact dual of `gammaSelfLoopScan` (scan **left** over
`0`s, stop on the first `1`; `Move.left` decrements the head, clamped at `0`).  Fully proven through
its run behaviour: `selfLoopScanLeft_runConfig_scanning` (leftward scanning invariant, `j ≤ c0.head` so
each step genuinely decrements) and `selfLoopScanLeft_runConfig_terminator` (a verified "return left to
the nearest `1`-marker": from head `h`, an all-`0` window `(k, h]` with a `1` at `k` stops the scan on
the marker after `(h − k) + 1` steps).  It never moves *right* (`selfLoopScanLeft_transition_move`, the
dual confinement).  This is a low-level motion primitive (not a premature decode program — §6b's
warning is about committing a high-level *gamma-decode program* before its design is settled, not about
basic motion), and is the first verified building block of the bidirectional layer.

**Straight-line composition of leftward phases already works** (no new toolkit): the `seq_stepConfig_*`
single-step lemmas are *transition-generic* (they never assume `TMNeverMovesLeft`), so the leftward
scan composes as a `seq` phase exactly as the rightward one — `selfLoopScanLeft_seqP2_runConfig_scanning`
and `selfLoopScanLeft_seqP2_runConfig_terminator` give it **full composition-API parity** with
`gammaSelfLoopScan` (standalone scanning+terminator, composed scanning+terminator).  So the bidirectional
*motion* layer is built.

**Two-sided head accounting is also DONE** (`TreeMCSPBidirHeadBounds.lean`): the head moves by at most
one cell per step in *either* direction, so `runConfig_head_val_ge` (`c.head − j ≤ head`, the
direction-agnostic lower bound, no `neverMovesLeft`) and `runConfig_head_dist_le`
(`c.head − j ≤ head ≤ c.head + j`) replace the right-only monotone-head confinement.  So the entire
bidirectional **foundation** — motion primitives (both directions, composing) **plus** the kinematic
head budget — is now built and verified.

**Remaining is the data-dependent core (design-first):** the **counted payload read** (recover `n`) and
the **prefix-agreement compare**, built atop both directions of motion + the counters (`selfLoopIncrement`
/`Decrement`) + the head budget.  These are the §6b candidate realizations to settle (layout: where the
scratch counter lives in the `tapeLength = inputLen + runTime + 1` budget; how the read head and counter
interleave) and prove next — design-first, since a wrong high-level program is worse than an honest
pause.  Then the row loop (separately upstream-blocked on `circuitEvaluatorCS_run_correct`) and final
assembly.

**Two candidate realizations** (decide and prove one next session; do *not* commit a program before
the design is settled — a wrong artifact is worse than an honest pause):

1. **Candidate-search** over `m ∈ [0, N)` (loop bound `N` via `repeatProgram`, justified by
   `instanceSize_lt`): a scratch counter holds the candidate `m` (incremented per iteration by the
   proven `incrementProgram`); the body tests whether the gamma block equals `gammaBit m` for all
   `gammaLen m` cells, recording the first match.  *Pro:* each per-candidate comparison is against a
   counter-known value; *con:* computing `gammaBit m` on tape from the counter is itself a sub-build.
2. **Head-carried scan + counter:** scan the unary zeros keeping the head at the scan position (so
   `z = head − tagLen` is *implicit* in the head); a scratch counter mirrors `z`; then read the
   `z`-bit payload.  *Pro:* direct; *con:* the payload read and field-end location need
   data-dependent seeks between scan and counter regions.

Either path is multi-brick (program + `timeBound` + `neverMovesLeft` + single-step + scan invariant +
correctness against `decodeGamma?`), mirroring the tag-check's ~10-lemma build but harder.

### 6c. Counted read / row loop — the shared bottleneck, with the bidirectional toolkit complete

The bidirectional foundation is now built: rightward scan (`gammaSelfLoopScan`) **and** leftward scan
(`selfLoopScanLeft`), both with full P1/P2 composition parity; variable-width binary increment/decrement;
and direction-agnostic head-displacement bounds (`TreeMCSPBidirHeadBounds`: `|head − c.head| ≤ j`).
Working the counted payload read through against these primitives surfaces a precise architectural
conclusion:

* **Scratch region.** `tapeLength L = L + runTime L + 1`, so positions `[L, tapeLength)` are blank in
  the initial config (`initial_tape_blank`) and untouched by the parse phases (their tape-unchanged
  lemmas). With `L = Θ(2^n)` and `runTime L = Θ(L)`, the scratch is `Θ(2^n)` cells — large enough to
  hold the row count `2^n` itself.
* **Both remaining data-dependent items reduce to one construct.** The counted payload read (read `z`
  bits, `z` = the implicit head offset) and the row loop (iterate `2^n` times) are both a **bounded
  body-reentry loop**: run a multi-phase body, decrement a counter, test the counter against `0`, and
  re-enter the body on non-zero (the phased model permits the back-edge — the body's last phase jumps
  to its first). The counter *step* (±1) is proven (`selfLoop{Increment,Decrement}`); the missing
  pieces are the **counter-zero test** and the back-edge wiring.
* **The counter-zero test is the genuine crux (marker-free binary alphabet).** Testing whether a
  *binary* counter is `0` requires scanning its bits — but delimiting a *variable-width* binary counter
  needs an end marker, which the binary alphabet lacks; a fixed machine cannot hardcode the width
  (it must serve all `n`). This is the same self-delimiting wall as the gamma field.
  - **Promising direction: unary counters in scratch.** A **unary** counter (a block of `1`s followed
    by blanks) is marker-free: zero-test = "leftmost cell is `0`" (one read), decrement = "flip the
    rightmost `1`" (a leftward scan to the first `1`, already built). The row count `2^n` fits in the
    `Θ(2^n)` scratch, so a unary row counter is feasible and sidesteps the width-delimiting problem.
    The cost is the `Θ(2^n)`-length counter, but the row loop is already `Θ(2^n)` iterations, so this
    is within the intended `poly(L)` budget.
* **Bounded body-reentry loop combinator — now BUILT** (`TreeMCSPRepeatBody.lean`): `repeatBody B`
  wraps a body `B` with a conditional **back-edge** (the toolkit's first back-edge to a *multi-phase*
  body), and `repeatBody_runConfig_iterate` proves it runs `B` exactly `K` times where `K` is a unary
  counter's value — control returns to `B`'s start, the head retreats `K` cells, and the `K` ticks
  clear to `0`.  Decomposed and verified as: definition + loop-control single-steps (consume / halt /
  handoff) + `repeatBody_runConfig_one_iteration` (the inductive step) + the `K`-fold
  `repeatBody_runConfig_iterate`.  The body's behaviour enters as an **intrinsic** hypothesis on
  `(repeatBody B).toTM` (`sB` steps from `B.start` reach `B.accept`, head/tape-preserving) — so no
  cross-instance bisimulation with `B.toTM`; a caller discharges it per-instance.  Resolves the
  positioning question via **option 1** (head-preserving body; the counter cell is the body's start
  cell, read at the decide phase).  The counter half it rests on (`selfLoopCountdownLeft`) is likewise
  complete.  **So the entire bounded-loop control infrastructure — counter + combinator — is built and
  verified.**

  **Remaining to *use* the combinator** (the data-dependent core proper):
  - discharge the intrinsic body hypothesis **per-instance** for a concrete body (re-derive `B`'s
    `sB`-step run-through on `(repeatBody B).toTM`), and **generalise the tape clause** for a *writing*
    body (the current run-`K`-times assumes a tape-preserving / read-only body; an accumulating body
    changes the work region too);
  - the two real bodies — the **counted gamma-payload read** (recover `n`) and the **prefix-agreement
    compare** — each a body program + its per-iteration behaviour, plus materialising the loop counter
    (the leading-zero count `z`, resp. the prefix length) as a unary block in scratch;
  - the **row-loop body** (single-row circuit evaluation) stays separately upstream-blocked on
    `circuitEvaluatorCS_run_correct` (§9);
  - then the final **assembly** of `M`, its `runTime_poly`, the `accepts = treePrefixSemanticAccepts`
    bridge, and the `PrefixExtensionNPWitness`.

The control infrastructure is done; the next coding is the per-instance body discharge + the real
data-dependent bodies (the writing-body tape generalisation of the combinator is the smallest next
brick, then a concrete body).

### 6d. Concrete gamma-payload-read pipeline (settled this session, grounded in the built primitives)

The data-dependent core's first item — recover `n` from the gamma field — now has a *concrete*
algorithm (not just §6b's candidates), built on the verified primitives:

* **Layout.** After `gammaSelfLoopScan` the head rests on the terminator `p_term = tagLen + z`; the `z`
  leading zeros occupy `[tagLen, p_term)` and the `z` payload bits `[p_term+1, p_term+1+z)`, with
  `n + 1 = 2^z + payload` (big-endian).  `tagLen` is a **constant** (so position `tagLen` is markable by
  a fixed-phase counter), and `gammaLen_le_treeMCSPPrefixM` keeps the whole field in-bounds.
* **Two-pointer read (`O(z²)`, polynomial since `z = Θ(log L)`).** The `z` leading zeros are themselves
  a unary count of `z` — use them as the loop counter.  Loop body (driven by `repeatBody`, one pass per
  leading zero): from the left pointer (a leading zero), scan **right** (`gammaSelfLoopScan`-style) to
  the next unread payload bit, read it, shift-accumulate it into an `n`-register in scratch
  `[L, tapeLength)` (the increment/decrement counters do the `×2 + bit`), then scan **left**
  (`selfLoopScanLeft`) back to the next leading zero (consumed via `selfLoopCountdownLeft`).  Head travel
  per pass is `O(z)`, total `O(z²)` — well within `poly(L)`.  This is the **writing body** that motivates
  the combinator's tape-clause generalisation (the body writes the `n`-register; it preserves the
  leading-zero counter region).
* **Downstream pipeline** (each a later brick): `n → 2^n` row counter by a **doubling loop** (`n`
  passes, each doubles a unary block in scratch — `O(2^n) = O(L)` total), then the **row loop**
  (`repeatBody` over the `2^n` counter) whose *body* is the upstream-blocked single-row circuit eval.

**First concrete brick:** the combinator's writing-body tape generalisation (now well-specified by the
read body above — the body preserves cells `≤ head`, i.e. the counter region, and writes only the
scratch `n`-register), then the shift-accumulate read body + its per-instance hypothesis discharge.

**Built so far (this session) and a re-check caveat for the next pass.**  The counter materialization is
done: `gammaSelfLoopFill` (standalone + seqP2) and `tagCheckThenGammaFill_runConfig` (tag verify ▸ fill,
on the composed machine) turn the gamma leading zeros into a length-`z` block of `1`s in place.
**However**, re-checking its downstream use exposed a design constraint: the fill makes
`[tagLen, p_term]` *contiguous* `1`s (the `z` filled zeros **and** the terminator `1` merge), which
**erases the terminator boundary** between counter and payload.  A two-pointer shuttle that needs to
*locate* the payload from a counter cell can no longer find that boundary by scanning.  So the shuttle's
counter representation must be settled first — options: (a) keep the terminator as a boundary (don't fill
*over* it; the fill already stops *at* it, so the boundary 1 is intact — the issue is only that the
filled zeros are now also 1s, indistinguishable from the terminator when scanning rightward); (b) use a
*symmetric* two-pointer anchored at the (still-known) terminator position `p_term = tagLen + z` rather
than scanning for it (the counter cell `p_term − j` and payload cell `p_term + j` are symmetric, and `j`
is tracked by the combinator's consumed-count); (c) materialize the counter in scratch instead of in
place.  `gammaSelfLoopFill` remains a correct, reusable primitive regardless; this caveat only governs
how the *shuttle* consumes it.  Settling (a)/(b)/(c) is the design step before the payload-read body.

**Motion vocabulary completed this pass (`TreeMCSPScanLeftOneProgram.lean`).**  Independent of which
of (a)/(b)/(c) wins, every candidate shuttle must traverse **`1`-blocks** (a filled or consumed
loop-counter), not just the `0`-blocks the existing scans cover — e.g. re-anchoring at the left
boundary of a `gammaSelfLoopFill`-materialized counter means travelling *left over `1`s* to the first
`0`.  `selfLoopScanLeftOne` supplies exactly that: the bit-dual of `selfLoopScanLeft` (self-loop **left
over `1`s**, stop on the first `0`), proven to full run-behaviour + P1/P2 composition parity
(`selfLoopScanLeftOne_runConfig_{scanning,terminator}` and the `seqP2` analogues).  Together with
`gammaSelfLoopScan` (right/`0`), `selfLoopScanLeft` (left/`0`) and the rightward fill, this gives the
bidirectional layer the full **four-way scan vocabulary** (`{0,1}` × {left, right}) the data-dependent
shuttle needs.  This deliberately does **not** commit to (a)/(b)/(c): the scheme selection — and the
payload-read body built on it — remains the next focused brick, now with complete motion primitives.
*(Landed via the stacked workflow: branch `claude/npv-gamma-payload-shuttle-design` → PR into the
`claude/elegant-noether-CnlU5` staging branch, not direct-pushed.)*

### 6e. Payload-read mechanism analysis (this pass) — the walking-terminator read and the count/read interdependency

Re-checking the payload read against the now-complete four-way scan vocabulary surfaced one clean
mechanism and one precise obstruction, both worth recording before the next build (a wrong artifact is
worse than an honest design note — §6b):

* **Walking-terminator read (clean, rightward-only; no leftward shift).**  The payload can be read
  **left-to-right** by *walking the terminator* through it: at the terminator `q` (a `1`), read the
  payload bit at `q+1`, then write `0` at `q` and `1` at `q+1` — the terminator advances one cell,
  leaving a `0` behind.  After `j` steps the tape is `0^{z+j} 1 (b_{j+1}…b_z) …`: still a `0^k 1 …`
  structure, terminator at `p_term+j`, and the read head sits at the **clean boundary** immediately
  right of the terminator every iteration.  This is a 2-phase `Bool`-state self-loop (advance ▸ read)
  and it removes the O(z) full-payload leftward shift the "shift-accumulator" framing implied — each
  bit is read at a findable boundary, rightward only.

* **The irreducible obstruction: stop/count and read contend for the terminator.**  The read must
  **stop after exactly `z` bits**, and the only marker-free source of `z` is the leading-zero block
  `[tagLen, p_term)`, whose countdown is naturally bounded by the **terminator at `p_term`**
  (`repeatBody`/`selfLoopCountdownLeft` consume the block and stop when the next cell is the terminator
  `1`).  But the walking-terminator read **moves that very terminator**, destroying the countdown's stop
  marker; conversely, a body that keeps the terminator fixed must reach payload bit `j` at `p_term+j` —
  a data-dependent move *past already-read payload bits that cannot be marked* (arbitrary `0/1` data —
  the 2-symbol wall).  So **read, stop, count and accumulate are interlocked**: they do not separate
  into independent verified bricks, which is precisely why the next step is one cohesive construction,
  not another incremental primitive.

* **Consequence for the scheme decision.**  This favors a design that **decouples the count from the
  read terminator** — e.g. (c) a separate countdown counter, but only once the *reachable-scratch*
  location problem is solved via a reliable landmark (position `0` through a clamped rewind, or the
  **constant** `tagLen`), or a **2-track / reserved-marker tape encoding** giving the payload region a
  markable frontier.  Both are genuine design commitments (the latter a model extension), not mirrors of
  existing primitives — so the (a)/(b)/(c)/encoding decision, and the cohesive read+count+accumulate
  build on it, are the next focused pass, deferred to an explicit scheme choice.

### 6f. Scheme decision — **localized decoupled unary countdown** (the filled leading-zero block *is* the loop counter)

The §6d (a)/(b)/(c)/encoding fork is now **settled**, after evaluating all four against the *actual*
layout (§4) and the *proven* loop convention (`repeatBody_runConfig_iterate'`, now built for **writing**
bodies — `TreeMCSPRepeatBody.lean:364`).  The decision and the reasoning that rules each alternative
in or out:

**Chosen: a decoupled unary countdown, materialized *in place* as the filled leading-zero block,
driving `repeatBody`; the payload bit is read by symmetric anchoring at the (fixed) terminator.**
This is option (c)'s *decoupling* — the count is carried by the combinator's `K`, **not** by the read
terminator (exactly what §6e's interlock demanded) — but realized **locally inside the gamma field**,
which is what makes it work without §6e's unreachable far-scratch problem (see "Why not (c)-in-scratch"
below).  It borrows (b)'s fixed-terminator anchor for *positioning* the read.

**Exact mapping onto the proven combinator.**  `repeatBody_runConfig_iterate'` consumes a unary counter
of `K` **ones ending at the start head**, walking leftward (head retreats one cell per iteration, cells
`≤ head − K` preserved, the body writing freely *above* the head).  Map:
* `K := z` (one iteration per leading zero / per payload bit; `z = Θ(log N)`, so the whole read is cheap).
* **Counter := the gamma leading-zero block filled to ones** by the *built* `gammaSelfLoopFill`
  (`[tagLen, p_term)` → `z` ones), with the **loop start head at `p_term − 1`**.  Then the counter
  window `(p_term − 1 − z, p_term − 1] = [tagLen, p_term)` is exactly the `z` ones the theorem wants.
* **The §6d terminator-merge caveat is neutralized, not fought.**  The fill merges the filled zeros with
  the terminator `1` at `p_term`, but the countdown head starts at `p_term − 1` and only ever touches
  cells `≤ p_term − 1`; the merged terminator sits at `p_term > head`, i.e. in the body's *work region*,
  irrelevant to the count.  The boundary erasure that blocked a *scanning* shuttle simply does not arise
  for a *counted* one.
* **Body (writing, counter-region-preserving):** read the payload bit symmetric to the consumed zero
  across `p_term`, shift-accumulate it into the `n`-register placed in the work region (`≥ p_term`,
  over the payload it has already read), return the head to the iteration's start cell.  The count/stop
  is the combinator's (`K = z` exhausted ⇒ loop exit), so read and count no longer contend.

**Why not the alternatives:**
* **(a) keep the terminator as boundary, no fill** — *rejected*: leaves the count tied to the terminator,
  and §6e showed any scanning read either moves it (kills the stop) or must cross unmarkable already-read
  payload (the 2-symbol wall).  Weakest.
* **(c) countdown counter in *far scratch* `[2N+1, …)`** — *rejected as the realization, kept as the idea*:
  the gamma field sits to the **left** of the `Θ(2^n)` x-field, scratch to the **right** of everything,
  so a per-bit shuttle between a far-scratch counter and the gamma payload crosses arbitrary `x`/cert data
  with **no content-findable landmark** (position 0 is input, not scratch; "first blank" is ambiguous —
  input cells may be `0`).  This is §6e's "reachable-scratch problem", and the layout makes it real.
  Localizing the counter *into the gamma field* (above) removes the shuttle entirely.
* **2-track / reserved-marker encoding** — *rejected*: it gives the cleanest local stop (a genuine third
  symbol), but it **mutates the foundational `TM` type** (binary alphabet, `tapeLength`/`runTime`, the
  pnp3 bridge, and *every* existing toolkit proof).  Enormous blast radius, and it forfeits the
  minimal-single-tape-binary cleanliness that gives the NP-membership claim its value.  Last resort, and
  not needed once the count is localized.

**Consistency with the row loop.**  The *same* `repeatBody` + unary-countdown paradigm serves the row
loop (`2^n` iterations) — there the counter genuinely lives in the `Θ(2^n)` scratch, and the
co-located per-row work (decoded circuit + gate registers, all in scratch) means no cross-arbitrary-data
shuttle arises.  So one coherent control architecture covers both loops; only the *counter placement*
differs (gamma field vs scratch), dictated by where each loop's work region lies.

**Concrete next brick (now unblocked).**  The control infra is complete (`repeatBody` read-only **and**
writing; `gammaSelfLoopFill`; the four-way scan vocabulary; `selfLoopCountdownLeft`; bidirectional head
bounds).  The next coding is the single per-instance **gamma-payload-read body** `B :
ConstStatePhasedProgram Unit` and its discharge against `repeatBody_runConfig_iterate'`: (i) the body
program (advance/read at the symmetric payload cell ▸ shift-accumulate ▸ return head), (ii) its `sB`-step
intrinsic `runConfig` behaviour (accept phase, head returned, counter region `≤ head` preserved), (iii)
its `timeBound`, (iv) the run-`z`-times correctness via `iterate'`, (v) the accumulated `n`-register
matches `decodeGamma?`.  Then length-convention check, prefix-agreement compare (same paradigm, counter =
prefix length), the row loop (upstream-blocked on `circuitEvaluatorCS_run_correct`), and final assembly.

**Accumulator constraint (from the `selfLoopIncrement` contract).**  The shift-accumulate in (i) reuses
`selfLoopIncrement`, whose `timeBound = n` is *exact only when the carry is absorbed in-window*
(`selfLoopIncrement_run_counterValue` requires the first `0` at `j < k ≤ L`; the all-`1`s saturating
pattern needing `L+1` is out of contract — `TreeMCSPSelfLoopCounter.lean:34`).  So the `n`-register must
carry a **spare high `0` bit** at every accumulate, or the read would inherit exactly that off-by-one
over-run.  `n` is `Θ(log N)` wide and the work region above the counter has room, so the spare bit is
free.  (This is the load-bearing fact behind the recurring Qodo "increment off-by-one" false positive:
the bound is right *given the contract*; the body must honour the contract.)

**Layout preconditions landed** (`TreeMCSPPrefixVerifierLayout.lean`): `gammaZeros n` (`= z = K`),
`gammaTermOffset n` (`= p_term`), and `gammaMirror_mem` (the mirror cell `2·p_term − c` of a counter
cell `c ∈ [tagLen, p_term)` is a genuine in-query payload cell) — the geometric facts the body program
consumes, proved `Classical`-free.

### 6g. Body navigation — walking-terminator read + four-way scans (re-checked against the built primitives)

The §6f body's *internal* motion is now worked out against the built scans (so the body program is
unambiguous to write).  One `repeatBody` iteration runs with the head on the current counter cell
`h = p_term − 1 − t` (descending, `t = 0 … z−1`); the read uses a **walking terminator** on the payload
side, kept decoupled from the count (which is `repeatBody`'s `K = z`, the leading-zero countdown).

* **Tape invariant after `t` walking-reads.**  The consumed-counter window and the walked-over payload
  prefix merge into one all-zero gap `[p_term − t, p_term + t)`, with the walking terminator (`1`) at
  `p_term + t`; the unconsumed counter `[tagLen, h]` is still ones, and `h = p_term − 1 − t` is its top.
* **One iteration (head `h` → … → head `h`).**  (1) step right to `h + 1 = p_term − t`; (2)
  `gammaSelfLoopScan` (right over `0`s) lands on the walking terminator at `p_term + t`; (3) read the
  payload bit at `p_term + t + 1 = 2·p_term − h = mirror(h)` (in-query by `gammaMirror_mem`); (4) **walk**
  it: write `0` at `p_term + t`, `1` at `p_term + t + 1`; (5) `selfLoopScanLeft` (left over `0`s) returns
  to the first `1` on the left, which is `h`.  Head is back at `h` and `[tagLen, h]` is untouched — so it
  discharges `repeatBody_one_iteration'`'s body hypothesis (accept phase + head returned + counter region
  `≤ h` preserved).  Each scan distance is `2t ≤ 2z`, so head travel is `O(z)`/iteration, `O(z²)` total.
* **Why the scans suffice.**  Every frontier the body must find is a `1`/`0` boundary reachable by the
  four-way vocabulary: the terminator is "first `1` right of the zero gap", the return is "first `1` left
  of it".  No data-dependent counting *inside* the body, no marker beyond the lone walking `1` — the
  2-symbol wall is never hit, exactly because count and read are decoupled (§6e).

**Open sub-point, deliberately deferred — the accumulate target.**  *Where* the read bit is accumulated
is **not** yet fixed: (α) shift-accumulate `n+1` into a fresh **scratch** register (§6d), or (β) leave
`n+1` **in situ** in the gamma field and have downstream read it in place.  (β) keeps the §6f
localization (no far-scratch shuttle) but pushes the materialization of `n` to whoever needs it; (α)
centralizes `n` but reintroduces the reachable-scratch problem.  This choice is **entangled with the row
loop's `2^n`-in-scratch setup** (the doubling loop that reads `n`), which is itself **upstream-blocked on
`circuitEvaluatorCS_run_correct`** — so resolving (α)/(β) now would be premature.  Therefore the next
buildable unit is the **navigate+read shuttle** above (steps 1–5, emitting the read bit in the body's
`Bool` state), proven against `repeatBody_one_iteration'`; the accumulate wrapper is layered on once the
(α)/(β) decision is forced by the (unblocked) row-loop work.  This keeps the verified surface honest and
avoids committing the accumulate mechanism before its consumer exists.

### 6h. Re-check (supersedes §6g's "next unit") — the accumulate body is *not* separable, and may be unnecessary

Re-checking the §6g shuttle against `repeatBody`'s **actual** interface (`def repeatBody
(B : ConstStatePhasedProgram Unit)`, `TreeMCSPRepeatBody.lean:35`) before writing it caught a real flaw —
the value of design-first over a wrong artifact:

* **The body is `Unit`-state and iterations share only the tape.**  `repeatBody`'s body is
  `ConstStatePhasedProgram Unit`; the `iterate'` body hypothesis is purely a `runConfig` on the shared
  TM from `B.start` to `B.accept`.  A read bit can still be *branched on via phases* (finite control is
  fine), but it **cannot be carried out of the body** — anything the body computes must be deposited on
  the **tape inside the body**.  So §6g's "emit the bit in state, layer the accumulate later" is wrong:
  the accumulate is **intrinsic**, and the (α)/(β) target is **not** deferrable.
* **The navigation medium and the register collide.**  The walked all-zero gap `[p_term−t, p_term+t)`
  must stay all-`0` for the scans to locate the terminator; it therefore cannot double as the
  `n`-register, and a separate register reintroduces the data-dependent region-navigation wall.
* **The deeper reframe: a shift-accumulate body may be unnecessary.**  After `gammaSelfLoopFill`
  establishes `z` (the loop count `K`), the value `n+1 = 1·b₁…b_z` already sits **in situ** in the gamma
  field `[p_term, p_term + 1 + z)`.  Nothing has to *move* it.  The §6d/§6f/§6g "shift-accumulate
  `n`-register" assumed a copy that downstream may not need.  What downstream *actually* needs is (1) the
  **length-convention check** `L = treeMCSPPrefixM codec n` and (2) the **row loop's `2^n`** — and the
  honest open question is whether each can read `n` *in situ* from the gamma field, or genuinely needs a
  relocated copy (the reachable-scratch question the row loop faces anyway).

**Consequence for the roadmap.**  The plan item "gamma payload-read body" should **not** be built as a
standalone accumulate brick yet — its necessity and shape depend on the downstream tape-access pattern,
which is entangled with the row loop (upstream-blocked on `circuitEvaluatorCS_run_correct`).  The honest
next design step is to pin **what the length-check needs from the gamma field** (in-situ read vs. copy),
since that is buildable independently of the blocked row loop and determines whether any payload *copy*
body is needed at all.  Verified geometry (§6f layout lemmas) stands regardless; no body program is
committed until its consumer is fixed.

### 6i. Correction — the per-row evaluator is **proven** (`_wf`); the row loop is *unbuilt*, not proof-blocked

Re-checking the "row loop is upstream-blocked on `circuitEvaluatorCS_run_correct`" claim that §6b/§6c/§9
(and §6h) repeat — **against the actual toolkit** — shows it is **stale/overstated**:

* **`circuitEvaluatorCS_run_correct_wf` is proven, `sorry`-free** (`GateWrappers.lean:5032`, via
  `circuitEvaluatorCSAt_RunCorrect_wf_unconditional` at `:4967`).  The whole file has **no
  `sorry`/`admit`/`axiom`/`native_decide`** and builds clean.  It gives full whole-circuit evaluator
  correctness — every scratch slot `i` ends holding gate `i`'s value, matching `SLProgram.evalAux` —
  **under a well-formedness hypothesis** `hwf : SLProgram_wfFromOffset gates 0`.
* Only the **bare** (non-`_wf`) `circuitEvaluatorCS_run_correct` is future-work (a packaged `Prop`,
  `:1047`) — the *unconditional* version for arbitrary, possibly-malformed gate lists.
* **The NP verifier does not need the bare version.**  A verifier *rejects* an ill-formed witness/circuit
  (well-formedness `SLProgram_wfFromOffset` is decidable, and the malformed case routes to the reject
  sink); it only ever runs the evaluator on **well-formed** gate lists — exactly where `_wf` applies.

**Conclusion.**  Item (3)'s per-row evaluation is **not blocked on a missing proof**: the needed
correctness (`_wf`) exists and is axiom-clean.  What remains for the row loop is *construction*, sharing
the same TM-build difficulties as items (1)/(2): a tape-level **well-formedness guard** (decode + check
`SLProgram_wfFromOffset`, route malformed → sink), the **`2^n` unary counter** (the doubling loop
materialising `2^n` in scratch), the **reachable-scratch navigation**, and the `repeatBody` row loop
whose body invokes `circuitEvaluatorCS_run_correct_wf` then compares the output bit to `x`.  These are
hard but *buildable* — none waits on an unproven upstream lemma.  All prior "upstream-blocked" wording in
this document is corrected accordingly: the dependency is the **proven** `_wf` evaluator plus a decidable
wf-guard.

### 6j. Resolution — α/β settled (**β, in situ**); the standalone read-body is unnecessary; the real crux is *reachable-scratch*

Re-checking §6g's walking-terminator read against §6h's (α)/(β) accumulate targets forces the decision the
earlier notes deferred, and it comes out cleanly:

* **§6g's read is *destructive*, so (α) "read+accumulate" and (β) "leave `n+1` in situ" are mutually
  exclusive.**  The walking terminator overwrites each payload cell as it passes (write `0` at the old
  terminator, `1` at the read cell), so after the `z` reads the gamma payload `[p_term, p_term+1+z)` is no
  longer `1·b₁…b_z` but `0^z 1` — the in-situ value of `n+1` is **gone**.  A read that consumes the payload
  cannot also preserve it.
* **(β) dominates (α).**  Both ultimately need `n` reachable where it is *used* — the length check and the
  row loop's `2^n`-doubling counter (in scratch).  (α) pays the **reachable-scratch** cost *and* destroys
  the in-situ copy; (β) keeps `[tagLen, p_term+1+z)` intact (read in place whenever needed) and pays
  reachable-scratch only where a consumer genuinely needs a *relocated* count.  Neither escapes
  reachable-scratch, so the destructive copy of (α) buys nothing.  **Choose (β).**
* **Consequence: the "gamma payload-read body" (plan item 1) is *not* a standalone brick — it dissolves.**
  Under (β) nothing moves the payload; there is no shuttle/accumulate program to write.  `gammaSelfLoopFill`
  is therefore **not** on the (β) path either (it was only the counter materialization for a *consuming*
  loop): the leading zeros stay zeros, `n+1` stays readable in situ.  This confirms §6h's "may be
  unnecessary" as a definite **unnecessary**, and retires §6f's filled-counter mechanism for this purpose.

**The genuine remaining crux, now isolated: reachable-scratch on a 2-symbol single tape.**  Every
*purely-local* loop is already covered — `repeatBody` keeps the head on its counter and a local body works
beside it (the gamma field is self-contained; the row loop's counter and per-row work both live in
scratch).  What is *not* solved is any **cross-region transfer**, and exactly two are needed: (T1) seed the
`2^n`-doubling loop with a count derived from `n` (gamma field → scratch), and (T2) compare input bit
`x[r]` (in the query) against the evaluator's output bit (in scratch) for a data-dependent `r`.  Both must
land the head at a *data-dependent* position in a different region with **no marker** to aim at.  Candidate
landmarks, and why each fails:

| Candidate landmark | Why it fails on the 2-symbol model |
|---|---|
| Position `0` via clamped left-rewind (`selfLoopScanLeft` floors at `0`) | reliable, but `0` is the *input* region; scratch starts at `2N+1` (data-dependent), not a constant offset from `0` |
| "First blank" by scanning right to the first `0` | input/cert cells may be `0` (= blank), so the scan stops *inside* the input — the input/scratch boundary is not content-findable |
| Write a sentinel at the scratch frontier, then home on it | needs a 3rd symbol; the binary alphabet has none (this is the 2-track model extension already rejected in §6f) |

**Honest status.**  Navigation and counter representation for the gamma read are fully settled (and the
read-body is now provably unnecessary under (β)).  No standalone shuttle brick will be built.  The next
real construction problem is a **reachable-scratch addressing scheme** for the cross-region transfers
(T1)/(T2) — the shared prerequisite of the length check and the row loop — which has no clean primitive on
the present model and is therefore the next *design* decision (not another motion primitive).  Documented
here rather than half-built, per the standing design-first discipline.

### 6k. The proven evaluator is an *unrolling*, not a loop — `M` needs an on-tape interpreter; unary-distance addressing resolves §6j's crux

Re-checking the toolkit `circuitEvaluatorCS` against what a *fixed* `M` can use (the central question for
items 3–5) settles two things the earlier notes left fuzzy:

* **`circuitEvaluatorCSAt` is recursion on the gate `List`** (`GateWrappers.lean:502`, `match gates with
  | [] => idleCS | g :: rest => seqCS (evalOneGateCS …) (circuitEvaluatorCSAt rest …)`).  So
  `circuitEvaluatorCS gates` is a **different program per `gates`**, with `numPhases` growing in the gate
  count — the same "per-instance unrolling" status as `repeatProgram` (§6's correction).  Its proven
  `_wf` correctness (§6i) is therefore a **spec / reasoning device**, *not* a body `M` can embed: the fixed
  `M` has one finite control and cannot pick an input-dependent program.  This sharpens §6i: item (3) is
  not proof-blocked, but neither is it "just call the evaluator" — `M` needs a **from-scratch on-tape gate
  interpreter**.
* **Shape of the interpreter.**  A back-edge loop (`repeatBody`) over a **unary gate-count** counter; the
  body reads one **fixed-width gate record** from a decoded-circuit scratch region (fixed strides — the
  record width is a compile-time constant), dispatches on the opcode (finite control), and writes the gate
  value into the next scratch slot.  The row loop is the analogous outer `repeatBody` over the `2^n`
  counter.  Both loop *counts* are data-dependent (handled by the unary counter); all *motion within a
  body* is fixed-stride **except** operand fetch.

* **Operand fetch is the §6j crux, and unary-distance addressing solves it.**  A gate back-references an
  earlier gate's output slot at a **runtime** index `j`; reaching slot `j` is a data-dependent seek with no
  marker.  **Scheme: the decoder stores each back-reference as a *unary distance* (a `1`-block) in the gate
  record**, and the fetch follows it by **scanning over the `1`-block** — `selfLoopScanRightOne` /
  `selfLoopScanLeftOne`, stopping at the bounding `0`.  This is marker-free, uses only the four-way scan
  vocabulary, and stays within the polynomial budget (distances are `≤ #gates = poly(n)`, so unary is
  poly-size).  It **resolves** §6j's "no clean primitive" status for the interpreter: the primitive is
  *scan-over-a-unary-distance*, and the cost is paid once, in the decoder, converting binary refs to unary.
  The same unary-distance technique services the (T2) `x[r]`-vs-output compare relative to the row counter.

* **`selfLoopScanRightOne` (this PR) is the missing piece of that vocabulary** — pure rightward traversal
  over `1`s (the earlier "rightward `1`" slot was only `gammaSelfLoopFill`, which *writes*).  Built with
  full run-behaviour (`selfLoopScanRightOne_runConfig_{scanning,terminator}`), it is the rightward
  marker-free unary-distance seek.

**Roadmap consequence.**  The named bricks ahead are now: (D) the **on-tape decoder** `witness → contiguous
gate records with unary back-reference distances` (the §9 codec-layout reconciliation lands here, and it is
the hardest single brick); (I) the **gate interpreter** `repeatBody` body (read record ▸ unary-seek
operands ▸ dispatch ▸ write slot); (R) the **row loop** `repeatBody` over `2^n` whose body runs (I) then
compares the output to `x[r]`; (P) the **prefix-agreement compare** (a smaller instance of the same
unary-distance compare); (A) **assembly** + `runTime_poly` + the `accepts = treePrefixSemanticAccepts`
bridge. The control combinators, counters, and now the full four-way *traversal* vocabulary are all built;
the remaining work is (D)/(I)/(R)/(P)/(A), in that dependency order.

## 7. Runtime accounting

With `threshold n = thresholdPoly k n = n^k + k`, `witnessBits n = (bitLength n + 4) · threshold n`,
`tableLen n = 2^n`, and input length `L = Θ(2^n)`:

* parse + length check: `poly(n)`;
* prefix agreement: `O(witnessBits n · offset) = poly(n) · O(2^n)`;
* verification: `2^n` rows × (`O(size)` gates × `O(offset ≈ 2^n)`) = `2^n · poly(n) · 2^n = poly(2^n)`.

So total `timeBound` is `poly(L)`; the `runTime_poly` obligation is then a closed-form `Nat`
inequality `timeBound(L) ≤ L^c + c` for a concrete `c` derived from the assembled bound. The exponent
`c` is fixed once the program is assembled.

## 8. Recommended brick order (each a separate verified commit)

0. **Back-edge / self-loop loop construct** — the prerequisite surfaced in §6's correction (fixed
   phase count, runtime-counted iteration).  **Two proven instances DONE:**
   * *Scanning* — `gammaSelfLoopScan` (`TreeMCSPGammaScanProgram.lean`): a fixed 2-phase scan phase
     re-entering while reading `0`, fully proven through end-to-end `TM.run` correctness
     (`gammaSelfLoopScan_run_locates_terminator`: decodes the gamma unary-prefix length).
   * *Counting (up)* — `selfLoopIncrement` (`TreeMCSPSelfLoopCounter.lean`): a fixed 2-phase
     **variable-width** binary increment (carry self-loop), fully proven through `counterValue + 1`
     correctness (`selfLoopIncrement_runConfig_counterValue`, via the toolkit's
     `counterValue_first_zero_diff`).  This is the data-dependent-width counter the fixed `M` needs,
     where the toolkit's fixed-`k` `incrementProgram` cannot serve.
   * *Counting (down)* — `selfLoopDecrement` (`TreeMCSPSelfLoopCounter.lean`): the exact dual, a fixed
     2-phase variable-width binary **decrement** (borrow self-loop), fully proven through
     `counterValue = after + 1` correctness (`selfLoopDecrement_run_counterValue`) via a locally-proven
     dual of the toolkit arithmetic (`counterValue_first_one_diff`; the toolkit ships only the increment
     direction).  Correct when the counter is positive — the natural termination mechanism for
     countdown-style bounded loops.

   So the back-edge primitive is demonstrated for **scanning** and **counting in both directions**.
   **Remaining:** the general *body-reentry* loop (re-enter a multi-phase body with a proven counter as
   the loop index, terminating at a data-dependent target — for the up-counter this is a comparison
   against `2^m`; for the down-counter, zero-detection over a data-dependent width — note both still
   require width-bounded comparison/scan machinery on the single-tape binary model) for the row loop
   (brick 5).  The two counter *steps* (±1) are proven; closing them into a *loop* needs that
   comparison layer.
1. **`boundedLoopProgram`** + composition reasoning layer (§6, §6a) — **DONE**, and now **extended to
   full self-loop composition-survival** (`TreeMCSPCounterComposition.lean`, `TreeMCSPScanComposition.lean`):
   every self-loop primitive (scan, increment, decrement) is proven to retain its run behaviour when
   embedded as a `seq` phase — as the **first** component (P1-region: carry/borrow-ripple,
   `counterValue ± 1`, terminator-locate, and the P1→P2 handoff) **and** as a **non-first** component
   from an arbitrary start configuration at an arbitrary tape offset (P2-region — now **all three**:
   increment, decrement **and** scan, `gammaSelfLoopScan_seqP2_runConfig_scanning`).  So every self-loop
   composes in **either** `seq` position.  Plus the **state-lifting** combinator `liftUnitProgram`
   (`BoundedLoopProgram.lean`) and the first **heterogeneous-state** assembly: `mSkeletonDemo`
   (`TreeMCSPSkeletonComposition.lean`).  **Resolution of the leading-phase run-behaviour transfer:** we
   took the **`Unit`-common-state route** (native `Unit` tag check `tagCheckProgramU`, §6a) rather than
   the `liftUnitProgram` bisimulation (which is therefore **off the critical path**).  The tag check's
   *run behaviour as `M`'s first phase* is now **DONE** (`TreeMCSPTagCheckComposition.lean`:
   `tagCheckProgramU_seq_runConfig_inv` re-derives the standalone invariant in the P1-region, plus the
   P1→P2 handoff `tagCheckProgramU_seq_runConfig_handoff`), and **`M`'s first two phases chain**
   (`TreeMCSPLeadingPhasesChain.lean`: `tagCheckThenGammaScan_runConfig` and
   `tagCheckThenGammaScanTerminator_runConfig` splice the tag-check handoff with the gamma-scan
   P2-region scan/terminator invariants via `TM.runConfig_add` — tag verify ▸ handoff ▸ gamma zero-scan
   ▸ stop *on the gamma terminator* on one composed machine).  This also lands on the **assembled**
   skeleton: `mSkeletonU_tagCheck_handoff` (`TreeMCSPSkeletonComposition.lean`) instantiates the generic
   handoff at `P2 := seqList […]`, so `mSkeletonU` itself (not a toy 2-phase `seq`) verifies the tag and
   hands off after `tagLen + 1` steps.  **Transitively-nested composition is now also DONE:** the gamma
   scan is re-derived in the doubly-nested *P2∘P1* position (P1 of the inner `seq gammaSelfLoopScan R`,
   itself P2 of the outer `seq tagCheckProgramU …`) via `seq_stepConfig_P2_*` ∘ `seq_transition_P1_normal_*`
   (`gammaSelfLoopScan_seqNested_*`, `TreeMCSPScanComposition.lean`), the generic nested chain
   `tagCheckThenNestedGammaScan_runConfig` (`TreeMCSPLeadingPhasesChain.lean`) splices it onto the
   tag-check handoff, and `mSkeletonU_tagCheck_then_scan` lands it on the **assembled** skeleton: the
   real `mSkeletonU` runs **tag check ▸ gamma zero-scan** end-to-end.  This proves the per-phase
   composition lemmas chain to *any* `seqList` depth — so the **right-only composition layer is now
   structurally complete** (both positions, transitive nesting, real-assembly capstone).  **Remaining
   is no longer right-only:** past the scan, the data-dependent loops (gamma payload read, prefix
   compare) need the **bidirectional** layer (see §6's correction and §6b's right-only-ceiling
   analysis), and the row loop additionally needs upstream `circuitEvaluatorCS_run_correct`.
2. **Parse-on-tape** — *tag check **DONE*** (`TreeMCSPTagCheckProgram.lean`: program, `timeBound`,
   `neverMovesLeft`, single-step lemmas, `runConfig_scan`, accept-iff, matched-state, semantic
   correctness `accepts ⇔ leading bits = tag`, Prop characterization) — valid for `M` since
   `tagLen` is a true constant.  The tag check also now runs correctly **as the first phase of a `seq`**
   (`TreeMCSPTagCheckComposition.lean`, brick 1) and **chains into the gamma scan**
   (`TreeMCSPLeadingPhasesChain.lean`).  Gamma layout/range bounds done.  The count-zeros scan (locate +
   decode the unary-prefix length) is done **both** as a `maxIters` reasoning device
   (`gammaZeroScanProgram`) **and**, crucially, as the `M`-compatible **self-loop** `gammaSelfLoopScan`
   (brick 0), composing in either `seq` position — so the gamma unary-prefix decode now has the right
   structure for `M`.
   **Remaining:** gamma payload-read (recover `n` from the `z` payload bits — needs a counted read),
   length-convention check.
3. **Witness slice + prefix-agreement compare** (bounded scan; `combineAtOffset` per-bit) — *remaining;
   the per-bit loop over `i` cells needs brick 0*.
4. **On-tape circuit decode + single-row evaluation** — single-row eval is `circuitEvaluatorCS`, but
   only its *single-gate* run-correctness is proven; the **full multi-gate `circuitEvaluatorCS_run_correct`
   is upstream toolkit future-work** (§9).  Plus the open piece of realizing **this codec's** decoder
   on tape, or proving it agrees with `Encoding.CircuitTree` (the §9 codec caveat) — *remaining,
   hardest single risk; partly upstream-blocked*.
5. **Row-iteration verification** — the `2^m`-row loop; `mcspCheckAllRows`/`RowConsistencyCheck`
   supply the per-row body + `timeBound`, but as a *per-`m` unrolling*, not a single-`M` loop.  The
   open piece is the **back-edge loop** (brick 0) over the per-row body with the row index on a tape
   counter — *remaining, **blocked on both brick 0 (back-edge) and brick 4's
   `circuitEvaluatorCS_run_correct`***.
6. **Assemble `M`**, prove the bridge (★), discharge `runTime_poly`, build the
   `PrefixExtensionNPWitness`, and feed it to `verifiedSource_treePoly`'s second hypothesis — *remaining*.

> **Toolkit status (verified, do not rebuild):** atomics, `seq`/`seqList`, gate evaluators
> (`GateWrappers`, **0 `sorry`**), `circuitEvaluatorCS` *single-gate* run-correctness + boundary
> lemmas (the *full multi-gate* `circuitEvaluatorCS_run_correct` is **upstream future-work**, §9),
> `CircuitTree` encode/decode round-trips, the binary counter **incl. `incrementProgram_correct`**
> (carry propagation — proven; the stale "Session 7c will prove" comment notwithstanding),
> `RowConsistencyCheck`/`mcspCheckAllRows` `timeBound`.  The NP-verifier track adds §6/§6a (bounded
> loop + composition layer), the tag-check phase, and the gamma count-zeros scan (locate + decode the
> unary-prefix length).  The genuinely missing core is the gamma payload-read/parse orchestration, the
> upstream single-row `circuitEvaluatorCS_run_correct`, the row-loop *correctness* invariant (blocked
> on it), the codec-layout reconciliation (§9), and the final assembly.

## 9. Existing parallel scaffolding, and a codec-encoding caveat

The repo already contains the same *kind* of obligation, unbuilt, on its main route:

* `pnp3/Complexity/TMVerifier/GapMCSPVerifier.lean` — a five-phase (A–E) scaffold for
  `canonicalGapMCSPVerifier`, with **all phases `TODO`** (no concrete TM); self-estimated ~800–1500 LOC.
* `pnp3/Magnification/CanonicalAsymptoticDecider.lean` — `CanonicalAsymptoticVerifierComponents`
  (`M`, `c`, `k`, `runTime_poly`, and `accepts_eq : accepts M (concatBitstring x w) = decideAsymptotic n x`)
  with a **proved** bridge `.witness` to `GapPartialMCSP_Asymptotic_TMWitness`. The decider
  `decideAsymptotic` is fully proved; the **only** missing piece is `buildCanonicalVerifierComponents`
  — the concrete TM. The repo's `NP_not_subset_*` / `P_ne_NP` route
  (`CanonicalIntegrationTests.lean`) is *conditional on* this same unbuilt witness.

Takeaways: (1) the proven assembly pattern is `components` (with an `accepts_eq` bridge) → witness — to
be mirrored here once a TM exists; (2) a concrete verifier TM is the **project-wide engineering
frontier**, not unique to this track.

Reusable beyond §3: `circuitEvaluatorCS` (`GateWrappers.lean:569`) is defined and has its
*single-gate* run-correctness proven (`circuitEvaluatorCSAt_{const,input}_run_correct`, the
`nil` case, and boundary lemmas), and `alwaysAccept`/`alwaysReject` are complete TMs.  **Correction
(re-verified this session):** the *full multi-gate* `circuitEvaluatorCS_run_correct` is **not yet
proven** — it is explicitly marked toolkit future-work ("Milestone F.4 target statement", "future
session", `GateWrappers.lean:1043+`), though `GateWrappers` carries **0 `sorry`** (the composite
theorem is simply unstated, not holed).  So *single-row* circuit evaluation is **partially** built,
and the **row loop (brick 5) is blocked on the toolkit finishing `circuitEvaluatorCS_run_correct`** —
this is an upstream dependency, not work this track can complete alone.  The genuinely missing pieces
are therefore: the full single-row evaluator correctness (upstream), then the **row loop** (§6).

**Codec-encoding caveat (this track is harder than the canonical one).** The toolkit's circuit codec is
`Encoding.CircuitTree` / `decodeCircuitTreeAtDepth`. But `treeCircuitWitnessCodec` (this track's codec)
decodes via the *pnp4* `treeSelfDelimitingCode` / `decodeCircuit` (`ConcreteTreeCodec.lean`,
`CircuitTreeBridge.lean`) — a **different** byte layout. So step 6 must either (a) realize *this codec's*
decoder on the tape, or (b) prove the toolkit `CircuitTree` encoding agrees with
`treeCircuitWitnessCodec.decode`. The "re-check after each step" discipline must include confirming the
on-tape decoder matches `codec.decode` exactly, or the bridge (★) breaks.

> **Concrete layout finding (verified by reading `Encoding.lean:120` `encodeCircuitTree`).** The two
> layouts are not just "different bytes" — they are *structurally* different, which scopes D2 precisely:
> * **Witness layout (`encodeCircuitTree`, what the certificate actually is):** a **recursive tree** with
>   **3-bit binary tags** — `input = 000 ++ encodeFin width i` (a fixed-`width` **binary** index),
>   `const = 001 ++ b`, `not = 010 ++ ‹subtree›`, `and = 011 ++ ‹sub1›‹sub2›`, `or = 100 ++ ‹sub1›‹sub2›`.
>   Subtrees are **inlined** (no sharing); decoded by `decodeCircuitTreeAtDepth` with a depth budget.
> * **Interpreter layout (D0 `encodeGateRecord`, what D1b/D2-spec decode):** a **flat stream** of records
>   with **unary** tags `1^t 0`, **unary** operand fields, and **back-reference distances** (chosen so a
>   single-tape head can follow a reference by scanning over `1`s — §6k).
> * **Consequence:** D1b's decoder does **not** read the witness; the D0/D1b/D2-spec line is the
>   interpreter's *internal* format. **D2's real content is a transcoder** `witness (recursive CircuitTree,
>   3-bit tags, binary indices) → flat unary-record stream with back-references`: parse the recursive tree
>   on tape (a stack/depth discipline on a single tape), assign gate indices in a linearisation order,
>   compute each reference as a back-distance, and convert binary indices to unary. This is the hardest
>   single brick and a multi-session sub-project. The D2 **spec** side is now **complete**
>   (`TreeMCSPGateStreamLayout.lean`): `encodeGateRecordStream`/`decodeGateRecordStream` + round-trip, the
>   CircuitTree→records **flattening spec with semantics preservation** (`decodeGateRecordStream_flatten_eval`,
>   `decodeGateStream_circuit_eval` via the toolkit's `CircuitTree.flatten_eval` + `evalCircuitTree_toTree`),
>   and the end-to-end transcoder spec `transcodeWitness` + `transcodeWitness_faithful` (the emitted record
>   stream decodes to a straight-line program computing `Circuit.eval c`). What remains open is purely the
>   **on-tape realisation** of that transcoder. (Option (b) — proving the two encodings *agree* — is **not**
>   available: they genuinely disagree; only option (a), an on-tape transcoder/decoder, can close the bridge.)
>   The on-tape difficulty is concrete: the witness's `encodeFin width i` indices are **fixed-width binary
>   with no terminator** (not self-delimiting), so reading one on a single 2-symbol tape needs a **counter in
>   tape scratch** — exactly what the unary-record layout (terminator-delimited) was designed to avoid. So the
>   transcoder, the interpreter, the row loop, and the prefix compare all require tape scratch-arithmetic;
>   there is no scratch-free shortcut, which is what makes the remainder a multi-session build (§10).
>
> **D2 loop control — DONE (`TreeMCSPGateStreamReachesSink.lean`).** The *record-stream* side of D2 (the
> head-advancing loop over D1b, halting at the malformed sink reused as the end-of-stream marker `1^5`) is
> now closed at the termination level: `gateStreamDecoder_runConfig_reachesSink` proves that a tape holding
> `encodeGateRecordStream gs ++ 1^5` drives the loop `loopUntilSink gateOneRecordDecoder ⟨13⟩` to its sink
> phase `13` — one record consumed per pass (the per-tag traversal), re-entered via the back-edge
> (`loopUntilSink_runConfig_oneIter`), halting at the marker (`gateStreamDecoder_runConfig_malformed`). The
> bridge from "tape window = bit list" to the traversals' per-cell predicates is `TapeHoldsAt` (splits along
> `++` exactly as the record layout concatenates unary fields). This discharges `loopUntilSink`'s
> `reachesSink` obligation for the concrete encoding; it operates on the interpreter's *internal* unary-record
> format, so the **transcoder** above (recursive `CircuitTree` → records) remains the open D2 sub-project.

**Honesty baseline (must be preserved).** The entire `pnp3`/`pnp4` tree currently has **0 `sorry`, 0
`admit`, 0 custom `axiom`, 0 `native_decide`**. Every TM brick must keep this — no proof holes, only the
standard `[propext, Classical.choice, Quot.sound]`.

## 10. Honest scope assessment

This is a **multi-PR, multi-session verified-engineering effort** (the analogous canonical verifier is
self-estimated at ~800–1500 LOC, and this track is harder — see §9), comparable to a verified
bounded-loop circuit interpreter running on a single-tape Turing machine with a machine-checked
runtime bound. The toolkit supplies roughly 60% of the parts (atomics, gates, counters, encodings,
configuration invariants); the missing core is **control flow (the bounded loop)** plus the parse /
verify orchestration and the runtime proof. There is **no shortcut**: the `correct` field demands a
machine that genuinely verifies the certificate, so the circuit-over-all-rows evaluation is
unavoidable. Until all bricks land with no `sorry` and only the standard axioms, the
`PrefixExtensionNPWitness` for the tree-MCSP prefix parser remains an open (engineering) obligation,
and `verifiedSource_treePoly` stays conditional on it — alongside the genuinely open circuit lower
bound `NoPolynomialBoundedSearchSolver`, which this track does **not** address.

## 11. D2 on-tape transcoder — design + sub-brick decomposition (multi-session)

The D2 *decoder* line (D0→D1a→D1b→D2: `gateStreamDecoder` + `reachesSink`) is complete, but it reads the
interpreter's **internal** unary-record format. The **transcoder** is the missing bridge: on-tape, it
must turn the certificate (a recursive `CircuitTree` in `encodeCircuitTree` form) into the unary-record
stream `encodeGateStream (flatten (toTree c)).gates` that the decoder/interpreter consume. Its pure spec
(`transcodeWitness`) and end-to-end faithfulness (`transcodeWitness_faithful`) are already proven; what
remains is the **on-tape realisation**, which is genuinely a multi-session sub-project. This section fixes
its design and decomposition so the bricks can land one at a time, each hole-free.

### Why it is hard (the irreducible core)

* **Preorder in, postorder out.** `encodeCircuitTree` is a **preorder** serialisation: `tag(root) ++
  encode(child₁) ++ encode(child₂)` with subtrees **inlined** (no length headers, no sharing).
  `flattenAt` (the output's structure) is **postorder**: `flatten(child₁) ++ flatten(child₂) ++
  [gate(root)]`, and the root gate's operands are **absolute indices** `offset + |sub₁| − 1`,
  `offset + |sub₁| + |sub₂| − 1`. Converting preorder→postorder is prefix→postfix: it **requires a
  stack**. A fixed-phase machine cannot have depth-many phases, so the stack must live in **tape
  scratch** — there is no scratch-free shortcut (confirmed against `CircuitTree.flattenAt`,
  `Encoding.lean:545`).
* **Binary, non-self-delimiting indices.** Input indices are `encodeFin width i` — **fixed-width little-
  endian binary with no terminator** (`Encoding.lean:12`). Reading one needs a **width counter** in
  scratch; emitting it as the record's unary field needs **binary→unary** conversion (a doubling loop).
* **No scratch primitives yet.** The toolkit has `selfLoopIncrement` (binary +1), `selfLoopCountdownLeft`
  / `repeatBody` (consume a unary counter). It has **no** tape-region copy, no unary-block writer, no
  binary→unary, no stack. These must be built.

### Tape layout (proposed)

```
[ input x | certificate (encodeCircuitTree) | WORK: output record stream | STACK | scratch counters ]
```
The transcoder reads left-to-right over the certificate, pushing/popping frames on STACK, appending
completed records to WORK; the row-loop interpreter then runs over WORK (the existing decoder line).

### Sub-brick decomposition (each a separate hole-free PR into staging)

* **D2t-1 — tag dispatcher (DONE, this PR).** `treeTagDispatch` (`TreeMCSPTreeTagDispatch.lean`): the
  3-bit binary-tag trie in finite control; reads the tag, dispatches `input/const/not/and/or`, rejects
  `101/110/111`. Scratch-free; per-tag run-behaviour proven (head +3, tape unchanged).
* **D2t-2 — scratch primitives (LARGELY ALREADY PRESENT — recon).** The reusable write/scratch layer
  mostly exists and must be **reused, not rebuilt**: the unary-block **writer** is `gammaSelfLoopFill`
  (pnp4, proven, with its `seqP2` lift); **counters both directions** are `selfLoopIncrement` /
  `selfLoopDecrement` (pnp4, with `counterValue ± 1` correctness); the **countdown/consume** is
  `selfLoopCountdownLeft`; and a **cell-copier** `copyAtOffsetProgram` exists in the pnp3 toolkit
  (a `PhasedProgram`, not yet in the pnp4 `ConstStatePhasedProgram Unit` lineage). The *gap* this
  brick closed: the down-counter's `seqP2` composition lift was incomplete (only `borrow` + the `stop`
  single-steps) — `selfLoopDecrement_seqP2_runConfig_{stop,counterValue}` now complete it, so the
  down-counter composes as a non-first phase (needed for binary→unary and the parser's pending-subtree
  scan). The chosen D2t-3 design (the **decrement loop** below) **avoids the copier entirely**; a
  pnp4-style copier (or a `PhasedProgram`→`seq` bridge) would only be needed for the *doubling-loop*
  variant, which we do **not** pursue. The real remaining cost from here on is the cross-region
  head-shuttling **composition** (D2t-3c), not any missing primitive.
* **D2t-3 — binary→unary.** Read `encodeFin width i` (width-counter-bounded), emit `unaryField i`.
  **Primitive groundwork DONE** (D2t-3a/b merged): the per-step pieces all exist in pnp4 with
  run-behaviour *and* `seqP2` lifts — `selfLoopDecrement` (`counterValue−1`), `selfLoopAppendOne`
  (append one `1`), `selfLoopScanRightOne` / `selfLoopScanLeftOne` (the U-region shuttle),
  `gammaSelfLoopScan` (the `B`-region zero-test scan), and the counters. What remains is the **loop
  composition D2t-3c**, a substantial cross-region proof (≈ the decoder's `reachesSink`):
  - **Algorithm (decrement loop, avoids the copier):** `acc := 0`; while `B > 0` { `decrement B`;
    `append 1 to U` }.  Correctness = induction on `counterValue B`: each pass is `counterValue B − 1`
    (the decrement lift) and `|U| + 1` (the append lift); termination at `B = 0` (the value reaches the
    spec `decodeFin`).
  - **The navigation crux (why it is a real construction, not a `seqList`):** after `selfLoopDecrement`
    the head rests **mid-`B` at a data-dependent cell**, and `B`'s remaining cells are **mixed `0/1`**,
    so the `B → U` hop *cannot* be a uniform `scan-over-bit` seek.  Resolution: a **fixed reference
    marker** at the `B|U` boundary — each body pass returns the head to the marker by a marker-seek, and
    the decrement / append / zero-test run at known offsets from it via the `seqP2`-offset lemmas
    (`…_seqP2_runConfig_*`, which take an arbitrary start `c0` at phase `P1.numPhases`).  The
    `B = 0` test runs `gammaSelfLoopScan` from `B`'s low end — recall it advances right over `0`s and
    **halts on the first `1`**.  The boundary marker placed at `B|U` is a `1`, so it *is* that
    terminating `1`: the scan halts **on the marker** iff `B` held no `1` before it (so `B = 0`), and
    halts **strictly before** the marker iff some bit of `B` is set (so `B > 0`).
  - **Sub-bricks:** D2t-3c-1 body (one pass: `counterValue B − 1` ∧ `|U| + 1` ∧ head back at the
    marker) → D2t-3c-2 the `loopUntilSink` wrapper + the `counterValue`-induction → D2t-3c-3 the bridge
    to `decodeFin` / `unaryField`.
* **D2t-4 — leaf emit.** `input`: D2t-3 then write `unaryField 0 ++ unaryField i`. `const`: read the
  literal bit, write `unaryField 1 ++ [b]`. (Leaves push an index onto STACK.)
* **D2t-5 — the stack discipline (the core).** Internal-node handling: on `not/and/or`, recurse via a
  tape STACK (push the pending node + child indices; on completion pop, compute the back-reference
  distances from the child indices, and append the gate record to WORK). This is the prefix→postfix
  engine; the largest brick.
* **D2t-6 — count prefix + assembly.** Prepend the unary gate-count to WORK (`encodeGateStream`), prove
  the whole machine's output equals `encodeGateStream (flatten (toTree c)).gates` (matching
  `transcodeWitness`), and bound its runtime polynomially.

### Correctness seam

Each emit brick is proven against the **pure** spec it realises (`decodeFin`, `encodeGateRecord`,
`flattenAt`'s index arithmetic), exactly as D0/D1a/D1b separated spec from tape. D2t-6 composes them into
`transcodeWitness` faithfulness, which `transcodeWitness_faithful` already lifts to `Circuit.eval`. No
`P ≠ NP` claim; headline stays conditional; honesty baseline (0 holes, standard triple) preserved
throughout.

## 12. D2t iteration plan — small finishable stages

The remaining transcoder (D2t-3c…D2t-6) is closed by **small, individually-completable iterations**,
each a single self-loop or a short `seq`/`loopUntilSink` composition with a proven `runConfig`
behaviour and only the standard axiom triple — the same brick discipline that closed D0…D2t-3b.

### D2t-3c — binary→unary loop (the navigation crux, resolved)

**Layout that makes the body navigation uniform** (the key design decision): place the unary output
`U` to the **left** of the binary counter `B`, with a `0` **sentinel** between them, and a `1`
**right-marker** just past `B`:
```
[ … blank | U = 1^|U| | sentinel(0) | B = b_0 b_1 … b_{w-1} | rightMarker(1) | … ]
                         ^HOME            (little-endian, b_0 next to sentinel)
```
Because the loop only ever scans over **uniform** stretches — `B`'s just-flipped low `1`s, or `U`'s
`1`s — it **never crosses `B`'s mixed high bits**, which was the blocker. Iterations:

* **D2t-3c-α — `selfLoopAppendLeftOne`** (leftward unary single-append): scan **left** over `U`'s `1`s,
  write one `1` at `U`'s left `0`-end (`U` grows leftward). Mirror of `selfLoopAppendOne` with
  `Move.left`. Standalone run-behaviour + `seqP2` lift. *(first iteration — clean mirror)*
* **D2t-3c-β — `seekHomeAfterDecrement`**: from the post-`decrement` config (cells `0..j-1 = 1`, cell
  `j = 0`, head at `j`), one `Move.left` then `selfLoopScanLeftOne` over the flipped `1`s lands the head
  on the sentinel (HOME); the `j = 0` edge collapses to the same target. A short `seq`/run lemma.
* **D2t-3c-γ — `binToUnaryBody`**: one pass over the **flattened atomic** chain `binToUnaryBody :=
  seqList [stepRightOnce, selfLoopDecrement, stepLeftOnce, selfLoopScanLeftOne, stepLeftOnce,
  selfLoopAppendLeftOne, selfLoopScanRightOne]` (the home-seek `seq stepLeftOnce selfLoopScanLeftOne`
  is inlined rather than nested as the `seekHomeAfterDecrement` composite, to keep each element a single
  primitive at a single nesting depth).  Prove from HOME with `B > 0`: `counterValue B − 1`, `|U| + 1`,
  head back at HOME.  **This is the substantial assembly phase — see the composition-toolkit status note
  below for the exact remaining bricks.**
* **D2t-3c-δ — `bZeroTest`**: from HOME decide `B = 0` vs `B > 0` (a `gammaSelfLoopScan` over `B` whose
  stop cell is the right-marker iff `B = 0`); supplies `loopUntilSink`'s `hstep`/`hbase`.
* **D2t-3c-ε — the loop**: `loopUntilSink binToUnaryBody (sink := done)`; `loopUntilSink_reachesSink`
  with measure `counterValue B`, giving `|U| = value(B)` after termination.
* **D2t-3c-ζ — correctness**: bridge `|U| = value(B) = (decodeFin w …).val`, i.e. the produced block is
  `unaryField (decodeFin …)`.

(Tiny helpers `stepRight`/`stepLeft` — unconditional one-cell moves — are 1-phase sub-bricks, or folded
into the adjacent `seq`.)

#### ε `hstep` navigation — the route→body re-homing crux (analysis; resolution needs body-session coordination)

The loop machine is now assembled (`binToUnaryLoop = loopUntilSink binToUnaryLoopBody ⟨4⟩`, #1559) and both
route decisions are lifted into it: `hbase` (`B=0 → sink phase 4`, #1561) and `decide_false`
(`B>0 → phase 5`, #1563).  Closing `hstep` (`B>0 → re-enter at phase 0` with `counterValue` strictly
decreasing) requires bridging the **route exit** to the **body entry**, and that bridge is not present in
the as-merged `binToUnaryLoopBody := seq binToUnaryRouteBody binToUnaryBody`:

* **Route exit (`decide_false`, B>0):** phase `5`, head at the **discriminator** `head₀ + z + 1`
  (`z = j+1`, so `j+2` cells *right* of the sentinel), tape unchanged.  Under the outer `seq`, phase `5`
  hands off to phase `6` = `binToUnaryBody`'s start.
* **Body entry (`binToUnaryBody_runConfig_onePass`):** head **on the sentinel** (`tape head = false`,
  `0 < head`), with `U = 1^u` immediately *left* (`hUboundary`: cell `head-u-1 = 0`) and `B = 0^j 1`
  immediately *right*.  The body opens with `stepRightOnce`, i.e. it assumes it already sits on the
  sentinel.

So phase `6` is reached `j+2` cells too far right; the body would misread the tape.  A seek-HOME step is
needed between route and body.

**Why seek-HOME is *not* a self-contained in-track add-on.**  Re-homing means *finding the sentinel while
scanning left*.  The sentinel is a `0`; to its right are `B`'s `0`s (indistinguishable) and to its left is
`U` (`1`s) — so the only structural landmark that locates the sentinel is `U`'s rightmost `1`.  **But `U`
is empty on the first iteration (`u = 0`)**: then `hUboundary` makes the sentinel's left neighbour also a
`0`, and a left-scan-over-`0`s overshoots into the scratch region with no `1` to stop at (the binary
alphabet + all-`Unit` state offer no other marker).  The fixes both touch the **parallel body session**'s
layout invariant:
  * **(a) permanent left floor-marker** — write a `1` just left of where `U` grows, as a fixed landmark;
    seek-HOME then stops on it.  Changes `binToUnaryBody`'s `hUboundary` (left-of-`U` becomes `1`, not `0`)
    and shifts the `ζ` bridge `|U| = value(B)` by the floor cell.
  * **(b) guarded-decrement / scan-fusion** — restructure so the route's rightward scan *is* the body's
    first scan, so no head ever leaves a known landmark; changes `binToUnaryBody`'s opening
    (`stepRightOnce` + `selfLoopDecrement`).

**Status:** `decide_false` (#1563, reaching phase `5`) is the half that holds under either fix and is the
shared peel (`binToUnaryLoop_transition_route`) consumer.  The seek-HOME primitive + the
`binToUnaryLoopBody` definitional revision + the `hstep` run-through (route → re-home → body one-pass →
loop back-edge, `counterValue − 1`) is the next brick, and the floor-vs-fusion choice should be settled
jointly with the `binToUnaryBody` layout owner so the U-boundary invariant stays consistent.

#### ε `B = 0` test — SOUNDNESS FINDING and the corrected (full-width-scan) design

**Finding (session `wizardly-hypatia`, while attempting to close `hstep`/`reachesSink`).**  The route's
`B = 0` test `bZeroRouteProgram = seq gammaSelfLoopScan stepRightThenBranch` — *scan right to the first
`1`, then read the next cell (the discriminator): `disc = 1 → B = 0` (sink), `disc = 0 → B > 0` (body)* —
is **not a sound `B = 0` test on a raw little-endian binary counter**.  For `B > 0` it silently requires
the cell *after* the lowest set bit to be `0`, which binary **decrement does not preserve** (a borrow
fills a `1`-run at the bottom).  Concrete counterexample: `B = 3 = "11"` (`b₀ = 1, b₁ = 1`).  With the
sentinel `0` at HOME and `B` at `[HOME+1, …]`, the tape from HOME is `0 1 1`, which matches
`binToUnaryLoopRehome_runConfig_hbase`'s pattern at `z = 1` (cells `[HOME, HOME+1) = 0`, `HOME+1 = 1`,
`HOME+2 = 1`) — so the loop routes `B = 3` to the **sink** and terminates early, emitting `unaryField 0`
instead of `unaryField 3`.  (`decide_false`'s `B > 0` branch needs `HOME+2 = 0`, which fails here, so
`B = 3` matches *only* the sink branch.)

This is **not a bug in any merged proof**: `hbase`/`decide_false`/`onePass`/seek/measure are all *sound
conditional theorems* about explicit tape patterns.  The gap is in the route's **test design** — no
cross-iteration invariant can make `disc` track `value B = 0` for arbitrary binary `B` — so the intended
`reachesSink`/`ζ` is **not provable on the as-merged loop**.  Literature confirms a correct binary-counter
zero-test inspects **all** counter bits at the counter's fixed bit-length (Seiferas, *Counting Is Easy*,
arXiv `cs/0110038`; counter-machine constructions), the first-`1`+next-cell shortcut is unsound.

**Corrected design (chosen: full-width zero scan).**  Replace the `disc` test with a **width-`w`
full-scan**: scan the entire fixed-width `B`-window `[HOME+1, HOME+1+w)` and accept `B = 0` iff every bit
is `0`.  As a `w`-parameterised program (phase count grows with `w`, like `gammaZeroScanProgram`'s
`maxIters`), it uses the **known width `w`** as the scan bound — sidestepping the binary-alphabet
delimiting wall (§6: a content-findable delimiter is impossible since `B`'s `1`s mimic any fixed marker).

**Entanglements (why this is a multi-brick milestone, not a local swap).**
* The full-scan leaves the head at `B`'s **right end** (`HOME + w`), not on a discriminator one-past the
  lowest set bit.  `seekHomeAfterRoute`'s left-scan assumes the cells between its start and HOME are all
  `0`, which **fails when `B > 0` has `1`s** — so re-homing from the right end needs a left-scan over `B`'s
  `1`s (different from the merged seek), or the scan should re-home as it goes.
* The body (`binToUnaryBody`/`onePass`, binary decrement + U-append), the `counterValue − 1` measure, and
  the seed-`U` landmark are **unchanged and reusable**.
* So corrected ε = new `bZeroFullScan w` (sound zero-test) + a re-home matching its exit + re-lifted
  `hbase`/`decide_false` analogues against it + the existing body/measure, then `reachesSink` (induction
  on `value B`) + `ζ`.  Scope ≈ the route-legs stack (#1559–#1576) redone for the new zero-test, plus the
  assembly — a focused next milestone.

**Reusable progress (session `wizardly-hypatia`).**  Per-leg ingredients all merged/landing and reused
under the corrected design: seek-HOME lift (#1577), body single-steps (#1578), body `onePass` (#1579),
`decide_false`+head (#1580), one-pass measure decrease (#1581).  The disc-test route *deciders*
(`hbase`/`decide_false` as `B=0`/`B>0` branches) are **superseded** by the full-scan and must not be wired
into the final `reachesSink`.

##### δ BUILT — `bZeroFullScan` (the sound width-`w` zero-test), with run-through

The corrected design is now realised in `TreeMCSPBZeroFullScan.lean` (`bZeroFullScan w :
ConstStatePhasedProgram Unit`, `numPhases = w + 2`): phases `0 .. w-1` read each cell of the `w`-window
(`0` → step right, next phase; `1` → phase `w+1` = `B > 0`); phase `w` is the accept (`B = 0`), phase
`w+1` the `B > 0` branch.  Proven this stack:
* **Structural** — `numPhases`/`startPhase`/`acceptPhase`/`timeBound`, `neverMovesLeft`,
  `transition_move`/`transition_bit` (so it composes under `seq`/`loopUntilSink`).
* **Spec foundation** — `counterValue_eq_zero_imp_all_false`: a zero counter value forces every cell of
  the width-`w` window to `false` (the converse of the toolkit's `counterValue_of_all_false`).  This is
  the fact the `B = 0` path consumes (the loop's `hbase` hypothesis is `μ = counterValue B = 0`).
* **Run-through** (mirroring `gateTagDispatch`'s phase-scanner template) — `..._runConfig_scanning`
  (induction on step count: `j ≤ w` leading `0`s ⇒ after `j` steps phase `j`, head `+ j`, tape
  unchanged), `..._runConfig_zero` (all `w` cells `0` ⇒ after `w` steps the accept phase `w` = `B = 0`),
  `..._runConfig_pos` (low `j` cells `0`, cell `j` set, `j < w` ⇒ after `j + 1` steps phase `w+1` =
  `B > 0`, head on the set bit).

All surfaces carry the standard `[propext, Classical.choice, Quot.sound]` triple (or fewer); audited in
`AxiomsAudit`, surfaced in `AlgorithmsToLowerBoundsSurfaceTests`.

**Remaining for ε/ζ (the focused next milestone, on the new sound test).**  Because `bZeroFullScan` is
`w`-parameterised, its loop assembly is `w`-parameterised too, so the route-leg phase arithmetic must be
re-expressed with `w`-dependent indices (this is the bulk of the redo `≈` #1564–#1581, now against a
*sound* decider):
1. **ε-seqP2** — lift `bZeroFullScan`'s run-through into the `seq` P2-region (re-derive `_runConfig_zero`
   / `_runConfig_pos` from an arbitrary start `c0` at phase `P1.numPhases`), the analogue of
   `gammaSelfLoopScan_seqP2_runConfig_*`, so the scan composes as a non-first phase.
2. **ε-assembly** — `binToUnaryLoopFullScan w := loopUntilSink (seq stepRightOnce (seq (bZeroFullScan w
   re-pointed to the `B>0` phase) (seq seekHome binToUnaryBody))) ⟨sink = the `B=0` accept⟩`; ship the
   phase-count facts.  (`stepRightOnce` moves HOME→`B`'s low end so the scan window is exactly
   `[HOME+1, HOME+1+w)`, matching the `counterValue` measure.)
3. **ε-hbase** — `B = 0` ⇒ sink: `counterValue = 0` →(δ1)→ all-`0` window →(ε-seqP2 `zero`)→ the scan
   reaches the sink phase.  (Does **not** need the re-home.)
4. **ε-rehome** — a fresh seek-HOME matching `bZeroFullScan`'s `B>0` exit (head on the lowest set bit at
   `HOME+1+j`, left of it all `0` to the sentinel, then the seed-`U` `1`): a fixed-phase
   scan-left-over-`0`s + step-right, the analogue of `seekHomeAfterRoute` at the new offset.
5. **ε-hstep** — `B > 0` ⇒ one pass: scan `pos` → re-home → `binToUnaryBody_runConfig_onePass` →
   loop back-edge, with `counterValue B` dropping by one (reuse `binToUnaryBody_onePass_counterValue`).
6. **ε-reachesSink** — feed `hstep`/`hbase` to `loopUntilSink_reachesSink` with `μ := counterValue B`.
7. **ζ** — the output bridge `|U| = value B = (decodeFin width …).val` (induction on `counterValue`,
   each pass `|U| + 1` via `binToUnaryBody_onePass_appendedBit`), closing D2t-3 against `unaryField`.

#### Composition-toolkit status (the loop-body vocabulary is complete; γ is the remaining assembly)

**Done — the per-primitive run-behaviour + composition lifts the loop body needs are all merged:**
`stepLeftOnce` (#1539) and `stepRightOnce` (#1541) with their `seqP2` lifts; `seekHomeAfterDecrement`
standalone home-seek (#1540, `= seq stepLeftOnce selfLoopScanLeftOne`); `selfLoopAppendLeftOne` standalone
(#1538) **and** its `seqP2` lift (#1542); plus the pre-existing `selfLoopDecrement` / `selfLoopScanLeftOne`
/ `selfLoopScanRightOne` / `gammaSelfLoopScan` standalone + `seqP2` lifts.  Every navigation step of the
binary→unary pass is thus an individually-verified primitive carrying only the standard axiom triple.

**The γ assembly is the next (laborious-but-mechanical) phase.**  Two facts about the `seq`/`seqList`
toolkit shape it:
* The run-decomposition lemmas `seqList_run_{two,three,four,five}` peel a `seqList` into per-element
  `runConfig` segments — but currently only up to **length 5**, while the flattened `binToUnaryBody` has
  **7** elements.  → first brick: add `seqList_run_{six,seven}` (mechanical mirrors).
* `seq` does **not** reassociate (`seq A (seq B C) ≠ seq (seq A B) C` as routed programs), so a primitive
  at chain-depth `d` is reached only through `d−1` nested `seq_stepConfig_P2_*` unfolds.  The existing
  `_seqP2_` lemmas cover depth 1 and the `_seqNested_` lemmas (e.g. `gammaSelfLoopScan_seqNested_*`) cover
  depth 2; the deepest chain run to completion so far is depth 2.  → γ needs each of the 7 elements
  re-derived at **its own depth** (depth-1 `stepRightOnce` … depth-7 `selfLoopScanRightOne`), each a fresh
  mirror of the `gammaSelfLoopScan_seqNested` pattern (the per-step lemmas are `decide`/`simp`-routine; the
  run inductions mirror the standalone ones).  This is ~one brick per element, then a final assembly brick
  composing them via `seqList_run_seven` with head/tape windows tracked against the U-left layout.

**Progress (this stack):** `seqList_run_{six,seven}` ✅ (#1544).  Decrement's depth-2 re-derivation ✅ —
`selfLoopDecrement_seqNested_*` (`TreeMCSPCounterComposition.lean`: the six borrow/stop single-step
lemmas plus the borrow-ripple, after-decrement, and `counterValue − 1` run lemmas on
`seq P1 (seq selfLoopDecrement R)`, generic in `P1`/`R`).  This is the decrement analogue of
`gammaSelfLoopScan_seqNested_*` and exactly element 2's segment behaviour for `seqList_run_seven`
(`binToUnaryBody`'s decrement sits as `seq stepRightOnce (seq selfLoopDecrement R)`).  Element 3
(`stepLeftOnce`, chain-depth 3) re-derivation ✅ — `stepLeftOnce_seqNested2_*`
(`TreeMCSPStepLeftProgram.lean`: phase/head/tape single-step lemmas + the one-step run lemma on
`seq P1 (seq Q (seq stepLeftOnce R))`, generic in `P1`/`Q`/`R`), proven by chaining the outer
`seq_stepConfig_P2_*` into a `simp [seq, stepLeftOnce, hsub]` that navigates both inner `seq` levels.
Element 4 (`selfLoopScanLeftOne`, chain-depth 4) re-derivation ✅ — `selfLoopScanLeftOne_seqNested3_*`
(`TreeMCSPScanLeftOneProgram.lean`: the scan/stop single-step lemmas + the scanning invariant and
terminator-locating run lemmas on `seq P1 (seq Q (seq Q2 (seq selfLoopScanLeftOne R)))`, generic in
`P1`/`Q`/`Q2`/`R`); the depth-4 navigation supplies the middle `¬(Q.numPhases + Q2.numPhases <
Q.numPhases)` fact to `simp` (depth 3 closed via `lt_self_iff_false` alone), confirming the self-loop
nesting scales past depth 2.

**All seven per-element re-derivations are now complete ✅** (element 1 = the outermost P1, handled by
the generic single-step `seq_stepConfig_P1_*` lemmas, needs no bundled lemma):
* element 5 — `stepLeftOnce` at depth 5: `stepLeftOnce_seqNested4_*` (`TreeMCSPStepLeftProgram.lean`);
* element 6 — `selfLoopAppendLeftOne` at depth 6: `selfLoopAppendLeftOne_seqNested5_*`
  (`TreeMCSPUnaryAppendLeftProgram.lean`);
* element 7 — `selfLoopScanRightOne` at depth 7: `selfLoopScanRightOne_seqNested6_*`
  (`TreeMCSPScanRightOneProgram.lean`).

For depth ≥ 5 the navigation supplies the successive middle subtraction facts `hsubᵢ : (a + b + …) − a =
…` explicitly (since `Nat.add_sub_cancel_left` only matches the immediate `a + m − a` shape) alongside
the non-self comparison negations.  **γ definition committed ✅** — `binToUnaryBody := seqList [stepRightOnce, selfLoopDecrement,
stepLeftOnce, selfLoopScanLeftOne, stepLeftOnce, selfLoopAppendLeftOne, selfLoopScanRightOne]`
(`TreeMCSPBinToUnaryBody.lean`), with its structural facts: `binToUnaryBody_eq_seq` (the
`seq stepRightOnce (seq selfLoopDecrement R)` shape the decrement's `_seqNested_` lemma consumes),
`binToUnaryBody_numPhases = 15`, and the closed-form `binToUnaryBody_timeBound n = 4·n + 10` (via
`seqList_timeBound_seven`).  **Remaining for γ: the one-pass run-behaviour composition** — from HOME with
`B > 0`, compose the seven per-element segment lemmas above (element 1 = `stepRightOnce` via the generic
`seq_stepConfig_P1_*`; elements 2–7 via their `_seqNested…_` lemmas) along the `seqList_run_seven` time
skeleton with `TM.runConfig_add` at each boundary, tracking head/tape windows against the U-left layout,
to obtain `counterValue B − 1`, `|U| + 1`, head back at HOME.  **Started ✅:** the leading-steps
composition `binToUnaryBody_runConfig_lead2` (`TreeMCSPBinToUnaryBody.lean`) — element 1
(`stepRightOnce`, the outermost P1) via per-`P2` step lemmas `binToUnaryBody_step1/2_*` (generic in
`P2`, the proven `seekHomeAfterDecrement` bound-`i` pattern): from start phase `0` with `head + 1` in
bounds, after `2` steps the machine is at phase `2` (the decrement's shifted start), head advanced one
cell right, tape unchanged — exactly `selfLoopDecrement_seqNested_runConfig_*`'s precondition.
**Element 2 (decrement) segment composed ✅:** `binToUnaryBody_runConfig_afterDecrement` — from HOME with
`B`'s low cells `[head+1, head+1+j)` all `0` and cell `head+1+j` set, after `2 + (j+1)` steps the machine
is at phase `3` (decrement done), head on the cleared cell `head+1+j`, with `B`'s low `j` cells flipped
to `1` and cell `head+1+j` cleared (composes `lead2` with `selfLoopDecrement_seqNested_runConfig_stop`
via `TM.runConfig_add`).  **Decrement→element-3 handoff composed ✅:**
`binToUnaryBody_runConfig_afterDecrHandoff` (after `2 + (j+1) + 1` steps, phase `4`; the handoff's `R`
is the `seqList` tail, so it matches the loop-body machine syntactically — no defeq friction).  Also
landed: the two nested accept-handoff boundary lemmas
`selfLoopDecrement_seqNested_stepConfig_handoff_*` and `stepLeftOnce_seqNested2_stepConfig_handoff_*`.

> **✅ Architectural blocker RESOLVED (`bodyFull` fully-unfolded representation).** The earlier manual
> hand-chaining *past* the handoff hit a `whnf` heartbeat timeout because the loop-body machine stored
> elements `3…7` buried inside one `seqList [stepLeftOnce, …]` literal while `stepLeftOnce_seqNested2_*`
> (and the deeper element lemmas) expect the *fully `seq`-nested* form `seq … (seq stepLeftOnce …)`; the
> previous attempt bridged them with `have h : <seqList-form> := <seq-form lemma>`, which forced Lean to
> defeq-check two large `…toPhased.toTM` terms.  **Fix (the documented second option): drive the whole
> composition on one consistent fully-unfolded `seq` representation.**  `bodyFull` is that representation
> (`seq stepRightOnce (seq selfLoopDecrement (seq stepLeftOnce (… (seq selfLoopScanRightOne (seqList [])))))`),
> with `binToUnaryBody_eq_bodyFull : binToUnaryBody = bodyFull := rfl` (axioms `[propext, Quot.sound]`,
> Classical-free) as the cheap bridge.  On `bodyFull` every element appears as an explicit `seq` head, so
> each `_seqNested…_` lemma `rw`-fires by **structural unification through the reducible abbrev** (one
> abbrev delta, no whnf blow-up) — empirically fast.  The leading-steps / decrement / decrement-handoff
> lemmas were restated on `bodyFull`, and **element 3 (`stepLeftOnce`) is now composed ✅:**
> `binToUnaryBody_runConfig_afterStepLeft3` — after `2 + (j+1) + 1 + 1` steps, phase `5`, head one cell
> left at `head+j`, tape the decremented pattern unchanged.  (One subtlety surfaced and is handled: the
> abbrev-vs-unfolded `tapeLength` mismatch makes `omega` atomize the two forms differently; discharge
> such bounds with `exact hb` / defeq rather than `omega`.)  **Element-3→4 handoff + element 4
> (`selfLoopScanLeftOne`) composed ✅:** `binToUnaryBody_runConfig_afterStepLeft3Handoff` (phase `6`) and
> `binToUnaryBody_runConfig_afterScanLeft4` — after `2 + (j+1) + 1 + 1 + 1 + (j+1)` steps the leftward
> scan has retraced `B`'s flipped `1`-run and stopped on the sentinel at phase `7` with the **head back at
> HOME** (`c0.head`).  Note **each element occupies 2 phases**, so a handoff step separates every element's
> accept from the next element's start; element 4 is composed as `scanning (j steps) + stop_zero (1 step)`
> rather than the bundled `_terminator`, whose `k < head` precondition excludes `j = 0` (`B` odd), and a
> new `h_sentinel : c0.tape c0.head = false` precondition records that HOME holds the sentinel `0`.  Each
> bundled segment lemma's output is in the unfolded form; bridge it to `bodyFull` with
> `have h : <bodyFull-form> := <unfolded fact>` (one cheap abbrev delta).  **Element-4→5 handoff + element
> 5 (`stepLeftOnce`) composed ✅:** `binToUnaryBody_runConfig_afterScanLeft4Handoff` (phase `8`) and
> `binToUnaryBody_runConfig_afterStepLeft5` — after `2 + (j+1) + 1 + 1 + 1 + (j+1) + 1 + 1` steps the
> second home-seek `stepLeftOnce` has stepped left off the sentinel onto `U`'s right end (`c0.head − 1`)
> at phase `9` (new precondition `hHOME : 0 < c0.head`).  The element-4→5 handoff needed a new depth-4
> `selfLoopScanLeftOne_seqNested3_stepConfig_handoff_*` (now in `TreeMCSPScanLeftOneProgram.lean`, modeled
> on the depth-3 `stepLeftOnce` handoff).  **Element-5→6 handoff + element 6 (`selfLoopAppendLeftOne`,
> the U-append) composed ✅:** `binToUnaryBody_runConfig_afterStepLeft5Handoff` (phase `10`) and
> `binToUnaryBody_runConfig_afterAppend6` — after `2 + (j+1) + 1 + 1 + 1 + (j+1) + 1 + 1 + 1 + (u+1)` steps
> (`u = |U|`) the append has scanned left over `U`'s `u` `1`s and **written one fresh `1` at `U`'s left
> `0`-boundary** (`c0.head − u − 1`), extending the unary output to `u + 1`, at phase `11`.  Needed the new
> depth-5 `stepLeftOnce_seqNested4_stepConfig_handoff_*` (in `TreeMCSPStepLeftProgram.lean`); composed as
> `scan(u) + append-stop(1)` to cover `u = 0` (empty `U`, first iteration); preconditions `hUfit`/`hU`
> (the `1^u` block) / `hUboundary` (its left `0`).  The append-stop's tape write is reconciled with the
> `if`-form tape via `Configuration.write_self` / `write` + `dif_neg`.  **Element-6→7 handoff + element 7
> (`selfLoopScanRightOne`, scan-home) + the terminator handoff into `idleCS` composed ✅ — THE ONE-PASS
> HEADLINE IS DONE:** `binToUnaryBody_runConfig_afterAppend6Handoff` (phase `12`),
> `binToUnaryBody_runConfig_afterScanRight7` (phase `13`, head back at HOME) and
> **`binToUnaryBody_runConfig_onePass`** (phase `14`, the `idleCS` sink).  Needed the new depth-6
> `selfLoopAppendLeftOne_seqNested5_stepConfig_handoff_*` and depth-7
> `selfLoopScanRightOne_seqNested6_stepConfig_handoff_*`.  The headline: from HOME with `(B, 1^u)`, after
> `2 + (j+1) + 1 + 1 + 1 + (j+1) + 1 + 1 + 1 + (u+1) + 1 + (u+1+1) + 1` steps the body reaches its
> `idleCS` sink (phase `14`) with the head back at HOME, `B` decremented by one, and `U` extended to
> `1^(u+1)` — i.e. one pass turns `(B, 1^u)` ↦ `(B − 1, 1^(u+1))`.  (The scanRight upper-bound `head + k <
> tapeLength` is discharged via `show … bodyFull.…tapeLength …` to avoid the abbrev/unfolded `omega`
> atomization.)  **Remaining (δ/ε/ζ):** δ (`bZeroTest`, a `gammaSelfLoopScan` over `B` deciding `B = 0`),
> ε (`loopUntilSink binToUnaryBody`, iterating `onePass` `value(B)` times — combinator +
> `loopUntilSink_reachesSink` already exist), ζ (the correctness bridge `|U| = value(B) =
> (decodeFin …).val`).

**Then:** δ (`bZeroTest` — a `gammaSelfLoopScan` over `B`), ε (`loopUntilSink binToUnaryBody` — the
combinator and `loopUntilSink_reachesSink` already exist), ζ (bridge `|U| = value(B) = (decodeFin …).val`).

(An alternative to the nesting ladder is a **monolithic** `binToUnaryBody` phased program — one ~12-phase
machine with every step inlined, proven directly à la `gateOneRecordDecoder` — which sidesteps the
non-reassociativity entirely at the cost of not reusing the `seqP2` lifts.  The ladder above is preferred
for reusing the already-merged, individually-verified vocabulary.)

### D2t-4 — leaf emit (iterations)
* **D2t-4a — `emitConstRecord`**: from the `const` dispatch phase, read the literal bit and write the
  fixed 3-cell record `1 0 b` into WORK (uses the U-left write discipline; fixed width, no loop).
* **D2t-4b — `emitInputRecord`**: `D2t-3c` (binary→unary of the index) then frame it as
  `unaryField 0 ++ unaryField i`. Each leaf pushes its WORK index onto STACK (feeds D2t-5).

### D2t-5 — the preorder→postorder tape stack (the research-grade core; its own iterations)
* **D2t-5a — frame format + `pushFrame` / `popFrame`** (each a bounded self-loop over a fixed frame
  layout: pending-child count + the gate tag + accumulated child WORK-indices).
* **D2t-5b — the recursion driver**: on `not/and/or` push a frame (children pending); on a completed
  subtree pop, compute the back-reference **distances** from the child indices, append the gate record
  to WORK, and decrement the parent's pending count. Driven by `loopUntilSink` with the stack-empty sink.
* **D2t-5c — correctness**: the emitted WORK equals `encodeGateRecordStream (flatten (toTree c)).gates`
  (the postorder linearisation), by induction on the tree via `flattenAt`'s index arithmetic.

### D2t-6 — assembly
* **D2t-6a**: prepend the unary gate-count (`encodeGateStream`); **D2t-6b**: compose the whole transcoder
  TM and prove its output `= transcodeWitness …` (lifting D2t-1…D2t-5), closing §9 against
  `transcodeWitness_faithful`.

**Discipline (every iteration):** new module / lemmas under `Frontier/ContractExpansion/`; register in
`lakefile.lean`; extend surface tests + `AxiomsAudit`; `lake build PnP3 Pnp4` + `./scripts/check.sh`
green; standard triple only; small stacked PR into staging, Qodo-reviewed, merged; **no `sorry`/holes**,
no `P ≠ NP` claim.

### D2t-5 status — pure foundation COMPLETE; on-tape realization is the remaining (multi-session) core

The **pure layer of D2t-5 is fully proven** (against the verified `CircuitTree.flattenAt`, standard axioms
only) — these are the settled specs the on-tape machine must realise:

* `TreeMCSPStackFlatten.lean` — `toSteps`/`runSteps`, `flattenStack_eq_flattenAt`: the postorder step
  linearisation equals `flattenAt 0`, **absolute-index arithmetic included**.
* `TreeMCSPStackFlattenValueStack.lean` — `runStack`, `flattenStackVS_eq_flatten`,
  `transcodeStreamViaStack_faithful`: the **value-stack** execution equals `flatten`, and the
  count-prefixed stream is a **faithful transcoder** (decodes to a straight-line program computing
  `Circuit.eval`).
* `TreeMCSPNatStack.lean` — `encodeNatStack` / `decodeNatStack_encodeNatStack`: the **on-tape value-stack
  format** (indices as self-delimiting unary fields) ↔ the abstract `List Nat`, with single-field pop.
* `TreeMCSPDriveStack.lean` — `drive` / `settle` / `driveWORK_eq_flatten`: the **preorder-streaming
  driver** (control stack of `(tag, remaining)` frames + value stack + settle cascade) produces the
  postorder `flatten`.  *This is the exact algorithm the on-tape loop runs.*

**Concrete on-tape design (the remaining bricks).**  Tape regions, left→right:
`[ input x | certificate (encodeCircuitTree) | WORK | STACK_val | STACK_ctrl | scratch ]`.  The driver is
`loopUntilSink driverBody (sink := certificate fully consumed ∧ STACK_ctrl empty)`, where `driverBody`
realises one `drive`/`processToken` step:
  - `treeTagDispatch` (D2t-1) reads the next 3-bit tag; on a **leaf**, `emitConstRecord` / `emitInputRecord`
    (D2t-4a/4b) append the record to WORK, then `pushFrame` the new index onto `STACK_val` and run
    `settle`; on `not/and/or`, `pushFrame (tag, arity)` onto `STACK_ctrl`.
  - `settle` is a bounded inner loop: decrement `STACK_ctrl`'s top; on reaching `0`, pop it, read the
    children's indices off `STACK_val` (the `NatStack` pop = `selfLoopScanLeftOne`-style field read),
    append the internal gate record to WORK with those operands, push the new index, and repeat.

* **D2t-5a** — `pushFrame` / `popFrame` machines over `STACK_val` (NatStack format) and `STACK_ctrl`
  (control-frame format), each a `ConstStatePhasedProgram` with a `*_runConfig_*` lemma realising the
  list push/pop against the `decodeNatStack`-style codecs.  *(The control-frame codec is the immediate
  next brick, the `(tag, remaining)` analogue of `NatStack`, building on `ITag` from `TreeMCSPDriveStack`.)*
* **D2t-5b** — `driverBody` assembled via `seq` from the above; `loopUntilSink_reachesSink` with the
  **two-stack loop invariant** "after consuming a certificate prefix, the tape `(WORK, STACK_val,
  STACK_ctrl)` encodes the corresponding `drive` configuration", discharged by `drive_preorder` (tree
  induction).
* **D2t-5c** — at the sink (whole certificate consumed, `STACK_ctrl` empty), WORK `= driveWORK (toTree c)
  = (flatten (toTree c)).gates` by `driveWORK_eq_flatten`; prepend the unary count (D2t-6a) for the full
  `encodeGateStream`, matching `transcodeWitness`.

This on-tape core is the largest remaining brick (comparable to the D2t-3 loop, a multi-session effort),
but every machine piece is now proven against a **settled pure spec** (`drive` / `driveWORK_eq_flatten`
plus the two stack-format codecs), so it decomposes into individually hole-free `ConstStatePhasedProgram`
iterations.

### D2t-5 progress update (NPV #1600–#1605): frame reads, small-step driver, cert codec, tape invariant

Since the section above was written, the **spec/spine layer expanded considerably** — all merged, standard
`[propext, Classical.choice, Quot.sound]` triple only, `./scripts/check.sh` 17/17 throughout.  This
*refines* (does not replace) the D2t-5a/5b/5c plan above.

* **Control-frame codec + reads (D2t-5a, #1600/#1601).**  `encodeCtrlStack` /
  `decodeCtrlStack_encodeCtrlStack` fix the `(tag, remaining)` frame format; `readCtrlFrameTag` (#1600) and
  `readCtrlFrameRemaining`
  (#1601) are the settling-branch reads — fixed-phase **unary tries** (≤ 3 cells, head-advancing, tape
  unchanged), the control-frame analogue of `treeTagDispatch`.  *(So "the control-frame codec is the
  immediate next brick" / "`pushFrame`/`popFrame` … reads" above are now DONE on the read side; the value
  push is `writeNatField` and the frame push is `pushCtrlFrame`, both with `*_extends_*` realisation
  bridges.)*
* **Small-step driver semantics (`DriveState.step`, #1602).**  The big-step `drive` runs an unbounded
  `settle` cascade per leaf; the on-tape loop runs **one primitive action per iteration**.
  `DriveState.step` is that micro-step; `step_iterate_settle` / `step_iterate_processToken` /
  `step_iterate_drive` prove iterating it reproduces `settle` / `processToken` / `drive`, and
  **`driveStep_out_eq_flatten`** that from the empty start
  it leaves `(flatten c).gates` in WORK.  Measure `DriveState.mu` with `mu_step_lt` (strict decrease off
  terminal) + `step_terminal` (terminal is fixed).
* **Termination + explicit bound (#1603).**  `step_reachesTerminal`, `step_terminal_at_mu` (terminal after
  exactly `mu` steps — the pure mirror of `loopUntilSink_reachesSink`), and **`driveStep_halts_bound`**:
  within **`3·c.size`** micro-steps the driver halts with WORK `= (flatten c).gates` (`preorder_length`:
  `|preorder c| = c.size`) — the polynomial runtime witness the on-tape loop inherits.
* **Certificate codec (#1604).**  `encodePreToken`/`encodePreorder` + **`encodePreorder_preorder`**:
  `encodePreorder (preorder c) = encodeCircuitTree c`, i.e. the certificate **is** the encoded preorder
  token stream, so the driver's abstract unread-token list decodes the on-tape certificate cell-for-cell.
* **Driver tape-layout invariant (#1605).**  `DriverLayout` (region base offsets) + `DriverLayout.WellFormed`
  (region ordering `certBase ≤ workBase ≤ valBase ≤ ctrlBase ≤ L`) + **`driverTapeInv`** (cert-from-cursor /
  WORK / `STACK_val` / `STACK_ctrl` regions spell `encodePreorder` / `encodeGateRecordStream` /
  `encodeNatStack` / `encodeCtrlStack` of the `DriveState` fields) + `driverTapeInv_init` (holds at start).
  This is the concrete **"two-stack loop invariant"** the D2t-5b plan named, stated machine-agnostically
  (over a bare `tape`/`cursor`) so it is well-typed before the driver TM exists.

**Remaining (unchanged in spirit — the multi-session machine core):**
1. the on-tape **`driverBody`** realising one `DriveState.step` under `driverTapeInv` (settling/reading
   dispatch over the merged read/write/push bricks);
2. the **cross-region head seeks** between cert / WORK / `STACK_val` / `STACK_ctrl` (genuine `reachesSink`
   loops, à la the `BinToUnaryLoop*` family);
3. the **`loopUntilSink_reachesSink` discharge** at the `Configuration` level — `driverTapeInv` + the
   head/`settling`-flag coupling, with `μ := DriveState.mu ∘ decode` (the pure `step_terminal_at_mu` already
   discharges the abstract termination).  The length-aware region non-overlap (`DriverLayout` capacities) is
   added when (1)–(2) first need it.

### D2t-5b corridor keystone layer (A1–A4, PRs #1610–#1615) — **Block A4 COMPLETE** (A4a–A4f)

After the `driverTapeInv` spine above, the on-tape realisation was re-based onto a **corridor layout**
that makes every driver head-hop a scan over a guaranteed-all-`0` corridor onto a guaranteed-`1`
anchor (`TreeMCSPDriverCorridor`, A3), revising the left-cert `driverTapeInv` into the right-cert
`driverCorridorInv` (certificate rightmost; right-anchored stacks `encodeNatStackR` / `encodeCtrlStackR`
in fixed zones between WORK and the certificate).  Against that invariant, the **per-`DriveState.step`
keystones** — each "given the right bounded tape rewrite, `driverCorridorInv` is preserved across one
`step`" — have now landed for **every** `step` branch (Block A4 complete):

* `corridorInv_nodeStep` (A4) — reading a `node tag`: push a control frame (`nodeStepTape`).
* `corridorInv_constStep` / `corridorInv_inputStep` (A4a) — reading a `leaf`: emit the record
  (`emitTape`), push the value index (`valPush_window`), advance the cursor marker (`cursorStepTape`),
  composed as `leafStepTape`.
* `corridorInv_decStep` (A4b) — settling, top frame `rem ≥ 2`: one `writeBlockTape` (decremented
  frame + a one-cell zero pad).
* **`corridorInv_settleClearStep` (A4c, this brick)** — settling, control stack **empty**: the cascade
  is finished; the machine writes **nothing** (only the finite-control `settling` flag flips), so the
  invariant transports verbatim and its settling-coherence clause becomes vacuous.

* **`valReplaceTop_window` (A4d)** — the value-stack **pop-k-push-1** window core: overwrite the popped
  operand block `oldTop` (one entry for `not`, two for `and` / `or`) by the single new entry
  `encodeNatEntryR out.length`, padded with `replicate (oldTop.length − newLen) false` so one
  `writeBlockTape` covers the `max` of the two widths; the result window spells
  `encodeNatStackR (out.length :: vs)` over the untouched suffix `vs`.
* **`corridorInv_popStep` (A4e)** — the settling, top-frame `rem = 1` **settle-EMIT** keystone
  (generic over `tag` / `gate` / `vpop`): three **disjoint** region rewrites (WORK < VAL < CTRL, cert
  untouched) composed as `popStepTape` — WORK emit (`emitTape`, with record `encodeGateRecord gate`),
  VAL pop-k-push-1 (`valReplaceTop_window`), CTRL top-frame zeroing (full-frame `writeBlockTape`-false,
  the `decStep` pattern) — re-establishing all 16 `driverCorridorInv` clauses, the same shape as
  `corridorInv_inputStep` with a CTRL pop in place of the cursor advance.
* **`corridorInv_terminalStep` (A4f)** — the terminal branch (`toks = []`, not settling): `step` is the
  identity (`DriveState.step_terminal`), so the invariant transports verbatim.

With these, **every** `DriveState.step` branch has a corridor keystone (**Block A4 complete**), and the
residual machine work is Block A5: the on-tape `driverBody` (assemble each arm's `seqList` of merged
components and equate its final tape with the keystone transformer), the cross-region seeks, and the
`loopUntilSink_reachesSink` discharge (items 1–3 above), now stated against `driverCorridorInv`.

All keystones and cores are kernel-checked, standard `[propext, Classical.choice, Quot.sound]` triple
only.  This is **Infrastructure** for the NP-verifier track (input (2) of `verifiedSource_treePoly`); it
builds no machine yet and proves no separation.  **No `P ≠ NP` claim.**
