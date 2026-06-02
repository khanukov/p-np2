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
