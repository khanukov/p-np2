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

## 6. Bounded-loop primitive — **BUILT** (`BoundedLoopProgram.lean`)

`seq`/`seqList` are straight-line (no back-edges) and `numPhases` is a literal `Nat`.  The key
realization (vs. the original plan, which assumed a hard back-edge construct was required): a loop
over a **symbolic** count `k` (e.g. `k = 2^n`) needs **no** back-edge — `seqList (List.replicate k body)`
is a well-typed `ConstStatePhasedProgram` for any `k`, and the toolkit's existing `seqList`
recurrences already give its time and run behaviour.  Built as:

* `ConstStatePhasedProgram.repeatProgram body k := seqList (List.replicate k body)`;
* `repeatProgram_timeBound : (repeatProgram body k).timeBound n = k * body.timeBound n + k`
  — polynomial-composable: with `k = 2^n` and `body.timeBound n = poly(n)`, the loop costs
  `poly(2^n) = poly(L)`;
* `repeatProgram_succ` (one peel, `rfl`) and `repeatProgram_run_succ` (per-iteration run
  decomposition, inherited from `seqList_run_decomp`) — the inductive backbone for the loop invariant.

So step 6's `2^n`-row evaluation loop is expressible with existing infrastructure.  What remains for
the loop is a *concrete* invariant proved against the specific row-evaluation body, applying
`repeatProgram_run_succ` peel-by-peel together with the tape-position lemmas of §4–5.

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

1. **`boundedLoopProgram`** + composition reasoning layer (§6, §6a) — **DONE**.
2. **Parse-on-tape** — *tag check **DONE*** (`TreeMCSPTagCheckProgram.lean`: program, `timeBound`,
   `neverMovesLeft`, single-step lemmas, `runConfig_scan`, accept-iff, matched-state, semantic
   correctness `accepts ⇔ leading bits = tag`, Prop characterization).  **Remaining:** gamma-decode
   `n` (variable-length scan; the pure spec `decodeGamma?` is already proven, so this realizes it
   on tape — tape-based counting via the now-proven `incrementProgram_correct`), length-convention
   check.
3. **Witness slice + prefix-agreement compare** (bounded scan; `combineAtOffset` per-bit) — *remaining*.
4. **On-tape circuit decode + single-row evaluation** — single-row eval is the proven
   `circuitEvaluatorCS`; the open piece is realizing **this codec's** decoder on tape, or proving it
   agrees with `Encoding.CircuitTree` (the §9 codec caveat) — *remaining, hardest single risk*.
5. **Row-iteration verification** — the `2^n`-row loop; `mcspCheckAllRows`/`RowConsistencyCheck`
   supply the per-row body + `timeBound`; the open piece is the **loop correctness invariant**
   (`repeatProgram_run_succ` peel-by-peel) — *remaining*.
6. **Assemble `M`**, prove the bridge (★), discharge `runTime_poly`, build the
   `PrefixExtensionNPWitness`, and feed it to `verifiedSource_treePoly`'s second hypothesis — *remaining*.

> **Toolkit status (verified, do not rebuild):** atomics, `seq`/`seqList`, gate evaluators
> (`GateWrappers`), single-row `circuitEvaluatorCS`, `CircuitTree` encode/decode round-trips, the
> binary counter **incl. `incrementProgram_correct`** (carry propagation — proven; the stale
> "Session 7c will prove" comment notwithstanding), `RowConsistencyCheck`/`mcspCheckAllRows`
> `timeBound`.  The NP-verifier track adds §6/§6a (bounded loop + composition layer) and the
> tag-check phase.  The genuinely missing core is the gamma-decode/parse orchestration, the row-loop
> *correctness* invariant, the codec-layout reconciliation (§9), and the final assembly.

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

Reusable beyond §3: `circuitEvaluatorCS` (`GateWrappers.lean:569`) is a **complete, proven** evaluator
of a gate list at offsets, and `alwaysAccept`/`alwaysReject` are complete TMs. So *single-row* circuit
evaluation is already built; the genuinely missing piece is the **row loop** (§6).

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
