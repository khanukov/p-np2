# `P ⊆ P/poly` — faithfulness audit map

Updated: 2026-05-29.
Scope: the inclusion side only (`P ⊆ PpolyDAG`).  This is the auditor-facing
argument that the machine-checked endpoint is **faithful** — i.e. that the
statement it proves is the real one and is not satisfied vacuously.

## 0. What the Lean kernel already guarantees (and what it does not)

`#print axioms Pnp3.Complexity.Simulation.proved_P_subset_PpolyDAG_internal`
reports exactly `[propext, Classical.choice, Quot.sound]` — the three standard
Lean/Mathlib axioms, with **no** `sorryAx` and **no** project-local `axiom`.
The same holds for `Pnp3.Magnification.P_ne_NP_final`.  Therefore the kernel has
checked that every proof term is valid: **the proofs are correct relative to
their stated types.**

The kernel does *not* check that the *statements* mean what their names
suggest.  That is the job of this document: confirm every definition in the
trust chain is faithful and that no theorem is a vacuous victory.

A whole-file red-flag scan of `Simulation.lean` is clean: `0` of
`sorry` / `admit` / `native_decide`, no statement of the form `: True` /
`= True`, no `Nonempty`-trick conclusions, no whole-proof `trivial`, and no
direct `Classical.choose`.  The only `decide` uses are the genuine indicators
`decide (c.head = i)` / `decide (c.state = q)` and ordinary boolean case
analysis.

## 1. The endpoint and the target

```text
Complexity.Simulation.proved_P_subset_PpolyDAG_internal
  : ComplexityInterfaces.P_subset_PpolyDAG          -- Circuit_Compiler.lean
```

with the target unfolding (`Complexity/Interfaces.lean`)

```text
P_subset_PpolyDAG := ∀ L, P L → PpolyDAG L
```

Both classes are faithful (audited separately, summarised here):

* `P L := polyTimeDecider L`
  (`PsubsetPpolyInternal/ComplexityInterfaces.lean`): there is a deterministic
  one-tape Turing machine `M` and `c` with `M.runTime n ≤ n^c + c` and
  `TM.accepts M n x = L n x` for all `n, x`.  The TM model in
  `PsubsetPpolyInternal/TuringEncoding.lean` is a textbook single-tape DTM
  (`step : state → Bool → state × Bool × Move`, finite control, genuine
  `stepConfig`/`runConfig`, `tapeLength = n + runTime n + 1`,
  `accepts = decide (state after runTime n steps = accept)`).

* `PpolyDAG L := ∃ _ : InPpolyDAG L, True` (`Complexity/Interfaces.lean`):
  a family of acyclic Boolean `DagCircuit`s (`and/or/not/const`, acyclicity
  enforced by the dependent gate index) with a **real** size bound
  `DagCircuit.size (family n) ≤ polyBound n` and **real** polynomiality
  `∃ c, ∀ n, polyBound n ≤ n^c + c`, satisfying
  `DagCircuit.eval (family n) x = L n x`.

So the endpoint is the genuine "every polynomial-time language has a
polynomial-size circuit family" statement.

## 2. The construction (Circuit_Compiler.lean)

For `L ∈ P`, `exists_poly_tm_for_P` extracts `(M, c)`.  The witness family is

```text
family n := acceptCircuitOf M (runtimeConfigCompiledLinear M n)   -- a StraightLineCircuit
```

converted to a `DagCircuit` by `toDag`.  The `InPpolyDAG` obligations are
discharged by three contracts, each closed internally:

1. `CompiledRuntimeCircuitSizeBoundLinear` — polynomial size;
2. `CompiledRuntimeAcceptCorrectnessLinear` — the circuit equals `TM.accepts`;
3. `CompiledAcceptOutputWireAgreementLinear` — the two evaluators agree
   (`StraightLineAdapter.eval`, used by `DagCircuit`, vs the internal
   `StraightLine.eval`, used by the spec), so the correctness proven for one
   transfers to the other.  `size_toDag` gives `(toDag C).size = C.gates + 1`,
   so the size bound is on the **genuine** DAG size.

## 3. Correctness chain (Simulation.lean) — faithful, non-vacuous

The correctness invariant is

```text
structure Spec (sc : StraightConfig M n) (f : Point n → TM.Configuration M n) : Prop
  tape_eq  : ∀ x i, evalTape  sc x i = (f x).tape i
  head_eq  : ∀ x i, evalHead  sc x i = headIndicator     (f x) i
  state_eq : ∀ x q, evalState sc x q = stateIndicator M  (f x) q
```

where `evalTape sc x i = StraightLine.evalWire sc.circuit x (sc.tape i)` is the
genuine evaluation of the circuit's tape-wire `i` on input `x`, and
`headIndicator c i = decide (c.head = i)`,
`stateIndicator M c q = decide (c.state = q)` are genuine indicators.  Thus
`Spec sc f` says exactly "the straight-line circuit `sc` computes the
configuration `f` (tape contents, head position, control state) on every
input".  It is a conjunction of pointwise equalities — not vacuous.

The chain that produces `Spec` for the runtime family and reads off acceptance:

| Step | Declaration | Faithful statement |
|------|-------------|--------------------|
| init | `initialStraightConfig_spec` | `Spec (initialStraightConfig M n) (M.initialConfig)` — the base circuit encodes input/blank tape, head at 0, state `start`. |
| one step | `stepCompiledLinearCandidateStepSpecProvider_internal` | `∀ sc f, Spec sc f → Spec (step sc) (TM.stepConfig ∘ f)`, from the three field specs `stepCompiledLinearCandidate{Tape,Head,State}_spec_internal`. |
| iterate | `runtime_spec_of_next` / `iterate_spec_of_next` | lifts one-step preservation to `Spec (iterate step (runTime n) init) (M.run)`, using `M.run = iterate stepConfig (runTime n) initialConfig`. |
| accept | `acceptCircuitOf_spec_of_runSpec` | `Spec sc (M.run) → eval (acceptCircuitOf M sc) x = TM.accepts M n x`, because `acceptCircuitOf` outputs the accept-state wire and `stateIndicator M (M.run x) accept = decide ((M.run x).state = accept) = TM.accepts`. |

`stepCompiledLinearCandidate` is a real append-only builder
(`buildNextTapeAll → buildNextHeadAll → buildNextStateAll`), not `id`; the
~5.6k-line `BuiltWire` namespace proves the field specs above.  Those proofs are
kernel-checked; what matters for faithfulness is that their **statements** pin
`evalTape/Head/State (step sc)` to the *next* TM configuration, which they do.

## 4. Size chain — bound is on the real gate count, and is polynomial

| Step | Declaration | Statement |
|------|-------------|-----------|
| per step | `stepCompiledLinearCandidate_gates_le_budgetExpanded` | one step adds ≤ `linearStepBudgetExpanded M n` gates. |
| iterate | `iterate_gates_le_of_next_gates_le` | `(iterate step t init).gates ≤ init.gates + t · inc`. |
| runtime | `runtimeConfigCompiledLinear_gates_le_budgetExpanded` | `gates ≤ 2 + runTime n · linearStepBudgetExpanded M n` (init has 2 gates). |
| polynomial | `Circuit_Compiler.compiledRuntimeBudgetPolyBound_internal` | `2 + runTime n · budget ≤ n^k + k` for some `k`, using `runTime n ≤ n^c + c` and `tapeLength n ≤ n^(c+3)`. |

`gates` is the straight-line circuit's actual gate count and `(toDag C).size =
C.gates + 1`, so the polynomial bound is genuinely the circuit size.

## 5. Honest scope caveat

This is a **coarse** polynomial-size inclusion (see
`Simulation_FineGrained_Status.md`).  It is *not* a fine-grained Cook–Levin /
hardness-magnification adequacy theorem and proves no small explicit exponent
or `O(T log T)`-style bound.  That is sufficient for the only consumer in this
repository, the DAG-side of `P ≠ NP` (which needs just `P ⊆ PpolyDAG`), but a
future magnification route depending on exact overhead would need a separate
fine-grained simulation proof.

## 6. Reproduce the checks

```bash
lake build PnP3 Pnp4
# faithfulness-relevant axiom surface:
lake env lean <<'EOF'
import Magnification.UnconditionalResearchGap
import Complexity.Simulation.Circuit_Compiler
#print axioms Pnp3.Complexity.Simulation.proved_P_subset_PpolyDAG_internal
#print axioms Pnp3.Magnification.P_ne_NP_final
EOF
./scripts/check.sh           # build + smoke + tests + hygiene + audits
```

See also `PsubsetPpoly_AUDITOR_CHECKLIST.md` (runnable spot checks),
`PsubsetPpoly_Internal_TODO.md`, and `Simulation_FineGrained_Status.md`.
