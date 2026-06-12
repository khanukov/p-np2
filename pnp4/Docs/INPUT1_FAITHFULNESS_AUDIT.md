# Input 1 (`ResearchGapWitness`) — Faithfulness Audit and the DAG Counting Frontier

Updated: 2026-06-12

This document records a focused audit session on the single remaining input
("input 1") of the public final theorems, and the new unconditional theorem
layer it produced (`pnp4/Pnp4/AlgorithmsToLowerBounds/DagShannonCounting.lean`).

## 1. What input 1 is

The public default endpoints are:

```text
NP_not_subset_PpolyDAG_final (gap : ResearchGapWitness)
P_ne_NP_final               (gap : ResearchGapWitness)
```

`ResearchGapWitness` has a single mathematical field:

```text
dagSeparation : ComplexityInterfaces.NP_not_subset_PpolyDAG
              = ∃ L, NP L ∧ ¬ PpolyDAG L
```

So input 1 is exactly the classical open problem `NP ⊄ P/poly` stated against
the strict in-repo classes.

## 2. Faithfulness audit of the formal statement

The session re-derived the definitional chain from scratch and checked it for
exploitable mismatches with the intended mathematical statement.

1. `Language = ∀ n, Bitstring n → Bool` with `Bitstring n = Fin n → Bool`.
   Faithful (length-indexed family of Boolean functions).
2. `NP = NP_TM`: a single-tape deterministic verifier TM (finite control,
   binary alphabet, standard step semantics in `TuringEncoding.lean`) with
   certificate length exactly `n ^ k + k` and runtime field bounded by
   `m ^ c + c` on the relevant lengths.  Faithful, with one quirk noted
   below.
3. `PpolyDAG`: families of acyclic DAG circuits over `{const, ¬, ∧, ∨}`
   (fan-in ≤ 2), size counted as gate count + 1, exact correctness at every
   length, polynomial bound `∃ c, ∀ n, polyBound n ≤ n ^ c + c`.  Faithful
   (standard non-uniform `P/poly` over a complete basis).

### The `runTime` advice quirk (checked, not exploitable)

`TM.runTime : ℕ → ℕ` is an arbitrary (possibly noncomputable) function field,
and acceptance is "control state equals `accept` after exactly `runTime m`
steps".  A machine can therefore extract `O(log m)` bits of nonuniform advice
per length from the value `runTime m ≤ m ^ c + c`.  Consequences:

- `NP ⊆ NP_TM ⊆ NTIME(poly)/O(log n)` (the advice being the step count);
- by the standard hardwiring argument, `NP ⊆ P/poly` implies
  `NP/O(log) ⊆ P/poly`; contrapositively, any proof of the formal statement
  `∃ L, NP_TM L ∧ ¬ PpolyDAG L` yields the real-world `NP ⊄ P/poly`;
- conversely a real-world proof of `NP ⊄ P/poly` (for this machine model)
  instantiates the formal statement, since `NP ⊆ NP_TM`.

A concrete probe confirming the quirk is absorbed by non-uniformity on the
circuit side: every length-only language `L n x = g n` (arbitrary
`g : ℕ → Bool`, including noncomputable `g`) is in `NP_TM` via a two-state
flip-flop machine whose `runTime` parity encodes `g`; but every such language
is also in `PpolyDAG` via the constant-gate family, so no separation leaks
from the quirk.

### Audit conclusion

The formal statement of input 1 is equivalent (up to the standard model
robustness above) to the genuine open problem `NP ⊄ P/poly`.  There is no
definitional shortcut: because the active tree is axiom-free and Lean's
kernel is sound, any compiling inhabitant of `ResearchGapWitness` would be an
actual mathematical solution of the open problem.  "Clever" routes that avoid
the mathematical content (extra axioms, vacuous hypotheses, statement
weakening) are exactly what the Research Constitution forbids and what the
falsifiability audits exist to catch.

## 3. External frontier check (June 2026)

A literature sweep found no published or claimed proof of `NP ⊄ P/poly`
(nor of the weaker `NEXP ⊄ P/poly`).  The live programme closest to this
repository's mainline remains hardness magnification for MCSP-style problems
(Oliveira–Pich–Santhanam; McKay–Murray–Williams), with the locality barrier
(Chen–Hirahara–Oliveira–Pich–Rathi–Santhanam) as the standing obstruction to
completing it with known lower-bound techniques.  This matches the repo's
existing framing in `pnp4/README.md` and
`pnp3/Magnification/UnconditionalResearchGap.lean`.

## 4. What was added in this session

`DagShannonCounting.lean` makes the *hardness half* of input 1 unconditional
at the exact endpoint class:

1. `dagCodeBound n g = (8 (n+g+1)²)^g (n+g+1)`: explicit bound on the number
   of flat DAG descriptions; every `DagCircuit` with at most `g` gates is
   simulated by such a description (`gateValueFuel_encodeCircuit`,
   `codeEval_encodeCircuit`), so at most `dagCodeBound n g` distinct Boolean
   functions are computable within the budget.
2. `exists_hard_function_for_dag_gates`: Shannon escape — once
   `dagCodeBound n g < 2 ^ (2 ^ n)`, some `n`-input function defeats every
   DAG circuit with at most `g` gates.
3. `dagHardBudget n = Nat.findGreatest (dagCodeBound n · < 2 ^ 2 ^ n) (2 ^ n)`:
   a self-calibrating per-length budget, with
   `dagHardBudget_superPolynomial : ∀ c, ∃ n ≥ 2, n ^ c + c ≤ dagHardBudget n`.
4. `dagHardLanguage` and the unconditional theorems

   ```text
   dagHardLanguage_not_PpolyDAG : ¬ PpolyDAG dagHardLanguage
   exists_language_not_PpolyDAG : ∃ L, ¬ PpolyDAG L
   ```

5. The honesty marker
   `NP_not_subset_PpolyDAG_of_NP_dagHardLanguage : NP dagHardLanguage →
   NP_not_subset_PpolyDAG`, documenting the exact remaining gap.  This is
   *not* a proposed closure route: the diagonal witness is a classical choice
   object with no verifier, and there is no reason to expect its hypothesis
   to hold.

Axiom audit of the new surface: `[propext, Classical.choice, Quot.sound]`
only; no project-local axioms, no `sorry`, no `native_decide`.

## 5. Classification per `AGENTS.md`

This work does **not** reduce the `NP`-membership half of
`VerifiedNPDAGLowerBoundSource` or `SearchMCSPWeakLowerBound`, so it is not
claimed as mainline progress.  It is endpoint-level unconditional counting
infrastructure that (a) pins the research gap to its sharp residual form —
*produce a language that is simultaneously `NP` and outside `PpolyDAG`* —
and (b) supplies the DAG-side counting engine that any future fair-side /
random-truth-table argument against `PpolyDAG` solvers will need.

## 6. What would close input 1 (unchanged)

A non-vacuous proof of `ComplexityInterfaces.NP_not_subset_PpolyDAG`
respecting the constraints listed in
`pnp3/Magnification/UnconditionalResearchGap.lean`.  Nothing in this session
changes the honest assessment that this is an open research-level problem;
the session's contribution is to make the already-known half formal and to
verify that the remaining half is stated faithfully.
