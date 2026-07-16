# P = coP, machine-checked in Lean 4

A complete, unconditional, kernel-checked proof that **the class P is
closed under complement**, over an explicit deterministic Turing-machine
model, in Lean 4 — with **zero external dependencies** (no mathlib, no
axiom declarations, no `sorry`).

```lean
theorem P_closed_under_complement (L : Language) (hL : P L) : P L.complement

theorem P_eq_coP (L : Language) : P L ↔ P L.complement
```

The kernel-reported axiom footprint (pinned in CI by `#guard_msgs`):

| Theorem | Axioms used |
|---|---|
| `P_closed_under_complement` | `propext` |
| `P_eq_coP` | `propext`, `Quot.sound` |
| `parity_in_P` | `propext`, `Quot.sound` |

No `Classical.choice`, no project axioms, no `sorry`/`admit`/`native_decide`.
All three names above are Lean's standard axioms.

## How to verify (2 minutes)

```bash
cd pcop
lake build          # elaborates and kernel-checks every proof; the
                    # #guard_msgs blocks in PCoP/Main.lean fail the build
                    # if any axiom footprint changes
```

With `elan` installed, the pinned toolchain (`lean-toolchain`:
`leanprover/lean4:v4.30.0`) is fetched automatically.  For an
*independent* check, replay every declaration through a fresh kernel with
the bundled external checker:

```bash
for m in PCoP.Basic PCoP.Machine PCoP.Complement PCoP.Parity PCoP.Main; do
  LEAN_PATH=.lake/build/lib/lean leanchecker "$m" || echo "FAILED: $m"
done
```

There is nothing else to trust: the package has no dependencies, so the
entire trusted base is the Lean kernel plus the ~700 lines of this
library, most of which are definitions you can read in one sitting.

## The model (`PCoP/Machine.lean`)

A deterministic single-tape Turing machine in the style of Sipser
(*Introduction to the Theory of Computation*, Def. 3.3):

* **states** are `Fin k` for an explicit `k : Nat` — the machine is
  finite data (start state, halting table, transition table on the
  finite domain `Fin k × Sym`);
* **tape** is one-way infinite over the alphabet `Sym = Option Bool`
  (`some b` = bit, `none` = blank), so the input is blank-delimited;
* **halting**: `halted q = some b` means `q` is a halting state with
  verdict `b` — i.e. the halting states are partitioned into accepting
  (`b = true`) and rejecting (`b = false`) states, exactly as in
  Sipser's definition of a decider.  Halting configurations are fixed
  points of the step function;
* **the class**:

  ```lean
  def P (L : Language) : Prop :=
    ∃ (M : TM) (T : Nat → Nat), PolyBounded T ∧ DecidesWithin M T L
  ```

  where `PolyBounded T ↔ ∃ c, ∀ n, T n ≤ n ^ c + c` and
  `DecidesWithin M T L` says that on every input of length `n` the
  machine has halted after `T n` steps with verdict `L n x`.

Languages are `Bool`-valued (`Language := (n : Nat) → (Fin n → Bool) → Bool`),
so the complement is the total operation `fun n x => !(L n x)` — no
decidability side conditions anywhere.

## The proof (`PCoP/Complement.lean`)

The textbook argument, executed literally.  The complement machine
*swaps which halting states count as accepting*:

```lean
def TM.complement (M : TM) : TM :=
  { M with halted := fun q => (M.halted q).map (fun b => !b) }
```

Same states, same start state, same transition table, negated verdicts.
The two lemmas that make the swap sound are exactly the two places where
a poorly chosen model breaks the proof:

1. `run_complement` — the dynamics never consult the verdicts, only
   *whether* a state is halting, which negation preserves; so the run is
   unchanged.
2. `DecidesWithin.complement` — the complement machine halts at the same
   step with the negated verdict, so the **same time bound `T`**
   witnesses membership: the complement costs zero extra time.

Additionally, `TM.output_mono` proves the clock semantics is robust:
once the machine halts, its verdict is stable, so the exact sampling
moment is irrelevant (`DecidesWithin.mono`: any larger time bound works).

## Non-degeneracy witnesses (`PCoP/Parity.lean`)

A class defined in a fresh model deserves evidence it is not degenerate:

* `const_in_P` — the constant languages are in `P` (a 1-state machine);
* `parity_in_P` — **PARITY ∈ P** by an explicit 4-state machine that
  scans the input, keeps the running parity in its finite control, and
  halts on the first blank, with the proved time bound `T n = n + 1`;
* `parity_complement_in_P` — the complement of parity, via the closure
  theorem, with the same time bound.

## Design rationale: why these definitions

This package lives inside a larger project (`p-np2`) whose frozen
P-vs-NP interface uses a different machine model.  Attempting the
complement theorem against *that* model revealed three genuine obstacles,
each traceable to a model-design choice; this package is the repaired
model, and each repair is load-bearing for the theorem:

1. **Acceptance by halting verdict, not by a single distinguished
   accept state.**  With one accept state and no reject state, "final
   state ≠ accept" covers `k − 1` states and cannot be re-expressed as
   "final state = q′" for any single `q′`; the classical swap is
   inexpressible.  Partitioned halting verdicts are Sipser's decider,
   and the swap becomes a one-line table negation.

2. **The clock belongs to the class, not to the machine.**  If the time
   bound is a field of the machine, an arbitrary `runTime : Nat → Nat`
   acts as an uncomputable length-indexed advice channel (in the frozen
   model of the host project, every length-only language — including
   undecidable ones — lands in "P" through a 2-state machine whose
   clock encodes the answer).  Here a machine has no clock; `P`
   existentially quantifies over polynomially bounded time bounds, and
   `output_mono` makes the sampling moment irrelevant.

3. **A blank-delimited alphabet.**  If the blank coincides with the bit
   `0`, no machine can locate the end of its input.  With
   `Sym = Option Bool` the parity machine detects the end of input by
   reading `none` — which is what makes the explicit witnesses possible.

One further choice is worth naming: **finite control (`Fin k`) is
load-bearing.**  If the state space were an arbitrary type, a "machine"
could record the entire read history in its state and a classical
halting table could decide *every* language, collapsing the class.

## What is claimed, honestly

`P = coP` is textbook-trivial mathematics; no new complexity theory is
claimed.  The contribution is: (a) a complete machine-checked pipeline —
model, class, closure theorem, explicit inhabitation witnesses with
proved runtimes — small enough to audit in an afternoon and checkable by
an independent kernel; and (b) the documented model-design lessons above,
which were extracted the hard way from a model where this "trivial"
theorem is likely false as stated.  This package makes no claim
whatsoever about P vs NP.

## Files

| File | Contents |
|---|---|
| `PCoP/Basic.lean` | bit strings, languages, complement, involution |
| `PCoP/Machine.lean` | the TM model, configurations, runs, `output_mono`, the class `P` |
| `PCoP/Complement.lean` | the complement machine, `P_closed_under_complement`, `P_eq_coP` |
| `PCoP/Parity.lean` | explicit machines: constants and PARITY, with proved runtimes |
| `PCoP/Main.lean` | top-level statements and the `#guard_msgs`-pinned axiom audit |
