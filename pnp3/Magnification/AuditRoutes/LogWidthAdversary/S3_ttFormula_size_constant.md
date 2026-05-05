# S3 structured failure: `ttFormula_size_le` with constant `6`

## 1. What was attempted

Slot S3 was selected by running the required `secrets.randbelow(10) + 1`
command, which returned `3`.  I attempted to close the seed-pack T2 target

```lean
theorem ttFormula_size_le (k : Nat) (f : Bitstring k → Bool) :
    FormulaCircuit.size (ttFormula f) ≤ 6 * 2 ^ k
```

in the designated S3 file
`pnp3/Magnification/AuditRoutes/LogWidthAdversary/TTFormulaSizeBound.lean`.
The attempted proof imported `Tests.FormulaSupportBoundsFalsifiabilityProbe`,
used the already-existing recursive `ttFormula`, and added only a local
private helper showing that `FormulaCircuit.rename` preserves
`FormulaCircuit.size`.  The intended induction was:

* base `k = 0`: `ttFormula f` is one `const`, so size is `1 ≤ 6`;
* step `k + 1`: unfold the existing `ttFormula`, rewrite both renamed
  recursive calls using the private `rename_size` helper, and combine the two
  induction hypotheses with arithmetic.

## 2. Where it broke

The proof breaks at the arithmetic step because the actual constructor count of
the committed `ttFormula` is larger than the seed pack's `6 * 2^k` target can
support inductively.

For successor width, the current definition in
`pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean` builds

```lean
(¬ x₀ ∧ c0') ∨ (x₀ ∧ c1')
```

where `c0'` and `c1'` are renamed recursive formulas.  With the current
`FormulaCircuit.size` definition:

* `¬ x₀` contributes size `2` (`input` plus `not`);
* the left `and` contributes an additional `1`;
* the right occurrence of `x₀` contributes size `1`;
* the right `and` contributes an additional `1`;
* the outer `or` contributes an additional `1`.

Thus the exact recurrence is

```text
S(k + 1) = S(k, f0) + S(k, f1) + 6
```

not a recurrence with zero overhead.  Lean reached the following final
arithmetic obstruction after unfolding size and applying the two induction
hypotheses:

```text
error: pnp3/Magnification/AuditRoutes/LogWidthAdversary/TTFormulaSizeBound.lean:75:6:
omega could not prove the goal:
a possible counterexample may satisfy the constraints
  c ≥ 0
  b ≥ 0
  a ≥ 0
  6*a - b ≥ 0
  6*a - c ≥ 0
  0 ≤ 12*a - b - c ≤ 5
where
 a := ↑2 ^ k
 b := ↑(ttFormula f0).size
 c := ↑(ttFormula f1).size
```

This is not just a proof-search issue.  The target statement is false for the
existing `ttFormula`: the exact worst-case-independent recurrence from the
committed constructors gives

```text
S(0) = 1
S(1) = 1 + 1 + 6 = 8
S(2) = 8 + 8 + 6 = 22
S(3) = 22 + 22 + 6 = 50
```

but `6 * 2^3 = 48`.  Therefore the requested bound fails already at width
`k = 3`, independent of the Boolean function `f`.

## 3. Local vs global obstruction

This is a local obstruction to the S3 statement as written, not a global
obstruction to the log-width hardwiring lift.

The global program only needs a polynomial-size bound for the truth-table-shaped
subformula.  The current `ttFormula` appears to satisfy the slightly weaker and
still perfectly usable estimate

```lean
FormulaCircuit.size (ttFormula f) ≤ 7 * 2 ^ k
```

because the exact closed form of the recurrence is `7 * 2^k - 6`.  A bound such
as `8 * 2^k` should be even easier.  The obstruction is specifically that the
seed-pack constant `6` is too small for the committed formula syntax and size
accounting.

Under the slot rules, I did not replace the requested theorem by a different
public theorem, did not edit the existing `ttFormula`, and did not change any
forbidden trust-root or integration files.

## 4. What S11/integration must know

S11 should not assume the S3 target with coefficient `6` is available for the
current `ttFormula`.  Integration should either:

1. change the downstream polynomial bound to use coefficient `7` or `8`, e.g.
   `polyBound n := 8 * (n + 1)`, if the width helper supplies
   `2^width ≤ n + 1`; or
2. introduce a more size-efficient truth-table formula constructor whose
   committed size recurrence actually supports the coefficient `6`.

The first option is likely simpler and does not affect the scientific content:
any fixed constant coefficient still gives the needed polynomial-size
hardwiring family.

## 5. Exact files/lemmas inspected

* `seed_packs/fp3b1_log_width_hardwiring_lift/README.md` — S3 target and
  allowed/forbidden scope.
* `seed_packs/fp3b1_log_width_hardwiring_lift/WORKER_PROMPT.md` — stricter
  worker-level output and failure-report instructions.
* `RESEARCH_CONSTITUTION.md` — research-governance and route-scope rules.
* `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean` — FP3b1 packaging
  skeleton and `InSupportFunctionalDiversity` context.
* `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean` — existing
  `FormulaCircuit.rename`, `ttFormula`, and `ttFormula_eval` definitions.
* `pnp3/Complexity/Interfaces.lean` — `FormulaCircuit.size` constructor
  accounting, read only to inspect the trusted syntax/size definitions.
* `scripts/check.sh` — required repository check command.
* attempted local helper: private `rename_size`, by structural induction on
  `FormulaCircuit`, in the discarded S3 Lean file.

## 6. Suggested next move

Have a follow-up S3/S11 integration worker land the true replacement lemma,
preferably one of:

```lean
theorem ttFormula_size_le_seven (k : Nat) (f : Bitstring k → Bool) :
    FormulaCircuit.size (ttFormula f) ≤ 7 * 2 ^ k
```

or

```lean
theorem ttFormula_size_le_eight (k : Nat) (f : Bitstring k → Bool) :
    FormulaCircuit.size (ttFormula f) ≤ 8 * 2 ^ k
```

Then adjust the later family packaging to use the corresponding constant in
`polyBound`.  If the exact theorem name `ttFormula_size_le` must be retained,
its statement should be corrected to a coefficient at least `7` for the current
`ttFormula` definition.
