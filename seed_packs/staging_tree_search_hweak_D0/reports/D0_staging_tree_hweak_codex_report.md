# D0 stagingTreeSearchTarget hWeak feasibility audit

## 1. Executive verdict

**YELLOW_CODEC_TOO_INEFFICIENT_BUT_USEFUL_FOR_INTERFACE**

Reason: the pinned staging target is well-typed and relation-strong (decoded
circuit must actually compute the input truth table under threshold), but its
finite-index/one-hot witness representation makes witness width enormous and
pushes `noBoundedSolver` toward an encoding-artifact hardness regime rather than
clean structural search hardness.

---

## 2. Target unpacking

For `stagingTreeSearchTarget`:

- `problem.instanceBits n = Partial.tableLen n` (truth-table length for `n`-var instances).
- `problem.witnessBits n = finiteIndexWitnessBits stagingTreeThreshold n`.
- `problem.promise n tt = treeMCSPPredicate n (stagingTreeThreshold n) tt`.
- `problem.relation n tt w` is codec verification via `decode w = some c ∧ size c ≤ threshold n ∧ ComputesTruthTable treeCircuitClass c tt`.
- `circuitClass = C_DAG`.
- `sizeBound n = stagingSolverSizeBound n = n^2 + 1`.

So the weak-lower-bound proposition is:

`SearchProblemNoBoundedSolver problem C_DAG (fun n => n^2 + 1)`

for the above staged codec problem.

---

## 3. WitnessBits scale audit

`finiteIndexWitnessBits threshold n = card(circuitsOfSizeAtMost n (threshold n)) + 1`.

With `stagingTreeThreshold n = n + 1`, this means:

- witness length is the number of enumerated circuits up to staged bound + spare bit;
- the solver must output **one circuit per witness bit** (by `BoundedSearchSolver.outputCircuit`);
- hence solver family arity grows with this cardinality, not with a compact encoding length.

Qualitatively, this scale is very large relative to instance length `tableLen n` and
is driven by enumeration cardinality, not by a compressed circuit description.

Verdict on scale: **encoding-inflated** and likely to make `noBoundedSolver`
artificially easier to satisfy (because required output dimensionality explodes).

---

## 4. Trivial solver audit

Attempted trivial strategies:

1. **Always output default index / all-false**: fails in general, because relation
   requires decoding to a circuit computing the specific input truth table.
2. **Universal witness across promises**: fails; promised instances are many truth
   tables, each generally needing different computing circuit witness.
3. **Exploit threshold `n+1`**: helps only for promised inputs that already have
   such small circuits; still does not yield a single universal witness function.
4. **Exploit one-hot shape**: one-hot eases decoder reasoning, but does not remove
   semantic correctness (`ComputesTruthTable`) constraint.

Conclusion: no immediate trivial bounded solver construction is evident.

---

## 5. Promise density audit

Promise is `treeMCSPPredicate n (n+1) tt`.

- Promised set is nonempty (contains low-complexity tables).
- It is not “single-witness only”: there can be many circuits computing a table.
- But threshold is tiny relative to full truth-table space, so promise is a sparse
  low-complexity slice.

This does **not** automatically make solver trivial; it only limits instances to
small-circuit tables.

---

## 6. Relation audit

Relation strength is adequate for correctness:

- witness is decoded to an actual `Circuit n`;
- decoded circuit must satisfy size bound (`≤ threshold n`);
- decoded circuit must compute the provided truth table.

So relation is semantically meaningful, not a weak placeholder.

---

## 7. hWeak plausibility

Target proposition:

`SearchProblemNoBoundedSolver stagingTreeSearchTarget.problem C_DAG stagingSolverSizeBound`.

Assessment:

- Not obviously false (no quick trivial solver found).
- But also not a clean “natural” weak lower bound because witness-output width is
  dominated by finset cardinality of staged enumeration.
- Therefore plausibility as *mathematical mainline evidence* is reduced; this is
  better viewed as interface stress-test hardness.

Classification: plausible as staging stress target, weak as final-form hWeak candidate.

---

## 8. Magnification relevance

Even if this staged `hWeak` were proved, magnification relevance is questionable:

- the witness encoding is intentionally inefficient one-hot finite-index;
- hardness may largely reflect representation blowup rather than intrinsic search-MCSP structure.

So this target is good for plumbing/proof-engineering, but likely needs codec/scale
repair before serving as persuasive `hMag`-facing source.

---

## 9. Recommendation

**open_efficient_structural_codec_route**

Concrete next step:

1. Keep this staging target for interface tests.
2. Design a more structural/compact codec (length polynomial in natural instance
   parameters, not finset cardinality).
3. Re-pin a repaired target and re-run hWeak feasibility against that repaired
   witness scale.

