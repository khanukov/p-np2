# Task: CircuitPHP proof-complexity audit D1

## Handle:
`codex53`

## Outcome:
Completed literature/theory audit for CircuitPHP as a candidate weak search lower-bound source.

## 1) Executive verdict

**LIT_RED_AS_HARD_AS_MAIN_GAP**

Reason in one line: the specific lower-bound needed by the pnp4 weak-target interface
(`noBoundedSolver` against arbitrary polynomial-size nonuniform DAG-circuit solvers)
has no known theorem path from current PHP/TFNP/PPP machinery, and appears comparable to
core unresolved nonuniform lower-bound gaps.

---

## 2) Problem classification

We fix the CircuitPHP search task:

- Input: circuit `C : {0,1}^{m+1} -> {0,1}^m`.
- Output: `x != y` with `C(x)=C(y)`.

Classification:

- **TFNP:** yes (totality by pigeonhole principle).
- **PPP:** yes, this is the canonical computational pigeonhole form.
- **PWPP:** generally no immediate exact identification from the plain form above; PWPP is a restricted weak-pigeonhole flavor and needs explicit reduction arguments and promise shape.
- **Relation to PIGEON / WEAK-PIGEON:** direct relation to PIGEONHOLE-CIRCUIT style principles; weak-pigeon variants are nearby but not automatically equivalent in the exact encoding used for CircuitPHP.
- **Role in reductions:** natural complete-style target in the PPP ecosystem (under standard encoding conventions), and natural reduction target from other pigeonhole total-search tasks.

For the pnp4 frontier object, this means CircuitPHP is a **credible `SearchMCSPCompressionProblem` candidate object**, but credibility of the problem object is not the same as having the required lower bound.

---

## 3) Known lower bounds relevant to PHP search

### A) Query / black-box lower bounds

**Typical statement class:** oracle/query models require many queries to find a collision.

- **Model:** black-box access to function/circuit behavior.
- **Relevance:** can show hardness of generic oracle algorithms.
- **Does it imply `noBoundedSolver`?** **No.**
- **Why not:** pnp4 needs unconditional lower bounds against explicit nonuniform circuit families that read full circuit descriptions, not only black-box query access.

### B) Proof-system lower bounds

**Typical statement class:** exponential lower bounds for propositional proofs of PHP in restricted proof systems (resolution and relatives).

- **Model:** proof complexity (size/width/degree/rank in specific systems).
- **Relevance:** indicates combinatorial hardness of proving PHP formulas.
- **Does it imply `noBoundedSolver`?** **No (directly).**
- **Why not:** requires a transfer theorem from proof lower bounds to nonuniform search-circuit lower bounds for arbitrary DAG families; known transfers are system- and interpolation-dependent and not universal.

### C) Communication lower bounds

**Typical statement class:** high communication complexity for associated search/verification games.

- **Model:** communication protocols (often multi-party or partition-specific).
- **Relevance:** can separate protocol classes and imply restricted proof lower bounds.
- **Does it imply `noBoundedSolver`?** **No (directly).**
- **Why not:** communication hardness does not automatically produce global lower bounds against unrestricted polynomial-size circuit-output solvers.

### D) Restricted circuit/search lower bounds

**Typical statement class:** lower bounds for bounded-depth, monotone, restricted branching-program, or constrained extractor/selector solvers.

- **Model:** restricted nonuniform computational classes.
- **Relevance:** may support side-track milestones.
- **Does it imply `noBoundedSolver`?** **No (for full pnp4 target).**
- **Why not:** target quantifies over arbitrary `PpolyDAG`-style families (general polynomial-size DAG circuits), not only restricted subclasses.

### E) Arbitrary nonuniform circuit lower bounds

**Needed statement class (our exact need):**

> No polynomial-size nonuniform solver family outputs a valid collision for every
> input circuit `C : {0,1}^{m+1}->{0,1}^m`.

- **Model:** unrestricted polynomial-size nonuniform DAG-circuit families.
- **Known theorem support:** none known from standard PHP/PPP literature in this full strength.
- **Does existing literature imply `noBoundedSolver`?** **No known implication.**

Bottom line: known bounds are powerful in restricted models, but the endpoint needed by pnp4 appears to leap to the main unresolved level.

---

## 4) Feasible interpolation route

Question: can proof-complexity lower bounds for PHP imply no bounded search solver?

- **Potential mechanism:** interpolation theorems can extract circuit/protocol objects from proofs in systems with suitable interpolation properties.
- **What is needed here:** a theorem pipeline of the form
  1) short proofs of a suitable contradiction principle induce small solver/interpolant circuits;
  2) lower bounds against those interpolants force large proofs;
  3) converse bridge from hypothetical small search solver to short proofs in a system with interpolation;
  4) conclude no small search solver.
- **Gap:** this pipeline is highly proof-system-specific and usually yields restricted computational lower bounds (e.g., monotone/bounded-depth/protocol classes), not arbitrary `PpolyDAG` nonuniform lower bounds.

Assessment:

- feasible interpolation is **relevant as restricted-model evidence**;
- currently **not a known theorem path** to the required unrestricted pnp4 `noBoundedSolver` claim.

---

## 5) Bounded arithmetic route

- PHP-style totality principles are connected to provably total search problems of bounded arithmetic fragments.
- This gives a structural classification of total search complexity and links to proof complexity.
- However, from “provably total in theory T” to “no polynomial-size nonuniform solver circuits” one still needs major additional lower-bound machinery.

Assessment:

- bounded arithmetic offers explanatory and formalization guidance;
- no known direct implication to unrestricted nonuniform solver lower bounds required by CircuitPHP route.

---

## 6) Diagonalization route

D0 already identified the self-reference shape:

- given candidate solver family `S`, define `C_S` that invalidates `S(C_S)`.

Audit findings:

- **Recursion theorem in this setting:** the usual computability fixed-point intuition does not by itself hand you an efficient nonuniform circuit-level fixed-point construction with the required global guarantees.
- **Choosing `C` after `S`:** nonuniformly you can tailor adversarial objects to a fixed `S`, but turning this into a uniform theorem “for every polynomial-size family `S`” with size accounting and full correctness is exactly where hard lower-bound content enters.
- **Circularity barrier:** consistency between `⟨C⟩` used as solver input and the final realized `C` is nontrivial and closely aligned with known hard meta-construction barriers.

Conclusion: a formal diagonal route appears to require circuit lower-bound theorems of essentially the same difficulty class as the target gap.

---

## 7) Barrier audit

- **Natural proofs risk:** high. Any “large/useful/constructive” predicate against general small circuits risks natural-proof obstruction relative to pseudorandomness assumptions.
- **Relativization risk:** high. Black-box/oracle reasoning tends to relativize and is unlikely to settle nonuniform global lower bounds here.
- **Algebrization risk:** moderate-to-high. Algebraic lifts usually still fail to reach unrestricted nonuniform lower bounds.
- **Hardwiring risk:** high. Solver families can encode substantial per-length behavior; excluding hardwiring without inadvertently reintroducing main-gap hardness is difficult.

Net: barrier profile is consistent with “near-main-gap hardness” rather than an L0-open target.

---

## 8) Relation to pnp4 SearchMCSP

Can CircuitPHP be a:

- **`SearchMCSPWeakCircuitLowerBoundTarget`?**
  - **As a problem object:** yes, naturally.
  - **As a proved weak lower bound (`noBoundedSolver`) today:** no known theorem path.

- **replacement target for mainline magnification?**
  - Not currently; replacement only helps if accompanied by a proved magnification contract and actual weak lower bound proof.

- **only side-track?**
  - Presently yes: valuable for formalization/literature mapping, not yet for mainline endpoint discharge.

---

## 9) Recommendation

**keep_as_side_track**

Rationale:

1. The object is mathematically natural and useful for organizing TFNP/PPP/proof-complexity interfaces.
2. Existing theorem support appears restricted-model only.
3. No known route currently yields the exact unrestricted nonuniform lower bound required by pnp4 mainline contracts.

---

## Known theorem path:
No known theorem path from current literature to unrestricted CircuitPHP `noBoundedSolver` against arbitrary polynomial-size `PpolyDAG`-style families.

## Restricted lower bounds:
Yes—substantial evidence exists in proof complexity, communication, and restricted computational models; these do not currently lift to the required unrestricted nonuniform solver lower bound.

## Does it imply noBoundedSolver?
No (at the unrestricted pnp4 target strength).

## Commands run:
- `sed -n '1,220p' RESEARCH_CONSTITUTION.md`
- `sed -n '1,220p' pnp4/Pnp4/Frontier/SearchMCSPMagnification.lean`
- `sed -n '1,220p' pnp4/Pnp4/Frontier/CompressionMagnification.lean`
- `sed -n '1,240p' pnp4/Pnp4/Frontier/PvsNPBridgeRequirements.lean`
- `sed -n '1,240p' outputs/circuitphp-search-lb-D0-audit-2026-05-22.md`
- `./scripts/check.sh`

## Scope violations:
None. Markdown-only change. No Lean/JSONL/source-theorem/gap endpoint edits.
