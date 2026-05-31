# SearchMCSP weak solver route D0 audit

## 1) Executive verdict

**YELLOW_NEEDS_TARGET_REPAIR**

Reason: the pnp4 SearchMCSP route surface is mathematically meaningful and non-refuted, and `SearchMCSPConcreteTargets.lean` provides a concrete tree-MCSP target shape; however, the current magnification step is still a contract field (`noBoundedSolver → VerifiedNPDAGLowerBoundSource`) rather than a discharged theorem pipeline tied to an explicit extracted NP language and proven `¬ PpolyDAG` transfer.

---

## 2) Existing pnp4 route surface

Classification of key objects:

1. `SearchMCSPCompressionProblem`
   - **Type:** definition.
   - **Role:** declares instance/witness bit-length schedules, promise, relation, and totality-on-promise.
   - **Status:** foundational interface, not itself a lower bound.

2. `BoundedSearchSolver`
   - **Type:** definition.
   - **Role:** nonuniform solver schema (one circuit per witness bit) + per-bit size bound + solves promise relation.
   - **Status:** formal solver object, not a theorem.

3. `SearchProblemNoBoundedSolver`
   - **Type:** definition (proposition).
   - **Role:** exact weak-LB proposition `¬ Nonempty (BoundedSearchSolver ...)`.
   - **Status:** theorem obligation target, not proved generically.

4. `SearchMCSPWeakCircuitLowerBoundTarget`
   - **Type:** definition/record.
   - **Role:** bundles concrete problem + circuit class + size schedule.
   - **Status:** concrete-target container; depends on instantiated fields.

5. `SearchMCSPWeakCircuitLowerBound`
   - **Type:** theorem obligation wrapper.
   - **Role:** package requiring one field `noBoundedSolver` for a target.
   - **Status:** wrapper around the weak lower-bound theorem.

6. `SearchMCSPMagnificationContract`
   - **Type:** theorem obligation wrapper.
   - **Role:** package requiring magnification map
     `target.noBoundedSolver → VerifiedNPDAGLowerBoundSource`.
   - **Status:** wrapper/contract; no generic proof in this file.

7. `VerifiedNPDAGLowerBoundSource`
   - **Type:** theorem endpoint object (imported from pnp4 bridge stack).
   - **Role:** accepted mainline source feeding the final bridge.
   - **Status:** endpoint requirement, not produced automatically by SearchMCSP definitions.

Net reading: route surface is honest and explicit, but two critical obligations are externalized as package fields (`weak` + `magnification`).

---

## 3) Candidate concrete target

Chosen candidate from `SearchMCSPConcreteTargets.lean`:

**Tree-MCSP search target** via
`treeMCSPSearchWeakLowerBoundTarget threshold encoding C sizeBound`.

Requested target details:

- **problem:** `treeMCSPSearchProblem threshold encoding`.
- **promise:** truth table `tt` has a tree circuit of size `≤ threshold n` (`treeMCSPPredicate n (threshold n) tt`).
- **relation:** witness `w` verifies/encodes a valid small tree circuit computing `tt` (through `TreeMCSPSearchWitnessEncoding.verifies`, optionally codec-induced).
- **instanceBits:** `Partial.tableLen n` (truth-table length for `n` variables).
- **witnessBits:** provided by `encoding.witnessBits n`.
- **circuitClass:** parameter `C` (can instantiate with `ContractExpansion.C_DAG` adapter if desired).
- **sizeBound:** parameter schedule `sizeBound n`.
- **threshold schedule:** parameter `threshold n`.
- **target language if magnified:** not concretely named in `SearchMCSPConcreteTargets.lean`; magnification obligation only requires producing some `VerifiedNPDAGLowerBoundSource` from `noBoundedSolver`.

Assessment: this is a real non-wrapper candidate object, but still partly parametric because witness encoding and size schedules are not canonically fixed in-file.

---

## 4) NoBoundedSolver sanity check

Attempted pre-mortem against the target weak lower bound:

- **Trivial solver?**
  - Not obvious. Producing a valid small tree-circuit witness for every YES instance seems nontrivial.
- **Nonuniform lookup solver?**
  - Per-length table lookup over all truth tables is exponentially large in input length; incompatible with polynomial `sizeBound` if bound is honest.
- **Truth-table hardwiring solve?**
  - For arbitrary promised inputs, hardwiring all answers appears too large unless `sizeBound` is effectively huge or promise is degenerate.
- **Witness-length triviality?**
  - If `witnessBits n` is very large and encoding permissive, per-bit output circuits can still be expensive; not instantly trivial.
- **SizeBound too large?**
  - Yes, if instantiated too permissively, could collapse into existence of easy hardwiring-style solvers.
- **SizeBound too small?**
  - If set to highly restricted classes, theorem may become restricted-model only and miss intended `PpolyDAG` strength.

**Verdict:** `unclear`.

Reason: no immediate trivial solver seen, but the answer is highly sensitive to concrete `threshold/encoding/C/sizeBound` instantiation.

---

## 5) Magnification contract sanity check

Analyzing
`SearchMCSPMagnificationContract target : target.noBoundedSolver → VerifiedNPDAGLowerBoundSource`.

- **Currently field/wrapper?** yes; contract is a structure field requiring a function.
- **Exact language `L` produced?** not explicitly fixed in this frontier layer.
- **`L ∈ NP` formalized?** generic NP formalization exists in contract-expansion components (prefix-extension stack), but no explicit theorem in the concrete-target file tying this particular tree-MCSP target to one named extracted `L` and full bridge.
- **Is `¬ PpolyDAG L` proved from `noBoundedSolver` + extraction?** not as a discharged theorem in this surface.
- **Reuse PrefixExtensionLanguage?** infrastructure exists and appears designed for this style of reduction, but explicit glued theorem for this concrete target is not landed here.
- **Exact missing theorem:** a concrete end-to-end magnification theorem for a fixed target instantiation that maps `noBoundedSolver` to a specific verified NP-vs-PpolyDAG source without assumption packaging.

Conclusion: contract is meaningful but not yet discharged; this is the key repair gap.

---

## 6) Wrapper audit

RED conditions check:

- assuming `VerifiedNPDAGLowerBoundSource`: **risk** (present as required codomain in contract field; not assumed globally, but currently externalized).
- assuming `ResearchGapWitness`: **not applicable** in this frontier route layer.
- adding field `noBoundedSolver → VerifiedNPDAGLowerBoundSource` without proof: **addressed as explicit contract**, but still a **wrapper risk** until discharged for concrete target.
- hiding `¬ PpolyDAG` in promise/certificate: **not observed** in current definitions; the weak proposition is explicit.
- reusing refuted provider/support route: **not observed directly** in these pnp4 files.

Wrapper audit result: **not RED_ROUTE_IS_WRAPPER overall**, but **repair-needed YELLOW** due to undischarged magnification field.

---

## 7) Hardwiring / NoGo cross-check

Cross-check statuses:

- FormulaCertificateProviderPartial refutation: **addressed** (this route does not depend on that refuted provider chain).
- support-bounds refutations: **addressed/risk-aware** (route sits in different frontier, but hardwiring hazards remain design risk).
- V2 filter no-gos: **not applicable** directly (different candidate family), but demonstrates broader hardwiring fragility.
- iso-strong route closure: **addressed** as cautionary precedent; current route must avoid analogous quantifier/hardwiring loopholes.
- per-slice hardwiring: **risk** (must constrain target/size schedule so weak LB cannot be bypassed by slice-wise hardwiring tricks).
- universal witness hazard: **risk** (avoid definitions that allow arbitrary witness families to trivialize claims).
- CircuitPHP D1 result: **addressed** (explicitly treated as side-track warning that unrestricted noBoundedSolver may be main-gap hard).

Overall cross-check: **risk**, not fatal yet.

---

## 8) Literature sanity

Brief sanity read:

- Target is aligned with SearchMCSP/hardness-magnification framing and with known “search-to-decision / prefix-extension” methodology.
- It is conceptually closer to existing magnification narratives than CircuitPHP PPP-style detour.
- Still, proving unrestricted nonuniform weak lower bounds remains delicate; careful theorem scoping is required before claiming tractability.

Deep literature dive is not strictly required for this D0 routing decision.

---

## 9) Recommended next Lean task

Because verdict is **YELLOW**, recommend exactly one L0 task:

**D. formalize exact magnification contract statement without hiding proof**

Concretely: for one fixed tree-MCSP target instantiation (fixed `threshold`, concrete witness codec/encoding, `C_DAG`, explicit `sizeBound` schedule), add a theorem statement that names the extracted NP language and explicitly states the chain from `target.noBoundedSolver` to `VerifiedNPDAGLowerBoundSource`, with no placeholder assumptions beyond the theorem hypothesis itself.

(No proof required at this L0 step.)

---

## 10) Final recommendation

**repair_target_surface**

Rationale: there is a plausible concrete target object worth pursuing, but the route should first be repaired from contract-wrapper shape into an explicit target-specific theorem statement surface before investing in lower-bound attempts.
