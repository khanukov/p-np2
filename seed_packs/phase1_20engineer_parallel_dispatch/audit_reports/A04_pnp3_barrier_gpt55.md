# A04 audit report: `pnp3/Barrier/`

Task: A04  
Engineer handle: gpt55  
Branch: `khanukov/phase1-A04-gpt55`  
Audit scope classification: Infrastructure / governance audit. This audit is markdown-only and makes no Lean/source changes.

## 1. Executive verdict

**Verdict: PARTIAL_BUT_USEFUL.**

The four `pnp3/Barrier/` files are small, kernel-checked interfaces plus wrappers, not concrete mathematical barrier-bypass certificates. `NaturalProofs.lean`, `Relativization.lean`, and `Algebrization.lean` each provide a minimal abstract predicate/witness shape and one elementary theorem converting a witness into non-barrier/non-invariance; these are complete for a minimal interface layer. `Bypass.lean` is less canonical because it packages barrier obligations as arbitrary `Prop` fields and includes wrappers around final pipeline theorems, including one formula-track wrapper whose separation component comes from a `RefutedRoute_*` theorem. No construction of `NaturalProofBypassWitness`, `RelativizationBypassWitness`, or `AlgebrizationBypassWitness` was found in active Lean files. Future pnp4 barrier work should extend beside these interfaces rather than modify the pnp3 trust-root barrier files.

## 2. Executive summary

### Trust-root / frozen boundary

The task file treats the four files under `pnp3/Barrier/` as the barrier-interface area, and the repository instructions list `pnp3/Barrier/**` among read-only trust-root files. I therefore treated these files as **trust-root-frozen for this audit**: safe to read and cite, not safe to edit in Phase 0 or ordinary Phase 1 implementation work.

### Interface versus concrete witnesses

The current pnp3 boundary is:

- **Frozen/minimal interface layer in pnp3:** abstract predicates such as `Relativizing`, `Algebrizing`, `SatisfiesNaturalProofBarrier`, and witness structures such as `NaturalProofBypassWitness`, `RelativizationBypassWitness`, and `AlgebrizationBypassWitness`.
- **Concrete/extensible layer expected outside pnp3 barrier files:** pnp4-side or candidate-local structures that define real oracle worlds, algebraic oracle worlds, natural-proof constructivity/largeness/usefulness notions, and bridge the concrete data into these pnp3 witness structures.
- **Audit-only wrapper layer in `Bypass.lean`:** final-theorem wrappers that require `BarrierBypassPackage` as an explicit assumption, but do not prove natural-proof/relativization/algebrization bypasses.

The safe pnp4 extension pattern is to import these pnp3 interfaces read-only and add new pnp4 structures/theorems that instantiate them only when there is genuine mathematical data. It would be unsafe to weaken pnp3 interfaces or populate `BarrierBypassAssumptions` with arbitrary placeholders and then report that as barrier progress.

## 3. Files audited

| File | Approximate role | Read mode | Reason if not fully read |
| --- | --- | --- | --- |
| `RESEARCH_CONSTITUTION.md` | repository governance and target-lock rules | skimmed structurally, relevant rules read | large governance document; I focused on trust-root, barrier, refuted-route, and Rule 16 constraints |
| `seed_packs/phase1_20engineer_parallel_dispatch/README.md` | phase dispatch overview | skimmed structurally | task prompt gave audit-specific override; README is broad dispatch context |
| `seed_packs/phase1_20engineer_parallel_dispatch/COMMON_WORKER_INSTRUCTIONS.md` | shared worker instructions | skimmed structurally, conflict rules noted | older E-number naming was superseded by the prompt override |
| `seed_packs/phase1_20engineer_parallel_dispatch/tasks/A04_audit_pnp3_barrier.md` | exact A04 task | read fully | primary task specification |
| `pnp3/Barrier/NaturalProofs.lean` | natural-proofs abstract triad and bypass witness | read fully | small required file |
| `pnp3/Barrier/Relativization.lean` | oracle-parametric relativization interface | read fully | small required file |
| `pnp3/Barrier/Algebrization.lean` | abstract algebrization interface | read fully | small required file |
| `pnp3/Barrier/Bypass.lean` | explicit barrier-obligation wrappers around final statements | read fully | small required file |
| `pnp3/Tests/BarrierAudit.lean` | compile-time audit for locality route, not RR/AW certificates | read fully | task requested cross-reference if present |
| `pnp3/Tests/BarrierBypassAudit.lean` | `#print axioms` surface for `Bypass.lean` wrappers | read fully | found by symbol search and directly relevant |
| `pnp3/Magnification/UnconditionalResearchGap.lean` | trust-root final target context | skimmed structurally | optional/recommended; not part of A04 direct scope |
| `pnp3/Complexity/Interfaces.lean` | trust-root complexity interface definitions | skimmed structurally | optional/recommended; file is large, only needed for imported target names |
| `outputs/nogolog.jsonl` | NoGoLog ledger | searched/validated by `./scripts/check.sh`; not manually read line-by-line | optional/recommended but not needed for the four barrier interfaces |
| `seed_packs/first_move_search_2026/reports/fp3b_epoch_strategic_retrospective_claudeopus.md` | historical strategic context | not read | optional and not necessary to answer A04 after direct Lean audit/searches |

## 4. File-by-file declaration inventory

### `pnp3/Barrier/NaturalProofs.lean`

1. `structure NaturalProofConditions (L : Language) : Type`
   - Fields:
     - `constructive : Prop`
     - `large : Prop`
     - `usefulAgainstPpoly : Prop`
   - Role: abstract Razborov--Rudich triad for a target language.
   - Classification: **staged Prop / harmless interface**.
   - Hard-payload dependency: none directly; it imports `Complexity.Interfaces` only for `Language`.

2. `def SatisfiesNaturalProofBarrier (L : Language) : Prop`
   - Signature summary: `∃ P : NaturalProofConditions L, P.constructive ∧ P.large ∧ P.usefulAgainstPpoly`.
   - Role: packages the triad as a barrier-satisfaction predicate.
   - Classification: **staged Prop / harmless interface**.
   - Hard-payload dependency: none directly.

3. `def AvoidsNaturalProofBarrier (L : Language) : Prop`
   - Signature summary: `¬ SatisfiesNaturalProofBarrier L`.
   - Role: negated barrier predicate.
   - Classification: **staged Prop / harmless interface**.
   - Hard-payload dependency: none directly.

4. `structure NaturalProofBypassWitness (L : Language) : Prop`
   - Field: `blocks : ∀ P : NaturalProofConditions L, P.constructive → P.large → P.usefulAgainstPpoly → False`.
   - Role: explicit package for proving no natural-proof triad can hold for `L`.
   - Classification: **conditional / staged Prop**.
   - Hard-payload dependency: none directly. It is hard only when a future worker tries to construct it for an interesting `L`.

5. `theorem avoidsNaturalProofBarrier_of_witness {L : Language} (hBypass : NaturalProofBypassWitness L) : AvoidsNaturalProofBarrier L`
   - Role: destructs the existential triad and applies `hBypass.blocks`.
   - Classification: **canonical interface theorem**.
   - Hard-payload dependency: depends on an explicit `NaturalProofBypassWitness L`, not on `ResearchGapWitness`, `NP_not_subset_PpolyDAG`, `VerifiedNPDAGLowerBoundSource`, or `SearchMCSPMagnificationContract`.

### `pnp3/Barrier/Relativization.lean`

1. `def Relativizing (S : Type u → Prop) : Prop`
   - Signature summary: `∀ O₁ O₂ : Type u, S O₁ ↔ S O₂`.
   - Role: abstract oracle-invariance predicate.
   - Classification: **staged Prop / harmless interface**.
   - Hard-payload dependency: none.

2. `structure RelativizationBypassWitness (S : Type u → Prop) : Type (u + 1)`
   - Fields: `O₁ : Type u`, `O₂ : Type u`, `holds₁ : S O₁`, `fails₂ : ¬ S O₂`.
   - Role: two-world witness for non-relativization.
   - Classification: **conditional interface**.
   - Hard-payload dependency: none directly. Any hard content must enter through the chosen statement scheme `S` and proofs of `holds₁`/`fails₂`.

3. `theorem not_relativizing_of_bypass {S : Type u → Prop} (hBypass : RelativizationBypassWitness S) : ¬ Relativizing S`
   - Role: applies oracle-invariance at `O₁`, `O₂`, transports `holds₁`, and contradicts `fails₂`.
   - Classification: **canonical interface theorem**.
   - Hard-payload dependency: explicit `RelativizationBypassWitness S` only; no `ResearchGapWitness`, `NP_not_subset_PpolyDAG`, `VerifiedNPDAGLowerBoundSource`, or `SearchMCSPMagnificationContract`.

### `pnp3/Barrier/Algebrization.lean`

1. `def Algebrizing (S : Type u → Prop) : Prop`
   - Signature summary: `∀ A₁ A₂ : Type u, S A₁ ↔ S A₂`.
   - Role: abstract algebraic-oracle invariance predicate.
   - Classification: **staged Prop / harmless interface**.
   - Hard-payload dependency: none.

2. `structure AlgebrizationBypassWitness (S : Type u → Prop) : Type (u + 1)`
   - Fields: `A₁ : Type u`, `A₂ : Type u`, `holds₁ : S A₁`, `fails₂ : ¬ S A₂`.
   - Role: two-world witness for non-algebrization.
   - Classification: **conditional interface**.
   - Hard-payload dependency: none directly. Any hard content enters through `S`, `holds₁`, and `fails₂`.

3. `theorem not_algebrizing_of_bypass {S : Type u → Prop} (hBypass : AlgebrizationBypassWitness S) : ¬ Algebrizing S`
   - Role: same shape as the relativization theorem, but for algebraic-oracle worlds.
   - Classification: **canonical interface theorem**.
   - Hard-payload dependency: explicit `AlgebrizationBypassWitness S` only; no `ResearchGapWitness`, `NP_not_subset_PpolyDAG`, `VerifiedNPDAGLowerBoundSource`, or `SearchMCSPMagnificationContract`.

### `pnp3/Barrier/Bypass.lean`

1. `structure BarrierBypassAssumptions : Type`
   - Fields: `relativization : Prop`, `naturalProofs : Prop`, `algebrization : Prop`.
   - Role: untyped-by-barrier-name bundle of explicit obligations.
   - Classification: **staged Prop / potential wrapper risk**.
   - Hard-payload dependency: none directly, but the fields are arbitrary `Prop`s and are not tied to the three witness structures above.

2. `def BarrierBypassPackage : Prop := Nonempty BarrierBypassAssumptions`
   - Role: proposition-level wrapper required by final signatures.
   - Classification: **staged Prop / potential wrapper risk**.
   - Hard-payload dependency: none directly. It can be inhabited by any three `Prop` fields if those fields are themselves inhabited or simply chosen as easy propositions.

3. `theorem NP_not_subset_PpolyFormula_with_barriers (hFormula : NP_not_subset_PpolyFormula) (hBarriers : BarrierBypassPackage) : NP_not_subset_PpolyFormula ∧ BarrierBypassPackage`
   - Role: pairs an already-provided formula-track separation with an already-provided barrier package.
   - Classification: **conditional wrapper**.
   - Hard-payload dependency: explicit `NP_not_subset_PpolyFormula` and `BarrierBypassPackage` hypotheses.

4. `theorem NP_not_subset_PpolyFormula_final_with_barriers (hMag : MagnificationAssumptions) (n : Nat) (hn : hMag.antiChecker.asymptotic.N0 ≤ n) (hBarriers : BarrierBypassPackage) : NP_not_subset_PpolyFormula ∧ BarrierBypassPackage`
   - Role: pairs `hBarriers` with `RefutedRoute_NP_not_subset_PpolyFormula_final hMag n hn`.
   - Classification: **refuted route / audit-only wrapper**.
   - Hard-payload dependency: `MagnificationAssumptions`, numeric threshold hypothesis, and `BarrierBypassPackage`; separation component is produced by a theorem explicitly named `RefutedRoute_*`.

5. `theorem P_ne_NP_final_with_barriers (hNPDag : NP_not_subset_PpolyDAG) (hPpolyContracts : Complexity.Simulation.PsubsetPpolyCompiledRuntimeLinearOutputContracts) (hBarriers : BarrierBypassPackage) : P_ne_NP ∧ BarrierBypassPackage`
   - Role: pairs `hBarriers` with `P_ne_NP_final_with_provider hNPDag hPpolyContracts`.
   - Classification: **conditional wrapper**.
   - Hard-payload dependency: explicit `NP_not_subset_PpolyDAG`, explicit internal `P ⊆ P/poly` compiler contracts, and `BarrierBypassPackage`. It does not construct `NP_not_subset_PpolyDAG`.

## 5. Top-level theorem / structure inventory

| Declaration | File | Type/signature summary | Classification | Hard-payload dependency |
| --- | --- | --- | --- | --- |
| `NaturalProofConditions` | `pnp3/Barrier/NaturalProofs.lean` | triad of `constructive`, `large`, `usefulAgainstPpoly` props | staged Prop / harmless interface | none directly |
| `SatisfiesNaturalProofBarrier` | `pnp3/Barrier/NaturalProofs.lean` | existential triad predicate | staged Prop | none directly |
| `AvoidsNaturalProofBarrier` | `pnp3/Barrier/NaturalProofs.lean` | negation of `SatisfiesNaturalProofBarrier` | staged Prop | none directly |
| `NaturalProofBypassWitness` | `pnp3/Barrier/NaturalProofs.lean` | proof that no triad can simultaneously hold | conditional / staged Prop | explicit witness obligation only |
| `avoidsNaturalProofBarrier_of_witness` | `pnp3/Barrier/NaturalProofs.lean` | witness implies `AvoidsNaturalProofBarrier L` | canonical interface theorem | depends on `NaturalProofBypassWitness L` |
| `Relativizing` | `pnp3/Barrier/Relativization.lean` | all oracle types have equivalent `S` truth | staged Prop / interface | none |
| `RelativizationBypassWitness` | `pnp3/Barrier/Relativization.lean` | two oracle worlds, one satisfying and one refuting `S` | conditional interface | explicit witness only |
| `not_relativizing_of_bypass` | `pnp3/Barrier/Relativization.lean` | witness implies `¬ Relativizing S` | canonical interface theorem | depends on `RelativizationBypassWitness S` |
| `Algebrizing` | `pnp3/Barrier/Algebrization.lean` | all algebraic-oracle types have equivalent `S` truth | staged Prop / interface | none |
| `AlgebrizationBypassWitness` | `pnp3/Barrier/Algebrization.lean` | two algebraic-oracle worlds, one satisfying and one refuting `S` | conditional interface | explicit witness only |
| `not_algebrizing_of_bypass` | `pnp3/Barrier/Algebrization.lean` | witness implies `¬ Algebrizing S` | canonical interface theorem | depends on `AlgebrizationBypassWitness S` |
| `BarrierBypassAssumptions` | `pnp3/Barrier/Bypass.lean` | arbitrary `Prop` fields for three barrier labels | staged Prop / potential wrapper risk | none directly |
| `BarrierBypassPackage` | `pnp3/Barrier/Bypass.lean` | `Nonempty BarrierBypassAssumptions` | staged Prop / potential wrapper risk | none directly |
| `NP_not_subset_PpolyFormula_with_barriers` | `pnp3/Barrier/Bypass.lean` | `NP_not_subset_PpolyFormula → BarrierBypassPackage → NP_not_subset_PpolyFormula ∧ BarrierBypassPackage` | conditional wrapper | explicit formula separation |
| `NP_not_subset_PpolyFormula_final_with_barriers` | `pnp3/Barrier/Bypass.lean` | `MagnificationAssumptions → n → threshold → BarrierBypassPackage → NP_not_subset_PpolyFormula ∧ BarrierBypassPackage` | refuted route / audit-only | `MagnificationAssumptions`, `RefutedRoute_*`, `BarrierBypassPackage` |
| `P_ne_NP_final_with_barriers` | `pnp3/Barrier/Bypass.lean` | `NP_not_subset_PpolyDAG → compiler contracts → BarrierBypassPackage → P_ne_NP ∧ BarrierBypassPackage` | conditional wrapper | explicit `NP_not_subset_PpolyDAG`, compiler contracts, package |

No top-level declaration in the four files mentions `ResearchGapWitness`, `VerifiedNPDAGLowerBoundSource`, or `SearchMCSPMagnificationContract`. Only `Bypass.lean` mentions `NP_not_subset_PpolyDAG`, and only as a hypothesis of `P_ne_NP_final_with_barriers`.

## 6. Existing inhabitations

I searched active Lean files for references and direct constructions of:

- `NaturalProofBypassWitness`
- `RelativizationBypassWitness`
- `AlgebrizationBypassWitness`
- `BarrierBypassAssumptions`
- `BarrierBypassPackage`

Findings:

1. **No construction of `NaturalProofBypassWitness` was found in active Lean files.** The only active Lean occurrence is its own structure declaration and theorem hypothesis in `NaturalProofs.lean`.
2. **No construction of `RelativizationBypassWitness` was found in active Lean files.** The only active Lean occurrence is its own structure declaration and theorem hypothesis in `Relativization.lean`.
3. **No construction of `AlgebrizationBypassWitness` was found in active Lean files.** The only active Lean occurrence is its own structure declaration and theorem hypothesis in `Algebrization.lean`.
4. **No direct construction of `BarrierBypassAssumptions` was found in active Lean files.** Active uses of `BarrierBypassPackage` are hypotheses in `Bypass.lean` wrappers and `#print axioms` targets in `pnp3/Tests/BarrierBypassAudit.lean`.
5. Historical docs and seed-pack reports mention these names, but those are not Lean inhabitations.

Conclusion: the repository has abstract barrier witness types, but no current concrete RR/relativization/algebrization bypass certificates.

## 7. Kernel-checked content

The following is actually kernel-checked in the audited barrier area:

1. `avoidsNaturalProofBarrier_of_witness` proves that if `hBypass : NaturalProofBypassWitness L`, then `AvoidsNaturalProofBarrier L`. The proof unfolds the existential triad behind `SatisfiesNaturalProofBarrier`, extracts `P`, `constructive`, `large`, and `usefulAgainstPpoly`, and applies `hBypass.blocks`.
2. `not_relativizing_of_bypass` proves that if a scheme has `RelativizationBypassWitness S`, then it is not `Relativizing`. The proof instantiates the alleged relativizing equivalence at `hBypass.O₁` and `hBypass.O₂`, transports `hBypass.holds₁`, and contradicts `hBypass.fails₂`.
3. `not_algebrizing_of_bypass` proves the analogous statement for `AlgebrizationBypassWitness S` and `Algebrizing S`.
4. `NP_not_subset_PpolyFormula_with_barriers` proves only conjunction introduction from two explicit hypotheses: a formula-track separation and a barrier package.
5. `NP_not_subset_PpolyFormula_final_with_barriers` proves a conjunction whose first component is obtained from `RefutedRoute_NP_not_subset_PpolyFormula_final hMag n hn`; this is kernel-checked but audit-only/refuted-route content, not mathematical progress.
6. `P_ne_NP_final_with_barriers` proves a conjunction whose first component is `P_ne_NP_final_with_provider hNPDag hPpolyContracts`; it requires the hard DAG separation as an explicit hypothesis.
7. `pnp3/Tests/BarrierAudit.lean` kernel-checks two locality contradiction audit theorems, but the file explicitly says it does **not** claim formalized bypass certificates for natural proofs, relativization, or algebrization.
8. `pnp3/Tests/BarrierBypassAudit.lean` kernel-checks `#print axioms` commands for the three `Bypass.lean` wrappers.

`./scripts/check.sh` completed successfully and specifically built `Barrier.Relativization`, `Barrier.Algebrization`, `Barrier.NaturalProofs`, `Barrier.Bypass`, `Tests.BarrierAudit`, and `Tests.BarrierBypassAudit` during its full Lean build.

## 8. Staged / placeholder / Prop-only content

| Declaration | Staging assessment | Risk interpretation |
| --- | --- | --- |
| `NaturalProofConditions` fields | honest staging | Harmless interface as long as future work does not claim the fields have concrete RR semantics without definitions/theorems. |
| `SatisfiesNaturalProofBarrier` | honest staging | It is just existential packaging of the triad. |
| `AvoidsNaturalProofBarrier` | honest staging | Negated interface predicate; meaningful only when `SatisfiesNaturalProofBarrier` is concretely instantiated. |
| `NaturalProofBypassWitness` | honest staging, possible hard theorem if instantiated | Constructing it for a meaningful `L` may be mathematically hard; the structure itself is safe. |
| `Relativizing` | honest staging | Abstract invariance over arbitrary `Type u`; no concrete oracle model. |
| `RelativizationBypassWitness` | honest staging, possible hard theorem if instantiated | Requires concrete two-world data for a meaningful `S`; currently uninhabited in active Lean. |
| `Algebrizing` | honest staging | Abstract invariance over arbitrary `Type u`; no concrete algebraic oracle model. |
| `AlgebrizationBypassWitness` | honest staging, possible hard theorem if instantiated | Requires concrete two-world data for a meaningful `S`; currently uninhabited in active Lean. |
| `BarrierBypassAssumptions` | potential wrapper risk | Three fields are arbitrary `Prop`, not linked to `NaturalProofBypassWitness`, `RelativizationBypassWitness`, or `AlgebrizationBypassWitness`. |
| `BarrierBypassPackage` | potential wrapper risk | `Nonempty BarrierBypassAssumptions` alone does not guarantee real barrier bypasses. |

No declaration in the audited barrier files is a hidden hard theorem by itself. The only significant wrapper risk is terminological: `BarrierBypassPackage` sounds like a certificate bundle but is only nonemptiness of arbitrary `Prop` fields.

## 9. Refuted / vacuous / legacy route check

Search terms required by the prompt were checked over `pnp3/Barrier` and the two directly relevant barrier test files.

Findings:

1. `pnp3/Barrier/Bypass.lean` imports `Magnification.FinalResult`, takes `MagnificationAssumptions` in `NP_not_subset_PpolyFormula_final_with_barriers`, and uses `RefutedRoute_NP_not_subset_PpolyFormula_final` to produce the formula-track separation component.
2. `pnp3/Tests/BarrierAudit.lean` imports `Magnification.Facts_Magnification_Partial` and `LowerBounds.AntiChecker_Partial`, and prints axioms for `RefutedRoute_NP_not_subset_PpolyFormula_final` and `P_ne_NP_final`.
3. No occurrences of `Vacuous`, `supportBounds`, `FinalPayloadProvider`, `via_ex_falso`, `weakRoute`, `_Legacy`, `TODO`, or `placeholder` were found in the four barrier files or directly relevant barrier tests.
4. `_Partial` occurs only in `pnp3/Tests/BarrierAudit.lean` imports/name surfaces for the locality partial-MCSP route, not in the four barrier interface files.

Isolation assessment: the refuted-route use is isolated to the formula-track wrapper `NP_not_subset_PpolyFormula_final_with_barriers` and to audit print surfaces. It must remain classified as audit-only/refuted-route content and should not be used as mainline `P != NP` progress.

## 10. Hidden payload / Rule 16 check

I searched the audit scope for:

- `class`
- `instance`
- `default_instance`
- `attribute [instance]`
- `Fact`
- `opaque`
- `Classical.choose`
- `noncomputable def`

Result over `pnp3/Barrier` plus `pnp3/Tests/BarrierAudit.lean` and `pnp3/Tests/BarrierBypassAudit.lean`: **no matches**.

Interpretation:

- There is no typeclass-based payload channel in the audited files.
- There are no default instances, opaque definitions, `Fact` wrappers, or `Classical.choose`-based hidden witnesses in the audited files.
- `BarrierBypassPackage` remains a wrapper risk, but not a Rule 16 hidden-payload pattern: its payload is explicit as a theorem hypothesis, not smuggled through instance search.

Classification: **harmless with respect to Rule 16; wrapper-risk only for naming/governance.**

## 11. Barrier relevance

| Barrier / concern | Audited area content | Classification |
| --- | --- | --- |
| Natural proofs | `NaturalProofConditions`, `SatisfiesNaturalProofBarrier`, `AvoidsNaturalProofBarrier`, `NaturalProofBypassWitness`, theorem from witness to avoidance | typed interface + staged Prop + elementary theorem |
| Relativization | `Relativizing`, `RelativizationBypassWitness`, theorem from witness to non-relativizing | typed interface + elementary theorem |
| Algebrization | `Algebrizing`, `AlgebrizationBypassWitness`, theorem from witness to non-algebrizing | typed interface + elementary theorem |
| Locality | `pnp3/Tests/BarrierAudit.lean` contains locality contradiction audit theorems via `StructuredLocalityProviderPartial`; four `pnp3/Barrier/*.lean` files do not define locality barrier interfaces | actual audit theorem in tests; not RR/AW certificate |
| Hardwiring | no direct pnp3 barrier-file content | nothing in the four files |
| Support-cardinality-only | no direct pnp3 barrier-file content | nothing in the four files |
| Syntax-only filters | no direct pnp3 barrier-file content | nothing in the four files |
| Normalization filters | no direct pnp3 barrier-file content | nothing in the four files |
| Search-to-decision | no direct pnp3 barrier-file content | nothing in the four files |
| MCSP / magnification | `Bypass.lean` imports final magnification result; `BarrierAudit.lean` uses partial MCSP locality/magnification audit surfaces | conditional/audit wrapper; no MCSP barrier bypass theorem |

## 12. Gaps for pnp4 extensions

### Natural proofs gap

Missing concrete content:

- A concrete pnp4-side notion of constructivity for the specific property/proof family under review.
- A concrete pnp4-side notion of largeness/density, with parameters and finite-length/asymptotic interpretation.
- A concrete pnp4-side notion of usefulness against the relevant circuit class, especially `PpolyDAG` if the route is claimed as mainline.
- A theorem connecting those concrete notions to `Pnp3.Barrier.NaturalProofConditions L`.
- A real `NaturalProofBypassWitness L`, or a narrower theorem showing which one of constructivity/largeness/usefulness necessarily fails for the route.

Possible pnp4-side augmentations without modifying pnp3:

- `Pnp4.Barrier.NaturalProofsConcrete` defining parameterized pnp4 RR conditions and adapters into `Pnp3.Barrier.NaturalProofConditions`.
- Route-local modules proving “not large”, “not constructive”, or “not useful” for a specific route, then packaging those into `NaturalProofBypassWitness` only when justified.

### Relativization gap

Missing concrete content:

- A concrete oracle model or at least a pnp4-level oracle-world record with semantics for the statement under audit.
- A statement scheme `S : Type u → Prop` that faithfully represents the lower-bound/proof claim in each oracle world.
- Two worlds `O₁`, `O₂` plus proofs `S O₁` and `¬ S O₂`.
- An adapter from route-specific oracle semantics to the minimal `RelativizationBypassWitness S`.

Possible pnp4-side augmentations without modifying pnp3:

- `Pnp4.Barrier.RelativizationConcrete` defining oracle-world descriptors and route statement schemes.
- A B02 task that proves only typed adapters and does not assert lower-bound truth unless the two-world theorems are actually available.

### Algebrization gap

Missing concrete content:

- A concrete algebraic-oracle model or abstraction stronger than plain `Type u`.
- A route-specific statement scheme over algebraic oracle worlds.
- Two algebraic oracle worlds `A₁`, `A₂` plus proofs of truth/failure for the scheme.
- Adapter into `AlgebrizationBypassWitness S`.

Possible pnp4-side augmentations without modifying pnp3:

- `Pnp4.Barrier.AlgebrizationConcrete` defining algebraic-oracle descriptors and statement schemes.
- A B03 task that carefully keeps “interface prepared” separate from “AW barrier bypass proved”.

### Barrier package gap

Missing concrete content:

- A typed connection from `BarrierBypassAssumptions.relativization` to `RelativizationBypassWitness`.
- A typed connection from `BarrierBypassAssumptions.naturalProofs` to `NaturalProofBypassWitness`.
- A typed connection from `BarrierBypassAssumptions.algebrization` to `AlgebrizationBypassWitness`.

Possible pnp4-side augmentation without modifying pnp3:

- A new pnp4 “strict barrier package” with fields that are actual witness types, plus a theorem that it implies `BarrierBypassPackage`. This should be pnp4-side only because pnp3 barrier files are frozen.

## 13. Cross-reference with `pnp3/Tests/BarrierAudit.lean`

`pnp3/Tests/BarrierAudit.lean` is present and relevant but not a certificate for the three A04 barrier interfaces.

It states in its module comment that it makes the locality route explicit and does not claim formalized bypass certificates for natural proofs, relativization, or algebrization. Its two theorems are:

1. `locality_contradiction_from_provider_witness`
   - Inputs: `StructuredLocalityProviderPartial`, `FormulaLowerBoundHypothesisPartial p δ`, and `PpolyFormula (gapPartialMCSP_Language p)`.
   - Output: `False`.
   - Proof shape: obtains a local solver from the provider and contradicts `noSmallLocalCircuitSolver_partial_v2`.

2. `locality_contra_np_to_formula`
   - Inputs: `StructuredLocalityProviderPartial`, `NP_strict (gapPartialMCSP_Language p)`, and `FormulaLowerBoundHypothesisPartial p δ`.
   - Output: `((∀ L : Language, NP_strict L → PpolyFormula L) → False)`.
   - Proof shape: converts the assumed universal NP-to-formula collapse into a formula witness for the partial MCSP language, then invokes `locality_contradiction_from_provider_witness`.

The audit file also prints axiom surfaces for these locality theorems, the OPS trigger, the refuted formula final, and `P_ne_NP_final`. During `./scripts/check.sh`, these printed axiom surfaces depended only on standard Lean/mathlib axioms (`propext`, `Classical.choice`, `Quot.sound`) according to the build output.

`pnp3/Tests/BarrierBypassAudit.lean` is also present and prints axiom surfaces for the three `Bypass.lean` wrapper theorems. It does not instantiate `BarrierBypassPackage` or any concrete bypass witness.

## 14. Reuse map

### Safe to reuse

- `Pnp3.Barrier.NaturalProofConditions` as the minimal target for route-specific natural-proof triad adapters.
- `Pnp3.Barrier.SatisfiesNaturalProofBarrier` and `Pnp3.Barrier.AvoidsNaturalProofBarrier` as abstract predicates only.
- `Pnp3.Barrier.NaturalProofBypassWitness` and `avoidsNaturalProofBarrier_of_witness` when a future task has an actual proof that the triad cannot hold.
- `Pnp3.Barrier.Relativizing`, `RelativizationBypassWitness`, and `not_relativizing_of_bypass` for future two-oracle-world certificates.
- `Pnp3.Barrier.Algebrizing`, `AlgebrizationBypassWitness`, and `not_algebrizing_of_bypass` for future two-algebraic-world certificates.
- `pnp3/Tests/BarrierAudit.lean` as a locality-route audit surface, not as RR/AW evidence.
- `pnp3/Tests/BarrierBypassAudit.lean` as an axiom-surface audit for wrapper theorems.

### Reuse with caution

- `BarrierBypassAssumptions` / `BarrierBypassPackage`: safe as explicit obligations in theorem signatures, but not safe as evidence that barriers have been bypassed unless paired with stronger typed witnesses.
- `NP_not_subset_PpolyFormula_final_with_barriers`: safe only as audit/refuted-route demonstration; not safe for progress claims.
- `P_ne_NP_final_with_barriers`: safe only as a conditional wrapper requiring explicit `NP_not_subset_PpolyDAG`; it should not be cited as constructing DAG separation.

### Avoid

- Do not modify `pnp3/Barrier/**` for B01/B02/B03 unless the operator explicitly authorizes a foundational/trust-root change.
- Do not fill `BarrierBypassAssumptions` with arbitrary easy propositions and call it a barrier certificate.
- Do not use the refuted formula-track wrapper as mainline progress.
- Do not claim natural-proof/relativization/algebrization bypasses from `pnp3/Tests/BarrierAudit.lean`; it is locality-only.

## 15. Gap map

### A. Engineering gap

- No pnp4-side concrete barrier modules currently adapt route-specific structures into the pnp3 barrier witness types.
- No strict typed barrier package exists that requires actual `NaturalProofBypassWitness`, `RelativizationBypassWitness`, and `AlgebrizationBypassWitness` fields.
- No dedicated pnp4 tests print axiom surfaces for future B01/B02/B03 concrete barrier adapters.

### B. Formalization gap

- The pnp3 interfaces do not define concrete oracle-machine semantics, algebraic-oracle semantics, or RR density/constructivity/usefulness measures.
- There are no formal `NaturalProofBypassWitness`, `RelativizationBypassWitness`, or `AlgebrizationBypassWitness` inhabitants for any meaningful active route.
- `BarrierBypassAssumptions` is not formally linked to the typed witness structures.

### C. Mathematical gap

- Constructing a meaningful `NaturalProofBypassWitness` may require proving that at least one RR condition fails for the proposed lower-bound method/property.
- Constructing a meaningful `RelativizationBypassWitness` requires two oracle worlds separating the route statement.
- Constructing a meaningful `AlgebrizationBypassWitness` requires two algebraic-oracle worlds separating the route statement.
- None of these pnp3 barrier files reduce `VerifiedNPDAGLowerBoundSource`, `SearchMCSPWeakLowerBound`, or `NP_not_subset_PpolyDAG`.

### D. Governance gap

- The name `BarrierBypassPackage` may overstate its strength because it is only `Nonempty BarrierBypassAssumptions` with arbitrary `Prop` fields.
- The formula-track final wrapper in `Bypass.lean` uses a `RefutedRoute_*` theorem and must stay quarantined as audit-only.
- Future tasks should explicitly state whether they are building interface adapters, concrete witness certificates, or only markdown barrier analysis.

## 16. Recommended Phase 1+ tasks

### Task 1: B01 pnp4 natural-proof concrete adapter skeleton

- **Title:** Define pnp4-side concrete natural-proof condition adapters without constructing bypasses.
- **Exact files to touch:** new `pnp4/Pnp4/Barrier/NaturalProofsConcrete.lean`; optional new pnp4 test file if module policy allows; `lakefile.lean` only if required by pnp4 module registration policy.
- **Allowed scope:** define route-parameterized pnp4 structures for constructivity/largeness/usefulness and adapter theorem into `Pnp3.Barrier.NaturalProofConditions`.
- **Forbidden scope:** no edits to `pnp3/Barrier/**`; no `NaturalProofBypassWitness` construction unless a concrete failure proof is included; no `P_ne_NP` or `NP_not_subset_PpolyDAG` claims.
- **Expected output:** typed adapter layer and tests/audit prints, clearly documented as interface only.
- **Estimated time:** 1--2 days.
- **Dependency on other audits:** should review A07/A08 to align with pnp4 route targets.
- **Risk level:** medium, mainly naming/governance risk.
- **Type:** Lean.

### Task 2: B02 pnp4 relativization statement-scheme skeleton

- **Title:** Define pnp4-side oracle-world statement-scheme interface and adapter to `RelativizationBypassWitness`.
- **Exact files to touch:** new `pnp4/Pnp4/Barrier/RelativizationConcrete.lean`; optional pnp4 test/audit file; `lakefile.lean` only if required.
- **Allowed scope:** define concrete oracle-world descriptors and helper theorem converting two-world data into `Pnp3.Barrier.RelativizationBypassWitness`.
- **Forbidden scope:** no claim that any route is nonrelativizing without actual `holds₁` and `fails₂`; no pnp3 barrier edits; no final endpoint changes.
- **Expected output:** route-neutral interface and adapter theorem.
- **Estimated time:** 1--2 days.
- **Dependency on other audits:** should coordinate with A07/A08 and B02 literature/design audit.
- **Risk level:** medium-high if statement scheme is too abstract/vacuous.
- **Type:** Lean plus documentation comments.

### Task 3: B03 pnp4 algebrization statement-scheme skeleton

- **Title:** Define pnp4-side algebraic-oracle statement-scheme interface and adapter to `AlgebrizationBypassWitness`.
- **Exact files to touch:** new `pnp4/Pnp4/Barrier/AlgebrizationConcrete.lean`; optional pnp4 test/audit file; `lakefile.lean` only if required.
- **Allowed scope:** define algebraic-oracle descriptors and helper theorem converting two-world data into `Pnp3.Barrier.AlgebrizationBypassWitness`.
- **Forbidden scope:** no AW bypass claim without real two-world evidence; no pnp3 barrier edits; no final endpoint changes.
- **Expected output:** route-neutral interface and adapter theorem.
- **Estimated time:** 1--2 days.
- **Dependency on other audits:** should coordinate with B03 design/literature audit.
- **Risk level:** high because algebrization semantics can be easy to under-specify.
- **Type:** Lean plus documentation comments.

### Task 4: Operator decision on strict barrier package naming

- **Title:** Decide whether to introduce a strict typed barrier package outside pnp3.
- **Exact files to touch:** operator decision document or new pnp4-side markdown/design file; no Lean required initially.
- **Allowed scope:** decide whether to supplement `BarrierBypassPackage` with a pnp4 package whose fields are actual witness types.
- **Forbidden scope:** no edits to `pnp3/Barrier/Bypass.lean`; no retroactive reinterpretation of current `BarrierBypassPackage`.
- **Expected output:** yes/no decision and naming convention.
- **Estimated time:** half day.
- **Dependency on other audits:** A04 sufficient; A07/A08 useful.
- **Risk level:** low.
- **Type:** operator decision / markdown-only.

## 17. Stop / hold recommendations

- **Hold any task that claims a natural-proof, relativization, or algebrization bypass by merely instantiating `BarrierBypassPackage`.** That package is not tied to the typed witness structures.
- **Downgrade any B01/B02/B03 task from “prove bypass” to “define concrete interface/adapter” unless it includes real failure/two-world theorems.**
- **Cancel or rename any planned task that would edit `pnp3/Barrier/**` during normal Phase 1 work.** These files should be treated as frozen pnp3 interfaces.
- **Do not use `NP_not_subset_PpolyFormula_final_with_barriers` as a progress endpoint.** It uses `RefutedRoute_NP_not_subset_PpolyFormula_final` and is audit-only.
- **No hold on pure pnp4-side adapter skeletons.** Those are useful if accurately labeled as interface infrastructure.

## 18. Honest caveats

- I fully read the four `pnp3/Barrier/*.lean` files and the two directly relevant test files, but did not reconstruct the complete import graph of `Magnification.FinalResult` or `Complexity.Simulation.Circuit_Compiler`.
- I did not inspect every proof body behind `P_ne_NP_final_with_provider`, `RefutedRoute_NP_not_subset_PpolyFormula_final`, `StructuredLocalityProviderPartial`, or `noSmallLocalCircuitSolver_partial_v2`; this audit classifies how `pnp3/Barrier/` uses them.
- I did not manually read every line of `outputs/nogolog.jsonl`; I relied on `./scripts/check.sh` validation and targeted searches for this A04 scope.
- I verified signatures and wrapper structure, not mathematical adequacy of any future RR/AW oracle model.
- I did not audit all historical markdown mentions of barrier names beyond search hits; historical docs are not active Lean inhabitations.
- This audit should be cross-checked with A07/A08 before dispatching pnp4 barrier adapter modules that reference current pnp4 route names.

## 19. Commands run

1. `pwd && find .. -name AGENTS.md -print && git status --short --branch`
   - Purpose: repository location, instruction discovery, and working tree status.
   - Result: found `/workspace/p-np2/AGENTS.md`; initial branch was `work`.

2. `cat AGENTS.md && git rev-parse HEAD && git branch --show-current`
   - Purpose: read repository agent rules and record starting commit/branch.
   - Result: starting commit `d27b069127f63a3f24ab30d1a91c86c84f8b79c7`; branch `work`.

3. `find seed_packs/phase1_20engineer_parallel_dispatch -maxdepth 3 -type f | sort | sed -n '1,200p' && find seed_packs/phase1_20engineer_parallel_dispatch/tasks -maxdepth 1 -type f -name 'A04_*.md' -print`
   - Purpose: locate exact A04 task file.
   - Result: found `seed_packs/phase1_20engineer_parallel_dispatch/tasks/A04_audit_pnp3_barrier.md`.

4. `git checkout -B khanukov/phase1-A04-gpt55`
   - Purpose: create/check out required audit branch.
   - Result: branch switched successfully.

5. `sed -n ... RESEARCH_CONSTITUTION.md ... README.md ... COMMON_WORKER_INSTRUCTIONS.md ... A04_audit_pnp3_barrier.md`
   - Purpose: required reading.
   - Result: read/skimmed required governance and task instructions; noted prompt override for A04 naming.

6. `for f in pnp3/Barrier/NaturalProofs.lean pnp3/Barrier/Relativization.lean pnp3/Barrier/Algebrization.lean pnp3/Barrier/Bypass.lean pnp3/Tests/BarrierAudit.lean pnp3/Magnification/UnconditionalResearchGap.lean pnp3/Complexity/Interfaces.lean; do sed -n '1,240p' "$f"; done`
   - Purpose: read required barrier files and recommended context.
   - Result: four barrier files read; `BarrierAudit` read; optional large files skimmed/truncated for structural context.

7. `nl -ba pnp3/Barrier/Bypass.lean | sed -n '1,220p' && nl -ba pnp3/Tests/BarrierAudit.lean | sed -n '1,260p'`
   - Purpose: read full `Bypass.lean` and `BarrierAudit.lean` with line numbers.
   - Result: all declarations and tests identified.

8. `rg -n "NaturalProofConditions|SatisfiesNaturalProofBarrier|AvoidsNaturalProofBarrier|NaturalProofBypassWitness|Relativizing|RelativizationBypassWitness|Algebrizing|AlgebrizationBypassWitness|BarrierBypassAssumptions|BarrierBypassPackage|with_barriers|not_relativizing_of_bypass|not_algebrizing_of_bypass|avoidsNaturalProofBarrier_of_witness" . -g'*.lean' -g'*.md' --glob '!seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/**'`
   - Purpose: find uses and possible inhabitations.
   - Result: active Lean uses are declarations/wrappers/tests only; additional hits were historical docs/seed reports/tasks.

9. `rg -n "ResearchGapWitness|NP_not_subset_PpolyDAG|VerifiedNPDAGLowerBoundSource|SearchMCSPMagnificationContract|SourceTheorem|gap_from" pnp3/Barrier pnp3/Tests/BarrierAudit.lean`
   - Purpose: required hard-payload search over audit scope.
   - Result: only `NP_not_subset_PpolyDAG` in `P_ne_NP_final_with_barriers`; no `ResearchGapWitness`, `VerifiedNPDAGLowerBoundSource`, `SearchMCSPMagnificationContract`, `SourceTheorem`, or `gap_from`.

10. `rg -n "RefutedRoute|Vacuous|supportBounds|MagnificationAssumptions|FinalPayloadProvider|via_ex_falso|weakRoute|Legacy|_Partial|TODO|placeholder" pnp3/Barrier pnp3/Tests/BarrierAudit.lean`
    - Purpose: required refuted/vacuous/legacy search.
    - Result: `MagnificationAssumptions` and `RefutedRoute_NP_not_subset_PpolyFormula_final` in `Bypass.lean`; `_Partial` imports and refuted-route print in `BarrierAudit.lean`; no other listed terms.

11. `rg -n "\bclass\b|\binstance\b|default_instance|attribute \[instance\]|\bFact\b|\bopaque\b|Classical\.choose|noncomputable def" pnp3/Barrier pnp3/Tests/BarrierAudit.lean`
    - Purpose: required Rule 16 hidden-payload search.
    - Result: no matches.

12. `nl -ba pnp3/Tests/BarrierBypassAudit.lean | sed -n '1,120p' && rg -n "⟨|where|\{|exact|refine" pnp3 -g'*.lean' | rg "NaturalProofBypassWitness|RelativizationBypassWitness|AlgebrizationBypassWitness|BarrierBypassAssumptions"`
    - Purpose: inspect wrapper audit file and search for direct witness/package constructions.
    - Result: no direct constructions found outside structure declarations.

13. `./scripts/check.sh`
    - Purpose: required repository check.
    - Result: passed all 17 steps. Build emitted existing linter warnings in unrelated files, but ended with `[check] All checks passed.`

14. `nl -ba pnp3/Barrier/NaturalProofs.lean`, `nl -ba pnp3/Barrier/Relativization.lean`, `nl -ba pnp3/Barrier/Algebrization.lean`, `nl -ba pnp3/Tests/BarrierBypassAudit.lean`
    - Purpose: line-numbered verification for final report and citations.
    - Result: confirmed declaration line ranges.

## 20. Scope violations

None. I created exactly one markdown audit report and did not edit Lean/source/spec/JSONL files.

## 21. Final structured output

Task: A04  
Engineer handle: gpt55  
Branch: khanukov/phase1-A04-gpt55  
Commit before: d27b069127f63a3f24ab30d1a91c86c84f8b79c7  
Commit after: TBD after commit

Files added/modified:
  - `seed_packs/phase1_20engineer_parallel_dispatch/audit_reports/A04_pnp3_barrier_gpt55.md`

Outcome:
  AUDIT_LANDED

Executive verdict:
  PARTIAL_BUT_USEFUL

Files audited:
  - 13 files inspected or searched: required governance/task docs, four `pnp3/Barrier/*.lean` files, two barrier tests, optional trust-root context files, and NoGoLog validation/search context.

Key findings:
  1. The barrier files provide minimal typed interfaces and elementary witness-to-nonbarrier theorems, not concrete RR/relativization/algebrization bypass certificates.
  2. No active Lean construction of `NaturalProofBypassWitness`, `RelativizationBypassWitness`, or `AlgebrizationBypassWitness` was found.
  3. `BarrierBypassPackage` is an explicit `Prop` wrapper and should not be treated as evidence of actual barrier bypasses without stronger typed witnesses.

Kernel-checked content found:
  - Witness-to-avoidance/non-invariance theorems for natural proofs, relativization, and algebrization; explicit conjunction wrappers for barrier packages; locality audit theorems in `pnp3/Tests/BarrierAudit.lean`.

Staged / placeholder content found:
  - `NaturalProofConditions`, `Relativizing`, `Algebrizing`, all bypass witness structures, and especially `BarrierBypassAssumptions` / `BarrierBypassPackage` are staged/interface-level content until concretely instantiated.

Refuted / vacuous / legacy route findings:
  - `NP_not_subset_PpolyFormula_final_with_barriers` uses `RefutedRoute_NP_not_subset_PpolyFormula_final`; it is audit-only and not mainline progress.

Hidden payload / Rule 16 findings:
  - No class/instance/default instance/Fact/opaque/Classical.choose/noncomputable-provider patterns were found in the audited scope.

Recommended Phase 1+ tasks:
  - 4
  - B01 natural-proof concrete adapter skeleton in pnp4.
  - B02 relativization statement-scheme skeleton in pnp4.
  - B03 algebrization statement-scheme skeleton in pnp4.
  - Operator decision on a stricter pnp4-side typed barrier package.

Hold / cancel recommendations:
  - Hold tasks that claim barrier bypass by merely inhabiting `BarrierBypassPackage`.
  - Downgrade B01/B02/B03 implementation claims to adapter/interface work unless real witness theorems are supplied.
  - Cancel/rename ordinary Phase 1 tasks that would edit `pnp3/Barrier/**`.
  - Do not use the refuted formula-track wrapper as a progress endpoint.

Commands run:
  - `./scripts/check.sh` → pass; all 17 steps completed with existing unrelated linter warnings and final `[check] All checks passed.`
  - `rg -n "ResearchGapWitness|NP_not_subset_PpolyDAG|VerifiedNPDAGLowerBoundSource|SearchMCSPMagnificationContract|SourceTheorem|gap_from" pnp3/Barrier pnp3/Tests/BarrierAudit.lean` → one `NP_not_subset_PpolyDAG` hypothesis in `Bypass.lean`; no other hard-payload terms.
  - `rg -n "RefutedRoute|Vacuous|supportBounds|MagnificationAssumptions|FinalPayloadProvider|via_ex_falso|weakRoute|Legacy|_Partial|TODO|placeholder" pnp3/Barrier pnp3/Tests/BarrierAudit.lean` → `MagnificationAssumptions` and `RefutedRoute_*` in `Bypass.lean`; `_Partial`/audit prints in `BarrierAudit.lean`; no other listed terms.
  - `rg -n "\bclass\b|\binstance\b|default_instance|attribute \[instance\]|\bFact\b|\bopaque\b|Classical\.choose|noncomputable def" pnp3/Barrier pnp3/Tests/BarrierAudit.lean` → no matches.
  - Additional `rg`, `find`, `sed`, `nl`, `git`, and status commands are listed in section 19.

Scope violations:
  none

Honest caveats:
  - I did not reconstruct the complete import graph behind final magnification/provider theorems.
  - I did not manually audit every historical markdown mention of barrier names.
  - I verified signatures and wrapper structure, not the mathematical adequacy of future concrete oracle/barrier models.
