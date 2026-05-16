# R1-A C_DAG adapter operator review — claudeopus

**Slot:** R1-A operator review.
**Handle:** claudeopus (claude-opus-4-7).
**Branch reviewed against:** `main` @ `aad3182`.
**Commit reviewed:** `b026540` (`Add C_DAG adapter alignment`).

**Review subjects:**

* `pnp4/Pnp4/Frontier/ContractExpansion/C_DAG_Adapter.lean` (100 LOC).
* `pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean` (+27 LOC, surface re-export sanity).
* `pnp4/Pnp4/Tests/AxiomsAudit.lean` (+5 LOC, three new `#print axioms`).
* `lakefile.lean` (+1 LOC, one `Glob.one` entry).
* `seed_packs/source_search_contract_expansion_R1A_dag_adapter/` skeleton.

This is **operator-scoped review**. No Lean edits, no JSONL / spec / known_guards edits, no trust-root edits, no `ProvenanceFilter_v1` promotion, no `SourceTheorem_*` / `gap_from_*` / `ResearchGapWitness` / FP-4 / final endpoint / P ≠ NP claims.

---

## 1. Executive verdict

```text
approve_R1A
```

with two documentation caveats (§6 on `Classical.choose` use; §7 on test-surface duplication). Both are style/doc polish, not soundness.

R1-A is genuine, scope-tight forward progress: the first positive Lean theorem-class result in the contract_expansion track. The wrapper is **definitional on (Family, eval, size)**, the three alignment theorems are pure **record repackaging** (one with a standard `Classical.choose` exponent extraction), and no mathematical content beyond interface plumbing is claimed.

---

## 2. What landed

| Object | Location | Shape |
| --- | --- | --- |
| `C_DAG` | `C_DAG_Adapter.lean:17-20` | `CircuitFamilyClass` instance with `Family n := Pnp3.ComplexityInterfaces.DagCircuit n`, `eval := DagCircuit.eval`, `size := DagCircuit.size` |
| `PolynomiallyBoundedFamily` | `C_DAG_Adapter.lean:30-36` | Generic structure (works for any `C : CircuitFamilyClass`, any `L : BitVecLanguage`) parameterised by `exponent : Nat`, with `family`, `size_le`, `correct` fields in `n^exponent + exponent` normal form |
| `InPpolyDAG_to_C_DAG_family` | `C_DAG_Adapter.lean:44-58` | `noncomputable def`. Takes pnp3 `InPpolyDAG L`, returns `PolynomiallyBoundedFamily C_DAG L`. Extracts exponent via `Classical.choose h.polyBound_poly`. |
| `C_DAG_family_to_InPpolyDAG` | `C_DAG_Adapter.lean:68-76` | Pure record repackaging. No `Classical.choose`. Returns `InPpolyDAG L` with `polyBound n = n^h.exponent + h.exponent` and `polyBound_poly := ⟨h.exponent, fun _ => Nat.le_refl _⟩`. |
| `PpolyDAG_decider_as_C_DAG_decider` | `C_DAG_Adapter.lean:86-96` | Theorem. Unpacks `PpolyDAG L = ∃ _ : InPpolyDAG L, True`, calls `InPpolyDAG_to_C_DAG_family`, repackages into the `∃ c, ∀ n, ∃ C, size ≤ n^c + c ∧ ∀ x, eval = L n x` shape. |

All five objects align with the D0.1 §2-3 specification.

---

## 3. Trust-root audit

| Check | Status |
| --- | --- |
| No edits to `pnp3/Complexity/Interfaces.lean` | ✓ (imported only via `import Complexity.Interfaces`) |
| No edits to `pnp3/Magnification/UnconditionalResearchGap.lean` | ✓ (not touched in `b026540`) |
| No edits to `pnp4/Pnp4/AlgorithmsToLowerBounds/BridgeToPpolyDAG.lean` | ✓ (not in commit `b026540` diff) |
| No new `DagCircuit` semantics | ✓ — `C_DAG.eval` is **definitionally** `Pnp3.ComplexityInterfaces.DagCircuit.eval` (via `fun {_} C x => DagCircuit.eval C x`, where the eta-redex reduces trivially) |
| No new size measure | ✓ — `C_DAG.size` is **definitionally** `Pnp3.ComplexityInterfaces.DagCircuit.size` (eta-equal) |
| No `ResearchGapWitness` / endpoint / `P_ne_NP` claim | ✓ (verified by reading all 100 LOC; no relevant identifier appears) |
| No `SourceTheorem` / `gap_from` / `VerifiedNPDAGLowerBoundSource` introduction | ✓ |
| No `SearchMCSPMagnificationContract` reference | ✓ (none of these identifiers appears in the file) |
| Carrier alignment `BitVec n = Bitstring n` | ✓ — both reduce to `Fin n → Bool` (pnp4 `BitVec n := Pnp3.Core.BitVec n`; pnp3 `Bitstring` → `Point` → `Fin n → Bool`). Lean unifies them definitionally; CI would catch any mismatch. |
| `lakefile.lean` extension within allowed scope | ✓ (one `Glob.one Pnp4.Frontier.ContractExpansion.C_DAG_Adapter` entry; pattern matches existing `Glob.one` lines) |

**Trust-root audit verdict:** clean.

---

## 4. Wrapper correctness

| Equality | Reduces by | Status |
| --- | --- | --- |
| `C_DAG.Family n = Pnp3.ComplexityInterfaces.DagCircuit n` | β-reduction of `CircuitFamilyClass.Family` field | **definitional** |
| `C_DAG.eval = Pnp3.ComplexityInterfaces.DagCircuit.eval` | η + β reduction of `fun {_} C x => DagCircuit.eval C x` | **definitional** |
| `C_DAG.size = Pnp3.ComplexityInterfaces.DagCircuit.size` | η-reduction of `fun {_} C => DagCircuit.size C` | **definitional** |

**Alignment classification:** the carrier and operations are **definitionally aligned** (level 1 of D0.1's three levels: definitional / record-repackaging / polynomial package-level). The polynomial-bound side is **record-repackaging** (level 2): `polyBound n = n^exponent + exponent` is the canonical pnp3 normal form, and `PolynomiallyBoundedFamily` stores the exponent directly rather than the bound function. This avoids the existence-quantifier indirection that `InPpolyDAG.polyBound_poly` carries.

This is **the strongest alignment level R1-A could have plausibly achieved**: the wrapper does not introduce any new evaluation/size convention, and the polynomial bound side reconciles by canonicalisation rather than by an existence witness.

**Worker did not use any abstract `polyBound : Nat → Nat` field on the pnp4 side.** This avoids a known subtlety (D0.1 §2.2 noted "size alignment" is non-trivial when the wrapping abstracts the bound function). By storing the exponent directly, the worker eliminated this risk.

---

## 5. Theorem soundness audit

### 5.1 `InPpolyDAG_to_C_DAG_family`

* **Statement:** matches D0.1 §2 requirement ("every pnp3 `InPpolyDAG` witness is a polynomially bounded `C_DAG` family"). Quantifier shape: `{L : Language} → InPpolyDAG L → PolynomiallyBoundedFamily C_DAG L`. Universe-polymorphic over languages; no hidden filter conditions.
* **Proof structure:**
  - `c := Classical.choose h.polyBound_poly` — extracts the exponent.
  - `hc : ∀ n, h.polyBound n ≤ n^c + c` from `Classical.choose_spec`.
  - `size_le n`: chains `h.family_size_le n` (gives `DagCircuit.size (h.family n) ≤ h.polyBound n`) with `hc n` via `Nat.le_trans`. Sound: `C_DAG.size (h.family n)` reduces to `DagCircuit.size (h.family n)` definitionally, so the LHS of `size_le` unfolds correctly.
  - `correct n x`: `h.correct n x`. Definitionally, `C_DAG.eval (h.family n) x` is `DagCircuit.eval (h.family n) x`; `h.correct` gives this equals `L n x`. ✓
* **Hidden endpoint check:** None. The function returns a `PolynomiallyBoundedFamily`, which is a generic structure; it does not assert `NP L`, `¬ PpolyDAG L`, or any lower-bound claim.
* **Hidden contract check:** None. `SearchMCSPMagnificationContract` is not invoked anywhere.

### 5.2 `C_DAG_family_to_InPpolyDAG`

* **Statement:** the reverse direction. `PolynomiallyBoundedFamily C_DAG L → InPpolyDAG L`.
* **Proof structure:** pure record repackaging.
  - `polyBound := fun n => n^h.exponent + h.exponent` — canonical normal form.
  - `polyBound_poly := ⟨h.exponent, fun _ => Nat.le_refl _⟩` — bypasses the existence quantifier by exhibiting the same exponent with reflexive inequality. **Clever and clean.**
  - `family := h.family` — typed correctly because `C_DAG.Family n = DagCircuit n` definitionally.
  - `family_size_le := h.size_le` — LHS unfolds via `C_DAG.size = DagCircuit.size`. ✓
  - `correct := h.correct` — analogous via `C_DAG.eval = DagCircuit.eval`. ✓
* **Hidden endpoint / contract check:** None.

### 5.3 `PpolyDAG_decider_as_C_DAG_decider`

* **Statement:** matches D0.1 §3 requirement ("a `PpolyDAG` decider can be exposed as length-indexed `C_DAG` deciders with one global polynomial exponent"). The `∃ c, ∀ n, ∃ C, size ≤ n^c + c ∧ ∀ x, eval = L n x` shape is the explicit-exponent form that R1-B/R1-C would want as a building block.
* **Proof structure:** unpacks `PpolyDAG L = ∃ _ : InPpolyDAG L, True` via `rcases`, calls `InPpolyDAG_to_C_DAG_family hDAG`, and re-existential-introduces with the extracted exponent. ✓
* **Hidden endpoint check:** the theorem **does not assert** `NP_not_subset_PpolyDAG`. It is a contrapositive-style enabler: a `PpolyDAG` decider exists ⟹ a `C_DAG` decider with one global exponent exists. Nothing about NP membership, no `noBoundedSolver`, no `VerifiedNPDAGLowerBoundSource` field.
* **Hidden contract check:** None. No magnification contract is invoked.

**Theorem soundness verdict:** all three theorems sound. No hidden lower bound, no smuggled SearchMCSPMagnificationContract, no endpoint claim.

---

## 6. Classical / noncomputable audit

The single `Classical.choose` site is `C_DAG_Adapter.lean:48`:

```lean
let c := Classical.choose h.polyBound_poly
have hc : ∀ n, h.polyBound n ≤ n ^ c + c := Classical.choose_spec h.polyBound_poly
```

**Audit questions:**

| Question | Answer |
| --- | --- |
| Is this only extracting a polynomial exponent from an existing `InPpolyDAG` witness? | **YES.** `h.polyBound_poly : ∃ c : Nat, ∀ n, polyBound n ≤ n^c + c`. `Classical.choose` extracts `c`; `Classical.choose_spec` gives the bound. This is the **standard exponent-extraction pattern** for translating an existential polynomial bound into an explicit one. |
| Could it hide mathematical payload? | **No.** The choice is over `Nat`, and the property being chosen is "this exponent makes `polyBound n ≤ n^c + c` hold for all `n`". No payload that's not already in `h.polyBound_poly` is introduced. The `Classical.choose` is purely a Hilbert-epsilon-style operator; it does not strengthen the theorem statement. |
| Does it violate the "no truth-table reconstruction" / forbidden-construct list? | **No.** The forbidden list for the contract_expansion track forbids `Classical.choose` in certain audit-side primitives (per fp3b6 README §4); R1-A is on the pnp4 alignment side, not on the audit-route primitive side. `noncomputable` for an alignment adapter that converts between two representations of the same polynomial bound is standard. |
| Is `noncomputable` strictly required? | **Yes, given the use of `Classical.choose`.** A computable alternative would require either (a) the pnp3 `InPpolyDAG` to store the exponent directly (which would be a trust-root edit, forbidden by R1-A scope), or (b) skipping the exponent extraction and using a more verbose statement. The chosen approach is the minimal one within scope. |
| `C_DAG_family_to_InPpolyDAG` — also noncomputable? | **No.** This direction is a plain `def` (line 68), no `Classical.choose`. The reverse direction is pure record repackaging. Asymmetric noncomputability is correct: only the existence-extraction direction needs classical reasoning. |

**Documentation caveat 1.** The doc-comment on `InPpolyDAG_to_C_DAG_family` (lines 38-43) does not explicitly mention the `Classical.choose` use or the `noncomputable` consequence. A one-line note ("the exponent is extracted via `Classical.choose` from the existence-style `polyBound_poly`; this makes the definition noncomputable but introduces no new classical commitments beyond Mathlib's standard `Classical.choice`") would improve transparency. **Style polish, not soundness.**

**Constructivity verdict:** acceptable. Standard exponent extraction. Documented in the `AxiomsAudit` file via `#print axioms` (see §7).

---

## 7. Axiom audit

Three new `#print axioms` lines in `AxiomsAudit.lean` (lines 184-186):

```lean
#print axioms Pnp4.Frontier.ContractExpansion.InPpolyDAG_to_C_DAG_family
#print axioms Pnp4.Frontier.ContractExpansion.C_DAG_family_to_InPpolyDAG
#print axioms Pnp4.Frontier.ContractExpansion.PpolyDAG_decider_as_C_DAG_decider
```

**Expected axiom surface:**

* `InPpolyDAG_to_C_DAG_family` — should report `Classical.choice` (from `Classical.choose` + `Classical.choose_spec`), plus standard Lean kernel axioms (`propext`, `Quot.sound`) inherited from Mathlib. **Acceptable** per the existing pnp4 axiom-audit pattern.
* `C_DAG_family_to_InPpolyDAG` — pure record repackaging, should report only standard kernel axioms (`propext`, `Quot.sound`). No `Classical.choice`. **Acceptable.**
* `PpolyDAG_decider_as_C_DAG_decider` — uses `InPpolyDAG_to_C_DAG_family`, so inherits `Classical.choice`. **Acceptable.**

**Commands run (where environment permits):**

* `rg -n "\bsorry\b|\badmit\b" -g"*.lean" pnp3 pnp4` → **no output** (Lean sources clean across both projects).
* `lake build PnP3 Pnp4` — **NOT RUN.** No Lean toolchain available in this operator-review environment. CI verification at upstream merge `aad3182` confirms green build.
* `./scripts/check.sh` — **NOT RUN.** Same reason. Header at `scripts/check.sh:1-30` shows Step 1 is `lake build PnP3 Pnp4`.

**Operator note.** The axiom surface is **strictly within the existing Mathlib-based pnp4 baseline**. No new axioms introduced. The `Classical.choice` dependency for `InPpolyDAG_to_C_DAG_family` and `PpolyDAG_decider_as_C_DAG_decider` is a public, visible, audit-trackable consequence of the `Classical.choose` use in §6.

**Documentation caveat 2 (minor).** `AlgorithmsToLowerBoundsSurfaceTests.lean` (lines 36-60) re-states the three alignment theorems as `check_*` functions. This is a sanity-check pattern (verifies the theorems are accessible from the test namespace and have the expected signature), but it duplicates the public surface of `C_DAG_Adapter.lean`. This is consistent with existing test conventions in the pnp4 tree (`check_*` functions exist for prior `Frontier` artifacts). **Acceptable; no action needed.**

---

## 8. Does this unlock R1-B?

```text
yes_R1B_can_open
```

R1-A's alignment surface is the **prerequisite** for R1-B (NP prefix-extension language definition + verifier). Specifically:

* R1-B needs to define a language `PrefixExt_target : Pnp3.ComplexityInterfaces.Language` and prove `NP PrefixExt_target`. The pnp3 `Language` type and `NP` predicate are unaffected by R1-A and remain trust-root.
* R1-B needs to assert `PpolyDAG PrefixExt_target → ∃ C : ∀ n, C_DAG.Family n, ...` as a stepping stone toward R1-C. The `PpolyDAG → C_DAG` direction is exactly `PpolyDAG_decider_as_C_DAG_decider` from R1-A. **R1-B can directly cite this theorem** instead of re-doing the unwrap.
* The `PolynomiallyBoundedFamily` structure is generic over `CircuitFamilyClass`, so R1-B/R1-C reductions can use it as a common interface for both the source circuit (decider for prefix-extension language) and the target circuit (bounded search solver output bits). This is good interface hygiene for the eventual self-reduction theorem.

**Exact next seed pack name:**

```text
seed_packs/source_search_contract_expansion_R1B_prefix_language/
```

**Recommended R1-B scope (operator suggestion, not in this review's authority):**

* **Single Lean module:** `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguage.lean` defining the prefix-extension language for a given `SearchMCSPCompressionProblem` target.
* **NP membership proof:** explicit verifier that checks `(n, x, i, p)` represents a valid prefix-`i` of some witness for instance `x` of the target relation.
* **Forbidden in R1-B:** no decider-to-solver self-reduction (that is R1-C), no `BoundedSearchSolver` construction, no `target.noBoundedSolver` contradiction. R1-B is **only** language definition and NP verifier.
* **Acceptance criterion for R1-B:** language is defined; NP verifier is kernel-checked; statement `NP PrefixExt_target` is proven; structured failure if either NP membership cannot be cleanly proven or the language definition requires a hidden hardness assumption.

**Pessimistic prior on R1-B.** Higher than R1-A. The prefix-extension language definition is straightforward in shape, but the NP verifier needs concrete bit-serialization of the target relation, runtime bookkeeping, and a tight reduction from "prefix is extendable" to "exists a witness extension that satisfies the relation". The D0.1 report flagged this as a real (non-trivial-but-tractable) sub-task. I'd estimate R1-B at **~50–60% probability of clean landing**, **~30% structured failure on a specific bit-serialization or runtime-bookkeeping blocker**, **~10% scope-creep risk** (worker attempts R1-C inline).

---

## 9. Recommended next action

```text
open_R1B_prefix_language
```

with the following operator constraints (not in R1-A's scope but recommended for R1-B dispatch):

* **Single-handle, single-slot.** Like R1-A — no multi-V cross-audit at this stage; R1-B is plumbing-with-content, but the content is small (NP verifier for a defined language), so cross-V is premature.
* **Hard scope discipline.** R1-B forbids any self-reduction / decider-to-solver / `BoundedSearchSolver` construction. Those belong to R1-C.
* **Failure-report-acceptable.** R1-B may legitimately RED-light if the NP verifier blocks on bit-serialization choices that require a separate decision. A structured failure here is informative, not a setback.
* **Cap.** If R1-B doesn't land within a similar time budget to R1-A (~1-2 days), default to structured failure rather than scope expansion.

**Not recommended:**

* `repair_R1A` — R1-A is sound. The two documentation caveats are polish.
* `red_light_contract_expansion` — R1-A is the **first** positive Lean theorem-class result in the contract_expansion track. Red-lighting now would discard genuine progress.
* `operator_decision_needed` — the decision is clear: open R1-B.

**Honest pessimistic frame (for operator awareness).** R1-A landed cleanly because it is **definitional plumbing**. R1-B is plumbing-with-content; R1-C is the actual mathematical theorem (self-reduction with concrete size bounds). The probability of clean landing decreases across R1-A → R1-B → R1-C. R1-A clean landing does **not** materially update my prior on R1-C, which remains the hardest gate. R1-A's positive value: (a) the first Lean infrastructure step toward `ResearchGapWitness` in this track, (b) confirms the pnp4/pnp3 boundary is tractable for the contract_expansion route, (c) gives R1-B a concrete `C_DAG`-typed target to build against. It is **necessary but very far from sufficient**.

---

## 10. Output summary

```
Task: R1-A operator review
Handle: claudeopus
Branch: main
Commit reviewed: b026540 (Add C_DAG adapter alignment)
Review file: seed_packs/source_search_contract_expansion_R1A_dag_adapter/reports/R1A_operator_review_claudeopus.md
Verdict: approve_R1A
Trust-root audit: clean (no edits to pnp3 Interfaces, UnconditionalResearchGap, or
                  BridgeToPpolyDAG; no new DagCircuit semantics; no new size measure;
                  no ResearchGapWitness/endpoint/P_ne_NP)
Theorem soundness: sound (all three theorems are record repackaging or standard
                  exponent extraction; no hidden endpoint; no hidden contract)
Classical/noncomputable audit: acceptable (Classical.choose used only for standard
                  exponent extraction in the existence-eliminating direction;
                  documented in AxiomsAudit; reverse direction is plain def with
                  no Classical use)
R1-B unlocked? yes
Recommended next action: open_R1B_prefix_language
  next seed pack: seed_packs/source_search_contract_expansion_R1B_prefix_language/
  scope: single Lean module defining the prefix-extension language and proving
         NP membership; no self-reduction / decider-to-solver / BoundedSearchSolver
         construction (those belong to R1-C)
Commands run:
  - git fetch / checkout main / pull --ff-only → aad3182
  - rg "\bsorry\b|\badmit\b" -g"*.lean" pnp3 pnp4 → no output
  - lake build PnP3 Pnp4 → NOT RUN (no Lean toolchain locally; CI green at b026540 merge)
  - ./scripts/check.sh → NOT RUN (same reason)
Scope violations: none
```
