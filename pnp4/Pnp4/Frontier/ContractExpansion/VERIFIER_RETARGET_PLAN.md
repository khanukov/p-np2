# VERIFIER_RETARGET_PLAN — the frozen NP-verifier target and its first slices

**Status:** versioned decision record. **Base of record:** `main = 98250643`
(`Merge pull request #1626 from khanukov/work/runtime-advice`).
**Authored on branch:** `work/verifier-retarget-plan`.

**Progress classification (AGENTS.md): Infrastructure.** This document freezes a target and
schedules specification/machine-interface work. It proves nothing, reduces neither
`VerifiedNPDAGLowerBoundSource` nor `SearchMCSPWeakLowerBound`, and carries **no `P ≠ NP` claim**.

It supersedes, for everything on the current-`main` critical path, the earlier read-only planning
manifest `verifier-next-slices.md` (branch `work/verifier-planning`, base of record
`main = 5d8ee5f8`). §2 lists exactly which of that manifest's assumptions are now stale and which
survive. No implementation code is introduced here.

---

## 1. The frozen target

### 1.1 Decision

Input (2) of the conditional chain — the NP-membership obligation — is **frozen** at the
content-truthful route:

```text
target interface : ContentPrefixExtensionNPWitness (treeCircuitWitnessCodec (thresholdPoly k))
target predicate : ContentAccepts    codec (z : PrefixBitVec N)
target language  : ContentPrefixExtensionLanguage codec                                  (`L'`)
```

Exact declarations, all in `pnp4/Pnp4/Frontier/ContractExpansion/ContentPrefixExtension.lean`:

| Declaration | Line | Shape |
|---|---|---|
| `padRead` / `padWord` | `:77` / `:81` | blank-padded read of a finite bitstring |
| `contentHeader?` | `:111` | `decodeGamma? (padWord z (2 * N + 1)) tagLen` |
| `contentInput?` | `:123` | strict parser re-run on `padWord z (treeMCSPPrefixM codec n')` |
| `contentWitness` | `:135` | `codec.witnessBits n` cells at `treeMCSPPrefixM codec n` |
| **`ContentAccepts`** | **`:152`** | `∃ pr, contentInput? codec z = some pr ∧ pr.2.prefixAgrees … ∧ relation …` |
| `ContentPrefixExtendable` | `:165` | `∃ w, ContentAccepts codec (concatBitstring y w)` |
| `ContentPrefixExtensionLanguage` | `:172` | classical `Bool` wrapper of the above |
| **`ContentPrefixExtensionNPWitness`** | **`:211`** | `M`, `c`, `runTime_poly`, `correct` |
| `contentPrefixExtensionLanguage_in_NP_of_witness` | `:231` | witness ⇒ `NP L'` |

Downstream consumers already exist and are unconditional given the interface:
`ContentConsolidatedSource.lean:57` `verifiedSourceCT_of_noPolynomialBoundedSearchSolver`,
`:73` `verifiedSourceCT_treePoly`, `:86` `NP_not_subset_PpolyDAG_treePolyCT`. At the concrete
threshold those take exactly two explicit hypotheses: `NoPolynomialBoundedSearchSolver`
(input (1), untouched by this plan) and `ContentPrefixExtensionNPWitness` (input (2), the target).

Note the certificate exponent is **fixed to `k = 1`** by the interface: `ContentPrefixExtensionNPWitness`
has no `k` field, and `certificateLength n 1 = n + 1` (`pnp3/Complexity/Interfaces.lean:521`).
The length-gated `PrefixExtensionNPWitness` (`PrefixExtensionNPWitness.lean:75`) does carry a `k`.
Any slice that needs a different certificate exponent is out of scope by construction.

### 1.2 Retirement of the old target

`PrefixExtensionNPWitness` (`PrefixExtensionNPWitness.lean:75`) and its chain
(`ExplicitConditionalSource.lean`, `ConcreteTreeCodecSource.lean`,
`ConsolidatedTreeSeparation.lean`) are **retired as a destination for new work**. Concretely:

* **No new slice may state its headline against `PrefixExtensionLanguage`** or against
  `PrefixExtensionNPWitness`. A slice whose top-level theorem mentions either is rejected.
* **Audit compatibility is preserved.** The length-gated modules keep compiling, keep their
  `#check` lines in `pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean` and their
  `#print axioms` lines in `pnp4/Pnp4/Tests/AxiomsAudit.lean`, and keep being cited by
  `AGENTS.md`'s "most concrete live form" paragraph. Removing or weakening them is **not** part of
  this plan.
* **Bridging lemmas are still admissible** in the direction old → new only when they serve the CT
  route, i.e. instances of the coincidence family
  `ContentPrefixExtensionCoincidence.lean:276` `ContentPrefixExtendable_iff_of_parse` /
  `:324` `ContentPrefixExtensionLanguage_eq_of_parse`.
* One CT-A artifact is **mis-targeted and must be re-pointed** (slice P0): the semantic core
  `TreeMCSPPrefixSemanticVerifier.lean:252` `treePrefixSemanticAccepts_correct` is stated for
  `PrefixExtensionLanguage (treeMCSPConcretePrefixParser threshold codec)`, not for `L'`.

### 1.3 What the freeze does **not** buy — target-validity caveats

These must be restated in every slice's module docstring; they are the honest boundary of the frozen
target and two of them are new since the donor manifest.

1. **The `(★′)` bridge is the whole remaining machine obligation.** No verifier TM, no runtime
   bound, and no `TM.accepts … = ContentAccepts …` statement exists for `L'` anywhere in the
   repository.
2. **Padding invariance is proved for the predicate, not the language.**
   `ContentPrefixExtensionPadding.lean:314` `ContentAccepts_padWord_of_le` and `:333`
   `ContentAccepts_iff_of_padRead_eq` are about *complete* words. Membership in `L'` at physical
   length `m` quantifies over `Bitstring (certificateLength m 1)` concatenated at offset `m`, both
   of which move with `m`; wrapper-level invariance is unproved.
3. **The re-decode gate's vacuity is unproved.** `contentInput?` re-runs the strict parser on the
   narrow window `padWord z (treeMCSPPrefixM codec n')`, and that parser re-applies its own
   `m = treeMCSPPrefixM codec n_dec` test. Only the *widening* direction
   (`ContentPrefixExtensionCoincidence.lean:82` `decodeGammaAux?_mono`) is available; the narrowing
   direction is absent. Padding stability does not help — it gives agreement *including on failure*.
4. **Non-vacuity is unproved.** The only existential statement about `ContentAccepts`,
   `ContentPrefixExtensionPaddingTransport.lean:39` `ContentAccepts_padWord_of_prefixExtendable`, is
   conditional on `hparse`, `hn`, `hext`, `hT`, none discharged. This is what GATE-0 addresses.
5. **The obligation lives in this repository's machine model only.** `NP` is `NP_TM`
   (`pnp3/Complexity/Interfaces.lean:560`) over `Pnp3.Internal.PsubsetPpoly.TM`: deterministic
   single-tape, binary alphabet, no read-only input tape, tape length `n + runTime n + 1`,
   `runTime : ℕ → ℕ` an unrestricted **structure field**, and `TM.accepts` evaluated **at exactly
   step `runTime n`** with no halting predicate. No cross-model runtime-robustness theorem is
   formalized.
6. **The unrestricted `runTime` field is a live model audit finding.**
   `pnp4/Pnp4/Frontier/ModelAudit/RuntimeAdviceBarrier.lean:77`
   `lengthAdviceLanguage_in_repo_P` proves that *every* `A : Nat → Bool`, with no computability
   hypothesis, yields a length-only language in this repository's `P`, via
   `lengthAdviceTM` (`:44`) whose zero-or-one-step runtime stores `A n`. Consequence for this plan:
   discharging `ContentPrefixExtensionNPWitness` establishes NP-membership *in a model whose `P`
   admits arbitrary length advice*. This is not a reason to abandon the target — it is a reason
   never to describe the target as model-independent, and it is why slice D1 pins the exact-step
   clock explicitly rather than treating `runTime` as slack.

---

## 2. Re-audit of `verifier-next-slices.md` against current `main`

The donor manifest was written at `main = 5d8ee5f8`. `main` is now `98250643`, **36 commits ahead**,
and those commits are precisely the work that changed the retarget picture: `#1621` (AC0 audit),
`#1622` (documentation-state audit), **`#1623` (CT-A)**, **`#1624` (CT-B)**, **`#1625` (CT-C)**,
**`#1626` (runtime advice)**.

### 2.1 Stale assumptions — corrected

| Donor claim | Verdict | Correction |
|---|---|---|
| §0 "`main` = `5d8ee5f8`" | **stale** | `main = 98250643`; `git rev-list --count pr1618..main = 36`. |
| §0 "`ContractExpansion/` has 39 files on main" | **stale** | 47 files on `98250643` (`git ls-tree -r --name-only`). |
| §0 / §9 "Nothing on `main` is reusable"; "every module named below as a donor exists **only** in the PR stack" | **false** | Eight modules directly on the retarget path landed on `main` after the donor snapshot (§3.1). Six of them also exist, **divergently**, on `pr1618` (§3.2), so the PR stack is not a superset of `main`. |
| §0 "BASE for every slice: `4a8ee0c9`; do not branch from `main`" | **false for this plan** | Every slice in §4 is dependency-closed on `main = 98250643` and branches from it (§5). Branching from `4a8ee0c9` would *lose* the CT-A/B/C prerequisites. |
| §0 "`git diff --stat main...pr1618` = 184 files / +56544 / −2420 — the whole stack" | **arithmetically unchanged, semantically misleading** | The number is identical today only because `...` resolves to the merge base, which is still `5d8ee5f8`. It therefore describes the stack against a 36-commit-old `main`, and hides the rebase surface in §3.2. |
| §4 GATE-0 = "embedding-route spike (A′ vs B) on `clearIterProgram`" | **not this plan's GATE-0** | It gates donor slices P1…P4 / D3 inside `pr1618`. It has no bearing on any slice targeting `ContentAccepts`. Superseded by the GATE-0 of §4.0. |
| §4 track letters P / I / D = pop arm / input arm / driver | **repurposed** | Retargeted in §4 to P = predicate-side semantic core, I = invariance and gate closure, D = machine/clock interface. The donor tracks stay valid *inside* `pr1618` and are parked (§3.3). |
| §9 "The pop arm's machine is finished; only the run remains" | **true of `pr1618`, irrelevant to input (2)** | See §3.4: the donor machine is a transcoder, not a verifier. |

### 2.2 Donor findings re-verified as still accurate (on `pr1618`, not on `main`)

* `LoopLayout` (`TreeMCSPBinToUnaryLoopFullScanReachesSink.lean`) still carries the **global** blank
  clause `∀ q, (q : Nat) < (c.head : Nat) - u → c.tape q = false`. The donor's §3.2 blocker stands.
* `TreeMCSPDriverStepTape.lean` still has the degenerate `| _, _ => True` arm of `DriverStepFits`
  (line 139) alongside `| _, _ => tape` (line 89). The donor's §3.3 operand-underflow gap stands.
* `TreeMCSPPopIterRun.lean`, any `inputIter*`, `TreeMCSPDriverProgram.lean` and
  `TreeMCSPDriverRealizationInstance.lean` are all **absent** from `pr1618`, as the donor stated.
* Branch tips are unchanged: `pr1526 = b1f4f31d` (289 ahead of `main`), `pr1616 = 57ee057a` (335),
  `pr1618 = 4a8ee0c9` (364).

---

## 3. Module boundary: current `main` vs donor-only

### 3.1 On current `main` — the retarget's actual foundation (8 modules, all reusable)

Landed by `#1623`/`#1624`/`#1625`/`#1626`, all absent from the donor's base of record:

| Module | LOC | Key declarations for this plan |
|---|---|---|
| `ContentPrefixExtension.lean` | 239 | the frozen target, §1.1 |
| `ContentPrefixExtensionCoincidence.lean` | 341 | `readBit?_mono` `:47`, `readNatBE_mono` `:59`, `decodeGammaAux?_mono` `:82`, `decodeGamma?_concat_pad` `:115`, `parseTreeMCSPPrefixInput_inversion` `:140`, `padWord_concat_left` `:207`, `contentWitness_concat` `:218`, `contentInput?_concat_of_parse` `:244`, `ContentPrefixExtendable_iff_of_parse` `:276`, `ContentPrefixExtensionLanguage_eq_of_parse` `:324` |
| `ContentPrefixExtensionPadding.lean` | 358 | `padRead_padWord_of_le` `:103`, `eq_padWord_of_padRead_eq` `:120`, `readBit?_padWord_of_lt/_of_ge` `:136`/`:143`, `readNatBE_padWord_transfer` `:151`, `decodeGammaAux?_padWord_support` `:186`, `decodeGammaAux?_padWord_canonical` `:223`, `contentHeader?_padWord_of_le` `:278`, `contentInput?_padWord_of_le` `:293`, `contentWitness_padWord_of_le` `:300`, `ContentAccepts_padWord_of_le` `:314`, `ContentAccepts_iff_of_padRead_eq` `:333`, `contentHeader?_of_decodeGamma` `:349` |
| `ContentPrefixExtensionPaddingTransport.lean` | 63 | `ContentAccepts_padWord_of_prefixExtendable` `:39` (the classical conditional existential) |
| `ContentPrefixExtensionTransfer.lean` | 155 | `DecidesContentPrefixExtensionLanguage` `:51`, `boundedSearchSolver_of_PpolyDAG_contentPrefixExtension` `:111`, `not_PpolyDAG_contentPrefixExtension_of_noExtractedScheduleSolver` `:132`, `_of_noPolynomialBoundedSearchSolver` `:145` |
| `ContentConsolidatedSource.lean` | 96 | the three consolidated CT sources, §1.1 |
| `TreeMCSPPrefixSemanticVerifier.lean` | 304 | `witnessBits_le_treeMCSPPrefixM` `:78`, `prefixAgreesBool` `:99` + `_eq_true_iff` `:105`, `verifiesBool` `:121` + `_eq_true_iff` `:128`, `witnessBits_le_certificateLength` `:148`, `extractWitness?` `:160` + `extractWitness_eq` `:172`, `treePrefixSemanticAccepts` `:192`, `treePrefixSemanticAccepts_correct` `:252` (**mis-targeted, see §1.2**) |
| `TreeMCSPPrefixVerifierLayout.lean` | 274 | `prefixVerifierInputLen` `:33`, `prefixVerifierCertStart` `:44`, `concatBitstring_left/_right` `:72`/`:80`, `verifierTape_left/_right` `:103`/`:114`, `queryXOffset` `:136`, `queryIdxOffset` `:139`, `queryPrefixOffset` `:143`, `queryPrefixOffset_add_witnessBits` `:148`, `queryXOffset_le_treeMCSPPrefixM` `:166`, `gammaZeros` `:219`, `gammaTermOffset` `:223`, `gammaLen_eq_two_mul_gammaZeros_add_one` `:226`, `gammaMirror_mem` `:258` |

Plus the pre-existing foundation, unchanged since the donor snapshot and equally reusable:
`PrefixParserConvention.lean` (1337 LOC — `treeMCSPPrefixM` `:40`, `decodeGammaAux?` `:87`,
`decodeGamma?` `:101`, `encodeTreeMCSPPrefixFields` `:631`,
`encodeTreeMCSPPrefixFields_length_convention` `:659`,
`CanonicalRawTreeMCSPPrefixFields.toPrefixInput` `:675`, `parseTreeMCSPPrefixInput` `:1130`,
`parse_encodeTreeMCSPPrefixFields` `:1184`, `parseTreeMCSPPrefixInput_length_convention` `:1231`);
`TreeMCSPPrefixSerializer.lean` (`zeroPrefixQueryValue` `:57`, `parse_zeroPrefixQueryValue` `:68`,
`zeroPrefixQueryValue_parses` `:84`); `ConcreteTreeCodec.lean` (`treeCircuitWitnessCodec`);
`ThresholdGrowth.lean` (`thresholdPoly` `:36`);
`pnp4/Pnp4/Frontier/SearchMCSPConcreteTargets.lean` (`TreeCircuitWitnessCodec` `:44`,
`.verifies` `:61`, `.sound` `:73`, `.complete` `:85`, `treeMCSPSearchProblem` `:114`);
`pnp4/Pnp4/Frontier/ModelAudit/RuntimeAdviceBarrier.lean`.

### 3.2 Donor-only (`pr1618 = 4a8ee0c9`) — and the overlap that is *not* clean

`ContractExpansion/` has **216** files on `pr1618` versus 47 on `main`; **183** of them are
`TreeMCSP*` machine modules (region-embedding toolkit, arm programs, arm runs, corridor invariants,
driver interface, transcoder capstone). None of these exist on `main`.

But six modules exist on **both**, with different contents — so `pr1618` is not a superset and a
rebase is not a fast-forward. Byte sizes:

| Module | `pr1618` | `main` |
|---|---|---|
| `ContentPrefixExtension.lean` | 9 513 | **15 015** |
| `ContentPrefixExtensionCoincidence.lean` | 14 991 | **16 531** |
| `ContentPrefixExtensionTransfer.lean` | 7 387 | **8 761** |
| `ContentConsolidatedSource.lean` | 3 856 | **5 580** |
| `TreeMCSPPrefixSemanticVerifier.lean` | **15 858** | 14 166 |
| `TreeMCSPPrefixVerifierLayout.lean` | 12 967 | **14 231** |
| `ContentPrefixExtensionPadding.lean` | *absent* | **20 417** |
| `ContentPrefixExtensionPaddingTransport.lean` | *absent* | **63 LOC** |

`main` is ahead on the CT chain (CT-C exists only on `main`); `pr1618` is ahead only on
`TreeMCSPPrefixSemanticVerifier.lean`. Any future rebase of the stack must reconcile these six
files plus `lakefile.lean`, `AlgorithmsToLowerBoundsSurfaceTests.lean` and `AxiomsAudit.lean`.

### 3.3 Disposition of the donor stack: parked, not cancelled

`pr1526` / `pr1616` / `pr1618` are **parked**. No slice in this plan branches from them, imports
from them, or is blocked by them. They are not reviewed, rebased, or merged as part of the retarget.
Reactivation is a separate decision, and its first step is the six-file reconciliation of §3.2 —
not the donor's GATE-0.

### 3.4 Why the donor machine stack does not discharge input (2) — new finding

The donor's headline machine results are **transcoder** results, not verifier results.
`TreeMCSPTranscoderCapstone.lean` on `pr1618` proves `DriverRealization.transcodes` and
`DriverRealization.transcodes_faithful`: for a certificate `encodeCircuit width h_width c ++ tail`,
the machine's output window spells the `transcodeWitness` gate stream, and that stream decodes to a
straight-line program computing `Circuit.eval c` on every input — conditional on a
`DriverRealization` instance that does not exist.

Against the frozen target that is **one component of one conjunct**. It never:

* reads the tag or decodes the Elias-gamma header (`contentHeader?`);
* reads the truth-table field `x` or the prefix-length field `i`;
* checks `prefixAgrees`, i.e. that the certificate extends the query's active prefix;
* checks `Circuit.size c ≤ threshold n`, or compares `Circuit.eval c` against
  `truthTableFunction x` on all `tableLen n = 2 ^ n` points;
* says anything about `TM.accepts`, `runTime`, or the exact-step evaluation point.

So even a completed donor driver instance would leave the `(★′)` bridge open. **Corollary for
sequencing:** finishing the donor arms is not on the critical path to input (2), and the donor
manifest's estimate of "5 slices / ~3100–4400 LOC to the pop arm" buys nothing against the frozen
target. Any future revival must be justified as *witness-decoding reuse*, with the four bullets
above scheduled separately.

---

## 4. GATE-0 and the first slices

All four items below are **dependency-closed on `main = 98250643`**: every donor lemma they cite is
in §3.1, none is on `pr1618`. GATE-0, P0 and I1 are mutually independent and may run in parallel;
D1 is independent of all three.

Every slice obeys: **≤ 1500 changed `.lean` LOC (added + deleted) and ≤ 10 changed `.lean` modules**
(§6). Every new module carries the Infrastructure classification line and the
"**No `P ≠ NP` claim**" sentence, plus caveats 1–6 of §1.3 as applicable.

### 4.0 GATE-0 — non-vacuity of `ContentAccepts` at the concrete codec · **blocking for D-track, not for P0/I1**

**Why this is the gate.** Nothing proves that any word is `ContentAccepts`-accepted (§1.3, caveat 4).
If `ContentAccepts` were unsatisfiable at the concrete codec, `L'` would be the empty language;
`ContentPrefixExtensionNPWitness` would then be discharged by a trivial machine, and the
consolidated CT source `NP_not_subset_PpolyDAG_treePolyCT` would be worthless — its other
hypothesis, `NoPolynomialBoundedSearchSolver`, would be refuted rather than merely open, since
`ContentPrefixExtensionTransfer.lean:145` pins the *empty* `L'` outside `PpolyDAG`. Building a
verifier machine before settling this risks discharging a vacuous obligation. This replaces, and is
unrelated to, the donor's arm-embedding GATE-0.

**New module:** `ContentPrefixExtensionNonVacuity.lean`.

**Exact outputs.**

```lean
/-- Generic: a satisfied promise at `n` makes the zero-prefix query content-extendable. -/
theorem contentAccepts_zeroPrefixQuery_of_predicate
    {threshold : Nat → Nat} (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat) (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (hpred : treeMCSPPredicate n (threshold n) x) :
    ∃ w : Pnp3.ComplexityInterfaces.Bitstring
            (Pnp3.ComplexityInterfaces.certificateLength (treeMCSPPrefixM codec n) 1),
      ContentAccepts codec
        (Pnp3.ComplexityInterfaces.concatBitstring (zeroPrefixQueryValue codec n x) w)

/-- Hence the zero-prefix query is in `L'`. -/
theorem contentPrefixExtensionLanguage_zeroPrefixQuery
    {threshold : Nat → Nat} (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat) (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (hpred : treeMCSPPredicate n (threshold n) x) :
    ContentPrefixExtensionLanguage codec (treeMCSPPrefixM codec n)
      (zeroPrefixQueryValue codec n x) = true

/-- Concrete discharge: the all-false table is computed by `Circuit.const false`, of size `1`. -/
theorem contentAccepts_nonvacuous_treePoly (k n : Nat) :
    ∃ (N : Nat) (z : PrefixBitVec N),
      ContentAccepts (treeCircuitWitnessCodec (thresholdPoly k)) z
```

**Proof route, fully on `main`.**
`zeroPrefixQueryValue_parses` (`TreeMCSPPrefixSerializer.lean:84`) supplies *both* hypotheses that
`contentInput?_concat_of_parse` (`Coincidence.lean:244`) needs — `hparse` **and**
`hn : input.n = n` — so the re-decode gate is discharged *in this instance* without proving its
general vacuity. `prefixAgrees` is vacuous because `zeroPrefixFields` sets `i := 0`
(`TreeMCSPPrefixSerializer.lean:49`) and `PrefixInput.prefixAgrees` is a `∀ k : Fin input.i`
(`PrefixExtensionLanguage.lean:52`). The relation conjunct comes from
`TreeCircuitWitnessCodec.complete` (`SearchMCSPConcreteTargets.lean:85`), with the witness
transported into the certificate's leading `witnessBits` block by
`contentWitness_concat` (`Coincidence.lean:218`). The concrete discharge takes
`c := Pnp3.Models.Circuit.const false` (size `1`, `pnp3/Models/Model_PartialMCSP.lean:53`) against
`x := fun _ => false`, and `1 ≤ thresholdPoly k n = n ^ k + k` for every `k, n`.

**Budget:** 200–350 LOC · 1 module. **Exit:** all three theorems green with the standard axiom
triple, `#check`/`#print axioms` lines added.
**Stop/go (G0):** if the third theorem cannot be discharged — i.e. if satisfiability of
`ContentAccepts` at `treeCircuitWitnessCodec (thresholdPoly k)` resists a *concrete* witness —
**halt the D-track and escalate.** Do not begin machine work against a predicate not known to be
satisfiable. P0 and I1 remain admissible either way, since both are statements *about* the predicate
rather than claims that it holds.

### 4.1 P0 — content-side semantic verifier and its correctness · *parallel-safe, starts immediately*

**Why.** CT-A's semantic core is stated against the retired language (§1.2), and its signature
splits query and certificate (`treePrefixSemanticAccepts codec N query cert`,
`TreeMCSPPrefixSemanticVerifier.lean:192`), whereas `ContentAccepts` consumes a **single complete
word** read through `padRead`. The frozen target therefore has no `Bool`-valued computable
counterpart, which is the object every `TM.accepts` bridge must be compared against.

**New module:** `ContentSemanticVerifier.lean`.

**Exact outputs.**

```lean
/-- The content-computed `Bool` verifier on a complete word: content-parse, read the content
witness window, check prefix agreement and codec verification. -/
def contentSemanticAccepts {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {N : Nat} (z : PrefixBitVec N) : Bool

/-- **Headline: the Bool verifier decides the frozen predicate.** -/
theorem contentSemanticAccepts_eq_true_iff {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {N : Nat} (z : PrefixBitVec N) :
    contentSemanticAccepts codec z = true ↔ ContentAccepts codec z

/-- Rejection when the content parse fails. -/
theorem contentSemanticAccepts_eq_false_of_contentInput_none {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {N : Nat} (z : PrefixBitVec N)
    (h : contentInput? codec z = none) :
    contentSemanticAccepts codec z = false

/-- Padding stability, inherited: the Bool verifier is a function of the padded tape. -/
theorem contentSemanticAccepts_padWord_of_le {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {N T : Nat} (z : PrefixBitVec N) (hNT : N ≤ T) :
    contentSemanticAccepts codec (padWord z T) = contentSemanticAccepts codec z

/-- **The `L'`-side replacement for `treePrefixSemanticAccepts_correct`.** -/
theorem contentSemanticAccepts_correct {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {m : Nat} (y : PrefixBitVec m) :
    ContentPrefixExtensionLanguage codec m y = true
      ↔ ∃ w : Pnp3.ComplexityInterfaces.Bitstring
                (Pnp3.ComplexityInterfaces.certificateLength m 1),
          contentSemanticAccepts codec (Pnp3.ComplexityInterfaces.concatBitstring y w) = true
```

**Proof route, fully on `main`.** `contentInput?` is a plain `def` over the computable strict parser
(`PrefixParserConvention.lean:1130`); the two checks reuse `prefixAgreesBool` /
`prefixAgreesBool_eq_true_iff` (`TreeMCSPPrefixSemanticVerifier.lean:99`, `:105`) and `verifiesBool`
/ `verifiesBool_eq_true_iff` (`:121`, `:128`). The existential in `ContentAccepts` is pinned by
`contentInput? codec z = some pr`, so the `↔` is a `match` analysis, not a choice. Padding
stability is `contentInput?_padWord_of_le` (`Padding.lean:293`) and `contentWitness_padWord_of_le`
(`:300`). The last theorem is `ContentPrefixExtensionLanguage_accepts_iff`
(`ContentPrefixExtension.lean:178`) composed with the headline.

Note `contentSemanticAccepts` does **not** need `extractWitness?` (`:160`): the content witness
window is already total via `padRead`, so CT-A's dependent-slice machinery is bypassed. Do not port
it.

**Budget:** 350–550 LOC · 1–2 modules.
**Stop/go (G1):** the headline must be an unconditional `↔`, with **no** `hparse`/`hn` hypothesis. If
a hypothesis is needed, the `Bool` definition is wrong (it is failing to mirror `contentInput?`'s
own failure branches) — fix the definition, not the statement.
**Stop/go (G2):** `contentSemanticAccepts` must be genuinely computable — the `Decidable` instances
must route through `Fintype.decidableForallFintype` and
`TreeCircuitWitnessCodec.verifiesDecidable`, never `Classical.propDecidable`. Check by confirming
the first four theorems avoid `Classical.choice` in `#print axioms` (the fifth inherits it from the
noncomputable `concatBitstring` and the classical language wrapper, as CT-A's does).

### 4.2 I1 — close the two residual gate hypotheses · *parallel-safe, starts immediately*

**Why.** Two unproved side conditions currently infect every coincidence statement and would infect
the machine's correctness proof:

* `hn : input.n = n` in `ContentPrefixExtendable_iff_of_parse` (`Coincidence.lean:276`) and
  `ContentPrefixExtensionLanguage_eq_of_parse` (`:324`). Inversion
  (`parseTreeMCSPPrefixInput_inversion`, `:140`) yields only
  `treeMCSPPrefixM codec input.n = treeMCSPPrefixM codec n`; injectivity of `treeMCSPPrefixM codec`
  is not proved (docstring at `:321`).
* The narrowing direction of the gamma decode, which is what would make the re-decode gate inside
  `contentInput?` demonstrably vacuous (§1.3, caveat 3).

**Edited/new modules:** new `ContentPrefixExtensionGateClosure.lean`; no edit to
`Coincidence.lean` in this slice (the `hn`-free corollaries are stated in the new module, so the
existing surface and its audit lines stay untouched).

**Exact outputs.**

```lean
/-- `treeMCSPPrefixM codec` is strictly monotone, hence injective: the truth-table field alone
contributes `tableLen n = 2 ^ n`. -/
theorem treeMCSPPrefixM_injective {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) :
    Function.Injective (treeMCSPPrefixM codec)

/-- **`hn` eliminated.** -/
theorem ContentPrefixExtendable_iff_of_parse' {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    {n : Nat} (y : PrefixBitVec (treeMCSPPrefixM codec n))
    (input : PrefixInput
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec))
      (treeMCSPPrefixM codec n))
    (hparse : parseTreeMCSPPrefixInput threshold codec y = some input) :
    ContentPrefixExtendable codec y
      ↔ PrefixExtendable (treeMCSPConcretePrefixParser threshold codec) y

/-- **Gate vacuity on canonical headers.**  If the content header decodes with the canonical
zero-run length, the strict parser's re-decode on the narrow window `padWord z (M n')` returns the
same target — so the surviving `m = treeMCSPPrefixM codec n_dec` test compares `M n'` with itself. -/
theorem decodeGamma?_padWord_narrow_of_canonical {N : Nat} (z : PrefixBitVec N)
    {threshold : Nat → Nat} (codec : TreeCircuitWitnessCodec threshold)
    {n' consumed : Nat}
    (hheader : contentHeader? z = some (n', consumed))
    (hcanon : consumed = gammaLen n') :
    decodeGamma? (padWord z (treeMCSPPrefixM codec n')) tagLen = some (n', consumed)

/-- Hence the gate never fires on a canonical header. -/
theorem contentInput?_ne_none_of_canonical_header {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {N : Nat} (z : PrefixBitVec N)
    {n' consumed : Nat}
    (hheader : contentHeader? z = some (n', consumed))
    (hcanon : consumed = gammaLen n')
    (hfields : <the four strict field reads at the canonical offsets succeed>) :
    ∃ pr, contentInput? codec z = some pr
```

**Proof route, fully on `main`.** Injectivity: `treeMCSPPrefixM` (`PrefixParserConvention.lean:40`)
contains the summand `tableLen n = 2 ^ n`, and `tableLen_le_treeMCSPPrefixM` (`:48`) plus
`Nat.lt_two_pow_self` give strict monotonicity; `instanceSize_lt_treeMCSPPrefixM`
(`TreeMCSPPrefixVerifierLayout.lean:194`) is the model for the arithmetic.
Narrowing: `decodeGammaAux?_padWord_support` (`Padding.lean:186`) puts the terminator strictly inside
the support, `readNatBE_padWord_transfer` (`:151`) moves the payload read to the narrow window, and
the width side condition is exactly `queryXOffset_le_treeMCSPPrefixM`
(`TreeMCSPPrefixVerifierLayout.lean:166`) combined with
`gammaLen_eq_two_mul_gammaZeros_add_one` (`:226`) — i.e. `tagLen + 2 · gammaZeros n' + 1 ≤ M n'`.
The existing `decodeGammaAux?_padWord_canonical` (`Padding.lean:223`) cannot be reused: it requires
`2 * N + 1 ≤ T'`, i.e. widening, and here `T' = M n' < 2N + 1` for a complete word.

**The canonicity hypothesis is load-bearing and must not be dropped.** For a *non-canonical* header
(a long zero run with a small payload value) `2 · consumed + tagLen + 1` can exceed
`treeMCSPPrefixM codec n'`, the narrow read runs off the window, and `contentInput?` legitimately
returns `none`. That is sound behaviour, not a defect: such words are simply not in `L'`. A slice
claiming *unconditional* gate vacuity is wrong and must be rejected.

**Budget:** 400–700 LOC · 1–2 modules.
**Stop/go (G3):** if injectivity of `treeMCSPPrefixM codec` fails to go through, stop and re-plan —
every coincidence statement then permanently carries `hn`, and the machine's correctness proof
inherits it. Do **not** work around it by strengthening `PrefixInput`.
**Stop/go (G4):** if the narrowing lemma needs a hypothesis stronger than canonicity of the zero-run
length, record the exact extra hypothesis in this file and re-baseline; do not silently widen the
statement.

### 4.3 D1 — the machine-facing tape and clock interface · *parallel-safe, starts immediately*

**Why.** The `(★′)` bridge `TM.accepts (M := M) (concatBitstring x w) = contentSemanticAccepts …`
compares two objects that are currently stated over different data: `TM.accepts` reads a
`Configuration` tape of length `TM.tapeLength n = n + runTime n + 1`, while `ContentAccepts` reads
`padRead` of a finite word. Identifying the two is a theorem, not a definition, and it is the exact
point where caveat 6 (the unrestricted `runTime`) becomes visible.

CT-A's layout module is the donor but is **not sufficient on its own**: `verifierTape_left` (`:103`)
and `verifierTape_right` (`:114`) read the start tape in the two `concatBitstring` ranges, and every
offset lemma (`:136`–`:270`) is stated against the *length-gated* query block
`treeMCSPPrefixM codec n`, not against the content-computed window.

**New module:** `ContentVerifierTapeInterface.lean`.

**Exact outputs.**

```lean
/-- **The start tape is the blank-padded complete word.**  For every in-range cell, the
`initialConfig` tape of the concatenated input equals `padRead` of that word — including past the
support, where both are the blank `false`. -/
theorem initialConfig_tape_eq_padRead
    (M : Pnp3.Internal.PsubsetPpoly.TM.{0}) {n m : Nat}
    (x : Pnp3.ComplexityInterfaces.Bitstring n)
    (w : Pnp3.ComplexityInterfaces.Bitstring m)
    (j : Fin (M.tapeLength (n + m))) :
    (<initialConfig of (concatBitstring x w)>).tape j
      = padRead (Pnp3.ComplexityInterfaces.concatBitstring x w) (j : Nat)

/-- **Tape-determined acceptance.**  Any two complete words with the same blank-padded tape are
`ContentAccepts`-equivalent — the machine-facing form of `ContentAccepts_iff_of_padRead_eq`. -/
theorem contentAccepts_of_initialConfig_tape_eq {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {N N' : Nat}
    (z : PrefixBitVec N) (z' : PrefixBitVec N')
    (h : ∀ j, padRead z j = padRead z' j) :
    ContentAccepts codec z ↔ ContentAccepts codec z'

/-- **The exact-step obligation, named.**  The bridge a verifier machine must discharge, with the
evaluation point spelled out as `runTime` rather than left implicit. -/
structure ContentVerifierBridge {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) where
  M : Pnp3.Internal.PsubsetPpoly.TM.{0}
  c : Nat
  runTime_poly : ∀ n,
    M.runTime (n + Pnp3.ComplexityInterfaces.certificateLength n 1)
      ≤ (n + Pnp3.ComplexityInterfaces.certificateLength n 1) ^ c + c
  accepts_eq : ∀ n (x : Pnp3.ComplexityInterfaces.Bitstring n)
      (w : Pnp3.ComplexityInterfaces.Bitstring
             (Pnp3.ComplexityInterfaces.certificateLength n 1)),
    Pnp3.Internal.PsubsetPpoly.TM.accepts
        (M := M) (n := n + Pnp3.ComplexityInterfaces.certificateLength n 1)
        (Pnp3.ComplexityInterfaces.concatBitstring x w)
      = contentSemanticAccepts codec (Pnp3.ComplexityInterfaces.concatBitstring x w)

/-- **The bridge discharges the frozen target.**  `(★′)` plus P0's correctness theorem *is* the
NP-witness — the only remaining input is a machine satisfying `ContentVerifierBridge`. -/
def contentPrefixExtensionNPWitness_of_bridge {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (B : ContentVerifierBridge codec) :
    ContentPrefixExtensionNPWitness codec
```

**Proof route.** The first theorem is read off `initialConfig` in
`pnp3/Complexity/PsubsetPpolyInternal/TuringEncoding.lean` — modelled line-for-line on
`verifierTape_left` / `verifierTape_right` (`TreeMCSPPrefixVerifierLayout.lean:103`, `:114`), with
`padRead_ge` (`ContentPrefixExtension.lean:88`) covering the blank tail. The second is
`ContentAccepts_iff_of_padRead_eq` (`Padding.lean:333`) restated for machine consumers. The last is
a one-line repackaging: `accepts_eq` rewrites `TM.accepts` into `contentSemanticAccepts`, and P0's
`contentSemanticAccepts_correct` converts that into the `correct` field of
`ContentPrefixExtensionNPWitness` (`ContentPrefixExtension.lean:211`).

**Dependency note.** The final declaration is the only cross-slice edge among the first four items:
it needs P0. Land D1's first three outputs independently, then add
`contentPrefixExtensionNPWitness_of_bridge` in the same slice only if P0 has already merged;
otherwise defer that one declaration to a D1b follow-up rather than blocking.

**Budget:** 300–500 LOC · 1–2 modules.
**Stop/go (G5):** `ContentVerifierBridge.accepts_eq` must be stated with the concatenated length
`n + certificateLength n 1` and no "within `t` steps" quantifier. If a slice introduces a
step-bounded or halting-based variant it has silently changed the machine model — reject it.
**Stop/go (G6):** `contentPrefixExtensionNPWitness_of_bridge` must consume `runTime_poly` verbatim.
If it needs to *construct* a runtime bound, the bridge structure is under-specified. Never exploit
the unrestricted `runTime` field to make `accepts_eq` easier: that is precisely the advice channel
`lengthAdviceLanguage_in_repo_P` (`RuntimeAdviceBarrier.lean:77`) exhibits, and a bridge that
depends on it is not a verifier.

### 4.4 Dependency graph and parallelism

```text
GATE-0  ─┐
P0      ─┼─ independent, start all four now
I1      ─┤
D1(a)   ─┘

P0        → D1(b) = contentPrefixExtensionNPWitness_of_bridge
GATE-0    → any D-track slice past D1  (do not build a machine for a possibly-vacuous predicate)
I1        → hn-free coincidence consumers  (quality-of-life, blocks nothing in this batch)
{P0, D1}  → the machine construction slices (out of scope here; a separate plan revision)
```

**Shared-file conflict surface — serialize the append or reserve a per-slice block:**

* `lakefile.lean` — the `lean_lib Pnp4` `Glob.one` list. Every slice touches it (AGENTS.md).
* `pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean` — add to the
  `ContentPrefixExtensionSurface` section; GATE-0 and P0 both append there.
* `pnp4/Pnp4/Tests/AxiomsAudit.lean` — one `#print axioms` line per new public theorem.
* `pnp4/Pnp4/Frontier/ContractExpansion/README.md` — the CT module list.
* This file — §7 log.

Assign each slice a contiguous reserved block in the three shared files at kickoff; conflicts then
resolve as adjacent-line merges.

### 4.5 Rejected slice proposals

* **"Rebase `pr1618` onto `main`"** as a retarget slice — §3.2/§3.4: it is a 184-file, six-way
  reconciliation that does not advance the frozen target.
* **"Finish `popIter_run_*` / `inputIter_run_full` / the driver instance"** — donor-only,
  transcoder-side, off the critical path (§3.4).
* **"Port `extractWitness?` to the content side"** — dead weight: `contentWitness` is total
  (§4.1).
* **"Retarget the layout offsets to the content window"** as a standalone slice — pure layout,
  rejected by the no-layout-only rule. Folded into D1, which carries
  `initialConfig_tape_eq_padRead`.
* **"Prove wrapper-level padding invariance of `L'`"** — not obviously true (the certificate length
  and concatenation offset both move with `m`, §1.3 caveat 2) and not needed by any of the four
  slices. Out of scope until a slice demonstrably needs it.
* **"Delete or deprecate the length-gated chain"** — forbidden by §1.2 (audit compatibility).
* **"Prove unconditional vacuity of the re-decode gate"** — false as stated (§4.2).

---

## 5. Branch and base strategy

```bash
# Base every slice on main, NOT on 4a8ee0c9.
git fetch origin
git checkout -b work/<slice-name> 98250643      # or the then-current main
```

* **Base:** `main` (`98250643` at time of writing). One branch per slice, one PR per branch,
  PR base `main`. No stacking: the four first slices are independent, so stacking would only
  serialize review.
* **Naming:** `work/ct-<letter><number>-<topic>`, matching the CT-A/B/C precedent
  (`work/ct-a-verifier-prereqs`, `work/ct-b-source-chain`, `work/ct-c-padding-stability`).
  So: `work/ct-gate0-nonvacuity`, `work/ct-p0-content-semantic-verifier`,
  `work/ct-i1-gate-closure`, `work/ct-d1-tape-interface`.
* **Never branch from `pr1526` / `pr1616` / `pr1618`** (§3.3). Never merge them into a slice branch.
* **No push without an explicit request** (AGENTS.md line 83). Local commits only by default.
* **Rebase, don't merge**, when `main` moves under an open slice; re-run §6 after every rebase,
  because the LOC/module gate is measured against the *current* merge base.

---

## 6. Size and acceptance gates

### 6.1 Size gate — must pass before opening a PR, and again after every rebase

```bash
# ≤ 1500 changed .lean LOC (added + deleted)
git diff --stat "$(git merge-base main HEAD)"...HEAD -- '*.lean' | tail -1
# ≤ 10 changed .lean modules
git diff --name-only "$(git merge-base main HEAD)"...HEAD -- '*.lean' | wc -l
```

Never waived. If a slice breaches either bound, split it before review — the split points are named
in each slice's "modules" range in §4.

### 6.2 Acceptance commands, in order

```bash
# 1. per-module compile — fastest failure signal
lake build Pnp4.Frontier.ContractExpansion.<NewModule>

# 2. both libraries (check.sh step 1 needs Pnp4's axiom dump)
lake build PnP3 Pnp4

# 3. smoke + tests
lake env lean --run scripts/smoke.lean
lake test

# 4. repository gate (17 steps: build, hygiene, axiom inventory, doc route policy, surface audit)
./scripts/check.sh

# 5. documentation honesty linter (Tier 2, repo-wide)
./scripts/check_doc_honesty.sh

# 6. purity gate — the audit block must print only the standard triple
lake build Pnp4 2>&1 | grep -A1 "depends on axioms" \
  | grep -v "propext, Classical.choice, Quot.sound"     # must produce no output

# 7. hygiene (also inside check.sh; standalone for speed)
rg -n "\bsorry\b|\badmit\b|\bnative_decide\b|^\s*axiom " -g'*.lean' pnp4   # must be empty
```

### 6.3 Mandatory per AGENTS.md, every slice

* new module registered in `lakefile.lean`;
* every new public theorem `#check`ed in
  `pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean` (`ContentPrefixExtensionSurface`);
* every new audited surface `#print axioms`-ed in `pnp4/Pnp4/Tests/AxiomsAudit.lean`;
* no `axiom` / `sorry` / `admit` / `native_decide`;
* module docstring states **Infrastructure** and "**No `P ≠ NP` claim**", and reproduces the
  applicable caveats from §1.3.

---

## 7. Review workflow

The CT-A/B/C commit history is the template; each slice follows the same five stages, and the
per-stage fix commits are expected to be visible in the branch log (as in
`20be8cbf` "address CT-A review", `9ba903d4` "doc-audit fixes", `545fc200` "count split padding
modules accurately").

1. **Implement.** One slice, one branch. Author the Lean, register it, add the surface and axiom
   lines, run §6.2 end to end locally.
2. **Qodo review** on the PR. Treat every finding as blocking until answered in writing. Qodo
   catches statement/docstring mismatches, which are the dominant defect class in this directory —
   the CT-C history is mostly prose-scope corrections, not proof fixes.
3. **Claude review** (`/code-review`, effort `high`, plus `/security-review` when a slice touches
   the machine model). Focus: does the headline actually say what the docstring claims, and is any
   hypothesis silently doing the work?
4. **Codex cross-check.** Independent re-derivation of the slice's headline from its cited donors,
   without reading the proof. Its job is to catch a *true theorem that does not mean what the plan
   said it would* — the failure mode §3.4 found in the donor stack.
5. **Documentation audit.** Re-read the slice's docstrings and this file's §1.3 against the merged
   statements. Update `ContractExpansion/README.md`, and §7's log below, in the same PR. Then
   re-run `./scripts/check.sh` and `./scripts/check_doc_honesty.sh`, because the doc guards read
   Markdown that step 5 has just changed.

**Scope discipline for reviewers.** Reject a slice that (i) states a headline against
`PrefixExtensionLanguage` or `PrefixExtensionNPWitness` (§1.2); (ii) claims any machine-side
consequence from a specification-side lemma; (iii) describes the CT route as removing
length-dependence from the machine (`runTime_poly` is still taken at
`n + certificateLength n 1`); (iv) describes the decision→search extraction as an equivalence
(AGENTS.md line 36); or (v) reports green CI as mathematical progress.

### 7.1 Slice log

| Slice | Branch | Status | Merged as |
|---|---|---|---|
| GATE-0 non-vacuity | `work/ct-gate0-nonvacuity` | not started | — |
| P0 content semantic verifier | `work/ct-p0-content-semantic-verifier` | not started | — |
| I1 gate closure | `work/ct-i1-gate-closure` | not started | — |
| D1 tape/clock interface | `work/ct-d1-tape-interface` | not started | — |

---

## 8. Stop/go summary

| Gate | Slice | Condition | Action if red |
|---|---|---|---|
| **G0** | GATE-0 | a *concrete* word is `ContentAccepts`-accepted at `treeCircuitWitnessCodec (thresholdPoly k)` | halt the D-track and escalate; do not build a machine for a possibly-empty `L'`. P0/I1 continue |
| **G1** | P0 | the `Bool`↔`Prop` headline is hypothesis-free | fix the `Bool` definition's failure branches, not the statement |
| **G2** | P0 | the four non-wrapper theorems avoid `Classical.choice` | replace `Classical.propDecidable` with the genuine instances |
| **G3** | I1 | `treeMCSPPrefixM codec` is injective | stop and re-plan; `hn` becomes permanent and infects the machine proof. Do not strengthen `PrefixInput` to dodge it |
| **G4** | I1 | narrowing needs no hypothesis beyond canonicity of the zero-run | record the exact extra hypothesis here and re-baseline |
| **G5** | D1 | `accepts_eq` uses the exact-step model, no halting/`∃ t ≤` variant | reject: the slice has changed the machine model |
| **G6** | D1 | the witness repackaging consumes `runTime_poly` verbatim | the bridge structure is under-specified; do not route through the advice channel |
| **G7** | all | ≤ 1500 LOC and ≤ 10 modules at PR time (§6.1) | split before review; never waived |
| **G8** | all | `./scripts/check.sh` and `./scripts/check_doc_honesty.sh` green | fix before review; a red doc guard is a blocking defect, not a formality |
| **G9** | all | axiom footprint is the standard triple or lighter | investigate any fourth axiom before merge |

---

## 9. Bottom line

* Input (2) is frozen at `ContentPrefixExtensionNPWitness` / `ContentAccepts`
  (`ContentPrefixExtension.lean:211`, `:152`). New work against the length-gated
  `PrefixExtensionNPWitness` stops; its modules stay for audit compatibility.
* The donor manifest's central premise — "nothing on `main` is reusable, branch from `4a8ee0c9`" —
  is now false. Eight modules on `main` (CT-A/B/C) are the actual foundation, and all four first
  slices are dependency-closed on `main = 98250643`.
* The donor TM stack is a **transcoder**, not a verifier: it decodes a certificate into an evaluable
  gate stream and never touches the header, the truth table, the size check, or `TM.accepts`.
  Completing it would not discharge the `(★′)` bridge. It is parked.
* Two obligations are unproved and must not be assumed: satisfiability of `ContentAccepts` (GATE-0)
  and vacuity of the strict parser's surviving re-decode gate (I1, provable only under canonicity).
* The machine model's `runTime` field is unrestricted
  (`RuntimeAdviceBarrier.lean:77` `lengthAdviceLanguage_in_repo_P`), so input (2) is an obligation
  *in this model*, and D1 pins the exact-step clock rather than treating it as slack.
* GATE-0, P0, I1 and D1(a) start in parallel today; total 1250–2100 LOC across 5–7 new modules.
