# VERIFIER_RETARGET_PLAN — the *provisionally* frozen NP-verifier target and its first slices

**Status:** versioned decision record. **Base of record:** `main = 98250643`
(`Merge pull request #1626 from khanukov/work/runtime-advice`).
**Authored on branch:** `work/verifier-retarget-plan`.

**Progress classification (AGENTS.md): Infrastructure.** This document freezes a target
*provisionally* and schedules specification/machine-interface work. It proves nothing, reduces
neither `VerifiedNPDAGLowerBoundSource` nor `SearchMCSPWeakLowerBound`, and carries
**no `P ≠ NP` claim**.

It supersedes, for everything on the current-`main` critical path, the earlier read-only planning
manifest `verifier-next-slices.md` (branch `work/verifier-planning`, base of record
`main = 5d8ee5f8`). §2 lists exactly which of that manifest's assumptions are now stale and which
survive. No implementation code is introduced here.

> **Revision note (this revision).** The previous revision of this file froze the target
> *unconditionally* and retired the length-gated target immediately. Review found a feasibility
> hole that makes both moves premature (§1.0), a **false** generic injectivity goal (§4.3), a
> gamma-canonicity hypothesis that is actually a **theorem** (§4.3), incorrect axiom expectations
> for P0 (§4.2), an unenforceable runtime-advice gate (§1.3 caveat 6), and several inventory /
> unit / range errors. All are resolved below.

---

## 1. The target

### 1.0 FEAS-0 — the feasibility gate that the freeze is conditional on · **blocking for the freeze itself**

**The hole.** `ContentAccepts` reads its query window at the *content-computed* length
`treeMCSPPrefixM codec n'`, where `n'` is decoded from the word's own Elias-gamma header. Nothing
bounds `n'` polynomially in the physical length `N`. Concretely, on `main`:

* `contentHeader? z = decodeGamma? (padWord z (2 * N + 1)) tagLen`
  (`ContentPrefixExtension.lean:111`). `decodeGammaAux?` (`PrefixParserConvention.lean:87`) scans
  for the unary terminator, i.e. the first `true` bit at `tagLen + zeros`. Every cell at index
  `≥ N` reads blank (`padRead_ge`, `ContentPrefixExtension.lean:88`), so a successful decode forces
  the terminator *inside the support*: `tagLen + zeros < N`.
* The decoded value is `n' + 1 = 2 ^ zeros + payload` with `payload < 2 ^ zeros`. Hence `n'` may be
  as large as `2 ^ (N - tagLen - 1) - 1` — **exponential in `N`** (`tagLen = 8`,
  `PrefixParserConvention.lean:13`).
* `contentInput?` then runs the strict parser on `padWord z (treeMCSPPrefixM codec n')`, and
  `treeMCSPPrefixM codec n' ≥ tableLen n' = 2 ^ n'` (`tableLen_le_treeMCSPPrefixM`,
  `PrefixParserConvention.lean:48`) — **doubly exponential in `N`**. The relation conjunct of
  `ContentAccepts` is `codec.verifies n' x w`, whose `ComputesTruthTable` component
  (`TruthTableMCSP.lean:35`) quantifies over all `2 ^ n'` inputs.

Such words are not hypothetical, and they *parse*. Take `zeros := N - tagLen - 1`, a single `1` at
index `N - 1`, the tag field set to `treePrefixTag` (`PrefixParserConvention.lean:10`), everything
else `false`. Then `payload = 0` (blank), so `n' + 1 = 2 ^ zeros` and `consumed = 2 * zeros + 1`,
which is *exactly* `gammaLen n'` (§4.3). The strict parser's length gate compares
`treeMCSPPrefixM codec n'` with itself and passes; every field slice fits by the Layout offset
lemmas (§4.3); `x` is the all-false table, `i = 0`, `p` empty, `pad` all-zero, so `prefixAgrees` is
vacuous and `padZero = true`. Acceptance of that word therefore reduces to the single question
`codec.verifies n' (all-false table) (all-zero witness block)` — and *whatever the answer*, a
polynomial-time verifier must decide it in `poly(N)` steps without reading a `2 ^ n'`-cell window.

**Why this blocks the freeze, not just the D-track.** The length gate that the CT route removed was
doing feasibility work: on the length-gated target, `N = treeMCSPPrefixM codec n` pins
`n = O(log N)` by construction, so the verifier's work is polynomial in its input. `ContentAccepts`
drops that gate and replaces it with nothing. Until FEAS-0 is settled, we do not know that `L' ∈ NP`
is *achievable at all* by this route — so the target is frozen **provisionally**, and the
length-gated target is **not retired** (§1.2).

**FEAS-0 must produce one of three outcomes.**

*(a) Polynomial size bound.* An unconditional bound from accepted complete words to the decoded
convention length:

```lean
theorem contentAccepts_target_poly {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) :
    ∃ c : Nat, ∀ (N : Nat) (z : PrefixBitVec N) (n' consumed : Nat),
      contentHeader? z = some (n', consumed) →
      ContentAccepts codec z →
      treeMCSPPrefixM codec n' ≤ N ^ c + c
```

**Expect this to be false in general.** If `codec.decode n' (fun _ => false)` returns
`some (Circuit.const false)` — size `1 ≤ thresholdPoly k n'` — then the word above *is* accepted
with `treeMCSPPrefixM codec n'` doubly exponential in `N`, refuting (a). Whether the *concrete*
`treeCircuitWitnessCodec (thresholdPoly k)` (`ConcreteTreeCodec.lean:67`) does this is open and is
FEAS-0's first computation; it is fixed by `treeSelfDelimitingCode` (`:53`) through
`SelfDelimitingCircuitCode.toCodec`. Settle it before anything else in this file is scheduled.

*(b) Polynomial fast-rejection equivalent.* A `Bool` predicate `contentBudgetOK` on the word,
computable in `poly(N)` *without materialising the wide window*, such that

```lean
theorem contentBudgetOK_eq_false_rejects {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {N : Nat} (z : PrefixBitVec N) :
    contentBudgetOK codec z = false → ¬ ContentAccepts codec z

theorem contentBudgetOK_bounds_target {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {N : Nat} (z : PrefixBitVec N)
    {n' consumed : Nat} (hheader : contentHeader? z = some (n', consumed))
    (hok : contentBudgetOK codec z = true) :
    treeMCSPPrefixM codec n' ≤ <an explicit polynomial in N>
```

i.e. every word whose decoded target is super-polynomial is rejected by a check that never reads the
big window. Note `contentBudgetOK` may inspect the header (`O(N)` cells) and the *support* of `z`,
but must not slice at offsets beyond `poly(N)`.

*(c) Target repair.* If neither (a) nor (b) goes through, `ContentAccepts` is the wrong predicate
and the freeze is void. The repair direction is a **budgeted** content predicate — a content-side
gate that is polynomial rather than absent, e.g. requiring
`tagLen + gammaLen n' + tableLen n' ≤ N` (which recovers `n' = O(log N)` without re-introducing the
exact equality `N = treeMCSPPrefixM codec n`). That is a new §1.1 and a new plan revision, not a
slice.

**Budget:** 250–450 LOC · 1–2 modules (`ContentTargetSizeBound.lean`).
**Exit (FEAS-0 green):** (a) or (b) proved, `#check`/`#print axioms` lines added, and this file's
§1.1/§1.2 promoted from *provisional* to *frozen* in the same PR.
**Stop/go (F0):** if the outcome is (c), **halt GATE-0, P0, I1, D1a and D1b**, revise §1.1, and do
not open any slice against `ContentAccepts` until the repaired predicate is frozen. FEAS-0 is the
only item in §4 that may start while the freeze is provisional.

### 1.1 The provisionally frozen target

Input (2) of the conditional chain — the NP-membership obligation — is **provisionally frozen**
(§1.0) at the content-truthful route:

```text
target interface : ContentPrefixExtensionNPWitness (treeCircuitWitnessCodec (thresholdPoly k))
target predicate : ContentAccepts    codec (z : PrefixBitVec N)
target language  : ContentPrefixExtensionLanguage codec                                  (`L'`)
```

Exact declarations, all in `pnp4/Pnp4/Frontier/ContractExpansion/ContentPrefixExtension.lean`:

| Declaration | Line | Shape |
|---|---|---|
| `padRead` / `padWord` | `:77` / `:81` | blank-padded read of a finite bitstring |
| `padRead_lt` / `padRead_ge` | `:84` / `:88` | in-support read / blank tail |
| `contentHeader?` | `:111` | `decodeGamma? (padWord z (2 * N + 1)) tagLen` |
| `contentInput?` | `:123` | strict parser re-run on `padWord z (treeMCSPPrefixM codec n')` |
| `contentWitness` | `:135` | `codec.witnessBits n` cells at `treeMCSPPrefixM codec n` |
| **`ContentAccepts`** | **`:152`** | `∃ pr, contentInput? codec z = some pr ∧ pr.2.prefixAgrees … ∧ relation …` |
| `ContentPrefixExtendable` | `:165` | `∃ w, ContentAccepts codec (concatBitstring y w)` |
| `ContentPrefixExtensionLanguage` | `:172` | classical `Bool` wrapper of the above |
| `ContentPrefixExtensionLanguage_accepts_iff` | `:178` | wrapper unwrapping |
| **`ContentPrefixExtensionNPWitness`** | **`:211`** | `M`, `c`, `runTime_poly`, `correct` |
| `contentPrefixExtensionLanguage_in_NP_of_witness` | `:231` | witness ⇒ `NP L'` |

Downstream consumers already exist and are unconditional given the interface:
`ContentConsolidatedSource.lean:57` `verifiedSourceCT_of_noPolynomialBoundedSearchSolver`,
`:73` `verifiedSourceCT_treePoly`, `:86` `NP_not_subset_PpolyDAG_treePolyCT`. At the concrete
threshold those take exactly two explicit hypotheses: `NoPolynomialBoundedSearchSolver`
(input (1), untouched by this plan) and `ContentPrefixExtensionNPWitness` (input (2), the target).

Note the certificate exponent is **fixed to `k = 1`** by the interface: `ContentPrefixExtensionNPWitness`
has no `k` field (`contentPrefixExtensionLanguage_in_NP_of_witness` supplies the literal `1`), and
`certificateLength n 1 = n + 1` (`pnp3/Complexity/Interfaces.lean:521`). The length-gated
`PrefixExtensionNPWitness` (`PrefixExtensionNPWitness.lean:75`) does carry a `k`. Any slice that
needs a different certificate exponent is out of scope by construction.

### 1.2 Status of the length-gated target: retained, retirement deferred to FEAS-0

`PrefixExtensionNPWitness` (`PrefixExtensionNPWitness.lean:75`) and its chain
(`ExplicitConditionalSource.lean`, `ConcreteTreeCodecSource.lean`,
`ConsolidatedTreeSeparation.lean`) are **retained as a live target**. Retirement is *deferred*
until FEAS-0 is green, because the length gate is exactly what §1.0 shows the CT route has not yet
replaced. Concretely, while the freeze is provisional:

* **New slices should state their headline against `ContentAccepts` / `L'`** and are scheduled in
  §4 — but a slice against `PrefixExtensionLanguage` / `PrefixExtensionNPWitness` is **not**
  rejected on target grounds alone. The blanket rejection rule of the previous revision is
  withdrawn; it returns only when FEAS-0 lands as (a) or (b).
* **Audit compatibility is preserved regardless.** The length-gated modules keep compiling, keep
  their `#check` lines in `pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean` and their
  `#print axioms` lines in `pnp4/Pnp4/Tests/AxiomsAudit.lean`, and keep being cited by
  `AGENTS.md`'s "most concrete live form" paragraph. Removing or weakening them is **not** part of
  this plan under any FEAS-0 outcome.
* **Bridging lemmas are admissible in both directions** when they serve either route, e.g. the
  coincidence family `ContentPrefixExtensionCoincidence.lean:276`
  `ContentPrefixExtendable_iff_of_parse` / `:324` `ContentPrefixExtensionLanguage_eq_of_parse`.
  Under FEAS-0 outcome (c) the old → new direction is the one that survives.
* One CT-A artifact is **mis-targeted relative to the CT route** (slice P0): the semantic core
  `TreeMCSPPrefixSemanticVerifier.lean:252` `treePrefixSemanticAccepts_correct` is stated for
  `PrefixExtensionLanguage (treeMCSPConcretePrefixParser threshold codec)`, not for `L'`. P0 adds
  an `L'`-side counterpart; it does not remove or re-point the existing theorem.

### 1.3 What the freeze does **not** buy — target-validity caveats

These must be restated in every slice's module docstring; they are the honest boundary of the
provisionally frozen target.

1. **The `(★′)` bridge is the whole remaining machine obligation.** No verifier TM, no runtime
   bound, and no `TM.accepts … = ContentAccepts …` statement exists for `L'` anywhere in the
   repository.
2. **Padding invariance is proved for the predicate, not the language.**
   `ContentPrefixExtensionPadding.lean:314` `ContentAccepts_padWord_of_le` and `:333`
   `ContentAccepts_iff_of_padRead_eq` are about *complete* words. Membership in `L'` at physical
   length `m` quantifies over `Bitstring (certificateLength m 1)` concatenated at offset `m`, both
   of which move with `m`; wrapper-level invariance is unproved.
3. **The re-decode gate's vacuity is open only in its *value* tests, not its gamma decode.**
   Corrected in this revision: `consumed = gammaLen n'` is a **theorem**, not a hypothesis — a
   successful `decodeGammaAux?` returns `consumed = 2 * zeros + 1` with
   `n' + 1 = 2 ^ zeros + payload` and `payload < 2 ^ zeros`, so `bitLength (n' + 1) = zeros + 1`
   and `gammaLen n' = 2 * zeros + 1` (§4.3). Consequently the strict parser's
   `m = treeMCSPPrefixM codec n_dec` gate *is* unconditionally vacuous given a successful header
   decode, and every range/fit premise of the narrow-window parse discharges from the Layout offset
   lemmas. What remains open is exactly three **value** tests inside
   `parseTreeMCSPPrefixInput` (`PrefixParserConvention.lean:1130`): `tag = treePrefixTag`,
   `i ≤ codec.witnessBits n'`, and `padZero = true`. Those are sound rejections, not defects.
   (The previous revision asserted the opposite — that unconditional gate vacuity is false and
   canonicity must be assumed. Both statements were wrong.)
4. **Non-vacuity is unproved.** The only existential statement about `ContentAccepts`,
   `ContentPrefixExtensionPaddingTransport.lean:39` `ContentAccepts_padWord_of_prefixExtendable`, is
   conditional on `hparse`, `hn`, `hext`, `hT`, none discharged. This is what GATE-0 addresses.
5. **The obligation lives in this repository's machine model only.** `NP` is `NP_TM`
   (`pnp3/Complexity/Interfaces.lean:560`) over `Pnp3.Internal.PsubsetPpoly.TM`: deterministic
   single-tape, binary alphabet, no read-only input tape, tape length `n + runTime n + 1`
   (`TuringEncoding.lean:73`), `runTime : ℕ → ℕ` an unrestricted **structure field** (`:60`), and
   `TM.accepts` evaluated **at exactly step `runTime n`** (`:178`, `:183`) with no halting
   predicate. No cross-model runtime-robustness theorem is formalized.
6. **The unrestricted `runTime` field is a live model audit finding, and avoiding it is
   *unenforced*.** `pnp4/Pnp4/Frontier/ModelAudit/RuntimeAdviceBarrier.lean:77`
   `lengthAdviceLanguage_in_repo_P` proves that *every* `A : Nat → Bool`, with no computability
   hypothesis, yields a length-only language in this repository's `P`, via `lengthAdviceTM` (`:44`)
   whose zero-or-one-step runtime stores `A n`. Consequence for this plan: discharging
   `ContentPrefixExtensionNPWitness` establishes NP-membership *in a model whose `P` admits
   arbitrary length advice*. Corrected in this revision: **nothing in `ContentVerifierBridge`
   (§4.5) prevents a bridge instance from exploiting that channel.** `runTime_poly` bounds the
   clock's *magnitude*; it says nothing about how the clock is computed, so a machine whose
   `runTime` encodes advice can satisfy `accepts_eq` legitimately. G6 is therefore a **review
   convention, not a machine-checked gate**. Making it enforceable requires a formal clock
   premise — an added field constraining `M.runTime` to a named explicit arithmetic expression, or
   a repo-level amendment to `TM` making `runTime` uniform. Until such a premise is written down
   and cited here, do **not** describe the CT route as advice-free.
7. **Feasibility itself is open (§1.0).** No bound relates the physical length of an accepted
   complete word to the decoded convention length `treeMCSPPrefixM codec n'`, and the decoded value
   can be exponential in `N`. This is FEAS-0 and it gates the freeze.

---

## 2. Re-audit of `verifier-next-slices.md` against current `main`

The donor manifest was written at `main = 5d8ee5f8`. `main` is now `98250643`, **36 commits ahead**
(`git rev-list --count 5d8ee5f8..main = 36`), and those commits are precisely the work that changed
the retarget picture: `#1621` (AC0 audit), `#1622` (documentation-state audit), **`#1623` (CT-A)**,
**`#1624` (CT-B)**, **`#1625` (CT-C)**, **`#1626` (runtime advice)**.

### 2.1 Stale assumptions — corrected

| Donor claim | Verdict | Correction |
|---|---|---|
| §0 "`main` = `5d8ee5f8`" | **stale** | `main = 98250643`; `git rev-list --count pr1618..main = 36` (the merge base is still `5d8ee5f8`, so this equals `5d8ee5f8..main`). |
| §0 "`ContractExpansion/` has 39 files on main" | **stale** | 39 files on `5d8ee5f8`, **47** on `98250643` (`git ls-tree -r --name-only`). |
| §0 / §9 "Nothing on `main` is reusable"; "every module named below as a donor exists **only** in the PR stack" | **false** | Eight modules directly on the retarget path landed on `main` after the donor snapshot (§3.1). Six of them also exist, **divergently**, on `pr1618` (§3.2), so the PR stack is not a superset of `main`. |
| §0 "BASE for every slice: `4a8ee0c9`; do not branch from `main`" | **false for this plan** | Every slice in §4 is dependency-closed on `main = 98250643` and branches from it (§5). Branching from `4a8ee0c9` would *lose* the CT-A/B/C prerequisites. |
| §0 "`git diff --stat main...pr1618` = 184 files / +56544 / −2420 — the whole stack" | **arithmetically unchanged, semantically misleading** | The number is identical today only because `...` resolves to the merge base, which is still `5d8ee5f8`. It therefore describes the stack against a 36-commit-old `main`, and hides the rebase surface in §3.2. |
| §4 GATE-0 = "embedding-route spike (A′ vs B) on `clearIterProgram`" | **not this plan's GATE-0** | It gates donor slices P1…P4 / D3 inside `pr1618`. It has no bearing on any slice targeting `ContentAccepts`. Superseded by FEAS-0 (§1.0) and GATE-0 (§4.1). |
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
| `ContentPrefixExtensionPadding.lean` | 358 | `padRead_padWord_of_le` `:103`, `padWord_padWord_of_le` `:111`, `eq_padWord_of_padRead_eq` `:120`, `lt_of_padRead_eq_true` `:127`, `readBit?_padWord_of_lt/_of_ge` `:136`/`:143`, `readNatBE_padWord_transfer` `:151`, `decodeGammaAux?_padWord_support` `:186`, `decodeGammaAux?_padWord_canonical` `:223`, `contentHeader?_padWord_of_le` `:278`, `contentInput?_padWord_of_le` `:293`, `contentWitness_padWord_of_le` `:300`, `ContentAccepts_padWord_of_le` `:314`, `ContentAccepts_iff_of_padRead_eq` `:333`, `contentHeader?_of_decodeGamma` `:349` |
| `ContentPrefixExtensionPaddingTransport.lean` | 63 | `ContentAccepts_padWord_of_prefixExtendable` `:39` (the classical conditional existential) |
| `ContentPrefixExtensionTransfer.lean` | 155 | `DecidesContentPrefixExtensionLanguage` `:51`, `correctNextBitDecider_of_decidesContentLanguage` `:62`, `boundedSearchSolver_of_deciderFamilyCT` `:92`, `boundedSearchSolver_of_PpolyDAG_contentPrefixExtension` `:111`, `not_PpolyDAG_contentPrefixExtension_of_noExtractedScheduleSolver` `:132`, `_of_noPolynomialBoundedSearchSolver` `:145` |
| `ContentConsolidatedSource.lean` | 96 | the three consolidated CT sources, §1.1 |
| `TreeMCSPPrefixSemanticVerifier.lean` | 304 | `witnessBits_le_treeMCSPPrefixM` `:78`, `prefixAgreesBool` `:99` + `_eq_true_iff` `:105`, `instDecidableCodecVerifies` `:114` (local), `verifiesBool` `:121` + `_eq_true_iff` `:128`, `sliceBits?_zero` `:137`, `witnessBits_le_certificateLength` `:148`, `extractWitness?` `:160` + `extractWitness_eq` `:172`, `treePrefixSemanticAccepts` `:192`, `treePrefixSemanticAccepts_correct` `:252` (**mis-targeted, see §1.2**) |
| `TreeMCSPPrefixVerifierLayout.lean` | 274 | `prefixVerifierInputLen` `:33`, `prefixVerifierCertStart` `:44`, `concatBitstring_left/_right` `:72`/`:80`, `verifierTape_left/_right` `:103`/`:114`, `queryXOffset` `:136`, `queryIdxOffset` `:139`, `queryPrefixOffset` `:143`, `queryPrefixOffset_add_witnessBits` `:148`, `queryPrefixOffset_le` `:157`, `queryXOffset_le_treeMCSPPrefixM` `:166`, `queryIdxOffset_le_treeMCSPPrefixM` `:174`, `gammaLen_le_treeMCSPPrefixM` `:183`, `instanceSize_lt_treeMCSPPrefixM` `:194`, `gammaZeros` `:219`, `gammaTermOffset` `:223`, `gammaLen_eq_two_mul_gammaZeros_add_one` `:226`, `gammaTermOffset_lt_queryXOffset` `:239`, `gammaTermOffset_le_treeMCSPPrefixM` `:246`, `gammaMirror_mem` `:258` |

Plus the pre-existing foundation, unchanged since the donor snapshot and equally reusable:

* `PrefixParserConvention.lean` (1337 LOC) — `treePrefixTag` `:10`, `tagLen` `:13`, `bitLength`
  `:22`, `gammaLen` `:26`, `idxWidth` `:30`, `treeMCSPPrefixM` `:40`,
  `tableLen_le_treeMCSPPrefixM` `:48`, `readBit?` `:57`, `readNatBE` `:61`, `sliceBits?` `:70`,
  `allZeroSlice?` `:78`, `decodeGammaAux?` `:87`, `decodeGamma?` `:101`,
  `prefixLength_lt_two_pow_idxWidth` `:329`, `gammaLen_eq_zeros_add_bitLength` `:364`,
  `gammaLen_eq_two_mul_zeros_add_one` `:371`, `encodeTreeMCSPPrefixFields` `:631`,
  `encodeTreeMCSPPrefixFields_length_convention` `:659`,
  `CanonicalRawTreeMCSPPrefixFields.toPrefixInput` `:675`, `parseTreeMCSPPrefixInput` `:1130`,
  `parse_encodeTreeMCSPPrefixFields` `:1184`, `treeMCSPConcretePrefixParser` `:1203`,
  `parseTreeMCSPPrefixInput_length_convention` `:1231`.
* `PrefixExtensionLanguage.lean` — `PrefixBitVec` `:10`, `PrefixInput` `:31`,
  `PrefixInput.prefixAgrees` `:52`, `PrefixExtendableInput` `:100`, `PrefixExtendable` `:108`,
  `PrefixExtensionLanguage` `:124`, `PrefixExtensionLanguage_accepts_iff` `:131`.
* `PrefixExtensionLanguageNP.lean` — `TreeCircuitWitnessCodec.verifiesDecidable` `:92`. **P0 depends
  on this module** (via `verifiesBool`); it was missing from the previous revision's inventory, and
  its axiom footprint is what makes §4.2's G2 expectation nontrivial.
* `TreeMCSPPrefixSerializer.lean` — `zeroPrefixFields` `:42` (sets `i := 0` at `:49`),
  `zeroPrefixQueryValue` `:57`, `parse_zeroPrefixQueryValue` `:68`, `zeroPrefixQueryValue_parses`
  `:84`.
* `ConcreteTreeCodec.lean` — `treeSelfDelimitingCode` `:53` (`witnessBits n = (bitLength n + 4) * threshold n`,
  `:54`), `treeCircuitWitnessCodec` `:67`,
  `polyBoundedInTable_treeWitnessBits_of_thresholdPoly` `:78`.
* `ThresholdGrowth.lean` — `thresholdPoly` `:36` (`= n ^ k + k`).
* `pnp4/Pnp4/Frontier/SearchMCSPConcreteTargets.lean` — `TreeCircuitWitnessCodec` `:44`
  (`witnessBits : Nat → Nat` at `:46`, **unconstrained** — see §4.3), `.verifies` `:61`, `.sound`
  `:73`, `.complete` `:85`, `TreeMCSPSearchWitnessEncoding.ofCodec` `:98`, `treeMCSPSearchProblem`
  `:114`.
* `pnp4/Pnp4/AlgorithmsToLowerBounds/TruthTableMCSP.lean` — `TruthTable` `:11`, `treeCircuitClass`
  `:22`, `truthTableFunction` `:28`, `ComputesTruthTable` `:35`, `circuitComplexityLE` `:50`,
  `treeMCSPPredicate` `:87`.
* `pnp3/Models/Model_PartialMCSP.lean` — `Circuit` `:42`, `Circuit.size` `:51`
  (`Circuit.const _ => 1` at `:53`), `Circuit.eval` `:59`.
* `pnp3/Complexity/Interfaces.lean` — `certificateLength` `:521`, `concatBitstring` `:528`,
  `NP_TM` `:560`, `NP` `:580`.
* `pnp3/Complexity/PsubsetPpolyInternal/TuringEncoding.lean` — `TM` `:45`, `runTime` `:60`,
  `tapeLength` `:73`, `initialConfig` `:133`, `initial_tape_input` `:140`,
  `initial_tape_blank` `:146`, `run` `:178`, `accepts` `:183`.
* `pnp4/Pnp4/Frontier/ModelAudit/RuntimeAdviceBarrier.lean` — `lengthAdviceLanguage` `:37`,
  `lengthAdviceTM` `:44`, `lengthAdviceTM_runTime_le_one` `:54`, `lengthAdviceTM_accepts` `:60`,
  `lengthAdviceLanguage_in_repo_P` `:77`.

### 3.2 Donor-only (`pr1618 = 4a8ee0c9`) — and the overlap that is *not* clean

`ContractExpansion/` has **216** files on `pr1618` versus 47 on `main`; **183** of them are
`TreeMCSP*` machine modules (region-embedding toolkit, arm programs, arm runs, corridor invariants,
driver interface, transcoder capstone). None of these exist on `main`.

But six modules exist on **both**, with different contents — so `pr1618` is not a superset and a
rebase is not a fast-forward. **Sizes in bytes throughout** (`git cat-file -s`):

| Module | `pr1618` (bytes) | `main` (bytes) |
|---|---|---|
| `ContentPrefixExtension.lean` | 9 513 | **15 015** |
| `ContentPrefixExtensionCoincidence.lean` | 14 991 | **16 531** |
| `ContentPrefixExtensionTransfer.lean` | 7 387 | **8 761** |
| `ContentConsolidatedSource.lean` | 3 856 | **5 580** |
| `TreeMCSPPrefixSemanticVerifier.lean` | **15 858** | 14 166 |
| `TreeMCSPPrefixVerifierLayout.lean` | 12 967 | **14 231** |
| `ContentPrefixExtensionPadding.lean` | *absent* | **20 417** |
| `ContentPrefixExtensionPaddingTransport.lean` | *absent* | **2 960** |

`main` is ahead on the CT chain (CT-C exists only on `main`); `pr1618` is ahead only on
`TreeMCSPPrefixSemanticVerifier.lean`. Any future rebase of the stack must reconcile these six
files plus `lakefile.lean`, `AlgorithmsToLowerBoundsSurfaceTests.lean` and `AxiomsAudit.lean`.

### 3.3 Disposition of the donor stack: parked, not cancelled

`pr1526` / `pr1616` / `pr1618` are **parked**. No slice in this plan branches from them, imports
from them, or is blocked by them. They are not reviewed, rebased, or merged as part of the retarget.
Reactivation is a separate decision, and its first step is the six-file reconciliation of §3.2 —
not the donor's GATE-0.

### 3.4 Why the donor machine stack does not discharge input (2) — insufficient, but reusable

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

So even a completed donor driver instance would leave the `(★′)` bridge open.

**But it is not dead weight.** Corrected in this revision: witness-decoding — turning a certificate
block into an object whose `Circuit.eval` can be checked — is a genuine sub-obligation of *any*
verifier for `L'`, and `transcodeWitness` plus the region-embedding toolkit is the only machinery in
the repository that attacks it. The accurate statement is **insufficient but potentially reusable**:
the donor stack supplies at most the witness-decoding component, and the five bullets above must be
scheduled separately.

**Corollary for sequencing:** finishing the donor arms is not on the critical path to input (2), and
the donor manifest's estimate of "5 slices / ~3100–4400 LOC to the pop arm" buys nothing against the
`(★′)` bridge by itself. Any future revival must be justified as *witness-decoding reuse*, scoped to
that component, and must not be described as progress on the bridge.

---

## 4. FEAS-0, GATE-0 and the first slices

All items below are **dependency-closed on `main = 98250643`**: every donor lemma they cite is in
§3.1, none is on `pr1618`.

**Sequencing.** FEAS-0 (§1.0) is the *only* item that may start while the freeze is provisional.
GATE-0, P0, I1, D1a and D1b are **all conditional on FEAS-0 landing as (a) or (b)**; under outcome
(c) they are void and §1.1 is rewritten first. Once FEAS-0 is green, GATE-0, P0, I1 and D1a are
mutually independent and may run in parallel, and D1b follows P0.

Every slice obeys: **≤ 1500 changed `.lean` LOC (added + deleted) and ≤ 10 changed `.lean` modules**
(§6). Every new module carries the Infrastructure classification line and the
"**No `P ≠ NP` claim**" sentence, plus caveats 1–7 of §1.3 as applicable.

### 4.1 GATE-0 — non-vacuity of `ContentAccepts` at the concrete codec · **blocking for D-track, not for P0/I1**

**Why this is a gate.** Nothing proves that any word is `ContentAccepts`-accepted (§1.3, caveat 4).
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

/-- Concrete discharge: the all-false table on `n` variables is computed by `Circuit.const false`,
of size `1`.  (The binder `n` is used: it fixes the instance the witness is built at.) -/
theorem contentAccepts_nonvacuous_treePoly (k n : Nat) :
    ∃ z : PrefixBitVec
            (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n
              + Pnp3.ComplexityInterfaces.certificateLength
                  (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n) 1),
      ContentAccepts (treeCircuitWitnessCodec (thresholdPoly k)) z
```

The third signature is corrected in this revision: the previous form
`∃ (N : Nat) (z : PrefixBitVec N), …` left `n` an unused binder, so the statement was weaker than
its docstring and would draw an unused-variable lint. Pinning `z`'s length to the concatenated
zero-prefix shape makes `n` load-bearing.

**Proof route, fully on `main`.**
`zeroPrefixQueryValue_parses` (`TreeMCSPPrefixSerializer.lean:84`) supplies *both* hypotheses that
`contentInput?_concat_of_parse` (`Coincidence.lean:244`) needs — `hparse` **and**
`hn : input.n = n`. `prefixAgrees` is vacuous because `zeroPrefixFields` sets `i := 0`
(`TreeMCSPPrefixSerializer.lean:49`), `toPrefixInput` copies it verbatim
(`PrefixParserConvention.lean:675`), and `PrefixInput.prefixAgrees` is a `∀ k : Fin input.i`
(`PrefixExtensionLanguage.lean:52`). The relation conjunct comes from
`TreeCircuitWitnessCodec.complete` (`SearchMCSPConcreteTargets.lean:85`), with the witness
transported into the certificate's leading `witnessBits` block by
`contentWitness_concat` (`Coincidence.lean:218`). The concrete discharge takes
`c := Pnp3.Models.Circuit.const false` (size `1`, `pnp3/Models/Model_PartialMCSP.lean:53`) against
`x := fun _ => false`, and `1 ≤ thresholdPoly k n = n ^ k + k` for every `k, n` (at `k = 0` the
first summand is `n ^ 0 = 1`; at `k ≥ 1` the second summand suffices).

**Budget:** 200–350 LOC · 1 module. **Exit:** all three theorems green with the standard axiom
triple, `#check`/`#print axioms` lines added.
**Stop/go (G0):** if the third theorem cannot be discharged — i.e. if satisfiability of
`ContentAccepts` at `treeCircuitWitnessCodec (thresholdPoly k)` resists a *concrete* witness —
**halt the D-track and escalate.** Do not begin machine work against a predicate not known to be
satisfiable. P0 and I1 remain admissible either way, since both are statements *about* the predicate
rather than claims that it holds.

### 4.2 P0 — content-side semantic verifier and its correctness · *parallel-safe once FEAS-0 is green*

**Why.** CT-A's semantic core is stated against the length-gated language (§1.2), and its signature
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

/-- **The `L'`-side counterpart of `treePrefixSemanticAccepts_correct`.** -/
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
**Stop/go (G2) — corrected in this revision.** The previous revision demanded that "the four
non-wrapper theorems avoid `Classical.choice` in `#print axioms`". That is **false and
unachievable**: `verifiesBool` resolves `Decidable (codec.verifies …)` through the local instance
`instDecidableCodecVerifies` (`TreeMCSPPrefixSemanticVerifier.lean:114`) to
`TreeCircuitWitnessCodec.verifiesDecidable` (`PrefixExtensionLanguageNP.lean:92`), which carries
`Classical.choice` — as `pnp4/Pnp4/Tests/AxiomsAudit.lean:479–483` already records for CT-A's own
`verifiesBool_eq_true_iff`. Correct expectations:

* `contentSemanticAccepts_padWord_of_le` — arithmetic/padding only; **may** be
  `[propext, Quot.sound]`, matching `ContentPrefixExtensionPadding.lean`'s Classical-free family.
  Do not force this if the definition routes through `verifiesBool`.
* `contentSemanticAccepts_eq_true_iff`, `contentSemanticAccepts_eq_false_of_contentInput_none`,
  `contentSemanticAccepts_correct` — **expect the standard triple**
  `[propext, Classical.choice, Quot.sound]`, inherited from `verifiesDecidable` and (for the last)
  the classical language wrapper and noncomputable `concatBitstring`.
* A fourth axiom is still a blocker (G9).

Computability is a **separate** property from the axiom footprint and must be checked separately:
`contentSemanticAccepts` must be a plain `def` with no `noncomputable` marker, its `Decidable`
instances must resolve to `Fintype.decidableForallFintype` and
`TreeCircuitWitnessCodec.verifiesDecidable` rather than `Classical.propDecidable`, and the slice
must exhibit one `#eval` (or `decide`) on a small concrete word in the surface-test file. `#print
axioms` cannot detect a `Classical.propDecidable` substitution here, because the honest route
already carries `Classical.choice`.

### 4.3 I1 — close the residual gate premises · *parallel-safe once FEAS-0 is green*

**Why.** Two families of side conditions currently infect every coincidence statement and would
infect the machine's correctness proof:

* `hn : input.n = n` in `ContentPrefixExtendable_iff_of_parse` (`Coincidence.lean:276`) and
  `ContentPrefixExtensionLanguage_eq_of_parse` (`:324`). Inversion
  (`parseTreeMCSPPrefixInput_inversion`, `:140`) yields only
  `treeMCSPPrefixM codec input.n = treeMCSPPrefixM codec n`; injectivity of `treeMCSPPrefixM codec`
  is not proved (docstring at `:319–:323`).
* The narrowing direction of the gamma decode, and the enumeration of what actually remains after
  it (§1.3, caveat 3).

**Edited/new modules:** new `ContentPrefixExtensionGateClosure.lean`; no edit to
`Coincidence.lean` in this slice (the `hn`-free corollaries are stated in the new module, so the
existing surface and its audit lines stay untouched).

#### 4.3.1 Injectivity: the generic goal is **false** — specialize it

The previous revision proposed
`treeMCSPPrefixM_injective (codec : TreeCircuitWitnessCodec threshold) : Function.Injective (treeMCSPPrefixM codec)`
and justified it by "`tableLen_le_treeMCSPPrefixM` plus `Nat.lt_two_pow_self` give strict
monotonicity". **Both the goal and the route are wrong.**

* `treeMCSPPrefixM codec n = tagLen + gammaLen n + tableLen n + idxWidth codec.witnessBits n + codec.witnessBits n`
  (`PrefixParserConvention.lean:40`), and `TreeCircuitWitnessCodec.witnessBits : Nat → Nat`
  (`SearchMCSPConcreteTargets.lean:46`) is **unconstrained**: only `decode_encode` touches it, and
  it bounds `witnessBits` from *below*. A codec may pad `witnessBits` upward by any amount at any
  single `n` (the extra bits are simply ignored by `decode`). Since
  `k ↦ k + bitLength k` advances by 1 or 2 per step, `witnessBits` can be inflated at `0` and at `1`
  until `treeMCSPPrefixM codec 0 = treeMCSPPrefixM codec 1`. So injectivity **fails for some legal
  codec**, and no proof can exist.
* `tableLen_le_treeMCSPPrefixM` (`:48`) gives `2 ^ n ≤ treeMCSPPrefixM codec n` — a *lower* bound.
  Strict monotonicity needs an *upper* bound on `treeMCSPPrefixM codec n`, which does not exist
  without constraining `witnessBits`. `instanceSize_lt_treeMCSPPrefixM`
  (`TreeMCSPPrefixVerifierLayout.lean:194`) proves `n < treeMCSPPrefixM codec n`, not monotonicity,
  so it is not a model for this argument.

Replace with the specialized forms, both true:

```lean
/-- Under monotone witness width, `treeMCSPPrefixM codec` is strictly monotone: `tagLen` is
constant, `gammaLen`, `idxWidth codec.witnessBits` and `codec.witnessBits` are monotone, and
`tableLen n = 2 ^ n` is strictly monotone. -/
theorem treeMCSPPrefixM_strictMono {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (hmono : Monotone codec.witnessBits) :
    StrictMono (treeMCSPPrefixM codec)

theorem treeMCSPPrefixM_injective_of_monotone {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (hmono : Monotone codec.witnessBits) :
    Function.Injective (treeMCSPPrefixM codec)

/-- The concrete codec qualifies: `witnessBits n = (bitLength n + 4) * thresholdPoly k n`. -/
theorem witnessBits_monotone_treePoly (k : Nat) :
    Monotone (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits

theorem treeMCSPPrefixM_injective_treePoly (k : Nat) :
    Function.Injective (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)))

/-- **`hn` eliminated, under the monotonicity premise.** -/
theorem ContentPrefixExtendable_iff_of_parse' {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (hmono : Monotone codec.witnessBits)
    {n : Nat} (y : PrefixBitVec (treeMCSPPrefixM codec n))
    (input : PrefixInput
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec))
      (treeMCSPPrefixM codec n))
    (hparse : parseTreeMCSPPrefixInput threshold codec y = some input) :
    ContentPrefixExtendable codec y
      ↔ PrefixExtendable (treeMCSPConcretePrefixParser threshold codec) y
```

`hmono` replaces `hn`, and every downstream consumer at the concrete threshold discharges it once
via `witnessBits_monotone_treePoly`. Monotonicity of `bitLength` (`PrefixParserConvention.lean:22`,
`if n = 0 then 0 else Nat.log2 n + 1`) and of `n ^ k + k` are the two arithmetic sublemmas.

#### 4.3.2 Gamma canonicity is a **theorem**, and the length gate is unconditionally vacuous

The previous revision carried `hcanon : consumed = gammaLen n'` as a hypothesis and declared
unconditional gate vacuity "false as stated". Corrected: canonicity is forced by a successful
decode.

```lean
/-- A field read of `width` bits is bounded by `2 ^ width`.  (No general bound exists on `main`;
`prefixLength_lt_two_pow_idxWidth` (`PrefixParserConvention.lean:329`) is a different statement.) -/
theorem readNatBE_lt_two_pow {m : Nat} (y : PrefixBitVec m) (offset width : Nat)
    {v : Nat} (h : readNatBE y offset width = some v) :
    v < 2 ^ width

/-- **Canonicity from a successful decode.**  `decodeGammaAux?` terminates at the first `true` bit,
returning `consumed = 2 * zeros + 1` and `n' + 1 = 2 ^ zeros + payload` with `payload < 2 ^ zeros`;
hence `bitLength (n' + 1) = zeros + 1` and `consumed = gammaLen n'`. -/
theorem decodeGamma?_consumed_eq_gammaLen {m : Nat} (y : PrefixBitVec m)
    {offset n' consumed : Nat}
    (h : decodeGamma? y offset = some (n', consumed)) :
    consumed = gammaLen n'

theorem contentHeader?_consumed_eq_gammaLen {N : Nat} (z : PrefixBitVec N)
    {n' consumed : Nat} (hheader : contentHeader? z = some (n', consumed)) :
    consumed = gammaLen n'

/-- **Narrowing, unconditional.**  A successful content-header decode re-succeeds, with the same
target, on the narrow window `padWord z (treeMCSPPrefixM codec n')`. -/
theorem decodeGamma?_padWord_narrow {N : Nat} (z : PrefixBitVec N)
    {threshold : Nat → Nat} (codec : TreeCircuitWitnessCodec threshold)
    {n' consumed : Nat}
    (hheader : contentHeader? z = some (n', consumed)) :
    decodeGamma? (padWord z (treeMCSPPrefixM codec n')) tagLen = some (n', consumed)

/-- **The length gate never fires.**  The strict parser's re-decode on the narrow window returns
`n'` itself, so its `m = treeMCSPPrefixM codec n_dec` test compares `treeMCSPPrefixM codec n'`
with itself and the `_hlen` branch is always taken. -/
theorem contentInput?_lengthGate_vacuous {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {N : Nat} (z : PrefixBitVec N)
    {n' consumed n_dec consumed_dec : Nat}
    (hheader : contentHeader? z = some (n', consumed))
    (hnarrow : decodeGamma? (padWord z (treeMCSPPrefixM codec n')) tagLen
                 = some (n_dec, consumed_dec)) :
    n_dec = n' ∧ treeMCSPPrefixM codec n' = treeMCSPPrefixM codec n_dec
```

**Proof route, fully on `main`.** Canonicity: `readNatBE_lt_two_pow` (new, by induction on `width`
over the `readNatBE` recursion, `PrefixParserConvention.lean:89`) plus
`gammaLen_eq_two_mul_zeros_add_one` (`:371`) and `bitLength` (`:22`).
Narrowing: a successful header decode puts the terminator strictly inside the support
(`padRead_ge`, `ContentPrefixExtension.lean:88`, so `tagLen + zeros < N`), and
`decodeGammaAux?_padWord_support` (`Padding.lean:186`) plus `readNatBE_padWord_transfer` (`:151`)
move both the terminator search and the payload read to the narrow window. The width side condition
is `queryXOffset_le_treeMCSPPrefixM` (`TreeMCSPPrefixVerifierLayout.lean:166`) combined with
`gammaLen_eq_two_mul_gammaZeros_add_one` (`:226`), i.e.
`tagLen + 2 · gammaZeros n' + 1 ≤ treeMCSPPrefixM codec n'`, which is now available *because*
`consumed = gammaLen n'` is a theorem rather than an assumption. Both windows agree on every read
cell: all read positions are `< tagLen + gammaLen n' ≤ 2 * N + 1`, and cells in `[N, ·)` are blank
in both. The existing `decodeGammaAux?_padWord_canonical` (`Padding.lean:223`) cannot be reused: it
requires `2 * N + 1 ≤ T'`, i.e. widening, and here `T' = treeMCSPPrefixM codec n'` may be smaller.

#### 4.3.3 Every remaining parser premise, enumerated

`parseTreeMCSPPrefixInput` (`PrefixParserConvention.lean:1130`) has **eleven** exit points, not
"four field reads". On the narrow window `padWord z (treeMCSPPrefixM codec n')`, given
`contentHeader? z = some (n', consumed)`, they split cleanly:

**Automatic (discharged by §3.1 lemmas — a slice must prove these, not assume them):**

| # | Premise | Discharged by |
|---|---|---|
| 1 | `readNatBE y 0 tagLen` succeeds | `TreeMCSPPrefixVerifierLayout.lean:183` `gammaLen_le_treeMCSPPrefixM` (`tagLen ≤ M n'`) |
| 2 | `decodeGamma? y tagLen` succeeds, returns `(n', consumed)` | `decodeGamma?_padWord_narrow` (§4.3.2) |
| 3 | length gate `m = treeMCSPPrefixM codec n_dec` | `contentInput?_lengthGate_vacuous` (§4.3.2) |
| 4 | `sliceBits? y xOffset (tableLen n')` succeeds | `TreeMCSPPrefixVerifierLayout.lean:174` `queryIdxOffset_le_treeMCSPPrefixM` |
| 5 | `readNatBE y iOffset (idxWidth codec.witnessBits n')` succeeds | `TreeMCSPPrefixVerifierLayout.lean:157` `queryPrefixOffset_le` |
| 6 | `sliceBits? y pOffset i` succeeds | `TreeMCSPPrefixVerifierLayout.lean:148` `queryPrefixOffset_add_witnessBits`, given #10 |
| 7 | `sliceBits? y padOffset (codec.witnessBits n' - i)` succeeds | `TreeMCSPPrefixVerifierLayout.lean:148` `queryPrefixOffset_add_witnessBits`, given #10 |
| 8 | `allZeroSlice? y padOffset (…)` succeeds | same range argument as #7 |

**Not automatic — three genuine *value* tests, and the honest residue:**

| # | Premise | Status |
|---|---|---|
| 9 | `tag = treePrefixTag` | open; `contentHeader?` never reads the tag, so a word with a valid gamma and a wrong tag is legitimately rejected |
| 10 | `i ≤ codec.witnessBits n'` | open; `i` is read off the tape and may exceed the witness width |
| 11 | `padZero = true` | open; the inactive suffix must be all-zero |

So the honest closure statement is a characterisation, not a vacuity claim:

```lean
/-- Given a successful content-header decode, `contentInput?` succeeds **iff** the three value tests
pass; every range/fit premise and the length gate discharge unconditionally. -/
theorem contentInput?_isSome_iff_of_header {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {N : Nat} (z : PrefixBitVec N)
    {n' consumed : Nat}
    (hheader : contentHeader? z = some (n', consumed)) :
    (contentInput? codec z).isSome
      ↔ (<#9 tag test> ∧ <#10 index bound> ∧ <#11 pad-zero test>
           at the canonical offsets of `padWord z (treeMCSPPrefixM codec n')`)
```

**The three value tests are load-bearing and must not be dropped.** A slice claiming that
`contentInput?` *never* returns `none` is wrong and must be rejected: words failing #9/#10/#11 are
simply not in `L'`, which is sound behaviour.

**Budget:** 500–800 LOC · 2–3 modules (split at §4.3.1 / §4.3.2+§4.3.3 if the size gate binds).
**Stop/go (G3):** state injectivity **only** in the two specialized forms of §4.3.1. A slice that
re-proposes the generic `Function.Injective (treeMCSPPrefixM codec)` must be rejected as false, not
merely unproved. Do **not** work around it by strengthening `PrefixInput`.
**Stop/go (G4):** `decodeGamma?_consumed_eq_gammaLen` must be **hypothesis-free** beyond the
successful decode. If canonicity needs an extra premise, the `readNatBE` payload bound is wrong —
fix `readNatBE_lt_two_pow`, not the statement.
**Stop/go (G4b):** `contentInput?_isSome_iff_of_header` must enumerate exactly premises #9–#11 on
its open side. Adding a fourth open premise means a range lemma was missed; folding one away means
the parser was mis-read.

### 4.4 D1a — the machine-facing tape lemmas and the bridge structure · *independent, parallel-safe once FEAS-0 is green*

**Why.** The `(★′)` bridge `TM.accepts (M := M) (concatBitstring x w) = contentSemanticAccepts …`
compares two objects that are currently stated over different data: `TM.accepts` reads a
`Configuration` tape of length `TM.tapeLength n = n + runTime n + 1`
(`TuringEncoding.lean:73`), while `ContentAccepts` reads `padRead` of a finite word. Identifying the
two is a theorem, not a definition, and it is the exact point where caveat 6 becomes visible.

CT-A's layout module is the donor but is **not sufficient on its own**: `verifierTape_left` (`:103`)
and `verifierTape_right` (`:114`) read the start tape in the two `concatBitstring` ranges, and every
offset lemma (`:136`–`:258`, ending at `gammaMirror_mem`) is stated against the *length-gated* query
block `treeMCSPPrefixM codec n`, not against the content-computed window.

**New module:** `ContentVerifierTapeInterface.lean`.

**Exact outputs — none of these depend on P0.**

```lean
/-- **The start tape is the blank-padded complete word.**  For every in-range cell, the
`initialConfig` tape of the concatenated input equals `padRead` of that word — including past the
support, where both are the blank `false`. -/
theorem initialConfig_tape_eq_padRead
    (M : Pnp3.Internal.PsubsetPpoly.TM.{0}) {n m : Nat}
    (x : Pnp3.ComplexityInterfaces.Bitstring n)
    (w : Pnp3.ComplexityInterfaces.Bitstring m)
    (j : Fin (M.tapeLength (n + m))) :
    (M.initialConfig (Pnp3.ComplexityInterfaces.concatBitstring x w)).tape j
      = padRead (Pnp3.ComplexityInterfaces.concatBitstring x w) (j : Nat)

/-- **Tape-determined acceptance.**  Any two complete words with the same blank-padded tape are
`ContentAccepts`-equivalent — the machine-facing form of `ContentAccepts_iff_of_padRead_eq`. -/
theorem contentAccepts_of_initialConfig_tape_eq {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {N N' : Nat}
    (z : PrefixBitVec N) (z' : PrefixBitVec N')
    (h : ∀ j, padRead z j = padRead z' j) :
    ContentAccepts codec z ↔ ContentAccepts codec z'

/-- **The exact-step obligation, named.**  The bridge a verifier machine must discharge, with the
evaluation point spelled out as `runTime` rather than left implicit.  See §1.3 caveat 6: this
structure does **not** exclude a machine whose `runTime` carries length advice. -/
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
```

`accepts_eq` mentions `contentSemanticAccepts`, so the *structure* is stated after P0's definition
lands; if D1a runs first, declare it against a section variable
`(acc : ∀ {N : Nat}, PrefixBitVec N → Bool)` and specialize in D1b. Either way the three outputs
above carry no P0 *proof* dependency.

**Proof route.** The first theorem is read off `initialConfig`
(`pnp3/Complexity/PsubsetPpolyInternal/TuringEncoding.lean:133`, with `initial_tape_input` `:140`
and `initial_tape_blank` `:146`) — modelled line-for-line on `verifierTape_left` /
`verifierTape_right` (`TreeMCSPPrefixVerifierLayout.lean:103`, `:114`), with `padRead_ge`
(`ContentPrefixExtension.lean:88`) covering the blank tail. The second is
`ContentAccepts_iff_of_padRead_eq` (`Padding.lean:333`) restated for machine consumers.

**Budget:** 250–400 LOC · 1–2 modules.
**Stop/go (G5):** `ContentVerifierBridge.accepts_eq` must be stated with the concatenated length
`n + certificateLength n 1` and no "within `t` steps" quantifier. If a slice introduces a
step-bounded or halting-based variant it has silently changed the machine model — reject it.

### 4.5 D1b — the witness repackaging · **depends on P0**

Split out from D1a in this revision: the previous revision buried a cross-slice dependency in a
"dependency note" while listing the declaration among D1's outputs, which made the slice's
independence claim wrong.

**Module:** appended to `ContentVerifierTapeInterface.lean`, or `ContentVerifierBridgeWitness.lean`
if the size gate binds.

```lean
/-- **The bridge discharges the frozen target.**  `(★′)` plus P0's correctness theorem *is* the
NP-witness — the only remaining input is a machine satisfying `ContentVerifierBridge`. -/
def contentPrefixExtensionNPWitness_of_bridge {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (B : ContentVerifierBridge codec) :
    ContentPrefixExtensionNPWitness codec
```

**Proof route.** A one-line repackaging: `M := B.M`, `c := B.c`, `runTime_poly := B.runTime_poly`
verbatim, and `correct` obtained by rewriting `TM.accepts` to `contentSemanticAccepts` via
`B.accepts_eq` and then applying P0's `contentSemanticAccepts_correct` (§4.2), whose shape matches
the `correct` field of `ContentPrefixExtensionNPWitness` (`ContentPrefixExtension.lean:211`)
exactly at `k = 1`.

**Budget:** 60–120 LOC · 1 module.
**Stop/go (G6) — a review convention, not a machine-checked gate (§1.3 caveat 6).**
`contentPrefixExtensionNPWitness_of_bridge` must consume `runTime_poly` verbatim; if it needs to
*construct* a runtime bound, the bridge structure is under-specified. Reviewers should also refuse a
bridge instance that makes `accepts_eq` easy by hiding work in the clock — that is the advice
channel `lengthAdviceLanguage_in_repo_P` (`RuntimeAdviceBarrier.lean:77`) exhibits. **But note this
is unenforceable as written:** `runTime_poly` constrains the clock's magnitude only, so no theorem
in this slice rules such an instance out. Treat G6 as unenforced until a formal clock premise is
added to `ContentVerifierBridge` and cited in §1.3 caveat 6.

### 4.6 Dependency graph and parallelism

```text
FEAS-0  ──────────────────────────────── the only item admissible today
   │  (a) or (b) green ⇒ freeze promoted, everything below unlocks
   │  (c)          ⇒ all of the below is void; rewrite §1.1 first
   ▼
GATE-0  ─┐
P0      ─┼─ mutually independent, start all four after FEAS-0
I1      ─┤
D1a     ─┘

P0        → D1b = contentPrefixExtensionNPWitness_of_bridge
GATE-0    → any D-track slice past D1a  (do not build a machine for a possibly-vacuous predicate)
I1        → hn-free coincidence consumers  (quality-of-life, blocks nothing in this batch)
{P0, D1a} → the machine construction slices (out of scope here; a separate plan revision)
```

**Shared-file conflict surface — serialize the append or reserve a per-slice block:**

* `lakefile.lean` — the `lean_lib Pnp4` `Glob.one` list. Every slice touches it (AGENTS.md).
* `pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean` — add to the
  `ContentPrefixExtensionSurface` section; FEAS-0, GATE-0 and P0 all append there.
* `pnp4/Pnp4/Tests/AxiomsAudit.lean` — one `#print axioms` line per new public theorem.
* `pnp4/Pnp4/Frontier/ContractExpansion/README.md` — the CT module list, and the "Plan of record
  for input (2)" paragraph, which must track §1.2's provisional status.
* This file — §1.2, §7 log.

Assign each slice a contiguous reserved block in the three shared files at kickoff; conflicts then
resolve as adjacent-line merges.

### 4.7 Rejected slice proposals

* **"Rebase `pr1618` onto `main`"** as a retarget slice — §3.2/§3.4: it is a 184-file, six-way
  reconciliation that does not advance the frozen target.
* **"Finish `popIter_run_*` / `inputIter_run_full` / the driver instance"** — donor-only,
  transcoder-side, off the critical path. Admissible later only as scoped witness-decoding reuse
  (§3.4), never as bridge progress.
* **"Port `extractWitness?` to the content side"** — dead weight: `contentWitness` is total
  (§4.2).
* **"Retarget the layout offsets to the content window"** as a standalone slice — pure layout,
  rejected by the no-layout-only rule. Folded into D1a, which carries
  `initialConfig_tape_eq_padRead`.
* **"Prove wrapper-level padding invariance of `L'`"** — not obviously true (the certificate length
  and concatenation offset both move with `m`, §1.3 caveat 2) and not needed by any slice here.
  Out of scope until a slice demonstrably needs it.
* **"Delete or deprecate the length-gated chain"** — forbidden by §1.2 under every FEAS-0 outcome.
* **"Prove `Function.Injective (treeMCSPPrefixM codec)` for a generic codec"** — **false**
  (§4.3.1).
* **"Assume `consumed = gammaLen n'` as a hypothesis"** — unnecessary: it is a theorem (§4.3.2).
* **"Prove `contentInput?` never returns `none`"** — false: premises #9–#11 of §4.3.3 are genuine
  rejections.
* **"Freeze the target unconditionally / retire `PrefixExtensionNPWitness` now"** — premature until
  FEAS-0 (§1.0, §1.2).

---

## 5. Branch and base strategy

```bash
# Base every slice on main, NOT on 4a8ee0c9.
git fetch origin
git checkout -b work/<slice-name> 98250643      # or the then-current main
```

* **Base:** `main` (`98250643` at time of writing). One branch per slice, one PR per branch,
  PR base `main`. No stacking: the slices after FEAS-0 are independent, so stacking would only
  serialize review. D1b is the one exception and may stack on P0.
* **Naming:** `work/ct-<letter><number>-<topic>`, matching the CT-A/B/C precedent
  (`work/ct-a-verifier-prereqs`, `work/ct-b-source-chain`, `work/ct-c-padding-stability`).
  So: `work/ct-feas0-target-size-bound`, `work/ct-gate0-nonvacuity`,
  `work/ct-p0-content-semantic-verifier`, `work/ct-i1-gate-closure`,
  `work/ct-d1a-tape-interface`, `work/ct-d1b-bridge-witness`.
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

Note on step 6: a Classical-free theorem prints a *shorter* axiom list, which this filter also
surfaces. That is expected for the arithmetic/padding families (§4.2, G2) and is not a defect —
inspect, do not "fix".

### 6.3 Mandatory per AGENTS.md, every slice

* new module registered in `lakefile.lean`;
* every new public theorem `#check`ed in
  `pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean` (`ContentPrefixExtensionSurface`);
* every new audited surface `#print axioms`-ed in `pnp4/Pnp4/Tests/AxiomsAudit.lean`;
* no `axiom` / `sorry` / `admit` / `native_decide`;
* module docstring states **Infrastructure** and "**No `P ≠ NP` claim**", and reproduces the
  applicable caveats from §1.3 — including caveat 7 (feasibility) while the freeze is provisional.

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

**Scope discipline for reviewers.** Reject a slice that (i) claims the target is unconditionally
frozen, or retires the length-gated chain, before FEAS-0 lands as (a) or (b) (§1.0, §1.2);
(ii) claims any machine-side consequence from a specification-side lemma; (iii) describes the CT
route as removing length-dependence from the machine (`runTime_poly` is still taken at
`n + certificateLength n 1`) or as advice-free (§1.3 caveat 6); (iv) describes the decision→search
extraction as an equivalence (AGENTS.md line 36); (v) proposes the generic injectivity goal or
unconditional `contentInput?` success (§4.7); or (vi) reports green CI as mathematical progress.

### 7.1 Slice log

| Slice | Branch | Status | Merged as |
|---|---|---|---|
| FEAS-0 target size bound / fast rejection | `work/ct-feas0-target-size-bound` | not started | — |
| GATE-0 non-vacuity | `work/ct-gate0-nonvacuity` | blocked on FEAS-0 | — |
| P0 content semantic verifier | `work/ct-p0-content-semantic-verifier` | blocked on FEAS-0 | — |
| I1 gate closure | `work/ct-i1-gate-closure` | blocked on FEAS-0 | — |
| D1a tape lemmas + bridge structure | `work/ct-d1a-tape-interface` | blocked on FEAS-0 | — |
| D1b bridge ⇒ NP-witness | `work/ct-d1b-bridge-witness` | blocked on FEAS-0, P0 | — |

---

## 8. Stop/go summary

| Gate | Slice | Condition | Action if red |
|---|---|---|---|
| **F0** | FEAS-0 | a polynomial bound from accepted complete words to `treeMCSPPrefixM codec n'`, **or** a poly-time fast-rejection equivalent | outcome (c): halt every other slice, rewrite §1.1 with a budgeted content predicate, keep the length-gated target live |
| **G0** | GATE-0 | a *concrete* word is `ContentAccepts`-accepted at `treeCircuitWitnessCodec (thresholdPoly k)` | halt the D-track and escalate; do not build a machine for a possibly-empty `L'`. P0/I1 continue |
| **G1** | P0 | the `Bool`↔`Prop` headline is hypothesis-free | fix the `Bool` definition's failure branches, not the statement |
| **G2** | P0 | the three codec-path theorems carry **exactly** the standard triple; the padding lemma may be lighter; computability checked by instance provenance + one `#eval`, **not** by an axiom check | a fourth axiom, a `noncomputable` marker, or a `Classical.propDecidable` instance is a blocker |
| **G3** | I1 | injectivity stated only as `treeMCSPPrefixM_injective_of_monotone` / `_treePoly` | reject any generic-codec injectivity claim as **false**; do not strengthen `PrefixInput` to dodge it |
| **G4** | I1 | `decodeGamma?_consumed_eq_gammaLen` needs no premise beyond a successful decode | fix `readNatBE_lt_two_pow`, not the statement |
| **G4b** | I1 | `contentInput?_isSome_iff_of_header` leaves exactly premises #9–#11 open | a fourth open premise means a range lemma was missed; folding one away means the parser was mis-read |
| **G5** | D1a | `accepts_eq` uses the exact-step model, no halting/`∃ t ≤` variant | reject: the slice has changed the machine model |
| **G6** | D1b | the witness repackaging consumes `runTime_poly` verbatim — **and note advice-avoidance is unenforced** (§1.3 caveat 6) | under-specified bridge; do not claim advice-freedom without a formal clock premise |
| **G7** | all | ≤ 1500 LOC and ≤ 10 modules at PR time (§6.1) | split before review; never waived |
| **G8** | all | `./scripts/check.sh` and `./scripts/check_doc_honesty.sh` green | fix before review; a red doc guard is a blocking defect, not a formality |
| **G9** | all | axiom footprint is the standard triple or lighter | investigate any fourth axiom before merge |

---

## 9. Bottom line

* Input (2) is **provisionally** frozen at `ContentPrefixExtensionNPWitness` / `ContentAccepts`
  (`ContentPrefixExtension.lean:211`, `:152`). The freeze is conditional on **FEAS-0**: nothing
  bounds the decoded convention length `treeMCSPPrefixM codec n'` polynomially in the physical
  length of an accepted word, and the decoded `n'` can be exponential in `N`, so a polynomial-time
  verifier for `L'` may not exist by this route at all (§1.0).
* Because of that, the length-gated `PrefixExtensionNPWitness` is **retained, not retired**. The
  previous revision's blanket ban on new length-gated work is withdrawn until FEAS-0 is green
  (§1.2).
* The donor manifest's central premise — "nothing on `main` is reusable, branch from `4a8ee0c9`" —
  is false. Eight modules on `main` (CT-A/B/C) plus the pre-existing parser/codec foundation are
  the actual base, and every slice in §4 is dependency-closed on `main = 98250643`.
* The donor TM stack is a **transcoder**, not a verifier: it never touches the header, the truth
  table, the size check, or `TM.accepts`, so completing it would not discharge `(★′)`. It is parked
  — but its witness-decoding machinery is a plausible component for a future verifier, so it is
  insufficient rather than useless (§3.4).
* Two claims from the previous revision are **corrected**: generic injectivity of
  `treeMCSPPrefixM codec` is **false** (specialize to monotone `witnessBits`, §4.3.1), and gamma
  canonicity is a **theorem** rather than a hypothesis, which makes the strict parser's length gate
  unconditionally vacuous and reduces the open residue to three explicit value tests (§4.3.2–4.3.3).
* The machine model's `runTime` field is unrestricted
  (`RuntimeAdviceBarrier.lean:77` `lengthAdviceLanguage_in_repo_P`), and `ContentVerifierBridge`
  does **not** exclude a bridge that exploits it. Advice-avoidance is an unenforced review
  convention until a formal clock premise is added (§1.3 caveat 6, G6).
* Only FEAS-0 starts today: 250–450 LOC · 1–2 modules. GATE-0, P0, I1, D1a and D1b — a further
  1360–2220 LOC across 6–9 new modules (200–350 + 350–550 + 500–800 + 250–400 + 60–120) — unlock
  only if FEAS-0 lands as (a) or (b).
