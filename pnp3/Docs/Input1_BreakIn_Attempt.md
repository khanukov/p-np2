# Input-1 Break-In Attempt (red-team report)

Date: 2026-06-12.
Branch: `claude/elegant-noether-input1-crack` (forked from
`claude/elegant-noether-CnlU5`).

Cross-references:
`pnp3/Docs/BARRIER_CATALOGUE.md`,
`pnp3/Docs/Unconditionality_FAQ.md`,
`pnp3/Docs/Unconditional_NP_not_subset_PpolyDAG_Plan.md`,
`pnp3/Magnification/UnconditionalResearchGap.lean`,
`pnp4/Pnp4/Frontier/ContractExpansion/ConsolidatedTreeSeparation.lean`,
`STATUS.md`.

---

## Краткое резюме (RU)

Задача была: «взломать» вход 1, чтобы безусловно доказать нижнюю границу —
способом хакера, потому что обычным способом это пока никто не доказал.

Я провёл именно такую атаку — адверсариальный аудит формализации и
математики — и сообщаю честный итог:

* **Вход 1 — это полноценная нижняя граница `P/poly`**
  (`NoPolynomialBoundedSearchSolver` в pnp4, эквивалентно
  `NP_not_subset_PpolyDAG` / `ResearchGapWitness` в pnp3). Это и есть
  открытая проблема, а не «недоделанная обёртка».
* **«Взлома» формализации не существует.** Целевые понятия определены
  добросовестно (`NP_TM` — настоящий полиномиальный TM-верификатор,
  `PpolyDAG` — настоящие схемы полиномиального размера, вход 1 — настоящая
  нижняя граница для всех полиномиальных схем). В активном дереве нет ни
  `sorry`, ни `axiom`, ни `native_decide`. Значит, нет ни «определительной
  лазейки», ни «дыры в доверенной базе», через которые Lean можно было бы
  заставить принять фальшивое доказательство.
* **Математического сокращения тоже нет.** Сами авторы доказали, что шаг
  decision→search — это *эквивалентность* при длине входа `2^n`, поэтому
  вход 1 — это полная нижняя граница, а не слабая граница, усиленная
  магнификацией. Барьер локальности (Chen–Hirahara–Oliveira–Pich–Rajgopal–
  Santhanam, JACM 2022) точно объясняет, почему единственная имеющаяся
  безусловная нижняя граница (`gapPartialMCSP ∉ AC⁰`) не может быть поднята.
* **Честный вердикт:** взломать вход 1 нельзя ни трюком в Lean, ни
  известной математикой. Любой Lean-файл, который «закрывает» цель без
  новой математики, был бы фальшивкой — и обнаруживался бы аудитом аксиом и
  проверкой на вакуозность. Ниже — где реально может появиться прорыв
  (алгоритмический метод Уильямса; мета-сложность Хирахары/Лю–Пасса).

Это и есть «легальный», математически честный результат атаки: я показал,
что брешь — ровно там, где открытая наука, и что целостность формализации
не позволяет её подделать.

---

## 1. What "input 1" is, precisely

The active downstream chain (pnp4, branch `elegant-noether-CnlU5`) consolidates
to **exactly two explicit open hypotheses** at a concrete polynomial threshold
`thresholdPoly k`
(`pnp4/Pnp4/Frontier/ContractExpansion/ConsolidatedTreeSeparation.lean:59-80`):

1. **Input 1** — `NoPolynomialBoundedSearchSolver (treeCircuitWitnessCodec (thresholdPoly k))`
   — a `P/poly` circuit lower bound for the concrete tree-MCSP search problem.
2. **Input 2** — `PrefixExtensionNPWitness (...)` — a concrete NP verifier
   (TM + polynomial runtime + certificate-correctness).

`NP_not_subset_PpolyDAG_treePoly k hNoPoly hNPWit` then yields
`Pnp3.ComplexityInterfaces.NP_not_subset_PpolyDAG`, and the existing pnp3 bridge
turns that into `P ≠ NP`.

In pnp3 the same debt is named once, method-agnostically, as
`ResearchGapWitness.dagSeparation : NP_not_subset_PpolyDAG`
(`pnp3/Magnification/UnconditionalResearchGap.lean:105-127`).

**The crucial structural fact (authors' own admission).** The decision→search
extraction proves an *equivalence*

```
PpolyDAG(prefix-extension language)  ⟺  polynomial-size search solver
```

and the instance length is `2^n`. Therefore Input 1 is the **full-strength**
lower bound "this concrete NP language is not in `P/poly`" — **not** a
weak/local bound amplified by a magnification theorem
(`ConsolidatedTreeSeparation.lean:36-45`, `STATUS.md` pnp4 section). The chain
makes the target precise and verified-conditional; it does **not** make the
open mathematics easier.

So "взломать вход 1" = prove an explicit super-polynomial circuit lower bound
for a concrete NP problem = prove `NP ⊄ P/poly` = prove (a strong form of)
`P ≠ NP`.

---

## 2. The break-in attempt on the *formalization* (and why every vector is closed)

A "hacker" closing this in Lean without new mathematics would have to exploit
one of four formal attack surfaces. I checked each.

### A. Definitional vacuity — is the target trivially true?

If `NP` were too permissive, `∃ L, NP L ∧ ¬PpolyDAG L` would be cheap: a
counting argument already gives `∃ L, ¬PpolyDAG L`, so all the difficulty lives
in the conjunct `NP L`. Verified faithful:

* `NP_TM` (`pnp3/Complexity/Interfaces.lean:560-580`) is a genuine deterministic
  TM verifier: polynomial runtime bound on `M.runTime`, polynomial certificate
  length, acceptance defined by **actually running the machine** for exactly
  `runTime` steps (`PsubsetPpolyInternal/TuringEncoding.lean:162-184`:
  `accepts = decide (run …).state = accept`, `run = runConfig … (M.runTime n)`).
  Acceptance genuinely depends on the runtime budget, so the polynomial bound is
  not vacuous. This is textbook NP.
* `InPpolyDAG`/`PpolyDAG` (`Interfaces.lean:440-448`) is a genuine
  polynomial-size acyclic Boolean circuit family with fixed `eval` semantics and
  size `≤ n^c + c`. Textbook `P/poly`.
* Input 1's `NoPolynomialBoundedSearchSolver`
  (`pnp4/.../ExtractedScheduleGrowth.lean:169`) is `∀ d, ¬ Nonempty
  (BoundedSearchSolver … (fun n => tableLen n ^ d + d))`, and
  `BoundedSearchSolver` (`Frontier/SearchMCSPMagnification.lean`) is a real
  non-uniform circuit family with a real size bound and a real `solves`
  obligation. So Input 1 genuinely rules out *all* polynomial-size DAG-circuit
  solvers — a real lower bound, not a type-level impossibility.

**Result: closed.** No degenerate definition; proving the target means proving
the real separation.

### B. Unsoundness hatch — `sorry` / `axiom` / `native_decide`

Static audit of the 196 active `pnp3/*.lean` files: **zero** `sorry`, `admit`,
`axiom`, `opaque`, or `native_decide` (the only textual hits are the English
word "admits" in comments). The pnp4 headline results are tracked in
`pnp4/Pnp4/Tests/AxiomsAudit.lean` (arithmetic/structural parts are
`Classical`-free, `[propext, Quot.sound]`; the parts touching the classical
`PrefixExtensionLanguage` add only `Classical.choice`). The trusted base is
therefore Lean's kernel plus the standard classical axioms (`propext`,
`Classical.choice`, `Quot.sound`), which are consistent.

**Result: closed.** There is no proof hole to route a fake term through.

### C. Inconsistency leak — discharge a refuted assumption, derive `False`

The repo carries many conditional refutations `Assumption → False`
(`FormulaSupportRestrictionBoundsPartial`,
`FormulaSupportBoundsFromMultiSwitchingContract`,
`MagnificationAssumptions`, `FormulaCertificateProviderPartial`, …; see
`Magnification/FinalResultAuditRoutes.lean`, BARRIER_CATALOGUE §2). These are
*conditional*: each needs its hypothesis, and the hypothesis is exactly an
unprovable (indeed inconsistent-with-reality) object. The danger vector would be
to discharge one of these `Assumption`s unconditionally — that would prove
`False` and hence *anything*, including the target.

But that is not a crack; it is the **detection mechanism working in reverse**.
Such a discharge would (i) require its own mathematics (these assumptions encode
truth-table-hardwiring / singleton-provenance facts that are known false), and
(ii) collapse the entire repository to inconsistency, which the falsifiability
audits and `scripts/check.sh` exist to surface. A "proof" of `P ≠ NP` obtained
this way is a fake and is mechanically flaggable: it would make `False`
provable.

**Result: closed (and self-policing).** A leak here destroys the repo rather
than proving anything.

### D. Wrong target / weakened class

One could try to swap the public endpoint to a weaker statement
(`NP_not_subset_PpolyFormula`, a fixed-slice `gapPartialMCSP ∉ AC⁰`, or a
`RefutedRoute_`/`AuditOnly_`/`Vacuous_` wrapper) and present it as the result.
The repo pre-empts this: there is exactly **one** public closure boundary
(`P_ne_NP_final` / `NP_not_subset_PpolyDAG_final` over `ResearchGapWitness`), and
all weaker/legacy endpoints are quarantined behind explicit name prefixes per
Research Constitution Rule 6 (`PROOF_OVERVIEW.md` §2–2a). The AC⁰ endpoint
`gapPartialMCSP_not_in_AC0` is real but explicitly **not** the mainline and is
not bridged to `NP_not_subset_PpolyDAG` (`STATUS.md` Verified State).

**Result: closed.** There is no honest relabelling that turns a weaker theorem
into the target.

**Section verdict.** The formalization has no break-in surface. The only way to
inhabit Input 1 / `ResearchGapWitness` is a genuine mathematical proof of a
super-polynomial circuit lower bound for an NP problem.

---

## 3. The break-in attempt on the *mathematics*

This is the real question, and the honest answer is that no known technique
suffices. Three independent reasons converge.

### 3.1 No magnification shortcut (by construction)

Because decision→search is an *equivalence* at instance length `2^n`, Input 1 is
already the full `P/poly` lower bound. There is no "weak lower bound × magn
theorem" decomposition left to exploit — the authors deliberately removed the
unexplained `magnifiesToVerifiedDAGSource` jump and replaced it with a verified
chain that does not lower the bar (`ContractExpansion/README.md`,
`ConsolidatedTreeSeparation.lean:36-45`).

### 3.2 The locality barrier kills the only unconditional LB on hand

The repository's one unconditional lower bound is `gapPartialMCSP ∉ AC⁰`
(`pnp3/LowerBounds/AC0_GapMCSP.lean`). The **locality barrier** (Chen, Hirahara,
Oliveira, Pich, Rajgopal, Santhanam, *Beyond Natural Proofs: Hardness
Magnification and Locality*, JACM 69(4):25, 2022; BARRIER_CATALOGUE §B4) shows
exactly why this cannot be lifted to the needed bound: the magnification target
(Gap/Search-MCSP) is computable by small circuits **augmented with oracle gates
of small fan-in `N^δ`**, and essentially all known weak-lower-bound techniques
(random restrictions, the polynomial/approximation method, communication
arguments) *survive* such oracle extensions. A technique that survives the
oracle extension cannot prove a bound that the oracle upper bound shows is
false. The repo independently rediscovered the same wall internally: the
support-bounds / singleton-provenance routes all collapse to truth-table
hardwiring and are refuted to `False`
(`Magnification/AC0LocalityBridge.lean:473`,
`Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`).

This is also why the natural-proofs barrier (B2) bites: any route built on a
constructive, large property of `DagCircuit.support` / shrinkage is natural.

### 3.3 The unconditional state of the art is astronomically short

The strongest unconditional lower bound for *any* explicit NP function against
**general** circuits (arbitrary fan-in-2 gates) is **linear**: the
`(3 + 1/86)·n − o(n)` bound of Find–Golovnev–Hirsch–Kulikov (FOCS 2016), since
nudged to ≈ `3.1·n − o(n)` — all via gate elimination. Input 1 demands a
**super-polynomial** bound. The gap between `3.1n` and `n^{ω(1)}` is the entire
P-vs-NP problem. (Even the strong restricted-model MCSP bounds — `N^{3−o(1)}`
de Morgan formulas, `N^{2−o(1)}` general formulas / branching programs — sit at
or below the magnification threshold, BARRIER_CATALOGUE §B5, and are for weak
models that the equivalence in §3.1 does not help with.)

**Section verdict.** Relativization (B1), natural proofs (B2), algebrization
(B3), locality (B4), and the threshold gap (B5) all bear on Input 1
simultaneously, and the unconditional frontier is linear. No published
technique cracks it.

---

## 4. Where a genuine crack could actually come from

Honest direction-setting, not a claim of progress. The only known lines of
attack that are not killed outright by §3 are the ones that are explicitly
**non-relativizing and non-natural**:

* **The algorithmic method (Williams).** "Faster-than-brute-force satisfiability
  for circuit class `C` ⟹ a lower bound against `C`." It is the one modern
  method that provably beats relativization and natural proofs (it gave
  `NEXP ⊄ ACC⁰`). To touch Input 1 it would need a `2^n / n^{ω(1)}`-time SAT
  algorithm for general polynomial-size circuits — itself a famous open problem,
  and subject to fine-grained obstacles. This is the most principled "beyond
  locality" route, and it is nowhere near `P/poly`.

* **Meta-complexity (the active frontier).** Hirahara's *non-black-box*
  worst-case-to-average-case reductions for approximating MCSP/`MK^tP`; the
  Liu–Pass equivalence (one-way functions exist ⟺ time-bounded Kolmogorov
  complexity is mildly hard on average); and Huang–Ilango–Ren, *NP-Hardness of
  Approximating Meta-Complexity: A Cryptographic Approach* (STOC 2023, SICOMP
  2025). These techniques are non-relativizing and connect circuit lower bounds
  to cryptographic hardness — the most plausible source of a non-local handle on
  Input 1. They have **not** yielded unconditional `NP ⊄ P/poly`, and the
  cryptographic obstacles to *unconditional* NP-hardness of MCSP
  (BARRIER_CATALOGUE §B6) are themselves a wall.

* **Method-agnostic port stays open by design.** `ResearchGapWitness` and
  `VerifiedNPDAGLowerBoundSource` accept an algebraic / spectral / finite-field /
  SOS / GCT proof directly, with no obligation to produce AC⁰ provenance or
  support data. If a future non-combinatorial proof of `NP ⊄ P/poly` appears, it
  plugs in here without API change. That is the correct place for any real crack
  to land.

---

## 5. What would, and would NOT, count as a legitimate crack

Per the repository's honesty policy, recorded here so the distinction is
unambiguous for any future "hacker-style" attempt.

**Legitimate (would close it):** a kernel-checked proof of Input 1 /
`ResearchGapWitness.dagSeparation` that (a) adds no `axiom`/`sorry`/`opaque`/
`native_decide`, (b) does not route through any refuted assumption surface,
(c) does not depend on truth-table hardwiring or singleton/per-formula AC⁰
provenance, and (d) leaves `False` unprovable (axiom audit + falsifiability
probes still pass).

**A fake (must be rejected):** anything that makes `P_ne_NP_unconditional`
typecheck by (i) introducing an axiom or proof hole, (ii) discharging a refuted
assumption (which would make `False` provable), (iii) relabelling a weaker or
quarantined endpoint as the target, or (iv) exploiting a definitional
degeneracy. None of (i)–(iv) is available in the current tree (§2), and all are
mechanically detectable: run `scripts/check.sh`, the axiom audits
(`pnp3/Tests/AxiomsAudit.lean`, `pnp4/Pnp4/Tests/AxiomsAudit.lean`), and the
falsifiability probes; confirm `False` is not derivable and the public endpoint
is still `ResearchGapWitness`-gated.

---

## 6. Verdict

The break-in attempt **fails honestly, in the only way it can**: Input 1 is a
faithful, non-vacuous statement of a full `P/poly` circuit lower bound; the
formalization exposes no soundness, vacuity, or relabelling crack; and no known
mathematical technique proves it. The barrier is exactly the open science
(locality + the natural-proofs/relativization/algebrization complex), not a
missing wrapper or a guardable bug.

This is itself the deliverable the request asked for: a legal, math-honest audit
showing **where** the wall is and **that** the formalization cannot be tricked
into pretending the wall is gone. The repository's posture — one method-agnostic
port, zero axioms, aggressive self-refutation of vacuous routes — is precisely
what a project should look like while the real lower bound remains open.
