# Status: complexity classes (P, coP, NP) for CSLib

Target repo: `leanprover/cslib` (official Lean 4 CS library). Goal: the first P/coP/NP layer
over CSLib's existing deterministic single-tape Turing machine
(`Cslib.Turing.SingleTapeTM`), answering every blocker raised in the earlier review of a
similar attempt against mathlib's TM1 model (see the design rationale in `DESIGN.md` §3,
"blocker map").

**This is a reviewed draft, not a submission.** No Lean toolchain is available in the
sandbox this was authored in, so nothing here has been compiled. Read this file before
acting on anything below.

## How this was produced and checked

1. A background workflow read CSLib's actual sources (the deterministic/nondeterministic
   TM files, `BiTape`/`StackTape`/`RelatesInSteps`, CONTRIBUTING/GOVERNANCE/ORGANISATION,
   and the current state of the CSLib niche — open PRs #192/#400/#611/#396 and who owns
   them), produced three independent designs (minimal-first-PR / textbook-fidelity /
   CSLib-idiom angles), had two independent judges score them (both picked the
   **minimal-first-PR** design — `DESIGN.md` is that design, with the judges' must-fix
   items grafted in), then drafted the Lean files below.
2. The workflow's automated adversarial-verification phase (one skeptic per blocker, an
   API auditor, a proof auditor, a style auditor) **did not run** — it hit a session token
   limit twice in a row. The `criticalCount: 0` / `majorCount: 0` you may see in tool logs
   for that run reflects **zero reports produced**, not zero issues found. Do not read it
   as a clean bill of health.
3. Given that, the code was instead reviewed **by hand, line by line, against the actual
   downloaded CSLib/Mathlib sources** (not from memory): every structure definition
   (`BiTape`, `StackTape`, `SingleTapeTM`, `SingleTapeTM.Cfg`) was read in full, every cited
   Mathlib identifier was grepped for in a local mathlib checkout, and every proof was
   traced against the real definitions.

## What that manual review found and fixed

**One real, structural bug class, now fixed in the files under `lean/`.** Both `BiTape`
and `SingleTapeTM.Cfg` declare their carrier type parameter (`Symbol`, `tm`) as an
*explicit* structure argument (`structure BiTape (Symbol : Type*) where …`,
`structure Cfg` inheriting the explicit `(tm : SingleTapeTM Symbol)` from its enclosing
`variable`). The original draft proved several injectivity lemmas
(`BiTape.mk₁_injective`, `StackTape.mapSome_injective`, `SingleTapeTM.initCfg_injective`,
`SingleTapeTM.haltCfg_injective`) using `congrArg <field> h` with the **bare** field
projection (`congrArg head h`, `congrArg toList h`, `congrArg Cfg.BiTape h`). Because the
projection's type has an explicit leading argument that dot notation would normally
resolve automatically but a bare identifier passed to `congrArg` will not, this pattern
does not elaborate in Lean 4 (an explicit argument is never auto-inferred outside dot
notation, unlike an implicit one). All 7 occurrences (5 in `BiTape.lean`, 2 in
`Deterministic.lean`) were rewritten to `congrArg (fun x => x.field) h`, which sidesteps
the issue by letting ordinary dot notation inside the lambda resolve the explicit argument
from the bound variable's type. This is a mechanical, low-risk fix, but it was **not**
optional: `initCfg_injective` is the root of the input-injectivity chain (blocker B1) that
essentially everything else in `Defs.lean` depends on.

Credit where due: the drafting agent's own risk list (`RISKS_PR1_PR2.md`, items 3 and 5)
had already flagged both spots as uncertain and proposed fallbacks — one of which
(item 5's `simp only [initCfg, Cfg.mk.injEq, …]`) would also have worked, the other
(item 3's `simpa … using congrArg toList h`) would not have, since it still contains the
same non-elaborating subterm. The fix applied here replaces the primary proof text
directly rather than relying on either fallback.

**One honesty fix, not a code bug.** `PR1_DESCRIPTION.md`'s "Checks" section originally
asserted that `lake build`/`lake test`/the linters "all pass locally" — a template
sentence, not a true statement (nothing has been built). It now reads as an explicit
checklist to complete *before* opening the PR, not a claim.

## Why there's still no compiler check (tried, hit a hard wall)

A follow-up session attempted to actually install a toolchain and compile this. Findings,
for whoever picks this up next:

- `elan` (the Lean toolchain manager) **can** be installed in a khanukov/*-scoped sandbox:
  it's packaged in Ubuntu's `universe` repo (`apt-get install elan`), a plain Debian
  mirror, not GitHub.
- The actual Lean 4 **toolchain** cannot. It is distributed exclusively via
  `github.com/leanprover/lean4/releases`, and every GitHub-hosted path that could reach it
  — `github.com`, `api.github.com`, `codeload.github.com` — returns the same session-scope
  403 (`"GitHub access to this repository is not enabled for this session"`) for the
  `leanprover` owner, because these campaign sessions are scoped to `khanukov/*` repos.
  `raw.githubusercontent.com` and `*.github.io` are reachable (they served the file-by-file
  reading this whole review was based on) but neither serves release binaries or archives,
  so there is no way to reach the toolchain from inside such a session. This is a
  same-owner-only restriction (confirmed via `add_repo`'s own error message: cross-tier
  adds — a different GitHub owner than the session's existing repos — are refused outright,
  you'd need a *fresh* session started with `leanprover/cslib` or `leanprover/lean4` as an
  explicit initial source), not a general network policy, and not something to route
  around from inside the sandbox.
- No alternative distribution of the Lean 4 compiler exists on any host these sessions can
  reach either (checked: not in `apt`, and PyPI/npm/crates.io don't carry it).

**`verify_locally.sh`** in this directory is the practical answer: a self-contained script
(elan install if needed → pinned toolchain → fresh `leanprover/cslib` clone → drop these
files in at their paths → `lake exe cache get` → the full check suite from the process
checklist below). Run it on any machine with ordinary internet access. It is the first
thing to run before opening any PR — nothing below substitutes for it.

## What is still unverified (needs a real toolchain, not more reading)

- **Everything else** — the rest of `Defs.lean`, `Relabel.lean`, `WellFormed.lean`,
  `NP.lean` was read against the real CSLib/Mathlib sources and no further elaboration
  problem was found by this method, but "no further problem found by careful reading" is
  weaker than "compiles." Treat every `rfl` and every `simp`/`grind` closing tactic as
  unverified until `lake build` says otherwise.
- **A handful of Lean-core (not Mathlib) lemma names** could not be checked at all: this
  sandbox has no Batteries/Lean-core source checkout, only the mathlib repo itself. Flagged
  in `RISKS_PR3_PR4.md` item 3: `List.takeWhile_cons`, `List.dropWhile_cons`,
  `List.getLast?_map`, `Option.map_none`/`map_some`. These are standard-sounding names and
  likely correct, but genuinely unverified by this review.
  `List.takeWhile_append_dropWhile`, `List.length_eq_zero_iff`, `Sum.inl_injective` /
  `inr_injective`, `Function.Injective.list_map`, `Option.map_eq_some_iff` /
  `map_eq_none_iff`, `Fintype.ofEquiv`, `Polynomial.eval_add`/`eval_one`/`eval_comp` **were**
  confirmed against the local mathlib checkout (file:line references in the risk files).
- The two "sanity anchor" proofs in `WellFormed.lean`
  (`checkComputer_outputsWithinTime_nil`/`_inr`) are chains of bare `rfl` on concrete
  transition steps of a 4-state machine — a good, checkable style, but exactly the kind of
  thing that either works cleanly or reveals a wrong match arm the moment a compiler sees
  it. The one substantial deferred proof, `checkComputer_spec`, is left as a **named TODO
  with the full induction plan written out** (not a `sorry`) — see the end of
  `WellFormed.lean`; this is a genuinely large (~250–350 line) machine-analysis proof and is
  the real remaining mathematical work, not a formality.

**Bottom line: do not open any PR from this until `lake build` (plus `lake test`,
`lake lint`, `lake exe lint-style`, `lake exe mk_all`, `lake shake`) has actually been run
against a real CSLib checkout and passes.** That is the next concrete step, and no amount
of further reading substitutes for it.

## The niche this fills (verified against the live repo, 2026-07-17)

- Nothing named `P`/`NP`/`DTIME`/decider/verifier exists on CSLib `main`.
- **PR #192** (Bolton Bailey, draft, updated 2026-07-15): quantifier-style
  `BitstringDecisionProblem`/PH-style NP, not `Language`-based, has `sorry`s, author has said
  he won't undraft it until further infrastructure lands. Conceptually adjacent, not
  file-colliding.
- **PR #400** (closed): verifier-based P/NP/coNP/PSPACE; author (Samuel Schlesinger) left to
  build a separate library. Reviewer Timeroot's critique of that PR's `Verifies` definition
  is exactly blocker B3 here (total verifier) — worth citing as prior art this design
  answers.
- **Issue #611** (roadmap, 0 comments): wants a DTIME/DSPACE-first ladder; no maintainer
  buy-in recorded either way.
- **PR #396** (active, same file as our PR-1): removes the `h_mono` wart from
  `PolyTimeComputable.comp`. PR-1 here only *adds* declarations and refactors one proof body
  without touching `h_mono`, so it should rebase cleanly regardless of merge order.

## Required process, before any code is pushed anywhere

CSLib's CONTRIBUTING.md is explicit: a new foundational framework like this should be
raised on Zulip (or a GitHub issue) *before* the PR, and any AI-assisted PR must disclose
tool usage in its description (CSLib states it follows the Mathlib AI policy verbatim).
`DESIGN.md` §7 has the concrete Zulip talking points (verdict convention, per-alphabet vs
bitstring classes, namespace placement, DTIME-first vs classes-first, certificate-length
convention, sequencing with #396/#192, the NTM-bridge obligation). None of this is
optional per CSLib's own stated process — post it, in your own words, before opening PR-1.

## Files in this directory

- `DESIGN.md` — the full design: definitions with signatures, the blocker map, the PR-1…4
  plan, what is explicitly not claimed, the process checklist, the Zulip discussion points.
- `PR1_DESCRIPTION.md` — draft description for the first PR (injectivity/uniqueness lemmas
  only — no new classes, no new files, touches two existing files).
- `RISKS_PR1_PR2.md`, `RISKS_PR3_PR4.md` — the drafting agents' own itemized elaboration
  risk registers, kept verbatim (including the two spots this review's fix superseded —
  left in place so the reasoning trail is visible).
- `lean/` — the drafted files, mirroring their intended CSLib paths:
  - `Cslib/Foundations/Data/BiTape.lean` — PR-1 additions to an existing file (fixed).
  - `Cslib/Computability/Machines/Turing/SingleTape/Deterministic.lean` — PR-1 additions to
    an existing file (fixed).
  - `Cslib/Computability/Complexity/Defs.lean` — PR-2 (new file): `DecSym`, `inputWord`,
    `DecidesWithinTime`, `P`, `coP`, `coP_eq_P`.
  - `Cslib/Computability/Complexity/Relabel.lean` — PR-3 part 1 (new file, draft):
    `StackTape.map`/`BiTape.map`, `relabelComputer`.
  - `Cslib/Computability/Complexity/WellFormed.lean` — PR-3 part 2 (new file, draft):
    `checkComputer`, the named TODO for its correctness proof.
  - `Cslib/Computability/Complexity/NP.lean` — PR-4 (new file, draft): `pairEncode`, `NP`,
    `P_subset_NP_of_checkComputerSpec`.

- `verify_locally.sh` — run this first, on a machine with ordinary internet access
  (see "why there's still no compiler check" above for why it can't run inside the
  sandbox that drafted these files).

## Next steps, in order

1. Run `bash verify_locally.sh` on a machine with normal internet access (or start a
   fresh Claude session scoped to include `leanprover/cslib`, if you want this done
   in the cloud instead — see the note above on same-owner scoping).
2. Fix whatever the compiler finds (expect some — see "what is still unverified" above);
   none of it should require redesigning anything, per the manual review.
3. Post the Zulip discussion (`DESIGN.md` §7) — this is a process requirement, not a
   suggestion, per CONTRIBUTING.md.
4. Fork `leanprover/cslib`, push PR-1 first (smallest, touches only existing files,
   independently useful, invites @BoltonBailey per the coordination note).
5. PR-2 (P/coP), then PR-3 (toolkit), then PR-4 (NP, P ⊆ NP) once `checkComputer_spec` is
   actually proven — that proof is real remaining work, not a formality.
