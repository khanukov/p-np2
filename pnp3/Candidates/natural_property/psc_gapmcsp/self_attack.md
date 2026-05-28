# Self-attack — psc_gapmcsp

**Updated by auditor (May 2026)**: two new attacks added (9, 10), both
**`attack-succeeded`** with kernel-checked Lean witnesses in
`proof.lean`. Status of the candidate downgraded to `under_review` in
`manifest.toml`. Attacks 1, 8, 9, 10 are now all relevant gates.

## Attack 1 — hardwiring  **(BLOCKING GATE)**

Does `SourceTheorem_psc_gapmcsp` admit a truth-table hardwired witness?
All nine existing `NoGoLog` entries have `failure_class = "hardwiring"`,
so this is the single most likely death. The defence is the
`NotHardwired P` conjunct (Rule 5 exclusion lemma); it must be a
*proved* lemma, attacked with the construction in
`pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`.

Status: `not-attempted`

If `attack-succeeded` → record `NoGoLog` entry, `failure_class = "hardwiring"`.

## Attack 2 — refuted-predicate sneak-in

Does the dependency closure of the source theorem or bridge reach any
refuted predicate in `spec/target.toml::[refuted_predicates]`
(support-bounds / multi-switching family)? Walk the closure once the
abstract parameters are instantiated.

Status: `not-attempted`

## Attack 3 — typeclass-payload channel

Any payload smuggled through a `class`/`instance`/`Fact`/`opaque` or a
`noncomputable def` named `Provider/Default/Payload/Witness/Source/Gap`?
(Rule 16.) The skeleton `proof.lean` uses none; re-check after the
inhabitant is written.

Status: `attack-failed` (skeleton clean; recheck post-inhabitant)

## Attack 4 — collapse-not-contradiction

Does the bridge actually deduce the separation, or only an implication
like "NP ⊆ P/poly ⇒ PH collapses"? (Rule 8.) Shape check: the bridge
must produce `NP_not_subset_PpolyDAG` from conjuncts (2)+(3) directly.

Status: `attack-failed` (by design; verify after bridge is retyped)

## Attack 5 — arbitrary-witness exploitation

Does the candidate rely on `∀ W : PpolyWitness, …` without the Rule 5
exclusion lemma? The usefulness conjunct (2) quantifies over poly-DAG
functions, so the `NotHardwired` exclusion lemma is mandatory (= Attack 1).

Status: `not-attempted` (tied to Attack 1)

## Attack 6 — prior-art duplication

Per Rule 15, is this Chow's `discrimination` property re-skinned, or an
already-refuted SoS-for-MCSP route? Structural difference must be
explicit (see `sketch.md` §"Connection to prior work"): target the
specific `GapMCSP` and use thinning to engineer sub-largeness.

Status: `not-attempted`

## Attack 7 — size policy violation

Per Rule 4, does `SourceTheorem_psc_gapmcsp` (and closure) fit
`K_stmt = 40`, `K_exp = 200`? The skeleton statement is ~10 lines;
instantiating the five abstract predicates with real repo defs must stay
within budget, else narrow before re-submission.

Status: `not-attempted`

## Attack 8 — inversion (certification vs function hardness)  **(BLOCKING GATE)**

The pseudo-calibration machinery natively certifies
*indistinguishability* (no low-degree distinguisher), which is the
**barrier direction**, not a circuit lower bound. Confirm the inhabitant
proves *function hardness* (`∀ poly C, ∃ x, C(x) ≠ tt(GapMCSP)(x)`) and
not merely "the planted distribution fools low-degree tests".

Status: `not-attempted`

If `attack-succeeded` (i.e. only certification hardness is obtained) →
the candidate is inverted and worthless as a source; record `NoGoLog`,
`failure_class = "inversion"` (propose new class if absent).

## Attack 9 — equivalence collapse (sub-largeness is decorative)  **(attack-succeeded)**

Status: **`attack-succeeded`** (kernel-checked, May 2026)

Formal witness: `psc_two_conjuncts_iff_bare_separation` in `proof.lean`.
The two main conjuncts of `SourceTheorem_psc_gapmcsp` — usefulness +
holds-on-target — are *provably equivalent* (as an `Iff`) to the bare
DAG separation `∀ n f, IsGapMCSP n f → ¬ InPpolyDAG n f`. The remaining
conjuncts (`Constructive`, `IsSubLarge`, `NotHardwired`) constrain the
form of the witness but do not reduce the mathematical content.

Concretely, taking `P := IsGapMCSP` satisfies the two main conjuncts
under the bare separation, so without a non-trivial `NotHardwired` the
candidate is structurally a re-statement of the target. This connects
Attack 9 to Attack 1: the trivial hardwired witness (P "is the target
function") automatically passes both main conjuncts and is sub-large
under any natural largeness measure; the only thing that distinguishes
a real candidate from this collapse is `NotHardwired`.

Implication for engineering: do **not** dispatch to write a positive
inhabitant against the current skeleton. The productive next deliverable
is the negative meta-theorem `PSC_Skeleton_Equivalence_Or_Hardwiring`
(`sketch.md §Productive next deliverable`).

## Attack 10 — forbidden-target instantiation (Gate B)  **(attack-succeeded)**

Status: **`attack-succeeded`** (kernel-checked, May 2026)

Formal witness: `psc_forbidden_target_collapse` in `proof.lean` (same
shape as `hdx_locality_current_shape_impossible`, against plain
`InPpolyDAG` rather than oracle-extended). If `IsGapMCSP` is
instantiated to any target the repo already proves to lie in
`InPpolyDAG`, the source theorem is unconditionally `False`.

**Repo-proved forbidden instantiations** (must be excluded by the
engineer before any positive work):

* `Tests.HInDagTrivialityProbe.fixedSlice_gapPartialMCSP_in_PpolyDAG`
  — fixed-slice `gapPartialMCSP_Language p` is in `PpolyDAG` via
  per-slice truth-table hardwiring at a slice-dependent constant `K_p`;
* `Tests.HInDagTrivialityProbe.hInDag_for_canonicalAsymptoticHAsym`
  — canonical asymptotic GapMCSP (`sYES=1, sNO=2`) is in `PpolyDAG` for
  the same reason; the canonical track is independently refuted at
  conclusion level (`STATUS.md §Audit chain stages 11, 14`).

A valid C1 instantiation requires a **new** asymptotic NP language not
yet hardwirable by the repo, AND no analogous hardwiring witness should
be derivable for it. Designing such a language is itself an open
research question — recorded here as the engineer-blocking
precondition.

`NoGoLog` recommendation (operator-side): `failure_class =
"forbidden_target_instantiation"` (extends the `oracle_target_collision`
family introduced by `hdx_locality`); structural pattern is
"instantiating the target predicate against a class for which the repo
already proves the target lies inside that class".
