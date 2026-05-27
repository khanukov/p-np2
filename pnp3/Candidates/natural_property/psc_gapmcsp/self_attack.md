# Self-attack — psc_gapmcsp

**Status: DRAFT.** Per Rule 12 this is a structured admission of the
most likely ways the candidate breaks — not a defence. Statuses are
`not-attempted` until the engineer runs them; the auditor should treat
Attacks 1 and 8 as **blocking gates**.

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
