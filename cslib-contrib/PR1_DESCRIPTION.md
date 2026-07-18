# feat(Computability): injectivity and uniqueness lemmas for single-tape TMs

## Summary

Adds foundational lemmas to the existing single-tape TM development — no new files, no new
concepts, no new definitions except two `Prop`-level theorems' worth of helper statements.
The lemmas make explicit, as theorems, guarantees that the model was designed around (cf. the
docstrings of `BiTape.mk₁` and `SingleTapeTM.initCfg`: "distinct lists map to distinct initial
configurations"), and extract a generally useful public composition lemma from two existing
private proofs.

This is the first of a planned short series adding complexity classes (P, coP, then
verifier-based NP) over `SingleTapeTM`, discussed on Zulip beforehand: [link to Zulip thread].
Everything in this PR is independently useful regardless of that series.

## Changes

`Cslib/Foundations/Data/BiTape.lean` (~53 lines):
- `StackTape.toList_injective`, `StackTape.mapSome_injective`
- `BiTape.mk₁_injective` — rendering a `List Symbol` onto the tape is injective

`Cslib/Computability/Machines/Turing/SingleTape/Deterministic.lean` (~92 lines added, one
proof refactored):
- `initCfg_injective`, `haltCfg_injective` — distinct words give distinct initial/halting
  configurations (turns the `initCfg` docstring's stated intent into a theorem)
- `transitionRelation_deterministic` — `tm.TransitionRelation` is right-unique
- `not_transitionRelation_haltCfg` — halting configurations are final
- `OutputsWithinTime.outputs` — forgetting the step bound
- `outputs_unique` — a machine outputs at most one word on a given input; proved via the
  existing `Relation.ReflTransGen.total_of_right_unique` rather than any new relation
  machinery
- `compComputer_outputsWithinTime` (public) — if `tm1` outputs `b` from `a` within `t₁` steps
  and `tm2` outputs `c` from `b` within `t₂`, then `compComputer tm1 tm2` outputs `c` from `a`
  within `t₁ + t₂`. This is extracted from the existing *private* lemmas
  `comp_left_relatesWithinSteps` / `comp_right_relatesWithinSteps`; `TimeComputable.comp`'s
  proof is refactored to consume it (net simplification, **no signature changes** — in
  particular `h_mono` is untouched, so this PR composes cleanly with #396 in either merge
  order; happy to rebase whichever lands second).

## Coordination

- @BoltonBailey: this touches your files and overlaps in spirit with draft #192 — review
  (or co-authorship) very welcome; the extraction of the private comp lemmas is meant as a
  net gift, not a fork of direction.
- Related: #396 (removes `h_mono` from `PolyTimeComputable.comp` — no conflict by
  construction, see above), issue #611 (complexity roadmap), closed #400 (earlier complexity
  attempt; the follow-up series addresses the verifier-totality concerns raised there).
- Follow-ups (already drafted, to be PR'd separately per the Zulip plan): deciders and
  P/coP with `coP = P`; a relabeling/well-formedness machine toolkit; verifier-based NP with
  an honest `P ⊆ NP`.

## Checks

> **Before opening this PR**, run and confirm all of the following locally — do not submit
> with this section still describing intent rather than a verified result:
- [ ] `lake build`
- [ ] `lake test`
- [ ] `lake lint`
- [ ] `lake exe lint-style --fix`
- [ ] `lake exe mk_all`
- [ ] `lake shake --add-public --keep-implied --keep-prefix --fix`
- [ ] All new declarations have docstrings; no `sorry`; no new imports beyond what shake keeps.

## Use of AI

Per the Mathlib AI policy that CSLib follows: the Lean code and proofs in this PR were written
with LLM assistance (Anthropic's Claude, used as a coding assistant for drafting lemma
statements and proofs against the existing `BiTape`/`SingleTapeTM` API), working under the
direction of Dmitry Khanukov, who specified the design, reviewed every statement and proof,
and verified the build and lints locally before submission. LLM-drafted proofs can make
characteristic mistakes (e.g. plausible-but-wrong lemma names or unnecessary hypotheses), so
extra reviewer scrutiny on those axes is welcome.
