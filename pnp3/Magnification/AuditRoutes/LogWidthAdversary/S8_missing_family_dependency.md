# S8 structured failure: missing admissible adversary family dependency

## 1. What was attempted

Slot S8 was selected by the required random draw.  The assigned theorem is
`adversary_support_unbounded` in
`pnp3/Magnification/AuditRoutes/LogWidthAdversary/Diversity_Unbounded.lean`,
against either the S6 `adversaryFamily_v_natlog2` construction or the S7
`adversaryFamily_v_pow2` construction.

I inspected the current repository state for any already-landed S6/S7 module or
symbol that S8 could import without writing outside its slot.  The intended
proof path would be:

1. import the landed S6 or S7 family module;
2. use its concrete `adversaryFamily_v_*` definition;
3. prove that the support cardinality along the chosen log-width/power-of-two
   subsequence exceeds any requested bound `B`;
4. expose the theorem as `adversary_support_unbounded` for S11.

## 2. Where it broke

No S6 or S7 file exists in the current tree, and neither
`adversaryFamily_v_natlog2` nor `adversaryFamily_v_pow2` is defined anywhere in
active Lean sources.  The only available FP-3b.1 adversary family is the
placeholder
`Pnp3.Magnification.AuditRoutes.FixedParamsProbe.FP3Attempt.FP3b1.adversaryFamily`,
whose body is `fun _ => FormulaCircuit.const false`.

That placeholder is explicitly documented in
`pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean` as not satisfying
`FP3Attempt.InSupportFunctionalDiversity`; its support is empty at every input
length, so the S8 unbounded-support theorem is false for it.

Within the allowed scope for S8, I am not allowed to define or repair the S6/S7
family, change the existing FP3b1 placeholder family, or modify supporting
Tier-1/Tier-4 files.  Creating a standalone family inside S8 would also violate
the slot decomposition because S8's target is the T5 unbounded conjunct against
an already-landed S6-or-S7 witness, not a new T4 construction.

## 3. Local vs global obstruction

This is a local dependency obstruction, not evidence that the log-width
hardwiring adversary is globally impossible.

The obstruction is local because the Lean environment currently lacks the
concrete family that S8 is supposed to analyze.  Once either S6 or S7 lands a
well-formed family with a support theorem/definitional shape exposing its
selected input window, S8 can be retried against that family.  Nothing inspected
here rules out the mathematical target.

## 4. What S11/integration must know

S11 should not treat S8 as a mathematical disproof of the unbounded-support
conjunct.  It is a sequencing failure: S8 was drawn before either admissible T4
family was present.

For integration, S8 needs one of the following to be available in a previously
landed module:

- `adversaryFamily_v_natlog2` from S6, plus enough facts to identify
  `(FormulaCircuit.support (adversaryFamily_v_natlog2 n)).card` along an
  unbounded subsequence; or
- `adversaryFamily_v_pow2` from S7, plus enough facts to identify
  `(FormulaCircuit.support (adversaryFamily_v_pow2 n)).card` along the
  power-of-two subsequence.

If S6/S7 only land the family/witness packaging without an explicit support
cardinality lemma, S8 will also need permission to prove that missing transport
fact in its own file by importing the chosen family module.  Without an exposed
concrete family, the S8 theorem has no legal target.

## 5. Exact files/lemmas inspected

- `seed_packs/fp3b1_log_width_hardwiring_lift/README.md`: slot table, allowed
  scope, T5 theorem statement, and dependency on S6 or S7.
- `RESEARCH_CONSTITUTION.md`: governance constraints, especially the ban on
  trust-root edits and unsupported endpoint/bridge claims.
- `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean`:
  - `FP3Attempt.InSupportFunctionalDiversity`;
  - `FP3Attempt.InSupportFunctionalDiversity_excludes_uniformPolyBound`;
  - `FP3Attempt.FP3b1.adversaryFamily`;
  - `FP3Attempt.FP3b1.adversaryWitness`;
  - the docstring explaining why the placeholder family does not satisfy
    diversity.
- `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`:
  - `FormulaCircuit.rename`;
  - `FormulaCircuit.eval_rename`;
  - `ttFormula`;
  - `ttFormula_eval`.
- `lakefile.lean`: current `Glob.one` module list; no log-width adversary slot
  modules are wired in yet.
- `scripts/check.sh`: repository guardrails that must remain green after the
  failure artifact.

## 6. Suggested next move

Land S6 or S7 first.  Prefer S7 if the power-of-two slice gives a simpler
closed form for support cardinality, because S8 can then witness a given bound
`B` with a power-of-two length and avoid depending on `Nat.log2` arithmetic.
After that module exists, retry S8 by importing the chosen family module and
proving `adversary_support_unbounded` against that exact family.
