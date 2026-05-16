# Worker prompt — `source_search_contract_expansion_D0`

## Branch

`main`

## Task

Produce one markdown report:

```text
seed_packs/source_search_contract_expansion_D0/reports/D0_contract_expansion_<HANDLE>.md
```

This is **D0 only**. Full Round 1 is **not** authorised.

Do not write Lean code. Do not edit JSONL, specs, trust roots, known guards, or
any endpoint files.

## Required reading

Read before writing the report:

- `RESEARCH_CONSTITUTION.md`
- `seed_packs/first_move_search_2026/reports/researchgap_source_theorem_reset_gpt55.md`
- `seed_packs/fp3b8_mcsp_direct_source_D0/audits/fp3b8_red_light_operator_decision_gpt55.md`
- `seed_packs/fp3b8_mcsp_direct_source_D0/reports/D0_mcsp_source_interface_gpt55.md`
- `pnp4/Pnp4/Frontier/SearchMCSPMagnification.lean`
- `pnp4/Pnp4/Frontier/SearchMCSPConcreteTargets.lean`
- `pnp4/Pnp4/Frontier/CompressionMagnification.lean`
- `pnp4/Pnp4/AlgorithmsToLowerBounds/BridgeToPpolyDAG.lean`
- `pnp3/Magnification/UnconditionalResearchGap.lean`
- `pnp3/Complexity/Interfaces.lean`
- `outputs/nogolog.jsonl` entries `NOGO-000001` through `NOGO-000009`

## Context

The ResearchGap source-theorem reset selected
`search_mcsp_contract_expansion` as the next honest source-theorem surface
after `fp3b6` stalled and `fp3b7` / `fp3b8` red-lighted.

The goal is **not** to assume `TreeMCSPSearchMagnificationSource`. The goal is
to study whether the currently abstract `SearchMCSPMagnificationContract` can be
expanded into a concrete theorem:

```text
target.noBoundedSolver → VerifiedNPDAGLowerBoundSource
```

with all assumptions visible.

## Central D0 question

Can `SearchMCSPMagnificationContract` be expanded into a concrete theorem whose
assumptions are strictly weaker than `VerifiedNPDAGLowerBoundSource` and which
avoids natural proofs / relativization / algebrization?

## Questions your report must answer

Your report must contain sections answering all of the following:

1. **What is the exact theorem surface?**
   - State the proposed theorem in precise prose or Lean-like pseudocode.
   - List every hypothesis explicitly.
   - Identify which hypotheses are old interfaces and which would be new.

2. **What is the concrete target?**
   - Identify the `SearchMCSPConcreteTarget`-style object or replacement target.
   - Explain the meaning of `target.noBoundedSolver` in the proposed surface.
   - Say whether the target is fixed, uniform in a family, or chosen from the
     lower-bound argument.

3. **What language `L` would be constructed?**
   - Define the intended NP language at the level of mathematical data.
   - State what the input length is and what witnesses/certificates look like.
   - Explain whether `L` depends on the target, on a solver, or on a diagonal
     choice.

4. **How is `L` in NP?**
   - Describe the verifier.
   - Account for witness length and verification time.
   - Flag any nonuniform advice, promise, oracle, or semantic-choice dependency.

5. **How would a `PpolyDAG` decider for `L` yield a bounded solver?**
   - Give the contrapositive extraction step in detail.
   - Identify the bounded solver output type and bound.
   - Explain whether the extraction is constructive, nonuniform, or uses choice.
   - State exactly where the `PpolyDAG` decider is used.

6. **Why is this not just `VerifiedNPDAGLowerBoundSource` in disguise?**
   - Compare your assumptions with the fields of `VerifiedNPDAGLowerBoundSource`.
   - Explain why no hypothesis already asserts `L ∈ NP ∧ ¬ PpolyDAG L`.
   - Reject any route that hides `¬ PpolyDAG` in a promise/certificate.

7. **Natural Proofs audit.**
   - Does the proposed argument define a large, constructive property of Boolean
     functions/circuits?
   - If yes, explain why it is not a Razborov--Rudich-natural property or mark
     the route RED-light / INCONCLUSIVE.
   - Check against the support-cardinality and syntactic-filter failures in
     `NOGO-000001` through `NOGO-000009`.

8. **Relativization audit.**
   - Identify any step that would relativize to arbitrary oracles.
   - Explain why the claimed conclusion would not contradict known
     relativization barriers, or mark the route RED-light / INCONCLUSIVE.

9. **Algebrization audit.**
   - Identify any algebraic extension, low-degree encoding, or black-box
     simulation step.
   - Explain why the claimed conclusion avoids algebrization barriers, or mark
     the route RED-light / INCONCLUSIVE.

10. **Hidden hardness / circularity audit.**
    - Check for assumptions equivalent to `SearchMCSPMagnificationContract`,
      `VerifiedNPDAGLowerBoundSource`, `ResearchGapWitness`, or
      `NP_not_subset_PpolyDAG`.
    - Check for fields of the form
      `weakLowerBound → VerifiedNPDAGLowerBoundSource`.
    - Check that no refuted support-bounds route is being reused under a new
      name.

11. **Verdict and recommended next action.**
    - End with exactly one verdict: `GREEN-light`, `RED-light`, or
      `INCONCLUSIVE`.
    - If `GREEN-light`, list the minimum Round 1 authorisation needed.
    - If `RED-light`, name the fatal obstruction.
    - If `INCONCLUSIVE`, name the missing definitions or audits required before
      any Round 1.

## What counts as fake progress

Reject any proposal that does one of the following:

- assumes `SearchMCSPMagnificationContract`;
- assumes `VerifiedNPDAGLowerBoundSource`;
- assumes `ResearchGapWitness`;
- adds a field `weakLowerBound → VerifiedNPDAGLowerBoundSource`;
- hides `¬ PpolyDAG` inside a promise/certificate;
- uses refuted support-bounds routes;
- claims endpoint progress.

## Forbidden scope

- No Lean code.
- No JSONL edits.
- No spec edits.
- No `known_guards` edits.
- No trust-root edits.
- No `SourceTheorem`.
- No `gap_from`.
- No `ResearchGapWitness`.
- No endpoint.
- No `P≠NP` claim.
- No full Round 1.

## Commands

Run:

```bash
./scripts/check.sh
```

Optional, if useful and time permits:

```bash
lake build PnP3 Pnp4
```

## Required output format

End your worker response with:

```text
Task: source_search_contract_expansion_D0 skeleton
Branch: main
Commit before:
Commit after:
Changed files:
Skeleton created: yes/no
D0 only: yes/no
Commands run:
Scope violations:
```
