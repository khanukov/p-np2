# Implicit assumption channels — Rule 16 detection spec

This document specifies how the verifier detects hidden mathematical
assumptions in candidate code. It is the operational counterpart to
**Rule 16** of `RESEARCH_CONSTITUTION.md`.

The detection runs over candidate-local files only:

```
pnp3/Candidates/<method>/<id>/**.lean
```

It also runs over the **dependency closure** of `SourceTheorem_<id>` and
`gap_from_<id>` restricted to candidate-local code (everything outside the
trusted boundary defined in `spec/source_theorem_size_policy.md`).

---

## 1. Hard-rejected declarations (in candidate-local code)

A candidate is **automatically rejected** if any of the following
declarations occur in candidate-local code:

| Declaration form                           | Reason                                |
| ------------------------------------------ | ------------------------------------- |
| `class ... where`                          | Hidden payload via typeclass          |
| `instance ... :=` / `instance ... where`   | Provider supplies the math silently   |
| `default_instance`                         | Auto-payload selection                |
| `attribute [instance] ...`                 | Same, indirect                        |
| `opaque ...`                               | Hides definition behind seal          |

The rule applies regardless of whether the declaration is exported.

> Exception: if the candidate genuinely needs `Decidable`/`DecidableEq`/
> `Inhabited`/`Fintype`/`Repr`/`Coe` instances over **non-frozen** infra
> types (e.g. `Bool`, `Nat`, `Fin n`, candidate-local `Vector`s), the
> candidate may add them in a separate file `proof.instances.lean` listed
> in `manifest.toml::[whitelisted_typeclasses]` and individually
> justified. The verifier still requires the typeclass to be in the
> whitelist of §3 below.

---

## 2. Soft-flagged declarations (require human review)

A candidate is **flagged for human review**, not auto-rejected, if it
contains any of the following:

- `noncomputable def` whose **name** matches the pattern
  ```
  .*(Provider|Default|Payload|Witness|Source|Gap).*
  ```
- `Fact <P>` arguments anywhere in the statement of `SourceTheorem_<id>`
  or `gap_from_<id>`.
- Implicit arguments in `SourceTheorem_<id>` whose type involves any
  identifier listed in `spec/target.toml::[frozen_identifiers]`.

Soft flags consume the human-review queue (Rule 7).

---

## 3. Whitelist of allowed typeclasses

A candidate may rely on instance synthesis **only** for the following
typeclasses, and **only when the type is from `Core` or the stdlib**:

```
Decidable        DecidableEq
Inhabited        Nonempty
Fintype          Finite
Repr             ToString
Coe              CoeHead   CoeTail
Add  Mul  Sub  Neg  Zero  One     -- algebraic instances on Nat/Int/Bool only
LE   LT   Ord   PartialOrder      -- order instances on Nat/Int/Bool only
```

A typeclass instance over any of the following types is **rejected**, even
if the typeclass itself is in the whitelist:

- `ComplexityInterfaces.PpolyFormula L` for any `L`
- `ComplexityInterfaces.PpolyDAG L` for any `L`
- `ComplexityInterfaces.NP_not_subset_PpolyDAG`
- `ComplexityInterfaces.P_ne_NP`
- `ResearchGapWitness`
- any type defined in `pnp3/Spec/FrozenSpec.lean`
- any type defined in `pnp3/Magnification/`
- any type defined in `pnp3/LowerBounds/`

This list mirrors Rule 0.

---

## 4. Forbidden identifiers in candidate code

These identifiers must **not appear** anywhere inside
`pnp3/Candidates/<method>/<id>/`:

```
FinalPayloadProvider
AsymptoticPayloadProvider
FormulaCertificateProviderPartial
FormulaSemanticMultiSwitchingProvider
AC0FamilyWitnessProvider
LocalCircuitFamilyWitnessProvider
AC0MultiSwitchingWitnessProvider
ResearchGapProvider
hasDefaultFormulaSupportRestrictionBoundsPartial
hasDefaultAsymptoticFormulaTrackData
```

This list is mirrored in `spec/target.toml::[hidden_payload_channels]`.
Updating it is a Foundational PR (because adding a name here is admitting
a new payload channel exists).

---

## 5. `pp.all` rendering

The verifier renders both

- `SourceTheorem_<id>` and
- `gap_from_<id>`

with `pp.all := true`, and stores the rendered text in the candidate's
verifier output. The check then asserts:

1. No identifier in the rendered text appears in the list of §4.
2. No implicit-argument typeclass in the rendered text fails the §3
   whitelist.
3. No frozen-target type appears as a typeclass parameter.

If `pp.all` rendering itself fails (e.g. due to elaboration errors), the
candidate is rejected, not soft-flagged.

---

## 6. Verifier output contract

For each candidate, the verifier emits a JSON record of the form

```json
{
  "candidate_id":               "...",
  "rule_16_passed":             true,
  "hard_rejected_decls":        [],
  "soft_flagged_decls":         [],
  "forbidden_identifiers_seen": [],
  "typeclass_violations":       [],
  "pp_all_paths": {
    "source_theorem": ".../SourceTheorem_<id>.pp_all.txt",
    "gap_bridge":     ".../gap_from_<id>.pp_all.txt"
  }
}
```

A `false` value of `rule_16_passed`, or any non-empty list except
`soft_flagged_decls`, is a verifier **FAIL** (not a soft flag).
