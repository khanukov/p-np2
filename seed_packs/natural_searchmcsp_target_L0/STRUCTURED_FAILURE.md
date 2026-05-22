# natural SearchMCSP target L0 — structured failure

## Outcome

**STRUCTURED_FAILURE_CODEC_NOT_READY**

This L0 requested a pinned closed constant

```lean
naturalTreeSearchTarget : SearchMCSPWeakCircuitLowerBoundTarget
```

with all components fixed (threshold schedule, sizeBound schedule, concrete
encoding/codec object, and `C_DAG`).

A closed target constant cannot be produced honestly at this point because a
concrete `TreeCircuitWitnessCodec` object is not present in the repository.

## 1) Exact threshold schedule (proposed)

`threshold(n) := n + 1`.

## 2) Exact sizeBound schedule (proposed)

`sizeBound(n) := n ^ 2 + 1`.

## 3) Exact encoding / codec object status

`treeMCSPSearchWeakLowerBoundTarget` needs
`TreeMCSPSearchWitnessEncoding threshold`, and the concrete route in
`SearchMCSPConcreteTargets.lean` builds that from
`TreeCircuitWitnessCodec threshold` via `TreeMCSPSearchWitnessEncoding.ofCodec`.

A concrete codec object with fields `witnessBits`, `encode`, `decode`, and
`decode_encode` is not currently available as a repository constant for this
natural target pin.

## 4) Named target constant

Not landed, because a closed target constant depends on a closed concrete codec
object that is currently unavailable.

## 5) Surface tests

No `#check` / `#print axioms` additions, because no new target constant was
introduced.

## Minimal next unblock

Land one concrete codec object first; then pin:

```lean
def naturalThreshold : Nat → Nat := fun n => n + 1
def naturalSizeBound : Nat → Nat := fun n => n ^ 2 + 1

def naturalTreeSearchTarget : SearchMCSPWeakCircuitLowerBoundTarget :=
  treeMCSPSearchWeakLowerBoundTarget
    naturalThreshold
    (TreeMCSPSearchWitnessEncoding.ofCodec (naturalTreeWitnessCodec naturalThreshold))
    ContractExpansion.C_DAG
    naturalSizeBound
```
