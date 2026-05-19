Task: global hInDag contract L0
Handle: codex53
Status: YELLOW_PARTIAL_LANDING

Summary:
- Implemented Pieces A, B, C in `pnp3/Tests/GlobalHInDagContractProbe.lean`.
- Attempted Piece D via transport through `ppolyDAGOnSlicesEventually_of_globalWitness_atCanonicalLengths`, but Lean type/field mismatches blocked kernel-check.

Blocking details:
- `GapSliceFamilyEventually.sliceEq` field does not exist (must use theorem-level coherence/slice lemmas instead).
- Polynomial-bound proof obligations for a global `PpolyDAG` witness were underconstrained with current direct construction.
- Namespace closure error triggered after unresolved goals.

Verdict:
YELLOW_PARTIAL_LANDING

Next action:
open_global_contract_L1_complete_projection
