# L0 global hInDag contract report (codex53)

- Classification: Infrastructure (contract surface repair/probe).
- Landed pieces: A, B, C, D (general form).
- Piece D style: global family projected to slice-local `InPpolyDAG` by active-length selection and `constFalseDag` off-slice.
- Anti-hardwiring lemma: deferred.
- Audit grep: no forbidden tokens matched in staging file.
- Check: `./scripts/check.sh` executed successfully in this environment (long build with pre-existing warnings outside this patch).

## Notes

The file `pnp3/Tests/GlobalHInDagContractProbe.lean` introduces the global witness contract and its forward projection without importing the prior triviality probe; all constructions are local to the staging file.

Verdict: **RED_GLOBAL_CONTRACT_CORE_LANDED**.
