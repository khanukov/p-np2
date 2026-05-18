# check.sh coordinator flake note — hInDag triviality probe D0

Command:

```sh
./scripts/check.sh
```

Observation:

- A full `./scripts/check.sh` run completed successfully once after the markdown report was initially created; the only later report edit was appending the report-generation command to the report's own "Commands run" inventory.
- Two subsequent reruns reached Step 12.e (`coordinator/test_coordinator.py`) and failed with:

```text
ConnectionResetError: [Errno 104] Connection reset by peer
```

- The failure happened in the coordinator HTTP-service e2e parallel result submission path, after the Lean build and source-hygiene/doc-honesty/refuted-route guards had already completed successfully.
- Because this task changed only markdown/failure-note files and no Lean/source/JSONL/spec files, this is recorded as an environment/flaky coordinator-service limitation rather than a code regression from the report.

Base-HEAD confirmation attempt:

```sh
rm -rf /tmp/p-np2-base-check && git worktree add --detach /tmp/p-np2-base-check ac96653ef5115bb407b3c1ca3137000c0758dabf && cd /tmp/p-np2-base-check && ./scripts/check.sh
```

This attempted detached-HEAD confirmation began by cloning/rebuilding dependencies in the fresh worktree and was terminated to avoid spending more time on an unrelated cold-cache rebuild.  The earlier successful full run plus the repeated identical coordinator `ConnectionResetError` on the unchanged working tree are the available evidence for non-regression.
