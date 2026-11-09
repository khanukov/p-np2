"""Deterministic DATA protocol only. Never a real model or search measurement."""
import json
import sys
import time
from pathlib import Path

TRUE_PROOF = '''intro n budget h
refine ⟨Pnp3.ComplexityInterfaces.DagCircuit.constCircuit n true, ?_, ?_⟩
· simpa using h
· intro x
  exact Pnp3.ComplexityInterfaces.DagCircuit.eval_constCircuit true x'''
FALSE_PROOF = '''intro h
have bad := h 0 2 (by decide) (Pnp3.ComplexityInterfaces.DagCircuit.constCircuit 0 false) (by simp) (fun i => Fin.elim0 i)
simp at bad'''


def main():
    mode, request, response = sys.argv[1:]
    d = json.loads(Path(request).read_text())
    if mode == 'timeout':
        time.sleep(10)
        return
    if mode == 'missing':
        return
    body = 'exact True.intro'
    if mode == 'repair' and d['round'] > 0:
        body = FALSE_PROOF if d['polarity'] == 'refute' else TRUE_PROOF
    Path(response).write_text(json.dumps({'proof': body})+'\n')


if __name__ == '__main__':
    main()
