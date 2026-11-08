# Solver-to-DAG construction: checked component slice

This separate Infrastructure addon targets the exact solver-to-recognizer endpoint
in the accompanying author checkpoint's TARGET.md. The full arbitrary-k bridge is
**unfinished**. There is no proof of R, lower bound, novelty or uniform algorithm.
The optional lengthwise interface and direct R route are unchanged and separate.

Let N=2^n and W=(bitLength n+4)(n^k+k). The imported source context is the
standalone package's `core` Lake srcDir, not an interchangeable root pnp3 copy.

* `Attempt.Equality`: actual Boolean DAG equality of two w-bit vectors (size 6w+3),
  including w=0; equality of two physical truth tables is its specialization.
* `Attempt.Assembly`: copies each of the W real solver-output DAGs once into a
  bundle and composes an actual head graph with passthrough input bits. Exact
  semantics and size <= size(head)+W(N^d+d) are proved. The whole solver bundle,
  including its output convention, has a closed polynomial bound for fixed k,d.
  The head is a graph parameter, **not** an assumed verifier-existence field.
* `Attempt.Leaves`: table matching uses 7N+3 size including constants. A real
  recognizer for size-one TREE formulas has size 2+(n+2)(7N+3), exact semantics
  on every table, and checked domination by N^e+e for all n. This is k=0 only.
* `Attempt.Fixtures`: n=0 constants, n=1 projection/NO negation, empty vectors,
  and malformed concrete-codec source decoding. The decoder fixture is not a
  circuit implementation of decoding and cannot prove arbitrary-NO rejection
  for the missing full bridge.
* `Attempt.Surface` and `Attempt.Audit`: full proposition mirrors, type/arity pins,
  complete owned declaration-set checking and direct axiom roots. These check
  signatures and dependencies, not independent proofs/review or model adequacy.

Remaining executable import boundary: construct the bounded concrete prefix
parser (with its actual ignored-tail semantics), validity/size check and decoded
TREE evaluation on all N assignments as a Boolean DAG. Prove its all-bit-string
semantics and polynomial gate bound. Only then can composing it with the solver
prove the arbitrary-k YES and arbitrary-NO recognizer capstone. Existing source
`codec.decode` and `BoundedContentSemanticVerifier` do not supply that DAG bound.
No recognizer/size premise is inserted to hide this obligation.

## Local verification

`python3 -B check.py --core /verified/installed-core --output /fresh/private/attempt`
compiles the exact owned modules with warnings-as-errors and fresh private import
object overrides. It performs no Lake build, update, cache acquisition or network.
It requires the caller's admitted execution wrapper: global SH then lane-a EX
locks exactly once, CPUs 0,1, >=5GiB free disk and available RAM, pinned Lean
4.22.0-rc2, clean Lean path/toolchain environment, and two Lean threads. Reused
verified core/dependency objects remain read-only. This is not a cold core build
or a sandbox for hostile source. Never rerun into an existing output directory.

The author checkpoint records actual execution, including failures, separately.
No compilation of this slice constitutes independent review, full bridge,
standard-model reconciliation, native CI, publication or release approval.
