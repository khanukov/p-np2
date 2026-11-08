# Concrete solver-to-DAG construction

This optional Infrastructure addon constructs the actual recognizer conditionally
from the existing concrete bounded search solver. `Codec.solver_to_dag_capstone`
in `Attempt/Codec.lean` states the literal arbitrary-k endpoint. Source-author
execution and pending independent review are recorded separately in the author
checkpoint; this README supplies no independent acceptance or release claim.
R remains UNPROVED. No lower bound, novelty, weaker hypothesis, new solver,
uniform algorithm or standard-model equivalence is established. The direct R
route, optional lengthwise interface and other research routes remain separate.

For fixed k,d and EVERY solver `ConcreteSolver k d`, the construction builds a
real single-output `DagCircuit N`, N=2^n, for every n. It accepts exactly
`treeMCSPPredicate n (n^k+k)` on every physical table. Solver correctness is used
only on YES promise inputs. On NO inputs the solver may emit arbitrary bits;
the constructed decoder/evaluator rejects every invalid purported witness.

## Construction and price

The authoritative imported source is the installed package's `core` Lake srcDir.
`Attempt.Equality`, `Assembly` and `Leaves` retain the previously checked equality,
per-output solver wiring and k=0 components. The successor adds:

* `Prefix`: bounded raw prefix-word comparisons as Boolean DAGs.
* `Parser`: memoized bottom-up actual native grammar parsing, size and evaluation.
  Nodes are ordered before start/end cursors and the evaluation bit. Each row is
  appended once; prior rows are shared wires. It implements input/const/not/and/or,
  little-endian bounded input indices, truncated/invalid-tag rejection and exact
  cursor returns. No Lean observer decoder is substituted for a graph.
* `Codec`: an accepted-native-parse inverse, exact decoder/DAG agreement, real MUX
  selection using the input table bit at every one of the N assignments, whole
  table equality and actual solver-output composition. Trailing unused witness
  bits are permitted exactly as the existing concrete codec permits them.
* `Fixtures`: empty witnesses, malformed tag 111, n=0 and n=1 boundaries, a genuine
  two-node negation witness and wrong-table rejection. These are kernel fixtures,
  not an exhaustive computational enumeration of witness strings.

Let b=bitLength n, T=n^k+k, W=(b+4)T and r=2(T+1)(W+1)^2. The checked price is

```
B = r*(60+n*(2*b+11)+48*r*(W+1))+(T+1)*(W+1)+2
size(recognizer) <= N*(2*B+6)+3 + W*(N^d+d).
```

This includes the single output convention (+1), both truth-value parser graphs
at each assignment and EVERY solver-bit graph (the solver bound is per output,
not total). Checked growth lemmas yield an exponent e depending only on fixed
k,d such that size <= N^e+e for ALL n, including 0 and 1 and k=0. There is no
structure/provider field assuming a verifier, recognizer, semantics or size bound.
`Surface` restates all public propositions and full definition types. `Audit`
checks the exact imported owned declaration set, prints every direct root and
allows only propext, Classical.choice and Quot.sound. Internal/generated roots
are reported too; these checks do not establish model adequacy or novelty.

## Local verification

Run from this addon using caller-chosen fresh private storage:

```
python3 -B check.py --core /verified/installed-core --output /fresh/private/attempt
```

The caller must supply the admitted wrapper: global SH then lane-a EX locks once,
CPUs 0,1, >=5GiB free disk and available RAM, Lean 4.22.0-rc2, clean Lean path and
toolchain environment, two Lean threads. The driver compiles every owned module
with warning-as-error and fresh private import overrides, then audits the roots.
It performs no Lake build/update/cache acquisition/network. Verified base objects
are reused read-only: this is not cold core verification or a hostile-code sandbox.
An existing output is rejected. Actual failed and successful attempts remain in
the author checkpoint. No source checkpoint authorizes Git publication or merge.

### Installed-core bootstrap identity

Before executing any installed workbench Python, `check.py` checks the exact
workbench bytes and complete package inventory against the reviewed public
`khanukov/p-np2` snapshot `1180e5e0ffe760bbc3a1c70143ec09b362d33a8e`.
It executes the same authenticated byte buffer, with standard-library bootstrap
imports only; a caller-supplied inventory cannot authorize a different loader.
The normal complete `verify_core` check still precedes attempt creation and is
repeated after compilation. The inventory also binds `tools/SourceImports.lean`.
A different installed version needs a separately reviewed pin update.

The core must already be independently trusted and remain immutable throughout
execution. This narrow bootstrap guard is not an arbitrary-code sandbox or a
transactional filesystem defense against concurrent replacement of core files.
It does not authenticate Python, its standard library, Lean or external tools.

Discoverable stdlib DATA regressions: `python3 -B -m unittest discover -s . -p test_bootstrap.py`. Set
`SOLVER_DAG_TEST_CORE` to the pre-trusted installed core to exercise the positive
identity and optimization cases too; those cases explicitly skip if omitted.
Use caller-owned `TMPDIR` and `PYTHONPYCACHEPREFIX` for all fixture/bytecode output.
Inert substitution seams test loader ordering and same-buffer execution, not Lean
acceptance, observed exploitation or general hostile-installation safety.

## Optional decision lower-bound interface (Infrastructure)

`Attempt/LowerBound.lean` defines `FixedKTreeMCSPDAGExclusion k`. In full:

```text
forall e, exists n, forall c : DagCircuit (2^n),
  size(c) <= (2^n)^e + e -> exists tt : TruthTable n,
    not (eval(c,tt) = true iff treeMCSPPredicate n (n^k+k) tt).
```

`TreeMCSPDAGLowerBound` is `exists k, FixedKTreeMCSPDAGExclusion k`: ONE k is
chosen before every excluded degree, and each small circuit has its own table
counterexample. The input length is N=2^n; size includes the output +1. This is
exact TREE-MCSP at threshold n^k+k, not an arbitrary language or a prefix solver.
No lower bound is established. We do not claim equivalence, weaker/easier
hardness, novelty, a uniform algorithm or unconditional P!=NP.

`fixedK_excludes_solver` uses `Codec.solver_to_dag_capstone` to contradict any
`ConcreteSolver k d`, whose size bound is PER witness-output bit and correctness
is promised only on YES inputs. The capstone's recognizer is nevertheless correct
on ALL tables. `lowerBound_implies_R` packages the same k into the literal
installed `ConditionalSeparation.OpenProblem.R`. Surface independently restates
both full propositions; Audit checks the added exact roots and standard axioms.
Direct R and LengthwiseR sources/APIs remain unchanged. The new hypothesis is
another optional sufficient assumption, not the missing lower bound itself.

## Dedicated optional-addon CI

The proposed `.github/workflows/solver-to-dag.yml` is independent of existing
root CI/Lean CI. It triggers on relevant addon/core/workflow pushes on ALL
branches and main-target PR opened/synchronize/reopened/edited events, including
retargeting. One standard Ubuntu job has contents:read and no persistent runner.
Its JSON-subset YAML syntax permits strict local stdlib parsing; local JSON,
context and bash checks do not claim an actual GitHub-hosted run.

The job installs hash-pinned elan4.2.4 and exact Lean4.22.0-rc2, materializes the
unchanged standalone lock (no lake update), verifies dependency Git revisions and
gets pinned external Mathlib cache. It then builds only the source dependency
closure of `+Complexity.DagGadgets` and `+ConditionalSeparation.OpenProblem` in
`conditional_separation`, not root PnP3/Pnp4 or the entire ProofCore library.
No standalone project objects are admitted from the foundation-cache step.

`ci_runner.py --core /verified/built/core --output /NEW/private/output` requires
the same caller lock/resource scope as check.py. It sets SOLVER_DAG_TEST_CORE to
that actual admitted core and runs exactly the existing nine bootstrap test IDs;
any skip, missing/extra ID, failure, error or missing report fails BEFORE Lean.
It then invokes the REAL check.py, validates its actual exit, complete module
and source roster, command terminals, COMPONENT_RESULT and matching root stdout.
The separate `test_ci_runner.py` DATA suite does not inflate those nine tests.

The workflow takes global SH then lane-a EX once, CPUs0,1, two Lean threads and
checks >=5GiB disk/MemAvailable before source builds and addon compilation.
All temp/output is private; upload always selects only owned `artifacts` and
build-evidence logs, never downloaded archives, credentials, core caches or SDK.
Artifacts retain test IDs/outcomes, actual check stdout/stderr/terminal, source
pins and compiler/import/axiom evidence; private compiled objects stay outside
the upload paths. Missing COMPONENT_RESULT/terminal is failure even after exit0.
The author's local admitted-object replay is NOT a hosted/cold core build.
Fresh exact-head hosted acceptance, independent reviews and publication remain
separate gates. This source change supplies no main-merge or release authority.
