# Conditional Separation research workbench

This source package exposes one exact, substantial **unproved** circuit-search
lower-bound proposition, `ConditionalSeparation.OpenProblem.R`. Its conditional
consequence is proved by the copied accepted core: one and the same fixed
threshold codec/language is in Ordinary NP, outside canonical DAG P/poly, and
outside Ordinary P. No assumption-free P-versus-NP separation theorem, novelty, nonvacuity or
successful proof of R is claimed. The legacy differently typed
ContentVerifierBridge remains unfilled and outside this direct route.

Read the [research note](PROOF_MAP.md#research-note) for the exact mathematical
premise/language and the [partial-work guide](#partial-work-across-machines)
for source-only exchange between independent installed core roots. The guide's
compiler commands are verification instructions, not an execution/acceptance claim.

## Install and build

Install Lean via elan and Python 3.10 or newer. From this directory run:

```sh
lake build
python3 ci/run_data_tests_v2.py
# Optional native compiler rejection suite in a separate fresh template:
# python3 tools/workbench.py new /path/to/validator-tests --core .
# Install its pinned dependencies through Lake or a verified external cache.
# python3 tests/lean_rejections.py --attempt /path/to/validator-tests
```

The toolchain is Lean 4.22.0-rc2. Mathlib and every transitive dependency are
pinned by `lake-manifest.json`; initial dependency acquisition needs network
access or an independently verified external cache. No monorepo source/object
path is a package dependency. `ConditionalSeparation.LightAudit` checks the exact
problem equivalence without importing the heavy final theorem;
`ConditionalSeparation.KernelAudit` checks eight named endpoint roots. Its imported `Pnp4.Tests.AxiomsAudit` retains the four bridge mirrors and imports `Pnp4.Tests.FullPublicSurfaceTests`: 72 separately owned audit modules cover the 2093 public logical constants in the original 72 Pnp4 modules, including generated auxiliaries, with literal complete type pins and direct axiom roots. It adds 1157 full-proposition theorem mirrors and reuses the existing matched bridge/final mirrors without an infinite mirror-of-mirror obligation. Twelve public audit-support definitions have separate complete type pins and direct roots. A transparent topologically ordered shared literal table reconstructs every independently frozen complete contract; reference notation never looks up a target type as its expectation. Compiler-generated literal types preserve binders, universe arrays, private constant identities and full proof-dependent premises; generated mirror authorship is not an independent semantic reproof. `core/` preserves original module names, private
identities and source bytes. PROVENANCE.json v2 maps all 1062 copied core files
by path, byte count and SHA256 directly to the public repository
`https://github.com/khanukov/p-np2.git`, exact snapshot
`c96d9d72c99120e3775437414417505fd4904a3d`. Each `source_relative` is exactly
`conditional_separation/` plus the installed `core/...` path. The original
`donor_relative` pnp3/pnp4 paths and historical donor
`e5dbbe7fd6dee72ae3c3b31a84b54fc1b2727f8f` remain recorded as LOCAL/NON-PUBLIC
origin; fetching that old donor from the public remote is not a supported route.
The public snapshot permits byte reproduction, not an independent demonstration
of historical review acceptance, novelty or a proof of R. `verify-core` checks
local source/schema/inventory identity; it does not fetch or authenticate a remote.
To reproduce the core independently, retrieve the exact public snapshot, compare
every listed `source_relative` byte count/SHA256, and check the installed mapping:
`python3 -B tools/workbench.py verify-core --core .`.
LICENSE is copied verbatim from the donor; extraction creates no new licensing
permission. Copied, newly authored and retired source are accounted separately. The task-specific source-size limits were prospectively removed; historical HOLD records are preserved.

The original Linux source tuple has completed independent cold-source
reproduction: 1069 fresh owned-source compilations/headers, 4360 admitted reused
foundations, eight public roots with standard axioms, the installed full
conditional consumer, three generic True successes and nineteen rejected invalid
attempts without a core rebuild. The original resumed objects matched the cold
objects byte-for-byte. These completed ORIGINAL-tuple results do not certify
this new installed/head tuple or native macOS. No build occurs as part
of this local source-installation invocation. Windows is not a CI or release-validation target;
native Windows support is not claimed.

Audit roles differ: compiling Audit.lean alone elaborates its named mirrors/type
pins and prints seven axiom roots; printing does not enforce an allowlist.
LightAudit checks three direct roots and KernelAudit checks eight, rejecting
missing roots or transitive axioms outside propext, Classical.choice and Quot.sound.
The native build's `fresh-public-root-audit` command compiles
`ConditionalSeparation/KernelAudit.lean` with `-DwarningAsError=true` and rejects a
nonzero compiler exit. Enforcement comes from that module's `run_cmd` guards,
not from treating Audit.lean's printed output as a fail-closed check. These
elaboration/axiom checks are not independent reproofs or a proof of R.

## Independent attempts

After building an installed copy of this core:

```sh
python3 tools/workbench.py new /path/to/attempt --core /path/to/installed/core
cd /path/to/attempt
lake build Attempt
python3 /path/to/installed/core/tools/workbench.py check . --proof Attempt.research_lower_bound
```

The starting template is PARTIAL and contains NO proof named
`Attempt.research_lower_bound`. Its final check must reject it today. A successful
attempt needs a named CLOSED declaration of EXACT type OpenProblem.R. A theorem
R -> R, an implicit extra premise, a different degree/k order, an assumed False,
or a custom axiom is not such a proof. Failed attempts remain separate projects.
The public provenance snapshot is a source anchor, not a Lake Git dependency;
attempts still use an explicit local installed source package.

The checker recompiles every own attempt module from source to fresh private
outputs, orders literal imports with Lean's own parser, and overrides all own import
artifacts. Compilation uses the verified installed core's Lake workspace, never
an attempt's Lake configuration or stale own object path. Own modules must be
`Attempt` or `Attempt.*`; declaration namespaces may be independent. It checks the
constant's full type against the explicitly imported installed R (including its
actual module owner, declaration kind and universe arity), and audits transitive axioms against exactly propext,
Classical.choice and Quot.sound. Only after that gate does it construct the full
same-language final consumer with a named full-proposition mirror. Actual compiler
stdout/stderr, source snapshots, setups, selected parts and terminals survive
under the attempt's .lake/conditional-check directory. No genuine proof of R is
available, so no positive R/final-unconditional integration test is fabricated.
Generic True validator fixtures test the checker only and are labeled internal.
The native suite rejects decoy R namespaces and installed-module shadowing,
and checks fresh commented imports while an invalid attempt Lake configuration
is ignored. The portable native suite also compiles deliberately rejected custom-axiom,
sorry and native-decision fixtures in the separate attempt to test the kernel
audit. Those fixtures are never library assumptions or proofs of R.

This is a source/provenance workflow for trusted research code, NOT a hardened
sandbox for arbitrary Lean metaprograms, plugins, forged installed objects or
adversarial concurrent filesystem mutation. Run untrusted code in an appropriate
separate security boundary. A compatible installed core cache is reused for
iteration; cold source build/replay remains the reproducibility authority.

## Research statement

There EXISTS ONE fixed k such that FOR EVERY degree d there is no nonuniform
bounded search solver for the concrete tree-circuit witness codec with threshold
n^k+k. Inputs are full truth tables (length 2^n). Each witness output bit has its
own canonical DAG circuit, separately bounded by (2^n)^d+d. Correctness is required
ONLY on the promise of a small tree circuit. The codec's unused tail is ignored;
consumed syntax and index validity still matter. See PROOF_MAP.md and the explicit
Lean definition; a different language for each excluded degree is insufficient.

The research lower bound is not proved easier than P != NP, is not an established
weak-bound magnification result, and is not claimed equivalent to the final
conclusion. No broad external-model equivalence is asserted. Independent exact
source/model/control reviews and all release/owner/CI gates remain separate.

## Installed native CI route and validation status

The repository workflow `conditional-separation-native.yml` and the identical
packaged proposal `ci/conditional-separation-native-v2.yml` are now installed
locally. Installing or presenting these workflow sources alone establishes neither an
executed GitHub workflow, exact-head kernel/native validation nor PR/release
acceptance.

The standard matrix is Ubuntu 24.04 x64 and macOS 15 ARM64,
up to two jobs in parallel. Pure asset-selection tests additionally cover
Linux ARM64 and macOS Intel metadata; those extra native jobs are deferred.
The proposed trusted-control route uses a push only on the existing remote feature
`infrastructure/conditional-separation-package-docfix-20261031` in khanukov/p-np2,
after independent exact control/workflow review and
publication admission. It does not execute a PR-supplied workflow definition as
a trusted controller. The same two native jobs and their resource limits remain.
Optional workflow_dispatch accepts exact controller_sha and source_sha inputs;
the controller must equal both GITHUB_SHA and GITHUB_WORKFLOW_SHA. Its source
head may differ, but must be in this same public repository. The parent must
independently join it to current PR1821; a job name or user input is not that join.
No main modification or default-branch dispatch discovery is assumed: the
explicit reviewed feature-push route is available without that prerequisite.
This replaces the old automatic PR-event policy; it is not a new required local
691 build or another executor. Root17/fullrepo and all existing final gates remain.
The publisher, independently reviewed immutable controller SHA and workflow
policy are trust roots. A PR-context job with the same name is not this gate.

Automatic runs are limited to this existing authorized feature branch.
There is no automatic native CI for main or later PRs. Subsequent use requires
independently admitted exact controller/source manual dispatch on a non-main branch,
with the same immutable SHA, current PR1821 source and parent/owner authorization
joins; selecting the inputs does not supply that authorization. There is
no promise after branch deletion or merge: the reviewed workflow must still be
available at the explicitly selected non-main controller revision. Future main
regression coverage is outside this feature-only scope; no main trigger,
schedule, installation or workflow dispatch is added here.

The older `ci/conditional-separation.yml.proposed` source-execution recipe is
retired. Its only prospective job is a fixed hosted refusal with no checkout,
source execution, bootstrap, installer or tests. It exits nonzero regardless of
the selected branch. It is not installed and is not an alternative native build;
the admitted, pinned controller route above remains the Linux/macOS executor.

The controller fetches its two authenticated admission helpers from its exact
controller revision, then independently fetches the exact tested source head.
The raw-blob materializer and Python/artifact actions remain hash/commit pinned.
ci/trusted_controls_v1.py has an external workflow SHA256 anchor; its literal
manifest digest authenticates the complete helper/test/configuration input set.
A PR-supplied PACKAGE_FILES.json or trust manifest cannot promote new controls.
Unknown/missing/aliased/hardlinked controls and bytecode directories reject.
Every Python control is executed from authenticated byte snapshots, including
normal imports, explicit file imports, native subprocess entries and the exporter.
Original __file__/filename semantics keep the tested package bound to its own
source head. Native child ownership/reaping remains the original command runner.
All theorem bytes, registered roots, source options and R/type/axiom guards stay
unchanged; the trusted tuple also pins public/audit inputs and existing provenance.
Updating those frozen control/model inputs requires a newly reviewed tuple.
This assumes a trusted interpreter/stdlib and no hostile concurrent host mutation;
it is not a general OS sandbox/attestation for arbitrary native code.
The CI driver verifies the selected Elan archive digest/size before extraction
and execution, then checks the exact Lean 4.22.0-rc2 version. It does not provide
independent Lean-download digest attestation. Declared external foundations may
reuse compatible cache objects; project sources build without a project-object
cache. It runs source build, root audit, Python unit tests, exact-R rejection
attempts and an installed-source conditional consumer/cache-identity check.
No positive proof of R is supplied or expected. Generic True validator success
is not a proof of R.

Portable source ZIP extraction permits at most 2,048 members, 16 MiB per member,
and 64 MiB total uncompressed payload. The complete exact92fb package has 1,180
members and 17,689,864 bytes including its inventory: margins are 868 members
and 49,419,000 bytes. Every declared size/type and the total are checked before
the first member read; actual returned bytes must also meet the cumulative cap
and each declared size. Inventory/digest/name-set checks still precede destination
creation. These bound retained payload, not total process RSS, compressed input,
ZIP-parser metadata or Python-object overhead. Finite DATA tests exercise budget
boundaries and complete current-package extraction; they do not observe an OOM
or establish native/installation acceptance.

The proposed native layout uses genuinely short runner-private `s/p` source,
`g` bare Git and `w` work directories under `RUNNER_TEMP`, with no source alias or
registry change. Before compiler dispatch it checks physical source/head pins and
all 1146 prospective owned module paths (the original 1069 plus the separately owned audit additions).
Shared offline path and archive-safety fixtures retain foreign-path rejection cases;
these do not create a Windows job or a Windows release requirement.
The real Linux/macOS native result remains a separate exact-head gate.

Only explicitly owned receipts/source pins/compiler identity metadata are staged
for best-effort always-on artifact transfer, with seven-day retention. Whole
temporary directories, environments, credentials/config, Git, toolchains,
dependencies, caches and binaries are not uploaded. A killed runner can prevent
staging/upload altogether; missing executor terminals remain UNKNOWN. Artifact
existence alone is not native-validation success. Two 330-minute job allowances
are not a measured runtime, cost or hosted-resource sufficiency guarantee.

For the proposed package, the ordinary portable unit command above exercises
the original workbench tests and ten CI DATA modules:
`test_portable_ci_data_v1`, `test_completion_v2`, `test_native_first_run_v1`,
`test_windows_layout_v1`, `test_locked_foundations_v1`, `test_locked_evidence_v1`, `test_path_archive_hardening_v1`, `test_trusted_controls_v1`, `test_reliability_v1`, and `test_reproducibility_v1`.
Native compiler
rejection tests remain a separate, explicit command; Python DATA is not a native
platform or kernel result. The original Linux cold-source checkpoint alone does not certify another
installed revision. Source review, exact-head build/full conditional consumer/cache
verification, actual native Linux/macOS CI, owner, latest-head Qodo,
raw CI and release acceptance remain separately scoped evidence. No assumption-free P-versus-NP separation, standard-class equivalence, ease or novelty
claim follows. R remains UNPROVED and the legacy bridge remains unfilled.

The portable Python unit runner supplies a fresh private `CI_DATA_ROOT` without
weakening the CI DATA suites' guards. The advertised plain command disables
project bytecode writes before discovery and sets `PYTHONDONTWRITEBYTECODE=1`
for child Python imports; `python3 -B ci/run_data_tests_v2.py` is also supported.
Existing/untrusted `__pycache__` or compiled controls remain rejected: `-B` does
not clean a source copy contaminated by an older run. Recover by taking a NEW
source-only package copy from the exact published revision, then rerun the
command there; preserve the old copy/evidence rather than deleting caches to
make a trust check pass. The finite entrypoint regression uses a synthetic
one-test tuple and the real trust validator, with one child import and no full
suite recursion. Its default temporary directory follows
the platform's normal temporary-directory configuration. To retain fixtures,
pass `--data-root /path/to/new/private-data`; the path must not already exist.
It never runs Lean, Lake or the native operational driver and rejects Python
optimization because ordinary discovery includes workbench tests. Direct
`python3 -B -m unittest discover -s tests -v` remains available when the caller
explicitly supplies an existing private `CI_DATA_ROOT` directory. Native CI's
unit command now uses the runner with its own fresh runner-private path.

## Partial work across machines

Compiling a useful closed lemma is different from proving R. This example
checks the exact threshold at one variable, where `N = 2`: for every `k`,
`thresholdPoly k 1 = k+1`. It is a boundary-case sanity lemma about the actual
threshold, not a lower bound, `True`, or an assumed proof of R. Its second named
theorem restates the arithmetic proposition independently of the threshold
abbreviation. Neither declaration has type R.

**Execution status:** these are runnable verification instructions, not a
claim that the documentation author ran Lean. Parent/recipient execution of
the exact blocks below is required. Read/review shared code first: the workbench
is not a sandbox for arbitrary Lean metaprograms, plugins or hostile packages.

### Preconditions and paths

Use two independently verified, already built installations of this exact
package, with its pinned Lean 4.22.0-rc2 and locked dependencies available
locally. A new attempt does not inherit those dependency checkouts. Compile its
complete single-file `Attempt.lean` from the verified installed core's workspace,
using `--root` and the explicit attempt source path below. This uses the same
installed dependency context as the final checker; it does not run `lake build`
in the new attempt or authorize dependencies declared only by that attempt.
The recipe requires already available dependency/object reuse: it does not
install Lean, fetch dependencies, rebuild a pristine/cold foundation or
authenticate a release. `CORE_A` and `CORE_B` may be on different machines; for
a local transfer check they must be different physical roots with identical
package inventory bytes. They must not be symlinks to one installation.
Source/attempt/check/transfer destinations below must be NEW.

Set absolute paths, for example (substitute your real installed cores):

```sh
export CORE_A=/researcher-a/installed/conditional_separation
export CORE_B=/researcher-b/installed/conditional_separation
export ATTEMPT_A=/researcher-a/new-partial-attempt
export ATTEMPT_B=/researcher-b/new-recipient-attempt
export WRONG_ATTEMPT=/researcher-b/new-wrong-R-attempt
export TRANSFER=/exchange/new-partial-bundle
export CHECK_ROOT=/researcher-b/new-partial-check-logs
# Optional: exact independently verified published PACKAGE revision, not a branch.
# export PACKAGE_REV=<40-lowercase-hex-commit>
# Unset PACKAGE_REV for a pre-publication tuple; the exchange will say null,
# not pretend that its inventory hash proves Git/publication provenance.
```

The uniquely marked blocks are the extraction contract for a parent verifier.
Run each in order in the shell/environment on its indicated machine. The Python
blocks only prepare/validate the exchange; the `lake` blocks actually compile.

<!-- cs-snippet: create-source -->
```bash
: "${CORE_A:?}" "${ATTEMPT_A:?}"
python3 -B "$CORE_A/tools/workbench.py" verify-core --core "$CORE_A"
python3 -B "$CORE_A/tools/workbench.py" new "$ATTEMPT_A" --core "$CORE_A"
```

Replace only the fresh attempt's template with this complete named source:

<!-- cs-snippet: partial-source -->
```bash
cat > "$ATTEMPT_A/Attempt.lean" <<'LEAN'
import ConditionalSeparation.OpenProblem

namespace Attempt

theorem threshold_at_one (k : Nat) :
    Pnp4.Frontier.ContractExpansion.thresholdPoly k 1 = k + 1 := by
  simp [Pnp4.Frontier.ContractExpansion.thresholdPoly, Nat.add_comm]

theorem check_threshold_at_one :
    ∀ k : Nat, (1 : Nat)^k + k = k + 1 := by
  intro k
  exact threshold_at_one k

end Attempt

#print axioms Attempt.threshold_at_one
#print axioms Attempt.check_threshold_at_one
LEAN
```

<!-- cs-snippet: compile-source -->
```bash
(cd "$CORE_A" && lake env lean -DwarningAsError=true --root="$ATTEMPT_A" "$ATTEMPT_A/Attempt.lean")
```

Require both named declarations to compile and inspect both actual axiom
printouts. No unapproved axiom may appear (the installed core allowlist is
`propext`, `Classical.choice`, `Quot.sound`). The actual sets are determined by
the compiler; this text does not invent an empty axiom receipt. Compile/axiom
checks do not independently reprove a theorem or establish R.

### Exchange only source and identity

Do not send `attempt.json`, `lakefile.lean`, `lake-manifest.json`, `.lake`,
`.olean`, setup/receipt/cache files, or dependency objects as portable inputs:
the generated attempt files bind the author's absolute core location. The
following finite one-file example sends only `Attempt.lean` and `exchange.json`.
The latter contains the **complete package inventory**, its raw-file digest,
provenance/toolchain/lock digests, optional claimed release revision, exact
source pins and the two named lemma/type entries. For a multi-file attempt,
extend the explicit source/lemma inventory with only `Attempt.*` modules and
require the recipient to repeat the same source/identity checks.

<!-- cs-snippet: export-bundle -->
```bash
python3 -B - <<'PY'
import hashlib, json, os, re
from pathlib import Path
core = Path(os.environ['CORE_A']).resolve()
attempt = Path(os.environ['ATTEMPT_A']).resolve()
bundle = Path(os.environ['TRANSFER'])
revision = os.environ.get('PACKAGE_REV')
if revision is not None and not re.fullmatch('[0-9a-f]{40}', revision):
    raise ValueError('exact published revision or unset PACKAGE_REV required')
if bundle.exists() or bundle.is_symlink():
    raise ValueError('fresh transfer destination required')
raw_inventory = (core/'PACKAGE_FILES.json').read_bytes()
sha = lambda data: hashlib.sha256(data).hexdigest()
identity = {'inventory': json.loads(raw_inventory), 'inventory_sha256': sha(raw_inventory),
            'pins': {n: sha((core/n).read_bytes()) for n in
                     ('PROVENANCE.json', 'lean-toolchain', 'lake-manifest.json')},
            'claimed_release_revision': revision}
source = attempt/'Attempt.lean'
if source.is_symlink() or not source.is_file():
    raise ValueError('literal Attempt.lean required')
data = source.read_bytes()
lemmas = [
    {'name':'Attempt.threshold_at_one',
     'type':'forall k : Nat, Pnp4.Frontier.ContractExpansion.thresholdPoly k 1 = k + 1'},
    {'name':'Attempt.check_threshold_at_one',
     'type':'forall k : Nat, (1 : Nat)^k + k = k + 1'}]
record = {'schema':'conditional-partial-exchange-v1', 'package':identity,
          'sources':[{'path':'Attempt.lean','bytes':len(data),'sha256':sha(data)}],
          'lemmas':lemmas, 'claim':'closed partial arithmetic only; NOT R'}
bundle.mkdir(parents=True, exist_ok=False)
(bundle/'Attempt.lean').write_bytes(data)
(bundle/'exchange.json').write_text(json.dumps(record, indent=2)+'\n', encoding='utf-8')
PY
```

Copy that two-file bundle by your chosen reviewed channel. Its self-supplied
hashes are **not** code trust, owner authorization, old acceptance evidence or
proof of a claimed Git revision. Independently authenticate the package/release
and inspect the lemma source. `source_commit` in PROVENANCE is the historical
public **core-byte** anchor; it is not necessarily this package's release SHA.

On the recipient machine generate a new local attempt; never patch/reuse the
sender's absolute-path manifest:

<!-- cs-snippet: create-recipient -->
```bash
: "${CORE_B:?}" "${ATTEMPT_B:?}"
python3 -B "$CORE_B/tools/workbench.py" verify-core --core "$CORE_B"
python3 -B "$CORE_B/tools/workbench.py" new "$ATTEMPT_B" --core "$CORE_B"
```

<!-- cs-snippet: import-bundle -->
```bash
python3 -B - <<'PY'
import hashlib, json, os, re
from pathlib import Path
core = Path(os.environ['CORE_B']).resolve()
attempt = Path(os.environ['ATTEMPT_B']).resolve()
bundle = Path(os.environ['TRANSFER'])
if bundle.is_symlink() or {p.name for p in bundle.iterdir()} != {'Attempt.lean','exchange.json'}:
    raise ValueError('source-only two-file bundle required')
if any(p.is_symlink() or not p.is_file() for p in bundle.iterdir()):
    raise ValueError('regular exchange files required')
def pairs(items):
    d = {}
    for k,v in items:
        if k in d: raise ValueError('duplicate exchange JSON key')
        d[k] = v
    return d
record = json.loads((bundle/'exchange.json').read_text(), object_pairs_hook=pairs)
if not isinstance(record,dict) or set(record) != {'schema','package','sources','lemmas','claim'} or record['schema'] != 'conditional-partial-exchange-v1':
    raise ValueError('exchange schema')
package = record['package']
if not isinstance(package,dict) or set(package) != {'inventory','inventory_sha256','pins','claimed_release_revision'}:
    raise ValueError('package identity schema')
revision = package['claimed_release_revision']
if revision is not None and (not isinstance(revision,str) or not re.fullmatch('[0-9a-f]{40}',revision)):
    raise ValueError('claimed revision schema')
sha = lambda data: hashlib.sha256(data).hexdigest()
raw_inventory = (core/'PACKAGE_FILES.json').read_bytes()
expected = {'inventory':json.loads(raw_inventory), 'inventory_sha256':sha(raw_inventory),
            'pins':{n:sha((core/n).read_bytes()) for n in
                    ('PROVENANCE.json','lean-toolchain','lake-manifest.json')},
            'claimed_release_revision':revision}
# Compare canonical JSON bytes too: bool/int/float substitutions are not equal.
if json.dumps(package, sort_keys=True) != json.dumps(expected, sort_keys=True):
    raise ValueError('recipient package differs; use the identical verified source tuple')
source = (bundle/'Attempt.lean').read_bytes()
if record['sources'] != [{'path':'Attempt.lean','bytes':len(source),'sha256':sha(source)}] or type(record['sources'][0]['bytes']) is not int:
    raise ValueError('Attempt source inventory/hash')
expected_lemmas = [
    {'name':'Attempt.threshold_at_one',
     'type':'forall k : Nat, Pnp4.Frontier.ContractExpansion.thresholdPoly k 1 = k + 1'},
    {'name':'Attempt.check_threshold_at_one',
     'type':'forall k : Nat, (1 : Nat)^k + k = k + 1'}]
if record['lemmas'] != expected_lemmas or record['claim'] != 'closed partial arithmetic only; NOT R':
    raise ValueError('lemma inventory differs from this finite example')
if json.loads((attempt/'attempt.json').read_text())['core'] != str(core):
    raise ValueError('recipient attempt was not regenerated for its local core')
if (attempt/'Attempt.lean').read_bytes() != (core/'template/Attempt.lean').read_bytes():
    raise ValueError('replace only a newly generated template; preserve existing work')
(attempt/'Attempt.lean').write_bytes(source)
PY
```

<!-- cs-snippet: compile-recipient -->
```bash
(cd "$CORE_B" && lake env lean -DwarningAsError=true --root="$ATTEMPT_B" "$ATTEMPT_B/Attempt.lean")
```

Require the same named checks/allowed axiom roots here. Direct compilation of
this single-file partial attempt in the installed core's workspace may succeed;
that is not final acceptance. The final workbench ignores dependencies declared
**only** in the attempt's Lake files:
it uses the verified installed core workspace, parses actual imports and
recompiles `Attempt`/`Attempt.*` with explicit fresh own-module overrides.
Additional research dependencies must be admitted in that environment before
sharing a checker-compatible attempt; this recipe grants no such admission.

### Required final rejection and a misleading identity

The partial file intentionally has no `Attempt.research_lower_bound`. Run the
real default final checker and retain its actual exit/logs/receipts:

<!-- cs-snippet: partial-final-rejection -->
```bash
: "${CHECK_ROOT:?}"
mkdir "$CHECK_ROOT"
set +e
python3 -B "$CORE_B/tools/workbench.py" check "$ATTEMPT_B" >"$CHECK_ROOT/partial.stdout" 2>"$CHECK_ROOT/partial.stderr"
code=$?
set -e
printf '%s\n' "$code" >"$CHECK_ROOT/partial.os-exit.txt"
test "$code" -eq 1
```

**Nonzero alone is insufficient.** The new run in
`ATTEMPT_B/.lake/conditional-check/runs/` must show successful source/import
stages, then `exact-closed-guard-compile/terminal.json` with real `OS_exit=1`
and compiler diagnostic `missing closed proof Attempt.research_lower_bound`.
The subsequent `#print axioms` may also report that name as unknown. There
must be no `RESULT.json` or final Assembly. Failure to find Lean/dependencies,
wrong package identity or an earlier compile failure is not this expected
rejection. All these diagnostics/actual terminals remain PENDING until run.

For contrast, the following complete file compiles an identity but still does
not supply R. Create another NEW attempt with the recipient's core:

<!-- cs-snippet: create-wrong -->
```bash
python3 -B "$CORE_B/tools/workbench.py" new "$WRONG_ATTEMPT" --core "$CORE_B"
```

<!-- cs-snippet: wrong-source -->
```bash
cat > "$WRONG_ATTEMPT/Attempt.lean" <<'LEAN'
import ConditionalSeparation.OpenProblem

namespace Attempt

theorem research_lower_bound :
    ConditionalSeparation.OpenProblem.R → ConditionalSeparation.OpenProblem.R :=
  fun h => h

end Attempt

#print axioms Attempt.research_lower_bound
LEAN
```

<!-- cs-snippet: compile-wrong -->
```bash
(cd "$CORE_B" && lake env lean -DwarningAsError=true --root="$WRONG_ATTEMPT" "$WRONG_ATTEMPT/Attempt.lean")
```

<!-- cs-snippet: wrong-final-rejection -->
```bash
set +e
python3 -B "$CORE_B/tools/workbench.py" check "$WRONG_ATTEMPT" >"$CHECK_ROOT/wrong.stdout" 2>"$CHECK_ROOT/wrong.stderr"
code=$?
set -e
printf '%s\n' "$code" >"$CHECK_ROOT/wrong.os-exit.txt"
test "$code" -eq 1
```

Here the expected boundary is again `exact-closed-guard-compile`, but the
compiler diagnostic must be `declaration must have CLOSED exact expected type`,
not a missing declaration or missing tool. The theorem has type `R → R`, not
R. Likewise changing `∃ k, ∀ d` into `∀ d, ∃ k` changes the research problem;
neither variation is a route around the exact-R guard. No positive R receipt
or unconditional separation is produced by any example in this guide.
