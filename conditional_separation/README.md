# Conditional Separation research workbench

This source package exposes one exact, substantial **unproved** circuit-search
lower-bound proposition, `ConditionalSeparation.OpenProblem.R`. Its conditional
consequence is proved by the copied accepted core: one and the same fixed
threshold codec/language is in Ordinary NP, outside canonical DAG P/poly, and
outside Ordinary P. No assumption-free P-versus-NP separation theorem, novelty, nonvacuity or
successful proof of R is claimed. The legacy differently typed
ContentVerifierBridge remains unfilled and outside this direct route.

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
identities and source bytes. PROVENANCE.json contains relative SHA256 provenance.
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
No published Git dependency revision is provided or invented; the initial mode
uses an explicit local installed source package.

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
the original workbench tests and nine CI DATA modules:
`test_portable_ci_data_v1`, `test_completion_v2`, `test_native_first_run_v1`,
`test_windows_layout_v1`, `test_locked_foundations_v1`, `test_locked_evidence_v1`, `test_path_archive_hardening_v1`, `test_trusted_controls_v1`, and `test_reliability_v1`.
Native compiler
rejection tests remain a separate, explicit command; Python DATA is not a native
platform or kernel result. The original Linux cold-source checkpoint alone does not certify another
installed revision. Source review, exact-head build/full conditional consumer/cache
verification, actual native Linux/macOS CI, owner, latest-head Qodo,
raw CI and release acceptance remain separately scoped evidence. No assumption-free P-versus-NP separation, standard-class equivalence, ease or novelty
claim follows. R remains UNPROVED and the legacy bridge remains unfilled.

The portable Python unit runner supplies a fresh private `CI_DATA_ROOT` without
weakening the CI DATA suites' guards. Its default temporary directory follows
the platform's normal temporary-directory configuration. To retain fixtures,
pass `--data-root /path/to/new/private-data`; the path must not already exist.
It never runs Lean, Lake or the native operational driver and rejects Python
optimization because ordinary discovery includes workbench tests. Direct
`python3 -m unittest discover -s tests -v` remains available when the caller
explicitly supplies an existing private `CI_DATA_ROOT` directory. Native CI's
unit command now uses the runner with its own fresh runner-private path.
