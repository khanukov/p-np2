# Part A R1 connected reader prefix

Current local correction (2026-10-23, uncommitted): `#partA_axioms` resolves each
literal against the invoking environment, with exact name roundtrip, membership,
ambiguity rejection and the existing standard-axiom allowlist. It retains no
process-global first-environment snapshot. A named same-module regression audits
an imported root before declaring and auditing late definitions and a literal
full-proposition mirror, including numeric/private and quoted-name cases.
Its fixture roots supplement the unchanged prefix inventory below; they do not
add a Part A theorem or establish private-ABI elaborator usability. Targeted
results for this correction are separate from prior default17 results. New-head
source review, fullgate, CI and release remain open. Qodo was restored by the
2026-10-23 human authorization; earlier no-Qodo phase restrictions below are
historical. This source-author phase requests no reviews and publishes nothing.

The implementation and docs-only chronology below refers to the preserved prior
commits, not to acceptance of this uncommitted helper correction.

Current design and evidence limits (2026-10-24, documentation-only correction):
prospective merge requires `/agentic_review` on the exact latest pushed SHA,
alongside independent Codex+Claude alignment, kernel/full17, current-head
protected-owner authority and raw CI. None is newly accepted by this docs child.

`printDirect` retains `for entry in env.constants.toList do` followed by
`let other := entry.1`. Tuple destructuring (`for (other, _) in ...`) would make
the equation compiler generate a matcher colliding with the explicit
`PartACanonical.Audit.printDirect.match_3` ABI shim. Keep the projection form.
The independent `e0004`/`e0005`/`e0006` pins establish expected type and instance
identity only, not matcher attributes, reducibility or equation-lemma equivalence.
No Lean helper bytes are changed by this design note.

The uncached collision scan is linear in the current environment per call and
materializes its constant list. The preserved parent central compile took
2368.447952 seconds in total, including legacy native prints; this is not a new
measurement, a timing of the scan alone or a LOC-based estimate.

The historical option inventory records raw occurrences only of maxHeartbeats,
maxRecDepth, linter.* and autoImplicit; comment/string matches are possible.
It is not an inventory of all set_option tokens or effective options across all
dependencies. No omitted current option/suppression defect is established.
The retained strict compiler result is modulo the disclosed
`set_option linter.deprecated false`; no unsuppressed-lint claim is made.

This Infrastructure implementation was locally committed on 2026-10-21 at
`e33fae0fabb930f744366b479d66575c7d6702f7`. The accepted
Body/AcceptedBody seven remain unchanged. Only InputRead.Machine/Path/Target/Proof/Raw,
GammaSupport.Target/Closure and ConnectedRead.Target/Closure are new originals:
815 physical source lines, copied with exact admitted bytes and private owners.

Scoped Codex+Claude source opinions approve the implementation with the chronology
LOW addressed by this docs-only follow-up. Its unchanged default17 has actual
parent-verified PASS: all 17 stages and 622 own-context standard-only direct roots.
This follow-up changes three docs only. Results for the fixed implementation SHA
do not establish new-docs-head checks or approval, raw CI or remote release.

The full ConnectedRead.exact surface retains accepted-input parsing, table support,
the n >= 3 guard, physical gamma support 9+2*z <= a+m, the whole final Config and
the exact 144*(pairLength a m+1)^2 bound. InputRead.Target.PartA's named body iff
contract is an interface expansion; it does not establish the dormant full reader
endpoint. Gamma support retains both semantic acceptance and parsed-input premises.
No source clock, table, relation, allocation or theorem premise is changed.

The owner-selected inventory has 213 public FQNs, including generated constructors,
recursors, projections and the loopTape.eq_1 name owned by InputRead.Raw. It has
108 theorem-kind entries. Sixty-eight existing named literal full mirrors are
reused; forty missing literal mirrors are mechanical restatements using original
proof terms. They are not independently authored mathematical correctness proofs.
The 213 original expected-type pins, 65 prior-consumer pins and 11 helper pins are
separate from mirrors. All 622 original/surface/pin/helper public roots are direct
commands in Tests.AxiomsAudit. This finite prefix exposes no private signature
among the actual 213 public source declarations; unrelated private families from
the full 872-module campaign are not part of this release payload.

The durable R1 report records actual current-source compiler exits, metadata,
selected import objects and direct root logs. Cached unchanged base inputs and
accepted seven source objects are reused inputs, never fresh R1 compile claims.
The RAM cache is ephemeral; accepted fresh outputs have durable retained copies.
Default aggregate check results and strict warning-as-error consumer results are
reported separately. A default pass cannot cure a historical strict-warning FAIL.

Source-only 815 LOC is not the release price. The R1 changeset includes every
untracked file, tests, literal pins/mirrors, central roots, Lake registration and
docs; controls, source snapshots, retired controls and storage are separately
priced. Ordinary policy is 1500 additions+deletions of Lean LOC /10 MODULES.
The human-authorized finite migration exception is not a global cap waiver.

Part A remains OPEN. This prefix does not close the legacy TM bridge or produce
an NP lower bound against PpolyDAG. New-docs-head source/docs closure,
final-head Codex+Claude alignment, protected Lake-path attestation,
serialized final-head checks, raw CI and publication remain coordinator work.

Historical worker scope and dated addenda follow verbatim. Their no-commit,
uncommitted/admission and pending-review fields describe earlier phases and are
superseded for the implementation by the fixed-SHA current status above.

No staging, commit, push, merge, PR or Qodo action is authorized in this phase.

The unchanged default17 script has literal /tmp log paths outside this R1 worker's
four authorized write roots. TMPDIR alone does not redirect them. Its admission
result is recorded separately from targeted kernel PASS; no aggregate PASS or
check-script OS exit is claimed when the script child was not launched.

Dated correction-capsule addendum (2026-10-21): this is a local rehearsal copied
from the uncommitted R1 tuple, not an accepted release parent. "Independent"
expected-type pins mean separately written literal annotations, including existing
elaboration auxiliaries where required. Examples include Body.install_exact._proof_1,
InputRead.install_exact._proof_1 and InputRead.modeOf._proof_1/_proof_2, plus the
check_*._proof_* terms in consumer types. These imported auxiliary dependencies
are excluded from the 213 intended public API names; their use is not an independent
reproof or standalone reconstruction of proof-dependent indices. No annotation,
mirror proposition, proof term, root or original machine/clock is changed here.

The private-ABI elaborator has no prefix call sites. Its five helper type pins
check types only; no private-case elaborator execution/usability is claimed.
Body.Target.PartA and InputRead.Target.PartA are distinct dormant interface constants
with byte-identical bodies. The G2 theorem expands only InputRead.Target.PartA's
definitional body; it is not a relating theorem or a proof of either interface.

"Fully audited" in the preserved R1 report means, at most, the recorded compiler,
API/type and direct-axiom checks. Both primary source opinions approve the scoped
R1 source with findings; the corrections themselves still need focused closure
review, exact-head gates, CI, protected attestation and release authorization.
The unchanged README's 2026-08-21 "current tree" claim is historical context,
not R1 compiler or check-script evidence.

The original BLOCKED_WRITE_SCOPE admission remains historical and is not a global
or permanent verdict. A separately parent-coordinated private-namespace default17
run uses scratch-backed /tmp. Only its actual terminal can establish that run's
outcome; completed stages are not aggregate PASS. Package cache is read-only only
inside that namespace. A required package write may therefore cause an environmental
failure, which by itself is not a source/theorem defect. The runner's "RAM" reserve
label is not a measurement of the backing filesystem. This capsule neither builds
nor changes that namespace/cache/source, and does not transfer any run result to
its comment-corrected snapshot or to an accepted/released head.
